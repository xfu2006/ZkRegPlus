/* Created 03/04/2025 
	Revised: 10/13/2025 -> improved m_table performance to 1xnlen
*/

use std::rc::{Rc};
use rayon::iter::{ParallelIterator,IntoParallelIterator,
	IndexedParallelIterator};
use ark_ff::{PrimeField};
use std::{
	marker::{PhantomData},
	collections::{HashMap}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice},
	container_config::{ContainerConfig},
};
use ark_r1cs_std::{
	fields::{
		//FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	//eq::EqGadget,
};
use std::any::Any;
use crate::gadgets::db::assert_logup;


#[allow(dead_code)]
/// This gadget is responsible for packing a list of
/// states into a set of final states.
/// No need to handle inp/oup as inp/oup only needed for signatures.
#[derive(Clone,Debug)]
pub struct PackFinalGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	/// should be LEGS * max_word_len + 1
	inp_states_len: usize, 
	/// the buffer size to hold output: the set of final states
	oup_states_len: usize,
	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	fsm_id: u32, 
}

impl <F:PrimeField> PackFinalGadget<F>{
	pub fn new(inp_states_len: usize, oup_states_len: usize, fsm_id: u32)
	-> Self{
		Self{_f: PhantomData, inp_states_len, oup_states_len, fsm_id}
	}
}

impl <F:PrimeField> SigmaGadget<F> for PackFinalGadget<F>{
	fn get_name(&self)->&str {"PackFinalGadget"}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: Rc<Vec<ContainerConfig>>, _idx: usize){
		unimplemented!("not needed. handled by legacy code");
	}

	fn get_container_config(&self)->ContainerConfig{
		unimplemented!("not needed. handled by legacy code");
	}

	/// Get the instructions for build its statement.
	/// NOTE: this is only needed for those used in SedGadgetMapper.
	/// Others are handled by legacy code in their gadget mapper.
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	/// return the sizes of inp/oup/data to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	fn est_cost(&self)->usize{
		let est = self.inp_states_len*2 + self.oup_states_len*7;
		est
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) no word_segment
		//  (2) inp: none,
		//  (3) oup: none,
		//  (4) data: 
		//       inp_states: inp_len (all valid values)
		//       oup_states: oup_len (may be padded with zero)
		//       m_table: oup_len
		//  (5) its own subtbl_id for data.
		//       (1) verify oup_states are all in final_states, or the val
		//              is 0 (padding value): oup_len
		// ]
		// NO msg1, but 1 messaege 2 for Logup, no msg3
		// Total statement len:  2*(inp_len + oup_len)
		// actual msg3 is inverse of two tables (ilen + olen)
		// BUT we can generate it in assert_msg3() directly, so we
		// do not list the size here.
		let (ilen, olen) = (self.inp_states_len, self.oup_states_len);
		let word_len = 0;
		let inp_len = 0;
		let oup_len = 0;
		let data_len = ilen + olen*2;
		let subtbl_id_len = olen;
		let stat_len = word_len + inp_len + oup_len + data_len + subtbl_id_len;
		assert!(stat_len == ilen + 3*olen);

		(stat_len, 0, 2, 0)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
		-> Vec<F>{
		vec![] // dummy
	}

	fn gen_msg3(&self, _stmt_vec: &Vec<F>, _stmt_idx: &Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		vec![]
		//the inverse table can be computed directly in assert_msg3()
		//when it calls assert_logup()
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		let b_debug = true;
		let mut nc = cs.num_constraints();
		let mut nv = cs.num_witness_variables();

		//1. retrive the statement instance 
		//COST: 0 n1rs, 0 var
		let (stmt_idx, _msg1_idx, msg2_idx, msg3_idx) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		//assert!(my_stmt.len()==self.get_msg_size().0);
		//disabled for manually test cases which is not constructed
		//from Witness.
		let (ilen, olen) = (self.inp_states_len, self.oup_states_len);
		if b_debug{
			println!("## pack step 1. olen: {}, ilen: {}, r1cs: {}, vars: {}", 
				olen, ilen, cs.num_constraints()-nc, 
					cs.num_witness_variables()-nv);
			nc = cs.num_constraints();
			nv = cs.num_witness_variables();
		}

		//2. get the parts of the statement
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		// NOTE: no word, input and output
		//COST: 0 r1cs, 0 var
		let data_seg = my_stmt[0..ilen+olen*2].to_vec(); 
		let subtbl_id = &my_stmt[ilen+olen*2..ilen+olen*2+olen];
		assert!(data_seg.len() + subtbl_id.len()
			== self.get_msg_size().0);
		let (_alpha, beta) = (wtns.msg2[msg2_idx].clone(), 
			wtns.msg2[msg2_idx+1].clone());
		let msg3 = wtns.msg3[msg3_idx..msg3_idx+ilen+olen].to_vec();
		if b_debug{
			println!("## pack step 2. olen: {}, ilen: {}, r1cs: {}, vars: {}", 
				olen, ilen, cs.num_constraints()-nc, 
					cs.num_witness_variables()-nv);
			nc = cs.num_constraints();
			nv = cs.num_witness_variables();
		}

		//3. assert that all output states must be in range
		// if the state is not zero (padding), it must be a final state
		// COST: 4 * inp/oup len r1cs, vars: 2 * inp len
		// could be improved, but not worth it as inp/oup buf small.
		let oup_states = &data_seg[ilen..ilen+olen];
		let m_table = &data_seg[ilen+olen..ilen+2*olen];
		let _tblid_finals= FpVar::<F>::new_constant(cs.clone(), 
			F::from(self.fsm_id + 2))?;//e.g., CRIT_FINALS
		let _zero_var= FpVar::<F>::new_constant(cs.clone(), 
			F::zero())?;//e.g., CRIT_FINALS
		/*
		for i in 0..olen{
			let val = oup_states[i].is_zero()?.select(&zero_var,&tblid_finals)?;
			subtbl_id[i].enforce_equal(&val)?;
			#[cfg(test)]{
				use ark_r1cs_std::{R1CSVar};
				if subtbl_id[i].value().is_ok(){
					assert!(subtbl_id[i].value()?==val.value()?);
				}
			}
		}
		*/
		if b_debug{
			println!("## pack step 3. olen: {}, ilen: {}, r1cs: {}, vars: {}", 
				olen, ilen, cs.num_constraints()-nc, 
					cs.num_witness_variables()-nv);
			nc = cs.num_constraints();
			nv = cs.num_witness_variables();
		}

		//4. assert validity of msg3 (inverse relation)
		let _one_var= FpVar::<F>::new_constant(cs.clone(), 
			F::one())?;//e.g., CRIT_FINALS
		let inp_states = &data_seg[0..ilen];
		let _inp_inv = msg3[0..ilen].to_vec();
		let _oup_inv = msg3[ilen..ilen+olen].to_vec();
		/*
		for i in 0..ilen{
			let prod = &inp_inv[i] * &(&inp_states[i] + &alpha);
			prod.enforce_equal(&one_var)?;
			#[cfg(test)]{
				use ark_r1cs_std::{R1CSVar};
				if prod.value().is_ok(){ assert!(prod.value()?==F::one()); }
			}
		}
		for i in 0..olen{
			let prod = &oup_inv[i] * &(&oup_states[i] + &beta);
			prod.enforce_equal(&one_var)?;
			#[cfg(test)]{
				use ark_r1cs_std::{R1CSVar};
				if prod.value().is_ok(){ assert!(prod.value()?==F::one()); }
			}
		}
		*/
		assert_logup(cs.clone(), &inp_states, &oup_states, m_table, &beta)?;
		if b_debug{
			println!("## pack step 4. olen: {}, ilen: {}, r1cs: {}, vars: {}", 
				olen, ilen, cs.num_constraints()-nc, 
					cs.num_witness_variables()-nv);
			if 1>0 {panic!("STOP HERE 3001");}
		}

		Ok(())
	}
}

/// Advice for the WordExtract Gadget.
#[derive(Debug)]
pub struct PackFinalAdvice<F:PrimeField>{
	/// oup_states (first final states and then padding 0)
	pub oup_states: Vec<F>,
	/// m_table appearance of oup_states
	pub m_table: Vec<F>,
	/// labeling of subtable_id (0 for padding state)
	pub subtbl_id: Vec<F>,
	/// capacity
	pub capacity: usize,
}

impl <F: PrimeField> NdAdvice for PackFinalAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> PackFinalAdvice<F>{
	/// Given a sequence of states (no padding), and the their
	/// corresponding subtbl_ids. 
	/// Identify the set of final states, and layout 
	/// the ouput states (padded with zero) at end.
	/// NOTE that here tblid_final 
	pub fn new(inp_states: &Vec<F>, subtbl_ids: &Vec<F>, tblid_final: &F,
		capacity: usize)->Self{
		//1. construct the output hashset and their occurence.
		assert!(inp_states.len()==subtbl_ids.len());
		let mul_final_states = inp_states.into_par_iter().zip(
			subtbl_ids.into_par_iter())
			.filter(|(_, f)| *f==tblid_final).map(|(s,_)| s.clone())
			.collect::<Vec<F>>();


		let map:HashMap<F,usize> = mul_final_states.into_par_iter()
		.fold(|| HashMap::new(),
			|mut acc, state| {
				*acc.entry(state).or_insert(0) += 1;
				acc
			})
		.reduce(//merge accumulator of threads
			|| HashMap::new(),
			|mut acc1, acc2| {
				for (key, val) in acc2{ *acc1.entry(key).or_insert(0) += val; }
				acc1
			}
		);
		let mut oup_states:Vec<F> = map.iter().map(|(k,_)| k.clone()).collect();
		/* RECOVER LATER
		#[cfg(test)]{
			assert!(oup_states.contains(F::zero(), "oup_states should contain zero"));
		}
		*/

		let mut m_table: Vec<F> = map.iter().map(|(_,v)| 
			F::from(*v as u32)).collect();

		let mut subtbl_id = vec![tblid_final.clone(); m_table.len()];
		assert!(oup_states.len() == m_table.len());
		let mut vzero = vec![F::zero(); capacity - oup_states.len()];
		let (mut vz2, mut vz3) = (vzero.clone(), vzero.clone());
		oup_states.append(&mut vzero);
		m_table.append(&mut vz2);
		subtbl_id.append(&mut vz3);


		Self{oup_states, m_table, subtbl_id, capacity}
	}
}

#[cfg(test)]
pub mod tests_pack_gadget{
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use crate::gadgets::pack::{PackFinalGadget,PackFinalAdvice};
	use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget;
	use ark_ff::{Zero};



	#[test]
	fn test_pack(){
		//1. create final states and then non-final states
		let msf_id:u32 = 0x10001001;
		let f_nonfinal_id = Fr::from(msf_id + 1);
		let f_final_id = Fr::from(msf_id + 2);
		let vec_final = vec![2u32, 3u32, 4u32, 5u32].into_iter()
			.map(|x| Fr::from(x)).collect::<Vec<Fr>>();
		let vec_non_final = vec![101u32, 123u32, 134u32, 133u32, 201u32, 211u32, 212u32, 255u32].into_iter().map(|x| Fr::from(x)).collect::<Vec<Fr>>();
		let inp_size = 24;
		let capacity = 10;
		//ratio is final is about 1/4
		let mut inp_states = vec![];
		let mut subtbl_ids = vec![];
		for i in 0..inp_size{
			let ele = if i%4==0{vec_final[(i*234234+2341)%vec_final.len()]}
				else{vec_non_final[(i*828342187+12183)%vec_non_final.len()]};
			let id = if i%4==0 {f_final_id.clone()}
				else {f_nonfinal_id.clone()};
			inp_states.push(ele);
			subtbl_ids.push(id);
		}
		let gadget= PackFinalGadget::<Fr>
			::new(inp_states.len(), capacity, msf_id);
		let rg = Rc::new(gadget);

		//2. build the advice
		let mut adv = 
			PackFinalAdvice::new(&inp_states, &subtbl_ids, &f_final_id, 
			capacity);
		let inp = vec![];
		let oup = vec![];
		let data = vec![
			inp_states.clone(),
			adv.oup_states,
			adv.m_table,
		].concat();
		assert!(data.len()==2*capacity + inp_states.len());
		let to_pad_size = inp.len() + oup.len() + data.len() 
			- adv.subtbl_id.len();
		println!("DEBUG USE 7888: to_pad_size: {}", to_pad_size);
		adv.subtbl_id = [&adv.subtbl_id[..], &vec![Fr::zero(); to_pad_size][..]]
			.concat(); //to make the Witness.to_vec_fp_var check happy
					   //in cp_map.rs this onstraint inp+oup+data.len
					   //  == subtbl_id.len will be satisfied but not
					   //for this manually constructed example

		let lkup_share_size = 4usize;
		test_gadget::<Fr>(rg, &vec![], &inp, &oup, &data, &adv.subtbl_id, 
			lkup_share_size);
	}
}
