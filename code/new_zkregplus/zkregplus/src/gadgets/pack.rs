/* Created 03/04/2025 
	Revised: 10/13/2025 -> improved m_table performance to 1 x nlen
*/


use folding_schemes::folding::foldpot::container_config::ColEle;
use rayon::iter::{ParallelIterator, IndexedParallelIterator,IntoParallelRefIterator};
use data_processor::clam_db::RANGE2;
use ark_ff::{PrimeField};
use std::{
	marker::{PhantomData},
	collections::{HashSet}
};
use ark_relations::{
	r1cs::{SynthesisError,ConstraintSystemRef,LinearCombination,Variable}
};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice},
		container_config::{ContainerConfig},
	}
};
use ark_r1cs_std::{
	R1CSVar,
	fields::{
		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	//eq::EqGadget,
};
use std::any::Any;
use crate::{
	gadgets::{
		db::assert_logup,
		commons::{gen_m_table,new_var, var_to_lb,new_const_var,
			is_zero_better, gen_vec_inverse, var_to_tuple, var_to_tuple_adv}
	}
};


/// This gadget is responsible for packing a list of
/// states into a set of final states.
/// No need to handle inp/oup as inp/oup only needed for signatures.
/// NOTE that it's essentially two parts:
/// (1) map the MULTI-set of states to a UNIQUE set of states (we do 
///     not care about destination is final states or not to cut cost
///     as unique set states is much smaller)
///      -> this is essentially accomplished using log_up (one direction).
///      then prove each element in m_table is non-zero so that it
///      accomplishes 2-directional map (note: need to handle 0 dummy element)
/// (2) Filter the UNIQUE set of states to a UNIQUE set of final
///     states only.
///     this is essentially a conditional equivalence test of two multi-sets
///     depending on a selector.
#[allow(dead_code)]
#[derive(Clone,Debug)]
pub struct PackFinalGadget<F:PrimeField + ColEle>{ 
	_f: PhantomData<F>,
	/// should be LEGS * max_word_len + 1
	inp_states_len: usize, 
	/// the intermediate buf size
	/// this is essentially the unique set of states (note: not final states)
	imm_buf_len: usize,
	/// the buffer size to hold output: the set of final states
	oup_states_len: usize,
	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	/// IN circuit, this is HARD CODED, either the ACDFA for the
	/// IGC case or case sensitive case.
	fsm_id: u32, 
}

impl <F:PrimeField + ColEle> PackFinalGadget<F>{
	pub fn new(inp_states_len: usize, imm_buf_len: usize, 
		oup_states_len: usize, fsm_id: u32)
	-> Self{
		Self{_f: PhantomData, inp_states_len, imm_buf_len,
			oup_states_len, fsm_id}
	}
}

impl <F:PrimeField + ColEle> SigmaGadget<F> for PackFinalGadget<F>{
	fn get_name(&self)->&str {"PackFinalGadget"}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: std::sync::Arc<Vec<ContainerConfig>>, _idx: usize){
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
		let est = self.inp_states_len + self.oup_states_len*7;
		est
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) no word_segment
		//  (2) inp: none,
		//  (3) oup: none,
		//  (4) data: 
		//       <<<inp_states: inp_len (all valid values) -> borrowed
		//            from previous component (fsm) -- FOREIGN COLUMN>>>
		//       -----------------------------------------
		//       imm_states: unique set of states (not necesaarily final)
		//          of inp_states.
		//       oup_states (final states): oup_len (may be padded with zero)
		//       m_table: (imm_len for inp_states <-> imm_states)
		//  (5) its own subtbl_id for data.
		//		inp_states: <<NO subtbl_id>>. they are ALREADY
		//          verified by lkup in previous (fsm) component.
		//		----------------------------
		//      imm_states: [will be set to EITHER final or NON_FINAL TAG],
		//			length: mlen
		//		oup_states:  [ just set to zero as there is a bi-directional
		//         multiset check between imm_states and oup_states.
		//         so there is no need to do extra subtbl id tagging
		//         const 0 keeps the logup check cost low]
		//         read assert_msg3 for details.
		//          lenth: olen
		//		m_tbl: zero (subtbl_id: zero's) , length: mlen
		//      total len: 2*mlen + olen 
		// ]
		// NO msg1, but 1 messaege 2 for Logup, no msg3
		// actual msg3 is inverse of two tables (ilen + olen)
		// BUT we can generate it in assert_msg3() directly, so we
		// do not list the size here.
		let (_ilen, olen, mlen) = (self.inp_states_len, 
			self.oup_states_len, self.imm_buf_len);
		let word_len = 0;
		let inp_len = 0;
		let oup_len = 0;
		let data_len = 2*mlen + olen; 
		let subtbl_id_len = 2*mlen + olen;  
		let stat_len = word_len + inp_len + oup_len + data_len + subtbl_id_len;
		assert!(stat_len == 2*(2*mlen+olen)); 
			//inp_states not counted

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

	/// Basic idea here:
	/// (1) inp_states <---> unique_states
	///     We first run a 1-direction log-up check to find
	///     all inp_states + [0] are contained in unique_states.
	///     	Then to make sure that unique_states are also COVERED
	///     in inp_states, we just check that all m_table entries are
	///     non_zero. This way we avoid do another logup check which
	///     is more costly as it needs the m_table to be of hte same
	///     size of inp_states (the trace len).
	///         Here, both inp_states and unique_states have dummy
	///     0 entrie sto make sure that the 2nd non-zero check of m_table
	///     will succeed.
	/// (2) unique_states <--> oup_states (final states)
	///     Now first, unique_states has the correct NON_FINAL and FINAL
	///     tag. So using the subtbl tag of each state, we do a conditoinal
	///     multi-set equivalence check between unique_states and
	///     oup_states (ignoring the entries which are not final, and
	///     ignoring zero entries)
	/// COST: nlen - nibbles length, mlen - imm buf len, olen - final state len
	///  (1)  nlen + 6*mlen
	///  (2)  4*mlen + 4*olen
	/// TOTAL = nlen + 10*mlen + 4*olen 
	/// in real setting: mlen much less 0.05% of trace and olen is usually
	/// fixed at lower than several thousand 
	/// (number of subsigs * pattern/subsig)
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig, 
		_word_id: FpVar<F>, _subseg_id: FpVar<F>) 
		-> Result<(), SynthesisError>{
		let b_debug = false;
		let nc = cs.num_constraints();
		let nv = cs.num_witness_variables();
		//1. retrive the statement instance 
		//COST: 0 n1rs, 0 var
		let (stmt_idx, _msg1_idx, msg2_idx, _msg3_idx) = 
			cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		//assert!(my_stmt.len()==self.get_msg_size().0);
		//disabled for manually test cases which is not constructed
		//from Witness.
		let (ilen, mlen, olen) = (self.inp_states_len, 
			self.imm_buf_len, self.oup_states_len);

		//2. get the parts of the statement
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		// NOTE: no word, input and output
		//COST: 0 r1cs, 0 var
		let data_seg = my_stmt[0..ilen+2*mlen+olen].to_vec(); 
		let subtbl_id = &my_stmt[ilen+2*mlen+olen..ilen+2*mlen+olen
			+2*mlen + olen];
		assert!(data_seg.len() + subtbl_id.len()
			== self.get_msg_size().0 + ilen); //because ilen is not counted
		let (_alpha, beta) = (wtns.msg2[msg2_idx].clone(), 
			wtns.msg2[msg2_idx+1].clone());

		//3. assert that all unique_states is the compressed
		// set of states of inp_states.
		// We first do a lookup from inp_states (padded with 0) to unique 
		// states, and then we asssert that the m_table is a non-zero vector
		// thus convincing: (1) all inp_states can be found in unique states
		//, and (2) all unique states can be found in inp_states (pad with 0)
		// NOTE: no need to check subtbl_ids, as based on fixed
		//COST: ilen + 6*mlen  (ilen is the max-nibble-len)
		//3.1 assert log up
		//COST: ilen + 2*mlen
		let _zero_var= FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let inp_states = &data_seg[0..ilen];
		let unique_states = &data_seg[ilen..ilen+mlen];
		let m_table = &data_seg[ilen+mlen..ilen+2*mlen];
		let oup_states = &data_seg[ilen+2*mlen..ilen+2*mlen+olen];
		assert_logup(cs.clone(), &inp_states,  &unique_states, m_table, &beta)?;

		//3.2 assert that when unique_states[i] is NOT zero, then
		// m_table[i] should not be zero (this shows that all states
		// in unique_states are COVERED in the inp_states, i.e.,
		// no fake states added).
		//
		// basically we are doing oup_states[i]!=0 IMPLY m_table[i]!=0
		// then apply not (a) or b we have
		// unique_states[i]==0 + m_table[i]!=0 is true (non_zero)
		// COST: 2*mlen
		//let zero = F::zero();
		let one_var = FpVar::<F>::constant(F::one());
		let lb_zero= LinearCombination::from((F::zero(),Variable::One));
		let m_vals= m_table.iter().map(|m|{m.value().unwrap()})
			.collect::<Vec<F>>();
		let vec_inv = gen_vec_inverse(&m_vals);
		for i in 0..m_table.len(){
			// we are argueing that
			// when unique_states[i]!=0:
			//    m_table[i]!=0, i.e., there exists inverse_m_table[i]
			//    s.t.
			//    unique_states[i] * (mtable[i] * inverse_mtable[i] - 1) = 0
			//    when unique_states[i]==0 it's don't care
			//let m_tbl_i_val = m_table[i].value()?;
			//let inv_m_val = if m_tbl_i_val.is_zero() {zero} else{
			//	m_tbl_i_val.inverse().expect("error no inverse")};
			let inv_m_var = new_var(&cs, vec_inv[i]);
			let item2 = &m_table[i] * &inv_m_var - &one_var;
			let lb_item2 = var_to_lb(&item2, F::one());
			let lb_unique_i = var_to_lb(&unique_states[i], F::one());
			cs.enforce_constraint(
				lb_unique_i,
				lb_item2,
				lb_zero.clone()
			)?;
		}

		//3.3 assert that subtbl_unique_states is either
		//non_final or final_states for fsm_id
		//note that: this segment is NOT constant (but dynamically
		//generated.
		// essentially we are checking:
		//  (subtbl_id[i] - non_final)*(subtbl_id[i]-final) * unique[i]
		//  Here unique[i] as a factor indicating htat if it's 0 (dummy)
		//  ignore the requirement that subtbl_id[i] must be final or non_final
		//COST: 2xmlen
		let subtbl_unique_states = &subtbl_id[0..mlen];
		let f_nonfinal_id = F::from(self.fsm_id+ 1);
		let f_final_id = F::from(self.fsm_id+ 2);
		let var_non_final = new_const_var(&cs, f_nonfinal_id);
		let var_final = new_const_var(&cs, f_final_id);
		let mut vec_lb_unique = vec![];
		for i in 0..mlen{
			let tmp = &(&subtbl_unique_states[i]-&var_non_final)*
				&(&subtbl_unique_states[i]-&var_final);
			let lb_tmp = var_to_lb(&tmp, F::one());
			let lb_unique_i= var_to_lb(&unique_states[i], F::one());
			vec_lb_unique.push(lb_unique_i.clone());
			cs.enforce_constraint(
				lb_tmp,
				lb_unique_i,
				lb_zero.clone()
			)?;
		}

		//4. assert that: if ignoring 0 (dummy) entries,
		// and also ignoring non_final states.
		//unique_states is a EQUAL multi_set equal to
		//the oup_states.
		//
		//so selector for unique_states is that
		//  (subtbl_unique_states[i] - final_state).is_zero()
		// - this ignores the 0 entry 
		// then if sel is 1:
		//   prod_next = prod * (uniqune_states[i] + 1)
		// if sel is 0
		//   prod_next = prod
		// this needs 2 r1cs
		//selector for oup_states is 
		//  1-oup_states[i].is_zero (this needs to be done using boolean)
		// We then ues log_up because the inverse of unique_states
		// is genereated in logup check in earlier inp_states -> unique_states
		// But m_tbl for 
		//
		//COST: 4*mlen + 4*olen 

		//4.1 compute the grand prod of the unique_states
		let sel_unique = subtbl_unique_states.iter().map(|s|
			is_zero_better(&(s - &var_final), &cs).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let mut prod_unique= FpVar::<F>::new_constant(cs.clone(), 
			F::one())?;
		let one_var= prod_unique.clone();
		let tp_neg_one= (-F::one(),Variable::One);
		//let lb_neg_one = LinearCombination::<F>(vec![
		//	(-F::one(), Variable::One)
		//]);

		for i in 0..mlen{
			//(a) assert conditional select of item
			//i.e. (1-sel) * (item-1) + sel*(item-unique[i]) = 0
			//i.e. item -1 + sel - sel*unique[i] = 0
			//i.e., sel * unique[i] = sel + item -1
			let item_val = if sel_unique[i].value()?.is_one(){
				unique_states[i].value()?
			} else {F::one()};
			let item = new_var(&cs, item_val);
			let tp_sel = var_to_tuple_adv(&sel_unique[i], F::one());
			let lb_sel = LinearCombination::<F>(vec![tp_sel.clone()]);
			//let lb_item = var_to_lb(&item, F::one());
			let lb_four = LinearCombination::<F>(vec![
				tp_sel,
				var_to_tuple(&item),
				tp_neg_one,
			]);
			cs.enforce_constraint(
				lb_sel.clone(),
				vec_lb_unique[i].clone(),
				//lb_sel + lb_item + lb_neg_one.clone()
				lb_four
			)?;
			prod_unique = &prod_unique * &item;
		}

		//4.2 compute the grand prodct of oup_states and ignoring zero 
		//entries
		let sel_oup= oup_states.iter().map(|s|
			&one_var - &is_zero_better(s, &cs).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let mut prod_oup= one_var.clone();
		for i in 0..olen{
			//assert conditional select of item
			//i.e. (1-sel) * (item-1) + sel*(item-oup[i]) = 0
			//i.e. item -1 + sel - sel*oup[i] = 0
			//i.e., sel * oup[i] = sel + item -1
			let item_val = if sel_oup[i].value()?.is_one(){
				oup_states[i].value()?
			} else {F::one()};
			let item = new_var(&cs, item_val);
			let lb_sel = var_to_lb(&sel_oup[i], F::one());
			let tp_sel = var_to_tuple_adv(&sel_oup[i], F::one());
			//let lb_item = var_to_lb(&item, F::one());
			let lb_oup = var_to_lb(&oup_states[i], F::one());
			let lb_four = LinearCombination::<F>(vec![
				tp_sel,
				var_to_tuple(&item),
				tp_neg_one,
			]);
			cs.enforce_constraint(
				lb_sel.clone(),
				lb_oup,
				//lb_sel + lb_item + lb_neg_one.clone()
				lb_four
			)?;
			prod_oup = &prod_oup * &item;
		}
		if b_debug{
			println!("## pack step.  ilen: {}, mlen: {}, olen: {},  r1cs: {}, vars: {}", 
					ilen, mlen, olen,
					cs.num_constraints()-nc, 
					cs.num_witness_variables()-nv
			);
			assert!(cs.is_satisfied().unwrap());
		}

		Ok(())
	}
}

/// Advice for the WordExtract Gadget.
#[derive(Debug)]
pub struct PackFinalAdvice<F:PrimeField + ColEle>{
	/// unique states (padded with 0 at beginning)
	pub unique_states: Vec<F>,
	/// oup_states (final states ONLY, padded with 0 at beginning)
	pub oup_states: Vec<F>,
	/// m_table appearance of unique states
	pub m_table: Vec<F>,
	/// labeling of subtable_id for unique_states, m_table and oup_states
	pub subtbl_id: Vec<F>,
}

impl <F: PrimeField + ColEle> NdAdvice for PackFinalAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField + ColEle> PackFinalAdvice<F>{
	/// Given a sequence of states (no padding), and the their
	/// corresponding b_final flag,identify the final states
	/// and generate the cooresponding m_table as proof.
	///
	/// This is split into two steps:
	/// (1) construct set of unique states (padded with zero)
	/// (2) comress unique states further into final states.
	/// to construct the buffer: capacity_imm is for immediate buffer
	/// and capacity_out is for the vector of final states
	pub fn new(inp_states: &Vec<F>, vec_b_final: &Vec<bool>, 
		capacity_imm: usize, capacity_out: usize, fsm_id: u32 )->
		Result<Self,Error>{
		//1. construct the out_states (all final states
		// and pad zero at the beginning)
		let zero = F::zero();
		assert!(inp_states.len()==vec_b_final.len());
		let mut vec_final_states = inp_states.par_iter().zip(
			vec_b_final.par_iter())
			.filter(|(_, &b)| b).map(|(s,_)| s.clone())
			.collect::<HashSet<F>>().into_iter().collect::<Vec<F>>();
		vec_final_states.sort();
		let set_final_states = vec_final_states.par_iter().map(|&s|
			s).collect::<HashSet<F>>();
		if vec_final_states.len()>capacity_out-1{
			return Err(Error::CapErr(vec![(format!("capacity_out: pack, fsm_id: 0x{:x}", fsm_id), vec_final_states.len()+1)]));
		}
		let vec_final_states = [ 
			&vec![zero; capacity_out - vec_final_states.len()][..],
			&vec_final_states[..],
		].concat();

		//2. construct the immediate states
		let mut vec_imm_states = inp_states.par_iter().map(|&s| s)
			.collect::<HashSet<F>>().into_iter().collect::<Vec<F>>();
		vec_imm_states.sort();
		assert!(vec_imm_states[0]!=zero);
		if vec_imm_states.len()>capacity_imm-1{
			return Err(Error::CapErr(vec![(format!("capacity_imm: pack, fsm_id: 0x{:x}", fsm_id), vec_imm_states.len()+1)]));
		}
		assert!(vec_imm_states.len()<capacity_imm, "imm_states: {} > capacity_imm: {}", vec_imm_states.len(), capacity_imm);
		let vec_imm_states = [
			&vec![zero; capacity_imm - vec_imm_states.len()][..],
			&vec_imm_states
		].concat();

		//3. generate the m_table
		let m_table = gen_m_table(inp_states, &vec_imm_states);
		assert!(m_table.len()==vec_imm_states.len());

		//4. construct the subtbl_id
		// it has 3 parts:
		// unique_states: real identifation of whether it's 
		//           final or not final (size: imm_buf_len)
		// oup_states: actually 0 (don't care as unique states is superset
		//    we'll run lkup (size: final_states_len)
		// m_table: don't care (size: final_states_len)
		let f_non_final = F::from(fsm_id + 1); 
		let f_final = F::from(fsm_id + 2); 
		let frg = F::from(RANGE2 as u32);
		let sid_unique_states = vec_imm_states.par_iter().map(|s|{
			if s.is_zero() {frg}
			else{
				if set_final_states.contains(s){ f_final } else {f_non_final}
			}
		}).collect::<Vec<F>>();
		assert!(sid_unique_states.len()==capacity_imm);
		let subtbl_id = [
			&sid_unique_states[..], //for imm_states
			&vec![zero; capacity_imm][..], //for m_table
			&vec![zero; capacity_out][..], //for oup_states (final only)
		].concat();

		Ok(Self{unique_states: vec_imm_states, oup_states: vec_final_states, 
			m_table, subtbl_id})
	}

	/// Given the same info as new(), estimate the
	/// capacity needed (capacity_imm, capacity_out)
	pub fn compute_capacity(
		inp_states: &Vec<F>, 
		vec_b_final: &Vec<bool>, 
	)-> (usize, usize){
		//1. construct the output states (all final states)
		assert!(inp_states.len()==vec_b_final.len());
		let vec_final_states = inp_states.par_iter().zip(
			vec_b_final.par_iter())
			.filter(|(_, &b)| b).map(|(s,_)| s.clone())
			.collect::<HashSet<F>>().into_iter().collect::<Vec<F>>();
		let set_final_states = vec_final_states.par_iter().map(|&s|
			s).collect::<HashSet<F>>();
		let capacity_out = set_final_states.len() + 1; //leave one for 0 entry

		//2. estimate the immedaite states needed
		let vec_imm_states = inp_states.par_iter().map(|&s| s)
			.collect::<HashSet<F>>().into_iter().collect::<Vec<F>>();
		let capacity_imm = vec_imm_states.len() + 1;

		//3. no need to generate m_table, it's the same size of
		//of vec_imm_states

		//4. no need to construct subtbl_id its size is
		//the sum of imm_states and output_states
		(capacity_out, capacity_imm)
	}
}

#[cfg(test)]
pub mod tests_pack_gadget{
	use std::{sync::Arc};
	use ark_bn254::{Fr};
	use crate::gadgets::pack::{PackFinalGadget,PackFinalAdvice};
	use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget;
	use ark_ff::{Zero};

	#[test]
	fn test_pack(){
		//1. create final states and then non-final states
		let msf_id:u32 = 0x10001001;
		//let f_nonfinal_id = Fr::from(msf_id + 1);
		//let f_final_id = Fr::from(msf_id + 2);
		let vec_final = vec![2u32, 3u32, 4u32, 5u32].into_iter()
			.map(|x| Fr::from(x)).collect::<Vec<Fr>>();
		let vec_non_final = vec![101u32, 123u32, 134u32, 133u32, 201u32, 211u32, 212u32, 255u32].into_iter().map(|x| Fr::from(x)).collect::<Vec<Fr>>();
		let inp_size = 100;
		let imm_buf_len = 20;
		let capacity = 10; //final states_len
		//ratio is final is about 1/4
		let mut inp_states = vec![];
		let mut vec_b_final = vec![]; 
		for i in 0..inp_size{
			let ele = if i%4==0{vec_final[(i*234234+2341)%vec_final.len()]}
				else{vec_non_final[(i*828342187+12183)%vec_non_final.len()]};
			inp_states.push(ele);
			vec_b_final.push( i%4 ==0 ); //i%4==0 is final
		}
		let gadget= PackFinalGadget::<Fr>
			::new(inp_states.len(), imm_buf_len, capacity, msf_id);
		let rg = Arc::new(gadget);

		//2. build the advice
		let mut adv = 
			PackFinalAdvice::new(&inp_states, &vec_b_final, 
				imm_buf_len, capacity, msf_id).unwrap();
		let inp = vec![];
		let oup = vec![];
		let data = vec![
			inp_states.clone(),
			adv.unique_states,
			adv.m_table,
			adv.oup_states,
		].concat();
		assert!(data.len()==capacity + 2*imm_buf_len + inp_states.len());
		let to_pad_size = inp.len() + oup.len() + data.len() 
			- adv.subtbl_id.len();
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
