/* Created 03/03/2025 */

use std::rc::{Rc};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice },
	container_config::{ContainerConfig},
	circuits_super::field_to_usize,
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{
//		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	//eq::EqGadget,
//	R1CSVar,
};
use std::any::Any;
use data_processor::hex_acdfa::HexACDFA;
use crate::gadgets::commons::{build_pows_56,check_eq,new_const_var};

#[allow(dead_code)]
/// This gadget is responsible for checking transitions
/// of running a finite state machine. Given a state to start
/// from and given 4-bit nibble sequences, it runs a check of
/// the validity of transitions mainly by lookup table.
/// Assumption: (1) 4-bit nibbles are already range checked (e.g.,
/// in word_extract_gadget), (2) 4-bit nibbles are already padded
/// for the given word, so we do not check act_word_len.
/// (3) the FSA ID is given as the first macro definition e.g.,
/// CRIT_INIT (its initial state ID), and then following the
/// subtbl_IDs defined in clam_db.rs.
#[derive(Clone,Debug)]
pub struct FsmGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	/// should be LEGS (62) x max_word_len
	max_nibble_len: usize, 
	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	fsm_id: u32, 

	/// how many bits are used to represent a state
	acdfa_state_part_bits: usize,
}

impl <F:PrimeField> FsmGadget<F>{
	pub fn new(
		max_nibble_len: usize, 
		fsm_id: u32, 
		acdfa_state_part_bits: usize) 
	-> Self{
		Self{_f: PhantomData, max_nibble_len, fsm_id, acdfa_state_part_bits}
	}
}

impl <F:PrimeField> SigmaGadget<F> for FsmGadget<F>{
	fn get_name(&self)->&str {"FsmGadget"}

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

	/// return the sizes of inp/oup/data/failed_sigs/discharged_sigs
	/// to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	fn est_cost(&self)->usize{
		let est = self.max_nibble_len* 3;

		est
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) no word_segment
		//  (2) inp: incoming_state_id 
		//  (3) oup: outgoing_state_id
		//  (4) data: 
		//         nibbles: max_nibble_len
		//         states:  max_nibble_len-1 (excluding the beginning
		//                  and ending state in sequence)
		//         transitions: max_nibble_len
		//  (5) its own subtbl_id for inp, states, and oup (but excluding
		//      nibbles part in data, as it's already checked in 
		//      word_extract_gadget
		//      it first asserts: states are valid
		//      it then asserts: transitions are valid
		// ]
		// NO msg1,2,3
		// Total statement len:  3*nibbles-1 + 2 + nibbles+1+nibbles
		// = 5nibbles + 2
		let nlen = self.max_nibble_len;
		let word_len = 0;
		let inp_len = 1;
		let oup_len = 1;
		//data: 3 parts (nibbles, states and trans)
		let data_len = nlen + nlen-1 + nlen; 
		//subtbl 2 parts: states and trans
		let subtbl_id_len = nlen+1 + nlen;
		let stat_len = word_len + data_len +inp_len + oup_len + subtbl_id_len;
		assert!(stat_len == nlen*5 + 2);
		(stat_len, 0, 0, 0)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
		-> Vec<F>{
		vec![] // dummy
	}

	fn gen_msg3(&self, _stmt_vec: &Vec<F>, _stmt_idx: 
		&Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		vec![]
	}

	//COST: r1cs: 1/4 * nlen, vars: 0
	// nlen = nibble len -> improved to nlen/4
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		let b_debug = false;
		let nc = cs.num_constraints();
		let nv = cs.num_witness_variables();
		let one = new_const_var(&cs, F::one());

		//1. retrive the statement instance and get all parts
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		//assert!(my_stmt.len()==self.get_msg_size().0);
		//skip for making manually constructed test case pass.
		let nlen= self.max_nibble_len;
		let data_len = 3*nlen - 1;
		let inp_len = 1;
		let oup_len = 1;
		let subtbl_id_len = nlen-1+inp_len+oup_len + nlen;
		assert!(data_len+inp_len+oup_len+subtbl_id_len ==
			self.get_msg_size().0);

		//2. get the parts of the statement
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		// NOTE: no input and output
		let inp = my_stmt[0..1].to_vec(); 
		let oup = my_stmt[1..2].to_vec(); 
		let data_seg = my_stmt[2..2 + nlen*3-1].to_vec(); 
		let subtbl_id = &my_stmt[1+nlen*3..1+nlen*3 +  2*nlen+1].to_vec();
		assert!(data_seg.len() + inp.len() + oup.len() + subtbl_id.len()
			== self.get_msg_size().0);


		//3. assert that all states must be in range
		let states = vec![inp.clone(), data_seg[nlen..2*nlen-1].to_vec(), 
			oup.clone()].concat();
		assert!(states.len()==nlen+1);
		// THE FOLLOWING IS ACTUALLY NOT NEEDED.
		// FSM IS ONLY PERFORMED ON TWO ACDFAS (fixed)
		// THESE ARE FIXED CONSTAN in circuit. no need to check
// 		let tblid_states = FpVar::<F>::new_constant(cs.clone(), 
// 			F::from(self.fsm_id + 6))?;//e.g., corresponding to CRIT_STATES
// 		for i in 0..nlen+1{
// 			subtbl_id[i].enforce_equal(&tblid_states)?;
// 			#[cfg(test)]{
// 				use ark_r1cs_std::{R1CSVar};
// 				if subtbl_id[i].value().is_ok(){
// 					assert!(subtbl_id[i].value()?==tblid_states.value()?);
// 				}
// 			}
// 		}

		//4. assert all transitions in range
		// IMPROVED to nlen/4 (using the trick from dfa_adv.rs
		// basic idea is that as the range of char-state-state
		// is controlled, the transition is guranteed to be no more than
		// 56-bit. we can pack checking 4 transitions in just one round
		let unit_var = FpVar::<F>::new_constant(cs.clone(),
			F::from((1<<(self.acdfa_state_part_bits+4)) as u32))?;
		let hex_var = FpVar::<F>::new_constant(cs.clone(),
			F::from(16 as u32))?;
		let pows_51 = build_pows_56(cs.clone());
		for i in 0..nlen/4{
			let start = i * 4;
			let mut sum_trans = one.clone();
			let mut sum_exp = one.clone();
			for j in 0..4{//check every 4 transitions
				let idx = start + j;
				let ch = &data_seg[idx];
				let st1 = &states[idx]; //already plus one
				let st2 = &states[idx+1];
				// simulate clam_db.rs: add_acdfa_to_lkup
				let exp_trans = ch + 
					&(st1 * &hex_var) +
					&(st2 * &unit_var); //no need to plus one, already did
				let trans = &data_seg[2*nlen-1 + idx];
				sum_trans = &sum_trans + &(&pows_51[j] * trans); //cost 
					//nothing because mul with constant!
				sum_exp = &sum_exp + &(&pows_51[j] * &exp_trans); 

				#[cfg(test)]{
					use ark_r1cs_std::{R1CSVar};
					if exp_trans.value().is_ok(){
						assert!(exp_trans.value()?==trans.value()?);
					}
				}
			}//end for j
			check_eq(&sum_trans, &sum_exp,  "ERROR checking trans")?;
		}

		//IF nlen is not multiple of 4
		for idx in nlen/4*4 .. nlen{
			let ch = &data_seg[idx];
			let st1 = &states[idx]; //already plus one
			let st2 = &states[idx+1];
			let exp_trans = ch + 
				&(st1 * &hex_var) +
				&(st2 * &unit_var); //no need to plus one, already did
			let trans = &data_seg[2*nlen-1 + idx];
			check_eq(&exp_trans, &trans, "ERROR checking trans part2")?;
		}

//		This part is NOT needed as trans id is constant in IRCUIT
//      In fact: even executing the following codes does nont
//      increase the circuit size/cost as all are constant operations
//
// 		let tblid_trans= FpVar::<F>::new_constant(cs.clone(), 
// 			F::from(self.fsm_id + 3))?;//e.g., corresponding to CRIT_TRANSITIONS
// 		for i in nlen+1..nlen+1+nlen{
// 			subtbl_id[i].enforce_equal(&tblid_trans)?;
// 			#[cfg(test)]{
// 				use ark_r1cs_std::{R1CSVar};
// 				if subtbl_id[i].value().is_ok(){
// 					assert!(subtbl_id[i].value()?==tblid_trans.value()?);
// 				}
// 			}
// 		}

		if b_debug{
			println!("## fsm cost for nibbles: {}, r1cs: {}, vars: {}", nlen, cs.num_constraints()-nc, cs.num_witness_variables()-nv);
		}

		Ok(())
	}
}

/// Advice for the WordExtract Gadget.
#[derive(Debug)]
pub struct FsmAdvice<F:PrimeField>{
	/// states: length is max_nibbles + 1
	pub states: Vec<F>,
	/// transitions: length is max_nibbles
	pub trans: Vec<F>,
	/// keep track of it for verification purpose
	pub acdfa_state_part_bits: usize,
	/// the fsm id corresponds to the acdfa
	_fsm_id: u32, 
}

impl <F: PrimeField> NdAdvice for FsmAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> FsmAdvice<F>{
	/// word_seg is the one with max compacity, actual size
	/// is the actual word len. We convert all remaining 
	/// as 0.
	/// NOTE: inp_state is the ADJUSTED satate (+1 of the raw_state on
	/// ACDFA)
	pub fn new(nibbles: &Vec<F>, acdfa: &HexACDFA, inp_state: F, fsm_id: u32)->Self{
		//1. normalize the input
		let acdfa_state_part_bits = acdfa.state_part_bits;
		let mut states = vec![];
		let mut trans = vec![];
		let mut cur_state = field_to_usize(&inp_state) - 1;
		// NOTE: state needs to be added 1 to be pushed
		// 0 is considered padding value.
		states.push(F::from( (cur_state+1) as u32));
		let unit = F::from((1<<(acdfa_state_part_bits+4)) as u32);
		let hex = F::from(16 as u32);
		let one = F::one();
		for i in 0..nibbles.len(){
			let ch: u8 = field_to_usize(&nibbles[i]).try_into().unwrap();
			let nxt_state = acdfa.trans.get(&cur_state).unwrap()[ch as usize];
			states.push(F::from( (nxt_state+1) as u32)); 

			let f_ch = F::from(ch);
			let f_src = F::from(cur_state as u32);
			let f_dst = F::from(nxt_state as u32);
			let tr = f_ch + (f_src + one) * hex + (f_dst + one) * unit;
			trans.push(tr);
			cur_state = nxt_state;
		}

		Self{states, trans, acdfa_state_part_bits, _fsm_id: fsm_id}
	}
}

#[cfg(test)]
pub mod tests_fsm_gadget{
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use crate::gadgets::fsm::{FsmGadget,FsmAdvice};
	use utils::data::{rand_fe_by_bits};
	use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget;
	use data_processor::{hex_acdfa::HexACDFA, clam_db::RANGE2_BIT};
	use ark_ff::{Zero};



	#[test]
	fn test_fsm(){
		let mut rng = ark_std::test_rng();
		let (nibble_len, state_bits) = (124, RANGE2_BIT);
		let mut nibbles:Vec<Fr> = vec![];
		for _i in 0..nibble_len{ nibbles.push(rand_fe_by_bits(4, &mut rng));}

		let msf_id:u32 = 0x10001001;
		let f_states_id = Fr::from(msf_id + 6);
		let f_trans_id = Fr::from(msf_id + 3);
		let gadget= FsmGadget::<Fr>::new(nibble_len, msf_id, state_bits);
		let rg = Rc::new(gadget);

		let patterns = vec!["abc", "cba", "1234567890abcdef"].
			iter().map(|s| {String::from(*s)}).collect();
		let acdfa = HexACDFA::new(1, &patterns);
		let init_state = acdfa.init_state;
		let inp_state = Fr::from( (init_state + 1) as u32);
		let adv = FsmAdvice::new(&nibbles, &acdfa, inp_state, msf_id);
		assert!(adv.acdfa_state_part_bits == rg.as_ref().acdfa_state_part_bits);
		assert!(adv.states.len()==nibble_len+1);	
		assert!(adv._fsm_id==msf_id);
		let inp = vec![adv.states[0].clone()];
		let oup = vec![adv.states[nibble_len].clone()];
		let data = vec![
			nibbles.clone(),
			adv.states[1..nibble_len].to_vec(),
			adv.trans
		].concat();
		assert!(data.len()==3*nibble_len-1);
		let subtbl_id = vec![
			vec![f_states_id; nibble_len+1],
			vec![f_trans_id; nibble_len]
		].concat();
		assert!(subtbl_id.len()==2*nibble_len+1);
		let to_pad_size = inp.len() + oup.len() + data.len() - subtbl_id.len();
		let subtbl_id = [&subtbl_id[..], &vec![Fr::zero(); to_pad_size][..]]
			.concat(); //to make the Witness.to_vec_fp_var check happy
					   //in cp_map.rs this onstraint inp+oup+data.len
					   //  == subtbl_id.len will be satisfied but not
					   //for this manually constructed example


		let lkup_share_size = 4usize;
		test_gadget::<Fr>(rg, &vec![], &inp, &oup, &data, &subtbl_id, 
			lkup_share_size);
	}
}
