/* Created 07/16/2025, Completed: 07/27/2025 */

//! This module dischages a nibble sequence against a collection
//! of DFAs (each one-to-one corresponding to a subsignature),
//! and reports the discharging status for each subsig.
//! It is a n-concurrent parallel version of the fsm component.
//! Then it assembles subsig result and report the discharge (via DFA)
//! result for sigs.

use rayon::iter::{ParallelIterator,IntoParallelIterator,IntoParallelRefIterator};
use std::{rc::{Rc},cell::{RefCell},collections::{HashMap}};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity,DischargeSigInfo},
	container_config::{ContainerConfig},
	circuits_super::field_to_usize,
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{
		//FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};
use std::{any::Any, sync::{Arc}};
use data_processor::{
	clam_db::{ClamavDB, RANGE2_BIT, RANGE2,CHAR_MAP,
		//STORE_SUBSIG,
	},
	type_def::{TriVal,ClamavSig},
	fsa_utils::{build_trap_dfa},
	hex_acdfa::{HexACDFA},
};
use utils::{data::{u8_to_hex}};
use crate::gadgets::{
	commons::{mix_vec,new_const_var, check_eq,encode_cols_better,gen_m_table,
		encode_cols_var_adv_better },
	traits::{Container,
		Col,
		IDX_WORD, IDX_INP,IDX_DATA, IDX_DISCHARGED_SIGS,
		IDX_SI_INP, 
		IDX_OUP, 
		IDX_SI_OUP, 
		IDX_SI_DATA, ComponentAdvice
	},
	db::{
		assert_logup,
		//verify_encoded_table,
		//assert_well_formed_sorted,
		//col_to_sorted_set, 
		//verify_col_to_sorted_set, 
		//tbl_filtered_to_sorted_tbl, 
		//verify_tbl_filtered_to_sorted_tbl,
		//tbl_to_sorted_tbl, 
		//verify_tbl_to_sorted_tbl, 
		//tbl_left_join, 
		//verify_tbl_left_join
	},
};
use rustomaton::dfa::DFA;

// -----------------------------------------------
//		Structs
// -----------------------------------------------

/// Capacity of the gadget
#[derive(Clone,Debug)]
pub struct DfaAdvCapacity{
	/// should be LEGS (62) x max_word_len
	pub max_nibble_len: usize, 

	/// the number of subsigs determines the number of 
	/// DFAs to run
	pub subsigs: usize,

	/// number of sigs
	pub sigs: usize,
}

/// Advice for the WordExtract Gadget.
#[derive(Clone,Debug)]
pub struct DfaAdvAdvice<F:PrimeField>{
	/// len must match capacity.subsigs
	pub inp_subsigs: Vec<F>,

	/// 1-1 correspoding to inp_subsigs
	pub v_dfa: Vec<Arc<DFA<char>>>,

	/// the fsm_ids of dfa
	pub v_dfa_id: Vec<F>,

	/// the input states for each DFA (note since this is
	/// streaming, for the 1sst segment it's the initial state
	/// of DFA, and then it's the last state of the previous seg)
	/// NOTE: all state id are stored as "1+real_state_id"
	pub f_inp_states: Vec<F>,

	/// the statement container object which is serialized to a vector
	/// of statement
	pub stmt_container: Rc<RefCell<Container<F>>>,

	/// capacity
	pub capacity: DfaAdvCapacity,
}

#[allow(dead_code)]
/// This gadget is responsible for checking transitions
/// of running a finite state machine. 
#[derive(Clone,Debug)]
pub struct DfaAdvGadget<F:PrimeField>{ 
	/// the capacity
	pub capacity: DfaAdvCapacity,

	// will be set when set_container_cfg is called
	pub cfgs_context: Option<Rc<Vec<ContainerConfig>>>,
	// dummy_cfg is used when cfgs_context is not ready yet
	pub dummy_cfg: ContainerConfig,
	pub my_idx_in_context: Option<usize>,
	_f: PhantomData<F>,

}


// ---------------------------------------------
//            Implementations
// ---------------------------------------------
impl Capacity for DfaAdvCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		let other = r_other.as_any().downcast_ref::<DfaAdvCapacity>()
			.expect("downcast err"); 
		self.max_nibble_len >= other.max_nibble_len &&
		self.subsigs>= other.subsigs &&
		self.sigs>= other.sigs
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(DfaAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			subsigs: self.subsigs,
			sigs: self.sigs,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField> NdAdvice for DfaAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> ComponentAdvice<F> for DfaAdvAdvice<F>{
	fn get_container(&self)->Rc<RefCell<Container<F>>>{
		self.stmt_container.clone()
	}
}

impl <F: PrimeField> DfaAdvAdvice<F>{
	/// Given nibbles and a COLLECTION of subsigs (and their DFA),
	/// produce the state reached by each subsig (in its DFA)
	/// Input: (v_input_states)
	pub fn new(
		nibbles: &Vec<F>, 
		inp_subsigs: &Vec<F>,  //will be padded to full #subsigs by capacity
		v_dfa_id: &Vec<F>, //the ids generaed by gen_dfa_id in clamdb
		v_dfa: &Vec<Arc<DFA<char>>>, //1-1 corresponding to inp_subsigs
		inp_states: &Vec<F>,  //it's already adjusted (starting from 1)
		capacity: &DfaAdvCapacity, 
		inp_sigs: &Vec<F>, //sigs to discharge 
		discharge_infos: &Vec<DischargeSigInfo>, //must match inp_sigs
					//extracting the dnf to the concat of inp_subsigs
		v_sig_obj: &Vec<Arc<ClamavSig>>, //needs to cover all inp_sigs
		sig_to_id: &HashMap<String,usize>,
	) ->Self{
		let stmt_container = Container::<F>::new("dfa_adv_stmt");
		//1. padding the input when necessary
		let dummy_fsm_id = F::from(ClamavDB::<F>::dfa_id(0, 0));
		let dummy_dfa = Arc::new(build_trap_dfa());
		let dummy_info = DischargeSigInfo{
				sig_name: "none".to_string(),
				b_success: false,
				min_cost: 0,
				min_dnf_id: 0,
				subsig_ids: vec![0],
				subsig_igc: vec![false]
			}; 
		
		let n = capacity.subsigs;
		let n1 = inp_subsigs.len();
		assert!(n>=n1, "capacity.subsigs: {} < inp_subsigs: {}. adjust DfaCapacity.subsigs", n, n1);
		let n2 = n - n1;
		let zero = F::zero();
		assert!(v_dfa_id.len()==n1 && v_dfa.len()==n1);
		let inp_subsigs = [&inp_subsigs[..], &vec![zero;n2][..]]
			.concat();
		let inp_sigs = [&inp_sigs[..], 
			&vec![zero;capacity.sigs-inp_sigs.len()][..]].concat();
		let discharge_infos= [&discharge_infos[..], 
			&vec![dummy_info;capacity.sigs-discharge_infos.len()][..]].concat();
		assert!(inp_sigs.len()==capacity.sigs);
		assert!(discharge_infos.len()==capacity.sigs);

		let v_dfa_id = [&v_dfa_id[..], &vec![dummy_fsm_id;n2][..]].concat();
		//note for dfa, clone is low cost
		let v_dfa = [&v_dfa[..], &vec![dummy_dfa.clone();n2][..]].concat();
		let inp_states = [&inp_states[..], &vec![inp_states[0];n2][..]]
			.concat();

		//2. construct the fsm_acc combo which has the 
		// (partial and current) evaluation of each subsig
		// stored in (subsig, res) columns. This is basically
		// depending on the state reached by the nibbles in
		// each DFA.
		let (mul_fsm_acc, subsig_res) = Self::gen_mul_fsm_acc_combo(
			nibbles, &inp_subsigs, &v_dfa_id, &v_dfa, &inp_states, capacity
		);
		stmt_container.borrow_mut().add_container(mul_fsm_acc);

		//3. construct the sig_res_combo
		let sig_res_combo = Self::gen_discharge_sig_combo(
			&inp_sigs, 
			&inp_subsigs, 
			&subsig_res, 
			&capacity,
			&v_sig_obj,
			&discharge_infos,
			&sig_to_id
		);
		stmt_container.borrow_mut().add_container(sig_res_combo);

		Self{
			capacity: Clone::clone(capacity), 
			inp_subsigs: inp_subsigs.clone(),
			v_dfa_id: v_dfa_id.clone(),
			v_dfa: v_dfa.clone(),
			f_inp_states: inp_states.clone(),
			stmt_container
		}
	}

	/// Given the input generates the container of the following
	/// structure: root level name: mul_fsm_acc
	/// It contains final result in two columns:
	/// (subsigs, res) where res is the TriVal result based
	/// on the last state in the trace. Notice that it
	/// runs multiple DFAs for the same nibble pices concurrently
	/// Return:
	/// (1) the proof combo, 
	/// (2) the subsig_res which corresponds to inp_subsigs)
	#[allow(dead_code)]
	fn gen_mul_fsm_acc_combo(
		nibbles: &Vec<F>, 
		inp_subsigs: &Vec<F>,  //will be padded to full #subsigs by capacity
		v_dfa_id: &Vec<F>, //the ids generaed by gen_dfa_id in clamdb
		v_dfa: &Vec<Arc<DFA<char>>>, //1-1 corresponding to inp_subsigs
		inp_states: &Vec<F>,
		capacity: &DfaAdvCapacity) 
	-> (Rc<RefCell<Container<F>>>,Vec<F>){
		//0. set up data
		let res = Container::<F>::new("mul_fsm_acc");
		let (m, nlen) = (capacity.subsigs, capacity.max_nibble_len);
		let (_one,zero) = (F::one(),F::zero());
		assert!(v_dfa_id.len()==m && v_dfa.len()==m && inp_subsigs.len()==m);
		assert!(nibbles.len()==nlen);

		//1. walk nibbles through transition of each DFA
		//this will be sequential, in practice, it's ok
		// NOTE: saved_states are adjused (by +1)
		// when query DFA, recover them by -1
		//1.1 buld all info using as much parallelism as possible
		let v2d = (0..m).collect::<Vec<_>>().into_par_iter().map(|j|{
			//for each dfa
			let dfa = &v_dfa[j];
			let fsm_id = v_dfa_id[j];
			let mut src = field_to_usize(&inp_states[j]) - 1;
			let mut v_states = vec![zero; nlen + 1];
			let mut v_trans = vec![zero; nlen];
			v_states[0] = F::from((src+1) as u32);
			let f_id_state = fsm_id + F::from(6u32);
			let f_id_trans= fsm_id + F::from(3u32);
			//sequentially walk nibbles through DFA
			let s_nibbles = nibbles.iter().map(|n| field_to_usize(n) as u8)
				.collect::<Vec<u8>>();
			let s2 = u8_to_hex(&s_nibbles).as_bytes().to_vec().iter()
				.map(|s| *s as char).collect::<Vec<char>>();
			let mut sid_nibbles = vec![zero;nibbles.len()];
			let f_map = F::from(CHAR_MAP as u32);
			for i in 0..nibbles.len(){
				let ch = s2[i];
				let dst = dfa.transitions[src].get(&ch);
				assert!(dst.is_some());
				let dst = dst.unwrap();
				let ch_usize = ch as usize;
				let trans = ch_usize +
					 ((src+1)<<4) + ((dst+1)<<(4+RANGE2_BIT));
				v_states[i+1] = F::from((dst+1) as u32);
				v_trans[i] = F::from(trans as u64);
				src = *dst;
				sid_nibbles[i] = F::from(ch as u8) + f_map;
			}
			let v_sid_states = vec![f_id_state; nlen+1];
			let v_sid_trans = vec![f_id_trans; nlen];
			(v_states, v_trans, v_sid_states, v_sid_trans,sid_nibbles)
		}).collect::<Vec<(Vec<F>,Vec<F>,Vec<F>,Vec<F>,Vec<F>)>>();

		//1.2 assembl slice references for later mixing.
		let v2d_states = v2d.iter().map(|v| &v.0[..]).collect::<Vec<&[F]>>();
		let v2d_trans= v2d.iter().map(|v| &v.1[..]).collect::<Vec<&[F]>>();
		let v2d_sid_states= v2d.iter().map(|v| &v.2[..]).collect::<Vec<&[F]>>();
		let v2d_sid_trans= v2d.iter().map(|v| &v.3[..]).collect::<Vec<&[F]>>();
		let v2d_sid_nibbles= v2d.iter().map(|v| &v.4[..]).collect::<Vec<&[F]>>();

		let states = mix_vec(&v2d_states);
		let trans = mix_vec(&v2d_trans);
		let sid_states = mix_vec(&v2d_sid_states);
		let sid_trans = mix_vec(&v2d_sid_trans);
		let sid_nibbles = &v2d_sid_nibbles[0];
		assert!(states.len()==m*(nlen+1));
		assert!(sid_states.len()==m*(nlen+1));
		assert!(trans.len()==m*nlen);
		assert!(sid_trans.len()==m*nlen);

		//1.3 build v_sig_id and v_raw_subsig_id, v_dfa_id
		//and add them into combo
		let n = capacity.subsigs;
		assert!(inp_subsigs.len()==n);
		assert!(v_dfa_id.len()==n);
		let frg = F::from(RANGE2);
		let v_sig = inp_subsigs.iter().map(|&ssid| 
			extract_sigid(ssid).0
		).collect::<Vec<F>>();
		let v_raw_subsig = inp_subsigs.iter().map(|&ssid| 
			extract_sigid(ssid).1
		).collect::<Vec<F>>();
		res.borrow_mut().add_col(Col::<F>::new(inp_subsigs.to_vec(),
			"v_subsig",IDX_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(v_sig, "v_sig",IDX_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(v_raw_subsig, "v_raw_subsig",
			IDX_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(v_dfa_id.to_vec(), "v_dfa_id",
			IDX_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(vec![frg;n], "sid_v_sig",
			IDX_SI_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(vec![frg;n], "sid_v_subsig",
			IDX_SI_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(vec![frg;n], "sid_v_raw_subsig",
			IDX_SI_DATA)); 
		res.borrow_mut().add_col(Col::<F>::new(vec![zero;n], "sid_v_dfa_id",
			IDX_SI_DATA)); 

		//1.4 add columns related to inp/mid/oup states
		let col_inp_state = Col::<F>::new(states[0..m].to_vec(),
			"inp_state",IDX_INP);
		let col_si_inp_state = Col::<F>::new(sid_states[0..m].to_vec(),
			"si_inp_state",IDX_SI_INP);

		let col_mid_states = Col::<F>::new(states[m..m*nlen].to_vec(),
			"mid_states", IDX_DATA);
		let col_si_mid_states = Col::<F>::new(sid_states[m..m*nlen]
			.to_vec(), "si_mid_states", IDX_SI_DATA);

		let col_oup_state = Col::<F>::new(states[m*nlen..m*(nlen+1)].to_vec(),
			"oup_state",IDX_OUP);
		let col_si_oup_state = Col::<F>::new(sid_states[m*nlen..m*(nlen+1)]
			.to_vec(), "si_oup_state",IDX_SI_OUP);
		let raw_states = &states;

		let states = Container::concat_cols(
			vec![col_inp_state, col_mid_states, col_oup_state], "states");
		let si_states = Container::concat_cols(vec![col_si_inp_state, 
			col_si_mid_states, col_si_oup_state], "si_states");
		res.borrow_mut().add_container(states); //remove clone later
		res.borrow_mut().add_container(si_states);


		//1.3. the transitions
		let col_trans = Col::<F>::new(trans, "trans", IDX_DATA);
		let col_si_trans = Col::<F>::new(sid_trans, "si_trans", IDX_SI_DATA);
		res.borrow_mut().add_col(col_trans);
		res.borrow_mut().add_col(col_si_trans);

		//1.4 the nibbles (LATER when reconstructed, it is 
		// retrieved from previous word_extract_adv gadget
		let col_nibbles = Col::<F>::new_external(nibbles.to_vec(), 
			"nibbles", IDX_DATA, -1, "word_extract_stmt nibbles");
		let col_si_nibbles = Col::<F>::new_external(sid_nibbles.to_vec(),
			"si_nibbles", IDX_SI_DATA, -1, 
			"word_extract_stmt si_nibbles");
		#[cfg(test)]{assert!(col_nibbles.borrow().data.len()==nlen);}
		#[cfg(test)]{assert!(col_si_nibbles.borrow().data.len()==nlen);}


		res.borrow_mut().add_col(col_nibbles);
		res.borrow_mut().add_col(col_si_nibbles);

		//1.4 add the 3 columns: subsig_res, oup_states_copy, si_opu_states_copy
		// here subsig_res is TriVal::False if oup_state is non-final state
		// otherwise it's set to true. We use si_oup_states_copy to
		// mark whether it's a final state (and it's earlier preprocessed
		// in lkup db). Thus, the mapping from a state to whether final
		// or not is handled by lkup.
		let f_true = F::from(TriVal::True as u8); //val 1
		let f_false= F::from(TriVal::False as u8); //val 2
		let subsig_res = raw_states[m*nlen..m*(nlen+1)].iter().enumerate()
			.map(|(i,s)|{
				let u_state = field_to_usize(s) - 1; //real state value
				let res = if v_dfa[i].finals.contains(&u_state) {f_true} 
					else {f_false};
				res
			}).collect::<Vec<F>>();
		assert!(subsig_res.len()==m);
		let sid_oup_state_copy = subsig_res.iter().enumerate()
			.map(|(i,res)|{
			let tbl_id = v_dfa_id[i];
			let nonfinal_tbl_id = tbl_id+F::one();
			let final_tbl_id = tbl_id+F::from(2u32);

			if *res==f_true {final_tbl_id} else {nonfinal_tbl_id} 
		}).collect::<Vec<F>>();

		res.borrow_mut().add_col(Col::<F>::new(raw_states[m*nlen..m*(nlen+1)]
			.to_vec(), "oup_state_copy",IDX_DATA));
		res.borrow_mut().add_col(Col::<F>::new(sid_oup_state_copy,
			"si_oup_state_copy",IDX_SI_DATA));
		res.borrow_mut().add_col(Col::<F>::new(subsig_res.clone(),
			"subsig_res",IDX_DATA));
		res.borrow_mut().add_col(Col::<F>::new(vec![zero;m],
			"si_subsig_res",IDX_SI_DATA)); //don't care as they'll be TriVal


		(res, subsig_res)
	}

	/// This module is adapted from the one in compute_sig_adv.rs
	/// Given the final result of subsig,
	/// use the EvalDNF information to discharge sig.
	/// Basic idea: each sig has a collection of EvalDNF (see type_def.rs)
	/// E.g., (1|2) & (3|4)
	/// It has two DNFs: (1|2) and (3|4)
	/// the Word Discharge Info has already pointed which one has
	/// lower cst to discharge, e.g., let it be (1|2).
	/// the combo needs to show that both subsigs 1 and 2 are 
	/// discharged (as False).
	/// 
	/// Proof Structure (table)
	/// sig - eval_dnf_id - step - count - subsig - res
	/// where the (subsig,res) is from the gen_synsis_subsig_combo.
	/// HERE: all sigs need to be discharged (they will be
	///   the list of sigs to be reported as "discharged").
	#[allow(dead_code)]
	fn gen_discharge_sig_combo(
		inp_sigs: &Vec<F>,
		inp_subsigs: &Vec<F>,
		subsig_result: &Vec<F>,
		capacity: &DfaAdvCapacity,
		v_sigs: &Vec<Arc<ClamavSig>>, //required to COVER inp_sigs
		discharge_infos: &Vec<DischargeSigInfo>, //must match inp_sigs
					//extracting the dnf to the concat of inp_subsigs
		sig_to_id: &HashMap<String,usize>,
	)->Rc<RefCell<Container<F>>>{
		let zero = F::zero();
		let frg = F::from(RANGE2);
		let res = Container::<F>::new("sig_res_combo");
		let n = capacity.subsigs;
		assert!(inp_subsigs.len()==n);
		assert!(subsig_result.len()==n); 
		assert!(inp_sigs.len()==capacity.sigs);

		//1. from the discharge info, build the proof table
		// sig - eval_dnf_id - step - count - subsig (expect res to be
		// TriVal::False)
		// Special note: the subsig/res in this talbe is DIFFERENT
		// from the subsig/res in the gen_synthesis_subsig_res (because
		// here, we do NOT include the sub-components of a subsig (thus
		// resulting a shorter list of subsigs and with different structure)
		// we have to run a LOOKUP to retrieve the result values from
		// the previous combo in step 2.
		// NOTE: we pad the size to #subsigs because in real data
		// vast majority are regular_regex 
		// (not Counterh of SubsigCounterConstraint)
		assert!(discharge_infos.len()==inp_sigs.len());
		for i in 0..discharge_infos.len() {
			let name = &discharge_infos[i].sig_name;
			let sig_id = if name =="none" {zero} else {
				F::from(*sig_to_id.get(name)
					.expect(&format!("cannot find sig: {}", name)) as u64)
			};
			assert!(sig_id == inp_sigs[i]);
		}
		let info_ts = discharge_infos.par_iter().map(|info|{
			let (sig_id, vec_ssid) = if info.sig_name=="none" {//dummy case 
				//don't genreate [1] instead generate 0
				(zero, vec![])
			}else{
				let sig_objs = v_sigs.iter().filter(|s| s.name==info.sig_name)
					.map(|s| s.clone())//low cost of Arc clone
					.collect::<Vec<Arc<ClamavSig>>>();
				assert!(sig_objs.len()==1, "cannot find or duplicate entries for {}", info.sig_name);
				let sig_obj = &sig_objs[0];
				let sig_id = sig_to_id.get(&info.sig_name)
					.expect(&format!("cannot find sig: {}", info.sig_name));
				let sig_id = F::from(*sig_id as u64);
				let dnf_id = info.min_dnf_id;
				let vssid = sig_obj.eval_dnf.vec_disjunc[dnf_id].iter().map(
					|x| F::from((*x+1) as u64)).collect::<Vec<F>>();
				(sig_id, vssid)
			};
			let eval_dnf_id = F::from(info.min_dnf_id as u64);
			let eval_count = F::from(vec_ssid.len() as u64);
			vec_ssid.iter().enumerate().map(|(i,ssid)|
				(eval_dnf_id, F::from(i as u64), eval_count, *ssid, sig_id)
			).collect::<Vec<(F,F,F,F,F)>>()
		}).flatten().collect::<Vec<(F,F,F,F,F)>>();
		let pad = vec![(zero,zero,zero,zero,zero); n-info_ts.len()];
		let info_ts = [&pad[..], &info_ts[..]].concat();
		assert!(info_ts.len()==n);
		let v_dnf_id = info_ts.iter().map(|t| t.0).collect::<Vec<F>>();
		let v_dnf_step = info_ts.iter().map(|t| t.1).collect::<Vec<F>>();
		let v_dnf_count = info_ts.iter().map(|t| t.2).collect::<Vec<F>>();
		let v_real_subsigs = info_ts.iter().map(|t| t.3).collect::<Vec<F>>();
		let v_sigs = info_ts.iter().map(|t| t.4).collect::<Vec<F>>();

		let info_id:u32 = 0x98882405; 
		let f1 = F::from(info_id);
		let factor = F::from(0x100000000 as u64); //32-bit 
		let v_sid_dnf_id = vec![frg; n];
		let v_sid_dnf_step = vec![frg; n];
		let v_sid_dnf_count= (0..n).collect::<Vec<usize>>().into_iter().map(|i|{
			let dnf_id = v_dnf_id[i];
			let sig_id = v_sigs[i];
			let tbl_id = f1*factor*factor*factor + sig_id * factor * factor
				+ dnf_id * factor;

			tbl_id
		}).collect::<Vec<F>>();

		let info_id:u32 = 0x99992405; 
		let f1 = F::from(info_id);
		let v_sid_real_subsigs= (0..n).collect::<Vec<usize>>()
			.into_iter().map(|i|{
			let dnf_id = v_dnf_id[i];
			let sig_id = v_sigs[i];
			let tbl_id = f1*factor*factor*factor + sig_id * factor * factor
				+ dnf_id * factor + v_dnf_step[i];

			tbl_id
		}).collect::<Vec<F>>();
		let v_sid_sigs = vec![frg; n];

		//2. Now prove that each sig in v_sigs is discharged as false
		//2.1 check that all subsig of a sig is well covered, i.e.,
		// the dnf_step is increasing, it starts from 0 and its
		// last step is equal to dnf_count
		// we do not have to generate the proof for it.
		// note that there is NO need to prove v_sigs is sorted,
		// the well formedness already proves the full coverage
		// of the related dnf_subsig for one sig. If there is one sig
		// shows up multiple times, it's costing more on prover but
		// does not affect soundness of proof.

		//2.2 build subsigs from (sig_id, real_subsig) and lookup
		// (subsig, False) in the (vec_subsig, vec_result) from the
		// previous gen_sytneshsis_subsig_result(). This is needed
		// as the structure of subsigs are different between the 
		// two components.
		let mut map = inp_subsigs.into_iter().zip(subsig_result.into_iter()).
			map(|(x,y)| (*x,*y)).collect::<HashMap<F,F>>();
		let f_false = F::from(TriVal::False as u8);
		map.insert(zero, f_false); //for dummy entry
		let mut v_computed_subsig = vec![zero; n];
		for i in 0..n{
			let subsig_id = F::from(HexACDFA::gen_subsig_id_worker(
						field_to_usize(&v_sigs[i]), 
						field_to_usize(&v_real_subsigs[i])
					) as u64);
			let res = map.get(&subsig_id)
				.expect(&format!("cannot find subsig_id: {}", &subsig_id));
			assert!(*res == f_false);
			v_computed_subsig[i] = subsig_id;
		}
		let src = encode_cols_better(
			vec![&v_computed_subsig[..], &vec![f_false; n][..]],
			vec![0,1]
		);
		//pad (0,1) for dummy entry
		let pad_subsigs = [&inp_subsigs[..], &vec![zero][..]].concat();
		let pad_res = [&subsig_result[..], &vec![f_false][..]].concat();
		let dst = encode_cols_better(
			vec![&pad_subsigs[..], &pad_res[..]],
			vec![0,1]
		);
		let mtbl_lk_res = gen_m_table(&src, &dst);

		//3. show that inp_sigs is a subset of v_sigs (covered)
		// where we have proved all v_sigs are discharged
		//note: v_sigs is required to have at least one dummy entry at beginning
		let mtbl_sigs= gen_m_table(&inp_sigs, &v_sigs);


		//4. add data columns into containers
		let names = vec![
				"v_sigs", 
				"v_dnf_id", 
				"v_dnf_step", 
				"v_dnf_count", 
				"v_real_subsigs"
				];
		let col2d = vec![
			v_sigs.clone(), 
			v_dnf_id, 
			v_dnf_step, 
			v_dnf_count, 
			v_real_subsigs
		];
		col2d.into_iter().zip(names.iter()).for_each(|(c, n)|{
			res.borrow_mut().add_col(Col::new(c, n, IDX_DATA));
		});
		let col2d_sid = vec![
			v_sid_sigs, 
			v_sid_dnf_id, 
			v_sid_dnf_step, 
			v_sid_dnf_count, 
			v_sid_real_subsigs
		];
		col2d_sid.into_iter().zip(names.iter()).for_each(|(c, n)|{
			res.borrow_mut().add_col(Col::new(c, &format!("sid_{}",n),
				IDX_SI_DATA));
		});
		assert!(mtbl_lk_res.len()==n+1);
		res.borrow_mut().add_col(Col::new(mtbl_lk_res,"mtbl_lk_res",IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;n+1],"sid_mtbl_lk_res",
			IDX_SI_DATA));
		
		assert!(mtbl_sigs.len()==n);
		res.borrow_mut().add_col(Col::new(mtbl_sigs,"mtbl_sigs",IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;n],"sid_mtbl_sigs",
			IDX_SI_DATA));
		res.borrow_mut().add_col(Col::new(inp_sigs.clone(),
			"discharged_sigs",IDX_DISCHARGED_SIGS));
		//res.borrow_mut().add_col(Col::new(vec![frg;capacity.sigs],
		//	"sid_discharged_sigs", IDX_SI_DATA));


		res
	}

}

impl <F:PrimeField> DfaAdvGadget<F>{
	pub fn new(
		capacity: &DfaAdvCapacity,
		prev_cfgs: &Vec<ContainerConfig>,
	) -> Self{
		//1. create the dummy input and dummy container config.
		let n = capacity.subsigs;
		let nibbles = vec![F::zero(); capacity.max_nibble_len];
		let dummy_inp_states = vec![F::one();n];  //adjust for 1
		let dummy_inp_subsigs = vec![F::zero(); n];
		let dummy_v_dfa_id = vec![F::zero();n];
		let dfa = Arc::new(build_trap_dfa());
		let dummy_v_dfa = vec![dfa; n];
		let v_sig_obj: Vec<Arc<ClamavSig>> = vec![]; //empty one
		//make a make one
		let discharge_infos = vec![
			DischargeSigInfo{
				sig_name: "none".to_string(),
				b_success: false,
				min_cost: 0,
				min_dnf_id: 0,
				subsig_ids: vec![0],
				subsig_igc: vec![false]
			}; capacity.sigs];
		let mut sigs_to_id = HashMap::<String,usize>::new();
		sigs_to_id.insert("none".to_string(), 0);
		let inp_sigs = vec![F::zero(); capacity.sigs];

		//2. create the dummy advice and cfg
		let dummy_adv = DfaAdvAdvice::new(&nibbles, &dummy_inp_subsigs,
			&dummy_v_dfa_id, &dummy_v_dfa, &dummy_inp_states, capacity,
				&inp_sigs, &discharge_infos, &v_sig_obj, &sigs_to_id
			);
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.borrow().get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[1].clone();

		Self{_f: PhantomData, capacity: Clone::clone(capacity), 
			cfgs_context: None,
			my_idx_in_context: None, dummy_cfg
		}
	}

	/// return None if not set yet.
	pub fn get_container_cfg(&self)->Option<ContainerConfig>{
		if self.my_idx_in_context.is_some(){
			let idx = self.my_idx_in_context.unwrap();
			let cfg = self.cfgs_context.as_ref().unwrap().as_ref()[idx].clone();
			Some(cfg)
		}else{
			Some(self.dummy_cfg.clone())
		}
	}

	/// validate the correctness of fsm_acc container
	#[allow(dead_code)]
	// validate the correctness of (subsig, res). where res:false meaning
	// not accepted by the dfas.
	//
	//COST: 14m + 3mn (m: subsigs, n: nibble length) -> subsigs
	//are usually very small (<10). meanly 3mn.
	fn validate_mul_fsm_acc_container(&self, fsm_acc: &Container<FpVar<F>>, cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
		//1. check the relations between v_sig, v_subsig,
		//v_raw_subsig and v_dfa_id
		//COST: 6n (where n = subsigs, in practice this is small: <10)
		let n = self.capacity.subsigs;
		let (zero,one) = (new_const_var(&cs, F::zero()), 
			new_const_var(&cs, F::one()));
		let fr = new_const_var(&cs, F::from(RANGE2));
		let bits = RANGE2_BIT; //26 bit
		let bit_part1 = bits*2/3; //16 for accomodating 64k sigs for bits 24
		let bit_part2 = bits - bit_part1;
		let _f_part1 = new_const_var(&cs, F::from(1u32<<bit_part1));
		let f_part2 = new_const_var(&cs, F::from(1u32<<bit_part2));
		let start = new_const_var(&cs, F::from(0x40000000u32));
		let f_part3 = new_const_var(&cs, F::from(1u32<<8));

		let names = vec!["v_sig", "v_subsig", "v_raw_subsig", "v_dfa_id"];
		let cols = names.iter().map(|n| fsm_acc.get_container(n)
			.unwrap().borrow().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();
		let (v_sig, v_subsig, v_raw_subsig, v_dfa_id) = (&cols[0],
			&cols[1], &cols[2], &cols[3]);
		for col in &cols {assert!(col.len()==n);}
		let sids = names.iter().map(|n| fsm_acc.get_container(
			&format!("sid_{}",n)).unwrap().borrow().to_vec())
			.collect::<Vec<Vec<FpVar<F>>>>();
		for i in 0..n{
			//1. ensure v_sig, subsig, raw_subsig in range
			//so that we can reason about dfa_id
			check_eq(&sids[0][i], &fr, "sid v_sig failed")?;	
			check_eq(&sids[1][i], &fr, "sid v_subsig_sig failed")?;	
			check_eq(&sids[2][i], &fr, "sid v_raw_subsig failed")?;	

			//2. check the relation between subsig <-- sig and raw_subsig 
			let exp_subsig = &v_raw_subsig[i] + &(&v_sig[i] * &f_part2);
			check_eq(&exp_subsig, &v_subsig[i], "fail subsig, sig check")?;

			//3. reason about DFA_ID this basically simulates
			// dfa_id() in data_processor/src/clam_db.rs
			// ignore dummy (0) entry, in computing dfa_id for it
			// there is a missing +1 shift. 
			let exp_dfa_id = &start + &(&f_part3 * &v_sig[i]) + 
				&v_raw_subsig[i] - &one;
			let diff = &exp_dfa_id - &v_dfa_id[i];
			check_eq(&(&v_sig[i]*&diff), &zero, "fail dfa_id")?;
		}

		//2. asserts all states and transitions must be in range
		// NOTE: we do not have to assert in range for nibbles they
		// are done already in word_extract_adv gadget.
		// in WordExtractAdv gadget: it has an nibbles_copy column
		// and it is PROVED that nibbles are already in "CHAR" range.
		// Here for the nibbles, they are lableled to their corresponding
		// translation, and this is gauranteed correct translation
		// given the nibbles_copy proof.
		//
		// COST: 2*m*nlen
		let names = vec!["states", "trans"];
		let cols = names.iter().map(|n| fsm_acc.get_container(n)
			.unwrap().borrow().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();
		let sids = names.iter().map(|n| fsm_acc.get_container(
			&format!("si_{}",n)).unwrap().borrow().to_vec())
			.collect::<Vec<Vec<FpVar<F>>>>();
		let (states,trans)=(&cols[0], &cols[1]);
		let (si_states,si_trans)=(&sids[0],&sids[1]);

		let (m,nlen) = (self.capacity.subsigs,self.capacity.max_nibble_len);
		let f_6 = new_const_var(&cs, F::from(6u32));
		let f_3 = new_const_var(&cs, F::from(3u32));
		let tblid_states = v_dfa_id.iter().map(|s| s + &f_6)
			.collect::<Vec<FpVar<F>>>();
		let tblid_trans = v_dfa_id.iter().map(|s| s + &f_3)
			.collect::<Vec<FpVar<F>>>();
		assert!(si_states.len()==m*(nlen+1) && si_trans.len()==m*nlen);
		for i in 0..nlen+1{
			for j in 0..m{
		  		check_eq(&si_states[i*m+j],&tblid_states[j],"err si_state")?;
			}
		}
		for i in 0..nlen{
			for j in 0..m{
		  		check_eq(&si_trans[i*m+j],&tblid_trans[j],"err si_trans")?;
			}
		}

		//3. assert correctness of building transition as weighted sum
		// of src, char, dst states
		//
		//COST: m*nlen
		let unit_var = FpVar::<F>::new_constant(cs.clone(),
			F::from((1<<(RANGE2_BIT+4)) as u32))?;
		let hex_var = FpVar::<F>::new_constant(cs.clone(),
			F::from(16 as u32))?;
			//note here: si_nibble = CHAR_MAP + ch
		let f_map = new_const_var(&cs, F::from(CHAR_MAP as u32));
		let chars = fsm_acc.get_container("si_nibbles")?.borrow().to_vec();
		let chars = chars.iter().map(|ch| ch-&f_map)
			.collect::<Vec<FpVar<F>>>(); 

		assert!(chars.len()==nlen && states.len()==(nlen+1)*m 
			&& trans.len()==nlen*m);
		for i in 0..nlen{
			let ch = &chars[i];
			for j in 0..m{//for each DFA
				let st1 = &states[i*m+j]; //already plus one
				let st2 = &states[(i+1)*m+j];
				// simulate clam_db.rs: add_acdfa_to_lkup
				let exp_trans = ch + 
					&(st1 * &hex_var) +
					&(st2 * &unit_var); //no need to plus one, already did
				let trans = &trans[i*m+j];
				check_eq(&trans, &exp_trans, 
					&format!("ERR: checking transition i:{}, j:{} ", i,j))?;
			}
		}

		//4. check the validity of subsig_res
		//
		//COST: 4m
		let names = vec!["subsig_res", "si_oup_state_copy"]; 
		let cols = names.iter().map(|n| fsm_acc.get_container(n)
			.unwrap().borrow().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();
		let (subsig_res,si_oup_state_copy) = (&cols[0], &cols[1]);
		let two = new_const_var(&cs, F::from(2u32));
		let f_true = new_const_var(&cs, F::from(TriVal::True as u8)); //2
		let f_false = new_const_var(&cs, F::from(TriVal::False as u8)); //1

		for i in 0..m{
			let tbl_id = &v_dfa_id[i];
			let final_tbl_id = tbl_id+&two;
			let b_final = final_tbl_id.is_eq(&si_oup_state_copy[i])?;
			let exp_res = b_final.select(&f_true, &f_false)?;
			let res = &subsig_res[i];
			check_eq(&exp_res, &res, "failing res check")?;
		}

		Ok( () )
	}

	/// validate all given ipu_sigs are DISCHARGED correctly.
	///
	/// COST: 2*n1 +  22*n
	/// where (n1 = num of sigs, n = num of subsigs)
	/// typically this is very small, n1 <4, n<10 => cost<300.
	/// this is adapted from the same function from compute_adv_sig.rs
	/// Here we made some simplification that there is no additional
	/// layer to turn extra layer of counter constraints. We 
	/// discharge sig from the eval_res_combo directly
	fn validate_discharge_sig_combo(&self, 
		eval_res_combo: &Rc<RefCell<Container<FpVar<F>>>>, 
		discharge_sig_combo: &Rc<RefCell<Container<FpVar<F>>>>, 
		r1: FpVar<F>,
		_r2: FpVar<F>,
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//0. retrieve data from combo
		let b_debug = true;
		let (zero,one)=(new_const_var(&cs,F::zero()),
			new_const_var(&cs,F::one()));
        let max_val:usize = (1<<RANGE2_BIT) - 1;
		let _max=new_const_var(&cs,F::from(max_val as u64));
		let frg = new_const_var(&cs, F::from(RANGE2));
		let names = vec![ "v_sigs", "v_dnf_id", "v_dnf_step", 
			"v_dnf_count", "v_real_subsigs"];
		let cols = names.iter().map(|n|
			discharge_sig_combo.borrow()
				.get_container(n).unwrap().borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		let (v_sigs, v_dnf_id, v_dnf_step, v_dnf_count, v_real_subsigs) = (
			&cols[0], &cols[1], &cols[2], &cols[3], &cols[4]);
		let sid_cols = names.iter().map(|n|
			discharge_sig_combo.borrow()
				.get_container(&format!("sid_{}",n)).unwrap().borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		let (v_sid_sigs, v_sid_dnf_id, v_sid_dnf_step, v_sid_dnf_count, 
			v_sid_real_subsigs) = (&sid_cols[0], &sid_cols[1], &sid_cols[2], 
				&sid_cols[3], &sid_cols[4]);
		let n = v_sigs.len();
		for i in 0..cols.len(){assert!(cols[i].len()==n);}
		for i in 0..cols.len(){assert!(sid_cols[i].len()==n);}

		//1. check the validity of sid cols (sequential as circ does not
		//allow parallelism)
		//
		// Cost: 5n
		let info_id:u32 = 0x98882405; 
		let f1_val = F::from(info_id);
		let factor_val = F::from(0x100000000 as u64); //32-bit 
		let factor = new_const_var(&cs, factor_val);
		let factor2 = &factor * &factor;
		let factor3 = &factor * &factor2;
		let f1 = new_const_var(&cs, f1_val);
		let part1 = &f1 * &factor3;

		let info_id:u32 = 0x99992405; 
		let f1_2 = new_const_var(&cs, F::from(info_id));
		let part1_2 = &f1_2 * &factor3;

		for i in 0..n{
			check_eq(&v_sid_dnf_id[i], &frg, "err sid dnf_id")?;
			check_eq(&v_sid_dnf_step[i], &frg, "erro sid_dnf_step")?;
			check_eq(&v_sid_sigs[i], &frg, "err id_sig")?;

			let sig_prod = &v_sigs[i] * &factor2;
			let dnf_id_prod = &v_dnf_id[i] * &factor;
			let exp_sid_dnf_count = &part1 + &sig_prod + &dnf_id_prod;
			check_eq(&exp_sid_dnf_count, &v_sid_dnf_count[i], 
				"err sid_dnf_cnt")?;

			let exp_sid_real_subsig = &part1_2 + &sig_prod + &dnf_id_prod
				+ &v_dnf_step[i];
			check_eq(&exp_sid_real_subsig, &v_sid_real_subsigs[i],
				"err sid_real_subsig")?;
		}

		//2. Now prove that each sig in v_sigs is discharged as false
		//2.1 check that all subsig of a sig is well covered, i.e.,
		// the dnf_step is increasing, it starts from 0 and its
		// last step is equal to dnf_count.
		// NOTE that the validity of v_dnf_step, ... columns are proved
		// already via v_sid columns in step 1.
		//
		// COST: 6n + 3
		check_eq(&v_sigs[0], &zero, "we require one dummy entry at begin")?;
		for i in 1..n{
			let b_new_row = v_sigs[i].is_neq(&v_sigs[i-1])?;
			let i_new_row: FpVar<F> = b_new_row.into();
			let res = &i_new_row * &(
				//(a) id_increase by one
				&v_dnf_step[i] - &v_dnf_step[i-1]
			) + (&i_new_row - &one) * &(
				//(b) starts from 0
				&(&r1 * &v_dnf_step[i]) + 
				//(c) previous row equals to count
				&(&v_dnf_step[i-1] + &one - &v_dnf_count[i-1])
			);
			let res = &res * &v_sigs[i]; //ignore zero entries
			check_eq(&res, &zero, "fails well-formed check")?;
		}


		//2.2 build subsigs from (sig_id, real_subsig) and lookup
		// (subsig, False) in the (vec_subsig, vec_result) from the
		// previous eval_res(). This is needed
		// as the structure of subsigs are different between the 
		// two components.
		//
		// COST: 8n 
		let bits = RANGE2_BIT;
		let bit_part1 = bits*2/3; //16 for accomodating 64k sigs for bits 24
		let bit_part2 = bits - bit_part1;
		let fac2 = new_const_var(&cs, F::from(1u64<<bit_part2) );
		let f_false = new_const_var(&cs, F::from(TriVal::False as u8));

		let v_computed_subsig = v_sigs.iter().zip(v_real_subsigs.iter())
			.map(|(sig_id, real_subsig_id)| {
				sig_id*&fac2 + real_subsig_id
		}).collect::<Vec<FpVar<F>>>();

		let src = encode_cols_var_adv_better(
			&vec![&v_computed_subsig[..], &vec![f_false.clone(); n][..]],
			&vec![0,1], &r1
		);
		//pad (0,1) for dummy entry
		//NOTE that here we assume that there are no SubsigCounterConstriant
		//they have two layers of synthesis.
		let inp_subsigs = eval_res_combo.borrow()
			.get_container("v_subsig").unwrap().borrow().to_vec();
		let subsig_result = eval_res_combo.borrow()
			.get_container("subsig_res").unwrap()
			.borrow().to_vec();
		let pad_subsigs = [&inp_subsigs[..], &vec![zero][..]].concat();
		let pad_res = [&subsig_result[..], &vec![f_false][..]].concat();
		let dst = encode_cols_var_adv_better(
			&vec![&pad_subsigs[..], &pad_res[..]],
			&vec![0,1], &r1
		);
		let mtbl_lkup_res = discharge_sig_combo.borrow()
			.get_container("mtbl_lk_res").unwrap().borrow().to_vec();
		assert_logup(cs.clone(), &src, &dst, &mtbl_lkup_res, &r1)?;

		//3. show that inp_sigs is a subset of v_sigs (covered)
		// where we have proved all v_sigs are discharged
		//note: v_sigs is shown earlier
		// to have at least one dummy entry at beginning so that just in
		// case inp_sigs has 0 entry.
		//
		//COST: let n1 = num of sigs, n = num of subsigs
		// 2n1 + 3n
		let discharged_sigs = discharge_sig_combo.borrow()
			.get_container("discharged_sigs").unwrap().borrow().to_vec();
		let mtbl_sigs= discharge_sig_combo.borrow()
			.get_container("mtbl_sigs").unwrap().borrow().to_vec();
		assert_logup(cs.clone(), &discharged_sigs, &v_sigs, &mtbl_sigs, &r1)?;

		if b_debug{
			println!("DEBUG USE 6901 === discharged sigs by DFA ===");
			for i in 0..discharged_sigs.len(){
				println!(" --i: {}, sig: {}", i, discharged_sigs[i].value()?);
			}
		}


		Ok( () )

	}

}

impl <F:PrimeField> SigmaGadget<F> for DfaAdvGadget<F>{
	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, cfgs_context: Rc<Vec<ContainerConfig>>, idx: usize){
		self.cfgs_context = Some(cfgs_context);
		self.my_idx_in_context = Some(idx);
	}

	/// Get the instructions for build its statement.
	/// NOTE: this is only needed for those used in SedGadgetMapper.
	/// Others are handled by legacy code in their gadget mapper.
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let res = cfg.gen_stmt_map_instructions();
		res
	}

	/// return the sizes of inp/oup/data/failed_sigs/discharged_sigs
	/// to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		for i in 0..3 {assert!(to_add[i+1] == to_add[4+i]);}
		assert!(to_add[IDX_INP]==to_add[IDX_OUP]);
		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA],
			0, self.capacity.sigs)
	}

	fn est_cost(&self)->usize{
		// key is the low perc_pat_in_trace 
		/*
		let est = 
			118 * 
			self.capacity.max_nibble_len 
			* self.capacity.perc_pats_in_trace/100 			
		+ 107 * self.capacity.avg_pats_per_subsig * self.capacity.subsigs;

		est
		*/
		1024
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		let stat_len = (IDX_WORD..IDX_SI_DATA+1).collect::<Vec<usize>>()
			.iter().map(|i| to_add[*i]).sum();
		//TODO: needs a separate container for msg3, and need to
		//determine msg2 then.
		(stat_len, 0, 2, 0)
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

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();

		//2. validate the fsm_acc combo 
		let mul_fsm_acc = stmt.get_container("mul_fsm_acc")?;
		self.validate_mul_fsm_acc_container(&mul_fsm_acc.borrow(), cs.clone())?;

		//2. validate the discharging of sig.
		let sig_res_combo= stmt.get_container("sig_res_combo")?;
		self.validate_discharge_sig_combo(&mul_fsm_acc,
			&sig_res_combo, r1.clone(), r2.clone(), cs.clone())?;

		Ok(())
	}
}

// ---------------------------------------------------
// Utility Functions
// ---------------------------------------------------

/// this is basically the inverse function of
/// HexACDFA::gen_subsig_id() in hex_acdfa.rs
/// it extracts the sig_id and the real subsig_id that
/// generates the subsig_id
#[inline(always)]
#[allow(dead_code)]
pub fn extract_sigid<F:PrimeField>(subsig_id: F)->(F,F){
	let u_subsig_id = field_to_usize(&subsig_id);
	let bits = RANGE2_BIT; //26 bit
	let bit_part1 = bits*2/3; //16 for accomodating 64k sigs for bits 24
	let bit_part2 = bits - bit_part1;
	let sig_id = u_subsig_id >> bit_part2;
	let real_subsig_id = u_subsig_id - (sig_id<<bit_part2);
	assert!(sig_id < (1<<bit_part1));
	assert!(real_subsig_id < (1<<bit_part2));

	(F::from(sig_id as u64), F::from(real_subsig_id as u64))
}

#[cfg(test)]
pub mod tests_dfa_adv_gadget{
	extern crate rustomaton;
	use ark_ff::{Zero};
	use std::{rc::Rc, sync::{Arc}};
	use ark_bn254::{Fr};
	use utils::{data::{pack_nibbles}, os::{read_nibbles,proj_root}};
	use crate::gadgets::{
		word_extract::{
			LEGS,
			tests_word_extract_gadget::{test_gadget_adv},
		},
		dfa_adv::{DfaAdvGadget,DfaAdvAdvice,DfaAdvCapacity},
		word_extract_adv::{WordExtractAdvAdvice},
	};
	use data_processor::{clam_db::{ClamavDB}, 
		hex_acdfa::HexACDFA, type_def::{ClamavSig},
		clamav::{quick_discharge_file_adv,default_clamav_cfg},

	};
	use folding_schemes::folding::foldpot::{
		sigma_ir1cs::{SigmaGadget,WordInfo},
		container_config::ContainerConfig,
		circuits_super::field_to_usize,
	};
	use rustomaton::dfa::DFA;

	#[test]
	fn test_dfa_adv(){
		//1. load the clamdb instance. It has the following sigs
		//sig1: a....c|c....a
		//word: 22a9999d111111 (it's expect c with a gap of 4 from a, but
		// got a d)
		//DFA discharges it. The Critical pattern and SED fail because
		// pattern "a" and "c" too short.
		let path= "debug/dfa/simple";
		let db = ClamavDB::<Fr>::build_db_from_dir(path);

		//2. create advice for word_extract_adv and dfa_adv
		// both advices are needed for producing related container_config
		// with external col referece.
		//2.1 the word_extract_adv
		let (wlen, act_size) = (2usize, 1usize);
		let nibbles_raw = read_nibbles(
			&format!("{}/data/{}/word2.txt",proj_root() , path));
		let f_nibbles = nibbles_raw.iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let word = vec![pack_nibbles(&f_nibbles), vec![Fr::zero()]].concat();
		let cfg = default_clamav_cfg();
		let wi: WordInfo = quick_discharge_file_adv(
			"word2.txt", 
			&nibbles_raw,
			&db.vec_sigs,
			&db.vec_sigs_no_critical_pat,
			&db.map_crit_pat, 
			&db.map_crit_pat_igc, 
			&db.dfa_crit, 
			&db.bundle_subsig.vec_acdfa[0], //dfa_patterns, 
			&db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
			&cfg, 
			&db.sig_to_id
		); //use optimize mode

		//note: set true to use char map for nibbles.
		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, true);
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.borrow().get_cfg(); 

		//2.2 the dfa_adv 
		let sig = &db.vec_sigs.iter().filter(|sig| sig.name=="sig1")
			.map(|sig| sig.clone()).collect::<Vec<Arc<ClamavSig>>>()[0];
		let v_sigs = vec![sig.clone()];
		let sig_id = db.sig_to_id.get(&sig.name).unwrap();
		let info = &wi.vec_dfa_sigs_info[0];
		assert!(info.sig_name=="sig1"); 

		let discharge_infos = vec![info.clone()]; //only one sig to discharge
		let inp_sigs: Vec<Fr> = vec![Fr::from(*sig_id as u64)];
		// here we just take the first dnf, in practice it
		// will be decided by the DischargeInfo advice which dnf to discharge
		let inp_subsigs = v_sigs.iter().map(|sig| sig.
			eval_dnf.vec_disjunc[0].iter().map(|i|
				Fr::from(HexACDFA::gen_subsig_id_worker(*sig_id, *i+1) as u32)
			).collect::<Vec<Fr>>()
		).collect::<Vec<Vec<Fr>>>();
		let inp_raw_subsigs = v_sigs.iter().map(|sig| sig.
			eval_dnf.vec_disjunc[0].iter().map(|i| Fr::from(*i as u64))
			.collect::<Vec<Fr>>()
		).collect::<Vec<Vec<Fr>>>();
		let v_dfa= v_sigs.iter().map(|sig| sig.
			eval_dnf.vec_disjunc[0].iter().map(|i| 
				sig.vec_subsig_automaton[*i].clone()) //clone of Arc low cost
			.collect::<Vec<Arc<DFA<char>>>>()
		).collect::<Vec<Vec<Arc<DFA<char>>>>>();

		assert!(&v_sigs[0].name=="sig1");
		let nibble_len = wlen*LEGS;
		let cap = DfaAdvCapacity{max_nibble_len: nibble_len, subsigs: 2,
			sigs: 1};

		let nibbles = stmt_wea.borrow().get_container("nibbles").unwrap()
			.borrow().to_vec();
		let f_nibbles = vec![f_nibbles.clone(), vec![Fr::zero(); 
			nibbles.len()-f_nibbles.len()]].concat();
		assert!(nibbles==f_nibbles);

		let v_inp_state = v_dfa.iter().map(|vec|
			vec.iter().map(|dfa| Fr::from((dfa.initial + 1) as u32))
				.collect::<Vec<Fr>>()
		).collect::<Vec<Vec<Fr>>>();
		let v_fsm_id = v_sigs.iter().zip(inp_raw_subsigs.iter())
			.map(|(sig, v_subsig)|{
				let sig_id = *(db.sig_to_id.get(&sig.name).unwrap()) as u32;
				v_subsig.iter().map(|subsig_id|{
					let dfa_id = ClamavDB::<Fr>::dfa_id(
						sig_id, 
						field_to_usize(subsig_id) as u32
					);
					Fr::from(dfa_id)
				}).collect::<Vec<Fr>>()
		}).collect::<Vec<Vec<Fr>>>();

		let v_subsig_ids = inp_subsigs.into_iter().map(|s| s).flatten()
			.collect::<Vec<Fr>>();
		let v_fsm_id= v_fsm_id.into_iter().map(|s| s).flatten()
			.collect::<Vec<Fr>>();
		let v_inp_state = v_inp_state.into_iter().map(|s| s).flatten()
			.collect::<Vec<Fr>>();
		let v_dfa= v_dfa.into_iter().map(|s| s).flatten()
			.collect::<Vec<Arc<DFA<char>>>>();
		let adv_faa = DfaAdvAdvice::new(
			&nibbles, &v_subsig_ids, &v_fsm_id, 
			&v_dfa, &v_inp_state, &cap,
			&inp_sigs, &discharge_infos, &v_sigs, &db.sig_to_id
		);
		let stmt_faa = adv_faa.stmt_container;
		let cfg_faa = stmt_faa.borrow().get_cfg(); 

		//2.3 given cfgs, set up the positions
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
		ContainerConfig::adjust_locations(&mut vec_cfg); //resolve

		//3. generate the 7 segments of output for building statment
		let cps1 = stmt_wea.borrow().gen_stmt_components(); 
		let cps2 = stmt_faa.borrow().gen_stmt_components(); 
		let cps = cps1.into_iter().zip(cps2.into_iter()).map(|(a,b)|
			vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();

		//4. create the gadget
		let lkup_share_size = 4usize;
		let mut fag = DfaAdvGadget::<Fr>::new(
			&cap, 
			&vec![cfg_wea.clone()],
		);
		fag.set_container_cfg(vec_cfg.clone().into(), 1);  //it's the 2nd cfg
		let _sizes = fag.get_to_add_size(); //test if sizes are ok
		let rg = Rc::new(fag);

		//5. test it
		test_gadget_adv::<Fr>(rg, &word, &cps[0], &cps[1], &cps[2],
			&cps[6], &cps[7],
			&vec![//subtbl_id (concats of si_inp, si_oup, si_data)
				cps[3].clone(), 
				cps[4].clone(), 
				cps[5].clone(),
			].concat(), lkup_share_size,
			false, //not legacy mode
			Some(vec_cfg),
		);

		//todo!("manually verify two cases if DFA hits accept state or not for two different test cases");
	}
}
