use utils::consts::{read_global_config, B_DEBUG};
/* Created 07/16/2025, Completed: 07/27/2025
	Revised 11/06/2025: improve efficiency
	Revised 01/10/2026: improve capaicity err exception
*/

// This module dischages a nibble sequence against a collection
// of DFAs (each one-to-one corresponding to a subsignature),
// and reports the discharging status for each subsig.
// It is a n-concurrent parallel version of the fsm component.
// Then it assembles subsig result and report the discharge (via DFA)
// result for sigs.

use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{logger::{log_perf, LOG1,LOG2}, 
	timer::Timer as GTimer};
use rayon::iter::{ParallelIterator,IntoParallelIterator,IntoParallelRefIterator};
use std::{sync::{Arc}, marker::{PhantomData}, any::Any, collections::{HashMap}};
use ark_ff::{PrimeField};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity,DischargeSigInfo},
		container_config::{ContainerConfig},
		circuits_super::field_to_usize,
		utils::{var_to_tuple_adv},
	}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef,Variable,LinearCombination};
use ark_r1cs_std::{
	fields::{
		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};
use data_processor::{
	clam_db::{ClamavDB,  RANGE2,CHAR,
		//STORE_SUBSIG,
	},
	type_def::{TriVal,ClamavSig},
	fsa_utils::{build_trap_dfa},
	hex_acdfa::{HexACDFA},
};
use utils::{data::{u8_to_hex}};
use crate::gadgets::{
	commons::{mix_vec,new_const_var, check_eq,encode_cols_better,gen_m_table,
		check_prod_zero,
		encode_cols_var_adv_better , packcheck_vec, build_pows_31_val,
		build_pows_56_val, var_to_lb},
	traits::{Container,
		Col,
		IDX_WORD, IDX_INP,IDX_DATA, IDX_DISCHARGED_SIGS,
		IDX_SI_INP, 
		IDX_OUP, 
		IDX_SI_OUP, 
		IDX_SI_DATA, ComponentAdvice},
	db::{assert_logup},
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
pub struct DfaAdvAdvice<F:PrimeField + ColEle>{
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
	pub stmt_container: std::sync::Arc<std::sync::Mutex<Container<F>>>,

	/// capacity
	pub capacity: DfaAdvCapacity,
}

#[allow(dead_code)]
/// This gadget is responsible for checking transitions
/// of running a finite state machine. 
#[derive(Clone,Debug)]
pub struct DfaAdvGadget<F:PrimeField + ColEle>{ 
	/// the capacity
	pub capacity: DfaAdvCapacity,

	// will be set when set_container_cfg is called
	pub cfgs_context: Option<std::sync::Arc<Vec<ContainerConfig>>>,
	// dummy_cfg is used when cfgs_context is not ready yet
	pub dummy_cfg: ContainerConfig,
	pub my_idx_in_context: Option<usize>,
	_f: PhantomData<F>,

	pub job_id: usize,
	}



// ---------------------------------------------
//            Implementations
// ---------------------------------------------
impl Capacity for DfaAdvCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		let other = r_other.as_any().downcast_ref::<DfaAdvCapacity>()
			.expect("downcast err"); 
		self.max_nibble_len >= other.max_nibble_len &&
		self.subsigs>= other.subsigs &&
		self.sigs>= other.sigs
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(DfaAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			subsigs: self.subsigs,
			sigs: self.sigs,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField + ColEle> NdAdvice for DfaAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField + ColEle> ComponentAdvice<F> for DfaAdvAdvice<F>{
	fn get_container(&self)->std::sync::Arc<std::sync::Mutex<Container<F>>>{
		self.stmt_container.clone()
	}
}

impl <F: PrimeField + ColEle> DfaAdvAdvice<F>{
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
		seg_id: F,
		) ->Result<Self,Error>{
		let stmt_container = Container::<F>::new("dfa_adv_stmt");
		//1. padding the input when necessary
		let dummy_fsm_id = F::from(ClamavDB::<F>::dfa_id_of_subsig(0));
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
		if n<n1{
			return Err(Error::CapErr(vec![(format!("dfa_adv::subsigs"), n1)]));
		}
		assert!(n>=n1, "capacity.subsigs: {} < inp_subsigs: {}. adjust DfaCapacity.subsigs", n, n1);
		let n2 = n - n1;
		if inp_sigs.len()>capacity.sigs{
			return Err(Error::CapErr(vec![(format!("dfa_adv::sigs"), 
				inp_sigs.len())]));
		}
		assert!(inp_sigs.len()<=capacity.sigs, "increase capacity.sigs: {} to cover inp_sigs: {}", capacity.sigs, inp_sigs.len());
		let zero = F::zero();
		assert!(v_dfa_id.len()==n1 && v_dfa.len()==n1);
		let inp_subsigs = [&inp_subsigs[..], &vec![zero;n2][..]]
			.concat();
		let inp_sigs = [&inp_sigs[..], 
			&vec![zero;capacity.sigs-inp_sigs.len()][..]].concat();
		if capacity.sigs<discharge_infos.len(){
			return Err(Error::CapErr(vec![(format!("dfa_adv::sigs"), 
				discharge_infos.len())]));
		}
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
			nibbles, &inp_subsigs, &v_dfa_id, &v_dfa, &inp_states, capacity, seg_id
		)?;
		stmt_container.lock().unwrap().add_container(mul_fsm_acc);

		//3. construct the sig_res_combo
		let sig_res_combo = Self::gen_discharge_sig_combo(
			&inp_sigs, 
			&inp_subsigs, 
			&subsig_res, 
			&capacity,
			&v_sig_obj,
			&discharge_infos,
			&sig_to_id
		)?;
		stmt_container.lock().unwrap().add_container(sig_res_combo);

		Ok( Self{
			capacity: Clone::clone(capacity), 
			inp_subsigs: inp_subsigs.clone(),
			v_dfa_id: v_dfa_id.clone(),
			v_dfa: v_dfa.clone(),
			f_inp_states: inp_states.clone(),
			stmt_container
		} )
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
	/// actually throws no CapErr
	#[allow(dead_code)]
	fn gen_mul_fsm_acc_combo(
		nibbles: &Vec<F>, 
		inp_subsigs: &Vec<F>,  //will be padded to full #subsigs by capacity
		v_dfa_id: &Vec<F>, //the ids generaed by gen_dfa_id in clamdb
		v_dfa: &Vec<Arc<DFA<char>>>, //1-1 corresponding to inp_subsigs
		inp_states: &Vec<F>,
		capacity: &DfaAdvCapacity,
		seg_id: F) 
	-> Result<(std::sync::Arc<std::sync::Mutex<Container<F>>>,Vec<F>),Error>{
		//0. set up data
		let b_debug = B_DEBUG;
		let res = Container::<F>::new("mul_fsm_acc");
		let (m, nlen) = (capacity.subsigs, capacity.max_nibble_len);
		let (_one,zero) = (F::one(),F::zero());
		assert!(v_dfa_id.len()==m && v_dfa.len()==m && inp_subsigs.len()==m);
		assert!(nibbles.len()==nlen, "nibbles: {}, nlen: {}", nibbles.len(), nlen);
		//1. walk nibbles through transition of each DFA
		//this will be sequential, in practice, it's ok
		// NOTE: saved_states are adjused (by +1)
		// when query DFA, recover them by -1
		//1.1 buld all info using as much parallelism as possible
		let frg = F::from(RANGE2);
		let v2d = (0..m).collect::<Vec<_>>().into_par_iter().map(|j|{
			//for each dfa
			let dfa = &v_dfa[j];
			let fsm_id = v_dfa_id[j];
			let mut src = field_to_usize(&inp_states[j]) - 1;
			let mut v_states = vec![zero; nlen + 1];
			let mut v_trans = vec![zero; nlen];
			v_states[0] = F::from((src+1) as u32);
			let f_id_state = frg; //ONLY range proof is good enough
				//the CHUNK in transition will FORBID INVALID state!
			let f_id_trans= fsm_id + F::from(3u32);
			//sequentially walk nibbles through DFA
			let s_nibbles = nibbles.iter().map(|n| field_to_usize(n) as u8)
				.collect::<Vec<u8>>();
			let s2 = u8_to_hex(&s_nibbles).as_bytes().to_vec().iter()
				.map(|s| *s as char).collect::<Vec<char>>();
			let sid_nibbles = vec![F::from(CHAR);nibbles.len()];
			for i in 0..nibbles.len(){
				let ch = s2[i];
				let dst = dfa.transitions[src].get(&ch);
				assert!(dst.is_some());
				let dst = dst.unwrap();
				if b_debug{
					let u_segid = field_to_usize(&seg_id);
					let start_idx = u_segid * capacity.max_nibble_len;
					let u_idx = i + start_idx;
					//if u_idx>=748447-100 && u_idx<=748447+10{
					
				}
				let ch_usize = s_nibbles[i] as usize; //0..15, NOT ascii
				let trans = ch_usize +
					 ((src+1)<<4) + ((dst+1)<<(4+read_global_config().range2_bit));
				v_states[i+1] = F::from((dst+1) as u32);
				v_trans[i] = F::from(trans as u64);
				src = *dst;
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

		//1.3 add v_subsig (v_dfa_id is recomputed in-circuit). INP + OUP
		//copy: the I/O hand-off fixes each row's subsig over the word (S9)
		let n = capacity.subsigs;
		assert!(inp_subsigs.len()==n);
		assert!(v_dfa_id.len()==n);
		res.lock().unwrap().add_col(Col::<F>::new(inp_subsigs.to_vec(),
			"v_subsig",IDX_INP)); 
		res.lock().unwrap().add_col(Col::<F>::new_const(vec![frg;n], "sid_v_subsig",
			IDX_SI_INP)); 
		res.lock().unwrap().add_col(Col::<F>::new(inp_subsigs.to_vec(),
			"v_subsig_oup",IDX_OUP)); 
		res.lock().unwrap().add_col(Col::<F>::new_const(vec![zero;n],
			"sid_v_subsig_oup",IDX_SI_OUP)); //bound by check_eq, no lookup

		//1.4 add columns related to inp/mid/oup states
		let col_inp_state = Col::<F>::new(states[0..m].to_vec(),
			"inp_state",IDX_INP);
		let col_si_inp_state = Col::<F>::new_const(sid_states[0..m].to_vec(),
			"si_inp_state",IDX_SI_INP);

		let col_mid_states = Col::<F>::new(states[m..m*nlen].to_vec(),
			"mid_states", IDX_DATA);
		let col_si_mid_states = Col::<F>::new_const(sid_states[m..m*nlen]
			.to_vec(), "si_mid_states", IDX_SI_DATA);

		let col_oup_state = Col::<F>::new(states[m*nlen..m*(nlen+1)].to_vec(),
			"oup_state",IDX_OUP);
		let col_si_oup_state = Col::<F>::new_const(sid_states[m*nlen..m*(nlen+1)] .to_vec(), "si_oup_state",IDX_SI_OUP);
		let raw_states = &states;

		let states = Container::concat_cols(
			vec![col_inp_state, col_mid_states, col_oup_state], "states");
		let si_states = Container::concat_cols(vec![col_si_inp_state, 
			col_si_mid_states, col_si_oup_state], "si_states");
		res.lock().unwrap().add_container(states); //remove clone later
		res.lock().unwrap().add_container(si_states);


		//1.3. the transitions
		let col_trans = Col::<F>::new(trans, "trans", IDX_DATA);
		let col_si_trans = Col::<F>::new(sid_trans, "si_trans", IDX_SI_DATA);
		res.lock().unwrap().add_col(col_trans);
		res.lock().unwrap().add_col(col_si_trans);

		//1.4 the nibbles (LATER when reconstructed, it is 
		// retrieved from previous word_extract_adv gadget
		let col_nibbles = Col::<F>::new_external(nibbles.to_vec(), 
			"nibbles", IDX_DATA, -1, "word_extract_stmt nibbles");
		let col_si_nibbles = Col::<F>::new_external(sid_nibbles.to_vec(),
			"si_nibbles", IDX_SI_DATA, -1, 
			"word_extract_stmt si_nibbles");
		if B_DEBUG {assert!(col_nibbles.lock().unwrap().data.len()==nlen);}
		if B_DEBUG {assert!(col_si_nibbles.lock().unwrap().data.len()==nlen);}


		res.lock().unwrap().add_col(col_nibbles);
		res.lock().unwrap().add_col(col_si_nibbles);

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

		res.lock().unwrap().add_col(Col::<F>::new(raw_states[m*nlen..m*(nlen+1)]
			.to_vec(), "oup_state_copy",IDX_DATA));
		res.lock().unwrap().add_col(Col::<F>::new(sid_oup_state_copy,
			"si_oup_state_copy",IDX_SI_DATA));
		res.lock().unwrap().add_col(Col::<F>::new(subsig_res.clone(),
			"subsig_res",IDX_DATA));
		res.lock().unwrap().add_col(Col::<F>::new_const(vec![zero;m],
			"si_subsig_res",IDX_SI_DATA)); //don't care as they'll be TriVal


		Ok( (res, subsig_res) )
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
	/// throws CapErr:subsigs
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
	)->Result<std::sync::Arc<std::sync::Mutex<Container<F>>>,Error>{
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
		if n<=info_ts.len(){
			return Err(Error::CapErr(vec![(format!("dfa_adv::subsigs"), 
				info_ts.len()+1)]));
		}
		assert!(n-info_ts.len()>0); //ensure one dummy entry
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
			assert!(*res == f_false, "ERR dfa_adv: for subsig: {}, it's result is {}", subsig_id, res);
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
			res.lock().unwrap().add_col(Col::new(c, n, IDX_DATA));
		});
		let col2d_sid = vec![
			v_sid_sigs, 
			v_sid_dnf_id, 
			v_sid_dnf_step, 
			v_sid_dnf_count, 
			v_sid_real_subsigs
		];
		let b_sid_const = vec![true, true, true, false, false];
		col2d_sid.into_iter().zip(names.iter().zip(b_sid_const))
		//col2d_sid.into_iter().zip(names.iter()).for_each(|(c, n)|{
		.for_each(|(c,(n,b))|{
			if b{
				res.lock().unwrap().add_col(Col::new_const(c, &format!("sid_{}",n),
					IDX_SI_DATA));
			}else{
				res.lock().unwrap().add_col(Col::new(c, &format!("sid_{}",n),
					IDX_SI_DATA));
			}
		});
		/*
		col2d_sid.into_iter().zip(names.iter()).for_each(|(c, n)|{
			res.lock().unwrap().add_col(Col::new(c, &format!("sid_{}",n),
				IDX_SI_DATA));
		});
		*/
		assert!(mtbl_lk_res.len()==n+1);
		res.lock().unwrap().add_col(Col::new(mtbl_lk_res,"mtbl_lk_res",IDX_DATA));
		res.lock().unwrap().add_col(Col::new_const(vec![zero;n+1],
			"sid_mtbl_lk_res", IDX_SI_DATA));
		
		assert!(mtbl_sigs.len()==n);
		res.lock().unwrap().add_col(Col::new(mtbl_sigs,"mtbl_sigs",IDX_DATA));
		res.lock().unwrap().add_col(Col::new_const(vec![zero;n],"sid_mtbl_sigs",
			IDX_SI_DATA));
		res.lock().unwrap().add_col(Col::new(inp_sigs.clone(),
			"discharged_sigs",IDX_DISCHARGED_SIGS));
		//res.lock().unwrap().add_col(Col::new(vec![frg;capacity.sigs],
		//	"sid_discharged_sigs", IDX_SI_DATA));


		Ok( res )
	}

}

impl <F:PrimeField + ColEle> DfaAdvGadget<F>{
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
		let seg_id = F::zero();
		let dummy_adv = DfaAdvAdvice::new(&nibbles, &dummy_inp_subsigs,
			&dummy_v_dfa_id, &dummy_v_dfa, &dummy_inp_states, capacity,
				&inp_sigs, &discharge_infos, &v_sig_obj, &sigs_to_id, seg_id
			).expect("dummy dfa_adv advice err");
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.lock().unwrap().get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[1].clone();

		Self{_f: PhantomData, capacity: Clone::clone(capacity), 
			cfgs_context: None,
			my_idx_in_context: None, dummy_cfg,
			job_id: 0
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
	//COST: 10m + mn*3/8 (m: subsigs, n: nibble length) -> subsigs
	//are usually very small (<10). meanly 3mn.
	fn validate_mul_fsm_acc_container(&self, fsm_acc: &Container<FpVar<F>>, cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
		//1. v_dfa_id = DFA_ID_START + DFA_ID_STRIDE*v_subsig (= dfa_id_of_subsig).
		//v_subsig is bound by the discharge LogUp. COST: n (+14n in the
		//sigma I/O Horner loops)
		let b_perf = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let nc = cs.num_constraints();
		let n = self.capacity.subsigs;
		let (zero,one) = (new_const_var(&cs, F::zero()), 
			new_const_var(&cs, F::one()));
		let bits = read_global_config().range2_bit;
		let start = new_const_var(&cs, F::from(ClamavDB::<F>::DFA_ID_START));
		let stride = new_const_var(&cs, F::from(ClamavDB::<F>::DFA_ID_STRIDE));
		let v_subsig = fsm_acc.get_container("v_subsig").unwrap()
			.lock().unwrap().to_vec();
		assert!(v_subsig.len()==n);
		let v_dfa_id = v_subsig.iter().map(|s| &start + &(&stride * s))
			.collect::<Vec<FpVar<F>>>();
		let v_subsig_oup = fsm_acc.get_container("v_subsig_oup").unwrap()
			.lock().unwrap().to_vec();
		for i in 0..n{ check_eq(&v_subsig_oup[i], &v_subsig[i], "S9 oup copy")?; }
		if b_perf{
			log_perf(self.job_id, log_level, "validate_mul_fsm step 1", &mut gt);
		}

		//2. asserts all states and transitions must be in range
		// NOTE: we do not have to assert in range for nibbles they
		// are done already in word_extract_adv gadget.
		// (WordExtractAdv default mode: si_nibbles = const CHAR).
		// m * n * 3/8
		let names = vec!["states", "trans"];
		let cols = names.iter().map(|n| fsm_acc.get_container(n)
			.unwrap().lock().unwrap().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();
		let sids = names.iter().map(|n| fsm_acc.get_container(
			&format!("si_{}",n)).unwrap().lock().unwrap().to_vec())
			.collect::<Vec<Vec<FpVar<F>>>>();
		let (states,trans)=(&cols[0], &cols[1]);
		let (si_states,si_trans)=(&sids[0],&sids[1]);

		let (m,nlen) = (self.capacity.subsigs,self.capacity.max_nibble_len);
		//let f_6 = new_const_var(&cs, F::from(6u32));
		let f_3 = new_const_var(&cs, F::from(3u32));
		//let tblid_states = v_dfa_id.iter().map(|s| s + &f_6)
		//	.collect::<Vec<FpVar<F>>>();
		let tblid_trans = v_dfa_id.iter().map(|s| s + &f_3)
			.collect::<Vec<FpVar<F>>>();
		assert!(si_states.len()==m*(nlen+1) && si_trans.len()==m*nlen);
		assert!(tblid_trans.len()==m);

		//let frg = new_const_var(&cs, F::from(RANGE2));
		// NO NEED TO CHECK CONSTANTS in circuit.
		//for i in 0..nlen+1{
		//	for j in 0..m{
		// 		check_eq(&si_states[i*m+j],&frg,"err si_state")?;
		//	}
		//}

		// --- WE IMPROVE THE FOLLOWING TO m*n/8 ---------
		// IDEA: trans_id is a FIXED value among tbl col2 and all
		// col2 values are NO MORE THAN 32-BIT
		// Note that later: (trans, si_trans) is checked in Sonobe
		// for lookup. so adversary will NOT be able to put
		// a FAKE col2 value here, otherwise it's NOT GOING to
		// pass the logup check in Sonobe later.
		//
		// With that being said, the ONLY trick value the adversary
		// can play is THAT it inserts a VALID col2 value (note: it's
		// always within 32-bit) but it's NOT the valid sid_trans.
		// Now note here if we do BIT-STRING concat of 8 such
		// values in one FIELD ELEMENT (and check - as all segs
		// are already limited to 32-bit - one check allows to
		// check all 8 legs are valid!). Thus we end up with
		// the cost of nlen/8 for check of sids for ONE DFA.
		// ------------------------------------------------
		//for i in 0..nlen{
		//	for j in 0..m{
		// 		check_eq(&si_trans[i*m+j],&tblid_trans[j],"err si_trans")?;
		//	}
		//}
		let vec_si_trans = (0..m).into_iter().map(|dfa_id|{
			let vec_si = (0..nlen).into_iter().map(|j|{
				si_trans[m*j + dfa_id].clone()
			}).collect::<Vec<FpVar<F>>>();
			vec_si
		}).collect::<Vec<Vec<FpVar<F>>>>();
		let pows_31 = build_pows_31_val();
		for i in 0..m{
			let exp_val = tblid_trans[i].clone();  
			packcheck_vec(&vec_si_trans[i], &exp_val, &pows_31)?;
		}
		if b_perf{
			log_perf(self.job_id, log_level, "validate_mul_fsm step 2", &mut gt);
		}

		//3. assert correctness of building transition as weighted sum
		// of src, char, dst states
		//
		//COST: m*nlen/4
		// IDEA of optimization: so where
		// since char is restricted to 4 bit, states are restricted
		// to 26 bit. The transition EXPECTED is computed is 
		// GURANTEED to be 56-bit
		// the transitions RETRIEVED from te proof are EARLIER
		// restricted by their SID_transition (and thus ALSO
		// guaranteed to be 56-bit
		// To compare the TWO arrays are essentially the same
		// we can simply pack 4 element's check INTO one!
		let unit_var = FpVar::<F>::new_constant(cs.clone(),
			F::from((1<<(read_global_config().range2_bit+4)) as u32))?;
		let hex_var = FpVar::<F>::new_constant(cs.clone(),
			F::from(16 as u32))?;
		//chars = nibbles (0..15, CHAR-range-checked by word_extract)
		let chars = fsm_acc.get_container("nibbles")?.lock().unwrap().to_vec();

		assert!(chars.len()==nlen && states.len()==(nlen+1)*m 
			&& trans.len()==nlen*m);
		let pows_51 = build_pows_56_val();
		assert!(pows_51.len()==4);
		let unit= F::from((1<<(bits+4)) as u32);
		let hex = F::from(16 as u32);
		let mut st_cons = vec![F::zero();5];
		for i in 0..4{
			st_cons[i] += hex * pows_51[i];
			st_cons[i+1] += unit * pows_51[i];
		}
		let lb_one = LinearCombination::<F>(vec![(F::one(), Variable::One)]);
		//PACKED VERSIOn
		for dfa_id in 0..m{//for each DFA
			for i in 0..nlen/4{
				/* LOGICAL VERSION 
				let start = i * 4;
				let mut sum_trans = one.clone();
				let mut sum_exp = one.clone();
				for j in 0..4{//CHECK every 4 transitions
					let idx = start + j; //index of char
					let ch = &chars[idx];
					let st1 = &states[idx*m+dfa_id]; //already plus one
					let st2 = &states[(idx+1)*m+dfa_id];
					let exp_trans = ch + 
						&(st1 * &hex_var) +
						&(st2 * &unit_var); //no need to plus one, already did
					let trans = &trans[idx*m+dfa_id];
					sum_trans = &sum_trans + &(&pows_51[j] * trans); //cost 
						//nothing because mul with constant!
					sum_exp = &sum_exp + &(&pows_51[j] * &exp_trans); 
				}
				check_eq(&sum_trans, &sum_exp,  "ERROR checking trans")?;
				*/
				let start = i * 4;
				let mut vec_sum_trans = vec![(F::zero(), Variable::One); 9];
					//2 tuples for each tranistion
					//an additional one for the last st2.
				let mut vec_sum_exp = vec![(F::zero(), Variable::One); 4];
				for j in 0..4{
					let idx = start + j;
					let ch = &chars[idx];
					vec_sum_trans[j*2] = var_to_tuple_adv(ch, pows_51[j]);
					vec_sum_trans[j*2+1] = var_to_tuple_adv(
						&states[idx*m+dfa_id], st_cons[j]);
					if j==3{
						vec_sum_trans[j*2+2]=var_to_tuple_adv(&states[(idx+1)*m+dfa_id], st_cons[j+1]);
					}
					vec_sum_exp[j] = var_to_tuple_adv(&trans[idx*m+dfa_id], 
						pows_51[j]);
				}
				let lb1 = LinearCombination::<F>(vec_sum_trans);
				let lb3 = LinearCombination::<F>(vec_sum_exp);
				//to assert that sum of transition == sum of expected transition
				//for every 4 transitions given that they are already proved
				//in range.
				cs.enforce_constraint( lb1, lb_one.clone(), lb3)?;
			}
		}
		//IF nlen is not multiple of 4
		for dfa_id in 0..m{//for each DFA
			for idx in nlen/4*4 .. nlen{
				let ch = &chars[idx];
				let st1 = &states[idx*m+dfa_id]; //already plus one
				let st2 = &states[(idx+1)*m+dfa_id];
				let exp_trans = ch + 
					&(st1 * &hex_var) +
					&(st2 * &unit_var); //no need to plus one, already did
				let trans = &trans[idx*m+dfa_id];
				check_eq(&exp_trans, &trans, "ERROR checking trans part2")?;
			}
		}
		if b_perf{
			log_perf(self.job_id, log_level, "validate_mul_fsm step 3", &mut gt);
		}

		//4. subsig_res in {False=1,True=2}; si_oup = v_dfa_id + res
		//(+1 nonfinal, +2 final); oup copy = walk's last state. COST: 3m
		let names = vec!["subsig_res", "si_oup_state_copy", "oup_state_copy"]; 
		let cols = names.iter().map(|n| fsm_acc.get_container(n)
			.unwrap().lock().unwrap().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();
		let (subsig_res,si_oup,oup_copy) = (&cols[0], &cols[1], &cols[2]);
		let f_true = new_const_var(&cs, F::from(TriVal::True as u8));
		let f_false = new_const_var(&cs, F::from(TriVal::False as u8));
		for i in 0..m{
			let res = &subsig_res[i];
			(res - &f_false).mul_equals(&(res - &f_true), &zero)?;
			check_eq(&si_oup[i], &(&v_dfa_id[i] + res), "oup sid")?;
			check_eq(&oup_copy[i], &states[m*nlen + i], "oup copy")?;
		}

		if b_perf{
			println!(" ### validate_mul_fsm_acc_container: m: {}, nlen: {}. cost: {}", m, nlen, cs.num_constraints()-nc); 
		}
		if b_perf{
			log_perf(self.job_id, log_level, "validate_mul_fsm step 4", &mut gt);
		}

		Ok( () )
	}

	/// validate all given ipu_sigs are DISCHARGED correctly.
	///
	/// COST: 9*n1 +  14*n2
	/// where (n1 = num of sigs, n2 = num of subsigs)
	/// typically this is very small, n1 <4, n<10 => cost<300.
	/// this is adapted from the same function from compute_adv_sig.rs
	/// Here we made some simplification that there is no additional
	/// layer to turn extra layer of counter constraints. We 
	/// discharge sig from the eval_res_combo directly
	fn validate_discharge_sig_combo(&self, 
		eval_res_combo: &std::sync::Arc<std::sync::Mutex<Container<FpVar<F>>>>, 
		discharge_sig_combo: &std::sync::Arc<std::sync::Mutex<Container<FpVar<F>>>>, 
		r1: FpVar<F>,
		_r2: FpVar<F>,
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//0. retrieve data from combo
		let b_debug = B_DEBUG;
		let b_perf = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let nc = cs.num_constraints();
		let (zero,one)=(new_const_var(&cs,F::zero()),
			new_const_var(&cs,F::one()));
        let max_val:usize = (1<<read_global_config().range2_bit) - 1;
		let _max=new_const_var(&cs,F::from(max_val as u64));
		let _frg = new_const_var(&cs, F::from(RANGE2));
		let names = vec![ "v_sigs", "v_dnf_id", "v_dnf_step", 
			"v_dnf_count", "v_real_subsigs"];
		let cols = names.iter().map(|n|
			discharge_sig_combo.lock().unwrap()
				.get_container(n).unwrap().lock().unwrap().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		let (v_sigs, v_dnf_id, v_dnf_step, v_dnf_count, v_real_subsigs) = (
			&cols[0], &cols[1], &cols[2], &cols[3], &cols[4]);
		let sid_cols = names.iter().map(|n|
			discharge_sig_combo.lock().unwrap()
				.get_container(&format!("sid_{}",n)).unwrap().lock().unwrap().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		let (_v_sid_sigs, _v_sid_dnf_id, _v_sid_dnf_step, v_sid_dnf_count, 
			v_sid_real_subsigs) = (&sid_cols[0], &sid_cols[1], &sid_cols[2], 
				&sid_cols[3], &sid_cols[4]);
		let n = v_sigs.len();
		for i in 0..cols.len(){assert!(cols[i].len()==n);}
		for i in 0..cols.len(){assert!(sid_cols[i].len()==n);}
		if b_perf{
			log_perf(self.job_id, log_level, "validate_discharge_sig step 0", &mut gt);
		}

		//1. check the validity of sid cols (sequential as circ does not
		//allow parallelism)
		//
		// Cost: 5n -> 2n
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
			//no need for constants check
			//check_eq(&v_sid_dnf_id[i], &frg, "err sid dnf_id")?;
			//check_eq(&v_sid_dnf_step[i], &frg, "erro sid_dnf_step")?;
			//check_eq(&v_sid_sigs[i], &frg, "err id_sig")?;

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
		if b_perf{
			log_perf(self.job_id, log_level, "validate_discharge_sig step 1", &mut gt);
		}

		//2. Now prove that each sig in v_sigs is discharged as false
		//2.1 check that all subsig of a sig is well covered, i.e.,
		// the dnf_step is increasing, it starts from 0 and its
		// last step is equal to dnf_count.
		// NOTE that the validity of v_dnf_step, ... columns are proved
		// already via v_sid columns in step 1.
		//
		// COST: 9n - 7 (row: is_neq 3 + 5 mul + 1 eq; pin 1; T962 F3 1)
		check_eq(&v_sigs[0], &zero, "we require one dummy entry at begin")?;
		for i in 1..n{
			//T962 F2 (W3): block = one (sig, dnf) clause; both RANGE2
			let b_new_row = (&v_sigs[i]*&factor + &v_dnf_id[i])
				.is_neq(&(&v_sigs[i-1]*&factor + &v_dnf_id[i-1]))?;
			let i_new_row: FpVar<F> = b_new_row.into();
			// Ported from compute_sig_adv.rs (the SED twin of this gadget),
			// which carries the correct form. The DFA copy had the two
			// branches attached to the wrong i_new_row multipliers and a
			// missing "-1", so it was vacuous for count=1 disjuncts but
			// UNSAT for any count>=2 discharge combo. The dummy/zero
			// boundary is handled by multiplying each term by v_sigs[i]
			// / v_sigs[i-1] (not an extra is_neq).
			let res = (&i_new_row - &one) * &(//if NOT new row (continuing):
				//(a) dnf_step increases by one; ignore v_sigs[i]==0
				&(&v_dnf_step[i] - &v_dnf_step[i-1] - &one) * &v_sigs[i]
			) + &i_new_row * &(//if NEW row:
				//(b) starts from 0
				&(&r1 * &v_dnf_step[i]) +
				//(c) previous sig completed; ignore when v_sigs[i-1]==0
				&(&(&v_dnf_step[i-1] + &one - &v_dnf_count[i-1])
					* &v_sigs[i-1])
			);
			check_eq(&res, &zero, "fails well-formed check")?;
		}
		//T962 F3 (W2): close the last block too (pads are in front)
		check_prod_zero(&(&v_dnf_step[n-1] + &one - &v_dnf_count[n-1]),
			&v_sigs[n-1], LinearCombination::zero(), "last block closes")?;
		if b_perf{
			log_perf(self.job_id, log_level, "validate_discharge_sig step 2.1", &mut gt);
		}


		//2.2 build subsigs from (sig_id, real_subsig) and lookup
		// (subsig, False) in the (vec_subsig, vec_result) from the
		// previous eval_res(). This is needed
		// as the structure of subsigs are different between the 
		// two components.
		//
		// COST: 4n
		let (_bit_part1, bit_part2) =
			utils::consts::current_bit_parts();
		let fac2 = new_const_var(&cs, F::from(1u64<<bit_part2) );
		let f_false = new_const_var(&cs, F::from(TriVal::False as u8));

		let v_computed_subsig = v_sigs.iter().zip(v_real_subsigs.iter())
			.map(|(sig_id, real_subsig_id)| {
				sig_id*&fac2 + real_subsig_id
		}).collect::<Vec<FpVar<F>>>();

		let f_unit = FpVar::<F>::constant(F::from(1u32<<read_global_config().range2_bit));
		let src = encode_cols_var_adv_better(
			&vec![&v_computed_subsig[..], &vec![f_false.clone(); n][..]],
			&vec![0,1], &f_unit
		);
		//pad (0,1) for dummy entry
		//NOTE that here we assume that there are no SubsigCounterConstriant
		//they have two layers of synthesis.
		let inp_subsigs = eval_res_combo.lock().unwrap()
			.get_container("v_subsig").unwrap().lock().unwrap().to_vec();
		let subsig_result = eval_res_combo.lock().unwrap()
			.get_container("subsig_res").unwrap()
			.lock().unwrap().to_vec();
		let pad_subsigs = [&inp_subsigs[..], &vec![zero][..]].concat();
		let pad_res = [&subsig_result[..], &vec![f_false][..]].concat();
		let dst = encode_cols_var_adv_better(
			&vec![&pad_subsigs[..], &pad_res[..]],
			&vec![0,1], &f_unit
		);
		let mtbl_lkup_res = discharge_sig_combo.lock().unwrap()
			.get_container("mtbl_lk_res").unwrap().lock().unwrap().to_vec();
		assert_logup(cs.clone(), &src, &dst, &mtbl_lkup_res, &r1)?;
		if b_perf{
			log_perf(self.job_id, log_level, "validate_discharge_sig step 2.2", &mut gt);
		}

		//3. show that inp_sigs is a subset of v_sigs (covered)
		// where we have proved all v_sigs are discharged
		//note: v_sigs is shown earlier
		// to have at least one dummy entry at beginning so that just in
		// case inp_sigs has 0 entry.
		//
		//COST: let n1 = num of sigs, n = num of subsigs
		// 2n1 + 3n
		let discharged_sigs = discharge_sig_combo.lock().unwrap()
			.get_container("discharged_sigs").unwrap().lock().unwrap().to_vec();
		let mtbl_sigs= discharge_sig_combo.lock().unwrap()
			.get_container("mtbl_sigs").unwrap().lock().unwrap().to_vec();
		assert_logup(cs.clone(), &discharged_sigs, &v_sigs, &mtbl_sigs, &r1)?;

		if b_perf{
			log_perf(self.job_id, log_level, "validate_discharge_sig step 3", &mut gt);
		}

		if b_perf{
			println!(" ### check discharge_subsig: sig: {}, subsigs: {}, cost: {}", self.capacity.sigs, self.capacity.subsigs, cs.num_constraints()-nc);
		}
			
		Ok( () )

	}

}

impl <F:PrimeField + ColEle> SigmaGadget<F> for DfaAdvGadget<F>{
	fn get_name(&self)->&str {"DfaAdvGadget"}

	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
	}

	fn get_job_id(&self)->usize{
		self.job_id
	}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, cfgs_context: std::sync::Arc<Vec<ContainerConfig>>, idx: usize){
		self.cfgs_context = Some(cfgs_context);
		self.my_idx_in_context = Some(idx);
	}

	fn get_container_config(&self)->ContainerConfig{
		self.get_container_cfg().unwrap()
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
		let s = self.capacity.sigs;
		let su = self.capacity.subsigs;
		let n = self.capacity.max_nibble_len;

		//see sasert msg3
		36*su + 2*s + 3*su*n
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

	//TOTAL COST: (m- subsigs, n: nibble length, s = sigs) 
	// - note that subsigs are 
	// usually small
	// 10*m + mn*3/8 + 9*s + 14*m
	// 3/8*mn + 24m + 9*s
	// in practice: m<20, s<5. So the major cost is
	// 3/8 *mn
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>,
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig,
		_word_id: FpVar<F>, _subseg_id: FpVar<F>,
		_virt_vals: &mut Vec<FpVar<F>>)
		-> Result<(), SynthesisError>{
		//1. retrive the statement instance and get all parts
		let b_perf = false;
		let log_level = LOG1;
		let mut gt = GTimer::new();
		let nc = cs.num_constraints();
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;
		if b_perf{
			log_perf(self.job_id, log_level, "dfa: step 0. load stmt", &mut gt);
		}
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();

		//2. validate the fsm_acc combo 
		let mul_fsm_acc = stmt.get_container("mul_fsm_acc")?;
		self.validate_mul_fsm_acc_container(&mul_fsm_acc.lock().unwrap(), cs.clone())?;
		if b_perf{
			log_perf(self.job_id, log_level, "dfa: step 1. validate_mul_fsm ", &mut gt);
		}

		//2. validate the discharging of sig.
		let sig_res_combo= stmt.get_container("sig_res_combo")?;
		self.validate_discharge_sig_combo(&mul_fsm_acc,
			&sig_res_combo, r1.clone(), r2.clone(), cs.clone())?;
		if b_perf{
			log_perf(self.job_id, log_level, "dfa: step 2. validate_discharge_sig_combo", &mut gt);
		}

		if b_perf{
			println!(" ### dfa_adv: sigs: {}, subsigs: {}, nlen: {}, cost: {}",
				self.capacity.sigs,
				self.capacity.subsigs,
				self.capacity.max_nibble_len,
				cs.num_constraints()-nc
			);
		}
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
pub fn extract_sigid<F:PrimeField + ColEle>(subsig_id: F)->(F,F){
	let u_subsig_id = field_to_usize(&subsig_id);
	let (bit_part1, bit_part2) =
		utils::consts::current_bit_parts();
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
    use std::{sync::Arc};
	use ark_bn254::{Fr};
	use utils::{data::{pack_nibbles, pad_word_to_multiple,
		gen_pad_nibbles_fe}, os::{read_nibbles,proj_root}};
	use crate::gadgets::{
		word_extract::{
			LEGS,
			tests_word_extract_gadget::{test_gadget_adv, outer_lkup_ok},
		},
		dfa_adv::{DfaAdvGadget,DfaAdvAdvice,DfaAdvCapacity},
		word_extract_adv::{WordExtractAdvAdvice},
	};
	use data_processor::{clam_db::{ClamavDB}, 
		hex_acdfa::HexACDFA, type_def::{ClamavSig},
		clamav::{quick_discharge_file_by_crit_bag_pm,default_clamav_cfg},

	};
	use folding_schemes::folding::foldpot::{
		sigma_ir1cs::{SigmaGadget,WordInfo,DischargeSigInfo},
		container_config::ContainerConfig,
		circuits_super::field_to_usize,
	};
	use rustomaton::dfa::DFA;
	use std::sync::Mutex;
	use crate::gadgets::traits::{Container, IDX_INP, IDX_OUP};
	use crate::gadgets::word_extract_adv::WordExtractAdvGadget;
	use data_processor::type_def::TriVal;

	fn dfa_adv_case(tamper: &dyn Fn(&Arc<Mutex<Container<Fr>>>, &DFA<char>, Fr)) -> bool{
		let db = ClamavDB::<Fr>::build_db_from_dir("debug/dfa/simple")
			.expect("db err");
		dfa_adv_run(&db, "sig1", None, 2, tamper, &|_, _| {})
	}

	/// dfa_adv_case on sig `name` of `db` over word2.txt (T962). ks =
	/// Some((dnf, slot subsig idxs)) sets the discharge info by hand, else
	/// native info, slots vec_disjunc[0]. dis(mul_fsm_acc, sig_res_combo)
	/// tampers the discharge table.
	fn dfa_adv_run(db: &ClamavDB<Fr>, name: &str,
		ks: Option<(usize, Vec<usize>)>, subsigs: usize,
		tamper: &dyn Fn(&Arc<Mutex<Container<Fr>>>, &DFA<char>, Fr),
		dis: &dyn Fn(&Container<Fr>, &Container<Fr>)) -> bool{
		//1. load the clamdb instance. It has the following sigs
		//sig1: a....c|c....a
		//word: 22a9999d111111 (it's expect c with a gap of 4 from a, but
		// got a d)
		//DFA discharges it. The Critical pattern and SED fail because
		// pattern "a" and "c" too short.
		let path= "debug/dfa/simple";

		//2. create advice for word_extract_adv and dfa_adv
		// both advices are needed for producing related container_config
		// with external col referece.
		//2.1 the word_extract_adv. Pad-invariant rework (Step 5):
		// act_size MUST equal word.len(); pad word to wlen using
		// the canonical pseudo-random stream so the gadget DFA and
		// discharge_prover see identical pad nibbles.
		let wlen = 2usize;
		let nibbles_raw = read_nibbles(
			&format!("{}/data/{}/word2.txt",proj_root() , path));
		let f_nibbles = nibbles_raw.iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let word = pad_word_to_multiple::<Fr>(
			&pack_nibbles(&f_nibbles), wlen);
		let act_size = word.len();
		let cfg = default_clamav_cfg();
		let wi: Option<WordInfo> = ks.is_none().then(||
			quick_discharge_file_by_crit_bag_pm(
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
			true, &cfg,
			&db.sig_to_id, wlen, wlen, db.aggressive_max_span_nibbles
        ).1); //use optimize mode

		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, false)
			.expect("word_extract_adv err");
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.lock().unwrap().get_cfg(); 

		//2.2 the dfa_adv 
		let sig = &db.vec_sigs.iter().filter(|sig| sig.name==name)
			.map(|sig| sig.clone()).collect::<Vec<Arc<ClamavSig>>>()[0];
		let v_sigs = vec![sig.clone()];
		let sig_id = db.sig_to_id.get(&sig.name).unwrap();
		let info = &match &ks {
			Some((d, _)) => DischargeSigInfo{sig_name: name.to_string(),
				b_success: true, min_cost: 0, min_dnf_id: *d,
				subsig_ids: vec![0], subsig_igc: vec![false]},
			None => wi.unwrap().vec_dfa_sigs_info[0].clone(),
		};
		assert!(info.sig_name==name);
		let b_lk = ks.is_some(); //T962: red tests also check outer lookups
		let slots = ks.map(|k| k.1)
			.unwrap_or(sig.eval_dnf.vec_disjunc[0].clone());

		let discharge_infos = vec![info.clone()]; //only one sig to discharge
		let inp_sigs: Vec<Fr> = vec![Fr::from(*sig_id as u64)];
		// here we just take the first dnf, in practice it
		// will be decided by the DischargeInfo advice which dnf to discharge
		let inp_subsigs = v_sigs.iter().map(|_| slots.iter().map(|i|
				Fr::from(HexACDFA::gen_subsig_id_worker(*sig_id, *i+1) as u32)
			).collect::<Vec<Fr>>()
		).collect::<Vec<Vec<Fr>>>();
		let inp_raw_subsigs = v_sigs.iter().map(|_| slots.iter()
			.map(|i| Fr::from(*i as u64))
			.collect::<Vec<Fr>>()
		).collect::<Vec<Vec<Fr>>>();
		let v_dfa= v_sigs.iter().map(|sig| slots.iter().map(|i| 
				sig.vec_subsig_automaton[*i].clone()) //clone of Arc low cost
			.collect::<Vec<Arc<DFA<char>>>>()
		).collect::<Vec<Vec<Arc<DFA<char>>>>>();

		assert!(&v_sigs[0].name==name);
		let nibble_len = wlen*LEGS;
		let cap = DfaAdvCapacity{max_nibble_len: nibble_len, subsigs,
			sigs: 1};

		let nibbles = stmt_wea.lock().unwrap().get_container("nibbles").unwrap()
			.lock().unwrap().to_vec();
		// Under the pad-invariant rework, nibbles past the raw
		// f_nibbles tail are:
		//   (1) gen_pad_nibbles_fe(0, m1) — sub-F pad inside the
		//       last real F-element (pack_nibbles).
		//   (2) gen_pad_nibbles_fe(0, (wlen-big_m)*62) — F-level
		//       pad, packed contiguously into the trailing
		//       F-elements (pad_word_to_multiple).
		let total_n = nibbles.len();
		let raw_n = f_nibbles.len();
		let m1 = if raw_n % 62 == 0 {0} else {62 - (raw_n % 62)};
		let big_m = (raw_n + 61) / 62;
		let mut expected = f_nibbles.clone();
		if m1 > 0 {
			expected.extend(gen_pad_nibbles_fe::<Fr>(0, m1));
		}
		let f_pad_nibs = (wlen - big_m) * 62;
		if f_pad_nibs > 0 {
			expected.extend(
				gen_pad_nibbles_fe::<Fr>(0, f_pad_nibs));
		}
		assert!(expected.len() == total_n);
		assert!(nibbles == expected);

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
		let seg_id = Fr::zero();
		let adv_faa = DfaAdvAdvice::new(
			&nibbles, &v_subsig_ids, &v_fsm_id, 
			&v_dfa, &v_inp_state, &cap,
			&inp_sigs, &discharge_infos, &v_sigs, &db.sig_to_id, seg_id
		).expect("adv_dfa advice err");
		let stmt_faa = adv_faa.stmt_container;
		let cfg_faa = stmt_faa.lock().unwrap().get_cfg(); 

		{ let fsm = stmt_faa.lock().unwrap().get_container("mul_fsm_acc").unwrap();
		  tamper(&fsm, &v_dfa[0], v_fsm_id[0]); }
		{ let st = stmt_faa.lock().unwrap();
		  let (fsm, dc) = (st.get_container("mul_fsm_acc").unwrap(),
			st.get_container("sig_res_combo").unwrap());
		  dis(&fsm.lock().unwrap(), &dc.lock().unwrap()); }
		//2.3 given cfgs, set up the positions
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
		ContainerConfig::adjust_locations(&mut vec_cfg); //resolve

		//3. generate the 7 segments of output for building statment
		let cps1 = stmt_wea.lock().unwrap().gen_stmt_components(); 
		let cps2 = stmt_faa.lock().unwrap().gen_stmt_components(); 
		let cps = cps1.0.into_iter().zip(cps2.0.into_iter()).map(|(a,b)|
			vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();

		//4. create the gadget
		let lkup_share_size = 4usize;
		let mut fag = DfaAdvGadget::<Fr>::new(
			&cap, 
			&vec![cfg_wea.clone()],
		);
		fag.set_container_cfg(vec_cfg.clone().into(), 1);  //it's the 2nd cfg
		let _sizes = fag.get_to_add_size(); //test if sizes are ok
		let rg = Arc::new(fag);

		//5. test it
		std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
		})).is_ok() && (!b_lk || outer_lkup_ok(&cps, &db.lkup))
		//todo!("manually verify two cases if DFA hits accept state or not for two different test cases");
	}

	#[test]
	fn test_dfa_adv(){ assert!(dfa_adv_case(&|_, _, _| {})); }

	fn honest_false(fsm: &Container<Fr>){
		let r = fsm.get_col("subsig_res").unwrap().lock().unwrap().data[0];
		assert!(r == Fr::from(TriVal::False as u8), "fixture: honest res False");
	}

	/// T936 S5: oup_state_copy is not tied to the walk's last state.
	#[test]
	fn test_t936_s5_oup_copy_unbound(){
		let sat = dfa_adv_case(&|fsm, dfa, _id| {
			let fsm = fsm.lock().unwrap();
			honest_false(&fsm);
			let col = fsm.get_col("oup_state_copy").unwrap();
			let mut col = col.lock().unwrap();
			let honest = col.data[0];
			//another member of the +1 (nonfinal) table
			col.data[0] = (0..dfa.transitions.len())
				.filter(|s| !dfa.finals.contains(s))
				.map(|s| Fr::from((s + 1) as u32))
				.find(|v| *v != honest).expect("need 2 nonfinal states");
		});
		println!("DEBUG USE 69365.1: forged sat = {}", sat);
		assert!(!sat);
	}

	/// T936 S5: si_oup_state_copy may name +6 (all states), res False.
	#[test]
	fn test_t936_s5_oup_sid_all_states(){
		let sat = dfa_adv_case(&|fsm, _dfa, id| {
			let fsm = fsm.lock().unwrap();
			honest_false(&fsm);
			fsm.get_col("si_oup_state_copy").unwrap().lock().unwrap()
				.data[0] = id + Fr::from(6u32);
		});
		println!("DEBUG USE 69365.2: forged sat = {}", sat);
		assert!(!sat);
	}

	/// T936 S2 red test. ASCII hex char in the 4-bit slot of the sig-DFA
	/// trans pack makes (s,'1'..'6') alias (s-3,'a'..'f'). Forged walk takes
	/// a transition the DFA lacks; today circuit SAT and every
	/// (si_trans, trans) is a real table row.
	#[test]
	fn test_dfa_char_slot_alias(){
		use std::collections::HashSet;
		use std::panic::{catch_unwind, AssertUnwindSafe};
		use utils::data::u8_to_hex;
		use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget_adv_ex;
		let path= "debug/dfa/simple";
		let db = ClamavDB::<Fr>::build_db_from_dir(path).expect("db err");
		let wlen = 2usize;
		let nibbles_raw = read_nibbles(
			&format!("{}/data/{}/word2.txt", proj_root(), path));
		let f_nibbles = nibbles_raw.iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let word = pad_word_to_multiple::<Fr>(&pack_nibbles(&f_nibbles), wlen);
		let act_size = word.len();
		let cfg = default_clamav_cfg();
		let wi: WordInfo = quick_discharge_file_by_crit_bag_pm("word2.txt",
			&nibbles_raw, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
			&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
			&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
			&db.sig_to_id, wlen, wlen, db.aggressive_max_span_nibbles).1;
		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, false)
			.expect("wea err");
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.lock().unwrap().get_cfg();
		let sig = db.vec_sigs.iter().find(|s| s.name=="sig1").unwrap().clone();
		let sig_id = *db.sig_to_id.get(&sig.name).unwrap();
		let info = wi.vec_dfa_sigs_info[0].clone();
		assert!(info.sig_name=="sig1");
		let dnf = sig.eval_dnf.vec_disjunc[0].clone();
		let v_subsig_ids = dnf.iter().map(|i| Fr::from(
			HexACDFA::gen_subsig_id_worker(sig_id, *i+1) as u32))
			.collect::<Vec<Fr>>();
		let v_fsm_id = dnf.iter().map(|i| Fr::from(
			ClamavDB::<Fr>::dfa_id(sig_id as u32, *i as u32)))
			.collect::<Vec<Fr>>();
		let real_dfa = dnf.iter().map(|i| sig.vec_subsig_automaton[*i].clone())
			.collect::<Vec<Arc<DFA<char>>>>();
		let v_inp_state = real_dfa.iter()
			.map(|d| Fr::from((d.initial+1) as u32)).collect::<Vec<Fr>>();
		let cap = DfaAdvCapacity{max_nibble_len: wlen*LEGS, subsigs: 2, sigs: 1};
		let nibbles = stmt_wea.lock().unwrap().get_container("nibbles").unwrap()
			.lock().unwrap().to_vec();
		let tbl: HashSet<(Fr,Fr)> = db.lkup.vals.iter().cloned().collect();
		// T936 S2: every sig-DFA trans row holds the 4-bit nibble of its char
		let rb = utils::consts::read_global_config().range2_bit;
		for (d, id) in real_dfa.iter().zip(v_fsm_id.iter()){
			for (src, hm) in d.transitions.iter().enumerate(){ for (ch, dst) in hm{
				let v = ch.to_digit(16).unwrap() as u64 + (((src+1) as u64)<<4)
					+ (((*dst+1) as u64)<<(4+rb));
				assert!(tbl.contains(&(*id + Fr::from(3u32), Fr::from(v))),
					"DEBUG USE 69362.2: trans row ({},{}) not nibble-encoded", src, ch);
			}}
		}

		// (circuit SAT, all (si_trans,trans) rows in table)
		let run = |v_dfa: &Vec<Arc<DFA<char>>>| -> (bool, bool) {
			let adv = DfaAdvAdvice::new(&nibbles, &v_subsig_ids, &v_fsm_id,
				v_dfa, &v_inp_state, &cap, &vec![Fr::from(sig_id as u64)],
				&vec![info.clone()], &vec![sig.clone()], &db.sig_to_id,
				Fr::zero()).expect("adv err");
			let stmt_faa = adv.stmt_container;
			let fa = stmt_faa.lock().unwrap().get_container("mul_fsm_acc").unwrap();
			let tr = fa.lock().unwrap().get_container("trans").unwrap()
				.lock().unwrap().to_vec();
			let si = fa.lock().unwrap().get_container("si_trans").unwrap()
				.lock().unwrap().to_vec();
			let in_tbl = tr.iter().zip(si.iter())
				.all(|(t,s)| tbl.contains(&(*s,*t)));
			let cfg_faa = stmt_faa.lock().unwrap().get_cfg();
			let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
			ContainerConfig::adjust_locations(&mut vec_cfg);
			let cps1 = stmt_wea.lock().unwrap().gen_stmt_components();
			let cps2 = stmt_faa.lock().unwrap().gen_stmt_components();
			let cps = cps1.0.into_iter().zip(cps2.0.into_iter())
				.map(|(a,b)| vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();
			let mut fag = DfaAdvGadget::<Fr>::new(&cap, &vec![cfg_wea.clone()]);
			fag.set_container_cfg(vec_cfg.clone().into(), 1);
			let rg = Arc::new(fag);
			let sat = catch_unwind(AssertUnwindSafe(|| test_gadget_adv_ex::<Fr>(
				rg, &word, &cps[0], &cps[1], &cps[2], &cps[6], &cps[7],
				&vec![cps[3].clone(), cps[4].clone(), cps[5].clone()].concat(),
				4, false, Some(vec_cfg), true))).is_ok();
			(sat, in_tbl)
		};

		// find first alias site that changes the walk but keeps the verdict
		let s2: Vec<char> = u8_to_hex(&nibbles.iter()
			.map(|n| field_to_usize(n) as u8).collect()).chars().collect();
		let walk = |d: &DFA<char>| -> Vec<usize> {
			let mut v = vec![d.initial];
			for c in &s2 { let s = *v.last().unwrap(); v.push(d.transitions[s][c]); }
			v
		};
		let mut forged: Option<(usize, DFA<char>)> = None;
		'outer: for (j, d) in real_dfa.iter().enumerate(){
			let w = walk(d.as_ref());
			let n_st = d.transitions.len();
			for (i, &c) in s2.iter().enumerate(){
				let src = w[i];
				let alias = if ('1'..='6').contains(&c) && src >= 3 {
					Some((src-3, (c as u8 + 48) as char))
				} else if ('a'..='f').contains(&c) && src+3 < n_st {
					Some((src+3, (c as u8 - 48) as char))
				} else { None };
				let Some((s_al, c_al)) = alias else { continue };
				let d_al = d.transitions[s_al][&c_al];
				if d_al == d.transitions[src][&c] { continue; }
				assert!(c as usize + 16*(src+1) == c_al as usize + 16*(s_al+1));
				let mut f = d.as_ref().clone();
				f.transitions[src].insert(c, d_al);
				let fw = walk(&f);
				if d.finals.contains(fw.last().unwrap())
					!= d.finals.contains(w.last().unwrap()) { continue; }
				forged = Some((j, f));
				break 'outer;
			}
		}

		let (h_sat, h_tbl) = run(&real_dfa);
		assert!(h_sat && h_tbl, "honest must be SAT with table rows");
		let (j, f) = forged.expect("no alias site in word2.txt; use another word");
		assert!(walk(&f) != walk(real_dfa[j].as_ref()));
		let mut v_forged = real_dfa.clone();
		v_forged[j] = Arc::new(f);
		let (sat, in_tbl) = run(&v_forged);
		let sat = sat && in_tbl;
		println!("DEBUG USE 69362.1: forged sat = {}", sat);
		assert!(!sat);
	}

	/// T936 S4 red (O3-3): real subsig walked on the trap DFA, dfa_id
	/// (pre-fix: dfa_id check voided by v_sig = 0, v_raw_subsig = v_subsig).
	#[test]
	fn test_dfa_id_alias(){
		use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget_adv_ex;
		use data_processor::fsa_utils::build_trap_dfa;
		let path= "debug/dfa/simple";
		let db = ClamavDB::<Fr>::build_db_from_dir(path).expect("db err");
		let wlen = 2usize;
		let cfg = default_clamav_cfg();
		let nib2 = read_nibbles(&format!("{}/data/{}/word2.txt",proj_root(),path));
		let wi: WordInfo = quick_discharge_file_by_crit_bag_pm("word2.txt",
			&nib2, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
			&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
			&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
			&db.sig_to_id, wlen, wlen, db.aggressive_max_span_nibbles).1;
		// matching word: bytes 61 99 99 63 = "a..c" hits /a..c/
		let nib: Vec<u8> = "2261999963111111".chars()
			.map(|c| c.to_digit(16).unwrap() as u8).collect();
		let f_nib = nib.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let word = pad_word_to_multiple::<Fr>(&pack_nibbles(&f_nib), wlen);
		let adv_wea = WordExtractAdvAdvice::new(&word, word.len(), false).expect("wea");
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.lock().unwrap().get_cfg();
		let nibbles = stmt_wea.lock().unwrap().get_container("nibbles").unwrap()
			.lock().unwrap().to_vec();
		let sig = db.vec_sigs.iter().find(|s| s.name=="sig1").unwrap().clone();
		let sig_id = *db.sig_to_id.get(&sig.name).unwrap();
		let info = wi.vec_dfa_sigs_info[0].clone();
		assert!(info.sig_name=="sig1");
		let dnf = sig.eval_dnf.vec_disjunc[0].clone();
		let v_subsig = dnf.iter().map(|i|
			Fr::from(HexACDFA::gen_subsig_id_worker(sig_id, *i+1) as u32))
			.collect::<Vec<Fr>>();
		let hd = &sig.vec_subsig_automaton[dnf[0]];
		let hex = utils::data::u8_to_hex(&nibbles.iter()
			.map(|n| field_to_usize(n) as u8).collect::<Vec<u8>>());
		let mut st = hd.initial;
		for ch in hex.chars(){ st = *hd.transitions[st].get(&ch).unwrap(); }
		println!("DEBUG USE 69364.2: honest subsig match = {}", hd.finals.contains(&st));
		let n1 = v_subsig.len();
		let trap = Arc::new(build_trap_dfa());
		let dummy_id = Fr::from(ClamavDB::<Fr>::dfa_id_of_subsig(0));
		let cap = DfaAdvCapacity{max_nibble_len: wlen*LEGS, subsigs: 2, sigs: 1};
		let adv = DfaAdvAdvice::new(&nibbles, &v_subsig, &vec![dummy_id; n1],
			&vec![trap; n1], &vec![Fr::from(1u32); n1], &cap,
			&vec![Fr::from(sig_id as u64)], &vec![info], &vec![sig.clone()],
			&db.sig_to_id, Fr::zero()).expect("adv");
		let stmt = adv.stmt_container;
		let cfg_faa = stmt.lock().unwrap().get_cfg();
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
		ContainerConfig::adjust_locations(&mut vec_cfg);
		let cps1 = stmt_wea.lock().unwrap().gen_stmt_components();
		let cps2 = stmt.lock().unwrap().gen_stmt_components();
		let cps = cps1.0.into_iter().zip(cps2.0.into_iter())
			.map(|(a,b)| vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();
		let mut fag = DfaAdvGadget::<Fr>::new(&cap, &vec![cfg_wea.clone()]);
		fag.set_container_cfg(vec_cfg.clone().into(), 1);
		let rg = Arc::new(fag);
		let sat = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
			test_gadget_adv_ex::<Fr>(rg, &word, &cps[0], &cps[1], &cps[2],
				&cps[6], &cps[7],
				&vec![cps[3].clone(), cps[4].clone(), cps[5].clone()].concat(),
				4, false, Some(vec_cfg), true))).is_ok();
		println!("DEBUG USE 69364.1: forged sat = {}", sat);
		assert!(!sat);
	}

	/// T936 S9: v_subsig and its OUP copy sit at the same offset of the
	/// INP/OUP regions (as inp_state/oup_state), so the Horner hand-off
	/// pairs them across segments.
	#[test]
	fn test_t936_s9_io_offsets(){
		let wlen = 2usize;
		let g_wea = WordExtractAdvGadget::<Fr>::new(wlen, false);
		let cap = DfaAdvCapacity{max_nibble_len: wlen*LEGS, subsigs: 2, sigs: 1};
		let g = DfaAdvGadget::<Fr>::new(&cap, &vec![g_wea.dummy_cfg.clone()]);
		let dest = |p: &str| match g.dummy_cfg.search_by_path(
			&format!("dfa_adv_stmt mul_fsm_acc {}", p)).expect(p){
			ContainerConfig::Column(l, ..) => l.dest.unwrap(),
			_ => panic!("{} not a column", p)};
		let (a, b) = (dest("v_subsig"), dest("v_subsig_oup"));
		assert!(a.0==IDX_INP && b.0==IDX_OUP && a.1==b.1 && a.2==cap.subsigs
			&& b.2==a.2, "T936 S9: v_subsig copies misaligned");
		let (c, d) = (dest("states inp_state"), dest("states oup_state"));
		assert!(c.1==d.1 && c.2==d.2, "T936 S9: state cells misaligned");
	}

	/// T936 S9: the OUP copy must equal the row's v_subsig.
	#[test]
	fn test_t936_s9_subsig_oup_copy(){
		let sat = dfa_adv_case(&|fsm, _dfa, _id| {
			fsm.lock().unwrap().get_col("v_subsig_oup").unwrap()
				.lock().unwrap().data[0] += Fr::from(1u32);
		});
		println!("DEBUG USE 69369.1: relabelled oup copy sat = {}", sat);
		assert!(!sat);
	}

	// ---- T962 W2/W3 red tests: the DFA twin of csa F2/F3. A red test
	// asserts sat == !FIXED_<id>; revert the fix and flip it to see SAT. ----
	const FIXED_W2: bool = true;
	const FIXED_W3: bool = true;
	/// S = (0|1)&(2|3): negated clauses d0 = {0,1}, d1 = {2,3}, each count
	/// 2. No subsig hits word2 (no b/c/e/f nibble run); slots run all 4.
	const T962_SIG: &str = "sigM;Engine:51-255,Target:0;(0|1)&(2|3);\
		/bbbbeeee/;/eeeebbbb/;/ffffcccc/;/ccccffff/";

	/// T962: honest discharge of sigM by d0 ([pad, pad, (d0,0), (d0,1)]),
	/// table tamper `dis`, then sid tags + m-tables re-derived.
	fn t962_dfa_run(name: &str, dis: &dyn Fn(&Container<Fr>)) -> bool{
		use crate::gadgets::commons::{gen_m_table, encode_cols_better};
		let dir = format!("debug/t962/{}", name);
		std::fs::create_dir_all(format!("{}/data/{}", proj_root(), dir))
			.unwrap();
		let v = vec!["sigM".to_string()];
		let db = ClamavDB::<Fr>::build_test_db(&default_clamav_cfg(), &dir,
			&vec![T962_SIG.to_string()], &v, &v, &v).expect("db");
		dfa_adv_run(&db, "sigM", Some((0, vec![0, 1, 2, 3])), 4,
			&|_, _, _| {}, &|fsm, c| {
			let g = |c: &Container<Fr>, n: &str| c.get_col(n).unwrap()
				.lock().unwrap().data.clone();
			let set = |n: &str, v: Vec<Fr>| c.get_col(n).unwrap()
				.lock().unwrap().data = v;
			let f_false = Fr::from(TriVal::False as u8);
			assert!(g(fsm, "subsig_res")[..4].iter().all(|r| *r == f_false),
				"fixture: all 4 slots False");
			dis(c);
			let (sig, dnf, step, real) = (g(c, "v_sigs"), g(c, "v_dnf_id"),
				g(c, "v_dnf_step"), g(c, "v_real_subsigs"));
			let n = sig.len();
			let fac = Fr::from(1u64 << 32);
			let tag = |id: u32, i: usize| Fr::from(id) * fac * fac * fac
				+ sig[i] * fac * fac + dnf[i] * fac;
			set("sid_v_dnf_count", (0..n).map(|i| tag(0x98882405, i)).collect());
			set("sid_v_real_subsigs", (0..n).map(|i| tag(0x99992405, i)
				+ step[i]).collect());
			let fac2 = Fr::from(1u64 << utils::consts::current_bit_parts().1);
			let comp: Vec<Fr> = (0..n).map(|i| sig[i] * fac2 + real[i]).collect();
			let pad_inp = [&g(fsm, "v_subsig")[..], &[Fr::zero()]].concat();
			let pad_res = [&g(fsm, "subsig_res")[..], &[f_false]].concat();
			set("mtbl_lk_res", gen_m_table(
				&encode_cols_better(vec![&comp[..], &vec![f_false; n][..]],
					vec![0,1]),
				&encode_cols_better(vec![&pad_inp[..], &pad_res[..]], vec![0,1])));
			set("mtbl_sigs", gen_m_table(&g(c, "discharged_sigs"), &sig));
		})
	}
	fn t962_set1(c: &Container<Fr>, name: &str, i: usize, x: Fr){
		c.get_col(name).unwrap().lock().unwrap().data[i] = x;
	}
	fn t962_col(c: &Container<Fr>, name: &str) -> Vec<Fr>{
		c.get_col(name).unwrap().lock().unwrap().data.clone()
	}

	/// T962 W3 (F2): the last row (d0, step 1, subsig 1) is re-labeled
	/// d1 step 1 (subsig 3, False). Each row is DB-valid; the boundary
	/// looks at v_sigs only, so the mixed "clause" {0, 3} closes with
	/// count 2. Control: the honest table (same re-derive) is SAT.
	#[test]
	fn test_t962_dfa_w3_clause_mix(){
		assert!(t962_dfa_run("w3", &|_| {}), "control: honest SAT");
		let sat = t962_dfa_run("w3", &|c| {
			let n = t962_col(c, "v_sigs").len();
			assert!(t962_col(c, "v_dnf_id")[n-1].is_zero()
				&& t962_col(c, "v_dnf_step")[n-1] == Fr::from(1u32)
				&& t962_col(c, "v_dnf_count")[n-1] == Fr::from(2u32),
				"precondition: (d0, 1) last");
			t962_set1(c, "v_dnf_id", n-1, Fr::from(1u32));
			t962_set1(c, "v_real_subsigs", n-1, Fr::from(4u32)); //subsig 3
		});
		assert_eq!(sat, !FIXED_W3, "T962 W3: sat = {}", sat);
	}

	/// T962 W2 (F3): drop the last row (d0, step 1) and prepend a pad;
	/// the block (d0, step 0) of count 2 ends the table, never closed.
	#[test]
	fn test_t962_dfa_w2_last_block_trunc(){
		assert!(t962_dfa_run("w2", &|_| {}), "control: honest SAT");
		let sat = t962_dfa_run("w2", &|c| {
			let n = t962_col(c, "v_sigs").len();
			assert!(t962_col(c, "v_sigs")[0].is_zero()
				&& t962_col(c, "v_dnf_count")[n-1] == Fr::from(2u32),
				"precondition");
			for nm in ["v_sigs", "v_dnf_id", "v_dnf_step", "v_dnf_count",
				"v_real_subsigs", "sid_v_sigs", "sid_v_dnf_id",
				"sid_v_dnf_step", "sid_v_dnf_count", "sid_v_real_subsigs"] {
				let v = t962_col(c, nm);
				c.get_col(nm).unwrap().lock().unwrap().data =
					[&v[..1], &v[..n-1]].concat();
			}
		});
		assert_eq!(sat, !FIXED_W2, "T962 W2: sat = {}", sat);
	}
}
