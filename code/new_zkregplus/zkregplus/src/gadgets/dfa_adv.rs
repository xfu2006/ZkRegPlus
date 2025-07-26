/* Created 07/16/2025, Completed: ?? */

//! This module dischages a nibble sequence against a collection
//! of DFAs (each one-to-one corresponding to a subsignature),
//! and reports the discharging status for each subsig.
//! It is a n-concurrent parallel version of the fsm component.
//! Then it assembles subsig result and report the discharge (via DFA)
//! result for sigs.

use rayon::iter::{ParallelIterator,IntoParallelIterator};
use std::{rc::{Rc},cell::{RefCell}};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity},
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
	//eq::EqGadget,
	//R1CSVar,
};
use std::{any::Any, sync::{Arc}};
use data_processor::{
	clam_db::{ClamavDB, RANGE2_BIT, RANGE2,CHAR_MAP,
		//STORE_SUBSIG,
	},
	//type_def::{SubsigPatternStore},
	fsa_utils::{build_trap_dfa},
};
use utils::{data::{u8_to_hex}};
use crate::gadgets::{
	commons::{mix_vec,new_const_var, check_eq
		//,gen_m_table
	},
	traits::{Container,
		Col,
		IDX_WORD, IDX_INP,IDX_DATA, 
		IDX_SI_INP, 
		IDX_OUP, 
		IDX_SI_OUP, 
		IDX_SI_DATA, ComponentAdvice
	},
	//db::{
		//assert_logup,
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
	//},
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
		self.subsigs>= other.subsigs
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(DfaAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			subsigs: self.subsigs,
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
	) ->Self{
		let stmt_container = Container::<F>::new("dfa_adv_stmt");
		//1. padding the input when necessary
		let dummy_fsm_id = F::from(ClamavDB::<F>::dfa_id(0, 0));
		let dummy_dfa = Arc::new(build_trap_dfa());
		
		let n = capacity.subsigs;
		let n1 = inp_subsigs.len();
		assert!(n>=n1, "capacity.subsigs: {} < inp_subsigs: {}. adjust DfaCapacity.subsigs", n, n1);
		let n2 = n - n1;
		let zero = F::zero();
		assert!(v_dfa_id.len()==n1 && v_dfa.len()==n1);
		let inp_subsigs = [&inp_subsigs[..], &vec![zero;n2][..]]
			.concat();
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
		let mul_fsm_acc = Self::gen_mul_fsm_acc_combo(
			nibbles, &inp_subsigs, &v_dfa_id, &v_dfa, &inp_states, capacity
		);
		stmt_container.borrow_mut().add_container(mul_fsm_acc);

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
	#[allow(dead_code)]
	fn gen_mul_fsm_acc_combo(
		nibbles: &Vec<F>, 
		inp_subsigs: &Vec<F>,  //will be padded to full #subsigs by capacity
		v_dfa_id: &Vec<F>, //the ids generaed by gen_dfa_id in clamdb
		v_dfa: &Vec<Arc<DFA<char>>>, //1-1 corresponding to inp_subsigs
		inp_states: &Vec<F>,
		capacity: &DfaAdvCapacity) 
	-> Rc<RefCell<Container<F>>>{
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

		//2. create the dummy advice and cfg
		let dummy_adv = DfaAdvAdvice::new(&nibbles, &dummy_inp_subsigs,
			&dummy_v_dfa_id, &dummy_v_dfa, &dummy_inp_states, capacity);
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
	fn validate_mul_fsm_acc_container(&self, fsm_acc: &Container<FpVar<F>>, cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
		//REMOVE LATER ------------
		let n0 = 0;
		//REMOVE LATER ------------
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
		//REMOVE LATER -------------------
		println!("DEBUG USE 7701: step 1 cost: {}, susigs: {}",
			cs.num_constraints()-n0, n);
		//REMOVE LATER ------------------- ABOVE

		//2. asserts all states and transitions must be in range
		// NOTE: we do not have to assert in range for nibbles they
		// are done already in word_extract_adv gadget.
		// in WordExtractAdv gadget: it has an nibbles_copy column
		// and it is PROVED that nibbles are already in "CHAR" range.
		// Here for the nibbles, they are lableled to their corresponding
		// translation, and this is gauranteed correct translation
		// given the nibbles_copy proof.
		//
		// COST: 2*m*n 
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
		//REMOVE LATER -------------------
		println!("DEBUG USE 7701: step 2 cost: {}, nlen: {}, subsigs: {}",
			cs.num_constraints()-n0, nlen, m);
		//REMOVE LATER ------------------- ABOVE

		//3. assert correctness of building transition as weighted sum
		// of src, char, dst states
		//
		//COST: 3*m*nlen
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
		//REMOVE LATER -------------------
		println!("DEBUG USE 7701: step 3 cost: {}, dfas: {}, nlen: {}",
			cs.num_constraints()-n0, m, nlen);
		//REMOVE LATER ------------------- ABOVE

		/*
		//3. assert the locations (increasing by 1)
		let locs = fsm_acc.get_container("locs")?.borrow().to_vec();
		assert!(locs.len()==nlen+1);
		check_increase(&locs)?;

		*/
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

	/// return the sizes of inp/oup/data to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		for i in 0..3 {assert!(to_add[i+1] == to_add[4+i]);}

		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA])
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

		//2. validate the fsm_acc combo 
		let mul_fsm_acc = stmt.get_container("mul_fsm_acc")?;
		self.validate_mul_fsm_acc_container(&mul_fsm_acc.borrow(), cs.clone())?;

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
		hex_acdfa::HexACDFA, type_def::{ClamavSig}
	};
	use folding_schemes::folding::foldpot::{
		sigma_ir1cs::SigmaGadget,
		container_config::ContainerConfig,
		circuits_super::field_to_usize,
	};
	use rustomaton::dfa::DFA;

	#[test]
	fn test_dfa_adv(){
		//1. load the clamdb instance. It has the following sigs
		//sig1: abc....123|123...abc
		//word: abc9999122cc (the 122 missing "3")
		//DFA discharges it
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

		//note: set true to use char map for nibbles.
		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, true);
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.borrow().get_cfg(); 

		//2.2 the dfa_adv (regular case, and SED approach)
		let sig = &db.vec_sigs.iter().filter(|sig| sig.name=="sig1")
			.map(|sig| sig.clone()).collect::<Vec<Arc<ClamavSig>>>()[0];
		let v_sigs = vec![sig.clone()];
		let sig_id = db.sig_to_id.get(&sig.name).unwrap();
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
		let cap = DfaAdvCapacity{max_nibble_len: nibble_len, subsigs: 2};

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
			&v_dfa, &v_inp_state, &cap
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
