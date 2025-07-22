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
	//alloc::AllocVar,
	//eq::EqGadget,
	//R1CSVar,
};
use std::{any::Any, sync::{Arc}};
use data_processor::{
	clam_db::{ClamavDB, RANGE2_BIT
		//RANGE2,CHAR, STORE_SUBSIG,
	},
	//type_def::{SubsigPatternStore},
	fsa_utils::{build_dfa},
};
use crate::gadgets::{
	commons::{mix_vec,repeat_vec,
		//check_arr_eq,check_eq,check_increase,gen_m_table
	},
	traits::{Container,
		//Col,
		IDX_WORD, IDX_INP,IDX_DATA, 
		//IDX_SI_INP, 
		IDX_OUP, 
		//IDX_SI_OUP, 
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
		let dummy_dfa = Arc::new(build_dfa("",false));
		
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
			for i in 0..nibbles.len(){
				let ch: u8 = field_to_usize(&nibbles[i]).try_into().unwrap();
				let dst = dfa.transitions[src].get(&(ch as char)).unwrap();
				println!("DEBUG USE 6501: DFA {}: src: {}, ch: {} -> dst: {}", 
					j, src, ch, dst);
				let trans = (ch as usize) 
					+ ((src+1)<<4) + ((dst+1)<<(4+RANGE2_BIT));
				v_states[i+1] = F::from((dst+1) as u32);
				v_trans[i] = F::from(trans as u64);
				src = *dst;
			}
			let v_sid_states = vec![f_id_state; nlen+1];
			let v_sid_trans = vec![f_id_trans; nlen];
			(v_states, v_trans, v_sid_states, v_sid_trans)
		}).collect::<Vec<(Vec<F>,Vec<F>,Vec<F>,Vec<F>)>>();

		//1.2 assembl slice references for later mixing.

		let v2d_states = v2d.iter().map(|v| &v.0[..]).collect::<Vec<&[F]>>();
		let v2d_trans= v2d.iter().map(|v| &v.1[..]).collect::<Vec<&[F]>>();
		let v2d_sid_states= v2d.iter().map(|v| &v.2[..]).collect::<Vec<&[F]>>();
		let v2d_sid_trans= v2d.iter().map(|v| &v.3[..]).collect::<Vec<&[F]>>();

		/*
		assert!(raw_states.len()==nlen+1 && raw_locs.len()==nlen+1);

		let f_id_state = F::from(fsm_id+6);
		let f_id_trans= F::from(fsm_id+3);
		let f_id_loc= F::from(RANGE2);
		let f_char= F::from(CHAR);

		//1.1 the inp/mid/oup states
		let col_inp_state = Col::<F>::new(vec![raw_states[0]],
			"inp_state",IDX_INP);
		let col_si_inp_state = Col::<F>::new(vec![f_id_state],
			"si_inp_state",IDX_SI_INP);

		let col_mid_states = Col::<F>::new(raw_states[1..nlen].to_vec(),
			"mid_states", IDX_DATA);
		let col_si_mid_states = Col::<F>::new(vec![f_id_state; nlen-1], 
			"si_mid_states", IDX_SI_DATA);

		let col_oup_state = Col::<F>::new(vec![raw_states[nlen]],
			"oup_state",IDX_OUP);
		let col_si_oup_state = Col::<F>::new(vec![f_id_state],
			"si_oup_state",IDX_SI_OUP);

		let states = Container::concat_cols(
			vec![col_inp_state, col_mid_states, col_oup_state], "states");
		let si_states = Container::concat_cols(vec![col_si_inp_state, 
			col_si_mid_states, col_si_oup_state], "si_states");
		#[cfg(test)]{assert!(states.borrow().to_vec().len()==nlen+1);}
		#[cfg(test)]{assert!(si_states.borrow().to_vec().len()==nlen+1);}
		res.borrow_mut().add_container(states.clone()); //remove clone later
		res.borrow_mut().add_container(si_states);

		//1.2 the inp/mid/oup locations
		let col_inp_loc = Col::<F>::new(vec![raw_locs[0]],
			"inp_loc",IDX_INP);
		let col_si_inp_loc = Col::<F>::new(vec![f_id_loc],
			"si_inp_loc",IDX_SI_INP);

		let col_mid_locs = Col::<F>::new(raw_locs[1..nlen].to_vec(),
			"mid_locs", IDX_DATA);
		let col_si_mid_locs = Col::<F>::new(vec![f_id_loc; nlen-1], 
			"si_mid_locs", IDX_SI_DATA);

		let col_oup_loc = Col::<F>::new(vec![raw_locs[nlen]],
			"oup_loc",IDX_OUP);
		let col_si_oup_loc = Col::<F>::new(vec![f_id_loc],
			"si_oup_loc",IDX_SI_OUP);

		let locs = Container::concat_cols(
			vec![col_inp_loc, col_mid_locs, col_oup_loc], "locs");
		let si_locs = Container::concat_cols(vec![col_si_inp_loc, 
			col_si_mid_locs, col_si_oup_loc], "si_locs");
		#[cfg(test)]{assert!(locs.borrow().to_vec().len()==nlen+1);}
		#[cfg(test)]{assert!(si_locs.borrow().to_vec().len()==nlen+1);}
		res.borrow_mut().add_container(locs);
		res.borrow_mut().add_container(si_locs);

		//1.3. the transitions
		let col_trans = Col::<F>::new(trans, 
			"trans", IDX_DATA);
		let col_si_trans = Col::<F>::new(vec![f_id_trans; nlen],
			"si_trans", IDX_SI_DATA);
		#[cfg(test)]{assert!(col_trans.borrow().data.len()==nlen);}
		#[cfg(test)]{assert!(col_si_trans.borrow().data.len()==nlen);}
		res.borrow_mut().add_col(col_trans);
		res.borrow_mut().add_col(col_si_trans);

		//1.4 the nibbles (LATER when reconstructed, it is 
		// retrieved from previous word_extract_adv gadget
		let col_nibbles = Col::<F>::new_external(nibbles.to_vec(), 
			"nibbles", IDX_DATA, -1, "word_extract_stmt nibbles");
		let col_si_nibbles = Col::<F>::new_external(vec![f_char; nlen], 
			"si_nibbles", IDX_SI_DATA, -1, 
			"word_extract_stmt si_nibbles");
		#[cfg(test)]{assert!(col_nibbles.borrow().data.len()==nlen);}
		#[cfg(test)]{assert!(col_si_nibbles.borrow().data.len()==nlen);}


		res.borrow_mut().add_col(col_nibbles);
		res.borrow_mut().add_col(col_si_nibbles);
		*/
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
		let dummy_inp_states = vec![F::zero();n]; 
		let dummy_inp_subsigs = vec![F::zero(); n];
		let dummy_v_dfa_id = vec![F::zero();n];
		let dfa = Arc::new(build_dfa("", false));
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
	fn validate_mul_fsm_acc_container(&self, _fsm_acc: &Container<FpVar<F>>, _cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
		/*
		//1. asserts all states and transitions must be in range
		// NOTE: we do not have to assert in range for nibbles they
		// are done already in word_extract_adv gadget
		let nlen = self.capacity.max_nibble_len;
		let tblid_state = FpVar::new_constant(cs.clone(),
			F::from(self.fsm_id+6))?;
		let tblid_trans= FpVar::<F>::new_constant(cs.clone(), 
			F::from(self.fsm_id + 3))?;
		let si_states = fsm_acc.get_container("si_states")?.borrow().to_vec();
		let si_trans= fsm_acc.get_container("si_trans")?.borrow().to_vec();
		assert!(si_states.len()==nlen+1 && si_trans.len()==nlen);

		check_arr_eq(&si_states,&tblid_state,"checking states in range")?;
		check_arr_eq(&si_trans,&tblid_trans,"checking trans in range")?;

		//2. assert correctness of building transition as weighted sum
		// of src, char, dst states
		let unit_var = FpVar::<F>::new_constant(cs.clone(),
			F::from((1<<(self.capacity.acdfa_state_part_bits+4)) as u32))?;
		let hex_var = FpVar::<F>::new_constant(cs.clone(),
			F::from(16 as u32))?;
		let chars = fsm_acc.get_container("nibbles")?.borrow().to_vec();


		let states = fsm_acc.get_container("states")?.borrow().to_vec();
		let trans = fsm_acc.get_container("trans")?.borrow().to_vec();
		assert!(chars.len()==nlen && states.len()==nlen+1 && trans.len()==nlen);
		for i in 0..nlen{
			let ch = &chars[i];
			let st1 = &states[i]; //already plus one
			let st2 = &states[i+1];
			// simulate clam_db.rs: add_acdfa_to_lkup
			let exp_trans = ch + 
				&(st1 * &hex_var) +
				&(st2 * &unit_var); //no need to plus one, already did
			let trans = &trans[i];
			check_eq(&trans, &exp_trans, 
				&format!("checking transition {} ", i))?;
		}

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
		todo!()
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
		// sig1 - "abc....cba" 
		// sig2 - "1234567890abcdef" - for full alphabet
		// we will try to discharge word "abc1111111cb" (missing the last a)
		// via DFA approach.
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

		let adv_wea = WordExtractAdvAdvice::new(&word, act_size);
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
			&vec![cfg_wea.clone()]
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
