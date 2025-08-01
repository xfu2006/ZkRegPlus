/* Recreated 04/03/2025, Completed: 05/04/2025 */

//! This module generates the (pat-loc) for a nibble sequence.

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
use std::any::Any;
use data_processor::{
	hex_acdfa::HexACDFA,
	clam_db::{RANGE2,CHAR, STORE_SUBSIG,RANGE2_BIT},
	type_def::{SubsigPatternStore},
};
use crate::gadgets::{
	commons::{check_arr_eq,check_eq,check_increase,gen_m_table},
	traits::{Container,Col,IDX_WORD, IDX_INP,IDX_DATA, IDX_SI_INP, 
		IDX_OUP, IDX_SI_OUP, IDX_SI_DATA,ComponentAdvice},
	db::{assert_logup,verify_encoded_table,assert_well_formed_sorted,col_to_sorted_set, verify_col_to_sorted_set, tbl_filtered_to_sorted_tbl, verify_tbl_filtered_to_sorted_tbl,tbl_to_sorted_tbl, verify_tbl_to_sorted_tbl, tbl_left_join, verify_tbl_left_join},
};

// -----------------------------------------------
//		Structs
// -----------------------------------------------

/// Capacity of the gadget
#[derive(Clone,Debug)]
pub struct FsmAdvCapacity{
	/// should be LEGS (62) x max_word_len
	pub max_nibble_len: usize, 

	/// how many bits are used to represent a state
	pub acdfa_state_part_bits: usize,

	/// how many subsigs in input
	pub subsigs: usize,

	/// average number of patterns over subsigs
	/// this is the average of the number of steps for a subsig.
	/// This determines the estimated (pat-state) pairs over subsigs
	pub avg_pats_per_subsig: usize,

	/// size of the final product (subsig-state-pat-loc) table
	/// This is usually much smaller than the max_nibble_len,
	/// It is mainly decided by the
	/// ** percentage of final states in trace **
	/// This ratio is usually VERY SMALL.

	/// NOTE:  percentage number, e.g. 50 means 50 percent.
	/// avg_pats*per_trace_perc/100 * max_nibble_len -> SIZE of packed tracke
	/// wherethe packed trace is the (pat, loc) table size. 
	/// This is a hybird
	/// ratio primary determined by the ratio of final states appearing
	/// in a trace, and then `enlarged` by the number of patterns associated
	/// with each state (we would not call multiply here as states have
	///  different ratio of appearance). We put it an `estimate` of such
	/// compund ratio. Usually this is a very small number, if the
	/// final states do not appear frequently (i.e., do not use small
	/// pattern words to generate ACDFA).
	pub perc_pats_in_trace: usize,
}

/// Advice for the WordExtract Gadget.
#[derive(Clone,Debug)]
pub struct FsmAdvAdvice<F:PrimeField>{
	/// the first id related to the corresponding ACDFA
	pub fsm_id: u32,

	/// the statement container object which is serialized to a vector
	/// of statement
	pub stmt_container: Rc<RefCell<Container<F>>>,

	/// capacity
	pub capacity: FsmAdvCapacity,
}

#[allow(dead_code)]
/// This gadget is responsible for checking transitions
/// of running a finite state machine. Compread with fsm.rs,
/// it also produces (state, loc) where loc starts from 1,
/// and indicates the location of the state in the ENTIRE trace (considering
/// all folding steps). It produces a compressed table
/// as following:
///   `(sig_id, state, id, total, loc)`
///  where all locations of a state are grouped together, and
/// id starts from 1, with ``total" number of locations belong to
/// each state.
/// E.g., the following shows two states belong to 1 signature (100), 
///  one with 2 locations, and one with 3 locations.
///  (100, 101,1,2,101), (100, 101,2,2,222), 
///  (100, 201,1,3,77), (100, 201,2,3,78), (100, 201,3,3,99)
/// All entries of such table are sorted.
#[derive(Clone,Debug)]
pub struct FsmAdvGadget<F:PrimeField>{ 
	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	pub fsm_id: u32, 
	/// the capacity
	pub capacity: FsmAdvCapacity,

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
impl Capacity for FsmAdvCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		let other = r_other.as_any().downcast_ref::<FsmAdvCapacity>()
			.expect("downcast err"); 
		assert!(self.acdfa_state_part_bits == other.acdfa_state_part_bits);

		self.max_nibble_len >= other.max_nibble_len &&
		self.subsigs >= other.subsigs &&
		self.avg_pats_per_subsig >= other.avg_pats_per_subsig &&
		self.perc_pats_in_trace >= other.perc_pats_in_trace

	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(FsmAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			acdfa_state_part_bits: self.acdfa_state_part_bits,
			subsigs: self.subsigs,
			avg_pats_per_subsig: self.avg_pats_per_subsig,
			perc_pats_in_trace: self.perc_pats_in_trace,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField> NdAdvice for FsmAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> ComponentAdvice<F> for FsmAdvAdvice<F>{
	fn get_container(&self)->Rc<RefCell<Container<F>>>{
		self.stmt_container.clone()
	}
}

impl <F: PrimeField> FsmAdvAdvice<F>{
	/// Given nibbles and ACDFA, produce the (state,loc) sequence, sorted
	/// by loc.
	/// Input: (input_state, inp_location) 
	pub fn new(
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's already adjusted (starting from 1)
		inp_loc: F, //it's starting from 1 (for first component). 
		inp_subsigs: &Vec<F>,
		capacity: &FsmAdvCapacity, 
		fsm_id: u32,
		store_subsig_pat: &SubsigPatternStore
	) ->Self{
		let stmt_container = Container::<F>::new("fsm_adv_stmt");
		//1. construct the fsm_acc combo which has the transition
		// info and results in (state, loc) columns
		let fsm_acc = Self::gen_fsm_acc_combo(nibbles, acdfa, 
			inp_state, inp_loc, capacity, fsm_id);
		let fsm_acc2 = fsm_acc.clone(); //low cost, need to add
		//fsm_acc to fix location first before we build exteranl cols from it.
		stmt_container.borrow_mut().add_container(fsm_acc);

		//2. construct the projected subsig-state-pattern store and the proof
		//for it
		assert!(inp_subsigs.len()<=capacity.subsigs);
		let inp_subsigs = vec![inp_subsigs.clone(), vec![F::zero(); 
			capacity.subsigs-inp_subsigs.len()]].concat();
		let proj_store_combo = Self::gen_proj_store_combo(&inp_subsigs, 
			store_subsig_pat,fsm_id, capacity);
		let proj_store_combo2 = proj_store_combo.clone(); //rc clone low cost
		stmt_container.borrow_mut().add_container(proj_store_combo);

		//3. construct the packed tracie
		let packed_trace_combo = Self::gen_packed_trace_combo(&fsm_acc2,
			&proj_store_combo2, capacity);
		stmt_container.borrow_mut().add_container(packed_trace_combo);


		Self{capacity: Clone::clone(capacity), fsm_id,
			stmt_container}
	}

	/// Given the input generates the container of the following
	/// structure: root level name: fsm_acc
	/// nibbles
	/// states: (inp, mid, oup): modeled as a container of 3 columns
	/// locs: (inp, mid, oup)
	/// trans
	///
	/// si_nibbles
	/// si_states (inp, mid, oup)
	/// si_locs (inp, mid, oup)
	/// si_trans
	fn gen_fsm_acc_combo(
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's the adjusted state (starting rom 1)
		inp_loc: F, //starting from 1. 
		capacity: &FsmAdvCapacity, 
		fsm_id: u32) 
	-> Rc<RefCell<Container<F>>>{
		let res = Container::<F>::new("fsm_acc");
		let nlen = capacity.max_nibble_len;
		assert!(nlen==nibbles.len(), "nlen: {}, nibbles.len: {}", nlen, nibbles.len());
		let acdfa_state_part_bits = acdfa.state_part_bits;
		let mut raw_states = vec![];
		let mut raw_locs = vec![];
		let mut trans = vec![];
		let mut cur_state = field_to_usize(&inp_state) - 1;
		// NOTE: state needs to be added 1 to be pushed
		// 0 is considered padding value. Similarly loc starts from 1
		raw_states.push(F::from( (cur_state+1) as u32));
		let mut cur_loc = inp_loc.clone();
		raw_locs.push(inp_loc);
		let unit = F::from((1<<(acdfa_state_part_bits+4)) as u32);
		let hex = F::from(16 as u32);
		let one = F::one();
		for i in 0..nibbles.len(){
			let ch: u8 = field_to_usize(&nibbles[i]).try_into().unwrap();
			let nxt_state = acdfa.trans.get(&cur_state).unwrap()[ch as usize];
			raw_states.push(F::from( (nxt_state+1) as u32)); 

			let f_ch = F::from(ch);
			let f_src = F::from(cur_state as u32);
			let f_dst = F::from(nxt_state as u32);
			let tr = f_ch + (f_src + one) * hex + (f_dst + one) * unit;
			trans.push(tr);
			cur_state = nxt_state;
			cur_loc = cur_loc + one;
			
			raw_locs.push(cur_loc);
		}
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

		res	
	}

	/// Generate the projected SubsigPatternStore and its PROOF as a combo.
	/// It consists of
	/// Columns of the SubsigPatternStore (5 cols)
	/// Col: Encoded subsigpattern store
	/// Its corresponding subtbl_id 
	///
	/// Note: call assert_proj_store_combi() in assert_msg3.
	fn gen_proj_store_combo(
		inp_subsigs: &Vec<F>, 
		store_subsig_pat: &SubsigPatternStore,
		fsm_id: u32,
		capacity: &FsmAdvCapacity,
	)->Rc<RefCell<Container<F>>>{
		//1. generate the projected store
		let state_part_bits = capacity.acdfa_state_part_bits;
		assert!(state_part_bits == RANGE2_BIT);
		let subsig_ids = inp_subsigs.iter().map(|f| field_to_usize(f))
			.collect::<Vec<usize>>();
		assert!(subsig_ids.len()==capacity.subsigs);
		let n = capacity.subsigs * capacity.avg_pats_per_subsig;
		let proj_store = store_subsig_pat.project_by(&subsig_ids);
		let mut cols = proj_store.gen_cols::<F>(state_part_bits, Some(n));
		cols.push(inp_subsigs.clone());
		let f_substore_id = F::from((fsm_id + STORE_SUBSIG) as u32);
		let f_range2 = F::from(RANGE2 as u32);
		let n = cols[0].len(); //same for all
		//just need to check all subfields in RANGE2 and then encoded
		//ensure that e.g., states in the right range.
		//the enocded column does need to be checked in f_substore_id
		let mut sid_cols = vec![
			vec![f_range2; n],  //subfield: subsig
			vec![f_range2; n],  //id1 
			vec![f_range2; n],  //state (no need to check see above),
								//also it saves cost as there are 0 and max vals
			vec![f_range2; n],  //id2 
			vec![f_range2; n],  //pat 
			vec![f_substore_id; n], //encoded
			vec![f_range2; inp_subsigs.len()], //subsigs
		];
		assert!(sid_cols.len()==cols.len());

		//2. for proving that all inpu_subsigs are covered in 
		// the projected store (the logup related m_table)
		let m_tbl = gen_m_table(&inp_subsigs, &cols[0]);
		let sid_m_tbl = vec![f_range2; n];
		assert!(m_tbl.len()==sid_m_tbl.len());
		cols.push(m_tbl);
		sid_cols.push(sid_m_tbl);

		//3. convert them to columns.
		let res = Container::<F>::new("proj_subsig_store");
		let col_names = vec!["subsig", "id1", "state", "id2", "pat", 
			"encoded", "inp_subsigs", "m_tbl"];
		let cols:Vec<_> = cols.iter().zip(col_names.iter()).map(|(d,n)|
			Col::<F>::new(d.to_vec(), n, IDX_DATA)).collect();
		let sid_cols:Vec<_> = sid_cols.iter().zip(col_names.iter()).map(|(d,n)|
			Col::<F>::new(d.to_vec(),&format!("sid_{}", n),IDX_SI_DATA))
			.collect();


		//note not much cost as it's rc
		for i in 0..cols.len(){ res.borrow_mut().add_col(cols[i].clone()); }
		for i in 0..sid_cols.len(){res.borrow_mut().add_col(sid_cols[i].clone());}


		res

	}

	/// Generate packed_trace in the following form:
	/// (subsig, state, pat, loc) where loc is sorted for key:(subsig,state,pat)
	/// It includes all the corresponding proofs for the claim.
	/// 
	/// Workflow: 
	/// (1) projected_subsig_store -> sorted set of states 
	/// (2) (state,loc) -- filter by sorted set of states --
	///    ---> well formed table (state, id, loc)
	/// (3) do table join (sugsit, pat, state) join with (state, id, loc)
	///    over key state. Basically, expand each (subsig, pat, state)
	///    with multiple entries of loc.
	///
	/// NOTE that since the ratio of final states in (state,loc) trace.
	/// Even the concrete table join cost is high, but since table size
	/// is small, it's going to be much smaller than the trace size.
	#[allow(dead_code)]
	fn gen_packed_trace_combo(
		fs_acc_combo: &Rc<RefCell<Container<F>>>,
		proj_store_combo: &Rc<RefCell<Container<F>>>,
		capacity: &FsmAdvCapacity,
	)->Rc<RefCell<Container<F>>>{
		let res = Container::<F>::new("packed_trace");

		//1. extract proj_store_combo column "states" to a sorted set
		let ext_state= proj_store_combo.borrow()
			.get_container("state").unwrap().borrow()
			.duplicate_as_external(0,None);
		let ext_state = Rc::new(RefCell::new(ext_state));
		let sorted_set_size = capacity.avg_pats_per_subsig 
			* capacity.subsigs;
		let sorted_states = col_to_sorted_set(&ext_state, sorted_set_size, 
			"sorted_states");
		let sorted_states2 = sorted_states.clone(); //low cost rc clone
		res.borrow_mut().add_container(sorted_states); //once created, add it.

		//2. (state,loc) filtered by sorted_states 
		// --> sorted_and well formed table (state, id, loc)
		let state_col = Rc::new(RefCell::new(
			fs_acc_combo.borrow().get_container("states").unwrap().borrow()
			.duplicate_as_external(0, None)));
		let loc_col = Rc::new(RefCell::new(
			fs_acc_combo.borrow().get_container("locs").unwrap().borrow()
			.duplicate_as_external(0, None)));

		let packed_trace_size = capacity.perc_pats_in_trace * 
			capacity.max_nibble_len/100;
		let state_loc_tbl = tbl_filtered_to_sorted_tbl(
			&state_col, 
			&loc_col, 
			&sorted_states2, 
			packed_trace_size,
			"state_loc_tbl"
		).expect("tbl_filtered_to_sorted_tbl err");
		let state_loc_tbl2 = state_loc_tbl.clone(); //low cost clone rc

		res.borrow_mut().add_container(state_loc_tbl);


		//3. projecting the (subsig-state-pat) sorted set further
		// to (pat-state) sorted table for further tbl join.
		// where adjust avg_pats_per_subsig if too small.
		let pat_state_set_size = capacity.avg_pats_per_subsig 
			* capacity.subsigs;
		let ext_pat= proj_store_combo.borrow()
			.get_container("pat").unwrap().borrow()
			.duplicate_as_external(0,None);
		let ext_pat= Rc::new(RefCell::new(ext_pat));
		let pat_state_tbl = tbl_to_sorted_tbl( 
			&ext_pat, &ext_state, pat_state_set_size, "pat_state_tbl")
			.expect("tbl_filter err");
		let pat_state_tbl2 = pat_state_tbl.clone(); //clone rc low cost
		res.borrow_mut().add_container(pat_state_tbl);

		//4. left join (pat-state) and (state-loc) both are sorted table.
		let packed_trace_size = capacity.perc_pats_in_trace * 
			capacity.max_nibble_len / 100;
		let pat_state_loc_tbl = tbl_left_join(
			&pat_state_tbl2, &state_loc_tbl2, 
			&sorted_states2, packed_trace_size, "pat_state_loc_tbl")
			.expect("err join");

		let pat_col = pat_state_loc_tbl.borrow()
			.get_container("join_tbl").expect("err get join_tbl").borrow()
			.get_container_by_idx(0).borrow().duplicate_as_external(0,None);
		let loc_col = pat_state_loc_tbl.borrow()
			.get_container("join_tbl").expect("err get join_tbl").borrow()
			.get_container_by_idx(4).borrow().duplicate_as_external(0,None);

		res.borrow_mut().add_container(pat_state_loc_tbl);

		//5. compress pat_state_loc_tbl to pat_loc_tbl
		let pat_loc_tbl = tbl_to_sorted_tbl(
			&Rc::new(RefCell::new(pat_col)), 
			&Rc::new(RefCell::new(loc_col)), 
			packed_trace_size, "pat_loc").expect("err pat_loc"); 
		res.borrow_mut().add_container(pat_loc_tbl);

		//6. return
		res
	}
}

impl <F:PrimeField> FsmAdvGadget<F>{
	pub fn new(
		acdfa: &HexACDFA,
		capacity: &FsmAdvCapacity,
		fsm_id: u32, 
		prev_cfgs: &Vec<ContainerConfig>,
		store_subsig_pat: &SubsigPatternStore,
		)
	-> Self{
		//1. create the dummy input and dummy container config.
		let dummy_inp_state = F::one(); //adjusted loc
		let dummy_inp_loc = F::from(1u32);
		let nibbles = vec![F::zero(); capacity.max_nibble_len];
		let dummy_inp_subsigs = vec![
			F::from(store_subsig_pat.subsig_ids[0] as u32)];
		let dummy_adv = FsmAdvAdvice::new(&nibbles, acdfa, dummy_inp_state,
			dummy_inp_loc, &dummy_inp_subsigs, capacity, 
			fsm_id, store_subsig_pat);
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.borrow().get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[1].clone();

		Self{_f: PhantomData, capacity: Clone::clone(capacity), 
			cfgs_context: None,
			my_idx_in_context: None, dummy_cfg, fsm_id}
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
	fn validate_fsm_acc_container(&self, fsm_acc: &Container<FpVar<F>>, cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
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

		Ok( () )
	}

	/// validate the correctness of fsm_acc container
	/// Mainly it verifies 
	/// (1) the store is well formed (id sequence follows the
	///      pattern increasing, and two wrapper entries around each subtbl)
	/// (2) corresponding SI tables are correct
	/// (3) all inp_subsig_ids are indeed covered by the projected store
	/// -- implicity the proj_store is a projection of the external
	/// -- full proj_store (note that inp_subsig_ids are included
	/// -- as part of the proj_store_combo, as non-deterministic advice.
	/// -- this is fine, as we'll prove that it corresponds uniquely
	/// -- to the set of sigs to discharge.
	/// This needs r1 (a random challenge Fiat-Shamir) from msg2.
	fn validate_proj_subsig_store(&self, 
		proj_store: &Container<FpVar<F>>,  //the projected result
		r1: FpVar<F>,
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//1. check all subtable IDs are correct.
		// This includes the check that the encoded column is
		// indeed in the external lookup table.
		let col_names = vec!["subsig", "id1", "state", "id2", "pat", 
			"encoded", "inp_subsigs", "m_tbl"];
		let f_substore_id = F::from((self.fsm_id + STORE_SUBSIG) as u32);
		let f_range2 = F::from(RANGE2 as u32);
		let vals = vec![f_range2, f_range2, f_range2, f_range2, f_range2,
			f_substore_id, f_range2, f_range2].iter().map(|f|
				FpVar::new_constant(cs.clone(), f).unwrap())
			.collect::<Vec<_>>();
		let sid_cols = col_names.iter().map(|name|
			proj_store.get_container(&format!("sid_{}", name)).unwrap()
				.borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		assert!(sid_cols.len()==vals.len());
		for i in 0..vals.len(){
			check_arr_eq(&sid_cols[i], &vals[i], 
				&format!("err check sid of {}", col_names[i]))?;
		}

		//2. check the m_tbl proof
		let cols = col_names.iter().map(|name| proj_store.get_container(&name).
			unwrap().borrow().to_vec()
			).collect::<Vec<Vec<FpVar<F>>>>();
		let (subsig, id1, state, id2, pat, encoded, inp_subsigs, m_tbl) = 
		  (&cols[0],&cols[1],&cols[2],&cols[3],&cols[4],&cols[5],&cols[6],&cols[7]);
		assert_logup(cs.clone(), &inp_subsigs, &subsig, &m_tbl, &r1)?; 

		//3. check the validity of encoding
		let unit_bits = self.capacity.acdfa_state_part_bits;
		assert!(unit_bits==RANGE2_BIT, "reset HexACDFA state part bits or RANGE2_BIT so that they are aligned");
		verify_encoded_table(cs.clone(),
			unit_bits, &vec![subsig,id1,state,id2,pat], encoded)?;

		//4. check the table is wellformed 
		let unit_bits = self.capacity.acdfa_state_part_bits;
		//note: no sorted proof is needed as it's proved to be part of
		//external table, thus guarantee completeness of vals for a key.
		assert_well_formed_sorted(cs.clone(),subsig,id1,state,None,None,None,
			None, r1,unit_bits)?;

		Ok( () )
	}

	/// validate the correctness of packed_trace containercontainer
	#[allow(dead_code)]
	fn validate_packed_trace(
		&self, 
		r1: &FpVar<F>, //random nonce from msg2
		r2: &FpVar<F>, //random nonce from msg2
		all: &Container<FpVar<F>>,  //entire container
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//1. check sorted_set of states is correct
		let col_to_sorted_combo = all
			.search_container("fsm_adv_stmt packed_trace sorted_states")?;
		verify_col_to_sorted_set(r1, &col_to_sorted_combo.borrow(), cs.clone())?;

		//2. check the filtered table of state and loc
		let states_col = all.search_container( 
			"fsm_adv_stmt fsm_acc states")?;
		let locs_col = all.search_container(
			"fsm_adv_stmt fsm_acc locs")?;
		let state_loc_tbl = all.search_container(
			"fsm_adv_stmt packed_trace state_loc_tbl")?;
		let sorted_states = all.search_container(
			"fsm_adv_stmt packed_trace sorted_states")?;
		verify_tbl_filtered_to_sorted_tbl(&r1, &r2,
			&states_col, &locs_col, &sorted_states,  &state_loc_tbl, 
			cs.clone())?;

		//3. check the pattern_state_tbl
		let proj_pats_col = all.search_container( 
			"fsm_adv_stmt proj_subsig_store pat")?;
		let proj_states_col = all.search_container( 
			"fsm_adv_stmt proj_subsig_store state")?;
		let pat_state_tbl = all.search_container(
			"fsm_adv_stmt packed_trace pat_state_tbl")?;
		verify_tbl_to_sorted_tbl(&r1, &r2,
			&proj_pats_col, &proj_states_col, &pat_state_tbl, cs.clone())?;

		//4. check the pat_state_loc
		let pat_state_loc_tbl = all.search_container(
			"fsm_adv_stmt packed_trace pat_state_loc_tbl")?;
		verify_tbl_left_join(&r1, &r2,
			&pat_state_tbl, &state_loc_tbl, 
			&sorted_states, 
			&pat_state_loc_tbl, cs.clone())?;

		Ok( () )
	}

}

impl <F:PrimeField> SigmaGadget<F> for FsmAdvGadget<F>{
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

		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA], 0, 0)
	}

	fn est_cost(&self)->usize{
		// key is the low perc_pat_in_trace 
		let est = 
			118 * 
			self.capacity.max_nibble_len 
			* self.capacity.perc_pats_in_trace/100 			
		+ 107 * self.capacity.avg_pats_per_subsig * self.capacity.subsigs;

		est
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
		let fsm_acc = stmt.get_container("fsm_acc")?;
		self.validate_fsm_acc_container(&fsm_acc.borrow(), cs.clone())?;

		//3. validate the proj_subsig_store
		let pss = stmt.get_container("proj_subsig_store")?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();
		self.validate_proj_subsig_store(&pss.borrow(),r1.clone(),cs.clone())?;

		//3. validate the packed trace combo
		self.validate_packed_trace(&r1, &r2, &stmt, cs.clone())?;
		

		Ok(())
	}
}

// ---------------------------------------------------
// Utility Functions
// ---------------------------------------------------


#[cfg(test)]
pub mod tests_fsm_adv_gadget{
	use ark_ff::{Zero};
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use utils::{data::{pack_nibbles}, os::{read_nibbles,proj_root}};
	use crate::gadgets::{
		word_extract::{
			LEGS,
			tests_word_extract_gadget::{test_gadget_adv},
		},
		fsm_adv::{FsmAdvGadget,FsmAdvAdvice,FsmAdvCapacity},
		word_extract_adv::{WordExtractAdvAdvice},
	};
	use data_processor::{clam_db::{ClamavDB}};
	use folding_schemes::folding::foldpot::sigma_ir1cs::SigmaGadget;
	use folding_schemes::folding::foldpot::container_config::ContainerConfig;

	#[test]
	fn test_fsm_adv(){
		//1. load the clamdb instance. It has the following sigs
		// sig1 - "abc....cba" 
		// sig2 - "1234567890abcdef" - for full alphabet
		// mainly it will results failing discharge in CP because pattern
		// too small, but will be ok for SED (because min word len is 0).
		// the word to discharge "abc1111111cba" (will be discharged via
		// SED but not CP.).
		let path = "debug/sed/simple";
		let db = ClamavDB::<Fr>::build_db_from_dir(path);

		//2. create advice for word_extract_adv and fsm_adv
		// both advices are needed for producing related container_config
		// with external col referece.
		//2.1 the word_extract_adv
		let (wlen, act_size) = (2usize, 1usize);
		let nibbles_raw = read_nibbles(
			&format!("{}/data/{}/word.txt",proj_root() , path));
		let f_nibbles = nibbles_raw.iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let word = vec![pack_nibbles(&f_nibbles), vec![Fr::zero()]].concat();
		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, false);
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.borrow().get_cfg(); 

		//2.2 the fsm_adv (regular case, and SED approach)
		let b_igc = false;
		let bundle = &db.bundle_subsig;
		let acdfa = &bundle.vec_acdfa[0]; //store id is 0 for `all` (SED)
		let vec_sigs_to_discharge = vec![bundle.vec_sigs[0][0].clone()];
		assert!(&vec_sigs_to_discharge[0].name=="sig1");
		let (nibble_len, state_bits) = (wlen*LEGS, acdfa.state_part_bits);
		//todo!() NOTE THAT when subsigs is set to 400 it will crash
		//stack. check out why?
		let cap = FsmAdvCapacity{max_nibble_len: nibble_len, 
			acdfa_state_part_bits: state_bits, 
			subsigs: 4,
			avg_pats_per_subsig: 4,
			perc_pats_in_trace: 16 
		};

		let nibbles = stmt_wea.borrow().get_container("nibbles").unwrap()
			.borrow().to_vec();
		let f_nibbles = vec![f_nibbles.clone(), vec![Fr::zero(); 
			nibbles.len()-f_nibbles.len()]].concat();
			
		assert!(nibbles==f_nibbles);
		let inp_state = Fr::from((acdfa.init_state + 1) as u32);
		let inp_loc = Fr::from(1u32);
		let sig_id = 1;
		let subsig_id_raw = 1;
		let input_subsigs = vec![Fr::from(
			acdfa.gen_subsig_id(sig_id, subsig_id_raw) as u32)];  
		let fsm_id = ClamavDB::<Fr>::pm_acdfa_id(0, b_igc); //0 for all
		let adv_faa = FsmAdvAdvice::new(&nibbles, &acdfa, inp_state, 
			inp_loc, &input_subsigs, &cap, fsm_id, 
			&bundle.vec_subsig_stores[0]); //for SED
		let stmt_faa = adv_faa.stmt_container;
		let cfg_faa = stmt_faa.borrow().get_cfg(); 


		//2.3 given cfgs, set up the positions
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
		ContainerConfig::adjust_locations(&mut vec_cfg); //resolve


		//3. generate the 7 segments of output for building statment
		let cps1 = stmt_wea.borrow().gen_stmt_components(); //from inp to si_data
		let cps2 = stmt_faa.borrow().gen_stmt_components(); //from inp to si_data
		let cps = cps1.into_iter().zip(cps2.into_iter()).map(|(a,b)|
			vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();

		//4. create the gadget
		let lkup_share_size = 4usize;
		let mut fag = FsmAdvGadget::<Fr>::new(&acdfa, &cap, fsm_id,
			&vec![cfg_wea.clone()], &bundle.vec_subsig_stores[0]);
		fag.set_container_cfg(vec_cfg.clone().into(), 1);  //it's the 2nd cfg
		let _sizes = fag.get_to_add_size(); //test if sizes are ok
		let rg = Rc::new(fag);

		//3. test it
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

	}
}
