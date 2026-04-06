use std::sync::{Arc, Mutex};
/* Recreated 04/03/2025, Completed: 05/04/2025 
	Revise started: 10/30/2025
	Revised 2: 11/11/2025 (cut loc from data)
	Revised 3: 12/18/2025 (further improved circuit building cost
		by mainly pre-compute field inverse and direct encoding
		of LinearCombinations.
	Revised 4: 01/09/2026 (improve exception handling for capacity)
	Revised 5: further improve algorithm for handling superlarge
		size of states from projected subsig store (started 01/17/2026)
*/

// This module generates the (pat-loc) for a nibble sequence.
use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{logger::{log_perf, LOG1,LOG2}, 
	timer::Timer as GTimer, consts::ADD_CHAIN_SIZE};
use rayon::iter::{ParallelIterator,IntoParallelRefIterator,
	IndexedParallelIterator, IntoParallelIterator};
use std::{collections::{HashSet,HashMap}};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity},
		container_config::{ContainerConfig},
		circuits_super::field_to_usize,
		utils::{var_to_tuple_adv, var_to_tuple},
	}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef,Variable,
	LinearCombination};
use ark_r1cs_std::{
	fields::{
		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	//eq::EqGadget,
	R1CSVar,
};
use std::any::Any;
use data_processor::{
	hex_acdfa::HexACDFA,
	clam_db::{RANGE2,CHAR, STORE_SUBSIG,RANGE2_BIT},
	type_def::{SubsigPatternStore},
};
use crate::gadgets::{
	commons::{check_eq,gen_m_table,new_const_var,
		is_zero_better, new_var, build_pows_56_val,
		 var_to_lb, better_select_check, 
		 two_col_to_wide_wellformed,encode_cols_better,
		 verify_encode_cols_in_range},
	traits::{Container,Col,IDX_WORD, IDX_INP,IDX_DATA, IDX_SI_INP, 
		IDX_OUP, IDX_SI_OUP, IDX_SI_DATA,ComponentAdvice},
	db::{assert_logup,verify_encoded_table,assert_well_formed_sorted,col_to_sorted_set, verify_col_to_sorted_set, tbl_filtered_to_sorted_tbl, verify_tbl_filtered_to_sorted_tbl,tbl_to_sorted_tbl, verify_tbl_to_sorted_tbl, tbl_left_join, verify_tbl_left_join, verify_tbl_left_join_wide, assert_wide_wellformed, tbl_left_join_wide},
};

// -----------------------------------------------
//		Structs
// -----------------------------------------------

pub const B_FSM_ADV_NEW: bool = true; //new alg skils expensive proj_store

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
	/// ** basis (0.01 percent) final states in trace **
	/// This ratio is usually VERY SMALL.

	/// NOTE:  basis number, e.g. 50 means 50 basis points.
	/// avg_pats * basis_trace_perc/10000 * max_nibble_len -> 
	///     SIZE of packed tracke
	/// wherethe packed trace is the (pat, loc) table size. 
	/// This is a hybird
	/// ratio primary determined by the ratio of final states appearing
	/// in a trace, and then `enlarged` by the number of patterns associated
	/// with each state (we would not call multiply here as states have
	///  different ratio of appearance). We put it an `estimate` of such
	/// compund ratio. Usually this is a very small number, if the
	/// final states do not appear frequently (i.e., do not use small
	/// pattern words to generate ACDFA).
	/// the ratio of acc states along path is in avg 3% and max 5%.
	/// the expansion ratio from acc states to patterns in avg is 1.1
	/// so this number likely should be less than %6.
	pub basis_pats_in_trace: usize,

	/// Along the path (all states), what is the basis
	/// of the unique states.
	pub basis_unique_states: usize,

	/// Along the path how many how final states (allowing duplicates)
	/// and not restricted to the projected combo store
	/// Usually this is less than 5%, wost case 30%.
	pub basis_acc_states: usize,
}

/// Advice for the WordExtract Gadget.
#[derive(Clone,Debug)]
pub struct FsmAdvAdvice<F:PrimeField + ColEle>{
	/// distance to the word_extract gadget (sometimes it's 2)
	pub offset_wea: usize,

	/// the first id related to the corresponding ACDFA
	/// NOTE that as the gadget is ONLY CALLED in SED
	/// it has only two choices: IGC and CS for PM  (0x2000000 and 0x3000000)
	pub fsm_id: u32,

	/// the statement container object which is serialized to a vector
	/// of statement
	pub stmt_container: std::sync::Arc<std::sync::Mutex<Container<F>>>,

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
pub struct FsmAdvGadget<F:PrimeField + ColEle>{ 
	/// if this is for igc acdfa.
	b_igc: bool, 

	/// distance to the word_extract gadget (sometimes it's 2)
	pub offset_wea: usize,

	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	pub fsm_id: u32, 
	/// the capacity
	pub capacity: FsmAdvCapacity,

	// will be set when set_container_cfg is called
	pub cfgs_context: Option<std::sync::Arc<Vec<ContainerConfig>>>,
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
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		let other = r_other.as_any().downcast_ref::<FsmAdvCapacity>()
			.expect("downcast err"); 
		assert!(self.acdfa_state_part_bits == other.acdfa_state_part_bits);

		self.max_nibble_len >= other.max_nibble_len &&
		self.subsigs >= other.subsigs &&
		self.avg_pats_per_subsig >= other.avg_pats_per_subsig &&
		self.basis_pats_in_trace >= other.basis_pats_in_trace &&
		self.basis_unique_states >= other.basis_unique_states &&
		self.basis_acc_states >= other.basis_acc_states

	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(FsmAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			acdfa_state_part_bits: self.acdfa_state_part_bits,
			subsigs: self.subsigs,
			avg_pats_per_subsig: self.avg_pats_per_subsig,
			basis_pats_in_trace: self.basis_pats_in_trace,
			basis_unique_states: self.basis_unique_states,
			basis_acc_states: self.basis_acc_states,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField + ColEle> NdAdvice for FsmAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField + ColEle> ComponentAdvice<F> for FsmAdvAdvice<F>{
	fn get_container(&self)->std::sync::Arc<std::sync::Mutex<Container<F>>>{
		self.stmt_container.clone()
	}
}

/// Helper function to report states with high appearance frequencies and their patterns.
fn report_top_states<F: ark_ff::PrimeField + ColEle>(
	states: &[F], 
	acdfa: &HexACDFA, 
	top_n: usize,
	label: &str
) {
	let mut counts = HashMap::<usize, usize>::new();
	for f in states.iter() {
		if f.is_zero() { continue; }
		let real_id = folding_schemes::folding::foldpot::circuits_super::field_to_usize(f) - 1;
		*counts.entry(real_id).or_insert(0) += 1;
	}

	let mut sorted: Vec<_> = counts.into_iter().collect();
	sorted.sort_by(|a, b| b.1.cmp(&a.1));

	println!("\n --- [DEBUG USE 6703] Top {} High Frequency States for {} ---", top_n, label);
	for (state_id, freq) in sorted.into_iter().take(top_n) {
		if acdfa.is_final(state_id) {
			let patterns = acdfa.final_to_patterns(state_id);
			println!("State Index: {}, Freq: {}, Patterns ({}):", 
					 state_id, freq, patterns.len());
			for (i, pat) in patterns.iter().enumerate() {
				println!("  [{}] {}", i + 1, pat);
			}
		} else {
			 println!("State Index: {} (Non-final), Freq: {}", state_id, freq);
		}
	}
	println!(" ----------------------------------------------------------- \n");
}

impl <F: PrimeField + ColEle> FsmAdvAdvice<F>{
	/// Given nibbles and ACDFA, produce the (state,loc) sequence, sorted
	/// by loc.
	/// Input: (input_state, inp_location) 
	/// 
	/// might throw CapErr("fsm_adv::subsigs", "basis_pats_in_trace",
	/// "basis_unique_states", "avg_pats_per_subsig")
	pub fn new(
		b_igc: bool,
		offset_wea: usize,
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's already adjusted (starting from 1)
		inp_loc: F, //it's starting from 1 (for first component). 
		inp_subsigs: &Vec<F>,
		capacity: &FsmAdvCapacity, 
		fsm_id: u32,
		store_subsig_pat: &SubsigPatternStore
	) ->Result<Self, Error>{
		let b_debug = false;
		let res = if B_FSM_ADV_NEW{
			Self::new_v2(b_igc, offset_wea, nibbles, acdfa, inp_state,
				inp_loc, inp_subsigs, capacity, fsm_id, store_subsig_pat)
		}else{
			Self::new_v1(b_igc, offset_wea, nibbles, acdfa, inp_state,
				inp_loc, inp_subsigs, capacity, fsm_id, store_subsig_pat)
		};
		if b_debug{
			res.as_ref().unwrap().dump_pat_loc();
		}

		res
	}

	/// used for debugging purpose.
	/// dump the pat loc table generated
	pub fn dump_pat_loc(&self){
		let packed_combo = self.stmt_container.lock().unwrap().
			get_container("packed_trace").unwrap();
		let pat_loc_tbl = packed_combo.lock().unwrap().get_container("pat_loc")
			.unwrap();
		let pats = pat_loc_tbl.lock().unwrap().
			search_container("pat_loc sorted_tbl sorted_key").
			unwrap().lock().unwrap().to_vec();
		let locs= pat_loc_tbl.lock().unwrap().
			search_container("pat_loc sorted_tbl sorted_val").
			unwrap().lock().unwrap().to_vec();
		assert!(pats.len()==locs.len());
		println!("--- pat-loc table, len: {}---", pats.len());
		for i in 0..pats.len(){
			println!("pat: {}, loc: {}", pats[i], locs[i]);
		}
		println!("---------------------");
	}

	/// the idea is to skip proj_store and directly pull out
	/// the information of pat-state (and skip subsig-states because
	/// one subsig can correspond to too many states)
	#[allow(dead_code)]
	pub fn new_v2(
		b_igc: bool,
		offset_wea: usize,
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's already adjusted (starting from 1)
		inp_loc: F, //it's starting from 1 (for first component). 
		_inp_subsigs: &Vec<F>,
		capacity: &FsmAdvCapacity, 
		fsm_id: u32,
		_store_subsig_pat: &SubsigPatternStore
	) ->Result<Self, Error>{
		let sname = if b_igc {"fsm_adv_stmt_igc"} else {"fsm_adv_stmt_cs"};
		let stmt_container = Container::<F>::new(sname);
		if _inp_subsigs.len()>capacity.subsigs{
			return Err(Error::CapErr(vec![(format!("fsm_adv::subsigs b_igc: {}", b_igc), _inp_subsigs.len())]));
		}
		assert!(_inp_subsigs.len()<=capacity.subsigs);

		//1. construct the fsm_acc combo which has the transition
		// info and results in (state, loc) columns
		let fsm_acc = Self::gen_fsm_acc_combo(
			b_igc,
			offset_wea as isize, 
			nibbles, acdfa, 
			inp_state, inp_loc, capacity, fsm_id)?;
		let fsm_acc2 = fsm_acc.clone(); //low cost, need to add
		//fsm_acc to fix location first before we build exteranl cols from it.
		stmt_container.lock().unwrap().add_container(fsm_acc);

		//2. generate the packed trace_combo
		//which eventually returns (pat-loc) table 
		let packed_trace_combo = Self::gen_packed_trace_combo_v2(b_igc,
			&fsm_acc2, capacity, acdfa, fsm_id)?;
		stmt_container.lock().unwrap().add_container(packed_trace_combo);

		Ok(Self{capacity: Clone::clone(capacity), fsm_id,
			stmt_container, offset_wea})
	}

	/// OLD deprecated version
	#[allow(dead_code)]
	pub fn new_v1(
		b_igc: bool,
		offset_wea: usize,
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's already adjusted (starting from 1)
		inp_loc: F, //it's starting from 1 (for first component). 
		inp_subsigs: &Vec<F>,
		capacity: &FsmAdvCapacity, 
		fsm_id: u32,
		store_subsig_pat: &SubsigPatternStore
	) ->Result<Self, Error>{
		let b_analyze = false; //set to false by default
		let b_return_dummy_advice = false; //set to false by default
		if b_analyze{
			Self::analyze_data(b_igc, nibbles, acdfa, inp_state, inp_loc,
				inp_subsigs, capacity, fsm_id, store_subsig_pat);

			//build a fake adivce to return to save cost.
			if b_return_dummy_advice{
				let sname = if b_igc {"fsm_adv_stmt_igc"} 
					else {"fsm_adv_stmt_cs"};
				let stmt_container = Container::<F>::new(sname);
				let packed_trace = Container::<F>::new("packed_trace");
				let packed_trace_size = capacity.basis_pats_in_trace * 
					capacity.max_nibble_len / 10000;
				let zcol = vec![F::zero(); packed_trace_size];
				let scol = vec![F::from(RANGE2); packed_trace_size];
				let pat_loc_tbl = Container::<F>::new("pat_loc");
				let sorted_tbl = Container::<F>::new("sorted_tbl");
				sorted_tbl.lock().unwrap().add_col(Col::<F>::new(zcol.clone(), 
					"sorted_key", IDX_DATA));
				sorted_tbl.lock().unwrap().add_col(Col::<F>::new(zcol.clone(), 
					"sorted_id", IDX_DATA));
				sorted_tbl.lock().unwrap().add_col(Col::<F>::new(zcol.clone(), 
					"sorted_val", IDX_DATA));
				sorted_tbl.lock().unwrap()
					.add_col(Col::<F>::new(scol.clone(), 
						"sid_sorted_key", IDX_SI_DATA));
				sorted_tbl.lock().unwrap()
					.add_col(Col::<F>::new(scol.clone(), 
						"sid_sorted_id", IDX_SI_DATA));
				sorted_tbl.lock().unwrap()
					.add_col(Col::<F>::new(scol, "sid_sorted_val", IDX_SI_DATA));
				pat_loc_tbl.lock().unwrap().add_container(sorted_tbl);
				packed_trace.lock().unwrap().add_container(pat_loc_tbl);
				stmt_container.lock().unwrap().add_container(packed_trace);

				//just fake 1 inp state 1 oupstate
				//needed by discharge_test to build inp/oup state
				let nlen = capacity.max_nibble_len;
				let f_rg2 = F::from(RANGE2);
				let col_states = Col::<F>::new(vec![inp_state],
					"states",IDX_DATA);
				let col_locs = Col::<F>::new(vec![inp_loc + F::from(nlen as u64)],
					"locs",IDX_DATA);
				let sid_states = Col::<F>::new(vec![f_rg2], 
					"si_sttes",IDX_SI_DATA);
				let sid_cols = Col::<F>::new(vec![f_rg2], 
					"oup_state",IDX_SI_DATA);
				let fsm_acc = Container::new("fsm_acc");
				fsm_acc.lock().unwrap().add_col(col_states);
				fsm_acc.lock().unwrap().add_col(col_locs);
				fsm_acc.lock().unwrap().add_col(sid_states);
				fsm_acc.lock().unwrap().add_col(sid_cols);
				stmt_container.lock().unwrap().add_container(fsm_acc);

				return Ok(Self{ 
					offset_wea, fsm_id, stmt_container, 
					capacity: Clone::clone(capacity),
				});
			}
		}
		
		let sname = if b_igc {"fsm_adv_stmt_igc"} else {"fsm_adv_stmt_cs"};
		let stmt_container = Container::<F>::new(sname);

		//1. construct the fsm_acc combo which has the transition
		// info and results in (state, loc) columns
		let fsm_acc = Self::gen_fsm_acc_combo(
			b_igc,
			offset_wea as isize, 
			nibbles, acdfa, 
			inp_state, inp_loc, capacity, fsm_id)?;
		let fsm_acc2 = fsm_acc.clone(); //low cost, need to add
		//fsm_acc to fix location first before we build exteranl cols from it.
		stmt_container.lock().unwrap().add_container(fsm_acc);

		//2. construct the projected subsig-state-pattern store and the proof
		//for it
		if inp_subsigs.len()>capacity.subsigs{
			return Err(Error::CapErr(vec![(format!("fsm_adv::subsigs b_igc: {}", b_igc), inp_subsigs.len())]));
		}
		//assert!(inp_subsigs.len()<=capacity.subsigs, "inp_subsigs.len: {}, capacity.subsigs: {}", inp_subsigs.len(), capacity.subsigs);
		let inp_subsigs = vec![inp_subsigs.clone(), vec![F::zero(); 
			capacity.subsigs-inp_subsigs.len()]].concat();
		let proj_store_combo = Self::gen_proj_store_combo(&inp_subsigs, 
			store_subsig_pat,fsm_id, capacity)?;
		let proj_store_combo2 = proj_store_combo.clone(); //rc clone low cost
		stmt_container.lock().unwrap().add_container(proj_store_combo);

		//3. construct the packed tracie
		let packed_trace_combo = Self::gen_packed_trace_combo(b_igc, &fsm_acc2,
			&proj_store_combo2, capacity, acdfa)?;
		stmt_container.lock().unwrap().add_container(packed_trace_combo);


		Ok(Self{capacity: Clone::clone(capacity), fsm_id,
			stmt_container, offset_wea})
	}

	/// this function is used to analyze the input data
	/// and decide appropriate algorithm to use
	pub fn analyze_data(
		b_igc: bool,
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's already adjusted (starting from 1)
		inp_loc: F, //it's starting from 1 (for first component). 
		inp_subsigs: &Vec<F>,
		capacity: &FsmAdvCapacity, 
		fsm_id: u32,
		store_subsig_pat: &SubsigPatternStore
	){
		let b_expensive = false; //set to false by default
		println!(" === ANALYSIS OF fsm_adv DATA ===\nb_igc: {}, nibbles_len: {}, inp_state: {}, inp_loc: {}", b_igc, nibbles.len(), inp_state, inp_loc);
		//0. analyze acdfa stats
		if b_expensive{
			let mut num2 = 0; //num of states that have >= 5 pats
			let mut num5 = 0; //num of states that have >= 5 pats
			let mut num10 = 0; //num of states that have >=10 pats
			let mut max_pats = 0; //max num of patterns for one state
			let mut max_id = 0; //who has the max_pats
			let mut total_pats = 0; //total count of pats across all states
			let mut acc_states = 0;
			for state in 0..acdfa.num_states{
				let count = if acdfa.outputs.contains_key(&state){
					acc_states += 1;
					acdfa.outputs.get(&state).unwrap().len()
				}else{
					0
				};
				total_pats += count;
				if count>=2 {num2+=1;}
				if count>=5 {num5+=1;}
				if count>=10 {num10+=1;}
				if count>max_pats{
					max_pats = count;
					max_id = state;
				}
			}
			println!("acdfa states: {}, acc_states: {}, num of states with >=2 patterns: {}, num5 :{}, num10: {}, max patterns: {}, avg: {}",
				acdfa.num_states,
				acc_states,
				num2, num5, num10,
				max_pats, (total_pats as f64)/(acc_states as f64)
			);
			println!("--- max pattersn at state: {}, num_patterns: {}", 
				max_id, max_pats);
			let pats = acdfa.outputs.get(&max_id).unwrap();
			for pat_id in pats{
				println!(" -- pat: {}", acdfa.patterns[*pat_id]); 
			}
			if 1>0 {panic!("ONCE collecting expensive data. disable it.");}
		}
		//1. build the states
		let state_part_bits = capacity.acdfa_state_part_bits;
		let nlen = capacity.max_nibble_len;
		let mut raw_states = vec![];
		let mut raw_locs = vec![];
		let mut cur_state = field_to_usize(&inp_state) - 1;
		// NOTE: state needs to be added 1 to be pushed
		// 0 is considered padding value. Similarly loc starts from 1
		raw_states.push(F::from( (cur_state+1) as u32));
		raw_locs.push(inp_loc);
		let _unit = F::from((1<<(state_part_bits+4)) as u32);
		let _hex = F::from(16 as u32);
		let _one = F::one();
		for i in 0..nibbles.len(){
			let ch: u8 = field_to_usize(&nibbles[i]).try_into().unwrap();
			let nxt_state = acdfa.trans.get(&cur_state).unwrap()[ch as usize];
			raw_states.push(F::from( (nxt_state+1) as u32)); 
			cur_state = nxt_state;
		}
		assert!(raw_states.len()==nlen+1 && raw_locs.len()==1);

		let f_id_non_final = F::from(fsm_id+1);
		let f_id_final = F::from(fsm_id+2);
		let vec_si_states = raw_states.par_iter().map(|s|{
			let f_s = field_to_usize(s) - 1;
			if acdfa.is_final(f_s) {f_id_final} else {f_id_non_final}
		}).collect::<Vec<F>>();

		//2. build the states_final and locs_final
		// NOTE: we do not include element 0 coz it's already
		// handled in the previous seg.
		let states_final = (1..vec_si_states.len()).into_par_iter().filter(|i|{
				vec_si_states[*i]==f_id_final
			}).map(|i| raw_states[i]).collect::<Vec<F>>();
		let locs_final = (1..vec_si_states.len()).into_par_iter().filter(|i|{
				vec_si_states[*i]==f_id_final
			}).map(|i| raw_locs[0] + F::from(i as u32)).collect::<Vec<F>>();
		assert!(states_final.len()==locs_final.len());
		println!("acc_states ratio: {}, state_final.len: {}", 
			(states_final.len() as f64)/(nlen as f64), states_final.len());

		//3. construct the projected subsig store and print out
		// the data
		let subsig_ids = inp_subsigs.iter().map(|f| field_to_usize(f))
			.collect::<Vec<usize>>();
		let proj_store = store_subsig_pat.project_by(&subsig_ids);
		let mut set_store_states = HashSet::new();
		let mut set_store_pats = HashSet::new();
		let mut vec_store_states = vec![];
		let mut vec_store_pats = vec![];
		let mut total_proj_pats = 0;
		for (_subsig, store_item) in proj_store.subsig_to_rec{
			let mut set_pats = HashSet::new();
			for id in store_item.state_ids{
				set_store_states.insert(id);
				vec_store_states.push(id);
			}
			for (_id, vec_pat) in store_item.state_to_pattern_ids{
				for pat in vec_pat{
					set_store_pats.insert(pat);
					vec_store_pats.push(pat);
					set_pats.insert(pat);
				}
			}
			total_proj_pats += set_pats.len();
		}
		println!("Projected Store Data: subsigs: {}, allowed states: {}, allowed patterns: {}", subsig_ids.len(), set_store_states.len(), set_store_pats.len());
		println!("  vec_allowed_states: {}, vec_allowed_pats: {} -- real projection cost (original design)", vec_store_states.len(), vec_store_pats.len());

		//4. from states_final and acdfa find all patterns
		let mut acc_state_to_pat_id = HashMap::<usize, Vec<usize>>::new();
		let mut alt1_len = 0;
		for acc_state in states_final{
			let real_state_id = field_to_usize(&acc_state) - 1;
			let real_pat_ids = acdfa.outputs.get(&real_state_id).unwrap();
			alt1_len += real_pat_ids.len();
			let pat_ids = real_pat_ids.iter().map(|x| x+1)
				.collect::<Vec<usize>>();
			acc_state_to_pat_id.insert(real_state_id+1, pat_ids.to_vec());
		}
		println!("Estimate of alg design 1 (no filter): output len: {}, projected_pats (sum of set of pats per subsig): {}", alt1_len, total_proj_pats);
			

		println!(" ========== END OF ANALYSIS ===========");
	}

	/// Given the input generates the container of the following
	/// structure: root level name: fsm_acc
	/// nibbles
	/// states: (inp, mid, oup): modeled as a container of 3 columns
	/// locs: (inp, mid, oup) -> REMOVE the mid part.
	/// trans
	/// states_final (this means ALL final states, not projected using 
	///    proj_store of the subsigs yet)
	/// locs_final
	///
	/// si_nibbles
	/// si_states (inp, mid, oup)
	/// si_locs (inp, mid, oup) -> REMOVE THE mid part
	/// si_trans
	/// si_states_final
	/// si_locs_final
	///
	/// might throw CapErr("fsm_adv::basis_acc_states")
	fn gen_fsm_acc_combo(
		b_igc: bool,
		wea_offset: isize,
		nibbles: &Vec<F>, 
		acdfa: &HexACDFA, 
		inp_state: F,  //it's the adjusted state (starting rom 1)
		inp_loc: F, //starting from 1. 
		capacity: &FsmAdvCapacity, 
		fsm_id: u32) 
	-> Result<std::sync::Arc<std::sync::Mutex<Container<F>>>, Error>{
		let b_debug = false;
		let b_perf = true;
		let mut gt = GTimer::new();
		let res = Container::<F>::new("fsm_acc");
		let nlen = capacity.max_nibble_len;
		assert!(nlen==nibbles.len(), "nlen: {}, nibbles.len: {}", nlen, nibbles.len());
		let acdfa_state_part_bits = acdfa.state_part_bits;

		//1. build the raw transition table
		let mut raw_states = vec![];
		let mut raw_locs = vec![];
		let mut trans = vec![];
		let mut cur_state = field_to_usize(&inp_state) - 1;
		// NOTE: state needs to be added 1 to be pushed
		// 0 is considered padding value. Similarly loc starts from 1
		raw_states.push(F::from( (cur_state+1) as u32));
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
			//cur_loc = cur_loc + one;
			if b_debug{
				println!("DEBUG USE 201: i: {}, src_adj: {}, ch {} => {}, igc: {}", i, f_src+one, f_ch, f_dst+one, b_igc);
			}
			//raw_locs.push(cur_loc); REMOVE THE MID PART
			//can be calculated directly in the last
		}
		assert!(raw_states.len()==nlen+1 && raw_locs.len()==1);

		let _f_id_state = F::from(fsm_id+6);
		let f_id_trans= F::from(fsm_id+3);
		let f_id_loc= F::from(RANGE2);
		let f_char= F::from(CHAR);
		let f_id_non_final = F::from(fsm_id+1);
		let f_id_final = F::from(fsm_id+2);
		let vec_si_states = raw_states.par_iter().map(|s|{
			let f_s = field_to_usize(s) - 1;
			if acdfa.is_final(f_s) {f_id_final} else {f_id_non_final}
		}).collect::<Vec<F>>();

		//2. build the states_final and locs_final
		// NOTE: we do not include element 0 coz it's already
		// handled in the previous seg.
		let states_final = (1..vec_si_states.len()).into_par_iter().filter(|i|{
				vec_si_states[*i]==f_id_final
			}).map(|i| raw_states[i]).collect::<Vec<F>>();
		let locs_final = (1..vec_si_states.len()).into_par_iter().filter(|i|{
				vec_si_states[*i]==f_id_final
			}).map(|i| raw_locs[0] + F::from(i as u32)).collect::<Vec<F>>();
		assert!(states_final.len()==locs_final.len());


		let target_size = nlen*capacity.basis_acc_states/10000;
		let target_size = if target_size < 2 {2} else {target_size};
		if states_final.len() + 1>target_size{
			report_top_states(&states_final, acdfa, 10, "basis_acc_states overflow");
			//needs at least one padding entry
			let target_basis_acc_states = (states_final.len()+1) * 10000/nlen 
				+ 1;
			return Err(Error::CapErr(vec![(format!("fsm_adv::basis_acc_states, b_igc: {}", b_igc), target_basis_acc_states)]));
		}
		assert!(states_final.len()<=target_size-1, "basis_acc_states too small: target_size: {} < states_final.len {}", target_size, states_final.len());
		let (oflen,to_pad) = (states_final.len(), 
			target_size - states_final.len());
		assert!(to_pad>0, "to_add needs >0 to leave one dummy entry");
		let zero = F::zero();
		let f_range2 = F::from(RANGE2 as u32);
		let states_final = vec![ vec![zero; to_pad], states_final].concat();
		let locs_final = vec![ vec![zero; to_pad], locs_final].concat();
		if b_debug{
			let max_loc = F::from( (1u64<<RANGE2_BIT) - 1);
			locs_final.par_iter().for_each(|x| {
				assert!(*x<max_loc); 
			});
		}
		let si_states_final = vec![
			vec![f_range2; to_pad],vec![f_id_final; oflen]
		].concat();
		let si_locs_final = vec![
			vec![f_range2; to_pad], vec![f_range2; oflen]
		].concat();

		//3. build the containers
		//3.1 the inp/mid/oup states
		let col_inp_state = Col::<F>::new(vec![raw_states[0]],
			"inp_state",IDX_INP);
		let col_si_inp_state = Col::<F>::new(vec![vec_si_states[0]],
			"si_inp_state",IDX_SI_INP);

		let col_mid_states = Col::<F>::new(raw_states[1..nlen].to_vec(),
			"mid_states", IDX_DATA);
		let col_si_mid_states = Col::<F>::new(vec_si_states[1..nlen].to_vec(),
			"si_mid_states", IDX_SI_DATA);

		let col_oup_state = Col::<F>::new(vec![raw_states[nlen]],
			"oup_state",IDX_OUP);
		let col_si_oup_state = Col::<F>::new(vec![vec_si_states[nlen]],
			"si_oup_state",IDX_SI_OUP);

		let states = Container::concat_cols(
			vec![col_inp_state, col_mid_states, col_oup_state], "states");
		let si_states = Container::concat_cols(vec![col_si_inp_state, 
			col_si_mid_states, col_si_oup_state], "si_states");
		#[cfg(test)]{assert!(states.lock().unwrap().to_vec().len()==nlen+1);}
		#[cfg(test)]{assert!(si_states.lock().unwrap().to_vec().len()==nlen+1);}
		res.lock().unwrap().add_container(states.clone()); //remove clone later
		res.lock().unwrap().add_container(si_states);

		//3.2 the inp/mid/oup locations
		let col_inp_loc = Col::<F>::new(vec![raw_locs[0]],
			"inp_loc",IDX_INP);
		let col_si_inp_loc = Col::<F>::new_const(vec![f_id_loc],
			"si_inp_loc",IDX_SI_INP);

		//let col_mid_locs = Col::<F>::new(raw_locs[1..nlen].to_vec(),
		//	"mid_locs", IDX_DATA);
		//let col_si_mid_locs = Col::<F>::new_const(vec![f_id_loc; nlen-1], 
		//	"si_mid_locs", IDX_SI_DATA);

		let col_oup_loc = Col::<F>::new(vec![raw_locs[0] 
			+ F::from(nlen as u32)],
			"oup_loc",IDX_OUP);
		let col_si_oup_loc = Col::<F>::new_const(vec![f_id_loc],
			"si_oup_loc",IDX_SI_OUP);

		let locs = Container::concat_cols(
			vec![col_inp_loc, col_oup_loc], "locs");
		let si_locs = Container::concat_cols(vec![col_si_inp_loc, 
			 col_si_oup_loc], "si_locs");
		#[cfg(test)]{assert!(locs.lock().unwrap().to_vec().len()==2);}
		#[cfg(test)]{assert!(si_locs.lock().unwrap().to_vec().len()==2);}
		res.lock().unwrap().add_container(locs);
		res.lock().unwrap().add_container(si_locs);

		//3.3. the transitions
		let col_trans = Col::<F>::new(trans, 
			"trans", IDX_DATA);
		let col_si_trans = Col::<F>::new_const(vec![f_id_trans; nlen],
			"si_trans", IDX_SI_DATA);
		#[cfg(test)]{assert!(col_trans.lock().unwrap().data.len()==nlen);}
		#[cfg(test)]{assert!(col_si_trans.lock().unwrap().data.len()==nlen);}
		res.lock().unwrap().add_col(col_trans);
		res.lock().unwrap().add_col(col_si_trans);

		//3.4 the nibbles (LATER when reconstructed, it is 
		// retrieved from previous word_extract_adv gadget
		let shift = 0 - (wea_offset as i32);
		let col_nibbles = Col::<F>::new_external(nibbles.to_vec(), 
			"nibbles", IDX_DATA, shift, "word_extract_stmt nibbles");
		let col_si_nibbles = Col::<F>::new_external(vec![f_char; nlen], 
			"si_nibbles", IDX_SI_DATA, shift, 
			"word_extract_stmt si_nibbles");
		#[cfg(test)]{assert!(col_nibbles.lock().unwrap().data.len()==nlen);}
		#[cfg(test)]{assert!(col_si_nibbles.lock().unwrap().data.len()==nlen);}

		res.lock().unwrap().add_col(col_nibbles);
		res.lock().unwrap().add_col(col_si_nibbles);

		//3.5 the state columns
		let col_states_final = Col::<F>::new(states_final,
			"states_final", IDX_DATA);
		let col_si_states_final = Col::<F>::new(si_states_final,
			"si_states_final", IDX_SI_DATA);
		let col_locs_final = Col::<F>::new(locs_final,
			"locs_final", IDX_DATA);
		let col_si_locs_final = Col::<F>::new(si_locs_final,
			"si_locs_final", IDX_SI_DATA);
		res.lock().unwrap().add_col(col_states_final);
		res.lock().unwrap().add_col(col_si_states_final);
		res.lock().unwrap().add_col(col_locs_final);
		res.lock().unwrap().add_col(col_si_locs_final);

		if b_perf{log_perf(LOG1, "-- -- fsm_gen_fsm_combo", &mut gt);}

		Ok(res)
	}

	/// Generate the projected SubsigPatternStore and its PROOF as a combo.
	/// It consists of
	/// Columns of the SubsigPatternStore (5 cols)
	/// Col: Encoded subsigpattern store
	/// Its corresponding subtbl_id 
	///
	/// Note: call assert_proj_store_combi() in assert_msg3.
	/// might throw CapErr:avg_pats_per_subsig
	fn gen_proj_store_combo(
		inp_subsigs: &Vec<F>, 
		store_subsig_pat: &SubsigPatternStore,
		fsm_id: u32,
		capacity: &FsmAdvCapacity,
	)->Result<std::sync::Arc<std::sync::Mutex<Container<F>>>, Error>{
		//1. generate the projected store
		let state_part_bits = capacity.acdfa_state_part_bits;
		assert!(state_part_bits == RANGE2_BIT);
		let subsig_ids = inp_subsigs.iter().map(|f| field_to_usize(f))
			.collect::<Vec<usize>>();
		assert!(subsig_ids.len()==capacity.subsigs);
		let n = capacity.subsigs * capacity.avg_pats_per_subsig;
		let proj_store = store_subsig_pat.project_by(&subsig_ids);
		let cols = proj_store.gen_cols::<F>(state_part_bits, Some(n));
		let mut cols = match cols{
			Ok(v_cols) => Ok(v_cols),
			Err(Error::CapErr(vec)) => {
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="proj_store::n"{
						let new_n = val / capacity.subsigs + 1;
						(format!("fsm_adv::avg_pats_per_subsig from proj_store, fsm_id: 0x{:x}", fsm_id),new_n)
					}else{
						(format!("fsm_adv::unknown capacity err: {}, fsm_id: 0x{:x}", s, fsm_id), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ =>cols 
		}?;
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
			Col::<F>::new_const(d.to_vec(),&format!("sid_{}", n),IDX_SI_DATA))
			.collect();

		//note not much cost as it's rc
		for i in 0..cols.len(){ res.lock().unwrap().add_col(cols[i].clone()); }
		for i in 0..sid_cols.len(){res.lock().unwrap().add_col(sid_cols[i].clone());}

		Ok(res)
	}

	/// Generate packed_trace in the following form:
	/// (subsig, state, pat, loc) where loc is sorted for key:(subsig,state,pat)
	/// It includes all the corresponding proofs for the claim.
	/// 
	/// Workflow: 
	/// (1) projected_subsig_store -> sorted set of states 
	/// (2) (state_final,loc_final) -- filter by sorted set of states --
	///    ---> well formed table (state, id, loc)
	/// (3) do table join (sugsit, pat, state) join with (state, id, loc)
	///    over key state. Basically, expand each (subsig, pat, state)
	///    with multiple entries of loc.
	///
	/// NOTE that since the ratio of final states in (state,loc) trace.
	/// Even the concrete table join cost is high, but since table size
	/// is small, it's going to be much smaller than the trace size.
	///
	/// might throw CapErr on "fsm_adv::basis_pats_in_trace",
	/// "fsm_adv::basis_unique_states", "fsm_adv::avg_pats_per_subsig",
	#[allow(dead_code)]
	fn gen_packed_trace_combo(
		b_igc: bool,
		fs_acc_combo: &std::sync::Arc<std::sync::Mutex<Container<F>>>,
		proj_store_combo: &std::sync::Arc<std::sync::Mutex<Container<F>>>,
		capacity: &FsmAdvCapacity,
		acdfa: &HexACDFA,
	)->Result<std::sync::Arc<std::sync::Mutex<Container<F>>>, Error>{
		let res = Container::<F>::new("packed_trace");
		//1. extract proj_store_combo column "states" to a sorted set
		let ext_state= proj_store_combo.lock().unwrap()
			.get_container("state").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);
		let ext_state = Arc::new(Mutex::new(ext_state));
		let sorted_set_size = capacity.avg_pats_per_subsig 
			* capacity.subsigs;
		let _final_states_len= capacity.basis_acc_states *
			capacity.max_nibble_len /10000; //final states for ALL sigs
		let _final_states_len = if _final_states_len<2 {2} else {_final_states_len};
		let sorted_states = col_to_sorted_set(&ext_state, sorted_set_size, 
			"sorted_states");
		let sorted_states2 = sorted_states.clone(); //low cost rc clone
		res.lock().unwrap().add_container(sorted_states); //once created, add it.

		//2. (state,loc) filtered by sorted_states 
		// --> sorted_and well formed table (state, id, loc)
		let state_col = Arc::new(Mutex::new(
			fs_acc_combo.lock().unwrap().get_container("states_final")
			.unwrap().lock().unwrap()
			.duplicate_as_external(0, None)));
		let loc_col = Arc::new(Mutex::new(
			fs_acc_combo.lock().unwrap().get_container("locs_final").unwrap().lock().unwrap()
			.duplicate_as_external(0, None)));
		#[cfg(test)]{
			assert!(state_col.lock().unwrap().to_vec().len()==_final_states_len);
		}

		let packed_trace_size = capacity.basis_pats_in_trace * 
			capacity.max_nibble_len/10000;
		let unique_key_size = capacity.basis_unique_states *
			capacity.max_nibble_len/10000;

		let state_loc_tbl = tbl_filtered_to_sorted_tbl(
			&state_col, 
			&loc_col, 
			&sorted_states2, 
			packed_trace_size,
			"state_loc_tbl",
			unique_key_size,
		);
		let state_loc_tbl = match state_loc_tbl{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let states_final = fs_acc_combo.lock().unwrap().get_container("states_final").unwrap().lock().unwrap().to_vec();
				report_top_states(&states_final, acdfa, 10, "basis_pats_in_trace (state_loc_tbl)");
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="target_size"{
						let t_val= val * 10000/capacity.max_nibble_len + 1;
						(format!("fsm_adv::basis_pats_in_trace from tbl_filtered_to_sorted_tbl, b_igc: {}", b_igc),t_val)
					}else if s=="unique_key_size"{
						let t_val= val * 10000/capacity.max_nibble_len + 1;
						(format!("fsm_adv::basis_unique_states from tbl_filtered_to_sorted_tbl, b_igc: {}", b_igc),t_val)
					}else if s=="target_size::hashmap_2col"{
						let t_val= val * 10000/capacity.max_nibble_len + 1;
						(format!("fsm_adv::basis_pats_in_trace from tbl_filtered_to_sorted_tbl, b_igc: {}", b_igc),t_val)
					}else{
						(format!("fsm_adv::unknown capacity err at step 2: b_igc: {},  {}", b_igc, s), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => state_loc_tbl 
		}?;
		let state_loc_tbl2 = state_loc_tbl.clone(); //low cost clone rc
		res.lock().unwrap().add_container(state_loc_tbl);

		//3. projecting the (subsig-state-pat) sorted set further
		// to (pat-state) sorted table for further tbl join.
		// Adjust avg_pats_per_subsig if too small.
		let pat_state_set_size = capacity.avg_pats_per_subsig 
			* capacity.subsigs;
		let ext_pat= proj_store_combo.lock().unwrap()
			.get_container("pat").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);
		let ext_pat= Arc::new(Mutex::new(ext_pat));
		let pat_state_tbl = tbl_to_sorted_tbl( 
			&ext_pat, &ext_state, pat_state_set_size, "pat_state_tbl");
		let pat_state_tbl = match pat_state_tbl{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="target_size"{
						let t_val= val /capacity.subsigs + 1;
						(format!("fsm_adv::avg_pats_per_subsig from pat_state, b_igc: {}", b_igc),t_val)
					}else{
						(format!("unknown capacity err at step 3: {}, b_igc: {}", s, b_igc), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => pat_state_tbl 
		}?;

		let pat_state_tbl2 = pat_state_tbl.clone(); //clone rc low cost
		res.lock().unwrap().add_container(pat_state_tbl);

		//4. left join (pat-state) and (state-loc) both are sorted table.
		let packed_trace_size = capacity.basis_pats_in_trace * 
			capacity.max_nibble_len / 10000;
		let pat_state_loc_tbl = tbl_left_join(
			&pat_state_tbl2, &state_loc_tbl2, 
			&sorted_states2, packed_trace_size, "pat_state_loc_tbl");
		let pat_state_loc_tbl = match pat_state_loc_tbl{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let states_final = fs_acc_combo.lock().unwrap().get_container("states_final").unwrap().lock().unwrap().to_vec();
				report_top_states(&states_final, acdfa, 10, "basis_pats_in_trace (pat_state_loc_tbl)");
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="target_size::2col_left_join"{
						let t_val= val*10000 /capacity.max_nibble_len+ 1;
						( format!(
						   "fsm_adv::basis_pats_in_trace from tbl_left_join for 2col_left_join, b_igc: {}", b_igc), t_val
						  )
					}else if s=="target_size::hashmap_2col"{
						let t_val= val*10000 /capacity.max_nibble_len+ 1;
						( format!(
						   "fsm_adv::basis_pats_in_trace from tbl_left_join for hashmap_2col, b_igc: {}", b_igc),t_val
						  )
					} else{
						(format!("unknown capacity err at step4: {}, b_igc: {}", s, b_igc), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => pat_state_loc_tbl 
		}?;

		let pat_col = pat_state_loc_tbl.lock().unwrap()
			.get_container("join_tbl").expect("err get join_tbl").lock().unwrap()
			.get_container_by_idx(0).lock().unwrap().duplicate_as_external(0,None);
		let loc_col = pat_state_loc_tbl.lock().unwrap()
			.get_container("join_tbl").expect("err get join_tbl").lock().unwrap()
			.get_container_by_idx(4).lock().unwrap().duplicate_as_external(0,None);

		res.lock().unwrap().add_container(pat_state_loc_tbl);

		//5. compress pat_state_loc_tbl to pat_loc_tbl
		let pat_loc_tbl = tbl_to_sorted_tbl(
			&Arc::new(Mutex::new(pat_col)), 
			&Arc::new(Mutex::new(loc_col)), 
			packed_trace_size, "pat_loc").expect("err pat_loc"); 
		res.lock().unwrap().add_container(pat_loc_tbl);

		//6. return
		Ok( res )
	}

	/// better version of gen_packed_trace_combo. We avoided
	/// the huge number of states associated with a subsig.
	/// Here the improvement is made over the following observations:
	/// (1) typically the ratio of accepted states in trace is
	///  less than 3%, or max 5% for the linux data set
	/// (2) the expansion rate from final states -> related patterns
	/// is only 1.1
	/// Then, we can just generate a slightly larger (pat-loc) sequence
	/// where a tiny portins of pats are actually not related to
	/// the input subsig list. This over approximation is conservative
	/// when we later reason about the step/backward queue and subsig
	/// eval result in discharge_sig.rs and compute_sig.rs
	///
	/// basic idea: 
	/// (1) retrieve (final_states, final_locs) from fsm_combo 
	/// (2) non-deterministically build the projection from
	///      lookup - (states - mul-pats) where states is a superset
	///      of the final states in the trace.
	/// (3) left join the (final_locs, final_states) with (states - multi-pats)
	///     --> (final_locs - final_states -> multi pats)
	/// (4) from the above table pack it as (pats -> multi-locs)
	#[allow(dead_code)]
	fn gen_packed_trace_combo_v2(
		b_igc: bool,
		fsm_acc_combo: &std::sync::Arc<std::sync::Mutex<Container<F>>>,
		capacity: &FsmAdvCapacity,
		acdfa: &HexACDFA,
		fsm_id: u32,
	)->Result<std::sync::Arc<std::sync::Mutex<Container<F>>>, Error>{
		let res = Container::<F>::new("packed_trace");
		let b_perf = true;
		let mut gt = GTimer::new();

		//1. retrive (final_states, loc) from fsm_combo
		let states_final = fsm_acc_combo.lock().unwrap()
			.get_container("states_final").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);
		let locs_final = fsm_acc_combo.lock().unwrap()
			.get_container("locs_final").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);

		//2. non-deterministically build the projection from
		//acdfa -> (states -> multi-pats) which is a well-formed
		//table.
		//2.1 extract set of states
		let set_states = states_final.to_vec()
			.par_iter().filter(|x|
			!x.is_zero()).map(|x| *x).collect::<HashSet<F>>().iter()
			.map(|x| *x).collect::<Vec<F>>();
	
		//2.2 build the table like clam_db.rs::add_acdfa_to_lkup 
		// extract the states - pats columns
		let tuples = set_states.par_iter().map(|state|{
			let raw_state = field_to_usize(state) - 1;
			let mut pats = acdfa.outputs.get(&raw_state).unwrap().clone();
			pats.sort();
			assert!(pats.len()>0);
			pats.iter().map(|id| {
				let pat_id = F::from( (id+1) as u32 );
				(*state, pat_id)
			}).collect::<Vec<(F,F)>>()
		}).flatten().collect::<Vec<(F,F)>>();
		let proj_states = tuples.par_iter().map(|t| t.0).collect::<Vec<F>>();
		let proj_pats= tuples.par_iter().map(|t| t.1).collect::<Vec<F>>();

		//2.2 build the wide-wellformed table
		//a wide-wellformed table is one which has
		//column key-val-id-count
		//where id starts from 0 and count is the real count -1
		//NOTE that it's light weighted. We do not gurantee
		//that key is sorted. The table is padded
		//by a real key-0 entries which are also well formed.
		//.e.g,
		// key - val - id - count
		// 0     1     0      2
		// 0     10    1      2   (last of padding entry)
		// 1    10     0      3
		// 1      5     1     3  (note not necessarily val is osrted
		// 1     20     2     3  (last entry) 
		// HERE the well-formed means that the id for a key starts
		// from 0 and ends at count-1. Thus it guarantees that
		// the entries projected from lookup is "COMPLETE" (having
		// all related entries copied).
		// NOTE2: here we construct the table with NO duplicate entries.
		// even if there are duplicate entries (same key-multi val)
		// appeared multiple times, it does not affect the correctness
		// of left join.
		let nlen = capacity.max_nibble_len;
		let ulen = nlen * capacity.basis_unique_states/10000;
		if ulen<proj_states.len()+1{//guaranees on dummy 0-entry for 
			//skipping conditional logup later
			let new_val = (tuples.len()+1) * 10000/nlen + 1;
			assert!(new_val * nlen /10000 >= tuples.len()+1);
			return Err(Error::CapErr(
				vec![(format!(
					"fsm_adv::basis_unique_states proj_state-pat, b_igc: {}", b_igc), new_val) ]
			));
		}
		let ct_stat_pat = two_col_to_wide_wellformed(&proj_states, &proj_pats,
			ulen, "tbl_proj_states_pats")
			.expect("We expect length err already handled above already");

		//2.3 constuct the encoded col
		let c1 = ct_stat_pat.lock().unwrap().get_container("key")?.lock().unwrap().to_vec();
		let c2 = ct_stat_pat.lock().unwrap().get_container("val")?.lock().unwrap().to_vec();
		let c3 = ct_stat_pat.lock().unwrap().get_container("id")?.lock().unwrap().to_vec();
		let c4 = ct_stat_pat.lock().unwrap().get_container("count")?.lock().unwrap().to_vec();
		if c1.len()>ulen{
			let new_val = (c1.len()+1) * 10000/nlen + 1;
			return Err(Error::CapErr(
				vec![(format!(
					"fsm_adv::basis_unique_states cs_stat_pat, b_igc: {}", b_igc), new_val) ]
			));
		}
		assert!(c1.len()<=ulen);
		let cols =  vec![&c1[..],&c2[..],&c3[..],&c4[..]];
		let encoded = encode_cols_better(cols,vec![0,1,2,3]);
		assert!(encoded.len()==ulen);
		let col_encoded= Col::new(encoded, 
			"encoded_proj_state_pat", IDX_DATA);
		let tbl_id = F::from((fsm_id + 7) as u32);
		let col_sid_encoded= Col::new_const(vec![tbl_id; ulen],
			"si_encoded_proj_stat_pat", IDX_SI_DATA);
		res.lock().unwrap().add_container(ct_stat_pat.clone()); //low cost clone
		res.lock().unwrap().add_col(col_encoded);
		res.lock().unwrap().add_col(col_sid_encoded);

		//3. left join loc-state and pat-state table
		//here only need pat-state to be wide-wellfomed
		let packed_trace_size = capacity.basis_pats_in_trace * 
			capacity.max_nibble_len / 10000;
		if capacity.basis_pats_in_trace > 2*capacity.basis_acc_states{
			println!("WARNING: basis_pats_in_trace: {} should be usually 1.1 * basis_acc_states: {}. It's too large. ", capacity.basis_pats_in_trace, capacity.basis_acc_states);
		}
		if capacity.basis_pats_in_trace > 10*capacity.basis_acc_states{
			panic!("ERROR: basis_pats_in_trace: {} is usually 1.1 * basis_acc_states: {}. It's too high. ", capacity.basis_pats_in_trace, capacity.basis_acc_states);
		}
		let loc_state_pat_tbl = tbl_left_join_wide(
			 &locs_final.to_vec(), 
			 &states_final.to_vec(), 
			 &ct_stat_pat,
			 packed_trace_size, 
			 "loc_state_pat_tbl"
		);
		let loc_state_pat_tbl = match loc_state_pat_tbl{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="tbl2"{
						let val = (ulen+1)*10000 /capacity.max_nibble_len+ 1;
						( 
						  format!("fsm_adv::basis_unique_states joinwide, b_igc: {}", b_igc), 
						  val 
						)
					}else if s=="target_size"{
						report_top_states(&states_final.to_vec(), acdfa, 10, "basis_pats_in_trace (joinwide)");
						let t_val= val*10000 /capacity.max_nibble_len+ 1;
						( format!(
						   "fsm_adv::basis_pats_in_trace from joinwide, b_igc: {}", b_igc),t_val
						  )
					} else{
						(format!("unknown capacity err at step4: {}, b_igc: {}", s, b_igc), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => loc_state_pat_tbl 
		}?;
		let loc_state_pat_tbl_len = loc_state_pat_tbl.lock().unwrap()
			.get_container("join_tbl").unwrap().lock().unwrap()
			.get_container("val").unwrap().lock().unwrap().to_vec().len();

		if loc_state_pat_tbl_len>packed_trace_size{
			let new_val = (loc_state_pat_tbl_len+1)*10000/capacity.max_nibble_len + 1;
			return Err(Error::CapErr(vec![(format!("fsm_adv::basis_pats_in_trace for loc_state_pat_tbl, b_igc: {}", b_igc), new_val)]));
		}
		let pat_col = loc_state_pat_tbl.lock().unwrap()
			.get_container("join_tbl").expect("err get join_tbl").lock().unwrap()
			.get_container("val").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);
		let loc_col = loc_state_pat_tbl.lock().unwrap()
			.get_container("join_tbl").expect("err get join_tbl").lock().unwrap()
			.get_container("c1").unwrap().lock().unwrap()
			.duplicate_as_external(0,None);
		#[cfg(test)]{
			assert!(pat_col.to_vec().len()==loc_col.to_vec().len());
		}
		res.lock().unwrap().add_container(loc_state_pat_tbl);

		//5. compress pat_state_loc_tbl to pat_loc_tbl
		let pat_loc_tbl = tbl_to_sorted_tbl(
			&Arc::new(Mutex::new(pat_col)), 
			&Arc::new(Mutex::new(loc_col)), 
			packed_trace_size, "pat_loc");
		let pat_loc_tbl = match pat_loc_tbl	{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let states_final = fsm_acc_combo.lock().unwrap().get_container("states_final").unwrap().lock().unwrap().to_vec();
				report_top_states(&states_final, acdfa, 10, "basis_pats_in_trace (tbl_to_sorted)");
				let vec_err = vec.iter().map(|(s,val)|{
					if s=="target_size::hashmap_2col"{
						let t_val= val*10000 /capacity.max_nibble_len+ 1;
						( format!(
						   "fsm_adv::basis_pats_in_trace from tbl_to_sorted, b_igc: {}", b_igc)
						   ,t_val
						  )
					} else{
						(format!("unknown capacity err at step4: {}, b_igc: {}", s, b_igc), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => pat_loc_tbl
		}?;

		if b_perf{log_perf(LOG1, "-- -- fsm_packed_trace", &mut gt);}
		res.lock().unwrap().add_container(pat_loc_tbl);
		Ok( res )
	}
}

impl <F:PrimeField + ColEle> FsmAdvGadget<F>{
	pub fn new(
		b_igc: bool,
		offset_wea: usize,
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
		let dummy_adv = FsmAdvAdvice::new(b_igc, 
			offset_wea, //offset to word_extract
			&nibbles, acdfa, dummy_inp_state,
			dummy_inp_loc, &dummy_inp_subsigs, capacity, 
			fsm_id, store_subsig_pat).expect("\n\n ==== **** =====\nCannot handle dummy advice generation for fsm_adv. Needs to raise the following for at least one circ. ");
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.lock().unwrap().get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[vec_cfg.len()-1].clone();

		Self{_f: PhantomData, capacity: Clone::clone(capacity), 
			cfgs_context: None,
			my_idx_in_context: None, dummy_cfg, fsm_id, b_igc,
			offset_wea}
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
	/// COST: (nlen - nibble len, alen - acc_states_ratio * neln
	///         note acc_states are ALL acc states even including
	///         non-related sigs. This average is 5% in real data.)
	///    2.25*nlen + 5*alen
	fn validate_fsm_acc_container(&self, fsm_acc: &Container<FpVar<F>>, r1: FpVar<F>, _r2: FpVar<F>, cs: ConstraintSystemRef<F>)
	->Result<(), SynthesisError>{
		//1. asserts all states and transitions must be in range
		// NOTE: we do not have to assert in range for nibbles they
		// are done already in word_extract_adv gadget
		let b_perf = false;
		let b_debug = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let (nc, nv) = (cs.num_constraints(), cs.num_witness_variables());
		let nlen = self.capacity.max_nibble_len;
		let alen = self.capacity.max_nibble_len 
			* self.capacity.basis_acc_states/10000;
		let alen = if alen<2 {2} else {alen};
		let _tblid_state = FpVar::new_constant(cs.clone(),
			F::from(self.fsm_id+6))?;
		let _tblid_trans= FpVar::<F>::new_constant(cs.clone(), 
			F::from(self.fsm_id + 3))?;
		let si_states = fsm_acc.get_container("si_states")?.lock().unwrap().to_vec();
		let si_trans= fsm_acc.get_container("si_trans")?.lock().unwrap().to_vec();
		assert!(si_states.len()==nlen+1 && si_trans.len()==nlen);
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 1", &mut gt);
		}

		//2. NO need to check transition id because its constant.
		// ALSO no need to check the si_states_id as there will be a 
		// logup check between all states and the final_states
		// the way we perform it is the Logup relation
		// (sid_state - fsm_id) is either 1 or 0 as selector
		// NOW, if a "fake" sid_state is provided, they can only
		// be (RANGE2, 0, some other fsm_state_sid) where
		// all of these are at least 2^28 away rom the real value. (because
		// how these fsm_id constants are defined like 
		// 0x2000 0000, 0x3000 0000 etc). 
		// on the right hand size, all logup entries are summed up
		// with m_tbl entry set to 1. So, the only way is to
		// have sufficient logup entries with the appropriate count
		// which are caused by the DISTANCE caused by the "fake".
		// We know the the max size of the right hand side table
		// is much smaller than nlen (which is no more than 128k)
		// Thus, there is no way for supplying fake SID_STATE for
		// the states to work.
		//check_arr_eq(&si_states,&tblid_state,"checking states in range")?;
		//check_arr_eq(&si_trans,&tblid_trans,"checking trans in range")?;

		//2. assert correctness of building transition as weighted sum
		// of src, char, dst states
		// COST 2*nlen
		// --> IMPROVED to: 1/4*nlen = 1/4 * nlen
		let unit_var = FpVar::<F>::new_constant(cs.clone(),
			F::from((1<<(self.capacity.acdfa_state_part_bits+4)) as u32))?;
		let hex_var = FpVar::<F>::new_constant(cs.clone(),
			F::from(16 as u32))?;
		let chars = fsm_acc.get_container("nibbles")?.lock().unwrap().to_vec();
		let states = fsm_acc.get_container("states")?.lock().unwrap().to_vec();
		let trans = fsm_acc.get_container("trans")?.lock().unwrap().to_vec();
		assert!(chars.len()==nlen && states.len()==nlen+1 && trans.len()==nlen);
		let pows_51 = build_pows_56_val();
		//constants for the states. Note that
		//for every 4 transitions, there are 5 states involved.
		//for each state the constant actually includes the value for
		//4 transitions.
		let unit= F::from((1<<(self.capacity.acdfa_state_part_bits+4)) as u32);
		let hex = F::from(16 as u32);
		let mut st_cons = vec![F::zero();5];
		for i in 0..4{
			st_cons[i] += hex * pows_51[i];
			st_cons[i+1] += unit * pows_51[i];
		}

		let lb_one = LinearCombination::<F>(vec![(F::one(), Variable::One)]);
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 2.1", &mut gt);
		}
		//IDEA: since char, st1, st2 are all already proved in range.
		//It can be proved that transition is no more than 52-bit
		//We then PACK 4 transitions in one to save constraints
		for i in 0..nlen/4{
			let start = i * 4;
			//LOGICAL CODE BELOW. But we will later directly
			//create LinearCombination to SAVE cost
			// ---------------------------------------
// 			let mut sum_trans = one.clone();
// 			let mut sum_exp = one.clone();
// 			for j in 0..4{//check every 4 transitions
// 				let idx = start + j;
// 				let ch = &chars[idx];
// 				let st1 = &states[idx]; //already plus one
// 				let st2 = &states[idx+1];
// 				// simulate clam_db.rs: add_acdfa_to_lkup
// 				let exp_trans = ch + 
// 					&(st1 * &hex_var) +
// 					&(st2 * &unit_var); //no need to plus one, already did
// 				let trans = &trans[idx];
// 				//check_eq(&trans, &exp_trans, 
// 				//&format!("checking transition {} ", i))?;
// 				sum_trans = &sum_trans + &(&pows_51[j] * trans); //cost 
// 					//nothing because mul with constant!
// 				sum_exp = &sum_exp + &(&pows_51[j] * &exp_trans); 
// 				#[cfg(test)]{
// 					if exp_trans.value().is_ok(){
// 						assert!(exp_trans.value()?==trans.value()?);
// 					}
// 				}
// 			}//end for j
//			check_eq(&sum_trans, &sum_exp,  "ERROR checking trans")?;
			//----------- LOGICAL CODE ABOVE -------------------
			let mut vec_sum_trans = vec![(F::zero(), Variable::One); 9];
				//2 tuples for each tranistion
				//an additional one for the last st2.
			let mut vec_sum_exp = vec![(F::zero(), Variable::One); 4];
			for j in 0..4{
				let idx = start + j;
				let ch = &chars[idx];
				vec_sum_trans[j*2] = var_to_tuple_adv(ch, pows_51[j]);
				vec_sum_trans[j*2+1] = var_to_tuple_adv(&states[idx], 
					st_cons[j]);
				if j==3{
					vec_sum_trans[j*2+2]=var_to_tuple_adv(&states[idx+1],
						st_cons[j+1]);
				}
				vec_sum_exp[j] = var_to_tuple_adv(&trans[idx], pows_51[j]);
			}
			let lb1 = LinearCombination::<F>(vec_sum_trans);
			let lb3 = LinearCombination::<F>(vec_sum_exp);
			//to assert that sum of transition == sum of expected transition
			//for every 4 transitions given that they are already proved
			//in range.
			cs.enforce_constraint( lb1, lb_one.clone(), lb3)?;

		}
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 2.2", &mut gt);
		}

		//IF nlen is not multiple of 4
		for idx in nlen/4*4 .. nlen{
			let ch = &chars[idx];
			let st1 = &states[idx]; //already plus one
			let st2 = &states[idx+1];
			let exp_trans = ch + 
				&(st1 * &hex_var) +
				&(st2 * &unit_var); //no need to plus one, already did
			let trans = &trans[idx];
			check_eq(&exp_trans, &trans, "ERROR checking trans part2")?;
		}
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 3", &mut gt);
		}


		let locs = fsm_acc.get_container("locs")?.lock().unwrap().to_vec();
		let inp_loc = &locs[0];
		let _oup_loc = &locs[1];
		#[cfg(test)]{
			assert!(inp_loc.value()? 
				+ F::from(nlen as u32) == _oup_loc.value()?);
		}
		//check_increase(&locs)?;
		//optimized to: as locs are already guarnateed to be less than
		//26 bit, use packcheck_increase() instead
		//cut cost to 1/4 of nlen
		//let pows_31 = build_pows_31(cs.clone());
		//packcheck_increase(&locs, &pows_31)?;
		// --> no need anymore as locs are directly computed
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 4", &mut gt);
		}


		//3. check the validity of final states
		//3.1 build a vec_dummy array to indicate the dummy entries
		//on the states_final and locs_final
		//COST: 2*alen
		let zero_var = FpVar::<F>::zero();
		let one_var = FpVar::<F>::one();
		let one_wit_var = new_var(&cs, F::one());
		check_eq(&one_var, &one_wit_var, "one wit var err")?;
		let f_id_final = new_const_var(&cs, F::from(self.fsm_id+2));
		let f_range = new_const_var(&cs, F::from(RANGE2 as u32));
		let si_states_final= fsm_acc.get_container("si_states_final")?
			.lock().unwrap().to_vec();
		//let si_locs_final= fsm_acc.get_container("si_locs_final")?
		//	.lock().unwrap().to_vec();
		let states_final= fsm_acc.get_container("states_final")?
			.lock().unwrap().to_vec();
		let locs_final= fsm_acc.get_container("locs_final")?
			.lock().unwrap().to_vec();
		if b_debug{
			let max_loc = F::from( (1u64<<RANGE2_BIT) - 1);
			locs_final.iter().for_each(|x| {
				assert!(x.value().unwrap()<max_loc); 
			});
		}
		let vec_not_dummy = states_final.iter().map(|s|
			&one_var - &is_zero_better(s, &cs).unwrap()
		).collect::<Vec<FpVar<F>>>();
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 5", &mut gt);
		}

		//3.1 check the validity of sid_states_final 
		//either it is 0 or fid_state (note that even we skip checking
		//sid of the "full" states vec, because of the logup, we do
		//have to check them here to provide the source of validity.
		//formally:
		// i.e., sid_states_final[i] = vec_not_dummy[i] * fid_final
		// this costs one constraint
		// similarly: for sid_locs_final[i]:
		// sid_locs_final = vec_dummy[i] * f_range2
		// COST: alen
		//let lb_minus_final = var_to_lb(&f_id_final, -F::one());
		for i in 0..alen{
			better_select_check(&vec_not_dummy[i], &f_id_final, &f_range,
				&si_states_final[i])?;
			//check_eq(&si_locs_final[i], &(&vec_not_dummy[i] * &f_range),
			// NO Need as locs are computed correctly always
		}
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 6", &mut gt);
		}

		//3.2 use sid_states_final to sum up the logup equation LHS
		//COST: 2*nlen
		assert!(states.len()==nlen+1);
		let unit_cvar = new_const_var(&cs, F::from(1u32<<RANGE2_BIT));
		let f_id_non_final = F::from(self.fsm_id+1);
		let non_final_cvar = new_const_var(&cs, f_id_non_final); 
		let lb_one= LinearCombination::from((F::one(),Variable::One));
		//3.2.1 precompute the value of inverse values
		let states_val = states.iter().map(|s| s.value().unwrap())
			.collect::<Vec<F>>();
		let r1_val = r1.value()?;
		let unit_val = unit_cvar.value()?;
		let inp_val = inp_loc.value()?;
		let vec_inv = states_val.into_par_iter().enumerate().map(|(i,s)|{
			let val = r1_val + s + unit_val *(inp_val + F::from(i as u32));
			val.inverse().expect("INV err")
		}).collect::<Vec<F>>();
		assert!(vec_inv.len()==nlen+1); //because have 1 more last state

		let si_state_vals = si_states.iter().map(|s| s.value().unwrap())
			.collect::<Vec<F>>();
		let c_non_final = non_final_cvar.value()?;
		let mut exp_lhs_sum_val = vec![F::zero();nlen+1];
		for i in 1..nlen+1{
			exp_lhs_sum_val[i] = exp_lhs_sum_val[i-1] + 
				(si_state_vals[i] - c_non_final) * vec_inv[i];
		}
		let exp_lhs_sum = exp_lhs_sum_val.into_iter().map(|v|
			new_var(&cs, v)
		).collect::<Vec<FpVar<F>>>();

		//3.2.2 now compute the constraints
		let tp_r1 = var_to_tuple_adv(&r1, F::one());
		let tp_inp_loc = var_to_tuple_adv(&inp_loc, unit_val);
		for i in 0..nlen{
			//let nc = cs.num_constraints();
			//we skip item [0] because it's handled in
			//the last round
			//Here the mul with unit_var is costing nothing
			//as unit_cvar is a CONSTANT.
			//We do NOT use another random here because locs[i]
			//has ALREADY been proved to be in range RANGE2
			//so we can just "concat" these two numbers of bit-strings
			//let item = &r1 + &states[i+1] + &unit_cvar*&(inp_loc + 
			//	&new_const_var(&cs, F::from( (i+1) as u32)));
			//let item_val = item.value()?;
			//let inv = item_val.inverse().expect("INV err");
			//let lb_item = var_to_lb(&item, F::one());
			let lb_item = LinearCombination::<F>( vec![
				(unit_val * F::from((i+1) as u32), Variable::One),
				tp_r1.clone(),
				var_to_tuple_adv(&states[i+1], F::one()),
				tp_inp_loc.clone(),
			]);
			let inv = vec_inv[i+1]; //improved using precompued value
			let inv_var = new_var(&cs, inv);
			let lb_inv = var_to_lb(&inv_var, F::one());
			//check_eq(&(&item *&inv_var), &one, "inv failed")?;
			cs.enforce_constraint(
				lb_item,
				lb_inv.clone(),
				lb_one.clone()
			)?;
		
			
			//let sel = &si_states[i+1] - &non_final_cvar; 
			//assert!(!si_states[i+1].is_constant());
			//lhs_sum = &lhs_sum + &inv_var * &sel;
			//OPTIMIZED CODE below
			//we are stating 
			//exp_lhs_sum[i+1] = exp_hs_sum[i] + inv[i] * si[i+1] - inv[i]*non_final_cvar
			//which is: 
			// inv[i] * si[i+1] = exp_lhs_sum[i+1] - exp_hs_sum[i] + non_final_cvar* inv[i]
			let lb_si = var_to_lb(&si_states[i+1], F::one());
			let lb3 = LinearCombination::<F>(vec![
				var_to_tuple_adv(&exp_lhs_sum[i+1], F::one()),
				var_to_tuple_adv(&exp_lhs_sum[i], F::zero()-F::one()),
				var_to_tuple_adv(&inv_var, c_non_final),
			]);
			cs.enforce_constraint(lb_inv, lb_si, lb3)?;

			//NOT needed (anymore as there is no longer chain)
			//forms a constraint each iteration
			//if i%ADD_CHAIN_SIZE==0{
			//	lhs_sum = &lhs_sum * &one_wit_var; 
			//		//to break long linear combination
			//}
		}
		let lhs_sum = exp_lhs_sum[nlen].clone(); //take the last one
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 7", &mut gt);
		}

		//3.3 use vec_not_dummy[i] to sum up the Logup RHS 
		//COST: 2*alen
		let mut rhs_sum = zero_var.clone();
		assert!(vec_not_dummy.len()==alen);
		assert!(locs_final.len()==alen);
		//3.3.1 precompute invese
		let states_final_val = states_final.iter().map(|s|
			s.value().unwrap()).collect::<Vec<F>>();
		assert!(states_final_val.len()==alen);
		let locs_final_val = locs_final.iter().map(|s|
			s.value().unwrap()).collect::<Vec<F>>();
		let vec_inv= states_final_val.par_iter().zip(locs_final_val.par_iter()).map(|(&a,&b)|{
			let item = r1_val + a + unit_val * b;
			item.inverse().expect("INV err")
		}).collect::<Vec<F>>();
		assert!(vec_inv.len()==alen);
		//3.3.2 build constraints
		for i in 0..alen{
			//let item = &r1 + &states_final[i] + &unit_cvar*&locs_final[i];
			//let item_val = item.value()?;
			//let inv = item_val.inverse().expect("INV err");
			//let inv_var = new_var(&cs, inv);
			//let lb_item = var_to_lb(&item, F::one());

			//OPTIMIZED version:
			let inv_var = new_var(&cs, vec_inv[i]); 
			let lb_item = LinearCombination::<F>(vec![
				tp_r1.clone(),
				var_to_tuple(&states_final[i]),
				var_to_tuple_adv(&locs_final[i], unit_val)
			]);
			let lb_inv = var_to_lb(&inv_var, F::one());
			//check_eq(&(&item *&inv_var), &one, "inv failed")?;
			cs.enforce_constraint(
				lb_item,
				lb_inv,
				lb_one.clone()
			)?;
			rhs_sum = &rhs_sum + &inv_var * &vec_not_dummy[i];
			if i%ADD_CHAIN_SIZE==0{
				rhs_sum = &rhs_sum * &one_wit_var; //to break long chain
			}
		}
		check_eq(&lhs_sum, &rhs_sum, "logup check fails")?;
		if b_perf{
			log_perf(log_level, "validate_fsm_acc_container step 8", &mut gt);
		}


		if b_perf{
			println!(" ### --- validate_fsm_acc_container, nlen: {}, alen: {}, nc: {}, nv: {}", nlen, alen, cs.num_constraints() - nc,cs.num_witness_variables()-nv);
		}

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
	/// COST: subsig*(1 + 11*avg_pat_subsig)
	fn validate_proj_subsig_store(&self, 
		proj_store: &Container<FpVar<F>>,  //the projected result
		r1: FpVar<F>,
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		let b_perf = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let (nc, nv) = (cs.num_constraints(), cs.num_witness_variables());
		//1. check all subtable IDs are correct.
		// This includes the check that the encoded column is
		// indeed in the external lookup table.
		// COST: 0
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
				.lock().unwrap().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		assert!(sid_cols.len()==vals.len());
		if b_perf{
			log_perf(log_level, "valid_proj_subsig_store step 1", &mut gt);
		}

		//NOT needed anymore
		//for i in 0..vals.len(){
		//	check_arr_eq(&sid_cols[i], &vals[i], 
		//		&format!("err check sid of {}", col_names[i]))?;
		//}

		//2. check the m_tbl proof
		//COST: subsigs + 2*subsigs*avg_pat*subsig 
		let cols = col_names.iter().map(|name| proj_store.get_container(&name).
			unwrap().lock().unwrap().to_vec()
			).collect::<Vec<Vec<FpVar<F>>>>();
		let (subsig, id1, state, id2, pat, encoded, inp_subsigs, m_tbl) = 
		  (&cols[0],&cols[1],&cols[2],&cols[3],&cols[4],&cols[5],&cols[6],&cols[7]);
		assert_logup(cs.clone(), &inp_subsigs, &subsig, &m_tbl, &r1)?; 

		//3. check the validity of encoding
		//COST: avg_pat_subsig * subsig
		let unit_bits = self.capacity.acdfa_state_part_bits;
		assert!(unit_bits==RANGE2_BIT, "reset HexACDFA state part bits or RANGE2_BIT so that they are aligned");
		verify_encoded_table(cs.clone(),
			unit_bits, &vec![subsig,id1,state,id2,pat], encoded)?;
		if b_perf{
			log_perf(log_level, "valid_proj_subsig_store step 2", &mut gt);
		}

		//4. check the table is wellformed 
		//COST: 8 avg_pat_subsig * subsig
		let unit_bits = self.capacity.acdfa_state_part_bits;
		//note: no sorted proof is needed as it's proved to be part of
		//external table, thus guarantee completeness of vals for a key.
		assert_well_formed_sorted(cs.clone(),subsig,id1,state,None,None,None,
			None, r1,unit_bits)?;
		if b_perf{
			log_perf(log_level, "valid_proj_subsig_store step 3", &mut gt);
		}

		if b_perf{
			println!(" ### --- validate_proj_store: subsigs: {}, pats_per_subsig: {}, nc: {}, nv: {}", self.capacity.subsigs, self.capacity.avg_pats_per_subsig, cs.num_constraints() - nc,cs.num_witness_variables()-nv);
		}

		Ok( () )
	}

	/// validate the correctness of packed_trace containercontainer
	///
	/// COST: 
	/// 10* subsigs * avg_pat_per_subsig + 
	/// + nlen*(4*basis_acc_states/10000 + 14 * basis_pats/10000
	///			+ 7 * basis_unique/10000) + 10*subsigs_avg_pats*subsigs
	/// + 17 * subsigs*avg_pats_subsig
	/// + 17 * subsigs *avg_pats_subsig + 31 * nlen * (basis_pats/10000)
	/// = 
	/// nlen*(4*basis_acc_states + 45*basis_pats + 7*basis_unique_states)/10000
	/// + 44 * subsigs * avg_pats_per_subsig
	fn validate_packed_trace(
		&self, 
		r1: &FpVar<F>, //random nonce from msg2
		r2: &FpVar<F>, //random nonce from msg2
		all: &Container<FpVar<F>>,  //entire container
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		let b_perf = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let mut nc = cs.num_constraints();
		//1. check sorted_set of states is correct
		// cost: 10* subsigs * avg_pat_per_subsig
		let nlen = self.capacity.max_nibble_len;
		let _plen = self.capacity.subsigs * 
			self.capacity.avg_pats_per_subsig;
		let sname = if self.b_igc {"fsm_adv_stmt_igc"} else
			{"fsm_adv_stmt_cs"};
		let col_to_sorted_combo = all.search_container(
			&format!("{} packed_trace sorted_states", sname))?;
		verify_col_to_sorted_set(r1, &col_to_sorted_combo.lock().unwrap(), cs.clone())?;
		if b_perf{
			log_perf(log_level, "valid_packed_trace step 1", &mut gt);
		}

		#[cfg(test)]{
			assert!(_plen==col_to_sorted_combo.lock().unwrap().get_container("id")
				.unwrap().lock().unwrap().to_vec().len());
			assert!(_plen==col_to_sorted_combo.lock().unwrap().get_container("sorted_val").unwrap().lock().unwrap().to_vec().len());
		}
		if b_perf{
			println!(" --- validate_packed_trace step 1: -- col len: {}, sorted_val: {}, cs: {}", col_to_sorted_combo.lock().unwrap().get_container("id").unwrap().lock().unwrap().to_vec().len(), col_to_sorted_combo.lock().unwrap().get_container("sorted_val").unwrap().lock().unwrap().to_vec().len(), cs.num_constraints()-nc);
			nc = cs.num_constraints();
		}

		//2. check the filtered table of state and loc
		//COST: 4*N + 16n + 7m + 10k
		//where N = ratio_acc_states * nlen
		//  n = ratio_pats_in_trace * nlen 
		//  m = ratio_unique_states * nlen
		//  k = avg_pats_per_subsig * subsigs 
		// i.e.,
		//nlen(4*basis_acc_state/10000 + 14*basis_pats/10000
		//	+ 7 *basis_unique_states/10000) + 10 * subsigs *avg_pats*subsigs
		let states_col = all.search_container( 
			&format!("{} fsm_acc states_final", sname))?;
		let locs_col = all.search_container(
			&format!("{} fsm_acc locs_final", sname))?;
		let state_loc_tbl = all.search_container(
			&format!("{} packed_trace state_loc_tbl", sname))?;
		let sorted_states = all.search_container(
			&format!("{} packed_trace sorted_states", sname))?;
		verify_tbl_filtered_to_sorted_tbl(&r1, &r2,
			&states_col, &locs_col, &sorted_states,  &state_loc_tbl, 
			cs.clone())?;
		if b_perf{
			println!(" --- validate_pack_trace step 2, nlen: {} cs: {}", nlen, cs.num_constraints()-nc);
			nc = cs.num_constraints();
		}
		if b_perf{
			log_perf(log_level, "valid_packed_trace step 2", &mut gt);
		}

		//3. check the pattern_state_tbl
		// COST: 17 * subsigs * avg_pats_subsig
		let proj_pats_col = all.search_container( 
			&format!("{} proj_subsig_store pat", sname))?;
		let proj_states_col = all.search_container( 
			&format!("{} proj_subsig_store state", sname))?;
		let pat_state_tbl = all.search_container(
			&format!("{} packed_trace pat_state_tbl", sname))?;
		verify_tbl_to_sorted_tbl(&r1, &r2,
			&proj_pats_col, &proj_states_col, &pat_state_tbl, cs.clone())?;
		if b_perf{
			print!(" --- verify_packed trace step 3: verify pattern-state: {}", 
				proj_states_col.lock().unwrap().to_vec().len());
			println!("--- cs: {}", cs.num_constraints()-nc);
			nc = cs.num_constraints();
		}
		if b_perf{
			log_perf(log_level, "valid_packed_trace step 3", &mut gt);
		}

		//4. check the pat_state_loc
		//COST: 17 * subsigs *avg_pats_per_subsig + 
		//   31 * pats_per_trace * nlen
		let pat_state_loc_tbl = all.search_container(
			&format!("{} packed_trace pat_state_loc_tbl", sname))?;
		verify_tbl_left_join(&r1, &r2,
			&pat_state_tbl, &state_loc_tbl, 
			&sorted_states, 
			&pat_state_loc_tbl, cs.clone())?;
		if b_perf{
			println!("--- verify packed_trace step 4: cs: {}", 
				cs.num_constraints()-nc);
		}
		if b_perf{
			log_perf(log_level, "valid_packed_trace step 4", &mut gt);
		}

		Ok( () )
	}

	/// validate packed_trace
	/// COST: ???
	/// let alen = ratio_of_acc_states * nlen (usually 5%)
	///   plen = ratio_of_patterns * nlen (usually alen *1.1 6%)
	///   ulen = ratio of unique states * neln (usually less than 1%) 
	/// 3*ulen + ulen + 2ulen + 2aleb + 6plen + 27plen
	/// = 6ulen + 4alen + 33plen
	/// roughly 34 * ratio_of_patterns * nlen (usually< 1.5 nlen)
	fn validate_packed_trace_v2(
		&self, 
		r1: &FpVar<F>, //random nonce from msg2
		r2: &FpVar<F>, //random nonce from msg2
		all: &Container<FpVar<F>>,  //entire container
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		let b_perf = false;
		let log_level = LOG2;
		let mut gt = GTimer::new();
		let mut gt0 = GTimer::new();
		let mut nc = cs.num_constraints();
		let nc0 = cs.num_constraints();
		let sname = if self.b_igc {"fsm_adv_stmt_igc"} else {"fsm_adv_stmt_cs"};
		let nlen = self.capacity.max_nibble_len;
		let ulen = nlen * self.capacity.basis_unique_states/10000;
		let alen = self.capacity.max_nibble_len 
			* self.capacity.basis_acc_states/10000;
		let plen = self.capacity.max_nibble_len 
			* self.capacity.basis_pats_in_trace /10000;

		//1. retrieve the state_final and locs final from fsm_acc combo
		//no cost
		let states_final= 
			all.search_container(
			&format!("{} fsm_acc states_final", sname))?.lock().unwrap().to_vec();
		let locs_final= 
			all.search_container(
			&format!("{} fsm_acc locs_final", sname))?.lock().unwrap().to_vec();
		if b_perf{
			log_perf(log_level, &format!(
				"valid_packed_trace step 1. cs: {}", cs.num_constraints()-nc),
				&mut gt);
			nc = cs.num_constraints();
		}

		//2. verify the projected states-pat table.
		//2.1 verify the proj_states-pat table is lightly 
		// well formed (i.e., a 2-col sorted-val table)
		//NOTE that this proof mainly guarantees that
		//the projection from the acdfa part of lookup is COMPLETE (covering
		//all pat_id entries related to a state).
		//COST: 3*ulen
		let tbl_proj_states_pats = 
			all.search_container(
			&format!("{} packed_trace tbl_proj_states_pats", sname))?;
		assert_wide_wellformed(&tbl_proj_states_pats, "key")?;
		if b_perf{
			log_perf(log_level, &format!(
				"valid_packed_trace step 2.1, ulen: {} cs: {}", 
					ulen, cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}

		//2.2. verify the encoded column is indeed an encoded
		//form of the proj_states and proj_pats column
		//NOTE that the sid of encoded column AUTOMATICALLY
		//asserts that the encoded_column is part of the database
		//also note that since this function is actually "de-factor"
		//only twice: one for cs and one for igc of the acdfa for
		//bag words, it's actually "fixed circuit" and the 
		//sid is "fixed/constants" for these two types. No need to double check
		//sid values.
		//Also note: we do NOT have to check if the proj_states
		//cover ALL the accept states along the trace, as
		//later when we assert the left-join relation, 
		// it automatically implies this relation.
		//
		// COST: ulen
		let col_encoded = 
			all.search_container(
			&format!("{} packed_trace encoded_proj_state_pat", sname))?
			.lock().unwrap().to_vec();
		let c1 = tbl_proj_states_pats.lock().unwrap().get_container("key")
			.unwrap().lock().unwrap().to_vec();
		let c2 = tbl_proj_states_pats.lock().unwrap().get_container("val")
			.unwrap().lock().unwrap().to_vec();
		let c3 = tbl_proj_states_pats.lock().unwrap().get_container("id")
			.unwrap().lock().unwrap().to_vec();
		let c4 = tbl_proj_states_pats.lock().unwrap().get_container("count")
			.unwrap().lock().unwrap().to_vec();
		let vec_cols = [&c1[..], &c2[..], &c3[..], &c4[..]];
		verify_encode_cols_in_range(&col_encoded[..], &vec_cols)?;

		if b_perf{
			log_perf(log_level, &format!(
				"valid_packed_trace step 2.2. ulen: {}, cs: {}", 
				ulen,cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}

		//3. check the loc_state_pat_tbl
		//COST: 2*alen + 2*ulen + 6*plen 
		let loc_state_pat_tbl = all.search_container(
			&format!("{} packed_trace loc_state_pat_tbl", sname))?;
		verify_tbl_left_join_wide(&r1, &r2,
			&locs_final,
			&states_final,
			&tbl_proj_states_pats,
			&loc_state_pat_tbl, 
			cs.clone()
		)?;
		if b_perf{
			log_perf(log_level, &format!(
				"valid_packed_trace step 3. ulen: {}, alen: {}, plen: {}, cs: {}", ulen, alen, plen, cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}

		//4. verify the pat-loc table is projected from the pat_state_loc_tbl 
		//COST: 27*plen 
		let pat_col= loc_state_pat_tbl.lock().unwrap()
			.get_container("join_tbl")?.lock().unwrap()
			.get_container("val")?;
		let loc_col= loc_state_pat_tbl.lock().unwrap()
			.get_container("join_tbl")?.lock().unwrap()
			.get_container("c1")?;
		let pat_loc_tbl = all.search_container( 
			&format!("{} packed_trace pat_loc", sname))?;
		#[cfg(test)]{
			assert!(pat_col.lock().unwrap().to_vec().len()==plen);
		}
		verify_tbl_to_sorted_tbl(&r1, &r2,
			&pat_col, &loc_col, &pat_loc_tbl, cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!("validate_packed trace trace step 4: verify pat_loc tbl (len: {})  is sorted: {}. ", plen, cs.num_constraints()-nc), &mut gt);
			log_perf(log_level, &format!("valid_packed_trace TOTAL: ulen: {}, alen: {}, plen: {}, nlen: {}, COST: {} cs. ", ulen, alen, plen, nlen, cs.num_constraints()-nc0), &mut gt0);
		}


		Ok( () )
	}


	/// VERSION 1 of assert_msg3 - DEPRECATED
	/// COST (nlen - nibble len, alen - perc of accepted states * trace len
	///     note that accepted states are for all
	/// nlen*(2.5+9*ratio_acc_states + 45*ratio_pats + 7*ratio_unique_states)
	///  + subsig *(1+ 55*avg_pats_per_subsig)
	/// REAL DATA:  average
	/// ratio_acc_states < 6%  (max 30%)
	/// ratio_pats <0.5%
	/// ratio_unique_states < 0.1%
	/// avg_pats_per_subsig = 5 avg (max 10 - limited by config, which
	///   does not cause false positive of flagging malware)
	/// subsigs - 2k
	/// So total cost < nlen * 4 + 2k * 250 (max) 
	///
	///  *** PROBLEM of Performance ***: 
	/// estimate of avg_pats_per_subsig does not
	/// precisely reflect the cost of proj_store as some subsigs
	/// have super large sets of states (which compressed into one pat)
	/// but the proje_store needs to have these states built in
	/// so this function is deprecated.
	#[allow(dead_code)]
	fn assert_msg3_v1(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig,
		_word_id: FpVar<F>, _subseg_id: FpVar<F>) 
		-> Result<(), SynthesisError>{
		let b_perf = false;
		let log_level = LOG1;
		let mut gt = GTimer::new();
		let mut nc = cs.num_constraints();
		let nc0 = cs.num_constraints();
		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;
		let pss = stmt.get_container("proj_subsig_store")?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();

		//2. validate the fsm_acc combo 
		// nlen*(3+ 5*ratio_acc_states_per_trace)
		let fsm_acc = stmt.get_container("fsm_acc")?;
		self.validate_fsm_acc_container(&fsm_acc.lock().unwrap(), r1.clone(),
			r2.clone(), cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!(
				" ## fsm_adv step1: {}", cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}

		//3. validate the proj_subsig_store
		// COST: subsig*(1 + 11*avg_pat_subsig)
		self.validate_proj_subsig_store(&pss.lock().unwrap(),r1.clone(),cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!(
				" ##fsm_adv step2: {}", cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}

		//3. validate the packed trace combo
		// nlen*(4*basis_acc_states + 45*basis_pats + 7*basis_unique_states)/10000
		// + 44 * subsigs * avg_pats_per_subsig
		self.validate_packed_trace(&r1, &r2, &stmt, cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!(" ## fsm_adv step3: {}, total: {}", 
				cs.num_constraints()-nc,
				cs.num_constraints()-nc0
			), &mut gt);
		}

		Ok(())
	}

	#[allow(dead_code)]
	fn assert_msg3_v2(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig, 
		_word_id: FpVar<F>, _subseg_id: FpVar<F>) 
		-> Result<(), SynthesisError>{
		let b_perf = false;
		let log_level = LOG1;
		let mut gt = GTimer::new();
		let mut nc = cs.num_constraints();
		let nc0 = cs.num_constraints();
		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;
		//let _pss = stmt.get_container("proj_subsig_store")?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();

		//2. validate the fsm_acc combo 
		// nlen*(3+ 5*ratio_acc_states_per_trace)
		let fsm_acc = stmt.get_container("fsm_acc")?;
		self.validate_fsm_acc_container(&fsm_acc.lock().unwrap(), r1.clone(),
			r2.clone(), cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!(
				" ## fsm_adv step1: {}", cs.num_constraints()-nc), &mut gt);
			nc = cs.num_constraints();
		}


		//3. validate the packed trace
		self.validate_packed_trace_v2(&r1, &r2, &stmt, cs.clone())?;
		if b_perf{
			log_perf(log_level, &format!(" ## fsm_adv step3: {}, total: {}", 
				cs.num_constraints()-nc,
				cs.num_constraints()-nc0
			), &mut gt);
		}

		Ok( () )
	}

}

impl <F:PrimeField + ColEle> SigmaGadget<F> for FsmAdvGadget<F>{
	fn get_name(&self)->&str {"FsmAdvGadget"}

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

		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA], 0, 0)
	}

	fn est_cost(&self)->usize{
		// key is the low basis_pat_in_trace 
		let est = 
			118 * 
			self.capacity.max_nibble_len 
			* self.capacity.basis_pats_in_trace/10000 			
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
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig, 
		_word_id: FpVar<F>, _subseg_id: FpVar<F>) 
		-> Result<(), SynthesisError>{
		let w_id = FpVar::new_constant(cs.clone(), F::zero())?;
		let s_id = FpVar::new_constant(cs.clone(), F::zero())?;
		if B_FSM_ADV_NEW{
			self.assert_msg3_v2(i, cs, wtns, wtns_cfg, w_id, s_id)
		}else{
			self.assert_msg3_v1(i, cs, wtns, wtns_cfg, w_id, s_id)
		}
	}

}

// ---------------------------------------------------
// Utility Functions
// ---------------------------------------------------


#[cfg(test)]
pub mod tests_fsm_adv_gadget{
	use ark_ff::{Zero};
	use std::{sync::Arc};
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
		let db = ClamavDB::<Fr>::build_db_from_dir(path).expect("db err");

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
		let adv_wea = WordExtractAdvAdvice::new(&word, act_size, false)
			.expect("word_extract_adv err");
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.lock().unwrap().get_cfg(); 

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
			subsigs: 5,
			avg_pats_per_subsig: 4,
			basis_pats_in_trace: 15*100,
			basis_unique_states: 40*100,
			basis_acc_states: 10*100,
		};

		let nibbles = stmt_wea.lock().unwrap().get_container("nibbles").unwrap()
			.lock().unwrap().to_vec();
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
		let adv_faa = FsmAdvAdvice::new(false, //case sensitive,
			1, //dist to wea
			&nibbles, &acdfa, inp_state, 
			inp_loc, &input_subsigs, &cap, fsm_id, 
			&bundle.vec_subsig_stores[0]).unwrap(); //for SED
		let stmt_faa = adv_faa.stmt_container;
		let cfg_faa = stmt_faa.lock().unwrap().get_cfg(); 


		//2.3 given cfgs, set up the positions
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa];
		ContainerConfig::adjust_locations(&mut vec_cfg); //resolve


		//3. generate the 7 segments of output for building statment
		let cps1 = stmt_wea.lock().unwrap().gen_stmt_components(); //from inp to si_data
		let cps2 = stmt_faa.lock().unwrap().gen_stmt_components(); //from inp to si_data

		let cps = cps1.0.into_iter().zip(cps2.0.into_iter()).map(|(a,b)|
			vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();

		//4. create the gadget
		let lkup_share_size = 4usize;
		let mut fag = FsmAdvGadget::<Fr>::new(false, 1, //dist to wea
			&acdfa, &cap, fsm_id,
			&vec![cfg_wea.clone()], &bundle.vec_subsig_stores[0]);
		fag.set_container_cfg(vec_cfg.clone().into(), 1);  //it's the 2nd cfg
		let _sizes = fag.get_to_add_size(); //test if sizes are ok
		let rg = Arc::new(fag);

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
