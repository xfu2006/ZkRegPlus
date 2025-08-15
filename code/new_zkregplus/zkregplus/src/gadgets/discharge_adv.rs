/* Created 05/06/2025
   Implementation initially completed 06/11/2025
   Further improvement to cut cost and completed: 06/26/2025
*/
//! This gadget is used for discharging subsigs using the streaming alg.
//! It produces the sigs that discharged.

use rayon::iter::{IntoParallelRefIterator,ParallelIterator,IntoParallelIterator
	, IndexedParallelIterator};
use std::{rc::{Rc},cell::{RefCell},collections::{HashMap}};
use ark_ff::{PrimeField};
use std::{marker::{PhantomData},collections::{HashSet}};
use crate::gadgets::{
	commons::{gen_m_table,check_arr_eq,encode_cols,decode_cols
		,new_const_var, encode_2col_var, encode_2col_var_adv,
		check_arr_eq_arr, encode_cols_var_adv, is_sorted,
		check_eq, encode_2col, check_rg2},
	db::{assert_logup, verify_encoded_table, assert_well_formed_sorted},
	traits::{Container,
		Col,
		IDX_WORD, IDX_INP,IDX_DATA, 
		IDX_SI_INP,  IDX_OUP, IDX_SI_OUP,
		IDX_SI_DATA,ComponentAdvice},
};
use ark_r1cs_std::{
	fields::{ fp::FpVar, FieldVar},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};
use data_processor::{
//	hex_acdfa::HexACDFA,
	clam_db::{
		RANGE2,
		//CHAR, 
		STORE_SUBSIG_STEP,
		RANGE2_BIT, ID_ENCODED_NORMAL_STEP, ID_ENCODED_LAST_STEP,
			ID_ENCODED_PAT, ID_ENCODED_PREV_ENCODED,
			ID_ENCODED_RG_START, ID_ENCODED_RG_END, ID_ENCODED_SUBSIG,
	},
	type_def::{SubsigStepStore},
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{
		SigmaGadget,
		WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, 
		NdAdvice,Capacity
	},
	container_config::{ContainerConfig},
	circuits_super::field_to_usize,
};
use std::any::Any;

// -----------------------------------------------
//		Structs
// -----------------------------------------------
/// type of stepqueue decides its to_container() size
#[derive(Clone,Debug,PartialEq)]
pub enum StepQueueType{
	/// representing the items to add for each step
	ToAdd,
	/// represent the itmes to delete
	ToDel,
	/// represent the result of forward propagation or backward pruning
	Res,
}

/// A step queue represents the state of the SED processing algorithm.
/// For each (subsig-id-pat) it includes the list of current "valid"
/// locations (in terms that they are propagated by the previous id/step,
/// and at this momoment, they are not eliminated by the next step locations
/// by back-elimination).
/// Note that for the same subsig its step queue at run time can
/// have dyanmic size! (depending on a step has VALID location).
/// By default, each step queue has a step 0 - which default has location
/// 1 (its "real steps" start at step id 1 - corresponding to its first pattern)
#[derive(Clone,Debug,PartialEq)]
pub struct StepQueue<F:PrimeField>{
	/// the list of subsigs (sorted)
	pub subsigs: Vec<F>,

	/// map from subsig id to the vector of StepQueueItems.
	/// Each item corresponds to one step (DOES NOT include
	/// any dummy entries - all entries are real. Always length>=1,
	/// as the first step 0 has the initial location 1)
	pub store_items: HashMap<F, Vec<StepQueueItem<F>>>,

	pub capacity: DischargeAdvCapacity,

	pub q_type: StepQueueType,
}

/// A step queue item represents the info of step que
/// for ONE step of ONE subsig.
#[derive(Clone,Debug,PartialEq)]
pub struct StepQueueItem<F: PrimeField>{
	/// encoded version of subsig-id-pat-rg_start-rg_end
	pub encoded: F, 
	/// the sorted locations (does NOT HAVE DUMMY ENTRIES)
	pub locs: Vec<F>,

	/// subsig ID: real subsig ID of (sig, subsig_id) generated in clamdb. 
	pub subsig: F,
	/// step (id). They are valid steps from 1 to number of steps only/
	/// NOT including 0 and max dummy entries.
	pub step: F,
	/// pattern ID: starts from 1
	pub pat: F, 
	/// rg_start for this item (i.e., propgating from last layer)
	pub rg_start: F,
	/// rg_end (included)
	pub rg_end: F,
}

/// A StepFwdPrf represents the forward propagation from
/// each layer to next layer. It works by taking the current
/// loc in the StepQueue, and take the range requirement of the
/// next layer, and given the pac-loc information, retrieve the
/// next layer locations in range. Similar to StepQueue, it has
/// the structure of mapping from subsig to the corresponding StepFwdPrfItem
pub struct StepFwdPrf<F:PrimeField>{
	/// the list of subsigs
	pub subsigs: Vec<F>,

	/// map from subsig id to the vector of StepFwdPrfItem
	/// the vec is padded with dummy 0 and max entries
	pub store_items: HashMap<F, Vec<StepFwdPrfItem<F>>>,

	pub capacity: DischargeAdvCapacity,
}

/// A stepfwdprf item represents the list of
/// generated locations (for the next layer).
/// This design wastes memory, in the sense that
/// ** a lot of columns such as (subsig-id-pat-rg1-rg2) will be
/// ** repeated for the same key. An alternative design is to
/// ** allocate a FIXED number of loc entries for each key (encoded
///  ** subsig-d-pat-rg1-rg2-loc). Note that this alternative design
///  ** does waste meomry over table length (as each key may have
///  ** rather different number of locations screened from trace).
///  ** our current approach wastes constant blow up of columns (around 6).
///  ** comparing the two approaches, we pick up the first.
pub struct StepFwdPrfItem<F:PrimeField>{
	// -------------- output into container info below ------
	// diff1 and diff2 are used
	// to verify the correctness of the query result. They have to
	// be included in output into the Statement instance for range check.
	// note that diff1 and diff2 are always in range [0,max] (non-negative).
	//
	// Example: loc1: 10,   (rg_start,rg_end) = (10,20) -> qry: (20,30)
	// The available locations (contained in a pat-id-loc table),
	// for the next pat after qry [20,30] is the following,
	// where 3-17 and 7-31 are wrapping entries (real result is 25-26-27)
	//
	// (pat2-3-17)
	// (pat2-4-25)
	// (pat2-5-26)
	// (pat2-6-27)
	// (pat2-7-31)
	//
	// --> generated StepFwdPrfItem
	// (subsig...rg2)         pat_id  loc diff1  diff2
	
	// 200 ...                 3       17  2        - 
	// 200 ...                 4       25  5        4
	// 200 ...                 5       26  6    	3 
	// 200 ...                 6       27  7    	2
	// 200 ...                 7       31  -   		0
	// Definition here:
	// b_begin = prev src_encoded_step_loc!=self.src_encode_step_loc
	// b_end = self.src_encode_step_loc!=next.src_code_step_loc
	// diff1 = if begin{ {rg_start+loc1-new_loc-1} //for >
	//            end {0}
	//            else {new_loc - (rg_start+loc1) //for >=
	// diff2 = if b_begin {0}
	//         else if end {new_loc - (rg_end+loc1)-1} //for >
	//         else {rg_end+loc1-new_loc}

	/// the ID of the loc in pat-loc table.
	pub vec_pat_id: Vec<F>,
	/// the destination locations which result in diff1 and diff2
	pub vec_dst_loc: Vec<F>,
	/// see formula in discussion. mainly dest_loc - (rg1 + loc1)
	pub vec_diff1: Vec<F>,
	/// see formula in discussoin. mainly (rg2_loc1)-dest_loc.
	/// the four columns vec_pat_id, ..., vec_diff2 should have
	/// the same length. If there are NO locations available, as the QUERY,
	/// two dummy entries with (0,0) and (some_id, max) will be 
	/// the entries (with no effective entries in between).
	/// So vec_diff2.len is at least 2.
	pub vec_diff2: Vec<F>,

	// ---------------------------------------------------------
	// the following information when output to container will be
	// replicated as the same length of vec_pat_id. (waste of memory).
	// However, compared with alternative design which wastes
	// memory over table length, we choose this one (see discussion at 
	// beginning).
	// ----------------------------------------------------------------------
	/// the one who's generating (note its location is src_step)
	/// it's encoding of (subsig-id/step-pat-rg_s-rg_e)
	pub src_encoded: F,
	/// step (id).  dest step is src_step+1 (0 means starting pos before step 1)
	pub src_step: F,
	/// the location embedded in src_encoded_step_loc
	pub src_loc: F,


	/// the encoded word of the destination step (step+1).
	/// it's encoding of (subsig-id/step-pat-rg_s-rg_e)
	/// when the src step is n or max, dst_encode (dst_pat, ...) are all max.
	/// this will be handled in verification logic
	pub dst_encoded: F,
	/// pattern ID of the next step
	pub dst_pat: F, 
	/// range_start used of the next step
	pub dst_rg_start: F,
	/// range_end of the next step
	/// (1,1) as range_start and rg_end has one element.
	pub dst_rg_end: F,
	/// it's the same as src_subsig
	pub dst_subsig: F,
}

/// A StepBwdPrf represents the backward progagation proof to
/// remove existing items from StepQueue. Note that this step is
/// optional and conservative, in the sense that even if it is
/// not performed, it does NOT affect the correctness of the proof.
/// But the benefit of this proof is to reduce the size of StepQueue
/// especially when there are multiple steps in folding for proving one
/// long word, which accumulates intermediate locs in the StepQueue.
/// This reduce the size and improves prover performance
pub struct StepBwdPrf<F:PrimeField>{
	/// the list of subsigs
	pub subsigs: Vec<F>,

	/// map from subsig id to the vector of StepFwdPrfItem
	/// the vec is padded with dummy 0 and max entries
	/// note that it is still ordered by steps. Each item
	/// corresponds to ONE step.
	pub store_items: HashMap<F, Vec<StepBwdPrfItem<F>>>,

	pub capacity: DischargeAdvCapacity,
}

/// A stepBwdprf item represents the list of
/// generated locations (for the PREVOIUS layer).
/// The design is similar to StepFwdPrf.
/// Note that it's different from StepFwdPrf that for each
/// encoded (subsig-step...), it only starts from the MIN location
/// (not every location), and eliminate those locs in the
/// previous layer such that prev_loc + rg_end < min_loc_current_layer
/// the reason is that "future" incoming locations can only be
/// larger than the current locations. Thus there is NO WAY for
/// future locations to be "linked" from the prevoius laye locatoins,
/// thus they should be eliminated.
pub struct StepBwdPrfItem<F:PrimeField>{
	/// the one who's generating (note its location is src_step)
	/// it's encoding of (subsig-id/step-pat-rg_s-rg_e)
	pub src_encoded: F,
	/// the subsig
	pub src_subsig: F,
	/// step (id).  
	pub src_step: F,
	/// pattern.  
	pub src_pat: F,
	/// NOTE for each src_encoded we only use the min_loc (it can be 0 - dummy)
	/// when there is no location existing.
	pub src_min_loc: F,
	/// range_start 
	pub src_rg_start: F,
	/// range_end of the next step
	/// (1,1) as range_start and rg_end has one element.
	pub src_rg_end: F,

	/// the encoded word of the PREVIOUS step (step-1).
	/// it's encoding of (subsig-id/step-pat-rg_s-rg_e)
	pub prev_encoded: F,
	/// the location to be eliminated.
	pub locs_to_del: Vec<F>,
}



/// Capacity of the gadget
#[derive(Clone,Debug,PartialEq)]
pub struct DischargeAdvCapacity{
	/// should be LEGS (62) x max_word_len
	pub max_nibble_len: usize, 

	/// how many subsigs in input
	pub subsigs: usize,

	/// average number of ACTIVE patterns over subsigs during
	/// forward propgation (note that this is a smaller number
	/// than the avg_pats_per_subsig in fsm_adv component, that reflects
	/// the STATIC number of steps of a subsig in average).
	pub avg_active_pats_per_subsig: usize,

	/// NOTE:  percentage number, e.g. 50 means 50 percent.
	/// avg_pats*per_trace_perc/100 * max_nibble_len -> SIZE of packed tracke
	/// wherethe packed trace is the (pat, loc) table size. 
	pub perc_pats_in_trace: usize,
}

/// Advice for the Discharge Subsig Gadget.
#[derive(Clone,Debug)]
pub struct DischargeAdvAdvice<F:PrimeField>{
	/// if this is for fsm (acdfa) for ignore case
	pub b_igc: bool,

	/// distance to the fsm_adv gadget
	/// this is a positive number (fsm_adv may be 1 or 2 positions
	/// ahead in the composite component mapper). Store the
	/// distance as a positive number
	pub offset_fsm: usize,

	/// the first id related to the corresponding ACDFA
	pub fsm_id: u32,


	/// the statement container object which is serialized to a vector
	/// of statement
	pub stmt_container: Rc<RefCell<Container<F>>>,

	/// capacity
	pub capacity: DischargeAdvCapacity,
}

#[allow(dead_code)]
/// This gadget is responsible for discharging subsigs (which are given
/// as non-deterministic advice).
/// It takes the pat-loc (for final states of given subsigs) from the
/// fsm_adv, and runs the streaming algorithm for handling discharging
/// subsigs, and finally run tri-logic to generate the signatures that
/// are discharged (note that: this result is only valid at the last step of
/// a word.
#[derive(Clone,Debug)]
pub struct DischargeAdvGadget<F:PrimeField>{ 
	/// if this is for fsm (acdfa) for ignore case
	pub b_igc: bool,

	/// distance to the fsm_adv gadget
	/// this is a positive number (fsm_adv may be 1 or 2 positions
	/// ahead in the composite component mapper). Store the
	/// distance as a positive number
	pub offset_fsm: usize,

	/// the first related lookup subtbl_id defined in clam_db.rs
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	pub fsm_id: u32, 
	/// the capacity
	pub capacity: DischargeAdvCapacity,

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
impl <F:PrimeField> StepQueue<F>{
	/// this function determine the size of the to_vec() and 
	/// to_container() size. Note that to_vec() and to_container()
	/// generates multiple column tables essentially, the size is
	/// the length of the column in the table. The size is
	/// determined by the capacity.
	pub fn vec_size(
		q_type: &StepQueueType, 
		capacity: &DischargeAdvCapacity
	)->usize{
		// basic idea is to take the max of the size needed by
		// subsig patterns and the locations appeared in traces.
		// adjust by the type of the StepQueue.
		let size_pat = capacity.subsigs*capacity.avg_active_pats_per_subsig;
		let perc_compress_ratio = match q_type{
			StepQueueType::Res => 100, //100%
			StepQueueType::ToAdd => 50, //50% (in practice maybe smaller)
			StepQueueType::ToDel => 20, //10% 
		};
		let size_trace =  capacity.max_nibble_len 
			* capacity.perc_pats_in_trace/100
			* perc_compress_ratio/100;
		if size_pat > size_trace {size_pat} else {size_trace}
	}

	/// converts the step queue to a vec combination of two columns
	pub fn to_vec(&self, subsig_store_info: &SubsigStepStore)->Vec<F>{
		let ct = self.to_container("temp", false, false, false, false, subsig_store_info);
		let encoded = ct.borrow().get_container("encoded").unwrap()
			.borrow().to_vec();
		let locs = ct.borrow().get_container("locs").unwrap()
			.borrow().to_vec();
		let n = Self::vec_size(&self.q_type, &self.capacity);
		assert!(encoded.len()==n && locs.len()==n);

		vec![encoded,locs].concat()
	}

	pub fn dump(&self){
		for subsig in &self.subsigs{
			println!(" ---- subsig: {}", subsig);
			let items = self.store_items.get(subsig).unwrap();
			for item in items {item.dump();}
		}
	}

	/// as parse_from is called by the sed_component in reconstruct object
	/// as the result queue. its type is set to Res
	pub fn parse_from(vec: &Vec<F>, capacity: &DischargeAdvCapacity)->Self{
		//1. split vec 2 cols: <encoded, loc>
		let tn = Self::vec_size(&StepQueueType::Res, capacity);
		assert!(vec.len()%2==0);
		assert!(vec.len()<=tn*2);
		let n = vec.len()/2;
		let vecs = (0..2).into_iter().map(|i| vec[n*i..n*(i+1)].to_vec())
			.collect::<Vec<Vec<F>>>();

		//2. collect groups based on encoded -> Vec<loc>
		let vec_groups: HashMap::<F, Vec<F>> = (0..n).collect::<Vec<_>>()
		.into_par_iter().filter(|&i| !vecs[0][i].is_zero())
			.fold(|| HashMap::<F, Vec<F>>::new(), |mut acc, i|{
				let encoded = vecs[0][i];
				let loc = vecs[1][i];
				acc.entry(encoded).or_insert(vec![]).push(loc);

				acc
			}).reduce(|| HashMap::<F, Vec<F>>::new(), |mut acc1, acc2|{
				for (k, mut vec) in acc2{
					let mut vec1 = if acc1.contains_key(&k) 
						{acc1.get(&k).unwrap().clone()} else {vec![]};
					vec1.append(&mut vec);
					acc1.insert(k, vec1);
				}

				acc1
			});

		//3. construct step queue item
		let vec_encoded = vec_groups.keys().map(|x| *x).collect::<Vec<F>>();
		let queue_items = vec_encoded.par_iter().map(|encoded|{
			let loc_tuples = vec_groups.get(encoded).unwrap();
			StepQueueItem::parse_from(*encoded, &loc_tuples)
		}).collect::<Vec<StepQueueItem<F>>>();

		//4. collect items by subsig
		let store_unsorted_items = queue_items.par_iter().fold(||
			HashMap::<F,Vec<StepQueueItem<F>>>::new(), |mut acc, item|{
				acc.entry(item.subsig).or_insert(vec![]).push(item.clone());
				acc
			}).reduce(|| HashMap::<F,Vec<StepQueueItem<F>>>::new(), 
			|mut acc1,acc2|{
				for (k, mut vec) in acc2{
					let mut vec1 = if acc1.contains_key(&k) 
						{acc1.get(&k).unwrap().clone()} else {vec![]};
					vec1.append(&mut vec);
					acc1.insert(k, vec1);
				}

				acc1
			});
		let store_items = store_unsorted_items.par_iter()
			.filter(|(k,_v)| !k.is_zero())
			.map(|(k,v)|{
				let mut v2 = v.clone();
				v2.sort_by(|a,b| a.step.partial_cmp(&b.step).unwrap());
				(*k,v2)
			}).collect::<HashMap<F,Vec<StepQueueItem<F>>>>();
		let mut subsigs = store_items.keys().map(|x| *x).collect::<Vec<F>>();
		subsigs.sort();

		//4. construct StepQueue
		let q_type = StepQueueType::Res;
		Self{subsigs, store_items, capacity: Clone::clone(capacity), q_type}
	}

	/// given the <pat,loc> table generate the 
	/// <ToAdd, Result, StepFwdPrf>
	pub fn gen_forward_prf(
		&self, 
		pat_loc: &Rc<RefCell<Container<F>>>,
		info: &SubsigStepStore)
	->(Self, Self, StepFwdPrf<F>){
		//1. pat_loc to hash table for easy processing
		let hm_loc = Self::pat_loc_to_hm(pat_loc);
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let mut stores_to_add = HashMap::new();
		let mut stores_res = HashMap::new();
		let mut stores_prf = HashMap::new();

		//2. process each subsig, propagating step by step
		for subsig in &self.subsigs{
			//2.1 retrieve ths subsig info
			let u_subsig = field_to_usize(subsig);
			let subsig_rec= info.subsig_to_steps.get(&u_subsig).expect(
				&format!("cannot find step info for subsig: {}", subsig));
			let max_steps= subsig_rec.vec_pm_bounds.len();
			let pm_bounds = &subsig_rec.vec_pm_bounds;
			let items =  self.store_items.get(subsig).unwrap();
			assert!(max_steps+1>=items.len());
			let init_item = items[0].clone();
			assert!(init_item.locs.len()==1 && init_item.step==zero
				&& init_item.locs[0]==F::one() );

			//2.2. init the return result
			let mut vec_to_add = vec![];
			let mut vec_res = vec![init_item]; 
			let mut vec_fwd_prf = vec![];

			//2.3 propgate for each layer (note: stop when there are NO MORE
			// to proess - thus, we do not NECESSARILY have to extend to full
			// steps).
			// ALSO note we retrieve the "fresh" LAST result layer (not from
			// the input step queue)
			for i in 1..max_steps+1{
				//use i-1 because step0 is not in info
				let (rg_start,rg_end) =(pm_bounds[i-1].1.0,pm_bounds[i-1].1.1);
				let f_rg_start = F::from(rg_start as u32);
				let f_rg_end = F::from(rg_end as u32);
				let dst_pat = F::from(subsig_rec.vec_pm_bounds[i-1].0 as u32);
				let locs_available = hm_loc.get(&dst_pat).map_or(
					//default is empty - two dummy entries
					vec![(zero,zero), (one,max)], 
					//if found, still has two dummy entries around
					//as the result of query range, the first is smaller
					//than qry.min and the last is larger than the qry.max
					//with the real entries in between
					|vec| vec.to_vec()
				);
				let mut cur_q_item= if i<items.len() {items[i].clone()}
					else {StepQueueItem::new(*subsig, F::from(i as u32),
							dst_pat, f_rg_start, f_rg_end, vec![])};
				let mut total_added = 0;
				for j in 0..vec_res[i-1].locs.len(){//each encoded-loc
					let (to_add_item, fwd_prf_item) = vec_res[i-1].
						gen_forward_prf(dst_pat, f_rg_start, f_rg_end, 
							j, &locs_available);
					cur_q_item.add(&to_add_item);
					total_added += to_add_item.locs.len();
					if to_add_item.locs.len()>0{
						vec_to_add.push(to_add_item);
					}
					vec_fwd_prf.push(fwd_prf_item);
				}
				//we will stop if results in 0 items added
				//when it has explored ALL existing items in the
				//current sq_res. Note that when total_added is 0
				//there might be other pac_loc that fits further steps
				//not processed in items yet.
				if total_added==0 && i>=items.len() {break};
				//otherwise push the most recent queue_item
				vec_res.push(cur_q_item);
			}

			//2.3 update the stores
			stores_to_add.insert(*subsig, vec_to_add);
			stores_res.insert(*subsig, vec_res);
			stores_prf.insert(*subsig, vec_fwd_prf);
		}

		//3. construct the return
		let sq_to_add = StepQueue::new(self.subsigs.clone(),
			stores_to_add, &self.capacity, StepQueueType::ToAdd);
		let sq_res = StepQueue::new(self.subsigs.clone(),
			stores_res, &self.capacity, StepQueueType::Res);
		let sfp = StepFwdPrf::new(self.subsigs.clone(),
			stores_prf, &self.capacity);

		(sq_to_add, sq_res, sfp)
	}

	/// Basic idea: get the MIN location (excluding zero) from
	///   each step, and then propgate backward.
	/// NOTE that we start from the last step of the fwd step queue result
	/// (this is NOT necessarily the last step of the subsignature),
	/// and works layer by layer backward until the moment we do not
	/// have any to eliminate (so it might stop in the middle, not
	/// necessarily reach the 1st step). Note that even if with max eliminate,
	/// we NEVER eliminate the default location 1 for step 0 (this step
	/// is always kept for each subsinature), for simplifying the
	/// proof in the next gadget to reason about the trilogic value
	///of the subsig. (Thus each subsig has at least one level 0 record
	/// in the final step-queue after elimination even if it has no real
	/// entries in step queue).
	///
	/// Return: <ToRemove, Result, StepBwdPrf>
	pub fn gen_backward_prf(&self) ->(Self, Self, StepBwdPrf<F>){
		//1. init data
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		let mut stores_to_del= HashMap::new();
		let mut stores_res = HashMap::new();
		let mut stores_prf = HashMap::new();

		//2. process each subsig, propagating step by step
		for subsig in &self.subsigs{
			//2.1 set up and verify data 
			// note that "self" represent the RESULT of the fwd propgation
			// process.
			let items =  self.store_items.get(subsig).unwrap();
			let init_item = items[0].clone();
			assert!(init_item.locs.len()==1 && init_item.step==zero
				&& init_item.locs[0]==F::one() ); //this is what we will keep
												  //for each subsig
			let steps = items.len(); 
			assert!(items[steps-1].step==F::from((steps-1) as u32));

			let mut vec_to_del= vec![];
			let mut vec_res = vec![items[steps-1].clone()];
			let mut vec_bwd_prf = vec![];

			//2.2 propgate from last step .. to 2 (included).
			// NOTE that we never produce the bwdprf from step1 -> step0
			// because we want to keep step0 for each subsig for future use
			// we break from the loop when there is no more proof to produce.
			// (which implies no update of min_loc for layers, thus no more
			//   need to explore further).
			if steps>=2{
			  for j in 0..steps-2{
				//2.2.1 retrive min loc
				let i = steps - 1 -j; //i from steps-1 to 2 (included)
				let (_rg_start,rg_end) = (vec_res[j].rg_start, 
					vec_res[j].rg_end); //retrieve the fresh LAST result
				let min_loc = vec_res[j].locs.iter().map(|l| *l).min().
					map_or(F::zero(), |x| x);

				//2.2.2 compute to_del
				let mut to_del = items[i-1].locs.iter().filter(|loc|
					**loc + rg_end < min_loc).map(|loc| *loc)
					.collect::<Vec<F>>();
				to_del.sort();


				let set_to_del = to_del.iter().map(|x| *x)
					.collect::<HashSet<F>>();
				let set_prev = items[i-1].locs.iter().map(|x| *x)
					.collect::<HashSet<F>>();
				let mut res = set_prev.difference(&set_to_del)
					.into_iter().map(|x| *x)
					.collect::<HashSet<F>>()
					.into_iter().map(|x| x).collect::<Vec<F>>();
				res.sort();
				assert!([&to_del[..],&res[..]].concat().into_iter().map(|x| x)
							.collect::<HashSet<F>>() ==
						set_prev);

				//2.2.3 compute the bwd_prf
				let src_encoded = items[i].encoded;
				let prev_encoded = items[i-1].encoded;
				let bwd_prf = StepBwdPrfItem::new(src_encoded,min_loc,
					prev_encoded, &to_del);
				let mut item_res = items[i-1].clone();
				item_res.locs = res;
				let mut item_to_del = items[i-1].clone();
				item_to_del.locs = to_del;

				//2.2.4 update the vecs
				if item_to_del.locs.len()==0 {break;} //no need to add empty
				vec_res.push(item_res);
				vec_to_del.push(item_to_del);
				vec_bwd_prf.push(bwd_prf);
			  }//end for
			}//end if

			//2.3 update the stores
			let vec_res:Vec<_> = vec_res.into_iter().rev().collect();
			let vec_to_del:Vec<_> = vec_to_del.into_iter().rev().collect();
			let vec_bwd_prf:Vec<_> = vec_bwd_prf.into_iter().rev().collect();
			assert!(vec_to_del.len()==vec_bwd_prf.len());
			let (n,n2) = (items.len(), vec_to_del.len());
			assert!(vec_res.len()==n2+1);
			let new_vec_res = [	items[0..(n-n2-1)].to_vec(), vec_res].concat();
			assert!(new_vec_res.len()==items.len());

			stores_to_del.insert(*subsig, vec_to_del);
			stores_res.insert(*subsig, new_vec_res);
			stores_prf.insert(*subsig, vec_bwd_prf);
		}

		//3. construct the return
		let sq_to_del= StepQueue::new(self.subsigs.clone(),
			stores_to_del, &self.capacity, StepQueueType::ToDel);
		let sq_res = StepQueue::new(self.subsigs.clone(),
			stores_res, &self.capacity, StepQueueType::Res);
		let sfp = StepBwdPrf::new(self.subsigs.clone(),
			stores_prf, &self.capacity);

		(sq_to_del, sq_res, sfp)
	}



	/// generate hashmap which maps from pat_id to a vector
	/// of locs which is wrapped with 0 and max entries
	fn pat_loc_to_hm(pat_loc: &Rc<RefCell<Container<F>>>)
	->HashMap<F, Vec<(F,F)>>{
		//1. retrieve cols
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let pats = pat_loc.borrow().get_container("sorted_key")
			.unwrap().borrow().to_vec();
		let ids = pat_loc.borrow().get_container("sorted_id")
			.unwrap().borrow().to_vec();
		let locs = pat_loc.borrow().get_container("sorted_val")
			.unwrap().borrow().to_vec();
		let n = pats.len();
		assert!(ids.len()==n && locs.len()==n);

		//2. fold and collect
		let hs=(0..n).into_par_iter().fold(|| HashMap::<F,Vec<(F,F)>>::new(),
			|mut acc, i|{
				acc.entry(pats[i]).or_insert(vec![]).push((ids[i], locs[i]));
				acc
			}).reduce(|| HashMap::<F, Vec<(F,F)>>::new(), |mut acc1, acc2|{
				for (k, mut vec) in acc2{
					let mut vec1 = if acc1.contains_key(&k) 
						{acc1.get(&k).unwrap().clone()} else {vec![]};
					vec1.append(&mut vec);
					acc1.insert(k, vec1);
				}
				acc1
			});

		let hs_sorted = hs.into_par_iter()
		.filter(|(k,_)| !k.is_zero())
		.map(|(k,v)|{
			let mut v2 = v.clone();
			v2.sort_by(|a,b| a.0.partial_cmp(&b.0).unwrap());
			assert!(v2[0].1==zero && v2[v2.len()-1].1==max);
			(k, v2)
		}).collect::<HashMap<F,Vec<(F,F)>>>();

		hs_sorted
	}

	pub fn new(subsigs: Vec<F>, store_items: HashMap<F,Vec<StepQueueItem<F>>>, capacity: &DischargeAdvCapacity, q_type: StepQueueType)->Self{
		assert!(!subsigs.contains(&F::zero()));
		assert!(!store_items.contains_key(&F::zero()));
		Self{subsigs, store_items, capacity: Clone::clone(capacity),q_type}
	}

	/// generate the container (including the si cols)
	/// generate two cols of equal length (encoded, loc)
	/// when loc is 0 (it is dummy entry means no available locs)
	/// b_inp indicates whether to add to inp_buf or DATA
	/// b_oup indicates whether  to add to oup_buf (b_inp and b_oup cannot
	///   be true)
	/// b_step indicates whether to add an step column
	/// b_subsig: indiates whether to add_subsig column column
	/// NOTE: for step and subsig (and their IDs), regardless if
	/// b_inp or b_oup is set, they are stored in DATA(SI_DATA).
	pub fn to_container(&self, 
		name: &str, 
		b_inp: bool, 
		b_step:bool, 
		b_oup: bool,
		b_subsig: bool, 
		subsig_store_info: &SubsigStepStore,
	)->Rc<RefCell<Container<F>>>{
		#[cfg(test)] { assert!(is_sorted(&self.subsigs)); }
		assert!(!b_inp || !b_oup); //b_inp and b_oup cannot be on the same time
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		let vec_tuples = self.subsigs.par_iter().map(|subsig|{
			let items = self.store_items.get(subsig).unwrap();
			let vec_tuples = items.par_iter().map(|item|{
				let tuples = item.locs.iter().filter(|loc| !loc.is_zero())
					.map(|loc| (item.encoded,item.step,*loc,*subsig))
					.collect::<Vec<(F,F,F,F)>>();
				let tuples = vec![
					tuples
				].concat();
				tuples
			}).flatten().collect::<Vec<(F,F,F,F)>>();
			vec_tuples
		}).flatten().collect::<Vec<(F,F,F,F)>>();
		let vec_encoded = vec_tuples.par_iter().map(|x| x.0)
			.collect::<Vec<F>>();
		let vec_step = vec_tuples.par_iter().map(|x| x.1)
			.collect::<Vec<F>>();
		let vec_locs = vec_tuples.par_iter().map(|x| x.2)
			.collect::<Vec<F>>();
		let vec_subsigs= vec_tuples.par_iter().map(|x| x.3)
			.collect::<Vec<F>>();

		//3. consruct container
		let n = Self::vec_size(&self.q_type, &self.capacity);
		assert!(n>vec_encoded.len(), "StepQueue type: {:?} buf too small, either adjust the compression ratio in vec_size() first, then check the perc_pats_in_trace in DischargeAdvCapacity, n: {}, vec_encoded.len: {}", self.q_type, n, vec_encoded.len());
		let n2 = n-vec_encoded.len();
		let vec_encoded = vec![vec![zero; n2], vec_encoded].concat();
		let vec_locs= vec![vec![zero; n2], vec_locs].concat();
		let vec_step= vec![vec![zero; n2], vec_step].concat();
		let vec_subsigs= vec![vec![zero; n2], vec_subsigs].concat();
		let vec_sid_step = vec_step.par_iter().enumerate().map(|(i,s)|{
			if i<n2{
				SubsigStepStore::gen_step_tbl_id(*s,ID_ENCODED_NORMAL_STEP)
			}else{
				let subsig = field_to_usize(&vec_subsigs[i]);
				let info = subsig_store_info.subsig_to_steps.get(&subsig)
					.expect(&format!("cannot find subsig: {}",subsig));
				let num_steps = info.vec_pm_bounds.len();
				let src_step = vec_step[i];
				let encoded = vec_encoded[i];
				let b_last_step = F::from(num_steps as u32) == src_step;
				let tag = if b_last_step {ID_ENCODED_LAST_STEP} else
					{ID_ENCODED_NORMAL_STEP};
				SubsigStepStore::gen_step_tbl_id(encoded,tag)
			}
		}).collect::<Vec<F>>();

		#[cfg(test)]{ for i in 0..vec_locs.len(){assert!(vec_locs[i]<_max);} }
		let res = Container::new(name); 
		let seg = if b_inp {IDX_INP} else if b_oup {IDX_OUP} else {IDX_DATA};
		let si_seg = if b_inp {IDX_SI_INP} else if b_oup {IDX_SI_OUP} else {IDX_SI_DATA};
		
		assert!(vec_encoded.len()==n && vec_locs.len()==n);
		res.borrow_mut().add_col(Col::new(vec_encoded,"encoded",seg));
		res.borrow_mut().add_col(Col::new(vec_locs, "locs", seg));
		res.borrow_mut().add_col(Col::new(vec![F::zero();n],
			"si_encoded",si_seg));
		res.borrow_mut().add_col(Col::new(vec![F::from(RANGE2);n],
			"si_locs",si_seg));

		if b_step{//regardless of inp/oup, they are always in DATA
			assert!(vec_step.len()==n && vec_sid_step.len()==n);
			res.borrow_mut().add_col(Col::new(vec_step,"step",IDX_DATA));
			res.borrow_mut().add_col(Col::new(vec_sid_step, "si_step",IDX_SI_DATA));
		}

		if b_subsig{
			let vec_sid_subsig = vec![F::from(RANGE2); n];
			assert!(vec_subsigs.len()==n && vec_sid_subsig.len()==n);
			res.borrow_mut().add_col(Col::new(vec_subsigs,"subsig",
				IDX_DATA));
			res.borrow_mut().add_col(Col::new(vec_sid_subsig, "si_subsig",
				IDX_SI_DATA));
		}


		res
	}
}

impl <F:PrimeField> StepQueueItem<F>{
	/// return 2 vectors: encoded, loc
	/// padded with 0 and max entry
	pub fn to_vec(&self)->Vec<Vec<F>>{
		let n = self.locs.len();
		let vec_encoded= vec![self.encoded; n+2];
		let vec_locs = vec![
			self.locs.clone(),
		].concat();
		assert!(vec_encoded.len()==n+2 && vec_locs.len()==n+2);
		vec![vec_encoded, vec_locs]
	}

	pub fn new(subsig: F, step: F, pat: F, rg_start: F, rg_end: F, 
		locs: Vec<F>)->Self{
		let encoded = encode_cols(&vec![vec![subsig], vec![step], 
			vec![pat], vec![rg_start], vec![rg_end]], &vec![0,1,2,3,4])[0];
		#[cfg(test)]{
			let dvec = decode_cols(&vec![encoded], 5);
			assert!(subsig==dvec[0][0], "subsig: {}, dev0: {}", subsig, dvec[0][0]);
			assert!(step==dvec[1][0], "step: {}, dev1: {}", step, dvec[1][0]);
			assert!(pat==dvec[2][0], "pat: {}, dev2: {}", step, dvec[2][0]);
			assert!(rg_start==dvec[3][0], "rg1: {}, dev2: {}", rg_start, dvec[3][0]);
			assert!(rg_end==dvec[4][0], "rg2: {}, dev2: {}", rg_end, dvec[4][0]);
		}
		Self{
			encoded, subsig, step, pat, rg_start, rg_end, locs
		}
	}

	/// info has (subsig, step, pat, rg_start, rg_end
	pub fn new2(info: Vec<F>, locs: Vec<F>)->Self{
		let (subsig, step, pat, rg_start, rg_end) = (info[0], info[1], 
			info[2], info[3], info[4]);
		// for step 0, always add position 1 to consider
		let locs = if step==F::zero() {vec![F::one()]} else {locs};
		Self::new(subsig, step, pat, rg_start, rg_end, locs)
	}

	pub fn dump(&self){
		println!("  encoded: {}, subsig: {}, step: {}, pat: {}, rg_start: {}, rg_end: {}, # of locs: {}", self.encoded, self.subsig, self.step, self.pat, self.rg_start, self.rg_end, self.locs.len());
		for i in 0..self.locs.len(){
			println!("        loc {}: {}", i, self.locs[i]);
		}
	}

	/// the loc_tuples should be GUARANTEED guaranteed to be sorted!
	/// NOTE that the loc_tuples will have all the entries including 0 and max.
	/// The result will REMOVE the two dummy entries.
	pub fn parse_from(encoded: F, loc_tuples: &Vec<F>)->Self{
		//1. sort out the locations
		let locs = loc_tuples.clone();
		#[cfg(test)] {
			assert!(is_sorted(&locs));
			let max_val:usize = (1<<RANGE2_BIT) - 1;
			let (zero,_one,max) = (F::zero(),F::one(),F::from(max_val as u32));
			for i in 0..loc_tuples.len(){assert!(locs[i]!=zero&&locs[i]!=max);}
		}

		//2. decode the encoded
		let dvec = decode_cols(&vec![encoded], 5);
		let (subsig, step, pat, rg_start, rg_end) = (dvec[0][0],
			dvec[1][0], dvec[2][0], dvec[3][0], dvec[4][0]);

		Self{encoded, locs, subsig, step, pat, rg_start, rg_end}
	}

	/// given the rg_start and rg_end of the next layer
	/// given the available locs of the next layer
	/// generate the locs to add, and the corresponding proof
	/// for loc[loc_idx] generate the corresponding prf
	pub fn gen_forward_prf(&self, 
		next_pat: F,  //pat of next step
		nxt_rg_start: F, nxt_rg_end: F,  //range belong to next step
		my_loc_idx: usize, //the idx of loc of mine
		locs_available: &Vec<(F,F)>, //query res for available locs for nxt pat 
	)->(StepQueueItem<F>, StepFwdPrfItem<F>){
		//0. initial data
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (_zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));

		let vec_pat_id = locs_available
			.par_iter().map(|x| x.0).collect::<Vec<F>>();
		let vec_locs = locs_available
			.par_iter().map(|x| x.1).collect::<Vec<F>>();
		assert!(vec_locs.len()>=2); //it should at least have two dummy entries
		#[cfg(test)]{
		 use super::commons::{is_incrementing_by_one};
	 	 assert!(is_sorted(&vec_locs) && is_incrementing_by_one(&vec_pat_id));
		}

		let src_loc = self.locs[my_loc_idx];
		let rg1= nxt_rg_start + src_loc;
		let rg2 = nxt_rg_end + src_loc;
		//no need for rg1 as later it will never underflow
		//rg2 reset is needed as later for case i==last
		//  we do dst_loc - rg2 - one (it needs to be a possible number)
		//  to satisfy the range-query semantics.
		let rg2 = if rg2>=max {max-one} else {rg2};

		//2. perform binary search for the query
		let id1 = match vec_locs.binary_search(&rg1) {Ok(k)=>k-1,Err(k) => k-1};
		let id2 = match vec_locs.binary_search(&rg2) {Ok(k)=>k+1,Err(k) => k};

		assert!(id1+1<vec_locs.len() && id2<vec_locs.len() && id2>0);
		assert!(vec_locs[id1]<rg1 && vec_locs[id1+1]>=rg1);
		assert!(vec_locs[id2]>rg2 && vec_locs[id2-1]<=rg2);

		//3. construct the StepQueueItem and StepFwdPrfItem
		let new_locs = (id1+1..id2).collect::<Vec<usize>>().iter().map(|i| 
			vec_locs[*i]).collect::<Vec<F>>();  
		let to_add = StepQueueItem::new(self.subsig, self.step+one,
			next_pat, nxt_rg_start, nxt_rg_end, new_locs);

		let dst_encoded = encode_cols(&vec![vec![self.subsig],
			vec![self.step+one], vec![next_pat], vec![nxt_rg_start], 
				vec![nxt_rg_end]], &vec![0,1,2,3,4])[0];
		let pat_loc_qry = (id1..id2+1).collect::<Vec<usize>>().into_iter()
			.map(|i| (vec_pat_id[i], vec_locs[i])).collect::<Vec<(F,F)>>();

		let prf = StepFwdPrfItem::new(self.encoded, src_loc,
			dst_encoded, pat_loc_qry);
			
		(to_add, prf)
	}

	/// Assumption: other has the same step ID and other relavent info.
	/// The first loc is greater than the last loc of hte current item.
	/// Append the locs
	pub fn add(&mut self, other: &StepQueueItem<F>){
		//1. data assertion
		assert!(self.encoded == other.encoded);
		assert!(self.step == other.step);

		//2. collect and sort locs
		let mut new_locs = vec![self.locs.clone(), other.locs.clone()].concat()
			.into_par_iter().map(|x| x).collect::<HashSet<F>>()
			.into_par_iter().map(|x| x).collect::<Vec<F>>();
		new_locs.sort();
		self.locs = new_locs;
	}

}

impl <F:PrimeField> StepFwdPrf<F>{
	/// return the estimated needed size of buf for to_container
	pub fn vec_size(&self)->usize{
		self.capacity.perc_pats_in_trace * self.capacity.max_nibble_len/100
	}

	/// generate the container (including the si cols)
	/// Will output (src_encoded, src_step, src_loc, dst_encoded, dst_pat,
	///    dst_rg_start, dst_rg_end, dst_loc, pat_id, diff1, diff2)
	pub fn to_container(&self, 
		name: &str, 
		subsig_store_info: &SubsigStepStore
	) ->Rc<RefCell<Container<F>>>{
		//0. check data
		#[cfg(test)] { assert!(is_sorted(&self.subsigs)); }
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, _max) = (F::zero(), F::one(), F::from(max_val as u32));

		//1. build the columns
		let vec_tuples = self.subsigs.par_iter().map(|subsig|{
			let items = self.store_items.get(subsig).unwrap();
			let vec_tuples = items.par_iter().map(|item|{
				let u = item.vec_pat_id.len();
				assert!(item.vec_diff1.len()==u && item.vec_diff2.len()==u);
				let tuples = (0..u).collect::<Vec<usize>>()
					.into_iter().map(|i| (
						item.src_encoded,
						item.src_loc,
						item.src_step,

						item.dst_encoded,
						item.dst_pat,
						item.dst_rg_start,
						item.dst_rg_end,

						item.vec_dst_loc[i], 
						item.vec_pat_id[i], 
						item.vec_diff1[i],
						item.vec_diff2[i],

						item.dst_subsig,
					)).collect::<Vec<(F,F,F,F,F, F,F,F,F,F, F, F)>>();
					
				tuples
			}).flatten().collect::<Vec<(F,F,F,F,F, F,F,F,F,F, F, F)>>();
			vec_tuples
		}).flatten().collect::<Vec<(F,F,F,F,F, F,F,F,F,F, F, F)>>();
		let v_src_encoded = vec_tuples.par_iter().map(|t| t.0)
			.collect::<Vec<F>>();
		let v_src_loc = vec_tuples.par_iter().map(|t| t.1)
			.collect::<Vec<F>>();
		let v_src_step= vec_tuples.par_iter().map(|t| t.2)
			.collect::<Vec<F>>();
		let v_dst_encoded = vec_tuples.par_iter().map(|t| t.3)
			.collect::<Vec<F>>();
		let v_dst_pat = vec_tuples.par_iter().map(|t| t.4)
			.collect::<Vec<F>>();
		let v_dst_rg_start= vec_tuples.par_iter().map(|t| t.5)
			.collect::<Vec<F>>();
		let v_dst_rg_end= vec_tuples.par_iter().map(|t| t.6)
			.collect::<Vec<F>>();
		let v_dst_loc = vec_tuples.par_iter().map(|t| t.7)
			.collect::<Vec<F>>();
		let v_dst_pat_id = vec_tuples.par_iter().map(|t| t.8)
			.collect::<Vec<F>>();
		let v_dst_pat_diff1 = vec_tuples.par_iter().map(|t| t.9)
			.collect::<Vec<F>>();
		let v_dst_pat_diff2 = vec_tuples.par_iter().map(|t| t.10)
			.collect::<Vec<F>>();
		let v_dst_subsig= vec_tuples.par_iter().map(|t| t.11)
			.collect::<Vec<F>>();
		let names = vec!["src_encoded", "dst_encoded", 
			"src_loc", "src_step", 
			"dst_pat", "dst_rg_start", "dst_rg_end",
			"dst_loc", "dst_pat_id", "diff1", "diff2", "dst_subsig"];
		let v2d = vec![v_src_encoded, v_dst_encoded, 
			v_src_loc, v_src_step, 
			v_dst_pat, v_dst_rg_start, v_dst_rg_end,
			v_dst_loc, v_dst_pat_id, v_dst_pat_diff1, v_dst_pat_diff2,
			v_dst_subsig];
		let n = self.vec_size();
		assert!(n>v2d[0].len(), "buf too small, adjust perc_pats_in_trace");
		let n2 = n-v2d[0].len();
		let pad = vec![zero; n2];
		#[cfg(test)]{
			for i in 2..v2d.len(){
				for j in 0..v2d[i].len(){ assert!(v2d[i][j] <= _max); }
			}
		}

		//3. consruct container
		//3.1 the columns
		let res = Container::new(name); 
		let frg = F::from(RANGE2);
		let se = vec![pad.clone(), v2d[0].clone()].concat();//src_encoded
		let de = vec![pad.clone(), v2d[1].clone()].concat();//dst_encoded
		v2d.iter().enumerate().for_each(|(i,vec)|{
			let name = names[i];
			res.borrow_mut().add_col(Col::new(vec![pad.clone(),vec.clone()]
				.concat(), name, IDX_DATA));
		});

		//3.2 sids (note should be added by the right order.
		res.borrow_mut().add_col(Col::new(vec![zero; n], 
			&format!("sid_{}",names[0]), IDX_SI_DATA)); //src_encoded
		res.borrow_mut().add_col(Col::new(vec![zero; n], 
			&format!("sid_{}",names[1]), IDX_SI_DATA)); //dst_encoded
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[2]), IDX_SI_DATA)); //src_loc

		//src_step
		let sids = se.iter().enumerate().map(|(i,s)| {
			if i<n2{
				SubsigStepStore::gen_step_tbl_id(*s,ID_ENCODED_NORMAL_STEP)
			}else{
				let subsig = field_to_usize(&v2d[11][i-n2]);
				let info = subsig_store_info.subsig_to_steps.get(&subsig)
					.expect(&format!("cannot find subsig: {}",subsig));
				let num_steps = info.vec_pm_bounds.len();
				let src_step = v2d[2][i-n2];
				let b_last_step = F::from(num_steps as u32) == src_step;
				let tag = if b_last_step {ID_ENCODED_LAST_STEP} else
					{ID_ENCODED_NORMAL_STEP};
				SubsigStepStore::gen_step_tbl_id( *s,tag)
			}
		}).collect::<Vec<_>>();
		res.borrow_mut().add_col(Col::new(sids,
			&format!("sid_{}",names[3]), IDX_SI_DATA)
		); 

		//columns 4,5,6
		// dst_pat, dst_rg_start, dst_rg_end
		let ids = [4,5,6];
		let cats = [ID_ENCODED_PAT, ID_ENCODED_RG_START, ID_ENCODED_RG_END];
		for x in 0..ids.len(){
			let sids = de.iter().map(|s| SubsigStepStore::gen_step_tbl_id(
				*s,cats[x])).collect::<Vec<_>>();
			res.borrow_mut().add_col(Col::new(sids,
				&format!("sid_{}",names[ids[x]]), IDX_SI_DATA)
			); 
		}

		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[7]), IDX_SI_DATA)); //dst_loc
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[8]), IDX_SI_DATA)); //dst_loc
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[9]), IDX_SI_DATA)); //diff1
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[10]), IDX_SI_DATA)); //diff2

		//col11: dst_subsig
		let sids = de.iter().map(|s| SubsigStepStore::gen_step_tbl_id(
			*s,ID_ENCODED_SUBSIG)).collect::<Vec<_>>();
		res.borrow_mut().add_col(Col::new(sids,
			&format!("sid_{}",names[11]), IDX_SI_DATA)
		); 


		res
	}

	pub fn dump(&self){
		println!("------------- Forward Proof -----------");
		for subsig in &self.subsigs{
			println!(" ---- subsig: {}", subsig);
			let items = self.store_items.get(subsig).unwrap();
			for item in items {item.dump();}
		}
	}

	pub fn new(subsigs: Vec<F>, store_items: HashMap<F,Vec<StepFwdPrfItem<F>>>, capacity: &DischargeAdvCapacity)->Self{
		assert!(!subsigs.contains(&F::zero()));
		assert!(!store_items.contains_key(&F::zero()));
		Self{subsigs, store_items, capacity: Clone::clone(capacity)}
	}
}

impl <F:PrimeField> StepFwdPrfItem<F>{
	/// src_encoded: where which to launch to the to_add,  dst_encoded:
	/// the NEXT encoded i.e., encoding (subisg-step+1-pat-rg_s-rg_e).
	/// when src_encoded corresponds to the LAST step, dst_encoded is max.
	/// when src_encoded belong to dummy entry (max), dst_encoded is max. 
	/// the Vec<(F,F)> corresponds to the query of the pat-loc table
	/// for the qeries of locations (let it be loc2) that satsifies
	/// loc2-loc1 in [rg_s,rg_e]. NOTE that they are NOT padded (just
	/// the query result).
	/// where loc1 is the loc embedded in src_encoded_step_loc.
	pub fn new(src_encoded: F, src_loc: F,
		dst_encoded:F, pat_loc_qry: Vec<(F,F)>)->Self{
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let dec = &decode_cols(&vec![src_encoded], 5);
		let (src_subsig, src_step, _pat, _rg_s, _rg_e) 
			= (dec[0][0], dec[1][0], dec[2][0], dec[3][0], dec[4][0]);
		if dst_encoded==max{//dummy case
			Self{vec_pat_id: vec![], vec_diff1: vec![],
				vec_diff2: vec![],
				src_encoded, src_step, src_loc, 
				dst_encoded: max, dst_pat: max, dst_rg_start: max, 
				dst_rg_end: max, vec_dst_loc: vec![],
				dst_subsig: src_subsig}
		}else{//normal case
			let dec = &decode_cols(&vec![dst_encoded], 5);
			let (dst_subsig, dst_step, dst_pat, dst_rg_start, dst_rg_end) 
				= (dec[0][0], dec[1][0], dec[2][0], dec[3][0], dec[4][0]);
			assert!(dst_subsig==src_subsig);
			assert!(dst_step == src_step + one);
			let vec_pat_id = pat_loc_qry.par_iter().map(|x| 
				x.0.clone()).collect::<Vec<F>>();
			let vec_dst_loc= pat_loc_qry.par_iter().map(|x| 
				x.1.clone()).collect::<Vec<F>>();
			let n_locs = vec_dst_loc.len();
			assert!(n_locs>=2); //at least two wrapping entries

			let rg1= dst_rg_start + src_loc;
			let rg2 = dst_rg_end + src_loc; 
			//no need for similar massage for rg1 as underflow never happens
			let rg2 = if rg2>=max {max-one} else {rg2};
			let vec_diff1 = (0..n_locs).into_par_iter().map(|i|{
				let diff = if i==0 {rg1-vec_dst_loc[i]-one}
					else if i==n_locs-1 {zero} //don't care
					else {vec_dst_loc[i]-rg1}; //normal case
				assert!(diff<=max);
				diff
			}).collect::<Vec<F>>();
			let vec_diff2 = (0..n_locs).into_par_iter().map(|i|{
				let diff = if i==n_locs-1 {vec_dst_loc[i]-rg2-one}
					else if i==0 {zero} //don't care case
					else {rg2-vec_dst_loc[i]};
				assert!(diff<=max);
				diff
			}).collect::<Vec<F>>();
			Self{ 
				vec_pat_id, 
				vec_dst_loc, 
				vec_diff1, 
				vec_diff2, 
				src_encoded, src_step, src_loc, 
				dst_encoded, dst_pat, dst_rg_start, 
				dst_rg_end, dst_subsig 
			}
		}
	}

	pub fn dump(&self){
		println!("Prf: src(encoded: {}, step: {}, loc: {}), destt(key: {}, pat: {}, rg1: {}, rg2: {}). Locs: ---", self.src_encoded, self.src_step, self.src_loc, self.dst_encoded, self.dst_pat, self.dst_rg_start, self.dst_rg_end);
		let n = self.vec_dst_loc.len();
		assert!(self.vec_diff1.len()==n && self.vec_diff2.len()==n &&
			self.vec_pat_id.len()==n);
		for i in 0..n{
			println!("  pat_id: {}, loc: {}, diff1: {}, diff2: {}", self.vec_pat_id[i], self.vec_dst_loc[i], self.vec_diff1[i], self.vec_diff2[i]);
		}
	}
}

impl <F:PrimeField> StepBwdPrfItem<F>{
	/// src_encoded: encoding of (subsig, step, loc, rg_start, rg_end)
	/// min_loc the minimum loc of src_encoded, if no locs available, it's
	/// 0. previous_encoded can be inferred.
	/// locs_to_del is the vector of locations to be deleted
	/// for the PREVIOUS step.
	pub fn new(src_encoded: F, src_min_loc: F, prev_encoded: F,
		locs_to_del: &Vec<F>)
	->Self{
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (_zero,_one,_max) = (F::zero(), F::one(), F::from(max_val as u32));
		let dec = &decode_cols(&vec![src_encoded], 5);
		let (src_subsig, src_step, src_pat, src_rg_start, src_rg_end) 
			= (dec[0][0], dec[1][0], dec[2][0], dec[3][0], dec[4][0]);
		Self{
			src_encoded, src_subsig, src_step, src_pat, src_rg_start, src_rg_end,
			src_min_loc, prev_encoded, locs_to_del: locs_to_del.clone()
		}
	}

	pub fn dump(&self){
		println!("BackPrf: src(encoded: {}, subsig: {}, step: {}, min_loc: {}, rg_s: {}, rg_e: {}), prev: (encoded: {}, locs_to_del---", self.src_encoded, self.src_subsig, self.src_step, self.src_min_loc, self.src_rg_start, self.src_rg_end, self.prev_encoded);
		let n = self.locs_to_del.len();
		for i in 0..n{
			println!("  i: {}, loc: {}", i, self.locs_to_del[i]);
		}
	}

}

impl <F:PrimeField> StepBwdPrf<F>{
	pub fn vec_size(&self)->usize{
		let raw_size = self.capacity.perc_pats_in_trace 
			* self.capacity.max_nibble_len / 100;
		//given that StepBwdPrf is usually much smaller 
		//we give it some fraction of the size of StepFwdPrf
		//adjust in practice
		let compress_ratio = 50;
		let size = raw_size * compress_ratio/100;
		size
	}
	pub fn dump(&self){
		println!("------------- Backward Proof -----------");
		for subsig in &self.subsigs{
			println!(" ---- subsig: {}", subsig);
			let items = self.store_items.get(subsig).unwrap();
			for item in items {item.dump();}
		}
	}

	pub fn new(subsigs: Vec<F>, store_items: HashMap<F,Vec<StepBwdPrfItem<F>>>, capacity: &DischargeAdvCapacity)->Self{
		assert!(!subsigs.contains(&F::zero()));
		assert!(!store_items.contains_key(&F::zero()));
		Self{subsigs, store_items, capacity: Clone::clone(capacity)}
	}

	/// generate the container (including the si cols)
	/// Will output (src_encoded, src_step, src_loc, dst_encoded, dst_pat,
	///    dst_rg_start, dst_rg_end, dst_loc, pat_id, diff1, diff2)
	pub fn to_container(&self, name: &str, subsig_store_info: &SubsigStepStore)->Rc<RefCell<Container<F>>>{
		//0. check data
		#[cfg(test)] { assert!(is_sorted(&self.subsigs)); }
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		//1. build the columns
		let vt = self.subsigs.par_iter().map(|subsig|{
			let items = self.store_items.get(subsig).unwrap();
			let vec_tuples = items.par_iter().map(|item|{
				let u = item.locs_to_del.len();
				let tuples = (0..u).collect::<Vec<usize>>()
					.into_iter().map(|i| (
						item.src_encoded,
						item.src_subsig,
						item.src_step,
						item.src_pat,
						item.src_rg_start,
						item.src_rg_end,
						item.src_min_loc,

						item.prev_encoded,
						item.locs_to_del[i],
					)).collect::<Vec<(F,F,F,F,F,F,F,  F,F)>>();
				tuples
			}).flatten().collect::<Vec<(F,F,F,F,F,F,F, F,F)>>();
			vec_tuples
		}).flatten().collect::<Vec<(F,F,F,F,F,F,F,  F,F)>>();

		let v_src_encoded = vt.par_iter().map(|t| t.0).collect::<Vec<F>>();
		//we skipped subsig.
		let v_src_subsigs= vt.par_iter().map(|t| t.1).collect::<Vec<F>>();
		let v_src_step= vt.par_iter().map(|t| t.2).collect::<Vec<F>>();
		let v_src_pat= vt.par_iter().map(|t| t.3).collect::<Vec<F>>();
		let v_src_rg_end= vt.par_iter().map(|t| t.5).collect::<Vec<F>>();
		let v_src_min_loc= vt.par_iter().map(|t| t.6).collect::<Vec<F>>();

		let v_prev_encoded = vt.par_iter().map(|t| t.7).collect::<Vec<F>>();
		let v_loc_to_del = vt.par_iter().map(|t| t.8).collect::<Vec<F>>();
		let names = vec![
			"src_encoded", "src_step",  //note we don't need subsig
			"src_pat", "src_rg_end", 
			"src_min_loc",
			"prev_encoded", "loc_to_del",
		];
		let v2d = vec![
			v_src_encoded, v_src_step,
			v_src_pat, v_src_rg_end,
			v_src_min_loc,
			v_prev_encoded, v_loc_to_del];
		let n = self.vec_size();
		assert!(n>v2d[0].len(), "buf too small for StepBwdPrf, adjust compress_ratio in vec_size() first, and then the perc_pats_in_trace in capacity");
		let n2 = n-v2d[0].len();
		let pad = vec![zero; n2];
		let se = vec![pad.clone(), v2d[0].clone()].concat();//src_encoded
		let de = vec![pad.clone(), v2d[5].clone()].concat();//prev_encoded
		#[cfg(test)]{
			for i in 0..v2d.len(){
				assert!(v2d[i].len()==v2d[0].len());
				for j in 0..v2d[i].len(){ 
					if i!=0 && i!=5{//not src_encoded, prev_encoded
						assert!(v2d[i][j] <= _max); 
					}
				}
			}
		}

		//3. consruct container
		let res = Container::new(name); 
		let frg = F::from(RANGE2);

		//3.0 src_encoded (col 0)
		res.borrow_mut().add_col(Col::new(vec![zero; n], 
			&format!("sid_{}",names[0]), IDX_SI_DATA)); //src_encoded

		//3.1 src_step (col 1)
		let sids = se.iter().enumerate().map(|(i,s)| {
			if i<n2{
				SubsigStepStore::gen_step_tbl_id(*s,ID_ENCODED_NORMAL_STEP)
			}else{
				let subsig = field_to_usize(&v_src_subsigs[i-n2]);
				let info = subsig_store_info.subsig_to_steps.get(&subsig)
					.expect(&format!("cannot find subsig: {}",subsig));
				let num_steps = info.vec_pm_bounds.len();
				let src_step = v2d[1][i-n2];
				let b_last_step = F::from(num_steps as u32) == src_step;
				let tag = if b_last_step {ID_ENCODED_LAST_STEP} else
					{ID_ENCODED_NORMAL_STEP};
				SubsigStepStore::gen_step_tbl_id( *s,tag)
			}
		}).collect::<Vec<_>>();
		res.borrow_mut().add_col(Col::new(sids, &format!("sid_{}",
			names[1]), IDX_SI_DATA)
		); 

		//3. src_pat,  srgrg_end (col 2,3) 
		let ids = [2,3];
		let cats = [ID_ENCODED_PAT, ID_ENCODED_RG_END];
		for x in 0..ids.len(){
			let sids = se.iter().map(|s| SubsigStepStore::gen_step_tbl_id(
				*s,cats[x])).collect::<Vec<_>>();
			res.borrow_mut().add_col(Col::new(sids,
				&format!("sid_{}",names[ids[x]]), IDX_SI_DATA)
			); 
		}

		//3.4. src_min_loc (col 4)
		// it will be proved to be the min of the loc
		//of locs in sq_res, which is already proved in range.
		//so no need to prove here (can even assign 0)
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[4]), IDX_SI_DATA)); //dst_loc

		//3.5 prev_encoded (col 5) - using table ID_ENCODED_PREV_ENCODED
		// so later we do not have to check their relation
		let sids = se.iter().zip(de.iter()).map(|(s,_d)|{
			//for "d" - prev_encoded its tag id is generated using
			//the source_encoded under category ID_ENCODED_PREV_ENCODED
			//so later in validate_bwrf_validate we simply check the
			//sid for each prev_encoded.
			SubsigStepStore::gen_step_tbl_id(*s,ID_ENCODED_PREV_ENCODED)
		}).collect::<Vec<_>>();
		res.borrow_mut().add_col(Col::new(sids,
			&format!("sid_{}",names[5]), IDX_SI_DATA)); //encoded-prev_encode

		//3.6 loc_to_del (col 6) - just in RANGE2
		res.borrow_mut().add_col(Col::new(vec![frg; n], 
			&format!("sid_{}",names[6]), IDX_SI_DATA)); //dst_loc

		//3.7 add real data cols
		v2d.into_iter().enumerate().for_each(|(i,vec)|{
			let name = names[i];
			res.borrow_mut().add_col(Col::new(vec![pad.clone(),vec].concat(), 
				name, IDX_DATA));
		});

		res
	}
}
impl DischargeAdvCapacity{
	/// this determines the pat_loc 2-col table len, it's also
	/// the length of step_queue.  (although techniqlly step_queue len
	/// should be the max of num_sub_sig_steps and perc_loc * max_nibble,
	/// but we simplify the calculation here).
	pub fn get_pat_loc_len(&self)->usize{
		let pats_len = self.perc_pats_in_trace 
			* self.max_nibble_len/100;
		pats_len
	}
}

impl Capacity for DischargeAdvCapacity{
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		let other = r_other.as_any().downcast_ref::<DischargeAdvCapacity>()
			.expect("downcast err"); 

		self.max_nibble_len >= other.max_nibble_len &&
		self.subsigs >= other.subsigs &&
		self.avg_active_pats_per_subsig >= other.avg_active_pats_per_subsig &&
		self.perc_pats_in_trace >= other.perc_pats_in_trace

	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(DischargeAdvCapacity{
			max_nibble_len: self.max_nibble_len,
			subsigs: self.subsigs,
			avg_active_pats_per_subsig: self.avg_active_pats_per_subsig,
			perc_pats_in_trace: self.perc_pats_in_trace,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField> NdAdvice for DischargeAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> ComponentAdvice<F> for DischargeAdvAdvice<F>{
	fn get_container(&self)->Rc<RefCell<Container<F>>>{
		self.stmt_container.clone()
	}
}

impl <F: PrimeField> DischargeAdvAdvice<F>{
	/// Given the <pats,locs> from the fsm_adv gadget (note it is padded
	/// to perc_pat_per_trace * max_nibblelen/100), generate
	/// the StepQueue of all related subsigs (NOTE: subsigs are provided
	/// as non-deterministic advice)
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		pat_loc: &Rc<RefCell<Container<F>>>,
		inp_subsigs: &Vec<F>,
		fsm_id: u32,
		subsig_store_info: &SubsigStepStore,
		capacity: &DischargeAdvCapacity, 
		inp_step_queue: &StepQueue<F>, // the steps_queue from input
	) ->Self{
		let sname = if b_igc {"discharge_adv_stmt_igc"} else 
			{"discharge_adv_stmt_cs"};
		let stmt_container = Container::<F>::new(sname);
		//1. constructure step_store. DEPRECATED. no need anymore
		//as we have info encoded in lkup table StoreSteps.

		//2. construct 1st (forward) step-queue
		let (forward_step_queue, sq_fwd) = Self::gen_forward_steps_queue_combo(
			b_igc, offset_fsm,
			&inp_subsigs, pat_loc, inp_step_queue, fsm_id, &capacity,
			subsig_store_info);
		let ct_fwd_sq = forward_step_queue.borrow().get_container("sq_res")
			.expect("cannot find sq_res");
		stmt_container.borrow_mut().add_container(forward_step_queue);


		//3. construct 2nd (backward) step-queue
		let backward_step_queue = Self::gen_backward_steps_queue_combo(
			&sq_fwd, &ct_fwd_sq, capacity, subsig_store_info);
		stmt_container.borrow_mut().add_container(backward_step_queue);

		Self{capacity: Clone::clone(capacity), fsm_id,
			stmt_container, b_igc, offset_fsm}
	}


	/// mainly used for initializing input. 
	/// Generate an steps_queue (serialized) based on the inp_subsig.
	/// For each subsig, generate an empty StepQueue which does not
	/// have ANY steps (because it's empty).
	pub fn gen_empty_steps_queue_serialized(
		inp_subsigs: &Vec<F>,
		_store_steps: &SubsigStepStore, //not used anymore
		_fsm_id: u32,
		capacity: &DischargeAdvCapacity
	)->StepQueue<F>{
		/*
		//1. generate store_combo get the REAL entries only
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (_zero,_one,_max) = (F::zero(), F::one(), F::from(max_val as u32));
		let store_combo = Self::gen_store_steps_combo(inp_subsigs,
			store_steps, fsm_id, capacity);
		let col_names = vec!["subsig", "id", "pat", "rg_start", "rg_end", 
			"encoded"];
		let cols = col_names.iter().map(|n|
			store_combo.borrow().get_container(n).unwrap().borrow().to_vec())
			.collect::<Vec<Vec<F>>>();
		let n = cols[0].len();
		for i in 0..cols.len(){assert!(cols[i].len()==n);}
		
		//2. generate StepQueueItem
		let items = (0..n).collect::<Vec<_>>().into_par_iter().map(|i|{
			let (subsig, step, pat, rg_start, rg_end, encoded) = 
				(cols[0][i], cols[1][i], cols[2][i], cols[3][i], cols[4][i],
					cols[5][i]);
			let locs = if step.is_zero() && !subsig.is_zero() {vec![F::one()]} else {vec![]};
			let item =  StepQueueItem{encoded, locs, subsig, step, pat, rg_start, rg_end};

			(subsig, step, item)
		}).collect::<Vec<(F,F,StepQueueItem<F>)>>();

		//3. map/reduce to generate the StepQueue
		let hs = items.into_par_iter()
		.filter(|(k,_,_)| !k.is_zero())
		.fold( || HashMap::<F,Vec<(F,StepQueueItem<F>)>>::new(),
		  |mut acc, (subsig, step, item)|{
		  	let mut to_add = vec![(step, item)];
		  	acc.entry(subsig).or_insert(vec![]).append(&mut to_add);
			acc
		  })
		.reduce(|| HashMap::<F,Vec<(F,StepQueueItem<F>)>>::new(),
		  |mut acc1, acc2|{
			for (k, mut vec) in acc2{
				let mut vec1 = if acc1.contains_key(&k) 
					{acc1.get(&k).unwrap().clone()} else {vec![]};
				vec1.append(&mut vec);
				acc1.insert(k, vec1);
			}
			acc1
		  }
		);

		//4. process each key
		let mut subsigs = hs.keys().map(|x| *x).collect::<Vec<F>>();
		subsigs.sort();
		let store_items = subsigs.par_iter().map(|subsig|{
			let tuples = hs.get(subsig).unwrap();
			let mut res = vec![tuples[0].1.clone(); tuples.len()];
			for i in 0..tuples.len(){
				let (step, item) = &tuples[i];
				let idx = field_to_usize(step);
				res[idx] = item.clone();
			}
			(*subsig, res)
		}).collect::<HashMap<F, Vec<StepQueueItem<F>>>>();

		let res = StepQueue::new(subsigs, store_items, &capacity);

		res
		*/
		let mut subsigs = inp_subsigs.clone();
		subsigs.sort();
		let zero = F::zero();
		let store_items = subsigs.par_iter().map(|&subsig|{
			//create a default step-0 item. note that rg_start, rg_end
			//does not apply as it has no previous step.
			let (step, pat, rg_start, rg_end) = (zero,zero,zero,zero);
			let encoded = encode_cols(&vec![vec![subsig], vec![step], 
				vec![pat], vec![rg_start], vec![rg_end]], &vec![0,1,2,3,4])[0];
			let locs = vec![F::one()];
			let item =  StepQueueItem{encoded, locs, 
				subsig, step, pat, rg_start, rg_end};
			(subsig, vec![item]) //empty StepQueueItems for each
		}).collect::<HashMap<F,Vec<StepQueueItem<F>>>>();

		StepQueue::new(subsigs, store_items, &capacity, StepQueueType::Res)
	}

	/// retrieve the steps_queue from input
	pub fn get_output_steps_queue(&self)->Vec<F>{
		let sname = if self.b_igc {"discharge_adv_stmt_igc"} 
			else {"discharge_adv_stmt_cs"};
		let res = self.stmt_container.borrow().search_container(
			&format!("{} bwd_steps_queue sq_res2", sname)).unwrap();
		let encoded = res.borrow().get_container("encoded").unwrap().
			borrow().to_vec();
		let locs = res.borrow().get_container("locs").unwrap().
			borrow().to_vec();
		vec![encoded, locs].concat()
	}

	/// prove that q1 union q2 -> q3
	#[allow(dead_code)]
	fn gen_step_queue_union_prf(
		prf_name: &str,
		q1: &Rc<RefCell<Container<F>>>,
		q2: &Rc<RefCell<Container<F>>>,
		q3: &Rc<RefCell<Container<F>>>,
	)->Rc<RefCell<Container<F>>>{
		let prf = Container::new(prf_name);		
		let e1=q1.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c1=q1.borrow().get_container("locs").unwrap().borrow().to_vec(); 
		let e2=q2.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c2=q2.borrow().get_container("locs").unwrap().borrow().to_vec(); 
		let e12 = vec![e1,e2].concat();
		let c12 = vec![c1,c2].concat();
		let e3=q3.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c3=q3.borrow().get_container("locs").unwrap().borrow().to_vec(); 

		let src = encode_cols(&vec![e12,c12], &vec![0,1]);
		let dst = encode_cols(&vec![e3,c3], &vec![0,1]);

		let mtb1 = gen_m_table(&src, &dst);
		let mtb2 = gen_m_table(&dst, &src);
		let (len1,len2) = (mtb1.len(), mtb2.len());
		let frg = F::from(RANGE2);
		prf.borrow_mut().add_col(Col::new(mtb1, "mtb1", IDX_DATA));
		prf.borrow_mut().add_col(Col::new(mtb2, "mtb2", IDX_DATA));
		prf.borrow_mut().add_col(Col::new(vec![frg; len1], 
			"sid_mtb1", IDX_SI_DATA));
		prf.borrow_mut().add_col(Col::new(vec![frg; len2], 
			"sid_mtb2", IDX_SI_DATA));

		prf
	}

	/// prove that the queue_step to_add covers the entries 
	/// listed by the fwd_prf
	#[allow(dead_code)]
	fn gen_to_add_valid_prf(
		prf_name: &str,
		sq_to_add: &Rc<RefCell<Container<F>>>,
		prf_fwd: &Rc<RefCell<Container<F>>>,
	)->Rc<RefCell<Container<F>>>{
		//1. retrieve info from to_add
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		let e2=sq_to_add.borrow().get_container("encoded")
			.unwrap().borrow().to_vec(); 
		let c2=sq_to_add.borrow().get_container("locs").unwrap()
			.borrow().to_vec(); 
		let s2=sq_to_add.borrow().get_container("step")
			.unwrap().borrow().to_vec(); 
		assert!(e2.len()==c2.len() && s2.len()==c2.len());
		let dst = encode_cols(&vec![e2.clone(),c2.clone()], 
			&vec![0,1]);
		let dst_sel = e2.iter().map(|encoded|
			if encoded.is_zero() {zero} else {one}
		).collect::<Vec<F>>();
		let dst_adj = dst.par_iter().zip(dst_sel.par_iter()).map(|(x,y)|
			*x**y).collect::<Vec<F>>();

		//2. retrieve info from prf_forward:
		// encoded, loc (note that encoded has the info of step and pat)
		// ignore the dummy entries at the beginning for each
		let e1=prf_fwd.borrow().get_container("dst_encoded")
			.unwrap().borrow().to_vec(); 
		let c1=prf_fwd.borrow().get_container("dst_loc").unwrap()
			.borrow().to_vec(); 
		let c3=prf_fwd.borrow().get_container("src_loc").unwrap()
			.borrow().to_vec(); 
		assert!(e1.len()==c1.len());
		let src = encode_cols(&vec![e1.clone(),c1.clone()], &vec![0,1]);
		let src_sel = (0..e1.len()).into_par_iter().map(|i|{
			if i==0 || i==e1.len()-1{zero}
			//ignore boundary entries.
			//on boundary if (dst_encoded[i],src_loc[i]) is DIFFERENT
			//from preivous or next entry
			else {
				let res = if ((e1[i]!=e1[i-1]) || (c3[i]!=c3[i-1])) ||
					((e1[i+1]!=e1[i]) || (c3[i+1]!=c3[i])) {zero} 
				else {one};

				res
			}
		}).collect::<Vec<F>>();
		let src_adj = src.par_iter().zip(src_sel.par_iter()).map(|(x,y)|
			*x**y).collect::<Vec<F>>();


		//3. build hte m_tbl needed for 2-direction lookup
		let prf = Container::new(prf_name);		
		let frg = F::from(RANGE2);
		let mtb1 = gen_m_table(&src_adj, &dst_adj);
		let mtb2 = gen_m_table(&dst_adj, &src_adj);
		let len1 = mtb1.len();
		let len2 = mtb2.len();
		prf.borrow_mut().add_col(Col::new(mtb1, "mtb1", IDX_DATA));
		prf.borrow_mut().add_col(Col::new(vec![frg;len1], "sid_mtb1", 
			IDX_SI_DATA));
		prf.borrow_mut().add_col(Col::new(mtb2, "mtb2", IDX_DATA));
		prf.borrow_mut().add_col(Col::new(vec![frg;len2], "sid_mtb2", 
			IDX_SI_DATA));

		prf
	}

	/// prove the validity of prf_fwd. Note that the structure
	/// is already implied by the reasoning of union of inp_queue and to_add,
	/// and to_add with step_store. So we do not have to prove that
	/// prf_fwd has the structure of step_store. We reason mainly
	/// about how thd diff1/diff2 are computed correctly, and the query
	/// of range result is consistent with pat_loc (using the trick of
	/// argueing about its ascending order, and the relation of begin/end
	/// wrapping entries with the query).
	#[allow(dead_code)]
	fn gen_fwdprf_valid_prf(
		prf_name: &str,
		prf_fwd: &Rc<RefCell<Container<F>>>,
		pat_loc: &Rc<RefCell<Container<F>>>,
		sq_res: &Rc<RefCell<Container<F>>>,
		capacity: &DischargeAdvCapacity,
	)->Rc<RefCell<Container<F>>>{
		//0. data retrieval
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let res = Container::new(prf_name);
		let names = vec!["src_encoded", "dst_encoded", 
			"src_loc", "src_step", 
			"dst_pat", "dst_rg_start", "dst_rg_end",
			"dst_loc", "dst_pat_id", "diff1", "diff2", "dst_subsig"];
		let v2d= names.iter().map(|n|{
			prf_fwd.borrow().get_container(n).unwrap().borrow().to_vec() 
		}).collect::<Vec<Vec<F>>>();
		let (src_encoded, _dst_encoded,
			src_loc, _src_step, 
			dst_pat, _dst_rg_start, dst_rg_end,
			dst_loc, dst_pat_id, _diff1, _diff2, 
			_dst_subsig) = (&v2d[0], &v2d[1],
				&v2d[2], &v2d[3], 
				&v2d[4], &v2d[5], &v2d[6],
				&v2d[7], &v2d[8], &v2d[9], &v2d[10], 
				&v2d[11]);
		let frg = F::from(RANGE2);


		//1. correctness of src_encoded (here we generate
		// the m-table to bind the src_encoded with src_step
		// DEPRECATED - this step is no longer needed as we add
		// additional tables in StepStore so that each step can now
		// just be tagged with the corresponding table_id for the encoded.
		// check is done now in SID check.

		//2. correctness of dst_encoded (no proof needed)
		//DEPRECATED - longer needed as new SID table check done the job.

		//3. lookup pat-loc in pat_loc. Note that the raw algorithm
		// can easily suffer from an attack. See example below:
		//   in the original discharging proof, we ignore "dummy"
		//   entries of location of 0 and max the reason is that
		//   there might be locations not appearing in pat-loc table
		//   at all. In this case, two dummy entries are provided
		//   for the forwardprf reasoning. However, an adversary
		//   can also provide two dummy entries (for locations which
		//    have real entries in query range) - this allows adversary
		//    to skip locations that are "required" to appear for the
		//    next step.
		//
		//    In this case, we prove the correct before. The "lookup table"
		//    should actually consists of two parts: (1) the pat-loc table
		//    and (2) a dummy lookup table for those pats that do NOT appear
		//    in the trace. 
		//        First, note that the 2nd dummy no-show lkup table has
		//    size UP TO the number of subsigs. The reason is that for each
		//    subsig, the "no show" pattern can ONLY APPEAR in the very
		//    last step of the on-going step queue. Thus, for each subsig,
		//    there can be UP TO one such "no show" pattern. Given that
		//    for each pattern we need to provide 2 dummy entries (simulating
		//    the pat-loc table), the size of this second dummy lkup table
		//    is 2*num_of_subsigs to discharge.
		//        In average, there are 5 steps per subsig. Thus, the
		//    needed 2nd fake talbe is only 1/5 of the size of pat-loc table
		//    or even smaller.
		//         Then we need to provide the following proof.
		//    Note that pat-loc is already proved to be sorted over its key 
		//		(pat) in fsm_adv.rs.
		//    (1) for each no-show pat show two neigboring elements in
		//        the pat-loc table (id, p1, p2) such that
		//          e1 < no-showpat <= p2
		//        this is essentially to show the difference are in range.
		//    (2) show the (p1,p2) are NEIGHBORING pairs are in pat-loc table.
		//    (3) perform the "query-range" of the dst_loc in the the
		//       combined lookup talbe (pat-loc || dummy-pat-loc)
		//    Cost analysis:  let n be the pat-loc size, s be the # of subsigs
		//		   (1) reason about 2 diff in range: 2s
		//         (2) compute pair columns and lkup: s + n + 
		//				2*s + 3*n =3s + 4n
		//         (3) query-range: 2s + 2(s+n) + 2n + 3(2s+n)
		//				 -> 10s + 10n
		//         Total: 12n + 7s (usually n>>s, so it's like 13n) for step 3
		

		//3.1 build up the a table of size 2*num_subsigs of the following 
		//structure: note that every nsp has 2 entries (min_loc, max_loc)
		//  (nsp, nsp_p1, p2_nsp)
		//  nsp: no_show_pat
		//  no_show patterns are collected from the fwd prf.
		// p1 and p2 are two neighboring patterns in pat-loc such that
		//   p1 < nsp < p2 (which proves that nsp didn't show in pat loc)
		// NOTE: in the corner cases p1 = 0, and p2 = max.
		// To save space: we do not store p1 and p2 as two separate columns,
		// but save the two differences (and later use SID to prove that 
		//    they are valid positive numbers).
		// the relation is defined as:
		//   nsp_p1 = nsp - 1 -p1 (>=0), implies nsp>p1
		//   p2_nsp = p2 -1 - nsp (>=0), implies p2>nsp
		// then we can compute p1 and p2 as follows
		// compute p1 = nsp - 1 - nsp_p1
		// compute p2 = nsp + 1 + p2_nsp 
		// we can do dynamic logup to prove that (p1,p2) are neighboring
		// entries of pat-loc table.
		let pat= pat_loc.borrow().get_container("sorted_key")
			.unwrap().borrow().to_vec();
		#[cfg(test)]{ 
			assert!(is_sorted(&pat)); 
			assert!(pat[0].is_zero(), "pat has no padding zero at beginning!");
		}
		let pat_id= pat_loc.borrow().get_container("sorted_id")
			.unwrap().borrow().to_vec();
		let loc = pat_loc.borrow().get_container("sorted_val")
			.unwrap().borrow().to_vec();
		let set_pat_in_trace = pat.iter().filter(|p| !p.is_zero())
			.map(|&p| p).collect::<HashSet<F>>();
		let set_dst_pat = dst_pat.iter().filter(|p| !p.is_zero())
			.map(|&p| p).collect::<HashSet<F>>();
		let mut vec_nsp = set_dst_pat.difference(&set_pat_in_trace)
			.map(|&p| p).collect::<Vec<F>>();
		vec_nsp.sort();
		let n_s = capacity.subsigs;
		vec_nsp = [vec![zero; n_s - vec_nsp.len()], vec_nsp].concat(); 
		let vec_tuples = vec_nsp.par_iter().map(|&nsp|{
			if nsp.is_zero(){
				(zero, zero, zero)
			}else{
				let res = pat.binary_search(&nsp);
				let idx_err = match res{
					Ok(_) => panic!("nsp: {} still in pat-loc!", nsp),
					Err(idx) => idx
				};
				let p1 = if idx_err==0 {zero} else {pat[idx_err-1]};
				let p2 = if idx_err==pat.len() {max} else {pat[idx_err]};
				assert!(p1<nsp && nsp<p2);
				let nsp_p1 = nsp - p1 - one;
				let p2_nsp = p2 - one - nsp;
				assert!(nsp_p1<=max && p2_nsp<=max);
				(nsp, nsp_p1, p2_nsp)
			}
		}).collect::<Vec<(F,F,F)>>();
		assert!(vec_tuples.len() == n_s);
		let nsp = vec_tuples.iter().map(|t| t.0).collect::<Vec<F>>();
		let nsp_p1 = vec_tuples.iter().map(|t| t.1).collect::<Vec<F>>();
		let p2_nsp = vec_tuples.iter().map(|t| t.2).collect::<Vec<F>>();

		//3.2 prove that p1 and p2 are valid pairs in pat_loc
		let p1_p2= nsp.iter().zip(nsp_p1.iter().zip(p2_nsp.iter()))
			.map(|(&nsp,(&nsp_p1,&p2_nsp))|{
			let p1 = nsp - one - nsp_p1;
			let p2 = nsp + one + p2_nsp;
			encode_2col(&[p1], &[p2])[0]
		}).collect::<Vec<F>>();
		let all_pairs = (0..pat.len()-1).into_iter().map(|i|
			encode_2col(&[pat[i]], &[pat[i+1]])[0] ).collect::<Vec<F>>();
		let all_pairs = [//add two dummy cols for 0 and max
			encode_2col(&[zero-one, pat[pat.len()-1]], &[one, max]),
			all_pairs
		].concat();
		let m_tbl_pairs = gen_m_table(&p1_p2, &all_pairs);
		let sid_m_tbl_pairs = vec![frg; m_tbl_pairs.len()];
			

		//3.3. now prove that (dst_loc, dst_pat_id, dst_loc)
		//are valid (they can be found in the concat of
		//    pat-loc table  || now_show_loc table

		let src_combined = encode_cols(
			&vec![dst_pat.clone(), dst_pat_id.clone(), dst_loc.clone()], 
			&vec![0,1,2]);	

		let dst_combined_1 = encode_cols(&vec![pat, pat_id, loc], &vec![0,1,2]);
		let dst_combined_2 = nsp.iter().map(|nsp|{
			//each no show location has two entries
			encode_cols(
				&vec![ 
					vec![*nsp, *nsp], //pat
			   		vec![zero, one], //ids
					vec![zero, max], //dummy locs
				], 
				&vec![0,1,2]
			)
		}).flatten().collect::<Vec<F>>();
		let dst_combined = [ dst_combined_1, dst_combined_2 ].concat();

		let mtb_pat = gen_m_table(&src_combined, &dst_combined);
		let len1 = mtb_pat.len();
		res.borrow_mut().add_col(Col::new(mtb_pat, "mtb_pat", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_mtb_pat", IDX_SI_DATA));

		let nsp_names = ["nsp", "nsp_p1", "p2_nsp"];
		let nsp_cols = [nsp, nsp_p1, p2_nsp];
		nsp_cols.into_iter().zip(nsp_names.iter()).for_each(|(c,n)|{
			res.borrow_mut().add_col(Col::new(c, n, IDX_DATA));
			res.borrow_mut().add_col(Col::new(vec![frg; n_s], 
				&format!("sid_{}",n),IDX_SI_DATA));
		});
		res.borrow_mut().add_col(Col::new(m_tbl_pairs,"m_tbl_pairs",IDX_DATA));
		res.borrow_mut().add_col(Col::new(sid_m_tbl_pairs,
				"sid_m_tbl_pairs", IDX_SI_DATA));



		//4. prove encoded-loc corresponds to result_queue (note:
		// where result is inp + to_add. the prf works on the "dynamic"
		// result from last step which includes new entries from to_add).
		let res_encoded= sq_res.borrow().get_container("encoded")
			.unwrap().borrow().to_vec();
		let _res_step= sq_res.borrow().get_container("step")
			.unwrap().borrow().to_vec();
		let res_loc = sq_res.borrow().get_container("locs")
			.unwrap().borrow().to_vec();
		let sid_res_step= sq_res.borrow().get_container("si_step")
			.unwrap().borrow().to_vec();

		let src_combined = encode_cols(&vec![res_encoded.clone(), res_loc.clone()], &vec![0,1]);
		let dst_adj= encode_cols(&vec![src_encoded.to_vec(), src_loc.to_vec()], 
			&vec![0,1]);
		let info_id= F::from(0x23001101u32); //tag to avoid collision
		let f1 = F::from(1u64<<RANGE2_BIT);
        let factor1 = f1*f1*f1*f1*f1; //models encoded
        let factor2 = F::from(1u64<<32); //32-bit
		let part1_alt = info_id*factor1*factor2 + 
			F::from(ID_ENCODED_LAST_STEP)*factor1;
		let src_sel = sid_res_step.iter().zip(res_encoded.iter())
			.map(|(sid_step, encoded)|{
				let final_id = part1_alt + encoded;
				if final_id==*sid_step {zero} else {one}
			}).collect::<Vec<F>>();
		let src_adj = src_combined.iter().zip(src_sel.iter()).map(|(a,b)|
			*a * *b).collect::<Vec<F>>();

		let mtb_res1= gen_m_table(&src_adj, &dst_adj);
		let mtb_res2= gen_m_table(&dst_adj, &src_adj);
		let len1 = mtb_res1.len();
		let len2 = mtb_res2.len();
		res.borrow_mut().add_col(Col::new(mtb_res1, "mtb_res1", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_mtb_res1", IDX_SI_DATA));
		res.borrow_mut().add_col(Col::new(mtb_res2, "mtb_res2", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len2], 
			"sid_mtb_res2", IDX_SI_DATA));

		//5. prove the ascending order of pat_id column (no need
		// for generating additional data, we are proving pat_id
		// increasing by 1. This is needed for range-query validity
		// to show that the returned query result has the right result
		// in the middle.

		//6. prove the validity of diff1/diff2.
		let rg2 = dst_rg_end.par_iter().zip(src_loc.par_iter()).map(|(a,b)|
			*a + *b).collect::<Vec<F>>();
		let abs_rg2_max = rg2.par_iter().map(|rg2|
			if *rg2>=max {*rg2-max} else {max-*rg2}).collect::<Vec<F>>();
		let len1 = abs_rg2_max.len();
		res.borrow_mut().add_col(Col::new(abs_rg2_max, 
			"abs_rg2_max", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1],
			"sid_abs_rg2_max", IDX_SI_DATA));

		res
	}

	/// The 1st of the 2-step streaming algorithm for producing
	/// the steps_queue. The steps_queue describes the locations
	/// of each step for discharging a subsig.
	/// It is a 3-col table <encoded, step, loc>
	/// where encoded is the encoded of step_store entries.
	/// Given: (1) the step_queue in the input buffer, (2) the pat-loc
	/// table, we propagate from each layer to next layer: that is:
	/// given an <encoded, step, loc> entry, and given the correpsonding
	/// range for the next layer, we query the pat-loc table for all the
	/// in-range locations for the next layer (id+1). 
	///
	/// Return: (1) the container of combo, and (2) forward result step queue
	#[allow(dead_code)]
	fn gen_forward_steps_queue_combo(
		b_igc: bool,
		offset_fsm: usize,
		_inp_subsigs: &Vec<F>,
		pat_loc: &Rc<RefCell<Container<F>>>,
		inp_step_queue: &StepQueue<F>, 
		_fsm_id: u32,
		capacity: &DischargeAdvCapacity,
		subsig_store_info: &SubsigStepStore,
	)->(Rc<RefCell<Container<F>>>, StepQueue<F>){
		let b_debug = false;
		let res = Container::<F>::new("fwd_steps_queue");
		//0. Generate the logical data:
		// from inp_step_queue generate the to_add, merged_result, 
		// and the fwd prf. Add them to container
		let (sq_to_add, sq_res, fwd_prf) = inp_step_queue
			.gen_forward_prf(pat_loc, subsig_store_info);
		let sname_fsm = if b_igc {"fsm_adv_stmt_igc"} else {"fsm_adv_stmt_cs"};
		let shift = 0-(offset_fsm as i32);
		println!("-- DEBUG USE 6101: shift: {}", shift);
		let pat_loc = pat_loc.borrow().duplicate_as_external_adv(shift,
			Some(format!("{} packed_trace pat_loc sorted_tbl", sname_fsm)),
			Some("pat_loc".to_string()));
		let ct_pat_loc = Rc::new(RefCell::new(pat_loc));


		if b_debug{
			println!("========== DEBUG USE 202: inp_step_queue: ");
			inp_step_queue.dump();
			println!("========== DEBUG USE 203: to_add: ");
			sq_to_add.dump();
			println!("========== DEBUG USE 204: res: ");
			sq_res.dump();
			println!("========== DEBUG USE 205: fwd_prf: ");
			fwd_prf.dump();
		}

		let ct_sq_inp = inp_step_queue.to_container("sq_inp",true,//inp
			false,  //b_step
			false,  //b_oup
			false,  //b_subsig
			&subsig_store_info);
		let ct_sq_to_add = sq_to_add.to_container("sq_to_add",false,
			true, false, false, &subsig_store_info);
		let ct_sq_res = sq_res.to_container("sq_res", false, 
			true, false, false, &subsig_store_info);
		res.borrow_mut().add_container(ct_sq_inp.clone()); //low cost, rc clone
		res.borrow_mut().add_container(ct_sq_to_add.clone());
		res.borrow_mut().add_container(ct_sq_res.clone());
		res.borrow_mut().add_container(fwd_prf.to_container("prf_fwd", 
			subsig_store_info));
		res.borrow_mut().add_container(ct_pat_loc.clone());

		//------------------------------------------------------------------
		//--- now argue that the generated step_queue and fwd_prf are correct
		//------------------------------------------------------------------
		//1. prove the sq_inp + sq_to_add = sq_res
		let prf = Container::new("prf");
		//1. prove inp_queue + to_add = sq_res
		let prf_union = Self::gen_step_queue_union_prf("prf_union",
			&ct_sq_inp, &ct_sq_to_add, &ct_sq_res);
		prf.borrow_mut().add_container(prf_union);

		//2. prove that sq_inp has the same structure of the store_steps.
		// This part is SKIPPED, as we have the new DB to bind
		// (subsig_id, encoded_word). This can be easily shown by tag
		// it will be done "recursively" for each sq_oup (which
		//  is performed in compute_sig_adv gadget when it's evaluating
		//  each subsig with its step_queue result).
		// initial sq_init is hard set in circ (which is already valid).
		// thus, this step can be skipped.
		// depcrated: Self::gen_sq_inp_valid_prf(..., store_steps)

		//3. prove that sq_to_add is valid (covering all new entries
		// that are produced in fwd proof
		let prf_fwd = res.borrow().get_container("prf_fwd").unwrap(); 
		let prf_to_add_valid = Self::gen_to_add_valid_prf("prf_to_add",
			&ct_sq_to_add, &prf_fwd);
		prf.borrow_mut().add_container(prf_to_add_valid);

		//4. prove the validity of the fwd_prf
		let prf_fwdprf_valid = Self::gen_fwdprf_valid_prf("prf_fwdprf_valid",
			&prf_fwd, &ct_pat_loc, &ct_sq_res, capacity);
		prf.borrow_mut().add_container(prf_fwdprf_valid);

		// --- now return 
		res.borrow_mut().add_container(prf);
		(res, sq_res)
	}

	/// The second of the 2-step streaming algorithm for producing
	/// the steps_queue. The steps "conservatively"
	/// prove the step queue in the senes that if the min_loc
	/// of a step is updated to a greater number, it deletes
	/// locations from the previous layer that could not reach this new loc_mix
	/// via rg_end.
	/// Like the fwd proof, the length the the backward prf does not
	/// necessarily have to cover the total number of steps for a subsignature
	#[allow(dead_code)]
	fn gen_backward_steps_queue_combo(
		input_step_queue: &StepQueue<F>,
		ct_fwd_res: &Rc<RefCell<Container<F>>>,
		_capacity: &DischargeAdvCapacity,
		subsig_store_info: &SubsigStepStore,
	)->Rc<RefCell<Container<F>>>{
		//0. Generate the logical data:
		// from inp_step_queue generate the to_del, res, bwd_prf, 
		// Add them to container
		let res = Container::<F>::new("bwd_steps_queue");
		let b_debug = false;
		let (sq_to_del, sq_res, bwd_prf) = input_step_queue.gen_backward_prf();

		if b_debug{
			println!("========== DEBUG USE 301: inp_step_queue (fwd_res): ");
			input_step_queue.dump();
			println!("========== DEBUG USE 302: to_del: ");
			sq_to_del.dump();
			println!("========== DEBUG USE 303: res: ");
			sq_res.dump();
			println!("========== DEBUG USE 304: backward_prf: ");
			bwd_prf.dump();
		}

		let ct_sq_to_del= sq_to_del.to_container("sq_to_del",false,true,false,false,
			&subsig_store_info);
		let ct_sq_res2 = sq_res.to_container("sq_res2",
			false,//inp
			true, //b_step (but it's saved in DATA)
			true, //oup
			true, //b_subsigs (saved in DATA)
			&subsig_store_info);
		res.borrow_mut().add_container(ct_sq_to_del.clone());
		res.borrow_mut().add_container(ct_sq_res2.clone());
		res.borrow_mut().add_container(bwd_prf.to_container("prf_bwd", 
			subsig_store_info));


		//------------------------------------------------------------------
		//--- now argue that the generated step_queue and fwd_prf are correct
		//------------------------------------------------------------------
		//1. prove the sq_to_del + sq_res2 = sq_res
		let prf = Container::new("prf");
		let prf_union = Self::gen_step_queue_union_prf("prf_union",
			&ct_sq_res2, &ct_sq_to_del, &ct_fwd_res);
		prf.borrow_mut().add_container(prf_union);

		//2. no need to argume for the sq_inp conforms to store_steps
		//as we are working on existing fwd prfs

		//3. prove that sq_to_del is valid (covering all new entries
		// that are produced in bwd proof
		let prf_bwd = res.borrow().get_container("prf_bwd").unwrap(); 
		let prf_to_del_valid = Self::gen_to_del_valid_prf("prf_to_del",
			&ct_sq_to_del, &prf_bwd);
		prf.borrow_mut().add_container(prf_to_del_valid);

		//4. prove the validity of the bwd_prf
		let prf_bwdprf_valid = Self::gen_bwdprf_valid_prf("prf_bwdprf_valid",
			&prf_bwd, &ct_sq_res2);
		prf.borrow_mut().add_container(prf_bwdprf_valid);

		// --- now return 
		res.borrow_mut().add_container(prf);
		res
	}

	/// prove that the to_del covers the entries prf_bwd
	/// This is very similar to the to_add prf except the
	/// boundary condtion (sel) is generated slightly different.
	#[allow(dead_code)]
	fn gen_to_del_valid_prf(
		prf_name: &str,
		sq_to_del: &Rc<RefCell<Container<F>>>,
		prf_bwd: &Rc<RefCell<Container<F>>>,
	)->Rc<RefCell<Container<F>>>{
		//1. retrieve info from to_add
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, _one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		let e2=sq_to_del.borrow().get_container("encoded")
			.unwrap().borrow().to_vec(); 
		let c2=sq_to_del.borrow().get_container("locs").unwrap()
			.borrow().to_vec(); 
		assert!(e2.len()==c2.len());
		let dst = encode_cols(&vec![e2.clone(),c2.clone()], 
			&vec![0,1]);

		//2. retrieve info from prf_bwd:
		// unlike the to_add_prf which has multiple src locs leading
		// to dst loc problem, here all are from src_min_loc. So
		// the logic can be simplified here.
		// note that no need for selector as encoded=0 have all 0 entries
		// and bwd_prf does not have boundary entries for sorting needs
		// (which was used in range-query in fwd prf but not needed here)
		let e1=prf_bwd.borrow().get_container("prev_encoded")
			.unwrap().borrow().to_vec(); 
		let c1=prf_bwd.borrow().get_container("loc_to_del").unwrap()
			.borrow().to_vec(); 
		assert!(e1.len()==c1.len());
		assert!(e1[0]==zero, "increase length to ensure at least one pad 0");

		let src = encode_cols(&vec![e1.clone(),c1.clone()], &vec![0,1]);


		//3. build the m_tbl needed for 1-direction is OK as
		// deletion is "conservative". If the prover only
		// includes a "subset" of the to_remove list, it's not going
		// to cause problem (only cost more).
		// the direction is to look for those in to_del in the prf_bwd
		let prf = Container::new(prf_name);		
		let frg = F::from(RANGE2);
		let mtb2 = gen_m_table(&dst, &src); //note: we lkup up dst
													//in src_adj
		let len1 = mtb2.len();
		prf.borrow_mut().add_col(Col::new(mtb2, "mtb2", IDX_DATA));
		prf.borrow_mut().add_col(Col::new(vec![frg;len1], "sid_mtb2", 
			IDX_SI_DATA));

		prf
	}

	/// prove the validity of prf_bwd. Mainly it shows that
	/// (1) validity of min_loc (take the 1st 
	///    loc from the sq_res and show that sq_res loc is sorted
	///    This needs that we prove that sq_res is sorted in ascending
	///     order in its encoded key. As encoded is the encoding of
	///     (subsig, step, ....). It implies it's also sorted by subsig.
	/// (2) prev_loc + rg2 < min_loc (which invlidates the prev_loc),
	///    so that there in the future ll be no subsequent loc for
	///    prev_loc
	#[allow(dead_code)]
	fn gen_bwdprf_valid_prf(
		prf_name: &str,
		prf_bwd: &Rc<RefCell<Container<F>>>,
		sq_res: &Rc<RefCell<Container<F>>>,
	)->Rc<RefCell<Container<F>>>{
		//0. data retrieval
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, _max) = (F::zero(), F::one(), F::from(max_val as u32));
		let res = Container::new(prf_name);
		let names = vec![
			"src_encoded", "src_step", 
			"src_pat", "src_min_loc", "src_rg_end",
			"prev_encoded", "loc_to_del"
		];
		let v2d= names.iter().map(|n|{
			prf_bwd.borrow().get_container(n).unwrap().borrow().to_vec() 
		}).collect::<Vec<Vec<F>>>();
		let (
			_src_encoded, _src_step,
			_src_pat, src_min_loc, src_rg_end,
			_prev_encoded, loc_to_del)
		= (
			&v2d[0], &v2d[1], 
			&v2d[2], &v2d[3], &v2d[4],
			&v2d[5], &v2d[6]
		);
		let frg = F::from(RANGE2);

		//1. DEPRECATED.
		// correctness of src_encoded-step-rg_end (we are not interested
		// in other attributes). Prove that they belong to store_steps.
		// -- this is no longer needed as the tab of sub-tbl ID proves
		// what is needed (see StepBwdPrf::to_container() and validate_bwdprf_valid_prf step 1).

		//2. DEPCRECATED - 
		// correctness of prev_encoded (i.e., previous step of src_encoded)
		// this is no longer as needed as subtbl_id of
		// ID_ENCODED_PREV_ENCODED does the trick.

		//3. prove (final) sq_res has its loc sorted (for each subsig-step)
		// This is NEEDED because we need to argue about the 
		// minimum loc for a step.
		// We need to prove that subsig-step itself is sorted first.
		let rescols = vec!["encoded", "step", "locs", "subsig"].iter().map(|n|
			sq_res.borrow().get_container(n).unwrap().borrow().to_vec()
		).collect::<Vec<Vec<F>>>();
		#[cfg(test)]{ assert!(is_sorted(&rescols[0])); }

		//3.1 prove that subsig is sorted
		let diff_subsig = (0..rescols[3].len()-1).into_par_iter().map(|i|{
			rescols[3][i+1] - rescols[3][i] 
		}).collect::<Vec<F>>();
		let len2 = diff_subsig.len();
		#[cfg(test)]{ check_rg2(&diff_subsig, &vec![frg;diff_subsig.len()]); }
		res.borrow_mut().add_col(Col::new(diff_subsig, "diff_subsig", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len2], 
			"sid_diff_subsig", IDX_SI_DATA));

		//3.2 prove that step is sorted per subsig
		let sel = (0..rescols[3].len()).into_par_iter().map(|i|{
			if i==0 {zero} else{
				if rescols[3][i]!=rescols[3][i-1] {zero} else {one}
			}
		}).collect::<Vec<F>>();
		let diff_step = (0..rescols[1].len()).into_par_iter().map(|i|{
			if i==0 {zero} else {
				(rescols[1][i] - rescols[1][i-1]) * sel[i]
			}
		}).collect::<Vec<F>>();
		let len1 = diff_step.len();
		#[cfg(test)]{ check_rg2(&diff_step, &vec![frg;diff_step.len()]); }
		res.borrow_mut().add_col(Col::new(diff_step, "diff_step", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_diff_step", IDX_SI_DATA));

		//3.3 prove that loc is sorted per subsig-step (encoded)
		let sel = (0..rescols[0].len()).into_par_iter().map(|i|{
			if i==0 {zero} else{
				if rescols[0][i]!=rescols[0][i-1] {zero} else {one}
			}
		}).collect::<Vec<F>>();
		let diff_loc = (0..rescols[0].len()).into_par_iter().map(|i|{
			if i==0 {zero} else {
				(rescols[2][i] - rescols[2][i-1]) * sel[i]
			}
		}).collect::<Vec<F>>();
		let len1 = diff_loc.len();
		#[cfg(test)]{ check_rg2(&diff_loc, &vec![frg;diff_loc.len()]); }
		res.borrow_mut().add_col(Col::new(diff_loc, "diff_loc", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_diff_loc", IDX_SI_DATA));


		
		//4. prove the min_loc is the first loc in sq_res
		// it's basically a lkup.
		// src_combined: encoded-step-min_loc
		// dst_combined: encoded-step-loc and selected by if it
		//    is the very first effective entry of each encoded-step
		//    (relying on the fact that the table
		//    is sorted in encoded, thus (subsig-step)). 
		let src_combined= encode_cols(&v2d, &vec![0,1,3]);
		let dst_combined = encode_cols(&rescols, &vec![0,1,2]);
		let dst_sel = (0..dst_combined.len()).into_par_iter().map(|i|{
			if i==0 {//we assume there is at least one dummy entry at begin
				assert!(rescols[0][0].is_zero(), "needs at least 1 dummy");
				zero
			}else{	//encoded not equal to previous 
					//(assumption tbl already sorted) which is proved earlier
				if rescols[0][i-1] != rescols[0][i] {one} else {zero}
			}
		}).collect::<Vec<F>>();
		let dst_adj = dst_combined.par_iter().zip(dst_sel.par_iter())
			.map(|(&x,&y)| x*y).collect::<Vec<F>>();
		let mtb_src = gen_m_table(&src_combined, &dst_adj);
		let len1 = mtb_src.len();
		res.borrow_mut().add_col(Col::new(mtb_src, "mtb_min_loc", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_mtb_min_loc", IDX_SI_DATA));

		//5. prove min_loc > (loc_to_remove + rg_2) 
		let sel = (0..src_rg_end.len()).into_par_iter().map(|i|
			if src_min_loc[i].is_zero() {zero} else {one}
		).collect::<Vec<F>>();
		let diff_min = (0..src_rg_end.len()).into_par_iter().map(|i|
			sel[i]*(src_min_loc[i] - (loc_to_del[i] + src_rg_end[i] + one))
		).collect::<Vec<F>>();
		let len1 = sel.len();
		res.borrow_mut().add_col(Col::new(diff_min, "diff_min", IDX_DATA));
		res.borrow_mut().add_col(Col::new(vec![frg;len1], 
			"sid_diff_min", IDX_SI_DATA));

		res
	}


}

impl <F:PrimeField> DischargeAdvGadget<F>{
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		capacity: &DischargeAdvCapacity,
		fsm_id: u32, 
		prev_cfgs: &Vec<ContainerConfig>,
		store_steps: &SubsigStepStore,
		)
	-> Self{
		//1. create the dummy input and dummy container config.
		let pats_len = capacity.get_pat_loc_len();
		let zero = F::zero();	
		let pats = vec![zero; pats_len];
		let ids = vec![zero; pats_len];
		let locs = vec![zero; pats_len];
		let pat_loc = Container::<F>::new("pat_loc");
		pat_loc.borrow_mut()
			.add_col(Col::<F>::new(pats, "sorted_key", IDX_DATA));
		pat_loc.borrow_mut()
			.add_col(Col::<F>::new(ids, "sorted_id", IDX_DATA));
		pat_loc.borrow_mut()
			.add_col(Col::<F>::new(locs, "sorted_val", IDX_DATA));
		let sigs = vec![zero; capacity.subsigs];
		let step_q_size = StepQueue::<F>::vec_size(&StepQueueType::Res,
			capacity);
		let inp_steps_queue = vec![zero; step_q_size*2];
		let inp_steps_queue_obj = StepQueue::parse_from(&inp_steps_queue,
			capacity);
		let dummy_adv = DischargeAdvAdvice::new(b_igc, offset_fsm,
			&pat_loc, &sigs, fsm_id, store_steps, 
			Clone::clone(&capacity), &inp_steps_queue_obj);
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.borrow().get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[vec_cfg.len()-1].clone(); //it's the last one

		Self{_f: PhantomData, capacity: Clone::clone(capacity), 
			cfgs_context: None,
			my_idx_in_context: None, dummy_cfg, fsm_id,
			b_igc, offset_fsm}
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
	#[allow(dead_code)]
	fn validate_store_steps_combo(&self, 
		store_steps: &Container<FpVar<F>>, 
		r1: FpVar<F>,
		cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//1. check all subtable IDs are correct.
		// This includes the check that the encoded column is
		// indeed in the external lookup table.
		let col_names = vec!["subsig", "id", "pat", "rg_start", "rg_end", 
			"encoded", "inp_subsigs", "m_tbl"];
		let f_substore_id = F::from((self.fsm_id + STORE_SUBSIG_STEP) as u32);
		let f_range2 = F::from(RANGE2 as u32);
		let vals = vec![f_range2, f_range2, f_range2, f_range2, f_range2,
			f_substore_id, f_range2, f_range2].iter().map(|f|
				FpVar::new_constant(cs.clone(), f).unwrap())
			.collect::<Vec<_>>();
		let sid_cols = col_names.iter().map(|name|
			store_steps.get_container(&format!("sid_{}", name)).unwrap()
				.borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		assert!(sid_cols.len()==vals.len());

		for i in 0..vals.len(){
			check_arr_eq(&sid_cols[i], &vals[i], 
				&format!("err check sid of {}", col_names[i]))?;
		}
		//2. check the m_tbl proof
		let cols = col_names.iter().map(|name| store_steps.get_container(&name).
			unwrap().borrow().to_vec()
			).collect::<Vec<Vec<FpVar<F>>>>();
		let (subsig, id, pat, rg_start, rg_end, encoded, inp_subsigs, m_tbl) = 
		  (&cols[0],&cols[1],&cols[2],&cols[3],&cols[4],&cols[5],&cols[6],&cols[7]);
		assert_logup(cs.clone(), &inp_subsigs, &subsig, &m_tbl, &r1)?; 

		//3. check the validity of encoding
		let unit_bits = RANGE2_BIT;
		verify_encoded_table(cs.clone(),
			unit_bits, &vec![subsig,id,pat,rg_start,rg_end], encoded)?;

		//4. check the table is wellformed 
		//note: no sorted proof is needed as it's proved to be part of
		//external table, thus guarantee completeness of vals for a key.
		assert_well_formed_sorted(cs.clone(),subsig,id,pat,None,None,None,
			None, r1,unit_bits)?;


		Ok( () )
	}

	/// validate forward_step_queue combo (info and prf) are valid
	/// This corresponds to the gen_forward_steps_queue_combo
	#[allow(dead_code)]
	fn validate_forward_step_queue(&self, 
		forward_step_q: &Container<FpVar<F>>, 
		r1: FpVar<F>,
		r2: FpVar<F>,
		_cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//0. retrieve the data
		let ct_sq_inp = forward_step_q.get_container("sq_inp")?;
		let ct_sq_to_add = forward_step_q.get_container("sq_to_add")?;
		let ct_sq_res = forward_step_q.get_container("sq_res")?;
		let ct_prf_fwd = forward_step_q.get_container("prf_fwd")?;
		let ct_pat_loc = forward_step_q.get_container("pat_loc")?;//external
		

		//1. verify sq_inp + sq_to_add = sq_res
		let prf = forward_step_q.get_container("prf")?;
		let prf_union = prf.borrow().get_container("prf_union")?;
		self.validate_step_queue_union_prf(&ct_sq_inp, &ct_sq_to_add,
			&ct_sq_res, &r1, &r2, &prf_union)?;

		//2. validate sq_inp covers the structure required by step_store.
		// This part is SKIPPED, as we have the new DB to bind
		// (subsig_id, encoded_word). This can be easily shown by tag
		// it will be done "recursively" for each sq_oup (which
		//  is performed in compute_sig_adv gadget when it's evaluating
		//  each subsig with its step_queue result).
		// initial sq_init is hard set in circ (which is already valid).
		// thus, this step can be skipped.
		// Deprecated: 
		//   self.validate_sq_inp_valid_prf(&ct_sq_inp,store_steps,&r1,&prf_inp)

		//3. validate the sq_to_add covers the entries in prf_fwd
		let prf_to_add = prf.borrow().get_container("prf_to_add")?;
		self.validate_to_add(&ct_sq_to_add, &ct_prf_fwd, 
			&r1, &prf_to_add)?;

		//4. validate the prf_fwd
		let prf_fwdprf_valid = prf.borrow().get_container("prf_fwdprf_valid")?;
		self.validate_fwdprf_valid_prf(&ct_prf_fwd, 
			&ct_sq_res, &ct_pat_loc,
			&r1, &r2, &prf_fwdprf_valid)?;

		Ok( () )
	}

	/// validate the proof for q1 + q2 = q3
	/// let n1 = |q1| = |q3|,
	/// let n2 = |q2|
	/// cost: (n1+n2) + n1 + (2(n1+n2) + 3n1) + (3(n1+n2) + 2n1)
	/// = 12n1 + 6n2
	#[allow(dead_code)]
	fn validate_step_queue_union_prf(&self,
		q1: &Rc<RefCell<Container<FpVar<F>>>>, //step_queue 1
		q2: &Rc<RefCell<Container<FpVar<F>>>>, //step_queue 2
		q3: &Rc<RefCell<Container<FpVar<F>>>>, //step_queue result
		r1: &FpVar<F>,
		r2: &FpVar<F>,
		prf_union: &Rc<RefCell<Container<FpVar<F>>>>
	)->Result<(), SynthesisError>{
		//1. retrieve the src and dst cols
		let cs = r1.cs();
		let e1=q1.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c1=q1.borrow().get_container("locs").unwrap().borrow().to_vec(); 
		let e2=q2.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c2=q2.borrow().get_container("locs").unwrap().borrow().to_vec(); 
		let e12 = vec![e1,e2].concat();
		let c12 = vec![c1,c2].concat();
		let e3=q3.borrow().get_container("encoded").unwrap().borrow().to_vec(); 
		let c3=q3.borrow().get_container("locs").unwrap().borrow().to_vec(); 

		//2. retrieve sid_cols and verify that they are in range.
		//check of sid_c2 can be skipped as to_add will be proved valid
		//inp_queue sid will be valid based on recursion (init is guaranteed ok)
		//can skip c3 as its range is guranteed after logup
		//alsmot mtb count can be skipped, as logup guanratees their 
		//correctness. So none has to be performed here

		//3. do 2-direction logup check
		let src = e12.iter().zip(c12.iter()).map(|(a,b)|
			a + (b*r1)).collect::<Vec<FpVar<F>>>();
		let dst = e3.iter().zip(c3.iter()).map(|(a,b)|
			a + (b*r1)).collect::<Vec<FpVar<F>>>();
		let mtb1=prf_union.borrow().get_container("mtb1").unwrap().borrow()
			.to_vec(); 
		let mtb2=prf_union.borrow().get_container("mtb2").unwrap().borrow()
			.to_vec(); 
		assert_logup(cs.clone(), &src, &dst, &mtb1, r2)?;
		assert_logup(cs.clone(), &dst, &src, &mtb2, r2)?;


		Ok( () )
	}

	/// validate the to_add covers what are produced in the forward prf
	#[allow(dead_code)]
	fn validate_to_add(&self,
		sq_to_add: &Rc<RefCell<Container<FpVar<F>>>>,
		prf_fwd: &Rc<RefCell<Container<FpVar<F>>>>,
		r1: &FpVar<F>,
		prf_to_add_valid: &Rc<RefCell<Container<FpVar<F>>>>
	)->Result<(), SynthesisError>{
		//1. retrieve info from to_add
		let encoded = sq_to_add.borrow().get_container("encoded")
			.unwrap().borrow().to_vec(); 

		let step = sq_to_add.borrow().get_container("step")
			.unwrap().borrow().to_vec(); 
		let locs = sq_to_add.borrow().get_container("locs")
			.unwrap().borrow().to_vec(); 
		let dst = encode_2col_var(&encoded, &locs);
		let dst_sel = step.iter().zip(locs.iter()).map(|(loc,step)|
			loc.is_zero().unwrap().not()
				.and(&step.is_zero().unwrap().not()).unwrap().into()
		).collect::<Vec<FpVar<F>>>();
		let dst_adj = dst.iter().zip(dst_sel.iter()).map(|(a,b)|
			a * b ).collect::<Vec<FpVar<F>>>();

		//2. retrieve info from prf_fwd
		let e1 = prf_fwd.borrow().get_container("dst_encoded")
			.unwrap().borrow().to_vec(); 
		let c1= prf_fwd.borrow().get_container("dst_loc")
			.unwrap().borrow().to_vec(); 
		let c3= prf_fwd.borrow().get_container("src_loc")
			.unwrap().borrow().to_vec(); 
		let src= encode_2col_var(&e1, &c1);
		let cs = locs[0].cs();
		let zero = new_const_var(&cs, F::zero());
		let e1_c3 = e1.iter().zip(c3.iter()).map(|(e,c)|
			e + &(c*r1)).collect::<Vec<FpVar<F>>>();
		let n = e1.len();
		let src_sel = (0..n).collect::<Vec<_>>().into_iter().map(|i|{
			if i==0 || i==n-1 {zero.clone()}
			else{//the entries in the middle are real values to add
				//boundary are defined over (dst_encode, src_loc) as key
				//note specifically src_loc does need to be included 
				// in consideration. 
				//This is because there might be multiple src loc from
				//the same src_pat that lead to new destination locs.
				//e1_c2 represents aggregaed (dst_encode, src_loc)
				//note here: i>0 and i<n-1
				let prod= &(&e1_c3[i]-&e1_c3[i-1]) 
					+ &((&e1_c3[i]-&e1_c3[i+1])*r1);
				let i_middle: FpVar<F> = prod.is_zero().unwrap().into();
				i_middle
			}
		}).collect::<Vec<FpVar<F>>>();
		let src_adj = src.iter().zip(src_sel.iter()).map(|(a,b)|
			a * b ).collect::<Vec<FpVar<F>>>();

		//4. verify the two lookups
		let mtb1=prf_to_add_valid.borrow()
			.get_container("mtb1").unwrap().borrow().to_vec(); 
		let mtb2=prf_to_add_valid.borrow()
			.get_container("mtb2").unwrap().borrow().to_vec(); 
		assert_logup(cs.clone(), &src_adj, &dst_adj, &mtb1, r1)?;
		assert_logup(cs.clone(), &dst_adj, &src_adj, &mtb2, r1)?;
		//no need to check mtb the log up ensures values ok.


		Ok( () )
	}

	/// Validate that the prf_fwd is wellformed (e.g., encoded corresponds
	/// to the right subsig-pat-rg info), and diff1/diff2 are generated
	/// correctly (for asserting the correct query result from pat-loc)
	#[allow(dead_code)]
	fn validate_fwdprf_valid_prf(&self,
		prf_fwd: &Rc<RefCell<Container<FpVar<F>>>>,
		sq_res: &Rc<RefCell<Container<FpVar<F>>>>,
		pat_loc: &Rc<RefCell<Container<FpVar<F>>>>,
		r1: &FpVar<F>,
		_r2: &FpVar<F>,
		prf_fwdprf_valid: &Rc<RefCell<Container<FpVar<F>>>>,
	)->Result<(), SynthesisError>{
		//0. retrieve data
		let cs = r1.cs(); 

		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let (zero, one, max) = (new_const_var(&cs, zero), 
			new_const_var(&cs, one), new_const_var(&cs, max));
		let names = vec!["src_encoded", "dst_encoded", 
			"src_loc", "src_step", 
			"dst_pat", "dst_rg_start", "dst_rg_end",
			"dst_loc", "dst_pat_id", "diff1", "diff2", "dst_subsig"];
		let v2d= names.iter().map(|n|{
			prf_fwd.borrow().get_container(n).unwrap().borrow().to_vec() 
		}).collect::<Vec<Vec<FpVar<F>>>>();
		let (src_encoded, dst_encoded,
			src_loc, _src_step, 
			dst_pat, dst_rg_start, dst_rg_end,
			dst_loc, dst_pat_id, diff1, diff2, dst_subsig) 
			= (&v2d[0], &v2d[1],
				&v2d[2], &v2d[3], 
				&v2d[4], &v2d[5], &v2d[6],
				&v2d[7], &v2d[8], &v2d[9], &v2d[10], &v2d[11]);
		let sid_cols = names.iter().map(|n|{
			prf_fwd.borrow().get_container(&format!("sid_{}",n)).unwrap()
				.borrow().to_vec()
		}).collect::<Vec<Vec<FpVar<F>>>>();
		let frg = new_const_var(&cs, F::from(RANGE2));

		//1. check sid ranges. This basically chencks the binding
		//between each col with their corresponding encoded column.
		//Note that: since encoded will be converted to sub_table_id,
		//this implicityly imply them in range as well.
		//1.1. check the validity of diff1, diff2 in range
		check_arr_eq(&sid_cols[9],&frg,&format!("err checking sid_diff1"))?; 
		check_arr_eq(&sid_cols[10],&frg,&format!("err checking sid_diff2"))?; 
		check_arr_eq(&sid_cols[2],&frg,&format!("err checking sid_src_loc"))?; 
		check_arr_eq(&sid_cols[7],&frg,&format!("err checking sid_dst_loc"))?; 

		//1.2 check src_step
		let info_id= F::from(0x23001101u32); //tag to avoid collision
		let f1 = F::from(1u64<<RANGE2_BIT);
        let factor1 = f1*f1*f1*f1*f1; //models encoded
        let factor2 = F::from(1u64<<32); //32-bit
		let part1 = info_id*factor1*factor2 + 
			F::from(ID_ENCODED_NORMAL_STEP)*factor1;
		let part1_alt = info_id*factor1*factor2 + 
			F::from(ID_ENCODED_LAST_STEP)*factor1;
		let part1 = new_const_var(&cs, part1);
		let part1_alt = new_const_var(&cs, part1_alt);
		let n = sid_cols[3].len();
		for i in 0..n{
			//check the tag is the sub-table-id derived from src_encoded
			//simulating the SubsigStepStore::gen_step_tbl_id
			//i.e., part1 + subsig_id = sid
			let subtbl_id = &part1 + &v2d[0][i]; 
			let subtbl_id_alt = &part1_alt + &v2d[0][i]; 
			let res = (&sid_cols[3][i]-&subtbl_id)*
					(&sid_cols[3][i]-&subtbl_id_alt);	 //either case is ok
			check_eq(&res, &zero, "fail src_step check")?;
		}

		//1.3 check other columns
		let ids = [4,5,6,11];
		let cats = [ID_ENCODED_PAT, ID_ENCODED_RG_START, 
			ID_ENCODED_RG_END, ID_ENCODED_SUBSIG];
		for x in 0..ids.len(){
			let part1 = info_id*factor1*factor2 + F::from(cats[x])*factor1;
			let part1 = new_const_var(&cs, part1);
			for i in 0..n{
				let subtbl_id = &part1 + &v2d[1][i]; 
				check_eq(&sid_cols[ids[x]][i], &subtbl_id, "fail dst check")?;
			}
		}


		//1. correctness of src_encoded (no proof needed). DEPRECATED
		// no longer needed as it's done already by sid-range

		//2. correctness of dst_encoded (no proof needed) - just decode it
		// DEPRECATED. no longer needed as it's checked by the
		// step 0.5 SID check

		//3. lookup pat-loc in pat_loc
		//3.1 verify the validity of nsp, nsp_p1 and p2_nsp
		//we just need to validate nsp_p1 and p2_nsp in range
		//nsp itself is not needed as later it's verified the lookup
		let pat_cols = ["sorted_key", "sorted_id", "sorted_val"].iter()
			.map(|n| pat_loc.borrow().get_container(n)
				.unwrap().borrow().to_vec()
			).collect::<Vec<Vec<FpVar<F>>>>();
		let (pat, pat_id, loc) = (&pat_cols[0], &pat_cols[1], &pat_cols[2]); 
		let _nsp_names = ["nsp", "nsp_p1", "p2_nsp"];
		let sid_nsp_p1 = prf_fwdprf_valid.borrow().get_container("sid_nsp_p1")
			.unwrap().borrow().to_vec();
		let sid_p2_nsp= prf_fwdprf_valid.borrow().get_container("sid_p2_nsp")
			.unwrap().borrow().to_vec();
		check_arr_eq(&sid_nsp_p1, &frg, "err checking sid_nsp_p1")?; 
		check_arr_eq(&sid_p2_nsp, &frg, "err checking sid_p2_nsp")?; 

		//3.2 prove that p1 and p2 are valid pairs in pat_loc
		let nsp_names = ["nsp", "nsp_p1", "p2_nsp"];
		let nsp_cols = nsp_names.iter().map(|n|
				prf_fwdprf_valid.borrow().get_container(n)
					.unwrap().borrow().to_vec())
				.collect::<Vec<Vec<FpVar<F>>>>();
		let (nsp, nsp_p1, p2_nsp) = (&nsp_cols[0], &nsp_cols[1], &nsp_cols[2]);
		let p1_p2= nsp.iter().zip(nsp_p1.iter().zip(p2_nsp.iter()))
			.map(|(nsp,(nsp_p1,p2_nsp))|{
			let p1 = nsp - &one - nsp_p1;
			let p2 = nsp + &one + p2_nsp;
			p1 + p2*r1
		}).collect::<Vec<FpVar<F>>>();
		let all_pairs = (0..pat.len()-1).into_iter().map(|i|
			&pat[i] + &pat[i+1]*r1).collect::<Vec<FpVar<F>>>();
		let all_pairs = [//add two dummy cols for 0 and max
			vec![
				&zero-&one + &one * r1,
				&pat[pat.len()-1] + &max * r1
			],
			all_pairs
		].concat();
		let m_tbl_pair = prf_fwdprf_valid.borrow().get_container("m_tbl_pairs")
			.unwrap().borrow().to_vec();//no need to check its sid
		assert_logup(cs.clone(), &p1_p2, &all_pairs, &m_tbl_pair, r1)?;

		//3.3. now prove that (dst_loc, dst_pat_id, dst_loc)
		//are valid (they can be found in the concat of
		//    pat-loc table  || now_show_loc table
		let src_combined = encode_cols_var_adv(
			&vec![dst_pat.to_vec(), dst_pat_id.to_vec(), dst_loc.to_vec()], 
			&vec![0,1,2], &r1);	
		let dst_combined_1 = encode_cols_var_adv(
			&vec![pat.to_vec(), pat_id.to_vec(), loc.to_vec()], 
			&vec![0,1,2], &r1);	
		let dst_combined_2 = nsp.iter().map(|item|{
			//each no show location has two entries
			encode_cols_var_adv(
				&vec![ //note var clone is low cost (still same var id)
					vec![item.clone(), item.clone()], //pat
			   		vec![zero.clone(), one.clone()], //ids
					vec![zero.clone(), max.clone()], //dummy locs
				], 
				&vec![0,1,2],
				&r1

			)
		}).flatten().collect::<Vec<FpVar<F>>>();
		let dst_combined = [ dst_combined_1, dst_combined_2 ].concat();
		let mtb_pat = prf_fwdprf_valid.borrow().get_container("mtb_pat")
			.unwrap().borrow().to_vec();
		//no need to check sid, just check logup
		assert_logup(cs.clone(), &src_combined, &dst_combined, &mtb_pat, r1)?;

		//4. prove encoded-loc corresponds to res_queue
		let res_encoded= sq_res.borrow().get_container("encoded")
			.unwrap().borrow().to_vec();
		let _res_step= sq_res.borrow().get_container("step")
			.unwrap().borrow().to_vec();
		let res_loc = sq_res.borrow().get_container("locs")
			.unwrap().borrow().to_vec();
		let sid_res_step= sq_res.borrow().get_container("si_step")
			.unwrap().borrow().to_vec();

		let dst_adj= encode_cols_var_adv(&vec![src_encoded.to_vec(), 
			src_loc.to_vec()], &vec![0,1], &r1);
		let src_combined = encode_cols_var_adv(&vec![res_encoded.clone(), res_loc.clone()], &vec![0,1], &r1);
		let info_id= new_const_var(&cs,F::from(0x23001101u32)); 
		let f1 = new_const_var(&cs,F::from(1u64<<RANGE2_BIT));
        let factor1 = &f1*&f1*&f1*&f1*&f1; //models encoded
        let factor2 = new_const_var(&cs,F::from(1u64<<32)); //32-bit
		let part1_alt = &(&info_id*&factor1*&factor2) + 
			&(&new_const_var(&cs, F::from(ID_ENCODED_LAST_STEP))*&factor1);
		let src_sel = sid_res_step.iter().zip(res_encoded.iter())
			.map(|(sid_step, encoded)|{
				let final_id = &part1_alt + encoded;
				let res:FpVar<F> = final_id.is_eq(&sid_step).unwrap().into();
				&one - &res
			}).collect::<Vec<FpVar<F>>>();
		let src_adj = src_combined.iter().zip(src_sel.iter()).map(|(a,b)|
			a * b).collect::<Vec<FpVar<F>>>();

		let mtb_res1 = prf_fwdprf_valid.borrow()
			.get_container("mtb_res1").unwrap().borrow().to_vec();
		let mtb_res2 = prf_fwdprf_valid.borrow()
			.get_container("mtb_res2").unwrap().borrow().to_vec();
		//no need to check sid of mtbs.
		assert_logup(cs.clone(), &src_adj, &dst_adj, &mtb_res1, r1)?;
		assert_logup(cs.clone(), &dst_adj, &src_adj, &mtb_res2, r1)?;

		//5. prove the ascending order of pat_id column.
		// Check: when (dst_encoded, src_loc) 
		// is the same, the pat_id increase by 1
		// NOTE that (dst_encoded, src_loc) pair is NEEDED,
		// as the same loc might be appearing for DIFFERENT subsig/pat
		// when they appear consecutively, there is no way to distinguish.
		//
		// when the (dst_encoded, src_loc) pair is the SAME,
		// it is required that pat_id increase by 1.
		// when they are not the same, there is NO restriction (as the
		//  starting pat_id does NOT necesarily starts from 0 - so that's
		//  no check for boundaries).
		for i in 1..dst_pat_id.len(){
			//b_same either 1 or 0
			let item1= &dst_encoded[i] + &(&src_loc[i]*r1);
			let item2= &dst_encoded[i-1] + &(&src_loc[i-1]*r1);
			let b_same:FpVar<F>=item1.is_eq(&item2)?.into();
			let item1 = &b_same * (&dst_pat_id[i]-&dst_pat_id[i-1]-&one);
			let item = &dst_encoded[i]* &item1;
			check_eq(&item, &zero, "failed increase check")?;
		}

		//6. prove the validity of diff1/diff2
		//6.1 retrieve the data (cost: n)
		let sid_abs_rg2_max = prf_fwdprf_valid.borrow()
			.get_container("sid_abs_rg2_max").unwrap().borrow().to_vec();
		check_arr_eq(&sid_abs_rg2_max,&frg,&format!("err abs_sid_rg2_max"))?; 
		let abs_rg2_max = prf_fwdprf_valid.borrow().get_container("abs_rg2_max")
				.unwrap().borrow().to_vec();

		//6.2 compute the border cases
		//cost: 4n
		let vec_b_begin = (0..diff1.len()).into_iter().map(|i|{
			let b_begin = if i==0 {one.clone()} else {
				(&dst_subsig[i]*r1+&src_loc[i]).is_neq(
					&(&dst_subsig[i-1]*r1 + &src_loc[i-1])
				).unwrap().into()
			};
			b_begin
		}).collect::<Vec<FpVar<F>>>();
		//note that b_begin[i] implies b_end[i-1]
		let vec_b_end= (0..diff1.len()).into_iter().map(|i|{
			if i==diff1.len()-1{one.clone()} else{vec_b_begin[i+1].clone()}
			//will not cost anything
		}).collect::<Vec<FpVar<F>>>();

		for i in 0..diff1.len(){
			let rg1 = &dst_rg_start[i] + &src_loc[i];
			let rg2 = &dst_rg_end[i] + &src_loc[i];
			//step 1. verify the validity of abs_rg2_max
			//note: one of item11 and item12 is 0
			//note2: no need for abs_rg1_max as it's not possible to underflow
			//unlike rg2 case in the end border sometimes src_loc + rg_end > max
			//cost:3n
			let item21 = &rg2 - &max + &abs_rg2_max[i];
			let item22 = &max- &rg2 + &abs_rg2_max[i];
			let item2 = &item21 * &item22;
			check_eq(&item2, &zero, "err abs2")?;

			//step 2. use abs_rg2_max to update rg2
			//when they are greater than max
			//cost:4n
			let rg2 = item22.is_zero()?.select(&(&max-&one), &rg2)?;

			//step 3. validate diff1 and diff2.
			//diff1 is: (1) rg1-dst_loc[i]-one when it's beginning of
			//a new subsig-loc, (2) don't care if it's end,
			// (3) otherwise it's dst_loc[i]-rg1 (in th middle)
			//cost: 7n
			let b_begin = &vec_b_begin[i];
			let b_end= &vec_b_end[i];
			let b_middle = &(&one-b_begin) * &(&one-b_end);
			let item1 = &dst_subsig[i]* &(
				b_begin * &(&diff1[i] + &one + &dst_loc[i]-&rg1)
				  + &b_middle *&(&diff1[i] + &rg1 - &dst_loc[i])
				 //b_end is don't care so no need to list
			);
			check_eq(&item1, &zero, "err_diff1")?;

			//diff2 is (1) dst_loc[i]-one-rg2 if at end,
			// (2) don't care if it's begin
			// (3) rg2-dst_loc[i] if in the middle
			let item2 = &dst_subsig[i]* &(
				b_end * &(&diff2[i] + &one + &rg2 - &dst_loc[i])
				+ &b_middle * &(&diff2[i] - &rg2 + &dst_loc[i])
			);
			check_eq(&item2, &zero, "err_diff2")?;

		}

		Ok( () )
	}

	/// validate forward_step_queue combo (info and prf) are valid
	/// This corresponds to the gen_forward_steps_queue_combo
	#[allow(dead_code)]
	fn validate_backward_step_queue(&self, 
		forward_step_q: &Container<FpVar<F>>,  //needed to extract its result
		backward_step_q: &Container<FpVar<F>>, //backward combo 
		r1: FpVar<F>,
		r2: FpVar<F>,
		_cs: ConstraintSystemRef<F>
	) ->Result<(), SynthesisError>{
		//0. retrive the data
		let ct_sq_res1 = forward_step_q.get_container("sq_res")?;
		let ct_sq_to_del= backward_step_q.get_container("sq_to_del")?;
		let ct_sq_res2 = backward_step_q.get_container("sq_res2")?;
		let ct_prf_bwd = backward_step_q.get_container("prf_bwd")?;

		//1. verify sq_del + sq_res2 = sq_res1
		let prf = backward_step_q.get_container("prf")?;
		let prf_union = prf.borrow().get_container("prf_union")?;
		self.validate_step_queue_union_prf(&ct_sq_res2, &ct_sq_to_del,
			&ct_sq_res1, &r1, &r2, &prf_union)?;

		//2. no need to validate sq_inp and step_store as it's based
		//on fwd_prf which is already validated

		//3. validate the sq_to_del covers the entries in prf_bwd
		let prf_to_del= prf.borrow().get_container("prf_to_del")?;
		self.validate_to_del(&ct_sq_to_del, &ct_prf_bwd, 
			&r1, &prf_to_del)?;

		//4. validate the prf_bwd is valid
		let prf_bwdprf_valid = prf.borrow().get_container("prf_bwdprf_valid")?;
		self.validate_bwdprf_valid_prf(&ct_prf_bwd, 
			&ct_sq_res2, &r1, &r2, &prf_bwdprf_valid)?;

		Ok( () )
	}

	/// validate the to_del covers what are produced in the backward prf
	/// In fact (unlike to_add) it only checks to_del is a SUBSET of backward
	/// prf (because if there are items missing it only increases prover's cost
	/// but not affecting soundness).
	fn validate_to_del(&self,
		sq_to_del: &Rc<RefCell<Container<FpVar<F>>>>,
		prf_bwd: &Rc<RefCell<Container<FpVar<F>>>>,
		r1: &FpVar<F>,
		prf_to_del_valid: &Rc<RefCell<Container<FpVar<F>>>>
	)->Result<(), SynthesisError>{
		//1. retrieve info from to_del
		let encoded = sq_to_del.borrow().get_container("encoded")
			.unwrap().borrow().to_vec(); 
		let locs = sq_to_del.borrow().get_container("locs")
			.unwrap().borrow().to_vec(); 
		let dst = encode_2col_var_adv(&encoded, &locs, r1);

		//2. no need to check default loc1 for step 0 (unlike prf_to_add)

		//3. retrieve info from prf_bwd
		let e1 = prf_bwd.borrow().get_container("prev_encoded")
			.unwrap().borrow().to_vec(); 
		let c1= prf_bwd.borrow().get_container("loc_to_del")
			.unwrap().borrow().to_vec(); 
		let cs = locs[0].cs();
		let src = encode_2col_var_adv(&e1, &c1, r1);

		//4. verify the one-direction lookup
		let mtb2=prf_to_del_valid.borrow()
			.get_container("mtb2").unwrap().borrow().to_vec(); 
		assert_logup(cs.clone(), &dst, &src, &mtb2, r1)?;
		Ok( () )
	}

	/// Validate that the prf_bwd is wellformed.
	#[allow(dead_code)]
	fn validate_bwdprf_valid_prf(&self,
		prf_bwd: &Rc<RefCell<Container<FpVar<F>>>>,
		sq_res: &Rc<RefCell<Container<FpVar<F>>>>, //the final sq_res
		r1: &FpVar<F>,
		r2: &FpVar<F>,
		prf_bwdprf_valid: &Rc<RefCell<Container<FpVar<F>>>>,
	)->Result<(), SynthesisError>{
		//0. retrieve data
		let cs = r1.cs(); 
		let max_val:usize = (1<<RANGE2_BIT) - 1;
		let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));
		let (zero, one, _max) = (new_const_var(&cs, zero), 
			new_const_var(&cs, one), new_const_var(&cs, max));
		let frg = new_const_var(&cs, F::from(RANGE2));
		let names = vec![
			"src_encoded",  "src_step", 
			"src_pat", "src_min_loc", "src_rg_end",
			"prev_encoded", "loc_to_del"
		];
		let v2d= names.iter().map(|n|{
			prf_bwd.borrow().get_container(n).unwrap().borrow().to_vec() 
		}).collect::<Vec<Vec<FpVar<F>>>>();
		let (
			_src_encoded, _src_step,
			_src_pat,  src_min_loc, src_rg_end,
			_prev_encoded, loc_to_del)
		= (
			&v2d[0], &v2d[1], 
			&v2d[2], &v2d[3], &v2d[4], 
			&v2d[5], &v2d[6]
		);
		let sid_cols = names.iter().map(|n|{
			prf_bwd.borrow().get_container(&format!("sid_{}",n)).unwrap()
				.borrow().to_vec()
		}).collect::<Vec<Vec<FpVar<F>>>>();

		//1.1. check the validity of diff1, diff2 in range
		// no need to check src_encoded and prev_encoded as later
		// also no need to check src_min_loc and loc_to_del they will
		// be looked up in sq_res and sq_to_del as well.
		// thus no need to check cols: 0, 3, 5, 6

		//1.2 check src_step
		let info_id= F::from(0x23001101u32); //tag to avoid collision
		let f1 = F::from(1u64<<RANGE2_BIT);
        let factor1 = f1*f1*f1*f1*f1; //models encoded
        let factor2 = F::from(1u64<<32); //32-bit
		let part1 = info_id*factor1*factor2 + 
			F::from(ID_ENCODED_NORMAL_STEP)*factor1;
		let part1_alt = info_id*factor1*factor2 + 
			F::from(ID_ENCODED_LAST_STEP)*factor1;
		let part1 = new_const_var(&cs, part1);
		let part1_alt = new_const_var(&cs, part1_alt);
		let n = sid_cols[1].len();
		for i in 0..n{
			//check the tag is the sub-table-id derived from src_encoded
			//simulating the SubsigStepStore::gen_step_tbl_id
			//i.e., part1 + subsig_id = sid
			let subtbl_id = &part1 + &v2d[0][i]; 
			let subtbl_id_alt = &part1_alt + &v2d[0][i]; 
			let res = (&sid_cols[1][i]-&subtbl_id)*
					(&sid_cols[1][i]-&subtbl_id_alt);	 //either case is ok
			check_eq(&res, &zero, "fail src_step check")?;
		}

		//1.3 check other columns
		let ids = [2,4,5];
		let cats = [ID_ENCODED_PAT, ID_ENCODED_RG_END, ID_ENCODED_PREV_ENCODED];
		for x in 0..ids.len(){
			let part1 = info_id*factor1*factor2 + F::from(cats[x])*factor1;
			let part1 = new_const_var(&cs, part1);
			for i in 0..n{
				let subtbl_id = &part1 + &v2d[0][i]; 
				check_eq(&sid_cols[ids[x]][i], &subtbl_id, "fail dst check")?;
			}
		}


		//1 and 2. DEPRECATED - correctness of src_encoded-step-rg_end 
		// and other related bindings.
		// already provided in sid check. no need

		//3. prove sq_res has its loc sorted and
		// we prove that first the subsig is sorted and then
		// the step is sorted per subsig.
		let rescols = vec!["encoded", "step", "locs", "subsig"].iter().map(|n|
			sq_res.borrow().get_container(n).unwrap().borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
		//3.1 prove subsig
		let diffsubsig = (0..rescols[3].len()-1).into_iter().map(|i|{
			&rescols[3][i+1] - &rescols[3][i] 
		}).collect::<Vec<FpVar<F>>>();
		let saved_diffsubsig = prf_bwdprf_valid.borrow()
			.get_container("diff_subsig").unwrap().borrow().to_vec();
		let sid_diffsubsig= prf_bwdprf_valid.borrow()
			.get_container("sid_diff_subsig").unwrap().borrow().to_vec();
		check_arr_eq(&sid_diffsubsig, &frg, "err checking sid_diffsubsig")?; 
		check_arr_eq_arr(&diffsubsig, &saved_diffsubsig, "err checking diffsubsig")?; 

		//3.2 prove step is sored per subsig
		let sel = (0..rescols[3].len()).into_iter().map(|i|{
			if i==0 {zero.clone()} else{
				rescols[3][i].is_eq(&rescols[3][i-1]).unwrap().into()
			}
		}).collect::<Vec<FpVar<F>>>();
		let diff_step = (0..rescols[1].len()).into_iter().map(|i|{
			if i==0 {zero.clone()} else {
				&(&rescols[1][i] - &rescols[1][i-1]) * &sel[i]
			}
		}).collect::<Vec<FpVar<F>>>();
		let saved_diff_step = prf_bwdprf_valid.borrow().get_container("diff_step")
			.unwrap().borrow().to_vec();
		let sid_diff_step= prf_bwdprf_valid.borrow()
			.get_container("sid_diff_step").unwrap().borrow().to_vec();
		check_arr_eq(&sid_diff_step, &frg, "err checking sid_diff_step")?; 
		check_arr_eq_arr(&diff_step, &saved_diff_step, "err checking diff_step")?; 

		//3.3 prove loc is sorted per subsig-step
		let sel = (0..rescols[0].len()).into_iter().map(|i|{
			if i==0 {zero.clone()} else{
				rescols[0][i].is_eq(&rescols[0][i-1]).unwrap().into()
			}
		}).collect::<Vec<FpVar<F>>>();
		let diff_loc = (0..rescols[0].len()).into_iter().map(|i|{
			if i==0 {zero.clone()} else {
				&(&rescols[2][i] - &rescols[2][i-1]) * &sel[i]
			}
		}).collect::<Vec<FpVar<F>>>();
		let saved_diff_loc = prf_bwdprf_valid.borrow().get_container("diff_loc")
			.unwrap().borrow().to_vec();
		let sid_diff_loc= prf_bwdprf_valid.borrow()
			.get_container("sid_diff_loc").unwrap().borrow().to_vec();
		check_arr_eq(&sid_diff_loc, &frg, "err checking sid_diff_loc")?; 
		check_arr_eq_arr(&diff_loc, &saved_diff_loc, "err checking diff_loc")?; 

		//4. prove the min_loc is the first loc in sq_res
		let src_combined= encode_cols_var_adv(&v2d, &vec![0,1,3], r1);
		let dst_combined = encode_cols_var_adv(&rescols, &vec![0,1,2], r1);
		let dst_sel = (0..dst_combined.len()).into_iter().map(|i|{
			if i==0 { zero.clone() //assuming 1st one is dummy
			}else{//only pick the very first entry
				//let b_first = rescols[0][i].is_neq(&rescols[0][i-1]).unwrap();
				//b_first.into()
				&one - &sel[i]
			}
		}).collect::<Vec<FpVar<F>>>();
		let dst_adj = dst_combined.iter().zip(dst_sel.iter())
			.map(|(x,y)| x*y).collect::<Vec<FpVar<F>>>();
		let mtb_min_loc= prf_bwdprf_valid.borrow().get_container("mtb_min_loc")
			.unwrap().borrow().to_vec();
		assert_logup(cs.clone(), &src_combined, &dst_adj, &mtb_min_loc, r2)?;

		//5. prove min_loc > (loc_to_remove + rg_2) 
		let sel = (0..src_rg_end.len()).into_iter().map(|i|
			&one - & src_min_loc[i].is_zero().unwrap().into()
		).collect::<Vec<FpVar<F>>>();
		let saved_diff_loc = prf_bwdprf_valid.borrow().get_container("diff_min")
			.unwrap().borrow().to_vec();
		let sid_saved_diff_loc = prf_bwdprf_valid.borrow()
			.get_container("sid_diff_min").unwrap().borrow().to_vec();
		let sum= (0..src_rg_end.len()).into_iter().map(|i|
			&sel[i]*(&saved_diff_loc[i] + 
				(&loc_to_del[i] + &src_rg_end[i] + &one) - &src_min_loc[i])
		).collect::<Vec<FpVar<F>>>();
		check_arr_eq(&sid_saved_diff_loc, &frg, "err checking sid_diff_loc")?; 
		check_arr_eq(&sum, &zero, "err checking expected sum for diff")?; 

		Ok( () )
	}
		
}

impl <F:PrimeField> SigmaGadget<F> for DischargeAdvGadget<F>{
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
		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA],0,0)
	}

	fn est_cost(&self)->usize{
		//TODO: refine formula in real data later
		let est1 = self.capacity.subsigs * 
			self.capacity.avg_active_pats_per_subsig * 1000;
		let est2 = self.capacity.get_pat_loc_len() * 1000;
		if est1>est2 {est1} else {est2}
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
		let n1 = cs.num_constraints(); 

		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();

		//3. validate the forward step queue
		let forward_step_queue= stmt.get_container("fwd_steps_queue")?;
		self.validate_forward_step_queue(&forward_step_queue.borrow(), 
			r1.clone(), r2.clone(), cs.clone())?;

		//4. validate the backward step queue
		let backward_step_queue= stmt.get_container("bwd_steps_queue")?;
		self.validate_backward_step_queue(&forward_step_queue.borrow(), 
			&backward_step_queue.borrow(),
			r1.clone(), r2.clone(), cs.clone())?;

		let b_perf = true;
		if b_perf{
			println!("PERF 102: discharge_adv: TOTAL num_cons: {}", 
				cs.num_constraints()-n1);	
		}

		Ok(())
	}
}

#[allow(dead_code)]
fn dummy_test<F:PrimeField>(){
	//just call it here for saving import lines 
	let _= is_sorted(&vec![F::zero()]); 
	check_rg2(&vec![F::zero()], &vec![F::zero()]);
}

#[cfg(test)]
pub mod tests_discharge_adv_gadget{
	use ark_ff::{Zero};
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use utils::{data::{pack_nibbles}, os::{read_nibbles,proj_root,write_to_file}};
	use crate::gadgets::{
		word_extract::{
			LEGS,
			tests_word_extract_gadget::{test_gadget_adv},
		},
		fsm_adv::{FsmAdvAdvice,FsmAdvCapacity},
		word_extract_adv::{WordExtractAdvAdvice},
		discharge_adv::{DischargeAdvAdvice,DischargeAdvGadget,
			DischargeAdvCapacity,StepQueueItem,StepQueue,StepQueueType},
		traits::{Container,Col,IDX_DATA},
	};
	use data_processor::{clam_db::{ClamavDB,RANGE2_BIT}, 
		type_def::{ClamavApproxConfig,SubsigStepStoreItem,SubsigStepStore},
		clamav::{default_clamav_cfg, quick_discharge_file_adv}};
	use folding_schemes::folding::foldpot::sigma_ir1cs::{SigmaGadget,
		WordInfo, DischargeSigInfo};
	use folding_schemes::folding::foldpot::container_config::ContainerConfig;
	use std::collections::{HashMap};

	/// a test case for discharge_test_case	
	struct Tcase{//test case
		pub file_content: String,
		pub sig_to_discharge: String, //the signatures to be discharged
			//NOTE: the sig should be INCLUDED in the discharge list
			//of the quick_discharge result's WordInfo. The motivation
			//is to restrict the testing to the original test case,
			//had other cases been added which causes expansion of the
			//list of sigs to discharge.
		pub b_ised: bool, //whether this runs in ISED mode.
						  //if in ISED model, the length of discharged_sig
						  //should be 1.
		pub b_igc: bool, //whether to run in b_igc mode
	}

	impl Tcase{
		pub fn new(file_content: &str, sig_to_disc: &str, b_ised: bool, b_igc: bool)->Self{
			Self{file_content: file_content.to_string(),
				sig_to_discharge: sig_to_disc.to_string(),
				b_ised, b_igc}
		}
	}


	/// MAINLY for testing the discharge (sed) component.
	///
	/// discharge each test case (mainly running through 
	/// all components from fsm_adv to discharge_adv
	/// we expect circuit is satisfiable and all SPECIFIED
	/// sigs in the test case are discharged.
	fn discharge_test_case(
		word_dir: &str,
		db: &ClamavDB<Fr>,
		tcase: &Tcase,
		cfg: &ClamavApproxConfig,
	){
		//1 data preparation
		//1.1. write the tcase file contents to the file
		//then do a quick discharge to retrieve the discharge info.
		let zero = Fr::zero();
		let path = format!("{}/data/{}/word.txt", proj_root(), word_dir);
		write_to_file(&path, &tcase.file_content);
		let nibbles_raw = read_nibbles(&path);
		let f_nibbles = nibbles_raw.iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let sig_to_discharge = tcase.sig_to_discharge.clone();
		let wi: WordInfo = quick_discharge_file_adv(
			"word.txt", 
			&nibbles_raw,
			&db.vec_sigs,
			&db.vec_sigs_no_critical_pat,
			&db.map_crit_pat, 
			&db.map_crit_pat_igc, 
			&db.dfa_crit, 
			&db.bundle_subsig.vec_acdfa[0], //dfa_patterns, 
			&db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
			cfg, 
			&db.sig_to_id
		); //use optimize mode

		//1.2 verify the sig_to_discharge is in the word info.
		// NOTE that here we essentially require that sig_to_discharge
		// be IN the required discharge_list (sed/ised). This helps
		// to handle hte case more signatures are added which complicates
		// the original test case.
		let sigs_info = if tcase.b_ised{&wi.vec_ised_sigs_info}
			else {&wi.vec_sed_sigs_info};
		let infos = sigs_info.iter().filter(|i| i.sig_name==sig_to_discharge)
			.map(|i| i.clone()).collect::<Vec<DischargeSigInfo>>();
		assert!(infos.len()==1, "ERR in idnetifying: {}, infos.len: {}",
			sig_to_discharge, infos.len());

		//1.3 set data of acdfa, input_sigs, and bundle info related to the sig.
		let info = infos[0].clone();
		let b_igc = tcase.b_igc;
		let bundle = if !b_igc {&db.bundle_subsig} else {&db.bundle_subsig_igc};
		assert!(bundle.b_igc == b_igc);
		let acdfa = if tcase.b_ised{
			let ids = bundle.vec_sig_names.iter().enumerate()
				.filter(|(_i,s)| s.to_string()==sig_to_discharge)
				.map(|(i,_s)| i).collect::<Vec<usize>>();
			assert!(ids.len()==1, "ERROR cannot find id or duplicate for {}, details of ids: {:?}", sig_to_discharge, ids);
			let id = ids[0];
			&bundle.vec_acdfa[id]
		}else {
			&bundle.vec_acdfa[0]
		};
		let sig_id = *(db.sig_to_id.get(&sig_to_discharge).unwrap());
		let input_subsigs = info.subsig_ids.iter().map(|i|
			Fr::from(acdfa.gen_subsig_id(sig_id, *i+1) as u32)
		).collect::<Vec<Fr>>();
		let store_id = if tcase.b_ised{sig_id} else {0};//0 for all
		let fsm_id = ClamavDB::<Fr>::pm_acdfa_id(store_id, b_igc);
		let steps_store = &bundle.vec_subsig_step_stores[store_id]; 

		//1.4 capacilities of fsm and discharge components
		let wlen = 2usize;
		let (nibble_len, state_bits) = (wlen*LEGS, acdfa.state_part_bits);
		let cap = FsmAdvCapacity{max_nibble_len: nibble_len, 
			acdfa_state_part_bits: state_bits, 
			subsigs: 4,
			avg_pats_per_subsig: 4,
			perc_pats_in_trace: 27 
		};
		let cap_disc = DischargeAdvCapacity{//capaciity of discharge comopnent
			max_nibble_len: nibble_len, 
			subsigs: cap.subsigs,
			avg_active_pats_per_subsig: 1,
			perc_pats_in_trace: cap.perc_pats_in_trace, 
		};

		//2. create advice for word_extract_adv, fsm_adv, and discharge_adv
		// both advices are needed for producing related container_config
		// with external col referece.
		let all_word = pack_nibbles(&f_nibbles);
		let alen = all_word.len();
		let n_cycles = if alen%wlen==0 {alen/wlen} else {alen/wlen+1};

		//2.0 input that needs to be fed to advice. update it at end of loop
		let mut inp_state = Fr::from((acdfa.init_state + 1) as u32);
		let mut inp_loc = Fr::from(1u32);
		let mut inp_steps_queue = DischargeAdvAdvice::gen_empty_steps_queue_serialized(&input_subsigs, &steps_store, fsm_id, &cap_disc);  

		for i in 0..n_cycles{
			//2.1 the word_extract_adv
			let end = if wlen*(i+1)>alen {alen} else {wlen*(i+1)};
			let word = all_word[wlen*i..end].to_vec();
			let word = if word.len()==wlen {word} else
				{vec![word.clone(), vec![zero; wlen-word.len()]].concat()};	
			let act_size = word.len();
			let adv_wea = WordExtractAdvAdvice::new(&word, act_size,false);
			let stmt_wea = adv_wea.stmt_container;
			let cfg_wea = stmt_wea.borrow().get_cfg(); 

			//2.2 the fsm_adv (SED approach)
			let nibbles = stmt_wea.borrow().get_container("nibbles").unwrap()
				.borrow().to_vec();
			assert!(nibbles.len()==nibble_len);

			let adv_faa = FsmAdvAdvice::new(b_igc, //case sensitive,
				1, //dist to wea gadget
				&nibbles, &acdfa, inp_state, 
				inp_loc, &input_subsigs, &cap, fsm_id, 
				&bundle.vec_subsig_stores[store_id]); 
			let stmt_faa = adv_faa.stmt_container;
			let cfg_faa = stmt_faa.borrow().get_cfg(); 

			//2.3 the discharge_adv
			let sname_fsm = if b_igc {"fsm_adv_stmt_igc"} 
				else {"fsm_adv_stmt_cs"};
			let pat_loc = stmt_faa.borrow().search_container(
				&format!("{} packed_trace pat_loc sorted_tbl", sname_fsm))
				.unwrap();
			let adv_disc= DischargeAdvAdvice::new(false, //case sensitive
				1, //offset to fsm
				&pat_loc, &input_subsigs,
				fsm_id, steps_store, &cap_disc, &inp_steps_queue);
			let oup_queue = adv_disc.get_output_steps_queue();
			let stmt_disc= adv_disc.stmt_container;
			let cfg_disc= stmt_disc.borrow().get_cfg(); 


			//2.4 given cfgs, set up the positions
			let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa.clone(), cfg_disc];
			ContainerConfig::adjust_locations(&mut vec_cfg); //resolve

			//2.6. generate the 7 segments of output for building statment
			//from inp to si_data
			let cps1 = stmt_wea.borrow().gen_stmt_components(); 
			let cps2 = stmt_faa.borrow().gen_stmt_components(); 
			let cps3 = stmt_disc.borrow().gen_stmt_components(); 
			let cps = cps1.into_iter().zip(cps2.into_iter()).map(|(a,b)|
				vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();
			let cps = cps.into_iter().zip(cps3.into_iter()).map(|(a,b)|
				vec![a,b].concat()).collect::<Vec<Vec<Fr>>>();

			//2.7 create the gadget
			let lkup_share_size = 4usize;
			let mut dcg = DischargeAdvGadget::<Fr>::new(false, //case sentive,
				1, //dist to fsm_adv gadget,
				&cap_disc, fsm_id,
				&vec![cfg_wea.clone(), cfg_faa.clone()],
				&bundle.vec_subsig_step_stores[0], //for sed
			);
			dcg.set_container_cfg(vec_cfg.clone().into(),2);  //2 for
															// it's the 3rd cfg
			let rg = Rc::new(dcg);

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

			//4. reset the inputs for the next cycle
			let states = stmt_faa.borrow()
				.search_container(&format!("{} fsm_acc states", sname_fsm))
				.expect("no states")
				.borrow().to_vec();
			inp_state = states[states.len()-1];
			let locs = stmt_faa.borrow()
				.search_container(&format!("{} fsm_acc locs", 
					sname_fsm))
				.expect("no locs")
				.borrow().to_vec();
			inp_loc = locs[locs.len()-1];
			inp_steps_queue = StepQueue::parse_from(&oup_queue, &cap_disc);
		}


		//4. verify the sigs_to_discharge have been discharged
		//todo!()
	}

	#[test]
	fn test_discharge_adv(){
		//1. define the sigs
		let sigs = vec![
			"sig2;Engine:51-255,Target:0;0&1;/def.*234.*567/;/234....def/",
			"sig1;Engine:51-255,Target:0;0&1;/abc..123/;/123....abc/",
			"sig3;Engine:51-255,Target:0;0&1;/fgh.*1234......56...78/;/56......fgh/",
		].iter().map(|x| x.to_string()).collect::<Vec<String>>();
		let needs_dfa = vec![];
		let needs_ised= vec![];
		let needs_ised_igc = vec![];
		let sigs_dir = "debug/sed/workdir";
		let cfg = default_clamav_cfg();
		let db = ClamavDB::<Fr>::build_test_db(&cfg, &sigs_dir, &sigs, 
			&needs_dfa, &needs_ised, &needs_ised_igc);

		//2. define the test cases
		let testcases = vec![
			//2. fails sig2 coz 3rd pattern missing
			Tcase::new("defxx234xx56", "sig2", false, false),
			//1. fails sig1 coz gap len incorrect
			Tcase::new("abcddd123", "sig1", false, false), //b_ised=F, igc=F
			//3. similar to test2 for longer string (2 cycles)
			// debug to verify that location 193 (corresponding to
			// 234 is added to "to_add" and in "res". "56" is not identified
			Tcase::new(
				&format!("def{}234xx56","x".repeat(90)), 
				"sig2", false, false),
			//4. a case where only one patterns occur at all, and across 3 cyles
			Tcase::new(
				&format!("ddd{}234xx{}56","x".repeat(90), "u".repeat(90)), 
				"sig2", false, false),
			//5. a case which has both fwd and backward elimination.
			//manually check debug messages of backward and forward proofs
			//baseically: the last 78 is not added, but the
			//first 78 kills the 1st 56, which then kills the first three
			//1234
			Tcase::new("fghxx1234xx1234xx1234x1234x56xxx56xxx78xx78xx", "sig3", false, false), 
		];

		for tc in testcases{
			discharge_test_case(&sigs_dir, &db, &tc, &cfg);
		}
	}

	fn to_vf(vec: Vec<u32>)->Vec<Fr>{
		vec.iter().map(|x| Fr::from(*x)).collect()
	}

	#[test]
	fn test_fwd_prf(){
		//0. create a subsig step store
		let item1 = SubsigStepStoreItem::new(100, false, //case sensitive
			vec![	
				(2, (10, 100)),
				(3, (20,30)),
			]);
		let item2 = SubsigStepStoreItem::new(200, false,
			vec![	
				(20, (20,120)),
				(30, (10,20)),
				(40, (100, 200)),
				(50, (100, 200)),
			]);
		let mut steps_info = SubsigStepStore::new();
		steps_info.add(&item1);
		steps_info.add(&item2);
		steps_info.finalize();

		//1. test the serialization
		let max :u32= (1<<RANGE2_BIT) - 1;
		let subsig100_steps = vec![
			StepQueueItem::new2( 
				// subsig, id, pat, rg_start, rg_end
				to_vf(vec![100u32, 0, 0, 0, 0]), to_vf(vec![1u32])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 1, 2, 10, 100]), to_vf(vec![11u32, 12])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 2, 3, 20, 30]), to_vf(vec![32,43])),
		];
		let subsig200_steps = vec![
			StepQueueItem::new2( 
				to_vf(vec![200u32, 0, 0, 0, 0]), to_vf(vec![1u32])),
			StepQueueItem::new2( 
				to_vf(vec![200u32, 1, 20, 20, 120]), to_vf(vec![22u32, 30])),
		];
		let subsigs = to_vf(vec![100,200]);
		let mut store_items = HashMap::new();
		store_items.insert(Fr::from(100u32), subsig100_steps);
		store_items.insert(Fr::from(200u32), subsig200_steps);
		let capacity= DischargeAdvCapacity{
			max_nibble_len: 62, 
			subsigs: 4,
			avg_active_pats_per_subsig: 4,
			perc_pats_in_trace: 48,
		};
		let sq = StepQueue{subsigs, store_items, capacity: capacity.clone(),
			q_type: StepQueueType::Res};
		let ct = sq.to_container("ct", true, false, false, true, &steps_info);
		let pat = ct.borrow().get_container("encoded")
			.unwrap().borrow().to_vec();
		let loc = ct.borrow().get_container("locs").unwrap().borrow().to_vec();
		let vec = vec![pat, loc].concat();
		let sq2 = StepQueue::parse_from(&vec, &capacity);
		assert!(sq == sq2);

		//2. test the forward proof
		let pat_loc = Container::new("pat_loc"); 
		let pat_tuples = vec![
			(2,0,0), //dummy
			(2,1,63),
			(2,2,102),
			(2,3,max), //dummy

			(3,0,0), 
			(3,1,65),
			(3,2,93),
			(3,3,94),
			(3,4,max),

			(20,0,0),
			(20,1,51),
			(20,2,max),

			(30,0,0),
			(30,1,60),
			(30,2,61),
			(30,3,72),
			(30,4,max),

			(40,0,0),
			(40,1,66),
			(40,2,73),
			(40,3,max),
		];
		pat_loc.borrow_mut().add_col(Col::new(
			to_vf(pat_tuples.iter().map(|t| t.0).collect::<Vec<_>>()),
				"sorted_key", IDX_DATA)); 
		pat_loc.borrow_mut().add_col(Col::new(
			to_vf(pat_tuples.iter().map(|t| t.1).collect::<Vec<_>>()),
				"sorted_id", IDX_DATA)); 
		pat_loc.borrow_mut().add_col(Col::new(
			to_vf(pat_tuples.iter().map(|t| t.2).collect::<Vec<_>>()),
		   		 "sorted_val", IDX_DATA)); 
		let (to_add, res, prf) = sq.gen_forward_prf(&pat_loc, &steps_info);

		let b_details = true;
		if b_details{
			println!("DEBUG USE 50001: to_add");
			to_add.dump();
			println!("DEBUG USE 50002: res");
			res.dump();
			println!("DEBUG USE 50003: proof");
			prf.dump();
		}

		//vec100 is an example of all steps has something added
		//also new added can lead to new added for next step
		let vec100 = res.store_items.get(&Fr::from(100)).unwrap(); 
		let vec200 = res.store_items.get(&Fr::from(200)).unwrap();
		assert!(vec100[1].pat==Fr::from(2u32));
		assert!(vec100[1].locs==to_vf(vec![11,12,63])); //63 is added
		assert!(vec100[2].pat==Fr::from(3u32) && 
			vec100[2].locs==to_vf(vec![32,43,93])); //93 added due to 63
		assert!(vec100.len()==3); //all steps stretched

		//vec200 is an example of adding stops when no new can be added.
		//e.g., even if there are step 5 locations, but since there's no
		// step 4, none of them will be added.
		assert!(vec200[0].pat==Fr::from(0u32) && 
			vec200[0].locs==to_vf(vec![1u32]));
		assert!(vec200[1].pat==Fr::from(20u32) && 
			vec200[1].locs==to_vf(vec![22,30,51])); //51 is the added
		assert!(vec200[2].pat==Fr::from(30u32) &&
			vec200[2].locs==to_vf(vec![61]));  //(new layer)
		//none of layer4 can be added, also no layer5
		assert!(vec200.len()==3);
	}

	#[test]
	fn test_bwd_prf(){
		//1. construct input sequence
		// example 1: this is a full delete from the "last" step to
		// the first "step"
		// note: 60 elims 37, 47 will elims 16, 
		//      22 will eliminate 9 (layer 0 will not be affected)
		// keep it always (we need to prove the subsig free of match later)
		let subsig100_steps = vec![
			StepQueueItem::new2( 
				// subsig, id, pat, rg_start, rg_end
				to_vf(vec![100u32, 0, 0, 0, 0]), to_vf(vec![1u32])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 1, 2, 10, 100]), to_vf(vec![9u32, 12])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 2, 3, 10, 12]), to_vf(vec![16u32, 22])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 3, 4, 20, 30]), to_vf(vec![37,47,57])),
			StepQueueItem::new2( 
				to_vf(vec![100u32, 4, 5, 20, 22]), to_vf(vec![60u32])),
		];

		// example 2: entire empty proof  
		let subsig200_steps = vec![
			StepQueueItem::new2( 
				to_vf(vec![200u32, 0, 0, 0, 0]), to_vf(vec![1u32])),
			StepQueueItem::new2( 
				to_vf(vec![200u32, 1, 20, 20, 120]), to_vf(vec![22u32, 30])),
			StepQueueItem::new2( 
				to_vf(vec![200u32, 2, 30, 10, 20]), to_vf(vec![33u32])),
			StepQueueItem::new2( 
				to_vf(vec![200u32, 3, 40, 10, 10]), to_vf(vec![43u32])),
		];

		//3. partial del: up to step 3
		//60 elims 36, 37, 47 elims none. stops there.
		let subsig205_steps = vec![ //can't ues 300 as out of 256 bound
			//when RANGE2 is 8 bit
			StepQueueItem::new2( 
				// subsig, id, pat, rg_start, rg_end
				to_vf(vec![205u32, 0, 0, 0, 0]), to_vf(vec![1u32])),
			StepQueueItem::new2( 
				to_vf(vec![205u32, 1, 2, 10, 100]), to_vf(vec![12])),
			StepQueueItem::new2( 
				to_vf(vec![205u32, 2, 3, 10, 12]), to_vf(vec![22])),
			StepQueueItem::new2( 
				to_vf(vec![205u32, 3, 4, 20, 30]), to_vf(vec![36, 37,47,57])),
			StepQueueItem::new2( 
				to_vf(vec![205u32, 4, 5, 20, 22]), to_vf(vec![60u32])),
		];
		let subsigs = to_vf(vec![100,200,205]);
		let mut store_items = HashMap::new();
		store_items.insert(Fr::from(100u32), subsig100_steps);
		store_items.insert(Fr::from(200u32), subsig200_steps);
		store_items.insert(Fr::from(205u32), subsig205_steps);
		let capacity= DischargeAdvCapacity{
			max_nibble_len: 62, 
			subsigs: 4,
			avg_active_pats_per_subsig: 4,
			perc_pats_in_trace: 48,
		};
		let sq = StepQueue{subsigs, store_items, capacity: capacity.clone(),
			q_type: StepQueueType::Res};

		//2. test the backward proof
		let (to_remove, res, prf) = sq.gen_backward_prf();

		let b_details = true;
		if b_details{
			println!("==== DEBUG USE 50000: original ====");
			sq.dump();
			println!("==== DEBUG USE 50001: to_remove====");
			to_remove.dump();
			println!("==== DEBUG USE 50002: res ====");
			res.dump();
			println!("==== DEBUG USE 50003: proof ====");
			prf.dump();
		}

		//verif example 1: the proof goes down to level 2 (min possible)
		let vec100 = res.store_items.get(&Fr::from(100)).unwrap(); 
		assert!(vec100[1].pat==Fr::from(2u32));
		assert!(vec100[1].locs==to_vf(vec![12]));
		assert!(vec100[2].pat==Fr::from(3) && vec100[2].locs==to_vf(vec![22]));
		assert!(vec100[3].pat==Fr::from(4) 
			&& vec100[3].locs==to_vf(vec![47,57]));
		assert!(vec100[4].pat==Fr::from(5) && vec100[4].locs==to_vf(vec![60]));
		let prf100 = prf.store_items.get(&Fr::from(100)).unwrap();
		assert!(prf100[0].src_step==Fr::from(2)); 
		assert!(prf100.len()==3);

		//verif example 2: completely empty proof
		let vec200 = res.store_items.get(&Fr::from(200)).unwrap();
		assert!(vec200[1].pat==Fr::from(20) && 
			vec200[1].locs==to_vf(vec![22,30]));
		assert!(vec200[2].pat==Fr::from(30) && vec200[2].locs==to_vf(vec![33]));
		assert!(vec200[3].pat==Fr::from(40) && vec200[3].locs==to_vf(vec![43]));
		let prf200 = prf.store_items.get(&Fr::from(200)).unwrap();
		assert!(prf200.len()==0);

		//verif example 3: the proof goes down to step 3 (and stops there)
		let vec205 = res.store_items.get(&Fr::from(205)).unwrap();
		assert!(vec205[1].pat==Fr::from(2) && vec205[1].locs==to_vf(vec![12]));
		assert!(vec205[2].pat==Fr::from(3) && vec205[2].locs==to_vf(vec![22]));
		assert!(vec205[3].pat==Fr::from(4) && 
			vec205[3].locs==to_vf(vec![47,57]));
		assert!(vec205[4].pat==Fr::from(5) && vec205[4].locs==to_vf(vec![60]));
		let prf205 = prf.store_items.get(&Fr::from(205)).unwrap();
		assert!(prf205[0].src_step==Fr::from(4)); 
		assert!(prf205.len()==1);
	}


}


