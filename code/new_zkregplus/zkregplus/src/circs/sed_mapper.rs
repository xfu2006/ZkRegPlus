/* Created 03/18/2025
	Revised 02/23/2026: add separate capacity for case senstive
		and ignore case
*/

/* 
 A SED component mapper handles the SED approach. Later if ISED
 needs to be supported, its gadget mapper is essentially 1/2 of
 SED (as SED needs to support both igc and non-igc cases).
   Regarding ISED, to do later if needed.

 Its goal is to discharge a collection of signatures by SED/PM approach. 
 It operarates several gadgets for:
 (1) extract word to 4-bit nibbles (each converted to 248-bit 62 nibbles)
 (2) generating the trace given the input state and output the
       entire trace (fsm_adv_gadget), compared with fsm, each transition
		 has a location ID (their position in the trace), and then
		states are mapped to specific patterns for a subsignature.
	  In summary, it's generating a table of the following, which is
	  much smaller than the size of the trace:
	  	[subsig_id, pattern_id, location]
		where one subsig_id correpsonds to multiple pattern id,
		and one pattern ID corresponds to multpile locations (sorted).
 (3) A gadget which takes the projected trace table, given non-deterministic
    advices on the subsig to discharge, and run SED algorithm to
	to compute their stack of pattern matches
 (4) sed_conclusion gadget which extracts from clam_db the
     signature records, subsignature records. The circuit containing
     this gadget is ONLY INCLUDED.
	 It performs the calculation of tri-logic to determine the
	 value of subsigs based on SED stack for each. The result is
	 put into the output table.

Note we have two copies of (2) and (3), i.e., the fsm_adv and
discharge_subsig_adv (one for case sentive and one for ignore case).

 *** STRUCTURE of its statement is managed by the new col/container 
 architecture. 
 	(wd, inp, oup, data, si_inp, si_oup, si_data)
	where si_[seg] always match the [seg], e.g., |si_data| = |data|.

*/

use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{logger::{log, log_perf, LOG7, LOG1}, timer::Timer, consts::read_global_config };

use std::{
	marker::PhantomData,
	sync::{Arc, Mutex},
	
	fmt::{Debug},
	collections::{HashMap,HashSet},
};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{ Capacity,  SigmaGadget, StatementConfig, NdAdvice,WordInfo,LookupTableTwoCol,StatementExtraInfo,DischargeSigInfo},
		//circuits_super::field_to_usize,
		container_config::{ContainerConfig},
	}
};
//use crate::{composable_gadget_mapper::{ComponentGadgetMapper}};
use ark_ff::{PrimeField};
use crate::{
	circs::{composable_gadget_mapper::{ComponentMapper,
			ComponentMapperCloneBox}},
	gadgets::word_extract_adv::{WordExtractAdvCapacity, WordExtractAdvGadget, WordExtractAdvAdvice },
	gadgets::word_extract::{LEGS},
	gadgets::fsm_adv::{FsmAdvGadget,FsmAdvAdvice,FsmAdvCapacity},
	gadgets::discharge_adv::{DischargeAdvGadget,DischargeAdvAdvice,DischargeAdvCapacity,StepQueue, StepQueueType},
	gadgets::compute_sig_adv::{ComputeSigAdvCapacity,ComputeSigAdvAdvice,
		ComputeSigAdvGadget},
	gadgets::traits::{ComponentAdvice},
	//gadgets::commons::{print_vec}
};
use data_processor::{
	clam_db::{ClamavDB, 
	//CRIT_INIT, 	CRIT_IGC_INIT,
	//CHAR,
	 //CRIT_STATES, CRIT_IGC_STATES,
	//	CRIT_TRANSITIONS, CRIT_IGC_TRANSITIONS,
	//	CRIT_IGC_FINAL, CRIT_FINAL, 
	//	RANGE2
	},
	hex_acdfa::HexACDFA,
	type_def::{SubsigPatternStore, ClamavSig, SubsigStepStore,SubsigInfoStore}
};
use std::any::Any;

// --------------------------------------------------------
//		Structs
// --------------------------------------------------------

/// Component Capacity of the Cp Cmponent
#[derive(Clone,Debug)]
pub struct SedCapacity{
	// will contain capacities for word_extract_adv, fsm_adv ...
	pub comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>>,

	pub	max_word_len: usize, 
	pub	acdfa_state_part_bits: usize, 
	pub	subsigs: usize,
	pub	avg_pats_per_subsig: usize,
	pub	avg_active_pats_per_subsig: usize,
	pub	basis_pats_in_trace: usize, //0.01 percent
	pub perc_pats_expansion_rate: usize, //to model the rate of
		//pats staying over more than one segment of word
	pub	sigs_sed: usize, //for sed approach to discharge
	pub	perc_comp_subsigs: usize,
	pub basis_unique_states: usize, //basis points of unique states
		//extracted from all states of a path (usually this is < 0.5%)
	pub basis_acc_states: usize, //basis points of ALL accepted states
		//along the path (usually less than 5%, max 305)
}

/// Now the "official" capacity of the SedComponent
#[derive(Clone,Debug)]
pub struct SedCapacityCombo{
	// will contain capacities cs and igc
	pub comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>>,

	/// the capacity for components for the case sensitive part
	pub cs: SedCapacity,
	/// the capacity for components for the case sensitive insensitive part
	pub igc: SedCapacity,
}

/// Represent the structure of Input
#[derive(Clone,Debug)]
pub struct SedInput<F:PrimeField + ColEle>{
	/// input state case sensitive
	pub inp_state_cs: F,
	/// input location (case sensitive version)
	pub inp_loc_cs: F,
	/// the steps_queue for the discharge (case sensitive version)
	pub inp_steps_queue_cs: Vec<F>,

	/// input state for ignore case
	pub inp_state_igc: F,
	/// input location for ignore case
	pub inp_loc_igc: F,
	/// the steps_queue for the discharge for ignore case
	pub inp_steps_queue_igc: Vec<F>,
}

#[derive(Clone,Debug)]
pub struct SedComponentMapper<F:PrimeField + ColEle, LK: LookupTableTwoCol<F>>{ 
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub capacity: SedCapacityCombo,

	/// its own gadgets 
	///pub gadgets: Vec<Rc<dyn SigmaGadget<F> + Send + Sync + ContainerCompatible>>,
	pub gadgets: Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>,

	/// clamdb
	pub clamdb: Arc<ClamavDB<F>>,

	pub job_id: usize,
}


// --------------------------------------------------------
//		Implementations	
// --------------------------------------------------------



impl SedCapacity{
	pub fn new(
		max_word_len: usize, 
		acdfa_state_part_bits: usize, 
		subsigs: usize,
		avg_pats_per_subsig: usize,
		avg_active_pats_per_subsig: usize,
		basis_pats_in_trace: usize, //0.01 perc (basis points)
		perc_pats_expansion_rate: usize,
		sigs_sed: usize, //for sed approach to discharge
		perc_comp_subsigs: usize,
		basis_unique_states: usize,
		basis_acc_states: usize,
	)->Self{
		//REMOVE LATER ---------
		if basis_pats_in_trace==822{
			panic!("STOP HERE 100: basis pats is 822!");
		}
		//REMOVE LATER --------- ABOVE
		let wea_capacity = WordExtractAdvCapacity{max_word_len};
		let max_nibble_len = max_word_len * LEGS;
		let faa_capacity = FsmAdvCapacity{max_nibble_len, acdfa_state_part_bits,			subsigs, avg_pats_per_subsig, basis_pats_in_trace,
			basis_unique_states, basis_acc_states};
		let da_capacity = DischargeAdvCapacity{max_nibble_len, subsigs, avg_active_pats_per_subsig, basis_pats_in_trace, perc_pats_expansion_rate};
		//NOTE csa_capacity for the other cs/igc case will be temporarily
		//set and later merged (because one csa coresponds to two discharge
		//adv components
		let csa_capacity = ComputeSigAdvCapacity{
			subsigs_cs: subsigs, 
			subsigs_igc: subsigs, 
			sigs: sigs_sed, max_nibble_len,
			basis_pats_in_trace_cs: basis_pats_in_trace,
			basis_pats_in_trace_igc: basis_pats_in_trace, 
			perc_pats_expansion_rate_cs: perc_pats_expansion_rate,
			perc_pats_expansion_rate_igc: perc_pats_expansion_rate,
			perc_comp_subsigs};
			
		let comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>> = vec![
			Arc::new(wea_capacity),
			Arc::new(faa_capacity),
			Arc::new(da_capacity),
			Arc::new(csa_capacity),
		];

		Self{comp_capacities, max_word_len, acdfa_state_part_bits,
			subsigs, avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, sigs_sed, perc_comp_subsigs,
			basis_unique_states, basis_acc_states, perc_pats_expansion_rate}
	}

	/// level1: double the subsig and sig size
	/// level2: double the internal buf size
	pub fn increased_copy(&self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{//incrase subsigs and sigs
			Self::new(
				self.max_word_len,
				self.acdfa_state_part_bits,
				self.subsigs * 2,
				self.avg_pats_per_subsig,
				self.avg_active_pats_per_subsig,
				self.basis_pats_in_trace,
				self.perc_pats_expansion_rate,
				self.sigs_sed*2,
				self.perc_comp_subsigs,
				self.basis_unique_states,
				self.basis_acc_states,
			)
		}else{
			Self::new(
				self.max_word_len,
				self.acdfa_state_part_bits,
				self.subsigs,
				self.avg_pats_per_subsig*2,
				self.avg_active_pats_per_subsig*2,
				self.basis_pats_in_trace*2,
				self.perc_pats_expansion_rate*2,
				self.sigs_sed,
				self.perc_comp_subsigs*2,
				self.basis_unique_states*2,
				self.basis_acc_states*2,
			)
		}
	}

	pub fn decreased_copy(&self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{//incrase subsigs and sigs
			Self::new(
				self.max_word_len,
				self.acdfa_state_part_bits,
				(self.subsigs*3/4).max(read_global_config().min_subsigs),
				(self.avg_pats_per_subsig*3/4).max(read_global_config().min_avg_pats_per_subsig),
				(self.avg_active_pats_per_subsig*3/4).max(read_global_config().min_avg_active_pats_per_subsig),
				(self.basis_pats_in_trace/2).max(read_global_config().min_basis_pats_in_trace),
				(self.perc_pats_expansion_rate*3/4).max(read_global_config().min_perc_pats_expansion_rate),
				(self.sigs_sed*4/5).max(read_global_config().min_sigs_sed),
				(self.perc_comp_subsigs*3/4).max(read_global_config().min_perc_comp_subsigs),
				(self.basis_unique_states*3/4).max(read_global_config().min_basis_unique_states),
				(self.basis_acc_states/2).max(read_global_config().min_basis_acc_states),
			)
		}else{
			Self::new(
				self.max_word_len,
				self.acdfa_state_part_bits,
				(self.subsigs*3/4).max(read_global_config().min_subsigs),
				(self.avg_pats_per_subsig*3/4).max(read_global_config().min_avg_pats_per_subsig),
				(self.avg_active_pats_per_subsig*3/4).max(read_global_config().min_avg_active_pats_per_subsig),
				(self.basis_pats_in_trace/4).max(read_global_config().min_basis_pats_in_trace),
				(self.perc_pats_expansion_rate*3/4).max(read_global_config().min_perc_pats_expansion_rate),
				(self.sigs_sed*4/5).max(read_global_config().min_sigs_sed),
				(self.perc_comp_subsigs*3/4).max(read_global_config().min_perc_comp_subsigs),
				(self.basis_unique_states*3/4).max(read_global_config().min_basis_unique_states),
				(self.basis_acc_states/4).max(read_global_config().min_basis_acc_states),
			)
		}
	}

	/// syntax sugar for returning a reference to its wea_capacity
	pub fn wea_capacity(&self)->&WordExtractAdvCapacity{
		self.comp_capacities[0].as_any()
			.downcast_ref::<WordExtractAdvCapacity>().unwrap()
	}

	pub fn faa_capacity(&self)->&FsmAdvCapacity{
		self.comp_capacities[1].as_any()
			.downcast_ref::<FsmAdvCapacity>().unwrap()
	}

	pub fn da_capacity(&self)->&DischargeAdvCapacity{
		self.comp_capacities[2].as_any()
			.downcast_ref::<DischargeAdvCapacity>().unwrap()
	}

	pub fn csa_capacity(&self)->&ComputeSigAdvCapacity{
		self.comp_capacities[3].as_any()
			.downcast_ref::<ComputeSigAdvCapacity>().unwrap()
	}
}

impl Capacity for SedCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		
		let other = r_other.as_any().downcast_ref::<SedCapacity>()
			.expect("downcast err"); 
		assert!(self.comp_capacities.len()==other.comp_capacities.len());
		let mut res = true;
		for i in 0..self.comp_capacities.len(){
			res &= self.comp_capacities[i].can_satisfy(&
				other.comp_capacities[i]);
		}

		res
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(SedCapacity{
			comp_capacities: self.comp_capacities.clone(),
			max_word_len: self.max_word_len,
			acdfa_state_part_bits: self.acdfa_state_part_bits,
			subsigs: self.subsigs,
			avg_pats_per_subsig: self.avg_pats_per_subsig,
			avg_active_pats_per_subsig: self.avg_active_pats_per_subsig,
			basis_pats_in_trace: self.basis_pats_in_trace,
			perc_pats_expansion_rate: self.perc_pats_expansion_rate,
			sigs_sed: self.sigs_sed,
			perc_comp_subsigs: self.perc_comp_subsigs,
			basis_unique_states: self.basis_unique_states,
			basis_acc_states: self.basis_acc_states,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}
impl SedCapacityCombo{
	pub fn new(cs: &SedCapacity, igc: &SedCapacity)->Self{
		let comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>> = vec![
			Arc::new(Clone::clone(cs)),
			Arc::new(Clone::clone(igc)),
		];
		Self{comp_capacities, cs: Clone::clone(cs), igc: Clone::clone(igc)}
	}
}

impl Capacity for SedCapacityCombo{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		
		let other = r_other.as_any().downcast_ref::<SedCapacityCombo>()
			.expect("downcast err"); 
		assert!(self.comp_capacities.len()==other.comp_capacities.len());
		let mut res = true;
		for i in 0..self.comp_capacities.len(){
			res &= self.comp_capacities[i].can_satisfy(&
				other.comp_capacities[i]);
		}

		res
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(SedCapacityCombo::new(&self.cs, &self.igc))
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}


/// The non-deterministic advice for the CP component
#[derive(Debug)]
pub struct SedAdvice<F:PrimeField + ColEle>{
	pub wd_extract_advice: WordExtractAdvAdvice<F>,
	pub fsm_adv_advice_cs: FsmAdvAdvice<F>,
	pub fsm_adv_advice_igc: FsmAdvAdvice<F>,
	pub discharge_adv_advice_cs: DischargeAdvAdvice<F>,
	pub discharge_adv_advice_igc: DischargeAdvAdvice<F>,
	pub compute_sig_adv_advice: ComputeSigAdvAdvice<F>,

	pub vec_advices: Vec<Arc<dyn ComponentAdvice<F> + Send + Sync>>,

}

impl <F:PrimeField+ColEle> NdAdvice for SedAdvice<F>{
	fn as_any(&self) -> &dyn Any{ self }
}

impl <F:PrimeField+ColEle> SedAdvice<F>{
	/// from a collection of signatures collect the subsigs id
	/// return a vector of subsigs sorted.
	/// ONLY return the subsigs that match the b_igc
	pub fn collect_subsig_ids(
		vec_sigs_to_discharge: &Vec<Arc<ClamavSig>>, 
		discharge_info: &Vec<DischargeSigInfo>,
		sig_to_id: &HashMap<String,usize>,
		b_igc: bool, 
		dfa: &HexACDFA, //different dfa given the same input will actually
						//generate the same subsig_id. Actually not
						//needed, keep it fore legacy.
	)->Vec<F>{
		assert!(vec_sigs_to_discharge.len() == discharge_info.len());
		let set_subsigs_inp = vec_sigs_to_discharge.iter()
		.zip(discharge_info.iter())
		.map(|(sig,info)|{
			let sig_id = sig_to_id.get(&sig.name).expect(
				&format!("can't find sig: {}", sig.name));
			let f_subsig_ids = info.subsig_ids.iter()
			.filter(|&id|{
				sig.vec_subsig_obj[*id].b_ignore_case== b_igc
			}).map(|id|
				F::from(dfa.gen_subsig_id(*sig_id, *id+1) as u32)
			).collect::<Vec<F>>();

			f_subsig_ids
		}).flatten().collect::<Vec<F>>().iter().map(|x| x.clone())
		.collect::<HashSet<F>>();

		let mut subsigs_inp = set_subsigs_inp.iter().map(|x| x.clone()).
			collect::<Vec<F>>();
		subsigs_inp.sort();

		subsigs_inp
	}

	/// word seg must be full maxword len. The information:
	/// <dfa, vec_sigs, subsig_store, map_pattern_sig> are essentially
	/// one entry from the corresponding BundleSubsigs for one specific
	/// acdfa used for the SED. The others (word_seg to map_pattern_isg
	/// are global information.
	/// subsigs_to_discharge are the ones to discharge, retrieved from
	/// word info. We feed two separate copies of info (case sensitive
	/// and ignore csae). But the discharge_info is one copy (as
	///    we discharge subsigs separately, but the EvalDNF rule is
	///    the same for one sig).
	pub fn new(
			//1. global info
			word_seg: &Vec<F>, //must be full len pad with zero
			actual_size: usize,
			cs_capacity: &SedCapacity,
			igc_capacity: &SedCapacity,
			inp: &SedInput<F>,

			//2. needed for fsm_adv advice
			fsm_id_cs: u32, //acdfa id generated by pm_acdfa_id
			fsm_id_igc: u32, //for igc 
			dfa_cs: &HexACDFA, //the ACDFA used to find PM/bag words
			dfa_igc: &HexACDFA, //the ACDFA IGC version
			vec_sigs_to_discharge: &Vec<Arc<ClamavSig>>,  //common
			subsig_pat_store_cs: &SubsigPatternStore,//subsubsig store
			subsig_pat_store_igc: &SubsigPatternStore,//subsubsig store igc 
			subsig_step_store_cs: &SubsigStepStore,//steps store
			subsig_step_store_igc: &SubsigStepStore,//steps store
			subsig_info_store_cs: &SubsigInfoStore,//steps extra_info store
			subsig_info_store_igc: &SubsigInfoStore,//steps extra_info store
			sig_to_id: &HashMap<String,usize>, //map from sig to id (common)
			discharge_info: &Vec<DischargeSigInfo>, //info: (common)
			seg_id: usize,
			job_id: usize,
		)->Result<Self, Error>{
		let mut t1 = Timer::new();
		let b_perf = true;

		//1. build the word extraction gadget's advice
		let wd_extract_advice = WordExtractAdvAdvice::<F>
			::new(word_seg, actual_size, false)?; //default mode for char sid
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step1: word_extract", &mut t1); }

		//2. build the fsm_adv advice (cs and igc)
		assert!(vec_sigs_to_discharge.len()==discharge_info.len());
		let nibbles = wd_extract_advice.stmt_container.lock().unwrap().
			get_container("nibbles").expect("no nibbles").lock().unwrap().to_vec();
		let inp_sigs = vec_sigs_to_discharge.iter().map(|sig|{
			let sig_id = sig_to_id.get(&sig.name)
				.expect(&format!("can't find sig: {}", sig.name));
			F::from(*sig_id as u64)
		}).collect::<Vec<F>>();
		let fsm_cap_cs = &cs_capacity.faa_capacity();
		let fsm_cap_igc = &igc_capacity.faa_capacity();

		//2.1 the cs version
		let subsigs_inp_cs = Self::collect_subsig_ids(vec_sigs_to_discharge,
			discharge_info, sig_to_id, false, dfa_cs);
		let fsm_adv_advice_cs = FsmAdvAdvice::<F>
			::new(false, 1, //distance to word extract gadget 
				&nibbles,dfa_cs, inp.inp_state_cs,inp.inp_loc_cs,
				&subsigs_inp_cs, &fsm_cap_cs,fsm_id_cs as u32,
				subsig_pat_store_cs, job_id)?;
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step2: fsm_cs", &mut t1); }

		//2.2 the igc version
		let subsigs_inp_igc= Self::collect_subsig_ids(vec_sigs_to_discharge,
			discharge_info, sig_to_id, true, dfa_igc);
		let fsm_adv_advice_igc = FsmAdvAdvice::<F>
			::new(true, //igc
				2, //offset to word_extract
				&nibbles,dfa_igc, inp.inp_state_igc,inp.inp_loc_igc,
				&subsigs_inp_igc, &fsm_cap_igc, fsm_id_igc as u32,
				subsig_pat_store_igc, job_id)?;
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step3: fsm_igc", &mut t1); }

		//3. build the discharge_adv advice (cs and igc)
		let da_cap_cs = &cs_capacity.da_capacity();
		let da_cap_igc = &igc_capacity.da_capacity();
		//3.1 the cs version
		let pat_loc_cs = fsm_adv_advice_cs.stmt_container.lock().unwrap()
			.search_container("fsm_adv_stmt_cs packed_trace pat_loc sorted_tbl")
			.unwrap();
		let inp_steps_queue_obj_cs = StepQueue::parse_from(
			&inp.inp_steps_queue_cs, StepQueueType::ResSmall, 
			&da_cap_cs, false);
		let locs_cs = fsm_adv_advice_cs.stmt_container.lock().unwrap()
                        .search_container("fsm_adv_stmt_cs fsm_acc locs").unwrap()
                        .lock().unwrap().to_vec();
                let last_loc_cs = locs_cs[locs_cs.len()-1];
                let discharge_adv_advice_cs = DischargeAdvAdvice::<F>
                        ::new(false, 2, &pat_loc_cs, &subsigs_inp_cs, fsm_id_cs as u32, 
                                subsig_step_store_cs, &da_cap_cs, &inp_steps_queue_obj_cs, last_loc_cs,
				seg_id, job_id)?;
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step4: discharge_cs", &mut t1); }

		//3.2 the igc version
		let pat_loc_igc = fsm_adv_advice_igc.stmt_container.lock().unwrap()
			.search_container("fsm_adv_stmt_igc packed_trace pat_loc sorted_tbl").unwrap();
		let inp_steps_queue_obj_igc = StepQueue::parse_from(
			&inp.inp_steps_queue_igc, StepQueueType::ResSmall,
			&da_cap_igc, true);
		let locs_igc = fsm_adv_advice_igc.stmt_container.lock().unwrap()
                        .search_container("fsm_adv_stmt_igc fsm_acc locs").unwrap()
                        .lock().unwrap().to_vec();
                let last_loc_igc = locs_igc[locs_igc.len()-1];
                let discharge_adv_advice_igc = DischargeAdvAdvice::<F>
                        ::new(true, 2, &pat_loc_igc, &subsigs_inp_igc, fsm_id_igc as u32, 
                                subsig_step_store_igc, &da_cap_igc, &inp_steps_queue_obj_igc, last_loc_igc,
				seg_id, job_id)?;
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step5: discharge_igc", &mut t1); }


		//4. build the compute_sig advice  (note: just one copy)
		let csa_cap_igc = &igc_capacity.csa_capacity(); //typically this is the 
		let mut csa_cap: ComputeSigAdvCapacity = Clone::clone(&cs_capacity.csa_capacity()); //typically this is the 
				//larger one (since compute_sig component is small, 
				// we do not further refactor capacity ere
		csa_cap.basis_pats_in_trace_igc = csa_cap_igc.basis_pats_in_trace_igc;
		csa_cap.perc_pats_expansion_rate_igc= csa_cap_igc.perc_pats_expansion_rate_igc;
		csa_cap.subsigs_igc = csa_cap_igc.subsigs_igc;
		let stmt_disc_cs = &discharge_adv_advice_cs.stmt_container;
		let sq_res_cs = stmt_disc_cs.lock().unwrap().search_container("discharge_adv_stmt_cs bwd_steps_queue sq_res2").expect("sq_res err");
		let stmt_disc_igc = &discharge_adv_advice_igc.stmt_container;
		let sq_res_igc = stmt_disc_igc.lock().unwrap().search_container("discharge_adv_stmt_igc bwd_steps_queue sq_res2").expect("sq_res err");
		let compute_sig_adv_advice = ComputeSigAdvAdvice::<F>::new(
			fsm_id_cs as u32, fsm_id_igc as u32,
			&inp_sigs, 
			&subsigs_inp_cs, &subsigs_inp_igc,
			&discharge_info,
			&sq_res_cs, &sq_res_igc,
			&csa_cap,
			subsig_step_store_cs,  subsig_step_store_igc,
			subsig_info_store_cs, subsig_info_store_igc,
			vec_sigs_to_discharge, sig_to_id, job_id)?;

		//3. assemble all advices
		let vec_advices:Vec<Arc<dyn ComponentAdvice<F> + Send + Sync>> = vec![
			Arc::new(wd_extract_advice.clone()),
			Arc::new(fsm_adv_advice_cs.clone()),
			Arc::new(fsm_adv_advice_igc.clone()),
			Arc::new(discharge_adv_advice_cs.clone()),
			Arc::new(discharge_adv_advice_igc.clone()),
			Arc::new(compute_sig_adv_advice.clone()),
		];
		if b_perf{ log_perf(job_id, LOG1, "-- Sed advice step6: compute_sig", &mut t1); }

		Ok(Self{
			wd_extract_advice, 
			fsm_adv_advice_cs, fsm_adv_advice_igc, 
			discharge_adv_advice_cs, discharge_adv_advice_igc, 
			compute_sig_adv_advice,
			vec_advices
		})
	}
}


impl <F:PrimeField + ColEle,LK:LookupTableTwoCol<F>> SedComponentMapper<F,LK>{
	/// constructor needs the max word len to handle the capacity
	/// of PackFinal (number of final states), and reference to clamdb

	/// print details for a subsig step store
	fn print_subsig_details(subsig_id: usize, b_igc: bool, 
		store: &SubsigStepStore, acdfa: &HexACDFA){
		if let Some(item) = store.subsig_to_steps.get(&subsig_id){
			println!("--- DEBUG USE 6621: Subsig Details for ID: {}, IGC: {} ---", 
				subsig_id, b_igc);
			for (i, step) in item.vec_pm_bounds.iter().enumerate(){
				let pat_id = step.0;
				let (a, b) = step.1;
				let word = if pat_id < acdfa.patterns.len(){
					&acdfa.patterns[pat_id]
				} else {
					"UNKNOWN_PAT_ID"
				};
				println!("  Step {}: PatID: {}, Word: {}, Range: ({}, {})", 
					i + 1, pat_id, word, a, b);
			}
		}
	}

	pub fn new(
		cs_capacity: SedCapacity,
		igc_capacity: SedCapacity,
		clamdb: Arc<ClamavDB<F>>,
	) ->Self{
		let b_debug = false;
		let mut cfgs = vec![];
		//1. build the gadgets
		//1.1 the word extract gadget
		let g_wea = WordExtractAdvGadget::<F>::new(cs_capacity.wea_capacity().max_word_len, false); //default mode , same for cs and igc
		cfgs.push( g_wea.dummy_cfg.clone() );

		//1.2 the fsm adv gadget (2 gadgets)
		let bundle_cs = &clamdb.bundle_subsig;
		let bundle_igc = &clamdb.bundle_subsig_igc;
		let acdfa_cs = &bundle_cs.vec_acdfa[0]; //0 stands for all
		let acdfa_igc = &bundle_igc.vec_acdfa[0];
		let subsig_pat_store_cs = &bundle_cs.vec_subsig_stores[0];
		let subsig_pat_store_igc= &bundle_igc.vec_subsig_stores[0];
		let subsig_step_store_cs = &bundle_cs.vec_subsig_step_stores[0];
		let subsig_step_store_igc = &bundle_igc.vec_subsig_step_stores[0];

		//DEBUG: print details for target subsig
		if b_debug{
			let target_id = 36598786;
			Self::print_subsig_details(target_id, false, subsig_step_store_cs, acdfa_cs);
			Self::print_subsig_details(target_id, true, subsig_step_store_igc, acdfa_igc);
		}
		let subsig_info_store_cs = &bundle_cs.vec_subsig_info_stores[0];
		let subsig_info_store_igc = &bundle_igc.vec_subsig_info_stores[0];
		let sig_id = 0; //for all
		let fsm_id_cs = ClamavDB::<F>::pm_acdfa_id(sig_id, false); 
		let fsm_id_igc = ClamavDB::<F>::pm_acdfa_id(sig_id, true); 
		//let fsm_cap = FsmAdvCapacity{max_nibble_len: nlen, 
		//	acdfa_state_part_bits: state_bits};
		let fsm_cap_cs = &cs_capacity.faa_capacity();
		let g_faa_cs = FsmAdvGadget::<F>::new(false, 1, //dist to word extract
			acdfa_cs, &fsm_cap_cs, fsm_id_cs, &cfgs, subsig_pat_store_cs); 
		cfgs.push( g_faa_cs.dummy_cfg.clone() );

		let fsm_cap_igc = &igc_capacity.faa_capacity();
		let g_faa_igc = FsmAdvGadget::<F>::new(true, 2, //dist to wea
			acdfa_igc, &fsm_cap_igc, fsm_id_igc, &cfgs, subsig_pat_store_igc); 
		cfgs.push( g_faa_igc.dummy_cfg.clone() );

		//1.3. discharge_subsig (2 gadgets)
		let da_cap_cs = &cs_capacity.da_capacity();
		let da_cap_igc = &igc_capacity.da_capacity();
		let g_da_cs = DischargeAdvGadget::<F>::new(false, 2, &da_cap_cs, 
			fsm_id_cs, &cfgs, subsig_step_store_cs);
		cfgs.push( g_da_cs.dummy_cfg.clone() );

		let g_da_igc = DischargeAdvGadget::<F>::new(true, 2, &da_cap_igc, 
			fsm_id_igc, &cfgs, subsig_step_store_igc);
		cfgs.push( g_da_igc.dummy_cfg.clone() );

		//1.4 compute_sigs gadget (1 gadget)
		let csa_cap_igc = &igc_capacity.csa_capacity(); //typically this is the 
		let mut csa_cap:ComputeSigAdvCapacity = 
			Clone::clone(cs_capacity.csa_capacity()); //typically this is the 
				//larger one (since compute_sig component is small, 
				// we do not further refactor capacity ere
		csa_cap.basis_pats_in_trace_igc = csa_cap_igc.basis_pats_in_trace_igc;
		csa_cap.perc_pats_expansion_rate_igc= csa_cap_igc.perc_pats_expansion_rate_igc;
		csa_cap.subsigs_igc = csa_cap_igc.subsigs_igc;
		let g_csa = ComputeSigAdvGadget::<F>::new(
			fsm_id_cs, 
			fsm_id_igc, 
			&csa_cap, 
			&cfgs,
			subsig_step_store_cs, 
			subsig_step_store_igc, 
			subsig_info_store_cs,
			subsig_info_store_igc,
		);
		cfgs.push( g_csa.dummy_cfg.clone() );

		//2. build the gadgets
		let gadgets: Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>> = vec![ 
			Arc::new(Mutex::new(g_wea)), //word_extract_adv gadget
			Arc::new(Mutex::new(g_faa_cs)), //fsm_adv gadget
			Arc::new(Mutex::new(g_faa_igc)), //fsm_adv gadget
			Arc::new(Mutex::new(g_da_cs)), //discharge subsigs via SED
			Arc::new(Mutex::new(g_da_igc)), //discharge subsigs via SED
			Arc::new(Mutex::new(g_csa)), //compute_sig_gadget 
		];

		Self{
			_f: PhantomData, 
			_lk: PhantomData, 
			capacity: SedCapacityCombo::new(&cs_capacity, &igc_capacity),
			clamdb,
			gadgets,
			job_id: 0,
		}
	}

	
}

impl <F:PrimeField + ColEle + 'static, LK: LookupTableTwoCol<F> + Send + Sync + 'static> ComponentMapper<F,LK> for SedComponentMapper<F,LK>{
	fn set_container_config(&mut self, r_advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		let advice = r_advice.as_any().downcast_ref::<SedAdvice<F>>()
			.expect("downcast err!");
		assert!(self.gadgets.len()==advice.vec_advices.len());
		let mut vec_cfgs = vec![];
		for i in 0..self.gadgets.len(){
			let cta_cfg = advice.vec_advices[i].gen_raw_container_config();
			vec_cfgs.push(cta_cfg);
		}
		ContainerConfig::adjust_locations(&mut vec_cfgs);
		let rc_cfgs = Arc::new(vec_cfgs);
		for i in 0..self.gadgets.len(){
			self.gadgets[i].lock().unwrap().set_container_cfg(rc_cfgs.clone(), i);
		}
	}

	fn get_name(&self)->String {format!("SedMapper")}

	fn get_capacity(&self)->Arc<dyn Capacity + Send + Sync>{
		Arc::new( Clone::clone(&self.capacity) )
	}

	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
		for g in self.gadgets.iter(){
			g.lock().unwrap().set_job_id(job_id);
		}
	}

	fn get_job_id(&self)->usize{
		self.job_id
	}

	fn create_gadgets(&self) -> Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>{
  
		self.gadgets.clone()
	}

	/// return the number of gadgets
	fn num_gadgets(&self) -> usize{
		self.gadgets.len() 
	}

	/// return the max word capacity of the component
	fn max_word_len(&self)->usize{ 
		let n = self.capacity.cs.wea_capacity().max_word_len;
		assert!(self.capacity.igc.wea_capacity().max_word_len==n);

		n
	}

	/// genera the avice using its own capacity
	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		r_prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, seg_id: usize, _job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
		//1. expand word to full length
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word);
		if seg_id==0 {assert!(r_prev_adv.is_none());}

		//2. collect the data for building advice.
		//most vars have two versions: cs and igc
		//cs stands for case sensitive
		//igc stands for case insensitve
		let bundle_cs = &self.clamdb.bundle_subsig;
		let bundle_igc = &self.clamdb.bundle_subsig_igc;

		let pm_acdfa_cs = &bundle_cs.vec_acdfa[0]; //0 stands for all
		let pm_acdfa_igc= &bundle_igc.vec_acdfa[0];
		let sig_to_id = &self.clamdb.sig_to_id;
		let vec_sigs_to_discharge = 
			bundle_cs.vec_sigs[0].iter().filter(|s|{
				let id = sig_to_id.get(&s.name)
					.expect(&format!("can't find sig: {}", s.name));
				word_info.vec_sed_sigs.contains(id)
			}).map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();
	
		let subsig_pat_store_cs = &bundle_cs.vec_subsig_stores[0];
		let subsig_pat_store_igc = &bundle_igc.vec_subsig_stores[0];
		let subsig_step_store_cs = &bundle_cs
			.vec_subsig_step_stores[0];
		let subsig_step_store_igc = &bundle_igc
			.vec_subsig_step_stores[0];
		let subsig_info_store_cs = &bundle_cs
			.vec_subsig_info_stores[0];
		let subsig_info_store_igc = &bundle_igc
			.vec_subsig_info_stores[0];
		let discharge_info = word_info.vec_sed_sigs_info.clone();
		let sig_id = 0; //meaning discharge all
		let pm_fsm_id_cs = ClamavDB::<F>::pm_acdfa_id(sig_id, false);
		let pm_fsm_id_igc = ClamavDB::<F>::pm_acdfa_id(sig_id, true);

		//3. generate the inputs.
		//3.1 the case sensitive version
		let init_state_cs = F::from((pm_acdfa_cs.init_state+1) as u32); //adj +1
		let init_loc_cs = F::one();
		let inp_subsigs_cs: Vec<F>= SedAdvice
			::collect_subsig_ids(&vec_sigs_to_discharge, 
				&discharge_info, sig_to_id, false, &pm_acdfa_cs);
		let init_steps_queue_cs = DischargeAdvAdvice
			::gen_empty_steps_queue_serialized(
				false, //b_igc = false
				&inp_subsigs_cs,
				&subsig_step_store_cs,
				pm_fsm_id_cs,
				&self.capacity.cs.da_capacity()
			).to_vec(&subsig_step_store_cs)?; //it's ok even with capacity
				//it's just to pass it as data member, will not crash
				//if lack of capacity


		let (inp_state_cs, inp_loc_cs, inp_steps_queue_cs) = r_prev_adv
		.as_ref().map_or(
			(init_state_cs, init_loc_cs, init_steps_queue_cs), |adv|{
				let adv= adv.as_any().downcast_ref::<SedAdvice<F>>(); 
				let fsm_adv_advice_cs= &adv.unwrap().fsm_adv_advice_cs;
				let states_cs = fsm_adv_advice_cs.stmt_container.lock().unwrap()
					.search_container("fsm_adv_stmt_cs fsm_acc states").unwrap()
					.lock().unwrap().to_vec();
				let last_oup_state_cs = states_cs[states_cs.len()-1]; //adjusted
				let locs_cs = fsm_adv_advice_cs.stmt_container.lock().unwrap()
					.search_container("fsm_adv_stmt_cs fsm_acc locs").unwrap()
					.lock().unwrap().to_vec();
				let last_loc_cs = locs_cs[locs_cs.len()-1];
				let da_adv_cs = &adv.unwrap().discharge_adv_advice_cs;
				let last_steps_queue_cs = da_adv_cs.get_output_steps_queue();
				(last_oup_state_cs, last_loc_cs, last_steps_queue_cs.to_vec())
			}
		);

		//3.2 the ignore case version 
		let init_state_igc = F::from((pm_acdfa_igc.init_state+1) as u32);//adj+1
		let init_loc_igc = F::one();
		let inp_subsigs_igc: Vec<F>= SedAdvice
			::collect_subsig_ids(&vec_sigs_to_discharge, 
				&discharge_info, sig_to_id, true, &pm_acdfa_igc);
		let init_steps_queue_igc = DischargeAdvAdvice
			::gen_empty_steps_queue_serialized(
				true, //b_igc
				&inp_subsigs_igc,
				&subsig_step_store_igc,
				pm_fsm_id_igc,
				&self.capacity.igc.da_capacity()
			).to_vec(&subsig_step_store_igc)?;

		let (inp_state_igc, inp_loc_igc, inp_steps_queue_igc) = r_prev_adv
		.as_ref().map_or(
			(init_state_igc, init_loc_igc, init_steps_queue_igc), |adv|{
				let adv= adv.as_any().downcast_ref::<SedAdvice<F>>(); 
				let fsm_adv_advice_igc= &adv.unwrap().fsm_adv_advice_igc;
				let states_igc = fsm_adv_advice_igc.stmt_container.lock().unwrap()
					.search_container("fsm_adv_stmt_igc fsm_acc states")
					.unwrap().lock().unwrap().to_vec();
				let last_oup_state_igc = states_igc[states_igc.len()-1]; 
				let locs_igc = fsm_adv_advice_igc.stmt_container.lock().unwrap()
					.search_container("fsm_adv_stmt_igc fsm_acc locs").unwrap()
					.lock().unwrap().to_vec();
				let last_loc_igc = locs_igc[locs_igc.len()-1];
				let da_adv_igc = &adv.unwrap().discharge_adv_advice_igc;
				let last_steps_queue_igc = da_adv_igc.get_output_steps_queue();
				(last_oup_state_igc,last_loc_igc,last_steps_queue_igc.to_vec())
			}
		);

		//3. build the advice
		let inp = SedInput{inp_state_cs, inp_loc_cs, inp_steps_queue_cs,
			inp_state_igc, inp_loc_igc, inp_steps_queue_igc};


		let advice = SedAdvice::<F>::new(
			&word_seg, 
			word.len(), 
			&self.capacity.cs, 
			&self.capacity.igc, 
			&inp, 

			pm_fsm_id_cs,
			pm_fsm_id_igc,
			pm_acdfa_cs,
			pm_acdfa_igc,
			&vec_sigs_to_discharge,
			subsig_pat_store_cs,
			subsig_pat_store_igc,
			subsig_step_store_cs,
			subsig_step_store_igc,
			subsig_info_store_cs,
			subsig_info_store_igc,
			&self.clamdb.sig_to_id,
			&discharge_info,
			seg_id,
			_job_id
			)?;

		Ok( Arc::new(advice) )

	}

	/// return the sizes of inp, oup, data buffer, failed_sigs, discharged_sigs
	fn get_sizes(&self)->Vec<usize>{
		let log_level = LOG7;
		let b_perf = true && log_level>=read_global_config().log_level;
		if b_perf{
			log(self.job_id, log_level, &format!(" ## sed gadgets data len: ==="));
			for i in 0..self.gadgets.len(){
				let vs = self.gadgets[i].lock().unwrap().get_to_add_size();
				log(self.job_id, log_level, &format!("  --  {}: {}",
					self.gadgets[i].lock().unwrap().get_name(), vs.2));
			}
		}
		let sizes = self.gadgets.iter().map(|g| g.lock().unwrap().get_to_add_size())
			.collect::<Vec<(usize, usize, usize, usize, usize)>>();
		let total = sizes.into_iter().fold((0,0,0,0,0), |x,y|
			(x.0+y.0, x.1+y.1, x.2+y.2, x.3+y.3, x.4+y.4));
		vec![total.0, total.1, total.2, total.3, total.4]
	}

	/// return the ``global" join constraints, so that
	/// it can generate constraints to bind its own statement elements
	/// with others. the comp_cfgs has the following structure,
	/// (inp_start_idx, oup_start_idx, data_start_idx) for each component
	/// in the upper level statement.
	/// The join statement are ``global" in the sense that
	/// they refer to the global position.
	/// i - informs the component that it is the i'th component
	/// stmg_cfg provides statement structure info.
	/// cmp_cfgs: each tuple is (idx_inp, idx_oup, idx_data) for each component.
	fn get_joins(&self, i: usize, stmt_cfg: &StatementConfig, comp_cfgs: &Vec<Vec<usize>>)->Vec<((usize,usize), (usize,usize))>{
		//1. the data[0] of g_ext needs to be act_word_len
		let my_cfg = &comp_cfgs[i];
		let idx_my_data = my_cfg[2]; //0: inp_start_idx,1: oup_start_idx, 2:dat
		let idx_g_ext_data = idx_my_data + stmt_cfg.idx_data;
		let idx_act_wlen = 7; //the idx of act_word_subseg_size in Statement
		let rg_g_ext = (idx_g_ext_data, idx_g_ext_data); //just 1 element
		let rg_g_ext_upper = (idx_act_wlen, idx_act_wlen);

		//2. no join for fsm_adv and discharge_adv
		vec![ (rg_g_ext, rg_g_ext_upper) ]
	}


	/// Given its own gadget stmt_map: 9 range entries for:
	///   word, inp,oup,data,
	///   subtbl_inp, subtbl_oup, subtbl_data 
	///   failed_sigs, discharged_sigs
	/// return the map entries for each of its gadgets for reconstructing
	/// their problem statement(note:
	///    entries solely depending on the gadget's own structure, need
	///    to read each gadget's doc for its statement structure)
	/// Return then three Vec<(col_size, if_const)> for data, inp, oup
	fn get_gadgets_stmt_map(&self, vec_alloc: &Vec<(usize,usize)>)
	->(Vec<Vec<(usize,usize)>>, Vec<(usize,bool)>, 
		Vec<(usize,bool)>, Vec<(usize,bool)>){
		//1. get the allocation and make sure not exceeding boundaries
		assert!(vec_alloc.len()==9); 
		let (s_wd, e_wd) = vec_alloc[0];
		let (s_inp, _e_inp) = vec_alloc[1];
		let (s_oup, _e_oup) = vec_alloc[2];
		let (s_data, _e_data) = vec_alloc[3];
		let (s_subtbl_inp, e_subtbl_inp) = vec_alloc[4];
		let (s_subtbl_oup, e_subtbl_oup) = vec_alloc[5];
		let (s_subtbl_data, e_subtbl_data_end) = vec_alloc[6];
		let (s_failed_sigs, _e_failed_sigs) = vec_alloc[7];
		let (s_discharged_sigs, _e_discharged_sigs) = vec_alloc[8];
		let wlen = self.max_word_len();
		assert!(e_wd - s_wd + 1 == wlen);
		let mut vec_res= vec![];

		//start positions for:
		// word, inp, oup, data, 
		// subtbl_id_inp, subtbl_id_oup, subtbl_id_data
		// failed_sigs, discharged_sigs,
		// where subtbl_xyz matches syz size
		let mut seg_starts = vec![
			vec![
				s_wd, s_inp, s_oup, s_data, 
				s_subtbl_inp, s_subtbl_oup, s_subtbl_data,
				s_failed_sigs, s_discharged_sigs, 
			]
		];

		//2. based on seg_starts construct map instruction
		let mut vec_si_data_info = vec![];
		let mut vec_si_inp_info = vec![];
		let mut vec_si_oup_info = vec![];
		for i in 0..self.gadgets.len(){
			//2.1. collect maps
			let instructions = self.gadgets[i].lock().unwrap()
				.get_stmt_map_instructions();
			let my_maps = instructions.into_iter().map(|instruction|{
				let (_gadget_offset, seg_id, start, len) = instruction;
				//let idx_gadget = ((i as i32) + gadget_offset) as usize;
				//it's already adjusted by adjust_locations of
				//container_config, so there is no need to perform adjust
				let res = (seg_starts[0][seg_id] + start, 
					seg_starts[0][seg_id] + start + len -1);

				res
			}).collect::<Vec<(usize,usize)>>();
			let ns = self.gadgets[i].lock().unwrap().get_to_add_size();
			// ns corresponds to 9 elements in sequence below:
			// word, inp, oup, data
			// sid_inp, sid_opu, sid_data
			// failed_sigs, discharged_sigs
			let ns = vec![0, ns.0, ns.1, ns.2, ns.0, ns.1, ns.2, ns.3, ns.4]; 
			let mut nxt_starts = seg_starts[seg_starts.len()-1].clone();
			assert!(ns.len()==nxt_starts.len() && ns.len()==9);
			for j in 0..9 {nxt_starts[j] += ns[j];}
			seg_starts.push(nxt_starts);
			vec_res.push(my_maps);

			let (si_data_info, si_inp_info, si_oup_info) = 
				self.gadgets[i].lock().unwrap()
				.get_container_config().gen_si_info();
			vec_si_data_info.push(si_data_info);
			vec_si_inp_info.push(si_inp_info);
			vec_si_oup_info.push(si_oup_info);
		}

		assert!(vec_res.len()==self.num_gadgets());
		let vec_si_data_info = vec_si_data_info.concat();
		let vec_si_inp_info = vec_si_inp_info.concat();
		let vec_si_oup_info = vec_si_oup_info.concat();
		let total_si_info_data_len = vec_si_data_info.iter().map(|(s,_)| s)
			.sum::<usize>();
		let total_si_info_inp_len = vec_si_inp_info.iter().map(|(s,_)| s)
			.sum::<usize>();
		let total_si_info_oup_len = vec_si_oup_info.iter().map(|(s,_)| s)
			.sum::<usize>();
		let total_si_data_len = e_subtbl_data_end-s_subtbl_data+1;
		let total_si_inp_len = e_subtbl_inp-s_subtbl_inp+1;
		let total_si_oup_len = e_subtbl_oup-s_subtbl_oup+1;
		assert!(total_si_info_data_len==total_si_data_len);
		assert!(total_si_info_inp_len==total_si_inp_len);
		assert!(total_si_info_oup_len==total_si_oup_len);

		(vec_res, vec_si_data_info, vec_si_inp_info, vec_si_oup_info)
	}

	/// return the inp, oup, data and 3 subtable segments, and
	/// then failed_sigs and discharge_sigs. (8 vecs)
	/// the id, cfg, and comp_mapping helps it to locate the information
	/// it needs in prev_stmt which has the same structure as specified
	/// in StatementConfig. Note we pass the max len word, padded.
	/// the actual_word_len indicates the actual word seg in the word_seg.
	///
	/// NOTE: comp_id refers to the component, stmt_map_id refers
	/// to the starting index of FIRST of its gadget in the stma_mapping.
	/// e.g., let's say there are two components with 2 and 3 gadgets,
	/// the the comp_id for the 2nd is 1, and its stmt_map_id is 2. (idx
	/// starting from 0). For conveneince, we sometimes use
	/// the prev_stmt or the vector of its prev_stmt.
	fn build_statement_comp(&self, _comp_id: usize, _stmt_map_id: usize, _word_seg: &Vec<F>, _actual_word_len: usize, _lkup: &Arc<LK>, _extra_info: &StatementExtraInfo<F>, advice: &Arc<dyn NdAdvice + Send + Sync>, _cfg: &StatementConfig, _stmt_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>{
		let log_level = LOG7;
		let b_perf = log_level >= read_global_config().log_level;
		//1. take the advice
		let advice = advice.as_any().downcast_ref::<SedAdvice<F>>()
			.expect("downcast err!");
		
		let res = advice.vec_advices.iter().fold(
			vec![vec![]; 8],
			|sum, adv|{
				let cps = adv.gen_stmt_components();
				assert!(cps.len()==8);
				sum.into_iter().zip(cps.into_iter()).map(|(a,b)|{
					let res:Vec<F> = vec![a, b].concat();
					res
				}).collect::<Vec<Vec<F>>>()
			}
		);

		if b_perf{
			log(0, log_level, &format!("## build_stmt: SED failed sigs"));
			for i in 0..res[6].len(){
				log(0, log_level, &format!(" -- {} => {}",
					i, &res[6][i]));
			}
			log(0, log_level, &format!("## build_stmt: SED discharged sigs"));
			for i in 0..res[7].len(){
				log(0, log_level, &format!(" -- {} => {}",
					i, &res[7][i]));
			}
		}

		assert!(res.len()==8);
		Ok( res )
	}
}

impl <F:PrimeField + ColEle, LK: LookupTableTwoCol<F> + Send + Sync + 'static>
	ComponentMapperCloneBox<F,LK> for SedComponentMapper<F,LK>
where F: 'static,
{
	fn clone_arc_component_mapper(&self)
		-> Arc<Mutex<dyn ComponentMapper<F,LK> + Send + Sync>> {
		let new_gadgets: Vec<Arc<Mutex<
			dyn SigmaGadget<F> + Send + Sync>>> =
			self.gadgets.iter().map(|g|
				g.lock().unwrap().clone_arc_sigma_gadget()
			).collect();
		Arc::new(Mutex::new(SedComponentMapper::<F,LK>{
			_f: PhantomData,
			_lk: PhantomData,
			capacity: Clone::clone(&self.capacity),
			gadgets: new_gadgets,
			clamdb: self.clamdb.clone(),
			job_id: self.job_id,
		}))
	}
}
