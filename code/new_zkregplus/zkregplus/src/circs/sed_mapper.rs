/* Created 03/18/2025
*/

/*!
 A SED component mapper handles the SED approach, and it can be
 used to handle ISED approach.
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
    advices on the subsig to discharge, and run SED/ISED algorithm to
	to compute their stack of pattern matches
 (5) [optional at the LAST word segment for a word] 
     sed_conclusion gadget which extracts from clam_db the
     signature records, subsignature records. The circuit containing
     this gadget is ONLY INCLUDED.
	 It performs the calculation of tri-logic to determine the
	 value of subsigs based on SED stack for each. The result is
	 put into the output table.

 *** STRUCTURE of its statement is managed by the new col/container 
 architecture. 
 	(wd, inp, oup, data, si_inp, si_oup, si_data)
	where si_[seg] always match the [seg], e.g., |si_data| = |data|.

*/

use std::{
	marker::PhantomData,
	rc::{Rc},
	sync::{Arc},
	cell::{RefCell},
	fmt::{Debug},
	collections::{HashMap,HashSet},
};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{ Capacity,  SigmaGadget, StatementConfig, NdAdvice,WordInfo,LookupTableTwoCol,StatementInst,StatementExtraInfo,DischargeSigInfo},
		//circuits_super::field_to_usize,
		container_config::{ContainerConfig},
	}
};
//use crate::{composable_gadget_mapper::{ComponentGadgetMapper}};
use ark_ff::{PrimeField};
use crate::{
	circs::composable_gadget_mapper::ComponentMapper,
	gadgets::word_extract_adv::{WordExtractAdvCapacity, WordExtractAdvGadget, WordExtractAdvAdvice },
	gadgets::word_extract::{LEGS},
	gadgets::fsm_adv::{FsmAdvGadget,FsmAdvAdvice,FsmAdvCapacity},
	gadgets::discharge_adv::{DischargeAdvGadget,DischargeAdvAdvice,DischargeAdvCapacity,StepQueue},
	gadgets::compute_sig_adv::{ComputeSigAdvCapacity,ComputeSigAdvAdvice,
		ComputeSigAdvGadget},
	//gadgets::pack::{PackFinalGadget,PackFinalAdvice},
	//gadgets::sigs::{GetSigAdvice,SigGadgetCapacity,SigGadgetData,GetSigGadget},
	gadgets::traits::{
		ComponentAdvice 
	},
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

/// Capacity of the Cp Cmponent
#[derive(Clone,Debug)]
pub struct SedCapacity{
	// will contain capacities for word_extract_adv, fsm_adv ...
	pub comp_capacities: Vec<Rc<dyn Capacity>>,
}

/// Represent the structure of Input
#[derive(Clone,Debug)]
pub struct SedInput<F:PrimeField>{
	/// input state
	pub inp_state: F,
	/// input location
	pub inp_loc: F,
	/// the steps_queue for the discharge
	pub inp_steps_queue: Vec<F>,
}

#[derive(Clone,Debug)]
pub struct SedComponentMapper<F:PrimeField, LK: LookupTableTwoCol<F>>{ 
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub capacity: SedCapacity,

	/// true if it's for ignore case
	pub b_igc: bool,
	/// which store in BundleSubsigStore to use.
	/// here '0' is for SED case where a collection of sigs to discharge.
	/// 'i>0" is for ISED case for a specific
	/// sig to be discharged individually
	pub store_id: usize,

	/// its own gadgets 
	///pub gadgets: Vec<Rc<dyn SigmaGadget<F> + ContainerCompatible>>,
	pub gadgets: Vec<Rc<RefCell<dyn SigmaGadget<F>>>>,

	/// clamdb
	pub clamdb: Rc<ClamavDB<F>>,
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
		perc_pats_in_trace: usize,
		sigs_sed: usize, //for sed approach to discharge
		perc_comp_subsigs: usize,
	)->Self{
		let wea_capacity = WordExtractAdvCapacity{max_word_len};
		let max_nibble_len = max_word_len * LEGS;
		let faa_capacity = FsmAdvCapacity{max_nibble_len, acdfa_state_part_bits,			subsigs, avg_pats_per_subsig, perc_pats_in_trace};
		let da_capacity = DischargeAdvCapacity{max_nibble_len, subsigs, avg_active_pats_per_subsig, perc_pats_in_trace};
		let csa_capacity = ComputeSigAdvCapacity{subsigs, sigs: sigs_sed, max_nibble_len,
			perc_pats_in_trace, perc_comp_subsigs};
			
		let comp_capacities: Vec<Rc<dyn Capacity>> = vec![
			Rc::new(wea_capacity),
			Rc::new(faa_capacity),
			Rc::new(da_capacity),
			Rc::new(csa_capacity),
		];

		Self{comp_capacities}
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
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		
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
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(SedCapacity{
			comp_capacities: self.comp_capacities.clone()
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

/// The non-deterministic advice for the CP component
pub struct SedAdvice<F:PrimeField>{
	pub wd_extract_advice: WordExtractAdvAdvice<F>,
	pub fsm_adv_advice: FsmAdvAdvice<F>,
	pub discharge_adv_advice: DischargeAdvAdvice<F>,
	pub compute_sig_adv_advice: ComputeSigAdvAdvice<F>,

	pub vec_advices: Vec<Rc<dyn ComponentAdvice<F>>>,

}

impl <F:PrimeField> NdAdvice for SedAdvice<F>{
	fn as_any(&self) -> &dyn Any{ self }
}

impl <F:PrimeField> SedAdvice<F>{
	/// from a collection of signatures collect the subsigs id
	/// return a vector of subsigs sorted.
	fn collect_subsig_ids(
		vec_sigs_to_discharge: &Vec<Arc<ClamavSig>>, 
		discharge_info: &Vec<DischargeSigInfo>,
		sig_to_id: &HashMap<String,usize>,
		b_igc: bool,
		dfa: &HexACDFA 
	)->Vec<F>{
		assert!(vec_sigs_to_discharge.len() == discharge_info.len());
		let set_subsigs_inp = vec_sigs_to_discharge.iter()
		.zip(discharge_info.iter())
		.map(|(sig,info)|{
			let sig_id = sig_to_id.get(&sig.name).expect(
				&format!("can't find sig: {}", sig.name));
			let f_subsig_ids = info.subsig_ids.iter()
			.filter(|id|
				sig.vec_subsig_obj[**id].b_ignore_case==b_igc
			).map(|id|
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
	/// acdfa used for the SED/ISED. The others (word_seg to map_pattern_isg
	/// are global information.
	/// subsigs_to_discharge are the ones to discharge, retrieved from
	/// word info. 
	pub fn new(
			//1. global info
			b_igc: bool, //whether this is for ignore case or not
			word_seg: &Vec<F>, //must be full len pad with zero
			actual_size: usize,
			capacity: &SedCapacity,
			inp: &SedInput<F>,

			//2. needed for fsm_adv advice
			fsm_id: u32, //acdfa id generated by pm_acdfa_id
			dfa: &HexACDFA, //the ACDFA used to find PM/bag words
			vec_sigs_to_discharge: &Vec<Arc<ClamavSig>>, //the sigs to 
				//discharge, SED case there are MULTIPLE,
				//ISED case, there is ONLY 1. (when store_id>1)
			subsig_pat_store: &SubsigPatternStore,//subsubsig store
			subsig_step_store: &SubsigStepStore,//steps store
			subsig_info_store: &SubsigInfoStore,//steps extra_info store
			sig_to_id: &HashMap<String,usize>, //map from sig to id
			discharge_info: &Vec<DischargeSigInfo>, //info: subsigs to process
		)->Self{
		//1. build the word extraction gadget's advice
		let wd_extract_advice = WordExtractAdvAdvice::<F>
			::new(word_seg, actual_size);

		//2. build the fsm_adv advice
		let nibbles = wd_extract_advice.stmt_container.borrow().
			get_container("nibbles").expect("no nibbles").borrow().to_vec();
		assert!(vec_sigs_to_discharge.len()==discharge_info.len());
		println!("DEBUG USE 200: dis_charge_info: {:?}", discharge_info);
		println!("DEBUG USE 201: vec_sigs_to_discharge: {:?}", vec_sigs_to_discharge);
		println!("DEBUG USE 202: vec_sigs_to_discharge: {:?}, fsm_id: {}", vec_sigs_to_discharge, fsm_id);

		//if 1>0 {panic!("DEBUG USE 101: subsigs to process: {:?}", subsigs_inp);}
		let subsigs_inp = Self::collect_subsig_ids(vec_sigs_to_discharge,
			discharge_info, sig_to_id, b_igc, dfa);
		let inp_sigs = vec_sigs_to_discharge.iter().map(|sig|{
			let sig_id = sig_to_id.get(&sig.name)
				.expect(&format!("can't find sig: {}", sig.name));
			F::from(*sig_id as u64)
		}).collect::<Vec<F>>();

		let fsm_cap = &capacity.faa_capacity();
		let fsm_adv_advice = FsmAdvAdvice::<F>
			::new(&nibbles,dfa, inp.inp_state,inp.inp_loc,
				&subsigs_inp, &fsm_cap,fsm_id as u32,
				subsig_pat_store);

		let da_cap = &capacity.da_capacity();
		let pat_loc = fsm_adv_advice.stmt_container.borrow()
			.search_container("fsm_adv_stmt packed_trace pat_loc sorted_tbl")
			.unwrap();
		let inp_steps_queue_obj = StepQueue::parse_from(&inp.inp_steps_queue, 
			&da_cap);
		let discharge_adv_advice = DischargeAdvAdvice::<F>
			::new(&pat_loc, &subsigs_inp, fsm_id as u32, 
				subsig_step_store, &da_cap, &inp_steps_queue_obj);

		let csa_cap = &capacity.csa_capacity();
		let stmt_disc = &discharge_adv_advice.stmt_container;
		let sq_res = stmt_disc.borrow().search_container("discharge_adv_stmt bwd_steps_queue sq_res2").expect("sq_res err");
		let compute_sig_adv_advice = ComputeSigAdvAdvice::<F>::new(
			fsm_id as u32, &inp_sigs, &subsigs_inp, &discharge_info,
				&sq_res, Clone::clone(&csa_cap), subsig_step_store, 
				subsig_info_store, vec_sigs_to_discharge, sig_to_id);

		//3. assemble all advices
		let vec_advices:Vec<Rc<dyn ComponentAdvice<F>>> = vec![
			Rc::new(wd_extract_advice.clone()),
			Rc::new(fsm_adv_advice.clone()),
			Rc::new(discharge_adv_advice.clone()),
			Rc::new(compute_sig_adv_advice.clone()),
		];

		Self{wd_extract_advice, fsm_adv_advice, discharge_adv_advice, 
			compute_sig_adv_advice,
			vec_advices
		}
	}
}


impl <F:PrimeField,LK:LookupTableTwoCol<F>> SedComponentMapper<F,LK>{
	/// constructor needs the max word len to handle the capacity
	/// of PackFinal (number of final states), and reference to clamdb

	pub fn new(
		sed_capacity: SedCapacity,
		clamdb: Rc<ClamavDB<F>>,
		b_igc: bool, //whether it's for ignore case ACDFA
		store_id: usize, //0 means 'all' (SED), after 1 it's the sig ID for ISED
	) ->Self{
		let mut cfgs = vec![];
		//1. build the gadgets
		//1.1 the word extract gadget
		let g_wea = WordExtractAdvGadget::<F>::new(sed_capacity.wea_capacity().max_word_len);
		cfgs.push( g_wea.dummy_cfg.clone() );

		//1.2 the fsm adv gadget
		let bundle = if b_igc {&clamdb.bundle_subsig_igc}
			else {&clamdb.bundle_subsig};
		let acdfa = &bundle.vec_acdfa[store_id];
		let subsig_pat_store = &bundle.vec_subsig_stores[store_id];
		let subsig_step_store = &bundle.vec_subsig_step_stores[store_id];
		let subsig_info_store = &bundle.vec_subsig_info_stores[store_id];
		let sig_id = if store_id==0{ 0 } else{//ised case
			let sig_name = &bundle.vec_sig_names[store_id];
			*clamdb.sig_to_id.get(sig_name).expect(
				&format!("Cant find sig {}", sig_name))
		}; //sig_id of the sig being discarged. store_id==0 is `all`
		let fsm_id = ClamavDB::<F>::pm_acdfa_id(sig_id, b_igc); 
		//let fsm_cap = FsmAdvCapacity{max_nibble_len: nlen, 
		//	acdfa_state_part_bits: state_bits};
		let fsm_cap = &sed_capacity.faa_capacity();
		let g_faa = FsmAdvGadget::<F>::new(acdfa, &fsm_cap, fsm_id, &cfgs, 
			subsig_pat_store); 
		cfgs.push( g_faa.dummy_cfg.clone() );

		let da_cap = &sed_capacity.da_capacity();
		let g_da = DischargeAdvGadget::<F>::new(&da_cap, fsm_id,
			&cfgs, subsig_step_store);
		cfgs.push( g_da.dummy_cfg.clone() );

		let csa_cap = &sed_capacity.csa_capacity();
		let g_csa = ComputeSigAdvGadget::<F>::new(
			fsm_id, &csa_cap, &cfgs,
			subsig_step_store, subsig_info_store);
		cfgs.push( g_csa.dummy_cfg.clone() );

		let gadgets: Vec<Rc<RefCell<dyn SigmaGadget<F>>>> = vec![ 
			Rc::new(RefCell::new(g_wea)), //word_extract_adv gadget
			Rc::new(RefCell::new(g_faa)), //fsm_adv gadget
			Rc::new(RefCell::new(g_da)), //discharge subsigs via SED
			Rc::new(RefCell::new(g_csa)), //compute_sig_gadget 
		];

		Self{
			_f: PhantomData, 
			_lk: PhantomData, 
			capacity: sed_capacity,
			b_igc,
			clamdb,
			gadgets,
			store_id
		}
	}
}

impl <F:PrimeField, LK: LookupTableTwoCol<F>> ComponentMapper<F,LK> for SedComponentMapper<F,LK>{
	fn set_container_config(&mut self, r_advice: &Rc<dyn NdAdvice>){ 
		let advice = r_advice.as_any().downcast_ref::<SedAdvice<F>>()
			.expect("downcast err!");
		assert!(self.gadgets.len()==advice.vec_advices.len());
		let mut vec_cfgs = vec![];
		for i in 0..self.gadgets.len(){
			let cta_cfg = advice.vec_advices[i].gen_raw_container_config();
			vec_cfgs.push(cta_cfg);
		}
		ContainerConfig::adjust_locations(&mut vec_cfgs);
		let rc_cfgs = Rc::new(vec_cfgs);
		for i in 0..self.gadgets.len(){
			self.gadgets[i].borrow_mut().set_container_cfg(rc_cfgs.clone(), i);
		}
	}

	fn get_capacity(&self)->Rc<dyn Capacity>{
		Rc::new( Clone::clone(&self.capacity) )
	}

	fn create_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>{  
		self.gadgets.clone()
	}

	/// return the number of gadgets
	fn num_gadgets(&self) -> usize{
		self.gadgets.len() 
	}

	/// return the max word capacity of the component
	fn max_word_len(&self)->usize{ self.capacity.wea_capacity().max_word_len }

	/// return the sizes of inp, oup, data buffer
	fn get_sizes(&self)->Vec<usize>{
		let sizes = self.gadgets.iter().map(|g| g.borrow().get_to_add_size())
			.collect::<Vec<(usize, usize, usize)>>();
		let total = sizes.into_iter().fold((0,0,0), |x,y|
			(x.0+y.0, x.1+y.1, x.2+y.2));
		vec![total.0, total.1, total.2]
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

	/// Also responsible for generating nd_advice
	fn gen_nd_advice_no_limit(&self, word: &Vec<F>, word_info: &WordInfo,
		prev_adv: Option<Rc<dyn NdAdvice>>
	) ->Option<(Rc<dyn Capacity>, Rc<dyn NdAdvice>)>{
		//1. expand word to full length
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word);

		//2. collect the data for building advice.
		let bundle = if self.b_igc {&self.clamdb.bundle_subsig_igc}
			else {&self.clamdb.bundle_subsig};
		let pm_acdfa = &bundle.vec_acdfa[self.store_id];
		let sig_to_id = &self.clamdb.sig_to_id;
		let vec_sigs_to_discharge= if self.store_id==0{//sed case
			bundle.vec_sigs[0].iter().filter(|s|{
				let id = sig_to_id.get(&s.name)
					.expect(&format!("can't find sig: {}", s.name));
				word_info.vec_sed_sigs.contains(id)
			}).map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>()
		}else{//ised case: only one sig (which is the sig at store_id)
			assert!(bundle.vec_sigs[self.store_id].len()==1);
			vec![bundle.vec_sigs[self.store_id][0].clone()]
		};
		
		let subsig_pat_store = &bundle.vec_subsig_stores[self.store_id];
		let subsig_step_store = &bundle.vec_subsig_step_stores[self.store_id];
		let subsig_info_store = &bundle.vec_subsig_info_stores[self.store_id];
		let discharge_info = if self.store_id ==0{//sed case
			word_info.vec_sed_sigs_info.clone()
		}else {
			assert!(vec_sigs_to_discharge.len()==1);
			let ised_sig_name = &vec_sigs_to_discharge[0].name;
			let vec_info = word_info.vec_ised_sigs_info.iter().filter(|wi|
				&wi.sig_name==ised_sig_name).map(|wi| wi.clone())
				.collect::<Vec<DischargeSigInfo>>();
			assert!(vec_info.len()==1);
			vec_info
		};
		let sig_id = if self.store_id==0{ 0 } else{//ised case
			let sig_name = &bundle.vec_sig_names[self.store_id];
			*sig_to_id.get(sig_name).expect(
				&format!("Cant find sig {}", sig_name))
		}; //sig_id of the sig being discarged. store_id==0 is `all`
		let pm_fsm_id = ClamavDB::<F>::pm_acdfa_id(sig_id, self.b_igc); 
		println!("DEBUG USE 301: store_id: {}, word_info: {:?}", self.store_id, word_info);
		println!("DEBUG USE 302: bundle.vec_sig_names: {:?}", bundle.vec_sig_names);

		
		//3. generate the inputs (or its default
		let init_state = F::from((pm_acdfa.init_state+1) as u32); //adjusted state
		let init_loc = F::one();
		let inp_subsigs: Vec<F>= SedAdvice
			::collect_subsig_ids(&vec_sigs_to_discharge, 
				&discharge_info, sig_to_id, self.b_igc, &pm_acdfa);
		let init_steps_queue = DischargeAdvAdvice
			::gen_empty_steps_queue_serialized(
				&inp_subsigs,
				&subsig_step_store,
				pm_fsm_id,
				&self.capacity.da_capacity()
			).to_vec(&subsig_step_store);


		let (inp_state, inp_loc, inp_steps_queue) = prev_adv.as_ref().map_or(
			(init_state, init_loc, init_steps_queue), |adv|{
				let adv= adv.as_any().downcast_ref::<SedAdvice<F>>(); 
				let fsm_adv_advice= &adv.unwrap().fsm_adv_advice;
				let states = fsm_adv_advice.stmt_container.borrow()
					.get_container("states").expect("no states")
					.borrow().to_vec();
				let last_oup_state = states[states.len()-1]; //adjusted
				let locs = fsm_adv_advice.stmt_container.borrow()
					.get_container("locs").expect("no locs")
					.borrow().to_vec();
				let last_loc = locs[locs.len()-1];
				let da_adv = &adv.unwrap().discharge_adv_advice;
				let last_steps_queue = da_adv.get_output_steps_queue();
				(last_oup_state, last_loc, last_steps_queue.to_vec())
			}
		);
		let inp = SedInput{inp_state, inp_loc, inp_steps_queue};

		let advice = SedAdvice::<F>::new(
			self.b_igc, 
			&word_seg, 
			word.len(), 
			&self.capacity, 
			&inp, 

			pm_fsm_id,
			pm_acdfa,
			&vec_sigs_to_discharge,
			subsig_pat_store,
			subsig_step_store,
			subsig_info_store,
			&self.clamdb.sig_to_id,
			&discharge_info
		);

		//3. build the advice
		let cap2 = Clone::clone(&self.capacity);
		Some((Rc::new(cap2), Rc::new(advice)) )
	}

	/// Given its own gadget stmt_map: 7 range entries for
	///   word, inp,oup,data,subtbl_inp, subtbl_oup, subtbl_data 
	/// return the map entries for each of its gadgets for reconstructing
	/// their problem statement(note:
	///    entries solely depending on the gadget's own structure, need
	///    to read each gadget's doc for its statement structure)
	fn get_gadgets_stmt_map(&self, vec_alloc: &Vec<(usize,usize)>)
	->Vec<Vec<(usize,usize)>>{
		//1. get the allocation and make sure not exceeding boundaries
		assert!(vec_alloc.len()==7); 
		let (s_wd, e_wd) = vec_alloc[0];
		let (s_inp, _e_inp) = vec_alloc[1];
		let (s_oup, _e_oup) = vec_alloc[2];
		let (s_data, _e_data) = vec_alloc[3];
		let (s_subtbl_inp, _e_subtbl_inp) = vec_alloc[4];
		let (s_subtbl_oup, _e_subtbl_oup) = vec_alloc[5];
		let (s_subtbl_data, _e_subtbl_data) = vec_alloc[6];
		let wlen = self.max_word_len();
		assert!(e_wd - s_wd + 1 == wlen);
		let mut vec_res= vec![];
		//start positions for:
		// word, inp, oup, data, subtbl_id_inp, subtbl_id_oup, subtbl_id_data
		// where subtbl_xyz matches syz size
		let mut seg_starts = vec![vec![s_wd, s_inp, s_oup, s_data, s_subtbl_inp,
			s_subtbl_oup, s_subtbl_data]];

		//2. based on seg_starts construct map instruction
		for i in 0..self.gadgets.len(){
			//2.1. collect maps
			let instructions = self.gadgets[i].borrow()
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
			let ns = self.gadgets[i].borrow().get_to_add_size();
			let ns = vec![0, ns.0, ns.1, ns.2, ns.0, ns.1, ns.2]; 
			let mut nxt_starts = seg_starts[seg_starts.len()-1].clone();
			for j in 0..7 {nxt_starts[j] += ns[j];}
			seg_starts.push(nxt_starts);
			vec_res.push(my_maps);
		}

		assert!(vec_res.len()==self.num_gadgets());
		vec_res
	}

	/// return the inp, oup, data and 3 subtable segments. (6 vecs)
	/// the id, cfg, and comp_mapping helps it to locate the information
	/// it needs in prev_stmt which has the same structure as specified
	/// in StatementConfig. Note we pass the max len word, padded.
	/// the actual_word_len indicates the actual word seg in the word_seg.
	fn build_statement_comp(&self, _id: usize, _word_seg: &Vec<F>, _actual_word_len: usize, _prev_stmt: &Option<StatementInst<F,LK>>, _lkup: &Rc<RefCell<LK>>, _extra_info: &StatementExtraInfo<F>, advice: &Rc<dyn NdAdvice>, _cfg: &StatementConfig, _stmt_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>{
		//1. take the advice
		let advice = advice.as_any().downcast_ref::<SedAdvice<F>>()
			.expect("downcast err!");

		let res = advice.vec_advices.iter().fold(
			vec![vec![]; 6],
			|sum, adv|{
				let cps = adv.gen_stmt_components();
				assert!(cps.len()==6);
				sum.into_iter().zip(cps.into_iter()).map(|(a,b)|{
					let res:Vec<F> = vec![a, b].concat();
					res
				}).collect::<Vec<Vec<F>>>()
			}
		);

		assert!(res.len()==6);
		Ok( res )
	}
}
