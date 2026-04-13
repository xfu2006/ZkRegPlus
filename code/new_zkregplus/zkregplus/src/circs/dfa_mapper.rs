/* Created 07/17/2025 */

/* 
 A DFA component mapper handles the dfa approach.
 Its goal is to discharge a collection of signatures by DFA.
 It operarates several gadgets for:
 (1) extract word to 4-bit nibbles (each converted to 248-bit 62 nibbles)
   -- reuse the word_extract_adv gadget
 (2) concurrently run 4-bit nibbles over the DFAs for subsigs 
   -- new: dfa_adv gadget
     -- its last component has a module which is simillar to
	 -- compute_sig_adv.rs (which evalutes susig result over TriVal
	 -- logic to generate dischage result for sig).
 	
 *** STRUCTURE of its statement is managed by the new col/container 
 architecture. 
 	(wd, inp, oup, data, si_inp, si_oup, si_data)
	where si_[seg] always match the [seg], e.g., |si_data| = |data|.
*/

use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{logger::{log,log_perf, LOG1, LOG7}, timer::Timer, consts::read_global_config};
use std::{
	marker::PhantomData,
	sync::{Arc, Mutex},
	
	fmt::{Debug},
	collections::{HashMap},
};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{ Capacity,  SigmaGadget, StatementConfig, NdAdvice,WordInfo,LookupTableTwoCol,StatementExtraInfo,DischargeSigInfo},
		circuits_super::field_to_usize,
		container_config::{ContainerConfig},
	}
};
//use crate::{composable_gadget_mapper::{ComponentGadgetMapper}};
use ark_ff::{PrimeField};
use crate::{
	circs::composable_gadget_mapper::ComponentMapper,
	gadgets::word_extract_adv::{WordExtractAdvCapacity, WordExtractAdvGadget, WordExtractAdvAdvice },
	gadgets::word_extract::{LEGS},
	gadgets::dfa_adv::{DfaAdvCapacity,DfaAdvAdvice,DfaAdvGadget},
	gadgets::traits::{ComponentAdvice},
	//gadgets::commons::{print_vec},
};
use data_processor::{
	clam_db::{ClamavDB},
	hex_acdfa::HexACDFA,
	type_def::{ClamavSig},
	fsa_utils::build_trap_dfa,
};
use std::any::Any;
use rustomaton::dfa::DFA;

// --------------------------------------------------------
//		Structs
// --------------------------------------------------------

/// Capacity of the Cp Cmponent
#[derive(Clone,Debug)]
pub struct DfaCapacity{
	/// the number of sigs to support
	pub sigs: usize,

	/// the number of subsigs to suport
	pub subsigs: usize,

	/// max word len (chunk processed) in packed nibbles.
	pub max_word_len: usize,

	// will contain capacities for word_extract_adv, fsm_adv ...
	pub comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>>,
}

/// Represent the structure of Input
#[derive(Clone,Debug)]
pub struct DfaInput<F:PrimeField + ColEle>{
	/// input state
	pub v_inp_state: Vec<F>,
}

#[derive(Clone,Debug)]
pub struct DfaComponentMapper<F:PrimeField + ColEle, LK: LookupTableTwoCol<F>>{ 
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub capacity: DfaCapacity,

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


impl DfaCapacity{
	/// level 1 increase sigs
	/// level 2 increase subsigs
	pub fn increased_copy(&self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{
			Self::new(
				self.max_word_len,
				self.sigs*2,
				self.subsigs*2,
			)
		}else{
			Self::new(
				self.max_word_len,
				self.sigs,
				self.subsigs
			)
		}
	}

	pub fn decreased_copy(&self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{
			Self::new(
				self.max_word_len,
				(self.sigs*4/5).max(read_global_config().min_sigs),
				(self.subsigs*4/5).max(read_global_config().min_subsigs),
			)
		}else{
			Self::new(
				self.max_word_len,
				(self.sigs/2).max(read_global_config().min_sigs),
				(self.subsigs/2).max(read_global_config().min_subsigs),
			)
		}
	}

	pub fn new(
		max_word_len: usize, 
		sigs: usize, 
		subsigs: usize,
	)->Self{
		let wea_capacity = WordExtractAdvCapacity{max_word_len};
		let max_nibble_len = max_word_len * LEGS;
		let dfa_capacity = DfaAdvCapacity{max_nibble_len, subsigs, sigs};
			
		let comp_capacities: Vec<Arc<dyn Capacity + Send + Sync>> = vec![
			Arc::new(wea_capacity),
			Arc::new(dfa_capacity),
		];

		Self{max_word_len, sigs, subsigs, comp_capacities}
	}

	/// syntax sugar for returning a reference to its wea_capacity
	pub fn wea_capacity(&self)->&WordExtractAdvCapacity{
		self.comp_capacities[0].as_any()
			.downcast_ref::<WordExtractAdvCapacity>().unwrap()
	}

	pub fn dfa_capacity(&self)->&DfaAdvCapacity{
		self.comp_capacities[1].as_any()
			.downcast_ref::<DfaAdvCapacity>().unwrap()
	}

}

impl Capacity for DfaCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		
		let other = r_other.as_any().downcast_ref::<DfaCapacity>()
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
		Arc::new(DfaCapacity{
			sigs: self.sigs,
			subsigs: self.subsigs,
			max_word_len: self.max_word_len,
			comp_capacities: self.comp_capacities.clone()
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

/// The non-deterministic advice for the CP component
#[derive(Debug)]
pub struct DfaAdvice<F:PrimeField + ColEle>{
	pub wd_extract_advice: WordExtractAdvAdvice<F>,
	pub dfa_adv_advice: DfaAdvAdvice<F>,

	pub vec_advices: Vec<Arc<dyn ComponentAdvice<F> + Send + Sync>>,

}

impl <F:PrimeField+ColEle> NdAdvice for DfaAdvice<F>{
	fn as_any(&self) -> &dyn Any{ self }
}

impl <F:PrimeField+ColEle> DfaAdvice<F>{
	/// word seg must be full maxword len. The information:
	/// <dfa, vec_sigs, subsig_store, map_pattern_sig> are essentially
	/// one entry from the corresponding BundleSubsigs for one specific
	/// acdfa used for the SED/ISED. The others (word_seg to map_pattern_isg
	/// are global information.
	/// subsigs_to_discharge are the ones to discharge, retrieved from
	/// word info. 
	pub fn new(
			//1. global info
			word_seg: &Vec<F>, //must be full len pad with zero
			actual_size: usize,
			capacity: &DfaCapacity,
			inp: &DfaInput<F>,

			//2. needed for dfa_adv advice
			vec_sigs_to_discharge: &Vec<Arc<ClamavSig>>, //the sigs to 
			sig_to_id: &HashMap<String,usize>, //map from sig to id
			discharge_info: &Vec<DischargeSigInfo>, //info: subsigs to process
			seg_id: F,
			job_id: usize,
		)->Result<Self, Error>{
		let mut t1 = Timer::new();
		let b_perf = true;

		//1. build the word extraction gadget's advice
		let wd_extract_advice = WordExtractAdvAdvice::<F>
			::new(word_seg, actual_size, true)?; //use char map mode for sid
		if b_perf{ log_perf(job_id, LOG1, "-- DFA advice step1: word_extract", &mut t1); }

		//2. build dfa_adv advice
		//we build a 2-d structure of info first and then
		//flatten them out to the info needed. This is
		//similar to the unit test code in dfa_adv.rs
		//2.1 create the 2-d version of the information
		let nibbles = wd_extract_advice.stmt_container.lock().unwrap().
			get_container("nibbles").expect("no nibbles").lock().unwrap().to_vec();
		let v_sigs = vec_sigs_to_discharge;
		assert!(v_sigs.len()==discharge_info.len());
		let inp_sigs = vec_sigs_to_discharge.iter().map(|sig|{
			let sig_id = sig_to_id.get(&sig.name)
				.expect(&format!("can't find sig: {}", sig.name));
			F::from(*sig_id as u64)
		}).collect::<Vec<F>>();
		let inp_subsigs = discharge_info.iter().map(|info| {
			let sig_id = sig_to_id.get(&info.sig_name).unwrap();
			info.subsig_ids.iter().map(|i|
				F::from(HexACDFA::gen_subsig_id_worker(*sig_id, *i+1) as u32)
			).collect::<Vec<F>>()
		}).collect::<Vec<Vec<F>>>();
		let inp_raw_subsigs = v_sigs.iter().zip(discharge_info.iter())
			.map(|(sig,info)| {
				sig.eval_dnf.vec_disjunc[info.min_dnf_id]
				.iter().map(|i| F::from(*i as u64))
				.collect::<Vec<F>>()
		}).collect::<Vec<Vec<F>>>();
		let v_dfa= v_sigs.iter().zip(discharge_info.iter())
		.map(|(sig,info)| 
			sig.eval_dnf.vec_disjunc[info.min_dnf_id].iter().map(|i| 
				sig.vec_subsig_automaton[*i].clone()) //clone of Arc low cost
			.collect::<Vec<Arc<DFA<char>>>>()
		).collect::<Vec<Vec<Arc<DFA<char>>>>>();
		assert!(v_sigs.len()==inp_raw_subsigs.len());
		let v_fsm_id = v_sigs.iter().zip(inp_raw_subsigs.iter())
			.map(|(sig, v_subsig)|{
				let sig_id = *(sig_to_id.get(&sig.name).unwrap()) as u32;
				v_subsig.iter().map(|subsig_id|{
					let dfa_id = ClamavDB::<F>::dfa_id(
						sig_id, 
						field_to_usize(subsig_id) as u32
					);
					F::from(dfa_id)
				}).collect::<Vec<F>>()
		}).collect::<Vec<Vec<F>>>();

		//2.2 flatten and pad info if needed
		let v_subsig_ids = inp_subsigs.into_iter().map(|s| s).flatten()
			.collect::<Vec<F>>();
		let v_fsm_id= v_fsm_id.into_iter().map(|s| s).flatten()
			.collect::<Vec<F>>();
		let v_dfa= v_dfa.into_iter().map(|s| s).flatten()
			.collect::<Vec<Arc<DFA<char>>>>();
		let dummy_fsm_id = F::from(ClamavDB::<F>::dfa_id(0, 0));
		let dummy_dfa = Arc::new(build_trap_dfa());
		
		let n = capacity.subsigs;
		let n1 = v_subsig_ids.len();
		if n<n1{
			return Err(Error::CapErr(vec![(format!("dfa_mapper::subsigs"), 
				n1)]));
		}
		assert!(n>=n1);
		assert!(v_fsm_id.len()==n1 && v_dfa.len()==n1);
		let n2 = n-n1;
		let zero = F::zero();
		let v_subsig_ids= [&v_subsig_ids[..], 
			&vec![zero; n2][..]].concat();
		let v_fsm_id = [&v_fsm_id[..], &vec![dummy_fsm_id;n2]].concat();
		let v_dfa = [&v_dfa[..], &vec![dummy_dfa.clone();n2][..]].concat();
		let v_inp_state = &inp.v_inp_state;
		assert!(v_inp_state.len()==n);

		let dfa_cap = &capacity.dfa_capacity();
		let dfa_adv_advice = DfaAdvAdvice::<F>
			::new( 
				&nibbles, &v_subsig_ids, &v_fsm_id,
				&v_dfa, &v_inp_state, &dfa_cap,
				&inp_sigs, &discharge_info, &v_sigs, &sig_to_id, seg_id,
			)?;

		//3. assemble all advices
		let vec_advices:Vec<Arc<dyn ComponentAdvice<F> + Send + Sync>> = vec![
			Arc::new(wd_extract_advice.clone()),
			Arc::new(dfa_adv_advice.clone()),
		];
		if b_perf{ log_perf(job_id, LOG1, "-- DFA advice step2: dfa", &mut t1); }

		Ok(Self{wd_extract_advice, dfa_adv_advice, vec_advices})
	}
}

impl <F:PrimeField + ColEle,LK:LookupTableTwoCol<F>> DfaComponentMapper<F,LK>{
	/// constructor needs the max word len to handle the capacity
	/// of PackFinal (number of final states), and reference to clamdb
	pub fn new(
		capacity: DfaCapacity,
		clamdb: Arc<ClamavDB<F>>,
	) ->Self{
		let mut cfgs = vec![];

		//1. build the gadgets
		//1.1 the word extract gadget
		let g_wea = WordExtractAdvGadget::<F>::new(capacity
			.wea_capacity().max_word_len, true); //use the char_map as
											//sid for nibbles
		cfgs.push( g_wea.dummy_cfg.clone() );

		//1.2 the dfm_adv gadget
		let dfa_cap = &capacity.dfa_capacity();
		let g_dfa = DfaAdvGadget::<F>::new(&dfa_cap, &cfgs);
		cfgs.push( g_dfa.dummy_cfg.clone() );

		let gadgets: Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>> = vec![ 
			Arc::new(Mutex::new(g_wea)), //word_extract_adv gadget
			Arc::new(Mutex::new(g_dfa)), //DFA gadget
		];

		Self{
			_f: PhantomData, 
			_lk: PhantomData, 
			capacity,
			gadgets,
			clamdb,
			job_id: 0,
		}
	}

}

impl <F:PrimeField + ColEle, LK: LookupTableTwoCol<F> + Send + Sync> ComponentMapper<F,LK> for DfaComponentMapper<F,LK>{
	fn set_container_config(&mut self, r_advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		let advice = r_advice.as_any().downcast_ref::<DfaAdvice<F>>()
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

	fn get_name(&self)->String {format!("DfaMapper")}

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
	fn max_word_len(&self)->usize{ self.capacity.wea_capacity().max_word_len }

	/// return the sizes of inp, oup, data buffer
	fn get_sizes(&self)->Vec<usize>{
		let log_level = LOG7;
		let b_perf = true && log_level>=read_global_config().log_level;
		if b_perf{
			log(0, log_level, &format!(" ## dfa gadgets data len: ==="));
			for i in 0..self.gadgets.len(){
				let vs = self.gadgets[i].lock().unwrap().get_to_add_size();
				log(0, log_level, &format!("  -- {}: {}", 
					self.gadgets[i].lock().unwrap().get_name(),
					vs.2));
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


	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, seg_id: usize, _job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
		//1. expand word to full length
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word);

		//2. collect the data for building advice.
		let sig_to_id = &self.clamdb.sig_to_id;
		let vec_sigs_name = word_info.vec_dfa_sigs.clone();
		let v_sigs = self.clamdb.vec_sigs.iter().filter(|sig| {
			let sid = sig_to_id.get(&sig.name).unwrap();
			vec_sigs_name.contains(sid)
		}).map(|sig| sig.clone()).collect::<Vec<Arc<ClamavSig>>>();
		let discharge_info = word_info.vec_dfa_sigs_info.clone();

		//3. build a dummy advice first to get the vec_dfa
		let n = self.capacity.subsigs;
		let inp = DfaInput{v_inp_state: vec![F::one(); n]};
		let dummy_adv = DfaAdvice::new(&word_seg, word.len(), &self.capacity,
			&inp, &v_sigs, &sig_to_id, &discharge_info, F::from(seg_id as u64), _job_id)?;
		let v_dfa = &dummy_adv.dfa_adv_advice.v_dfa;
		assert!(v_dfa.len()==n);
		let init_states = v_dfa.iter().map(|dfa| 
			F::from((dfa.initial+1) as u32)).collect::<Vec<F>>();

		//4. generate the inputs EITHER from input or initial
		let inp_states = prev_adv.as_ref().map_or(
			init_states, |adv|{
				let adv= adv.as_any().downcast_ref::<DfaAdvice<F>>(); 
				let dfa_adv_advice= &adv.unwrap().dfa_adv_advice;
				let states = dfa_adv_advice.stmt_container.lock().unwrap()
					.search_container("dfa_adv_stmt mul_fsm_acc states").expect("no states")
					.lock().unwrap().to_vec();
				let states_len = states.len();  //nibbles * subsigs
				let last_oup_states = states[states_len-n..states_len]
					.to_vec();
				last_oup_states
			}
		);
		assert!(inp_states.len()==n); //capacity.subsigs
		let inp = DfaInput{v_inp_state: inp_states};


		let advice = DfaAdvice::<F>::new(
			&word_seg, 
			word.len(), 
			&self.capacity, &inp, 
			&v_sigs, &sig_to_id, &discharge_info, //keep the v_sigs earlier
			F::from(seg_id as u64),
			_job_id
		)?;

		Ok( Arc::new(advice) )
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
	->(Vec<Vec<(usize,usize)>>, Vec<(usize,bool)>, Vec<(usize,bool)>,
		Vec<(usize,bool)>){
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
		// word, inp, oup, data, failed_sigs, discharged_sigs,
		// subtbl_id_inp, subtbl_id_oup, subtbl_id_data
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
			// failed_sigs, discharged_sigs
			// sid_inp, sid_opu, sid_data
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

	/// return the inp, oup, data and 3 subtable segments,
	///   and then the failed_sigs, discharged_sigs. (8 vecs)
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
		let b_perf = read_global_config().log_level >= log_level;
		//1. take the advice
		let advice = advice.as_any().downcast_ref::<DfaAdvice<F>>()
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
			log(0, log_level, &format!("## build_stmt: DFA failed sigs"));
			for i in 0..res[6].len(){
				log(0, log_level, &format!(" -- {} => {}",
					i, &res[6][i]));
			}
			log(0, log_level, &format!("## build_stmt: DFA discharged sigs"));
			for i in 0..res[7].len(){
				log(0, log_level, &format!(" -- {} => {}",
					i, &res[7][i]));
			}
		}

		assert!(res.len()==8);
		Ok( res )
	}
}
