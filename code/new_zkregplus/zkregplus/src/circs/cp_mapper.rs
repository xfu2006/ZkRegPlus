use utils::consts::{read_global_config, B_DEBUG};
/* Created 02/16/2025
   Modified: 07/30/2025 to incororate the failed_sig and discharged_sig 
   sections.
*/

// A CP component mapper handles the critical pattern
// It operarates several gadgets for:
// (1) extract word to 4-bit nibbles (each converted to 248-bit 62 nibbles)
// (2) generating the trace given the input state and output the
//       entire trace (fsm_gadget)
// (3) pack the trace into set of states
// (4) map from the states to signatures by retrieving from lkup.
//   --> the FAILED SIGANTURES are stored in the oup_buf ofer the 
//   the sig.rs. We make a copy of it and STORE then in the
//   failed_sigs.

// *** STRUCTURE of its statement (except wd which is already passed)
// inp: inp_state
// oup: oup_state, ... oup_sigs
// data: 
//       -- introduced by gadget extract_word
//		 act_w_len [1], 
//       extracted_word [62*wlen], 
//       -- introduced by gadget fsm --
//       states [62*wlen-1], //not including first and last
//       transitions [62*wlen]
//       -- introduced by gadget pack_fs
//       unique_states [imm_buf_len]
//       m_table [final [imm_buf_len]]
//       final_states [final_states_len]
//       -- introduced by gadget sigs
//       many items (call its advice to generate data item
// failed_sigs: the COPY of the  oup_sigs (last #sigs elements of oup)
//   -- will reserve at least one dummy (0) entry
// discharged_sigs: size 1 (to ensure at least one dummy entry)

// subtbl: follow inp/oup/data
use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{logger::{log, log_perf, emit_stdout, LOG1, LOG7}, timer::Timer };
use std::{
	marker::PhantomData,
	sync::{Arc, Mutex},
	
	fmt::{Debug},
	collections::{HashMap},
};
//use rayon::iter::{IndexedParallelIterator,IntoParallelRefIterator,ParallelIterator};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{ Capacity,  SigmaGadget, StatementConfig, NdAdvice,WordInfo,LookupTableTwoCol,StatementExtraInfo},
		circuits_super::field_to_usize,
	}
};
//use crate::{composable_gadget_mapper::{ComponentGadgetMapper}};
use ark_ff::{PrimeField};
use crate::{
	circs::{composable_gadget_mapper::{ComponentMapper,
			ComponentMapperCloneBox},
		  },
	gadgets::word_extract::{WordExtractGadget,LEGS,WordExtractAdvice},
	gadgets::fsm::{FsmGadget,FsmAdvice},
	gadgets::pack::{PackFinalGadget,PackFinalAdvice},
	gadgets::sigs::{GetSigAdvice,SigGadgetCapacity,SigGadgetData,GetSigGadget},
	//gadgets::commons::{print_vec},
};
use data_processor::{
	clam_db::{ClamavDB,CHAR,CRIT_INIT,
		CRIT_IGC_INIT, CRIT_STATES, CRIT_IGC_STATES,
		CRIT_TRANSITIONS, CRIT_IGC_TRANSITIONS,
		CRIT_IGC_FINAL, CRIT_FINAL, RANGE2},
	hex_acdfa::HexACDFA
};
use std::any::Any;

/// Capacity of the Cp Cmponent
#[derive(Clone,Debug)]
pub struct CpCapacity{
	/// maximum word capacity: note: after extracted,
	/// the word seg expands to 62X (248bit/4 = 62) nibbles.
	pub max_word_len: usize,
	///0.01 percent, reflects the
	///ratio of UNIQUE states in a trace
	pub basis_unique_states: usize, 
	///the number of subsigs out of (note not sigs)
	pub subsigs: usize, 
	///how many patterns per subsig
	pub avg_pats_per_subsig: usize, 
	// NOT used: average number of usbsigs per sig
	//pub avg_subsig_per_sig: usize,
}

impl CpCapacity{
	/// return the original 
	/// (final_states_len, join_buf_capacity,sig_buf_capacity, imm_buf_len)
	/// in the old design of the
	/// CpCapacity for legacy consistency.
	pub fn get_old_stats(&self)->(usize, usize, usize, usize){
		let final_states_len = self.avg_pats_per_subsig
			*self.subsigs;
		let join_buf_capacity= self.subsigs *  
			self.avg_pats_per_subsig;
		let sig_buf_capacity= self.subsigs;
		let imm_buf_len = self.max_word_len * LEGS  *
			 self.basis_unique_states / 10000;
		
		(final_states_len, join_buf_capacity, sig_buf_capacity, imm_buf_len)
	}

	/// increase capacity, here we keep the same max_word_len
	/// but double the rest
	pub fn increased_copy(&mut self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{
			Self{
				max_word_len: self.max_word_len,
				basis_unique_states: self.basis_unique_states,
				subsigs: self.subsigs * 2,
				avg_pats_per_subsig: self.avg_pats_per_subsig,
				//avg_subsig_per_sig: self.avg_subsig_per_sig+1,
			}
		}else{
			Self{
				max_word_len: self.max_word_len,
				basis_unique_states: self.basis_unique_states * 2,
				subsigs: self.subsigs,
				avg_pats_per_subsig: self.avg_pats_per_subsig * 2,
				//avg_subsig_per_sig: self.avg_subsig_per_sig+1,
			}
		}
	}

	pub fn decreased_copy(&self, level: usize)->Self{
		assert!(level==1 || level==2);
		if level==1{
			Self{
				max_word_len: self.max_word_len,
				basis_unique_states: (self.basis_unique_states*9/16) // OLD: *3/4
					.max(read_global_config().min_basis_unique_states),
				subsigs: (self.subsigs*9/16).max(read_global_config().min_subsigs), // OLD: *3/4
				avg_pats_per_subsig: (self.avg_pats_per_subsig*9/16) // OLD: *3/4
					.max(read_global_config().min_avg_pats_per_subsig),
			}
		}else{
			Self{
				max_word_len: self.max_word_len,
				basis_unique_states: (self.basis_unique_states/4).max(read_global_config().min_basis_unique_states), // OLD: /2
				subsigs: (self.subsigs/4).max(read_global_config().min_subsigs), // OLD: /2
				avg_pats_per_subsig: (self.avg_pats_per_subsig/4).max(read_global_config().min_avg_pats_per_subsig), // OLD: /2
			}
		}
	}
}

impl Capacity for CpCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		let other = r_other.as_any().downcast_ref::<CpCapacity>()
			.expect("downcast err"); 

		self.max_word_len>= other.max_word_len &&
		self.basis_unique_states>= other.basis_unique_states &&
		self.subsigs>= other.subsigs &&
		self.avg_pats_per_subsig>= other.avg_pats_per_subsig 
		//self.avg_subsig_per_sig>= other.avg_subsig_per_sig 
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(CpCapacity{
			max_word_len: self.max_word_len,
			basis_unique_states: self.basis_unique_states,
			subsigs: self.subsigs,
			avg_pats_per_subsig: self.avg_pats_per_subsig,
			//avg_subsig_per_sig: self.avg_subsig_per_sig,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

/// The non-deterministic advice for the CP component
#[derive(Debug)]
pub struct CpAdvice<F:PrimeField + ColEle>{
	/// the advice needed for the word_extract gadget
	pub wd_extract_advice: WordExtractAdvice<F>,

	/// the advice for the fsm gadget
	pub dfa_crit_advice: FsmAdvice<F>,
	/// the advice for the pack final gadget
	pub packfinal_crit_advice: PackFinalAdvice<F>,
	/// the advice for the sigs gadget
	pub sigs_advice: GetSigAdvice<F>,

	/// input buffer for the badget
	pub inp_buf: Vec<F>,
}

impl <F:PrimeField + ColEle> NdAdvice for CpAdvice<F>{
	fn as_any(&self) -> &dyn Any{ self }
}

impl <F:PrimeField + ColEle> CpAdvice<F>{
	/// word seg must be full maxword len
	pub fn new(
			word_seg: &Vec<F>, //must be full len pad with zero
			actual_size: usize,
			capacity: &CpCapacity,
			inp_buf: &Vec<F>,  //input buffer
			dfa_crit: &HexACDFA,
			map_crit_pat: &HashMap<String,Vec<String>>,
			sig_to_id: &HashMap<String,usize>,
			fsm_id: usize, //e.g., CRIT_INIT or CRIT_IGC_INIT
			vec_sig_id_no_crit_pat: &Vec<usize>, //the pats to include 
					//in failed_sigs by default
			job_id: usize,
		)->Result<Self, Error>{
		//0. construct the capacity fields needed by sub-components
		let mut t1 = Timer::new();
		let b_perf = true;
		let (final_states_len,join_buf_capacity,sig_buf_capacity,imm_buf_len)
			 = capacity.get_old_stats();

		//1. build the word extraction gadget's advice
		let inp_state = inp_buf[0].clone();
		let wd_extract_advice = WordExtractAdvice::<F>
			::new(word_seg, actual_size)?;
		let nibbles = wd_extract_advice.data[1..].to_vec();
		let dfa_crit_advice = FsmAdvice::<F>
			::new(&nibbles, dfa_crit, inp_state, fsm_id as u32)?;
		if b_perf{ log_perf(job_id, LOG1, "-- CpMapper gen_adv step1", &mut t1); }


		//2. build the packing final states gadget's advice
		let vec_b_final = dfa_crit_advice.states.iter().map(|s|{
			let val_s = field_to_usize(s);
			dfa_crit.is_final(val_s - 1)
		}).collect::<Vec<bool>>();
		let pack_res = PackFinalAdvice::<F>
			::new(&dfa_crit_advice.states, &vec_b_final,
				imm_buf_len, final_states_len, fsm_id as u32);
		let packfinal_crit_advice = match pack_res{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let vec_err = vec.iter().map(|(s,val)|{
					if s.contains("capacity_imm"){
						let basis_unique_states = val * 10000 
							/(capacity.max_word_len * LEGS) + 1;
						(format!("cp::basis_unique_states from pack.rs"),basis_unique_states)
					}else if s.contains("capacity_out"){
						let avg_pats_per_subsig = val / capacity.subsigs + 1;
						(format!("cp::avg_pats_per_subsig from pack.rs"),avg_pats_per_subsig)
					}else{
						(format!("unknown capacity err: {}", s), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => pack_res 
		}?;
		if b_perf{ log_perf(job_id, LOG1, "-- CpMapper gen_adv step2: pack_res", &mut t1); }

		//3. build the advice for the sigs gadget
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: final_states_len,
			join_buf_capacity: join_buf_capacity,
			sig_buf_capacity: sig_buf_capacity,
			count_sig_no_crit_pat: vec_sig_id_no_crit_pat.len(),
		};
		let inp_sigs = inp_buf[1..sig_buf_capacity+1].to_vec();
		if b_perf{ log_perf(job_id, LOG1, "-- CpMapper gen_adv step3: sig", &mut t1); }

		
		let sigs_res = GetSigAdvice::<F>::new(
			&packfinal_crit_advice.oup_states, &inp_sigs, sig_cap, 
			dfa_crit, map_crit_pat, sig_to_id, fsm_id, vec_sig_id_no_crit_pat);
		let sigs_advice = match sigs_res{
			Ok(adv) => Ok(adv),
			Err(Error::CapErr(vec)) => {
				let vec_err = vec.iter().map(|(s,val)|{
					if s.contains("slen"){
						let subsigs = val;
						(format!("cp::subsigs"),*subsigs)
					}else if s.contains("olen"){
						let avg_pats_per_subsig = val / capacity.subsigs + 1;
						(format!("cp::avg_pats_per_subsig from sigs.rs olen"),avg_pats_per_subsig)
					}else if s.contains("jlen"){
						let avg_pats_per_subsig = val / capacity.subsigs + 1;
						(format!("cp::avg_pats_per_subsig from sigs.rs jlen"),avg_pats_per_subsig)
					}else{
						(format!("unknown capacity err: {}", s), 0)
					}
				}).collect::<Vec<(String,usize)>>();
				Err(Error::CapErr(vec_err))
			},
			_ => sigs_res 
		}?;
		if b_perf{ log_perf(job_id, LOG1, "-- CpMapper gen_adv step4: assemble", &mut t1); }

		Ok(Self{
			wd_extract_advice,
			dfa_crit_advice,
			packfinal_crit_advice,
			sigs_advice,
			inp_buf: inp_buf.clone(),
		})
	}

}


#[derive(Clone,Debug)]
pub struct CpComponentMapper<F:PrimeField + ColEle, LK: LookupTableTwoCol<F>>{ 
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub capacity: CpCapacity,

	pub b_igc: bool,

	/// its own gadgets 
	pub gadgets: Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>,

	/// clamdb
	pub clamdb: Arc<ClamavDB<F>>,

	pub job_id: usize,
}

impl <F:PrimeField + ColEle,LK:LookupTableTwoCol<F>> CpComponentMapper<F,LK>{
	/// constructor needs the max word len to handle the capacity
	/// of PackFinal (number of final states), and reference to clamdb

	pub fn new(
		cp_capacity: CpCapacity,
		clamdb: Arc<ClamavDB<F>>,
		b_igc: bool //whether it's for ignore case ACDFA
	) ->Self{
		//1. build the gadgets
		let (final_states_len, join_buf_capacity, sig_buf_capacity,imm_buf_len) 
			= cp_capacity.get_old_stats();

		let nlen = cp_capacity.max_word_len * LEGS;
		let state_bits = clamdb.dfa_crit.state_part_bits;
		let fsm_id = if b_igc {CRIT_IGC_INIT} else {CRIT_INIT};

		let g_extract = WordExtractGadget::<F>::new(cp_capacity.max_word_len);
		let dfa_crit = FsmGadget::<F>::new(nlen, fsm_id, state_bits); 
		let pack_crit = PackFinalGadget::<F>::new(nlen+1, imm_buf_len,
			final_states_len, fsm_id);

		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: final_states_len,
			join_buf_capacity: join_buf_capacity,
			sig_buf_capacity: sig_buf_capacity,
			count_sig_no_crit_pat: clamdb.vec_sigs_no_critical_pat.len(),  
		};
		let sig_gadget= GetSigGadget::<F>::new(&sig_cap, fsm_id);
		let gadgets: Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>> = vec![ 
			Arc::new(Mutex::new(g_extract)), //word -> nibbles
			Arc::new(Mutex::new(dfa_crit)), //run through dfa_crit
			Arc::new(Mutex::new(pack_crit)), //pack trace to final states
			Arc::new(Mutex::new(sig_gadget)), //generate signatures
		];
		assert!(clamdb.as_ref().vec_sigs_no_critical_pat.len()
			<sig_buf_capacity,
			concat!("\n\n ==== **** ==== \nNEEDS to INCREASE the MINIMUM CpCapacity.subsigs from {} to {}.\n",
			"because from sig DB there are {} subsigs have no critical pattern,",
			"they will not pass CP component and will need to be passed ",
			"to SED. The CpCapacity.subsigs need to be greater. This applies to all input words (system wide)"),
			sig_buf_capacity,
			clamdb.as_ref().vec_sigs_no_critical_pat.len() + 1, 
			clamdb.as_ref().vec_sigs_no_critical_pat.len(), 
			);

		Self{
			_f: PhantomData, 
			_lk: PhantomData, 
			capacity: cp_capacity,
			gadgets,
			b_igc,
			clamdb,
			job_id: 0,
		}
	}

}

impl <F:PrimeField + ColEle + 'static, LK: LookupTableTwoCol<F> + Send + Sync + 'static> ComponentMapper<F,LK> for CpComponentMapper<F,LK>{
	fn set_container_config(&mut self, _r_advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		// no need to handle for legacy code.
	}

	fn get_name(&self)->String{format!("CpMapper")}

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
	fn num_gadgets(&self) -> usize{self.gadgets.len() }

	/// return the max word capacity of the component
	fn max_word_len(&self)->usize{ self.capacity.max_word_len }

	/// return the sizes of inp, oup, data, failed_sigs, discharged_sigs
	fn get_sizes(&self)->Vec<usize>{
		//1. gadget of word extension
		let log_level = LOG7;
		let b_perf = true && log_level >=read_global_config().log_level;
		let (final_states_len,join_buf_capacity,sig_buf_capacity,mlen) = 
			self.capacity.get_old_stats();

		let wlen = self.capacity.max_word_len;
		let nlen = LEGS * wlen; //nibble len
		let flen = final_states_len;
		let clen = self.clamdb.vec_sigs_no_critical_pat.len();
		let inp_g_ext = 0;
		let oup_g_ext = 0;
		let data_g_ext = 1 + nlen;

		let inp_dfa= 1;
		let oup_dfa= 1;
		let data_dfa= 2*nlen-1; //NOTE: excluding the gadget's
									 // "shared" nibbles with w_extract
		let data_pack= 2*mlen+flen; // the increased are unique_states, 
									//final_staes, m_table

		let inp_sigs= sig_buf_capacity;
		let oup_sigs= sig_buf_capacity;
		let data_sigs = final_states_len * 3 
			+ join_buf_capacity * 5
			+ sig_buf_capacity * 3
			+ clen + 1; //for the sigs_no_crit_pat and its count

		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: final_states_len,
			join_buf_capacity: join_buf_capacity,
			sig_buf_capacity: sig_buf_capacity,
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};
		assert!(data_sigs == SigGadgetData::<F>::get_len(&sig_cap) 
			- final_states_len);

		//2. collect all data
		// 2026-05-15: was log(0,..) — routed every job's
		// CP-mapper data-len traces into log_job_0.txt. Same
		// family of bug as the gen_witness step-3.x sites.
		if b_perf{
			log(self.job_id, log_level, &format!(" ## CP mapper data len, nlen: {} ###", nlen));
			log(self.job_id, log_level, &format!("  -- word_extract: {}", data_g_ext));
			log(self.job_id, log_level, &format!("  -- word_fsm: {}", data_dfa));
			log(self.job_id, log_level, &format!("  -- pack: {}", data_pack));
			log(self.job_id, log_level, &format!( "  -- sigs: {}", data_sigs));
		}
		let vec_inp_len = vec![inp_g_ext, inp_dfa, inp_sigs];
		let vec_oup_len = vec![oup_g_ext,  oup_dfa, oup_sigs];
		let vec_data_len = vec![data_g_ext,  data_dfa, data_pack, data_sigs];

		//3. sum all
		let inp_size:usize = vec_inp_len.iter().map(|x| x).sum();
		let oup_size:usize = vec_oup_len.iter().map(|x| x).sum();
		let data_size:usize = vec_data_len.iter().map(|x| x).sum();
		let failed_sig_size = sig_buf_capacity;
		let discharged_sig_size = 1;
		vec![inp_size, oup_size, data_size,failed_sig_size,discharged_sig_size]
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

		//2. no join for fsm (dfa_crit) gadget
		//3. no joins for pack_crit gadget
		//4. no joins for sigs gadget
		
		vec![ (rg_g_ext, rg_g_ext_upper) ]
	}

	fn gen_nd_advice(&self, word: &Vec<F>, _word_info: &WordInfo,
		prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, _seg_id: usize, _job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
		//1. expand to full length. WordExtractGadget enforces
		// extracted_word[i]=0 for i >= actual_size, so the pad
		// F-elements MUST be zero to satisfy R1CS.
		let (zero,one) = (F::zero(),F::one());
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word);

		//2. build the input for computing advice 
		let capacity = &self.capacity;
        let (_final_states_len,_join_buf_capacity,sig_buf_capacity,_imm_buf_len)
                        = capacity.get_old_stats();

		let init_state = if !self.b_igc {
			F::from(self.clamdb.dfa_crit.init_state as u32)
		}else{
			F::from(self.clamdb.dfa_crit_igc.init_state as u32)
		};
		//note inp_state if init, is adjusted by one
		//for subsequent cases, output are already adjusted by 1.
		let inp_state = prev_adv.as_ref().map_or(init_state+one, |adv|{
			let adv= adv.as_any().downcast_ref::<CpAdvice<F>>(); 
			let dfa_crit_advice = &adv.unwrap().dfa_crit_advice;
			let last_oup_state = dfa_crit_advice.states[
				dfa_crit_advice.states.len()-1];
			last_oup_state
		});
		
		let (acdfa, map_crit) = if self.b_igc{
			(&self.clamdb.as_ref().dfa_crit_igc, 
			 &self.clamdb.as_ref().map_crit_pat_igc)
		}else{
			(&self.clamdb.as_ref().dfa_crit, 
			 &self.clamdb.as_ref().map_crit_pat)
		};
		let fsm_id = if self.b_igc {CRIT_IGC_INIT} else {CRIT_INIT};
		let sigs_to_id = &self.clamdb.as_ref().sig_to_id;

		// those for sure will FAIL crit_pat (their short patterns
		// are not included in acdfa for CP). So they are included
		// automatically in cp failed signatures.
		let mut vec_sig_id_no_crit_pat= self.clamdb
			.as_ref().vec_sigs_no_critical_pat
			.iter().map(|sig|
			*sigs_to_id.get(&sig.name)
				.expect(&format!("cannot find sig: {}", sig.name))
		).collect::<Vec<usize>>();
		vec_sig_id_no_crit_pat.sort();

		//3. compute the advice
		let inp_sigs = prev_adv.map_or(vec![zero; sig_buf_capacity], 
		|adv|{
			let adv= adv.as_any().downcast_ref::<CpAdvice<F>>(); 
			let last_oup_sigs = &adv.unwrap().sigs_advice.oup;
			last_oup_sigs.to_vec()
		});
		let inp_buf = vec![ vec![inp_state], inp_sigs].concat();
		let advice = CpAdvice::<F>::new(
			&word_seg,
			word.len(),
			&self.capacity,
			&inp_buf,
			acdfa,
			map_crit,
			sigs_to_id,
			fsm_id as usize,
			&vec_sig_id_no_crit_pat,
			_job_id,
		)?;

		// 2026-05-16: probe 77320.1 — per-segment dump of what CP
		// sees. Together with 77320.2 (discharge_prover set_sigs_crit
		// per file) this isolates where CP and discharge_prover
		// diverge: if added_this_seg includes 34602/35386/35701 in
		// the last segment only, pack-padding zeros are the culprit;
		// if at segment boundaries (inp_state != init), the prev_adv
		// DFA-state carry-over diverges from acc_path's single pass.
		if std::env::var("ZKR_PROBE_77317").is_ok() {
			use folding_schemes::folding::foldpot::utils::
				probe_77317_f_as_u64_lossy;
			use std::collections::BTreeSet;
			let inp_unique: BTreeSet<u64> = inp_buf[1..]
				.iter().filter(|f| !f.is_zero())
				.map(|f| probe_77317_f_as_u64_lossy(f))
				.collect();
			let oup_unique: BTreeSet<u64> = advice
				.sigs_advice.oup.iter()
				.filter(|f| !f.is_zero())
				.map(|f| probe_77317_f_as_u64_lossy(f))
				.collect();
			let no_crit_set: BTreeSet<u64> = vec_sig_id_no_crit_pat
				.iter().map(|x| *x as u64).collect();
			let added_this_seg: Vec<u64> = oup_unique.iter()
				.filter(|x| !inp_unique.contains(x))
				.filter(|x| !no_crit_set.contains(x))
				.copied().collect();
			let last_state = advice.dfa_crit_advice.states.last()
				.copied().unwrap_or(F::zero());
			emit_stdout(format!(
				"DEBUG USE 77320.1: CP b_igc={} seg_id={} \
				 actual_size={} inp_state_u64={} \
				 last_state_u64={} no_crit.len={} \
				 inp.unique.len={} oup.unique.len={} \
				 added_this_seg.len={}",
				self.b_igc, _seg_id, word.len(),
				probe_77317_f_as_u64_lossy(&inp_state),
				probe_77317_f_as_u64_lossy(&last_state),
				vec_sig_id_no_crit_pat.len(),
				inp_unique.len(), oup_unique.len(),
				added_this_seg.len()));
			emit_stdout(format!(
				"DEBUG USE 77320.1.added_this_seg b_igc={} \
				 seg_id={} ids={:?}",
				self.b_igc, _seg_id, added_this_seg));
			let oup_list: Vec<u64> = oup_unique.iter().copied()
				.collect();
			emit_stdout(format!(
				"DEBUG USE 77320.1.oup b_igc={} seg_id={} \
				 ids={:?}",
				self.b_igc, _seg_id, oup_list));

			// Probe B: partition final-state hits into real vs pad
			// region. real_nib = word.len() * LEGS;  unpacked_nib =
			// states.len() - 1. Anything at position > real_nib is
			// scanned over F::zero() padding inserted to fill the
			// segment to max_word_len. If 34602/35386/35701 show up
			// in pad_only_ids, pack-padding is the culprit.
			use crate::gadgets::word_extract::LEGS;
			let states = &advice.dfa_crit_advice.states;
			let real_nib = word.len() * LEGS;
			let unpacked_nib = states.len().saturating_sub(1);
			let pad_nib = unpacked_nib.saturating_sub(real_nib);
			let mut hits_real = 0usize;
			let mut hits_pad = 0usize;
			let mut sigs_real = BTreeSet::<u64>::new();
			let mut sigs_pad = BTreeSet::<u64>::new();
			for i in 0..states.len() {
				let st = field_to_usize(&states[i]);
				if st == 0 { continue; }
				let raw_st = st - 1;
				if !acdfa.is_final(raw_st) { continue; }
				let in_real = i <= real_nib;
				if in_real { hits_real += 1; }
				else { hits_pad += 1; }
				let pats = acdfa.final_to_patterns(raw_st);
				for pat in &pats {
					if let Some(sigs) = map_crit.get(pat) {
						for s in sigs {
							if let Some(sid) =
								sigs_to_id.get(s)
							{
								let v = *sid as u64;
								if in_real {
									sigs_real.insert(v);
								} else {
									sigs_pad.insert(v);
								}
							}
						}
					}
				}
			}
			let pad_only: Vec<u64> = sigs_pad.iter()
				.filter(|x| !sigs_real.contains(x))
				.copied().collect();
			emit_stdout(format!(
				"DEBUG USE 77320.1.pad b_igc={} seg_id={} \
				 real_nib={} pad_nib={} hits_real={} \
				 hits_pad={} pad_only_sigs.len={}",
				self.b_igc, _seg_id, real_nib, pad_nib,
				hits_real, hits_pad, pad_only.len()));
			emit_stdout(format!(
				"DEBUG USE 77320.1.pad_only_ids b_igc={} \
				 seg_id={} ids={:?}",
				self.b_igc, _seg_id, pad_only));
		}

		Ok( Arc::new(advice) )
	}



	/// Given its own gadget stmt_map: 9 range entries for
	///  ** 
	///   inp,oup,data,
	///   subtbl_inp, subtbl_oup, subtbl_data,
	///   failed_sigs, discharged_sigs,
	///  **
	/// return the map entries for each of its gadgets (note:
	///    entries solely depending on the gadget's own structure)
	/// Then return three secs of : si_data_info, si_inp_inof, si_oup_info
	fn get_gadgets_stmt_map(&self, vec_alloc: &Vec<(usize,usize)>)
	->(Vec<Vec<(usize,usize)>>, Vec<(usize,bool)>, 
		Vec<(usize,bool)>, Vec<(usize,bool)>){
		//1. get the allocation and make sure not exceeding boundaries
		assert!(vec_alloc.len()==9); 
		let (s_wd, e_wd) = vec_alloc[0];
		let (s_inp, _e_inp) = vec_alloc[1];
		let (s_oup, _e_oup) = vec_alloc[2];
		let (s_data, _e_data) = vec_alloc[3];
		let (s_subtbl_inp, _e_subtbl_inp) = vec_alloc[4];
		let (s_subtbl_oup, _e_subtbl_oup) = vec_alloc[5];
		let (s_subtbl_data, _e_subtbl_data) = vec_alloc[6];
		let (s_failed_sigs, e_failed_sigs) = vec_alloc[7];
		let (_s_discharged_sigs, _e_discharged_sigs) = vec_alloc[8];
		let wlen = self.max_word_len();
		assert!(e_wd - s_wd + 1 == wlen);
		let mut vec_res= vec![];
		let (final_states_len,join_buf_capacity,sig_buf_capacity,mlen)
			 = self.capacity.get_old_stats();
	
		//1. word extract gadget prob statement:
		// [word; act_w_len; extracted_word, no_inp/out, subtbl_ids]
		// NOTE: right bound is INCLUDED!
		let we = vec![(s_wd, e_wd), (s_data, s_data + wlen*LEGS),
			(s_subtbl_data, s_subtbl_data + wlen*LEGS)];
		let we_len = we.iter().map(|x| x.1-x.0+1).sum::<usize>();
		assert!(we_len==self.gadgets[0].lock().unwrap().get_msg_size().0);
		vec_res.push(we);


		//2. dfa_crit problem statement
		// [inp; oup; data; subtbl_id (inp; states; oup; trans)]
		let nlen = wlen * LEGS;
		let dfa_data_start = s_data+1;
		let dfa_data_len = 3*nlen-1;
		let dfa_subtbl_inp_start = s_subtbl_inp;
		let dfa_subtbl_oup_start = s_subtbl_oup;
		let dfa_subtbl_states_start = s_subtbl_data + 1 + nlen;
		let dfa_subtbl_states_len= nlen-1;
		let dfa_subtbl_trans_start = s_subtbl_data + nlen + nlen; 
		let dfa_subtbl_trans_len= nlen;
		let dfa_crit = vec![
			(s_inp, s_inp), 
			(s_oup, s_oup),
			(dfa_data_start, dfa_data_start+dfa_data_len-1),
			(dfa_subtbl_inp_start, dfa_subtbl_inp_start),
			(dfa_subtbl_states_start,
				dfa_subtbl_states_start+dfa_subtbl_states_len-1),
			(dfa_subtbl_oup_start, dfa_subtbl_oup_start),
			(dfa_subtbl_trans_start, dfa_subtbl_trans_start
				+dfa_subtbl_trans_len-1),
			];
		vec_res.push(dfa_crit);

		//3. pack_crit gadget problem statement structure
		//[data; subtbl_id]
		let (olen,jlen,slen) = (final_states_len, 
			join_buf_capacity, sig_buf_capacity);
		let pack_crit= vec![
			(s_inp, s_inp),  //the input state
			(s_data+1+nlen, s_data+1+nlen+ nlen-2), //the nlen-1 states in mid 
					//NOTE: this is BORROWED from the dfa_data
			(s_oup, s_oup), //the state in output buffer
			(s_data+3*nlen, s_data+3*nlen + mlen-1), //the unique states
			(s_data+3*nlen+mlen, s_data+3*nlen+mlen + mlen-1), //the m_table
			(s_data+3*nlen+2*mlen, s_data+3*nlen+2*mlen 
				+ olen-1), //final states
			(s_subtbl_data+3*nlen, s_subtbl_data+3*nlen+ mlen-1), //subtbl_id 
								//for unique_states
			(s_subtbl_data+3*nlen+mlen, s_subtbl_data+3*nlen+mlen
					+ mlen-1), //subtbl for m_table
			(s_subtbl_data+3*nlen+2*mlen, s_subtbl_data+3*nlen+2*mlen +olen-1),
								//sub
								//for final states

		];
		vec_res.push(pack_crit);

		//4. statement for sigs
		// [inp; oup; data; sub_tbl; failed_sigs]
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: final_states_len,
			join_buf_capacity: join_buf_capacity,
			sig_buf_capacity: sig_buf_capacity,
			//NOTE that this is the REAL VALUE
			//not allowing one moreentry.
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};
		//data_len excluding the input of final_states
		let sig_data_len = SigGadgetData::<F>::get_len(&sig_cap) - olen; 
		let sig_data_start = s_data+3*nlen+2*mlen+olen; //
			//the part EXCLUDING the final states
		//see subtbl_data definition in build_stement_comp
		let sig_st_start = s_subtbl_data + 3*nlen + 2*mlen + olen;
			//the part EXCLUDING final states
		let sig_st_len = sig_data_len;  //data (excluding fs input)
		let sig_st_oup_start = s_subtbl_oup +  1;
		let sig_st_oup_len = slen;
		if B_DEBUG {
			let sig_gadget = &self.gadgets[3];
			let (stmt_len,_,_,_) = sig_gadget.lock().unwrap().get_msg_size();
			assert!( stmt_len == 
				slen + slen + 
				sig_data_len+olen + 
				sig_st_len + 
				sig_st_oup_len + 
				slen //the last failed_sig part
				);
		}


		let sigs_range = vec![
			(s_inp+1, s_inp+1 + slen-1),  //inp
			(s_oup+1, s_oup+1 + slen-1),  //oup
			(sig_data_start-olen, sig_data_start-olen + olen-1), 
				//the final states (ACTUALLY imported from pack.rs last part)
			(sig_data_start, sig_data_start +  sig_data_len-1), //data without final states input
			(sig_st_start, sig_st_start + sig_st_len-1), //subtbl_ids (data part)
			(sig_st_oup_start, sig_st_oup_start+ sig_st_oup_len-1),//st_oup
				//excluding oup
			(s_failed_sigs, e_failed_sigs), //failed sigs
		];
		vec_res.push(sigs_range);

		//2. build the results
		assert!(vec_res.len()==self.num_gadgets());
		let vec_si_data_info = vec![ //chunk infor for si_data
			// *** see subtbl_data definition in build_statement_comp ***
			// -- the word extract generated data
			(1, true), // vec![zero], //act_wrd_len
			// -- the fsm gadget generated data
			(nlen, true), // vec![f_char; nlen], //the extracted word
			(nlen-1, true), //vec![f_crit_states; nlen-1], //the states
			(nlen, true), // vec![f_crit_trans; nlen], //the transitions
			// -- the pack gadget generated data
			(mlen, false), //unique_states (dynamically generated)
			(mlen, true), // vec![zero; mlen], //the m_table
			(olen, true), 	//final states (all zero, no need to check
							//as there are 2-directoinal lookup from
							//unique states
			// -- the sig gadget generated data
			//	advice.sigs_advice.gen_subtbl_id_for_data(), (below)
			(olen, false),  //all gen_sids are generated run time -> false
			(olen, false),
			(olen, true),
			(jlen, false),
			(jlen, false),
			(jlen, true),
			(jlen, true),
			(slen, true),
			(slen, true),
			(slen, true),
			(jlen, true),
			(sig_cap.count_sig_no_crit_pat, false), //ids_no_pat
			(1, true),

		];
		let total_si_info_size = vec_si_data_info.iter().map(|(s,_)| s)
			.sum::<usize>();
		let total_data_size = vec_alloc[3].1 - vec_alloc[3].0 + 1;
		let total_si_data_size = vec_alloc[6].1 - vec_alloc[6].0 + 1;
		assert!(total_si_info_size==total_data_size);
		assert!(total_si_info_size==total_si_data_size);

		let vec_si_inp_info = vec![//chunk info for si_inp
			//word_extract and fsm
			(1, true), //state
			(slen, true), //signatures
		];
		let total_si_inp_info_size = vec_si_inp_info.iter().map(|(s,_)| s)
			.sum::<usize>();
		assert!(total_si_inp_info_size == vec_alloc[4].1-vec_alloc[4].0+1);
		assert!(vec_alloc[1].1-vec_alloc[1].0==vec_alloc[4].1-vec_alloc[4].0);
		let vec_si_oup_info = vec_si_inp_info.clone();

		(vec_res, vec_si_data_info, vec_si_inp_info, vec_si_oup_info)
	}

	/// return the inp, oup, data, failed, discharged_sigs
	/// and 3 subtable segments. (8 vecs)
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
	fn build_statement_comp(&self, _comp_id: usize, _stmt_map_id: usize, word_seg: &Vec<F>, actual_word_len: usize, _lkup: &Arc<LK>, _extra_info: &StatementExtraInfo<F>, advice: &Arc<dyn NdAdvice + Send + Sync>, _cfg: &StatementConfig, _stmt_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>{
		let log_level = LOG7;
		let b_perf = log_level >= read_global_config().log_level;

		//1. take the advice
		let (final_states_len,join_buf_capacity,sig_buf_capacity,mlen)
			 = self.capacity.get_old_stats();
		let advice = advice.as_any().downcast_ref::<CpAdvice<F>>()
			.expect("downcast err!");
		let (olen,jlen,slen) = (final_states_len,
			join_buf_capacity, sig_buf_capacity);
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: olen,
			join_buf_capacity: jlen,
			sig_buf_capacity: slen,
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};

		//2. build inp/oup/data and 3 segments of subtbl_ids
		let _zero = F::zero();
		let wlen = word_seg.len();
		let olen = final_states_len;
		let sizes = self.get_sizes();
		let (inp_len, oup_len, data_len) =  (sizes[0], sizes[1], sizes[2]);
		assert!(inp_len==oup_len);
		let inp = advice.inp_buf.clone();
		assert!(inp.len()==inp_len);
		let oup = vec![
		  vec![advice.dfa_crit_advice.states[advice.dfa_crit_advice.states.len()-1]],  		//states
		  advice.sigs_advice.oup.clone(), //the oup_sigs
		].concat(); 
		assert!(oup.len()==oup_len);

		//3. build the data
		let nlen = wlen * LEGS;
		let wd_data = &advice.wd_extract_advice.data.clone();
		assert!(wd_data[0]==F::from(actual_word_len as u32));
		assert!(wd_data.len()==wlen*LEGS + 1);
		assert!(advice.dfa_crit_advice.states.len()==nlen+1);
		assert!(advice.dfa_crit_advice.trans.len()==nlen);
		assert!(advice.packfinal_crit_advice.unique_states.len()==mlen);
		assert!(advice.packfinal_crit_advice.m_table.len()==mlen);
		assert!(advice.packfinal_crit_advice.oup_states.len()==olen);
		let data_sigs = advice.sigs_advice.data.clone()
			.to_vec()[olen..].to_vec(); //reason: oup_states
										//shared between pack.rs and sigs.rs
		assert!(data_sigs.len()==SigGadgetData::<F>::get_len(&sig_cap) - olen);
		let data = vec![
			advice.wd_extract_advice.data.clone(),
			advice.dfa_crit_advice.states[1..nlen].to_vec(),
			advice.dfa_crit_advice.trans.clone(),
			advice.packfinal_crit_advice.unique_states.clone(),
			advice.packfinal_crit_advice.m_table.clone(),
			advice.packfinal_crit_advice.oup_states.clone(),
			data_sigs
		].concat();
		assert!(data.len()==data_len);


		//4. build the subtbl
		let zero = F::zero();
		let f_char = F::from(CHAR);
		
		let f_crit_states = if self.b_igc {F::from(CRIT_IGC_STATES)}
			else {F::from(CRIT_STATES)};
		let f_crit_trans = if self.b_igc {F::from(CRIT_IGC_TRANSITIONS)}
			else {F::from(CRIT_TRANSITIONS)};
		let _f_crit_final= if self.b_igc {F::from(CRIT_IGC_FINAL)}
			else {F::from(CRIT_FINAL)};
		let f_range2 = F::from(RANGE2);

		let subtbl_inp = vec![
			vec![f_crit_states], //state
			vec![f_range2; slen], //signatures in range2 
		].concat();

		let subtbl_oup = vec![
			vec![f_crit_states],
			advice.sigs_advice.gen_subtbl_id_for_oup(), //signatures in range2
		].concat();

		let subtbl_data = vec![
			// -- the word extract generated data
			vec![zero], //act_wrd_len
			// -- the fsm gadget generated data
			vec![f_char; nlen], //the extracted word
			//vec![f_crit_states; nlen-1], //the states
			vec![f_range2; nlen-1], //ONLY need to bind it to rg2
									//transition sid will ENFORCE the state
			vec![f_crit_trans; nlen], //the transitions
			// -- the pack gadget generated data
			advice.packfinal_crit_advice
				.subtbl_id.clone(), //for unque states, final states, m_tbl
			// -- the sig gadget generated data
			advice.sigs_advice.gen_subtbl_id_for_data(), //it has
				//excluded the final_states, which already in pack.rs
		].concat();
		assert!(subtbl_data.len()==data.len());
		assert!(subtbl_inp.len()==inp.len());
		assert!(subtbl_oup.len()==oup.len());

		//4. the failed sigs and discharged sigs
		let failed_sigs = advice.sigs_advice.oup.clone();
		assert!(failed_sigs.len()==sig_buf_capacity);
		if !failed_sigs.contains(&F::zero()){
			return Err(Error::CapErr(vec![(format!("cp::sigs to accomodate one dummy entry: "), failed_sigs.len() + 1
			)]));
		}
		let discharged_sigs = vec![F::zero()]; //dummy entry
		// 2026-05-16: probe 77318.2 — CpComponentMapper output.
		// CP returns a real failed_sigs (from sigs_advice.oup) but a
		// DUMMY single-zero discharged_sigs. Any non-zero entry in
		// failed_sigs is therefore expected to be covered by a
		// SED/DFA component's discharged_sigs downstream. If
		// 77318.1.c<i>.MULTISET_MISMATCH fires on the CP component
		// it just means CP-side failed entries weren't covered —
		// the bug is then in whichever later component should have
		// covered them.
		if std::env::var("ZKR_PROBE_77317").is_ok() {
			use folding_schemes::folding::foldpot::utils::
				probe_77317_dump_f_vec;
			emit_stdout(format!(
				"DEBUG USE 77318.2: CpComponentMapper b_igc={} \
				 failed.len={} discharged.len={} (dummy [0])",
				self.b_igc, failed_sigs.len(),
				discharged_sigs.len()));
			probe_77317_dump_f_vec("2.cp.failed",
				"cp.failed_sigs", &failed_sigs);
		}
		
		if b_perf{
			log(self.job_id, log_level, &format!("## build_stmt: CP b_igc: {}. Failed sigs:",
				self.b_igc));
			for i in 0..failed_sigs.len(){
				log(self.job_id, log_level, &format!(" -- {} => {}",
					i, failed_sigs[i]));
			}
		}

		Ok(	vec![inp, oup, data, subtbl_inp, subtbl_oup, subtbl_data,
			failed_sigs, discharged_sigs] )
	}
}

impl <F:PrimeField + ColEle, LK: LookupTableTwoCol<F> + Send + Sync + 'static>
	ComponentMapperCloneBox<F,LK> for CpComponentMapper<F,LK>
where F: 'static,
{
	fn clone_arc_component_mapper(&self)
		-> Arc<Mutex<dyn ComponentMapper<F,LK> + Send + Sync>> {
		let new_gadgets: Vec<Arc<Mutex<
			dyn SigmaGadget<F> + Send + Sync>>> =
			self.gadgets.iter().map(|g|
				g.lock().unwrap().clone_arc_sigma_gadget()
			).collect();
		Arc::new(Mutex::new(CpComponentMapper::<F,LK>{
			_f: PhantomData,
			_lk: PhantomData,
			capacity: Clone::clone(&self.capacity),
			b_igc: self.b_igc,
			gadgets: new_gadgets,
			clamdb: self.clamdb.clone(),
			job_id: self.job_id,
		}))
	}
}
