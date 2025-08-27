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
//       -- introduced by gadget pack_fs
//       transitions [62*wlen]
//       final_states [final_states_len]
//       m_table [final_states_len]
//       -- introduced by gadget sigs
//       many items (call its advice to generate data item
// failed_sigs: the COPY of the  oup_sigs (last #sigs elements of oup)
// discharged_sigs: size 0

// subtbl: follow inp/oup/data

use std::{
	marker::PhantomData,
	rc::{Rc},
	cell::{RefCell},
	fmt::{Debug},
	collections::{HashMap},
};
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
	circs::composable_gadget_mapper::ComponentMapper,
	gadgets::word_extract::{WordExtractGadget,LEGS,WordExtractAdvice},
	gadgets::fsm::{FsmGadget,FsmAdvice},
	gadgets::pack::{PackFinalGadget,PackFinalAdvice},
	gadgets::sigs::{GetSigAdvice,SigGadgetCapacity,SigGadgetData,GetSigGadget},
	gadgets::commons::{print_vec},
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

	/// the capacity for PackFinal to hold final states
	pub final_states_len: usize,

	/// the capacity of join buf for the sigs gadget
	pub join_buf_capacity: usize,

	/// the capacity of signature inp/oup of sigs gadget
	pub sig_buf_capacity: usize,
}

impl Capacity for CpCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		let other = r_other.as_any().downcast_ref::<CpCapacity>()
			.expect("downcast err"); 

		self.max_word_len>= other.max_word_len &&
		self.final_states_len>= other.final_states_len &&
		self.join_buf_capacity>= other.join_buf_capacity &&
		self.sig_buf_capacity>= other.sig_buf_capacity
	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(CpCapacity{
			max_word_len: self.max_word_len,
			final_states_len: self.final_states_len,
			join_buf_capacity: self.join_buf_capacity,
			sig_buf_capacity: self.sig_buf_capacity
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

/// The non-deterministic advice for the CP component
#[derive(Debug)]
pub struct CpAdvice<F:PrimeField>{
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

impl <F:PrimeField> NdAdvice for CpAdvice<F>{
	fn as_any(&self) -> &dyn Any{ self }
}

impl <F:PrimeField> CpAdvice<F>{
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
		)->Self{
		//1. build the word extraction gadget's advice
		let inp_state = inp_buf[0].clone();
		let wd_extract_advice = WordExtractAdvice::<F>
			::new(word_seg, actual_size);
		let nibbles = wd_extract_advice.data[1..].to_vec();
		let dfa_crit_advice = FsmAdvice::<F>
			::new(&nibbles, dfa_crit, inp_state, fsm_id as u32);


		//2. build the packing final states gadget's advice
		let f_nonfinal_id = F::from((fsm_id+ 1) as u32);
		let f_final_id = F::from((fsm_id+ 2) as u32);
		let subtbl_ids = dfa_crit_advice.states.iter().map(|s|{
			let val_s = field_to_usize(s);
			let tbl_id = if dfa_crit.is_final(val_s - 1) {f_final_id} 
				else {f_nonfinal_id};

			tbl_id
		}).collect::<Vec<F>>();
		let packfinal_crit_advice = PackFinalAdvice::<F>
			::new(&dfa_crit_advice.states, &subtbl_ids, &f_final_id, 
				capacity.final_states_len);

		//3. build the advice for the sigs gadget
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: capacity.final_states_len,
			join_buf_capacity: capacity.join_buf_capacity,
			sig_buf_capacity: capacity.sig_buf_capacity,
			count_sig_no_crit_pat: vec_sig_id_no_crit_pat.len(),
		};
		let inp_sigs = inp_buf[1..capacity.sig_buf_capacity+1].to_vec();
		
		let sigs_advice = GetSigAdvice::<F>::new(
			&packfinal_crit_advice.oup_states, &inp_sigs, sig_cap, 
			dfa_crit, map_crit_pat, sig_to_id, fsm_id, vec_sig_id_no_crit_pat);
		Self{
			wd_extract_advice,
			dfa_crit_advice,
			packfinal_crit_advice,
			sigs_advice,
			inp_buf: inp_buf.clone(),
		}
	}
}


#[derive(Clone,Debug)]
pub struct CpComponentMapper<F:PrimeField, LK: LookupTableTwoCol<F>>{ 
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub capacity: CpCapacity,

	pub b_igc: bool,

	/// its own gadgets 
	pub gadgets: Vec<Rc<RefCell<dyn SigmaGadget<F>>>>,

	/// clamdb
	pub clamdb: Rc<ClamavDB<F>>,
}

impl <F:PrimeField,LK:LookupTableTwoCol<F>> CpComponentMapper<F,LK>{
	/// constructor needs the max word len to handle the capacity
	/// of PackFinal (number of final states), and reference to clamdb

	pub fn new(
		cp_capacity: CpCapacity,
		clamdb: Rc<ClamavDB<F>>,
		b_igc: bool //whether it's for ignore case ACDFA
	) ->Self{
		//1. build the gadgets
		let nlen = cp_capacity.max_word_len * LEGS;
		let state_bits = clamdb.dfa_crit.state_part_bits;
		let fsm_id = if b_igc {CRIT_IGC_INIT} else {CRIT_INIT};

		let g_extract = WordExtractGadget::<F>::new(cp_capacity.max_word_len);
		let dfa_crit = FsmGadget::<F>::new(nlen, fsm_id, state_bits); 
		let pack_crit = PackFinalGadget::<F>::new(nlen+1, 
			cp_capacity.final_states_len, fsm_id);

		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: cp_capacity.final_states_len,
			join_buf_capacity: cp_capacity.join_buf_capacity,
			sig_buf_capacity: cp_capacity.sig_buf_capacity,
			count_sig_no_crit_pat: clamdb.vec_sigs_no_critical_pat.len(),  
		};
		let sig_gadget= GetSigGadget::<F>::new(&sig_cap, fsm_id);
		let gadgets: Vec<Rc<RefCell<dyn SigmaGadget<F>>>> = vec![ 
			Rc::new(RefCell::new(g_extract)), //word -> nibbles
			Rc::new(RefCell::new(dfa_crit)), //run through dfa_crit
			Rc::new(RefCell::new(pack_crit)), //pack trace to final states
			Rc::new(RefCell::new(sig_gadget)), //generate signatures
		];
		assert!(clamdb.as_ref().vec_sigs_no_critical_pat.len()
			<cp_capacity.sig_buf_capacity,
			"vec_sigs_no_crit_pat.len(): {} > sig_buf_capacity: {}",
			clamdb.as_ref().vec_sigs_no_critical_pat.len(), 
			cp_capacity.sig_buf_capacity);

		Self{
			_f: PhantomData, 
			_lk: PhantomData, 
			capacity: cp_capacity,
			gadgets,
			b_igc,
			clamdb
		}
	}
}

impl <F:PrimeField, LK: LookupTableTwoCol<F>> ComponentMapper<F,LK> for CpComponentMapper<F,LK>{
	fn set_container_config(&mut self, _r_advice: &Rc<dyn NdAdvice>){ 
		// no need to handle for legacy code.
	}

	fn get_capacity(&self)->Rc<dyn Capacity>{
		Rc::new( Clone::clone(&self.capacity) )
	}

	fn create_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>{  
		self.gadgets.clone()
	}

	/// return the number of gadgets
	fn num_gadgets(&self) -> usize{self.gadgets.len() }

	/// return the max word capacity of the component
	fn max_word_len(&self)->usize{ self.capacity.max_word_len }

	/// return the sizes of inp, oup, data, failed_sigs, discharged_sigs
	fn get_sizes(&self)->Vec<usize>{
		//1. gadget of word extension
		let wlen = self.capacity.max_word_len;
		let nlen = LEGS * wlen; //nibble len
		let flen = self.capacity.final_states_len;
		let clen = self.clamdb.vec_sigs_no_critical_pat.len();
		let inp_g_ext = 0;
		let oup_g_ext = 0;
		let data_g_ext = 1 + nlen;

		let inp_dfa= 1;
		let oup_dfa= 1;
		let data_dfa= 2*nlen-1; //NOTE: excluding the gadget's
									 // "shared" nibbles with w_extract
		let data_pack= 2*flen; // the increased are final_staes, m_table

		let inp_sigs= self.capacity.sig_buf_capacity;
		let oup_sigs= self.capacity.sig_buf_capacity;
		let data_sigs = self.capacity.final_states_len * 3 
			+ self.capacity.join_buf_capacity * 5
			+ self.capacity.sig_buf_capacity * 3
			+ clen + 1; //for the sigs_no_crit_pat and its count

		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: self.capacity.final_states_len,
			join_buf_capacity: self.capacity.join_buf_capacity,
			sig_buf_capacity: self.capacity.sig_buf_capacity,
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};
		assert!(data_sigs == SigGadgetData::<F>::get_len(&sig_cap) 
			- self.capacity.final_states_len);

		//2. collect all data
		let vec_inp_len = vec![inp_g_ext, inp_dfa, inp_sigs];
		let vec_oup_len = vec![oup_g_ext,  oup_dfa, oup_sigs];
		let vec_data_len = vec![data_g_ext,  data_dfa, data_pack, data_sigs];

		//3. sum all
		let inp_size:usize = vec_inp_len.iter().map(|x| x).sum();
		let oup_size:usize = vec_oup_len.iter().map(|x| x).sum();
		let data_size:usize = vec_data_len.iter().map(|x| x).sum();
		let failed_sig_size = self.capacity.sig_buf_capacity;
		let discharged_sig_size = 0;
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

	/// Also responsible for generating nd_advice
	fn gen_nd_advice_no_limit(&self, word: &Vec<F>, _word_info: &WordInfo,
		prev_adv: Option<Rc<dyn NdAdvice>>)
		->Option<(Rc<dyn Capacity>, Rc<dyn NdAdvice>)>{
		//1. expand to full length
		let (zero,one) = (F::zero(),F::one());
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word);

		//2. build the capaicty and advice
		let capacity = &self.capacity;
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
		let inp_sigs = prev_adv.map_or(vec![zero; capacity.sig_buf_capacity], 
		|adv|{
			let adv= adv.as_any().downcast_ref::<CpAdvice<F>>(); 
			let last_oup_sigs = &adv.unwrap().sigs_advice.oup;
			last_oup_sigs.to_vec()
		});
		let inp_buf = vec![ vec![inp_state], inp_sigs].concat();
		
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

		let advice = CpAdvice::<F>::new(
			&word_seg, 
			word.len(), 
			&capacity, 
			&inp_buf, 
			acdfa,
			map_crit,
			sigs_to_id,
			fsm_id as usize,
			&vec_sig_id_no_crit_pat,
		);

		//3. build the advice
		let cap2 = Clone::clone(&self.capacity);
		Some((Rc::new(cap2), Rc::new(advice)) )
	}

	/// Given its own gadget stmt_map: 9 range entries for
	///  ** 
	///   inp,oup,data,
	///   subtbl_inp, subtbl_oup, subtbl_data,
	///   failed_sigs, discharged_sigs,
	///  **
	/// return the map entries for each of its gadgets (note:
	///    entries solely depending on the gadget's own structure)
	fn get_gadgets_stmt_map(&self, vec_alloc: &Vec<(usize,usize)>)
	->Vec<Vec<(usize,usize)>>{
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

	
		//1. word extract gadget prob statement:
		// [word; act_w_len; extracted_word, no_inp/out, subtbl_ids]
		// NOTE: right bound is INCLUDED!
		let we = vec![(s_wd, e_wd), (s_data, s_data + wlen*LEGS),
			(s_subtbl_data, s_subtbl_data + wlen*LEGS)];
		let we_len = we.iter().map(|x| x.1-x.0+1).sum::<usize>();
		assert!(we_len==self.gadgets[0].borrow().get_msg_size().0);
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
		let (olen,_jlen,slen) = (self.capacity.final_states_len,
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity);
		let pack_crit= vec![
			(s_inp, s_inp),  //the input state
			(s_data+1+nlen, s_data+1+nlen+ nlen-2), //the nlen-1 states in mid 
			(s_oup, s_oup), //the state in output buffer
			(s_data+3*nlen, s_data+3*nlen + olen-1), //the final states
			(s_data+3*nlen+olen, s_data+3*nlen+olen + olen-1), //the m_table
			(s_subtbl_data+3*nlen, s_subtbl_data+3*nlen+ olen-1), //subtbl_id for final_states
		];
		vec_res.push(pack_crit);

		//4. statement for sigs
		// [inp; oup; data; sub_tbl; failed_sigs]
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: self.capacity.final_states_len,
			join_buf_capacity: self.capacity.join_buf_capacity,
			sig_buf_capacity: self.capacity.sig_buf_capacity,
			//NOTE that this is the REAL VALUE
			//not allowing one moreentry.
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};
		//data_len excluding the input of final_states
		let sig_data_len = SigGadgetData::<F>::get_len(&sig_cap) - olen; 
		let sig_data_start = s_data+3*nlen+olen + olen;
		//see subtbl_data definition in build_stement_comp
		let sig_st_start = s_subtbl_data + 3*nlen + 2*olen; 
		let sig_st_len = sig_data_len;  //data (excluding fs input)
		let sig_st_oup_start = s_subtbl_oup +  1;
		let sig_st_oup_len = slen;
		#[cfg(test)]{
			let sig_gadget = &self.gadgets[3];
			let (stmt_len,_,_,_) = sig_gadget.borrow().get_msg_size();
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
			(s_data+3*nlen, s_data+3*nlen + olen-1), //the final states
			(sig_data_start, sig_data_start +  sig_data_len-1), //data without final states input
			(sig_st_start, sig_st_start + sig_st_len-1), //subtbl_ids (data part)
			(sig_st_oup_start, sig_st_oup_start+ sig_st_oup_len-1),//st_oup
			(s_failed_sigs, e_failed_sigs), //failed sigs
		];
		vec_res.push(sigs_range);

		//2. build the results
		assert!(vec_res.len()==self.num_gadgets());
		vec_res
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
	fn build_statement_comp(&self, _comp_id: usize, _stmt_map_id: usize, word_seg: &Vec<F>, actual_word_len: usize, _lkup: &Rc<RefCell<LK>>, _extra_info: &StatementExtraInfo<F>, advice: &Rc<dyn NdAdvice>, _cfg: &StatementConfig, _stmt_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>{
		let b_debug = true;

		//1. take the advice
		let advice = advice.as_any().downcast_ref::<CpAdvice<F>>()
			.expect("downcast err!");
		let (olen,jlen,slen) = (self.capacity.final_states_len,
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity);
		let sig_cap = SigGadgetCapacity{
			final_states_buf_capacity: olen,
			join_buf_capacity: jlen,
			sig_buf_capacity: slen,
			count_sig_no_crit_pat: self.clamdb.vec_sigs_no_critical_pat.len(), 
		};

		//2. build inp/oup/data and 3 segments of subtbl_ids
		let _zero = F::zero();
		let wlen = word_seg.len();
		let olen = self.capacity.final_states_len;
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
		assert!(advice.packfinal_crit_advice.oup_states.len()==olen);
		assert!(advice.packfinal_crit_advice.m_table.len()==olen);
		let data_sigs = advice.sigs_advice.data.clone()
			.to_vec()[olen..].to_vec();
		assert!(data_sigs.len()==SigGadgetData::<F>::get_len(&sig_cap) - olen);
		let data = vec![
			advice.wd_extract_advice.data.clone(),
			advice.dfa_crit_advice.states[1..nlen].to_vec(),
			advice.dfa_crit_advice.trans.clone(),
			advice.packfinal_crit_advice.oup_states.clone(),
			advice.packfinal_crit_advice.m_table.clone(),
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
			vec![f_crit_states; nlen-1], //the states
			vec![f_crit_trans; nlen], //the transitions
			// -- the pack gadget generated data
			advice.packfinal_crit_advice
				.subtbl_id.clone(), //for final states, padded
			vec![zero; olen], //the m_table
			// -- the sig gadget generated data
			advice.sigs_advice.gen_subtbl_id_for_data(),
		].concat();
		assert!(subtbl_data.len()==data.len());
		assert!(subtbl_inp.len()==inp.len());
		assert!(subtbl_oup.len()==oup.len());

		//4. the failed sigs and discharged sigs
		let failed_sigs = advice.sigs_advice.oup.clone(); 
		assert!(failed_sigs.len()==self.capacity.sig_buf_capacity);
		let discharged_sigs = vec![];
		
		if b_debug{
			print_vec(&format!("DEBUG USE 6901: CP b_igc: {}, failed_sigs", 
				self.b_igc), &failed_sigs);
		}

		Ok(	vec![inp, oup, data, subtbl_inp, subtbl_oup, subtbl_data, 
			failed_sigs, discharged_sigs] )
	}
}
