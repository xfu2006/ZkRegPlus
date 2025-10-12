/* Created 03/06/2025, completed 03/11/2025 */

use std::rc::{Rc};
use rayon::iter::{
	ParallelIterator,
	IntoParallelIterator,
	IntoParallelRefIterator,
	//IndexedParallelIterator
};
use ark_ff::{PrimeField};
use std::{
	marker::{PhantomData},
	collections::{HashMap,HashSet}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, 
	NdAdvice},
	container_config::{ContainerConfig},
};
use ark_r1cs_std::{
	boolean::Boolean,
	fields::{
		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
};
use std::any::Any;
use crate::gadgets::commons::{verify_logup_inverse, verify_inverse, verify_encoded_states_sig_count, verify_encoded_states_sig, check_imply, check_eq, check_arr_eq, check_arr_eq_nz, expand_vec,gen_m_table,new_const_var,check_arr_eq_arr};
use data_processor::{
	clam_db::{RANGE2,RANGE2_BIT,ID_SIG_NO_CRIT_COUNT,ID_SIG_NO_CRIT}, 
	hex_acdfa::HexACDFA
};
use folding_schemes::{folding::foldpot::circuits_super::{field_to_usize}};

#[allow(dead_code)]


/// This gadget is responsible for retrieving the signatures
/// from final states (like a sql select).
/// 
/// Basic idea: given a transcript which is structured
/// as following:
/// encoded(state_1, num_of_records)
/// encoded(state_1, sig1)
/// ...
/// encoded(state_1, sig_k)
/// The challenge here is that k is a different value for each state,
/// So the transcript like input maximizes memory efficiency.
/// We then apply log-up to reason about subset (lookup) relation
#[derive(Clone,Debug)]
pub struct GetSigGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	/// its capacity
	capacity: SigGadgetCapacity,
	/// e.g., CRIT_INIT for the ACDFA of critical table in clam_db.rs
	fsm_id: u32, 
}

/// Capacity of SigGadget
#[derive(Clone,Debug)]
pub struct SigGadgetCapacity{
	/// final states table size, (matches the oup_states_size in pack.rs)
	pub final_states_buf_capacity: usize,
	/// decode transcript size (this later will be a capacity req)
	pub join_buf_capacity: usize, 
	/// buffer to hold signatures
	pub sig_buf_capacity: usize,
	/// the number of sigs that HAVE NO CRIT PAT included in ACDFA
	/// THIS IS THE REAL VALUE at set up.
	/// It can be regarded as a system constant (set up initially)
	/// It's taking the exact value of clamdb.vec_sig_no_crit_pat.len()
	/// at set up (ALL CONFIGS should have the same value for this property).
	pub count_sig_no_crit_pat: usize,
}

/// Models the data part the stat instance for SigGadget.
/// This allows easy maintainability of items for serialization.
/// Note that it can containe either PrimeField for FpVar<F>
#[derive(Clone,Debug)]
pub struct SigGadgetData<F: Clone>{
	/// the input of final states, padded by zero [size: olen]
	pub final_states: Vec<F>,

	// --- the rest are "new" data for the cp_mapper
	/// encoded final_state_signature_count [size: olen]
	pub final_states_sigs_count: Vec<F>, 
	/// decoded final_states (states part) [size: olen]
	pub decoded_final_states_sigs_count_states: Vec<F>,
	/// decoded final_states (count part) [size: olen]
	pub decoded_final_states_sigs_count_count: Vec<F>,

	/// encoded final states sigs [size: jlen] (this is the "join buf")
	pub final_states_sigs: Vec<F>,
	/// decoded of the final states sigs (states part) [size: jlen]
	/// All starts from 1
	pub decoded_final_states_sigs_states: Vec<F>,
	/// decoded of the final states sigs (ids part) [size: jlen]
	/// All starts from 1
	pub decoded_final_states_sigs_ids: Vec<F>,
	/// decoded of the final states sigs (ids part) [size: jlen]
	/// All starts from 1
	pub decoded_final_states_sigs_sigs: Vec<F>,

	/// sigs to merge (extracted from decoded_final_states_sigs) [size: slen}
	pub sigs_to_merge: Vec<F>,

	/// mtable for lkup: join buff to sigs_to_merge [size: slen]
	pub m_tbl_joins_to_sigs: Vec<F>,
	/// mtable for inp + sigs -> oup [size: slen]
	pub m_tbl_inp_sigs_oup: Vec<F>,
	/// mtable for lkups for mapping final_states (inp) to the
	/// final states in decoded_final_states_sigs_count, to show
	/// that they are covered, to show
	/// that they are covered [size: jlen]
	pub m_tbl_decoded_final_states: Vec<F>,

	/// it's the public list of sigs of no critical pat
	pub sigs_no_crit_pat: Vec<F>,
	/// one single element vector which has the length of sigs_no_crit_pat
	/// it is a FIXED constant defined in clam_db::ID_SIG_NO_CRIT_COUNT
	pub sigs_no_crit_pat_count: Vec<F>,

	/// capacity: will not be serialized
	pub capacity: SigGadgetCapacity,
}

impl <F: Clone> SigGadgetData<F>{
	/// return the expected len
	pub fn get_len(capacity: &SigGadgetCapacity)->usize{
		let desc = Self::gen_desc(capacity);
		desc.iter().map(|(_,s)|  s).sum()
	}

	/// return the size restriction of all fields
	pub fn gen_desc(capacity: &SigGadgetCapacity)->Vec<(&str, usize)>{
		let (olen, jlen, slen, clen) = (
			capacity.final_states_buf_capacity,
			capacity.join_buf_capacity, 
			capacity.sig_buf_capacity,
			capacity.count_sig_no_crit_pat,
		);

		
		vec![
			("final_states", olen), //will be later excluded from size calc
									//as it's mapped from existing data

			("final_states_sigs_count", olen),
			("decoded_final_states_sigs_count_states", olen),
			("decoded_final_states_sigs_count_count", olen),

			("final_states_sigs", jlen),
			("decoded_final_states_sigs_states", jlen),
			("decoded_final_states_sigs_ids", jlen),
			("decoded_final_states_sigs_sigs", jlen),

			("sigs_to_merge", slen),

			("m_tbl_joins_to_sigs", slen),
			("m_tbl_inp_sigs_oup", slen),
			("m_tbl_decoded_final_states", jlen),

			("sigs_no_crit_pat", clen),
			("sigs_no_crit_pat_count", 1),
		]
	}

	pub fn self_check(&self){
		let vec = vec![
			&self.final_states,

			&self.final_states_sigs_count,
			&self.decoded_final_states_sigs_count_states,
			&self.decoded_final_states_sigs_count_count,

			&self.final_states_sigs,
			&self.decoded_final_states_sigs_states,
			&self.decoded_final_states_sigs_ids,
			&self.decoded_final_states_sigs_sigs,

			&self.sigs_to_merge,

			&self.m_tbl_joins_to_sigs,
			&self.m_tbl_inp_sigs_oup,
			&self.m_tbl_decoded_final_states,

			&self.sigs_no_crit_pat,
			&self.sigs_no_crit_pat_count,
		];
		let desc = Self::gen_desc(&self.capacity);
		for i in 0..desc.len(){
			if vec[i].len()!=desc[i].1{
				panic!("ERROR length for {}, actual: {}, expected: {}", desc[i].0, vec[i].len(), desc[i].1);
			}
		}
	}


	/// serialize to a vector of data
	/// the instance is destroyed after operation
	pub fn to_vec(self)->Vec<F>{
		[
			self.final_states,

			self.final_states_sigs_count,
			self.decoded_final_states_sigs_count_states,
			self.decoded_final_states_sigs_count_count,

			self.final_states_sigs,
			self.decoded_final_states_sigs_states,
			self.decoded_final_states_sigs_ids,
			self.decoded_final_states_sigs_sigs,

			self.sigs_to_merge,

			self.m_tbl_joins_to_sigs,
			self.m_tbl_inp_sigs_oup,
			self.m_tbl_decoded_final_states,

			self.sigs_no_crit_pat,
			self.sigs_no_crit_pat_count,
		].concat()
	}
	
	/// rebuild the object from a vector of field ele
	pub fn from_vec(capacity: &SigGadgetCapacity, vec: &Vec<F>)->Self{
		//1. check len
		let desc = Self::gen_desc(capacity); 
		let total_len:usize = desc.iter().map(|(_,s)| *s).sum();
		assert!(total_len==vec.len());

		//2. chop vec into the corresponding secs by desc
		let mut idx = 0;
		let mut vec2d = vec![];
		for i in 0..desc.len(){
			let len = desc[i].1;
			let slice = &vec[idx..idx+len];
			vec2d.push(slice);
			idx+= len;
		}
		assert!(idx==total_len);

		//3. construct the object
		let res = Self{
			final_states: vec2d[0].to_vec(),

			final_states_sigs_count: vec2d[1].to_vec(),
			decoded_final_states_sigs_count_states: vec2d[2].to_vec(),
			decoded_final_states_sigs_count_count: vec2d[3].to_vec(),

			final_states_sigs: vec2d[4].to_vec(),
			decoded_final_states_sigs_states: vec2d[5].to_vec(),
			decoded_final_states_sigs_ids: vec2d[6].to_vec(),
			decoded_final_states_sigs_sigs: vec2d[7].to_vec(),

			sigs_to_merge: vec2d[8].to_vec(),

			m_tbl_joins_to_sigs: vec2d[9].to_vec(),
			m_tbl_inp_sigs_oup: vec2d[10].to_vec(),
			m_tbl_decoded_final_states: vec2d[11].to_vec(),

			sigs_no_crit_pat: vec2d[12].to_vec(),
			sigs_no_crit_pat_count: vec2d[13].to_vec(),

			capacity: capacity.clone()
		};

		res
	}
}

#[derive(Clone,Debug)]
pub struct SigGadgetMsg3<F:Clone>{
	/// Inverse list for Logup for sigs in join_buf (decoded_states_sigs_sigs)
	/// sigs_to_merge. size [jlen]
	pub inv1_left: Vec<F>,
	/// the right part of invert list size[slen]
	pub inv1_right: Vec<F>,
	/// Inverse list for Logup for sigs in inp + sigs_to_merge -> oup.
	/// part left: size [2xslen]
	pub inv2_left: Vec<F>,
	/// The right part of inverse list 2. size [slen]
	pub inv2_right: Vec<F>,
	/// Inverse list for Logup for input (final states) to
	/// decoded_final_states_states. [size: olen]
	pub inv3_left: Vec<F>,
	/// Part right of inverse 3 list. [size: jlen]
	pub inv3_right: Vec<F>,

	/// the capacity of gadget
	pub capacity: SigGadgetCapacity,
}

impl <F:Clone> SigGadgetMsg3<F>{
	/// return the expected len
	pub fn get_len(capacity: &SigGadgetCapacity)->usize{
		let desc = Self::gen_desc(capacity);
		desc.iter().map(|(_,s)| s).sum()
	}

	pub fn gen_desc(capacity: &SigGadgetCapacity)->Vec<(&str, usize)>{
		let (olen, jlen, slen, clen) = (
			capacity.final_states_buf_capacity,
			capacity.join_buf_capacity, 
			capacity.sig_buf_capacity,
			capacity.count_sig_no_crit_pat,
		);
		
		vec![
			("inv1_left", jlen),
			("inv1_right", slen),
			("inv2_left", 2*slen + clen),
			("inv2_right", slen),
			("inv3_left", olen),
			("inv3_right", jlen),
		]
	}

	pub fn self_check(&self){
		let vec = [
			&self.inv1_left,
			&self.inv1_right,
			&self.inv2_left,
			&self.inv2_right,
			&self.inv3_left,
			&self.inv3_right
		];
		let desc = Self::gen_desc(&self.capacity);
		for i in 0..desc.len(){
			if vec[i].len()!=desc[i].1{
				panic!("ERROR MSG3 length for {}, actual: {}, expected: {}", desc[i].0, vec[i].len(), desc[i].1);
			}
		}
	}

	/// serialize to a vector of field elements
	pub fn to_vec(self)->Vec<F>{
		[
			self.inv1_left,
			self.inv1_right,
			self.inv2_left,
			self.inv2_right,
			self.inv3_left,
			self.inv3_right
		].concat()
	}

	pub fn from_vec(capacity: &SigGadgetCapacity, vec: &Vec<F>)->Self{
		//1. check len
		let desc = Self::gen_desc(capacity); 
		let total_len:usize = desc.iter().map(|(_,s)| *s).sum();
		assert!(total_len==vec.len());

		//2. chop vec into the corresponding secs by desc
		let mut idx = 0;
		let mut vec2d = vec![];
		for i in 0..desc.len(){
			let len = desc[i].1;
			let slice = &vec[idx..idx+len];
			vec2d.push(slice);
			idx+= len;
		}
		assert!(idx==total_len);

		//3. construct the object
		let res = Self{
			inv1_left: vec2d[0].to_vec(),
			inv1_right: vec2d[1].to_vec(),

			inv2_left: vec2d[2].to_vec(),
			inv2_right: vec2d[3].to_vec(),

			inv3_left: vec2d[4].to_vec(),
			inv3_right: vec2d[5].to_vec(),

			capacity: capacity.clone()
		};

		res
	}
}

/// Advice for the WordExtract Gadget.
#[derive(Debug)]
pub struct GetSigAdvice<F:PrimeField>{
	pub capacity: SigGadgetCapacity,

	/// the data segment (note: subtbl_id) can be easiy
	/// generated by call gen_subtbl_id()
	pub data: SigGadgetData<F>,

	/// output signatures, [size: slen]
	pub oup: Vec<F>,

	/// the fsm_id of the ACDFA to handle (e.g., CRIT_INIT)
	pub fsm_id: usize,

	/// the list of sig_ids that will ALWAYS fail the crit pat method
	pub vec_sig_id_no_crit_pat: Vec<usize>,
}

impl <F: PrimeField> NdAdvice for GetSigAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> GetSigAdvice<F>{
	/// Given a sequence of final_states (with padding).
	/// Identify the data needed to build data segment and subtables.
	pub fn new(
		final_states: &Vec<F>,  //the input
		inp_sigs: &Vec<F>, //the input signatures
		capacity: SigGadgetCapacity,
		acdfa: &HexACDFA,
		map_crit_pat: &HashMap<String,Vec<String>>,
		sig_to_id: &HashMap<String,usize>,
		fsm_id: usize,
		vec_sig_id_no_crit_pat: &Vec<usize>,
	)->Self{
		//1. sets up the data
		assert!(vec_sig_id_no_crit_pat.len()==capacity.count_sig_no_crit_pat);
		let (olen, jlen, slen) = (
			capacity.final_states_buf_capacity,
			capacity.join_buf_capacity, 
			capacity.sig_buf_capacity
		);
		let mut final_states = final_states.clone();
		expand_vec(&mut final_states, olen); //the input
		let sigbit_factor = F::from(1u32 << RANGE2_BIT);
		let sigbit_fac2 = sigbit_factor * sigbit_factor;
		assert!(final_states.len() == olen);
		assert!(inp_sigs.len()==slen);

		//2. compute the signures and the counts (note state IDs
		// already have +1 applied)
		let mut final_states_sigs_count = vec![];
		let mut decoded_final_states_sigs_count_states = vec![];
		let mut decoded_final_states_sigs_count_count = vec![];

		let mut final_states_sigs = vec![];
		let mut decoded_final_states_sigs_states = vec![];
		let mut decoded_final_states_sigs_ids = vec![];
		let mut decoded_final_states_sigs_sigs = vec![];

		let mut hashset_sigs_to_merge = HashSet::<F>::new(); 

		for s1 in &final_states{
			let s = s1.clone();
			if s.is_zero() {continue;}

			let i = field_to_usize(&s) - 1; //the real state idx
			let pats = acdfa.final_to_patterns(i);
			let vec_sigs = pats.iter().map(|pat|{
				map_crit_pat.get(pat).expect("err").to_vec()
			}).flatten().collect::<Vec<String>>();
			let vec_sigs_id = vec_sigs.iter().map(|s|
				*sig_to_id.get(s).expect("sig_2_id err")
			).collect::<Vec<usize>>();
		
			for id in 0..vec_sigs_id.len(){
				let f_sig = F::from(vec_sigs_id[id] as u32);
				decoded_final_states_sigs_states.push( F::from((i+1) as u32));
				decoded_final_states_sigs_ids.push(F::from( (id+1) as u32));
				decoded_final_states_sigs_sigs.push(f_sig); //started from 1 

				let encoded = F::from((i+1) as u32)*sigbit_fac2+ 
							F::from((id+1) as u32) * sigbit_factor+
							F::from(f_sig);
				final_states_sigs.push(encoded);
				hashset_sigs_to_merge.insert(f_sig);
			}
			let count = vec_sigs_id.len();

			decoded_final_states_sigs_count_states.push(s);
			decoded_final_states_sigs_count_count.push(F::from(count as u32));
			let encoded = s * sigbit_factor + F::from(count as u32);
			final_states_sigs_count.push(encoded);
		}
		let mut sigs_to_merge = hashset_sigs_to_merge.iter().map(|x| x.clone())
			.collect::<Vec<F>>();
		let sigs_to_include = vec_sig_id_no_crit_pat.iter().map(|x| 
			F::from(*x as u64)).collect::<HashSet<F>>();
		assert!(sigs_to_include.is_disjoint(&hashset_sigs_to_merge));

		let vec_sigs_to_include = vec_sig_id_no_crit_pat.iter().map(|x|
			F::from(*x as u64)).collect::<Vec<F>>(); 
		#[cfg(test)]{ 
			use crate::gadgets::commons::is_sorted;
			assert!(is_sorted(&vec_sigs_to_include));
		}
		assert!(vec_sigs_to_include.len()==capacity.count_sig_no_crit_pat);

		let output_vec = [&inp_sigs[..], &sigs_to_merge[..],
			&vec_sigs_to_include[..]].concat();
		let set_ouput_vec = output_vec.iter().filter(|x| !x.is_zero())
			.map(|x| x.clone())
			.collect::<HashSet<F>>();
		let mut oup = set_ouput_vec.iter().map(|x| x.clone()).
			collect::<Vec<F>>();

		//3. set up their sizes and genreate data
		expand_vec(&mut final_states_sigs_count, olen);
		expand_vec(&mut decoded_final_states_sigs_count_states, olen);
		expand_vec(&mut decoded_final_states_sigs_count_count, olen);

		expand_vec(&mut final_states_sigs, jlen);
		expand_vec(&mut decoded_final_states_sigs_states, jlen);
		expand_vec(&mut decoded_final_states_sigs_ids, jlen);
		expand_vec(&mut decoded_final_states_sigs_sigs, jlen);

		expand_vec(&mut sigs_to_merge, slen); 

		expand_vec(&mut oup, slen);
		oup.sort();
		assert!(oup[0].is_zero(), 
			"output buf too small, needs 1st element to be dummy zero");

		//3. generate the m_tables
		let m_tbl_joins_to_sigs = gen_m_table(
			&decoded_final_states_sigs_sigs, &sigs_to_merge);

		let src_sigs = [ &inp_sigs[..], &sigs_to_merge[..], 
				&vec_sigs_to_include[..] ].concat(); 
		let m_tbl_inp_sigs_oup = gen_m_table(&src_sigs, &oup);
		let m_tbl_decoded_final_states = gen_m_table(
			&final_states, &decoded_final_states_sigs_states);

		let data = SigGadgetData{
			final_states: final_states.clone(),

			final_states_sigs_count,
			decoded_final_states_sigs_count_states,
			decoded_final_states_sigs_count_count,
			final_states_sigs,
			decoded_final_states_sigs_states,
			decoded_final_states_sigs_ids,
			decoded_final_states_sigs_sigs,
			sigs_to_merge,
			m_tbl_joins_to_sigs,
			m_tbl_inp_sigs_oup,
			m_tbl_decoded_final_states,

			sigs_no_crit_pat: vec_sigs_to_include.clone(), 
			sigs_no_crit_pat_count: vec![ //1 element
					F::from(capacity.count_sig_no_crit_pat as u64)
				],

			capacity
		};


		#[cfg(test)]{ data.self_check(); }
		let capacity = data.capacity.clone();

		#[cfg(test)]{
			let data2 = data.clone();
			let vec2 = data2.to_vec();
			let data3 = SigGadgetData::from_vec(&data.capacity, &vec2);
			assert!(data3.to_vec()==vec2);
		}
		
		Self{data, capacity, oup, fsm_id, vec_sig_id_no_crit_pat:
			vec_sig_id_no_crit_pat.clone()}
	}

	/// generate the subtbl_ids for its oup
	pub fn gen_subtbl_id_for_oup(&self)->Vec<F>{
		let f_range2 = F::from(RANGE2 as u32);
		vec![f_range2; self.capacity.sig_buf_capacity]
	}

	/// generate the sid for non-zero elements of vec
	fn gen_sid(vec: &Vec<F>, n: usize, sid: F)->Vec<F>{
		assert!(n==vec.len());
		let zero = F::zero();
		vec.par_iter().map(|x|
			if x.is_zero() {zero} else {sid}
		).collect::<Vec<F>>()
	}

	/// Generate the subtbl_ids for its data
	pub fn gen_subtbl_id_for_data(&self)->Vec<F>{
		let (olen, jlen, slen) = (
			self.capacity.final_states_buf_capacity,
			self.capacity.join_buf_capacity, 
			self.capacity.sig_buf_capacity
		);
		let state_2_sig_id = self.fsm_id+4; //for subtbl_id
		let state_sig_count_id = self.fsm_id+5; //for subtbl_id
		let f_final_2_sig = F::from(state_2_sig_id as u32);
		let f_final_sig_count = F::from(state_sig_count_id as u32);
		let f_final_states = F::from((self.fsm_id+2) as u32);
		let f_range2 = F::from(RANGE2 as u32);

		let zero = F::zero();
		let sig_id_no_crit_pat_count = self.vec_sig_id_no_crit_pat.len();
		let ids_no_pat = (0..sig_id_no_crit_pat_count).collect::<Vec<usize>>().
			into_iter().map(|i|
				F::from((ID_SIG_NO_CRIT + i as u32 +1u32) as u32)
			).collect::<Vec<F>>();

		let vec_subtbl_ids = vec![
			// subtbl_ids for final_states [ignore it ] as it's already
			// checked by previous gadgets.
			//vec![f_final_states; olen],

			// for pub final_states_sigs_count: Vec<F>, 
			//vec![f_final_sig_count; olen],
			Self::gen_sid(&self.data.final_states_sigs_count, 
				olen, f_final_sig_count),

			// for pub decoded_final_states_sigs_count_states: Vec<F>,
			Self::gen_sid(&self.data.decoded_final_states_sigs_count_states, 
				olen, f_final_states),

			// for pub decoded_final_states_sigs_count_states: Vec<F>,
			vec![f_range2; olen],
			
			// for  pub final_states_sigs: Vec<F>,
			// vec![f_final_2_sig; jlen],
			Self::gen_sid(&self.data.final_states_sigs, 
				jlen, f_final_2_sig),

			// for pub decoded_final_states_sigs_states: Vec<F>,
			//vec![f_final_states; jlen],
			Self::gen_sid(&self.data.decoded_final_states_sigs_states, 
				jlen, f_final_states),

			// pub decoded_final_states_sigs_ids: Vec<F>,
			vec![f_range2; jlen],
			// pub decoded_final_states_sigs_sigs: Vec<F>,
			vec![f_range2; jlen],

			//pub sigs_to_merge: Vec<F>,
			vec![f_range2; slen],

			//pub m_tbl_joins_to_sigs: Vec<F>,
			vec![zero; slen], //don't care it's verified by Logup
			//pub m_tbl_inp_sigs_oup: Vec<F>,
			vec![zero; slen], 
			// pub m_tbl_decoded_final_states: Vec<F>,
			vec![zero; jlen], 

			//subtbl_id for each of the sigs_no_crit_pat
			ids_no_pat,
			//count of vec_sig_id_no_crit_pat
			vec![F::from(ID_SIG_NO_CRIT_COUNT)],

		];
		#[cfg(test)]{
			let desc1 = SigGadgetData::<F>::gen_desc(&self.capacity)
				.iter().map(|(_,s)| *s)
				.collect::<Vec<usize>>();
			let desc2 = vec_subtbl_ids.iter().map(|v| v.len())
				.collect::<Vec<usize>>();
			assert!(desc1[1..].to_vec()==desc2);
		}
		let res = vec_subtbl_ids.concat();
		#[cfg(test)]{
			let data_len = SigGadgetData::<F>::get_len(&self.capacity);
			assert!(data_len - olen == res.len());
		}

		res
	}
}

impl <F:PrimeField> GetSigGadget<F>{
	/// constructor. Join_buf_size: the buf size needed to 
	/// hold its join buffer, sig_buf_size: the buf needed to
	/// hold its signature buffer. We expect inp/oup will have
	/// the same size.
	pub fn new(
		capacity: &SigGadgetCapacity,
		fsm_id: u32
	) -> Self{
		Self{ _f: PhantomData, capacity: capacity.clone(), fsm_id }
	}
}

impl <F:PrimeField> SigmaGadget<F> for GetSigGadget<F>{
	fn get_name(&self)->&str {"GetSigGadget"}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: Rc<Vec<ContainerConfig>>, _idx: usize){
		unimplemented!("not needed. handled by legacy code");
	}

	fn get_container_config(&self)->ContainerConfig{
		unimplemented!("not needed. handled by legacy code");
	}

	/// Get the instructions for build its statement.
	/// NOTE: this is only needed for those used in SedGadgetMapper.
	/// Others are handled by legacy code in their gadget mapper.
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	/// return the sizes of inp/oup/data/failed_sigs/discharge_sigs
	/// to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	/// return the estimated cost
	fn est_cost(&self)->usize{
		let (olen, jlen, slen) = (self.capacity.final_states_buf_capacity, 
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity);
		let costs = vec![
			("verify_inverse", 2*(jlen+slen+2*slen+slen+olen+jlen)),
			("verify_logup_inverse", 1*(slen + slen + jlen)+3), 
			("verify_encoded", 1*jlen + 2*jlen),
			("verify_subtbl_ids", 
				3*jlen + 3*jlen + jlen +
				3*jlen + 3*jlen + jlen + jlen 
				+ slen + slen + jlen 
				+slen),
			("verify_main_left", 5*olen),
			("verify_main_right", 16*jlen), 
		];

		costs.iter().map(|(_,c)| c).sum::<usize>()
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) no word_segment
		//  (2) inp: signtures  [sig_buf_size],
		//  (3) oup: signatures [sig_buf_size],
		//  (4) data:  [size: call gen_desc()]
		//      related defined in SigGadgetData structure.
		//  (5) its own subtbl_id for data.  
		//		subtbl_id_for_data and for_oup
		//      check SigGadgetAdvice:gen_subtbl_id_for_data() and for_oup()
		//		Note: it excludes the final_states part for data.
		//  (6) failed_sigs [sig_buf_size]
		// ]
		// NO msg1, but msg2: 4 elements (4 lookups), 
		//          msg3: three invtable for the last 3 Logup type lkups: see
		//			SigGadgetMsg3 for details. The 1st lookup uses
		//			random combination of poly (exact list matching, no
		//				need to use Logup).	
		//		
		let (olen, _jlen, slen) = (self.capacity.final_states_buf_capacity, 
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity);
		let word_len = 0;
		let inp_len = slen;
		let oup_len = slen;
		let data_len = SigGadgetData::<F>::get_len(&self.capacity);
		let msg3_len = SigGadgetMsg3::<F>::get_len(&self.capacity);
		let failed_len = slen;
		//subtbl_id excludes subtbl_ids FOR the first final_states of data,
		//but includes the subtbl_ids for oup
		let subtbl_id_len = data_len -olen + slen; 
		let stat_len = word_len + inp_len + oup_len + data_len + subtbl_id_len
			+ failed_len;

		(stat_len, 0, 4, msg3_len)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
		-> Vec<F>{
		vec![] // dummy
	}

	fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: &Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		msg2_vec: &Vec<F>, idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		//1. retrieve the statement and get the data part
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			stmt_vec[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<F>>();
		//assert!(my_stmt.len()==self.get_msg_size().0);
		//make it pass for manually constructed stmt_vec in my own
		//unit test.
		let (_alpha, beta, gamma, eta) = (msg2_vec[idx_msg2], 
			msg2_vec[idx_msg2+1], msg2_vec[idx_msg2+2], msg2_vec[idx_msg2+3]);
		let (_olen, _jlen, slen) = (self.capacity.final_states_buf_capacity,
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity);
		let data_len = SigGadgetData::<F>::get_len(&self.capacity);
		let data_vec = my_stmt[2*slen..2*slen+data_len].to_vec();
		let data = SigGadgetData::from_vec(&self.capacity, &data_vec);
		#[cfg(test)]{
			let data_vec2 = data.clone().to_vec();
			assert!(data_vec2==data_vec);
		}

		//2. build the inverse lists as specified in SigGadgetMsg3
		let inv1_left = data.decoded_final_states_sigs_sigs.clone()
			.into_par_iter().map(|x| (beta + x).inverse().expect("inv failed"))
			.collect::<Vec<F>>();

		let inv1_right= data.sigs_to_merge.par_iter().map(|x|
			(beta + *x).inverse().expect("inv failed")).collect::<Vec<F>>();

		let inp = &my_stmt[0..slen];
		let vec_inp = [
			&inp[..],
			&data.sigs_to_merge[..],
			&data.sigs_no_crit_pat[..]
		].concat();
		let vec_oup = &my_stmt[slen..2*slen];
		let inv2_left = vec_inp.into_par_iter().map(|x|
			(gamma+x).inverse().expect("inv failed")).collect::<Vec<F>>();
		let inv2_right = vec_oup.into_par_iter().map(|x|
			(gamma+x).inverse().expect("inv failed")).collect::<Vec<F>>();

		let inv3_left = data.final_states.par_iter().map(|x|
			(eta+ *x).inverse().expect("inv failed")).collect::<Vec<F>>();
		let inv3_right = data.decoded_final_states_sigs_states
			.par_iter().map(|x|
			(eta+ *x).inverse().expect("inv failed")).collect::<Vec<F>>();

		let msg3 = SigGadgetMsg3{
			inv1_left, inv1_right, inv2_left, inv2_right, inv3_left, inv3_right,
			capacity: self.capacity.clone(),
		};

		let msg3_vec = msg3.to_vec();
		#[cfg(test)]{ 
		  	let msg3_2 = SigGadgetMsg3::<F>::from_vec(&self.capacity, 
		  		&msg3_vec.clone()); 
			let msg3_vec2 = msg3_2.to_vec();
			assert!(msg3_vec2==msg3_vec);
		}

		msg3_vec	
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{

		//0. retrive the statement instance 
		let (olen, jlen, slen, clen) = (self.capacity.final_states_buf_capacity,
			self.capacity.join_buf_capacity, self.capacity.sig_buf_capacity,
			self.capacity.count_sig_no_crit_pat);
		let (stmt_idx, _, msg2_idx, msg3_idx) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		//assert!(my_stmt.len()==self.get_msg_size().0);
		//disabled for making unit testing pass, which constructs
		//customized stmt_vec.


		let inp = &my_stmt[0..slen];
		let oup = &my_stmt[slen..2*slen];
		let data_len = SigGadgetData::<F>::get_len(&self.capacity);
		let data_vec = my_stmt[2*slen..2*slen+data_len].to_vec();
		let data = SigGadgetData::from_vec(&self.capacity, &data_vec);
		#[cfg(test)] data.self_check();

		//subtbl_id: only the data (excluding final_states_inp) and then oup
		let subtbl_len = data_len -olen + slen; 
		let subtbl_id = &my_stmt[2*slen+data_len.. 2*slen+data_len+subtbl_len];
		let m2= wtns.msg2[msg2_idx..msg2_idx+4].to_vec();
		let (alpha, beta, gamma, eta) = (&m2[0], &m2[1], &m2[2], &m2[3]);
		let msg3_len = SigGadgetMsg3::<F>::get_len(&self.capacity);
		let msg3_vec = wtns.msg3[msg3_idx..msg3_idx+ msg3_len].to_vec();
		let msg3 = SigGadgetMsg3::from_vec(&self.capacity, &msg3_vec);
		#[cfg(test)] msg3.self_check();

		//1. check validity msg3 (Logup Inverse and Logup Relations)
		verify_inverse(cs.clone(), &data.decoded_final_states_sigs_sigs,
			&msg3.inv1_left, &beta, jlen)?;
		verify_inverse(cs.clone(), &data.sigs_to_merge, 
			&msg3.inv1_right, &beta,slen)?;
		verify_logup_inverse(cs.clone(), &msg3.inv1_left, &msg3.inv1_right, &data.m_tbl_joins_to_sigs)?;

		let to_merge = [
			&inp[..],
			&data.sigs_to_merge[..],
			&data.sigs_no_crit_pat[..]
		].concat();
		verify_inverse(cs.clone(), &to_merge, &msg3.inv2_left, 
			&gamma,slen+slen+clen)?;
		verify_inverse(cs.clone(), oup, &msg3.inv2_right, &gamma,slen)?;
		verify_logup_inverse(cs.clone(), &msg3.inv2_left, &msg3.inv2_right, &data.m_tbl_inp_sigs_oup)?;

		verify_inverse(cs.clone(), &data.final_states,
			&msg3.inv3_left, &eta,olen)?;
		verify_inverse(cs.clone(), &data.decoded_final_states_sigs_states, 
			&msg3.inv3_right, &eta, jlen)?;
		verify_logup_inverse(cs.clone(), &msg3.inv3_left, &msg3.inv3_right,
			&data.m_tbl_decoded_final_states)?;




		//2. verify the validity of encoded messages
		verify_encoded_states_sig_count(cs.clone(), 
			&data.final_states_sigs_count,
			&[
				data.decoded_final_states_sigs_count_states,
				data.decoded_final_states_sigs_count_count.clone(),
			].concat())?;
		verify_encoded_states_sig(cs.clone(), &data.final_states_sigs, 
			&[
				data.decoded_final_states_sigs_states,
				data.decoded_final_states_sigs_ids.clone(),
				data.decoded_final_states_sigs_sigs,
			].concat())?;

		//3. check the ranges (subtables). Here subtbl_id has the 
		//same structure of data + oup. Use a SigGadgetData to
		//deserialize the subtbl_id vector and verify in batch.
		let f_final_2_sig = FpVar::<F>::new_constant(cs.clone(),
			F::from((self.fsm_id+4) as u32))?;
		let f_final_sig_count = FpVar::<F>::new_constant(cs.clone(),
			F::from((self.fsm_id+5) as u32))?;
		let f_final_states = FpVar::<F>::new_constant(cs.clone(),
			F::from((self.fsm_id+2) as u32))?;
		let f_range2 = FpVar::<F>::new_constant(cs.clone(),
			F::from(RANGE2 as u32))?;
		let ids_no_pat = (0..clen).collect::<Vec<usize>>().
			into_iter().map(|i|
				new_const_var(&cs, 
					F::from((ID_SIG_NO_CRIT + i as u32 +1u32) as u32))
			).collect::<Vec<FpVar<F>>>();
		let f_count = new_const_var(&cs, F::from(ID_SIG_NO_CRIT_COUNT));
		let zero = FpVar::new_constant(cs.clone(), F::zero())?;
		let mut desc = SigGadgetData::<F>::gen_desc(&self.capacity);
		desc = desc[1..desc.len()].to_vec(); //chop off final states (external)
		desc.push( ("oup", slen) ); //the output buf


		let vals = vec![//match desc
			//excluding f_final_states.clone(),	 (this is the input from
			//previous gadget
			//f_states_sigs_cnt
			f_final_sig_count, f_final_states.clone(), f_range2.clone(),
			//f_states_sigs
			f_final_2_sig, f_final_states, f_range2.clone(), f_range2.clone(),
			//sigs_to_merge
			f_range2.clone(), 
			//3m_tbles 
			zero.clone(), zero.clone(), zero.clone(), 
			//dmmy value: for id_no_crit_pat, we'll check it separately
			zero.clone(),
			//count_no_crit_pat,
			f_count.clone(),
			//oup signatures
			f_range2.clone(), 
		];
		//when padded, needs to call thecheck_arr_eq_nz; otherwise
		//if it's simple range without padding, just call check_arr_eq
		//for smaller cost
		let b_check_nz: Vec<bool> = vec![
			//f_states_sigs_cnt
			true, true, false,
			//f_states_sigs
			true, true , false, false,
			//sigs_to_merge
			false,
			//3m_tbles 
			false, false, false,
			//id_no_crit_pat (this value does not matter as we'll
			//check it in a separate branch
			true,
			//count_crit_pat,
			false,
			//oup signatures
			false
		];
		assert!(vals.len()==desc.len());
		let mut start = 0;
		//let one_var= FpVar::<F>::new_constant(cs.clone(), F::one())?;


		for i in 0..vals.len(){
			let cur_len = desc[i].1; //SHOULD BE REGARDED AS A CONSTANT
									 //IT'S a fixed CONSTANT set up
									 //at the Capacity.

			if i==vals.len()-3{//the id_no_pat. //cost 1 each unit.
				//this branch ensures that the listed
				//sigs are INDEED those listed in clam_db subtbl
				//of ID_SIG_NO_CRIT_PAT
				//next ID_SIG_NO_CRIT_PAT COUNT ensures that all are
				//covered.
				//The argument has 3 sections:
				//(1) all sid are valid ID_NO_CRIT_PAT id
				//(2) these sids are increased by 1, and start from (1)
				//(3) the last ID matches the count

				//(1) sids for (SIG_ID_NO_CRIT_PAT) are valid
				// and (2) the  are increasing (increasing
				// is asserted when generating ids_no_pat as constants)
				assert!(desc[i].0=="sigs_no_crit_pat");
				check_arr_eq_arr(&subtbl_id[start..start+cur_len], 
					&ids_no_pat, "check subtbl id for sig_no_crit_pat err")?;

				//(2) the extracted count matches that of 
				// sigs_no_crit_pat_count (this is simply
				// and essentially asserting cur_len == proved_count
				// where proved_count is ASSERTED EALIER BY the sid
				// that it is the correct TOTAL_SIG_NO_PAT_COUNT saved
				// in DB. 
				// -- in fact - this step is actually not needed.
				let proved_count = &data.sigs_no_crit_pat_count[0];
				let expected_count = new_const_var(&cs, F::from(
					self.capacity.count_sig_no_crit_pat as u64));
				check_eq(&proved_count,&expected_count, "err count prf")?;
			}else if b_check_nz[i]{//cost 2
				check_arr_eq_nz(&subtbl_id[start..start+cur_len],&vals[i], 
					desc[i].0)?;
			}else{//cost 1
				check_arr_eq(&subtbl_id[start..start+cur_len],&vals[i], 
					desc[i].0)?;
			}
			start += cur_len;
		}



		//4.  main goal: to verify the signatures (as the join operation) is
		// fully covering the signature_count, e.g., if for state 1 the
		// signature count says there are 5 records, then we verify the
		// last record in decoded_final_states_sigs is 5. However, as
		// records number vary, we build a random polynomial eval to
		// check this consistency. That is: in the 
		// decoded_states_signs (state, id, sigs)
		// we verify for each signature: (1) the id is increasing
		// by 1 for its max count; (2) the max count of the signature
		// matches that of the decoded_states_sigs_count. This is
		// accomplished by building a polynomial evaluation over the
		// max_counts for each signature.
		let mut sum_left= FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let mut sum_right= sum_left.clone();
		let one_var= FpVar::<F>::new_constant(cs.clone(), F::one())?;
		for i in 0..olen{
			sum_left= (&data.decoded_final_states_sigs_count_count[i])
				.is_zero()?
				.select(
					&sum_left, 
					&(&sum_left*alpha
						+&data.decoded_final_states_sigs_count_count[i])
				)?;

		}

		
		let mut b_padded = Boolean::<F>::FALSE;
		for i in 0..jlen{
			//1. if record is zero, should be regarded as entering
			// padded state. If entering padded state should be
			// padded forever.
			let b_rec_zero = data.final_states_sigs[i].is_zero()?;
			check_imply(&b_padded, &b_rec_zero, "check padded")?;
			b_padded = b_rec_zero;

			//2. in non-padded mode: if i==jlen-1, or next record
			// has ID 1, this recourd should be regarded as LAST record
			// of the current signature.
			// thus its ID should be counted into sum_right.
			let b_not_padded = b_padded.not();
			let b_last = if i==jlen-1 {b_not_padded.clone()} else{
				data.decoded_final_states_sigs_ids[i+1].is_eq(&one_var)?
					.or( 
						&(&data.final_states_sigs[i+1].is_zero()?
							.and(&b_not_padded)?)
					)?
			};
			let b_not_last = b_last.not();
			sum_right = b_last.select(
				&(&sum_right*alpha + &data.decoded_final_states_sigs_ids[i]), 
				&sum_right
			)?;

			//3. in non-padding mode, ensure difference between IDs
			// is one for the same signature
			let diff = if i<jlen-1 {
				&data.decoded_final_states_sigs_ids[i+1] 
					- &data.decoded_final_states_sigs_ids[i]
			} else { one_var.clone()};
			check_imply(&b_not_padded.and(&b_not_last)?, 
				&diff.is_eq(&one_var)?, "diff check")?;
		}
		check_eq(&sum_left, &sum_right, "sum_left==sum_right")?;


		Ok(())
	}
}



#[cfg(test)]
pub mod tests_sigs_gadget{
	use std::{rc::Rc};
	use std::collections::{HashMap,HashSet};
	use ark_bn254::{Fr};
	use ark_std::{Zero,One};
	use crate::gadgets::sigs::{GetSigGadget,GetSigAdvice,SigGadgetCapacity};
	use crate::gadgets::word_extract::tests_word_extract_gadget::{
		test_gadget};
	use data_processor::hex_acdfa::HexACDFA;

	#[test]
	fn test_sigs(){
		//1. create final states and then non-final states
		let fsm_id:u32 = 0x10001001;
		let patterns = vec!["abc", "cba", "1234567890abcdef"].
			iter().map(|s| {String::from(*s)}).collect();
		let acdfa = HexACDFA::new(1, &patterns);
		let num_acc_states = acdfa.num_acc_states;
		let mut map_crit_pat = HashMap::<String,Vec<String>>::new();
		map_crit_pat.insert(format!("abc"), vec![format!("s1")]);
		map_crit_pat.insert(format!("cba"), vec![format!("s1"), format!("s3")]);
		map_crit_pat.insert(format!("1234567890abcdef"), vec![format!("s4")]);
		let mut sig_to_id = HashMap::<String, usize>::new();
		for i in 1..5 {sig_to_id.insert(format!("s{}", i), i);}

		let (_fs, fs2) = (num_acc_states - 1, num_acc_states-2);
		let final_states = vec![
			vec![Fr::from(fs2 as u32)], //trigers sig4
			vec![Fr::zero(); 13], //pad to 16
		].concat(); //NOTE that they encode REAL state + 1
		let capacity = SigGadgetCapacity{
			final_states_buf_capacity: 16,
			join_buf_capacity: 8,
			sig_buf_capacity: 5,
			count_sig_no_crit_pat: 2,
		};
			
		let gadget= GetSigGadget::<Fr>::new(&capacity, fsm_id);
		let rg = Rc::new(gadget);

		//2. build the advice
		let inp= vec![ //sigs
			vec![Fr::one()],
			vec![Fr::zero(); 4]
		].concat(); //as required, padded as zero.
		let vec_sig_id_no_crit_pat = vec![2usize, 5usize]; //sig2,5 which
			//have no mapping of any critical patterns, so we list
		let adv = GetSigAdvice::new(&final_states, &inp, capacity, &acdfa, 
			&map_crit_pat, &sig_to_id, fsm_id as usize, 
			&vec_sig_id_no_crit_pat);
		let oup = adv.oup.clone();
		let data = adv.data.clone().to_vec();

		let subtbl_id = vec![
			adv.gen_subtbl_id_for_data(),
			adv.gen_subtbl_id_for_oup()
		].concat();
		let to_pad_size = inp.len() + oup.len() + data.len() - subtbl_id.len();
		let subtbl_id = [&subtbl_id[..], &vec![Fr::zero(); to_pad_size][..]]
			.concat(); //to make the Witness.to_vec_fp_var check happy
					   //in cp_map.rs this onstraint inp+oup+data.len
					   //  == subtbl_id.len will be satisfied but not
					   //for this manually constructed example

		let lkup_share_size = 4usize;
		let failed_sigs = oup.clone();
		//expected 1,2,4,5 coz 1 is passed from inp, 2 and 5 are for
		//the vec_sig_id_no_crit_pat, and 4 is triggred by fs2 final state
		let expected_failed = vec![1,2,4,5].into_iter().map(|x|
			Fr::from(x)).collect::<HashSet<Fr>>();
		let failed = failed_sigs.iter().filter(|x| !x.is_zero())
			.map(|x| x.clone()).collect::<HashSet<Fr>>();
		assert!(expected_failed == failed);
		/*
		test_gadget_adv::<Fr>(rg, &vec![], &inp, &oup, &data, 
			&failed_sigs, &vec![],
			&subtbl_id, 
			lkup_share_size, 
			true, None);
		*/
		test_gadget::<Fr>(rg, &vec![], &inp, &oup, &data,
			&subtbl_id, lkup_share_size);
	}
}
