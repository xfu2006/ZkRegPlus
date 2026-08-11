use std::sync::{Arc};
/* Created 03/26/2025, 
   Completed: 04/02/2025 
	Revised 4: 01/09/2026 (improve exception handling for capacity)
*/

// This is a better refactored version of word_extractor.rs
// It extract a word (packed with 62 nibbles) into nibbles.
// NOTE that it has two modes: char mode (for regular DFA),
// and normal mode (for ACDFA).

use utils::consts::B_DEBUG;
use folding_schemes::folding::foldpot::container_config::ColEle;
use ark_r1cs_std::R1CSVar;
use rayon::{ iter::{ParallelIterator,IntoParallelIterator,IntoParallelRefIterator} };
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::{
	Error,
	folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity},
	container_config::{ContainerConfig},
	circuits_super::{field_to_usize},
	}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{
		//FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
};
use data_processor::{clam_db::{CHAR,CHAR_MAP}};
use std::any::Any;
use utils::{data::{packed_to_nibbles,u8_to_hex}};
use crate::gadgets::{
	traits::{ComponentAdvice,Col, IDX_WORD, IDX_DATA,IDX_INP, IDX_OUP, IDX_SI_DATA, Container},
	word_extract::{LEGS},
	commons::{check_eq, sum_vec_vars_weighted},
};


// -----------------------------------------------
//		Structs
// -----------------------------------------------
/// Capacity of WordExtractAdv Gadget
#[derive(Clone,Debug)]
pub struct WordExtractAdvCapacity{
	/// the word sugsegment length (full, padded)
	pub max_word_len: usize,
}

/// Advice for the WordExtractAdv Gadget.
#[derive(Clone,Debug)]
pub struct WordExtractAdvAdvice<F:PrimeField + ColEle>{
	/// the container object which is serialized to vector of stmt.
	pub stmt_container: std::sync::Arc<std::sync::Mutex<Container<F>>>,
}

/// This gadget is responsible for extract a word (248-bit)
/// into 62 field elements. The basic idea is to simply
/// break it using power operations and then assert the range of each
#[derive(Clone,Debug)]
pub struct WordExtractAdvGadget<F:PrimeField + ColEle>{ 
	/// b_map_char mode: for sid of nibbles, should
	/// their sid be char_val(v) + CHAR_MAP
	pub b_map_char: bool,

	pub capacity: WordExtractAdvCapacity,

	// will be set when set_container_cfg is called
	pub cfgs_context: Option<std::sync::Arc<Vec<ContainerConfig>>>,
	// dummy_cfg is used when cfgs_context is not ready yet
	pub dummy_cfg: ContainerConfig,
	pub my_idx_in_context: Option<usize>,
	_f: PhantomData<F>,

	pub job_id: usize,
}


// -----------------------------------------------
//		Implementations	
// -----------------------------------------------
impl Capacity for WordExtractAdvCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>) -> bool{
		let other = r_other.as_any().downcast_ref::<WordExtractAdvCapacity>()
			.expect("downcast err"); 

		self.max_word_len>= other.max_word_len

	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(WordExtractAdvCapacity{
			max_word_len: self.max_word_len,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField + ColEle> NdAdvice for WordExtractAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField + ColEle> WordExtractAdvAdvice<F>{
	/// word_seg is the one with max compacity, actual size
	/// is the actual word len. We convert all remaining 
	/// as 0.
	///
	/// b_map_char: whether sid_char shouldbe the char translation
	/// this is useful for DFA (not ACDFA) which takes char (such as
	/// '0' instead of 0) as input.
	/// In this mode: we have to create an EXTRA COPY of nibbles
	/// we first: (1) prove nibbles == nibbles_copy
	/// (2) mark sid_nibbles_copy as CHAR (thus restructing them to be valid chars)
	/// (3) mark the translation of each nibble element to their char
	///    correspondingly
	/// This approach prevents attacker to pick a tuple in other sub-table
	/// that goes out of the range of char.
	pub fn new(word_seg: &Vec<F>, actual_size: usize, b_map_char:bool)->
		Result<Self,Error>{
		//1. normalize the input
		let stmt_container = Container::new("word_extract_stmt");
		let mut word = word_seg.clone();
		for i in actual_size..word_seg.len(){ word[i] = F::zero(); }
		let f_act_size = F::from(actual_size as u32);
		let col_word = Col::<F>::new(word.clone(), "word", IDX_WORD);
		let col_act_size= Col::<F>::new(vec![f_act_size], "act_size", 
			IDX_DATA);
		let col_si_act_size = Col::<F>::new_const(
			vec![F::zero()], "si_act_size",
			IDX_SI_DATA
		); //as it's zero no need to check actually
		stmt_container.lock().unwrap().add_col(col_word);
		stmt_container.lock().unwrap().add_col(col_act_size);
		stmt_container.lock().unwrap().add_col(col_si_act_size);

		//2. do the conversion
		let nibbles = packed_to_nibbles(&word);
		assert!(nibbles.len() == LEGS * word.len());
		if B_DEBUG {
			use utils::data::{pack_nibbles};
			let packed = pack_nibbles(&nibbles);
			assert!(packed.len() == word.len());
			for i in 0..word.len(){
				assert!(word[i]==packed[i]);
			}
		}

		//3. construct the problem statement container for serialization
		let nlen = nibbles.len();
		let col_si_nibbles= if !b_map_char{//default mode
			Col::<F>::new_const(
				vec![F::from(CHAR); nlen], 
				"si_nibbles", IDX_SI_DATA
			)
		}else{//for DFA (instead of ACDFA
			let s_nibbles = nibbles.par_iter().map(|n| field_to_usize(n) as u8)
				.collect::<Vec<u8>>();
			let s2 = u8_to_hex(&s_nibbles).as_bytes().to_vec().par_iter()
				.map(|s| *s as char).collect::<Vec<char>>();
			let f_char_map = F::from(CHAR_MAP);
			let vec = s2.into_par_iter().map(|ch|{
				f_char_map + F::from(ch as u8)
			}).collect::<Vec<F>>();
			//NOTE: it's NOT constant mode
			Col::<F>::new(vec, "si_nibbles", IDX_SI_DATA) 
		};
		//conditional add two extra columns only when in b_map_char
		if b_map_char{
			stmt_container.lock().unwrap().add_col(
				Col::<F>::new(nibbles.clone(), "nibbles_copy", IDX_DATA)
			);
			stmt_container.lock().unwrap().add_col(
				Col::<F>::new_const(
					vec![F::from(CHAR);nlen],"si_nibbles_copy",
					IDX_SI_DATA)
				);
		}

		let col_nibbles= Col::<F>::new(nibbles, "nibbles", IDX_DATA);

		//the following are regular columns	
		stmt_container.lock().unwrap().add_col(col_nibbles);
		stmt_container.lock().unwrap().add_col(col_si_nibbles);

		//will always be successful no resource issue
		Ok(Self{stmt_container})
	}
}

impl <F: PrimeField + ColEle> ComponentAdvice<F> for WordExtractAdvAdvice<F>{
	fn get_container(&self)->std::sync::Arc<std::sync::Mutex<Container<F>>>{
		self.stmt_container.clone()
	}
}


impl <F:PrimeField + ColEle> WordExtractAdvGadget<F>{
	/// constructor
	///
	/// b_map_char indicates when generating sid for char, we
	/// generate its mapping to char (actual value is
	/// its char value + CHAR_MAP). E.g., given 1 as the input
	/// its sid is ('1' + CHAR_MAP)
	pub fn new(max_word_len: usize, b_map_char:bool) -> Self{
		let capacity = WordExtractAdvCapacity{max_word_len};
		let dummy_wd = vec![F::zero(); max_word_len];
		let dummy_adv = WordExtractAdvAdvice::new(&dummy_wd, max_word_len,
			b_map_char).unwrap();
		let mut vec_cfg = vec![dummy_adv.stmt_container.lock().unwrap().get_cfg()];
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[vec_cfg.len()-1].clone();

		Self{_f: PhantomData, capacity: capacity, cfgs_context: None,
			my_idx_in_context: None, dummy_cfg, b_map_char, job_id: 0}
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
}

impl <F:PrimeField + ColEle> SigmaGadget<F> for WordExtractAdvGadget<F>{
	fn get_name(&self)->&str {
		if self.b_map_char{
			"WordExtractAdvGadget(b_map_mode)"
		}else{
			"WordExtractAdvGadget"
		}
	}

	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
	}
	fn get_job_id(&self)->usize{
		self.job_id
	}

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
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		//1. retrieve my cfg
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let res = cfg.gen_stmt_map_instructions();

		res
	}

	/// return the sizes of inp/oup/data/failed_sigs/discharged_sigs/
	///to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		for i in 0..3 {assert!(to_add[i+1] == to_add[4+i]);}
		assert!(to_add[IDX_INP]==to_add[IDX_OUP]);

		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA], 0, 0)
	}

	/// estimated cost
	fn est_cost(&self)->usize{
		// obtain the value by actually measure the size of R1CS
		// in assert_msg3
		// this is about 1x nlen
		let est = if self.b_map_char {
			self.capacity.max_word_len*6
		}else{//6*wlen + nlen = (62+6)*wlen
			self.capacity.max_word_len * 68
		};
		est
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		let stat_len = (IDX_WORD..IDX_SI_DATA+1).collect::<Vec<usize>>()
			.iter().map(|i| to_add[*i]).sum();
		(stat_len, 0, 0, 0)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
		-> Vec<F>{
		vec![] // dummy
	}

	fn gen_msg3(&self, _stmt_vec: &Vec<F>, _stmt_idx: 
		&Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		vec![] //no msg3
	}

	/// COST: default mode: 6*wlen (very small)
	///       b_map mode: 6*wlen + nlen
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>,
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig, 
		_word_id: FpVar<F>, _subseg_id: FpVar<F>,
		_virt_vals: &mut Vec<FpVar<F>>)
		-> Result<(),SynthesisError>{
		let b_perf = false;
		let (nc, nv) = (cs.num_constraints(), cs.num_witness_variables());

		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;

		//2. get the parts of the statement
		//COST: 0
		let col_word = stmt.get_col("word")?;
		let word_seg= &col_word.lock().unwrap().data;
		assert!(word_seg.len()==self.capacity.max_word_len);
		let col_nibble = stmt.get_col("nibbles")?;
		let nibbles = &col_nibble.lock().unwrap().data;
		let act_seg_len= stmt.get_col("act_size")?.lock().unwrap().data[0].clone();
		//let col_si_nibbles = stmt.get_col("si_nibbles")?;
		//let si_nibbles= &col_si_nibbles.lock().unwrap().data;
		//actually no need to check si_act_size (it's tagged with 0 don't care)
		let _si_act_size= stmt.get_col("si_act_size")?.lock().unwrap()
			.data[0].clone(); 
		let mut remain =  act_seg_len.clone();
		let nlen = nibbles.len();

		//3. build the power of 4's
		// COST: 0, because they are all const.
		let zero_var = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?;
		//let f4 = FpVar::<F>::new_constant(cs.clone(), F::from(16u32))?;
		//let f1 = FpVar::<F>::new_constant(cs.clone(), F::from(1u32))?;
		let f4 = F::from(16u32);
		let f1 = F::one();
		let mut vec_pows = vec![f1; LEGS];
		for i in 1..LEGS{ vec_pows[i]	 = vec_pows[i-1] * f4; }

		//4. check extraction correct
		//COST: 6*wlen (because add does not cost anything)
		//note the vec_pows are const
		let wlen = self.capacity.max_word_len;
		let remain_val = remain.value()?;
		let vec_inv= (0..wlen).into_par_iter().map(|i|{
			let res = remain_val - F::from(i as u32);
			if res.is_zero() {F::zero()} else {res.inverse().unwrap()}
		}).collect::<Vec<F>>();
		for i in 0..wlen{
			let b_remain_zero = remain.is_zero_adv(&vec_inv[i])?;
			let wd = b_remain_zero.select(&zero_var, &word_seg[i])?;
			// LOGICAL
			//let mut wsum = zero_var.clone();
			//for j in 0..LEGS{
			//	let idx = i*LEGS + j;
			//	wsum += &vec_pows[j] * &nibbles[idx];
			//}
			let wsum = sum_vec_vars_weighted(
				&nibbles[i*LEGS..(i+1)*LEGS], &vec_pows);
			wsum.enforce_equal(&wd)?;
			if B_DEBUG {
				if wsum.value().is_ok(){
					assert!(wsum.value()?==wd.value()?);
				}
			}
			remain = b_remain_zero.select(&zero_var, &(&remain - &one_var))?;
		}

		//5. check the sub-tbl_ids
		//let char_tbl = FpVar::<F>::new_constant(cs.clone(), F::from(CHAR))?;
		//COST: default mode: 0, b_map mode: nlen
		if !self.b_map_char{
			// this is A constant table, no need to check
			//check_arr_eq(&si_nibbles,&char_tbl,"failing check of si_nibbles")?;
		}else{
			//let si_nibbles_copy = stmt.get_container("si_nibbles_copy")
			//	.unwrap().lock().unwrap().to_vec();
			let nibbles_copy = stmt.get_container("nibbles_copy").unwrap().
				lock().unwrap().to_vec();
			// this is a CONSTANT table, no need to check
			//check_arr_eq(&si_nibbles_copy, &char_tbl, "failing si_ni copy")?;
			for i in 0..nibbles.len(){
				check_eq(&nibbles_copy[i], &nibbles[i], 
					"failing eq extra")?;
			}
		}
		if b_perf{
			println!(" ### word_extract_adv(b_map: {}): wlen: {}, nlen: {}, nc: {}, nv: {}", self.b_map_char, wlen,
			nlen, cs.num_constraints() - nc,cs.num_witness_variables()-nv);
		}

		Ok(())
	}
}


#[cfg(test)]
pub mod tests_word_extract_adv_gadget{
	//use ark_crypto_primitives::sponge::Absorb;
	//use ark_relations::r1cs::ConstraintSystem;
	use std::{sync::Arc};
	use ark_bn254::{Fr};
	use folding_schemes::{
		folding::foldpot::sigma_ir1cs::{
			SigmaGadget, 
	//WitnessSigmaIR1CS,
	//		WitnessSigmaIR1CSConfig, WitnessSigmaIR1CSVar,
	//		ZiPartTwoInst,
		},
		folding::foldpot::container_config::ContainerConfig,
	};
	use crate::gadgets::word_extract_adv::{WordExtractAdvGadget,WordExtractAdvAdvice};
	use utils::data::{rand_fe_by_bits};
	use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget_adv;



	#[test]
	fn test_word_extract_adv(){
		//1. create adivce and input container
		let b_map_char = true;
		let mut rng = ark_std::test_rng();
		// Pad-invariant rework (Step 5): act_size MUST equal wlen.
		let wlen = 8usize;
		let act_size = wlen;
		let word = vec![rand_fe_by_bits(248, &mut rng); wlen];
		let adv = WordExtractAdvAdvice::new(&word, act_size, b_map_char)
			.expect("word_extract_adv advice err");
		let stmt_cont = adv.stmt_container; 

		//2. create gadget
		let cfg = stmt_cont.lock().unwrap().get_cfg();
		let mut vec_cfg =vec![cfg];
		ContainerConfig::adjust_locations(&mut vec_cfg); //resolve
		let cps = stmt_cont.lock().unwrap().gen_stmt_components().0; //from inp to si_data
		let lkup_share_size = 4usize;
		let mut weg = WordExtractAdvGadget::<Fr>::new(wlen, b_map_char);
		weg.set_container_cfg(vec_cfg.clone().into(), 0); 
		let rg = Arc::new(weg);

		//3. test it
		test_gadget_adv::<Fr>(rg, &word, &cps[0], &cps[1], &cps[2],
			&cps[6], &cps[7], //failed and discharged_sigs
			&vec![//subtbl_id (concats of si_inp, si_oup, si_data)
				cps[3].clone(), 
				cps[4].clone(), 
				cps[5].clone()
			].concat(), lkup_share_size,
			false, //not legacy mode
			Some(vec_cfg),
		);
	}
}
