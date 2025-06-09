/* Created 03/26/2025, 
   Completed: 04/02/2025 
*/

// This is a better refactored version of word_extractor.rs
use std::{rc::{Rc},cell::{RefCell}};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::{
	folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice,Capacity},
	container_config::{ContainerConfig},
	}
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{
		FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
};
use data_processor::{clam_db::CHAR};
use std::any::Any;
use utils::{data::{packed_to_nibbles}};
use crate::gadgets::{
	traits::{ComponentAdvice,Col, IDX_WORD, IDX_DATA,IDX_INP, IDX_OUP, IDX_SI_DATA, Container},
	word_extract::{LEGS},
	commons::{check_arr_eq},
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
#[derive(Clone)]
pub struct WordExtractAdvAdvice<F:PrimeField>{
	/// the container object which is serialized to vector of stmt.
	pub stmt_container: Rc<RefCell<Container<F>>>,
}

/// This gadget is responsible for extract a word (248-bit)
/// into 62 field elements. The basic idea is to simply
/// break it using power operations and then assert the range of each
#[derive(Clone,Debug)]
pub struct WordExtractAdvGadget<F:PrimeField>{ 
	pub capacity: WordExtractAdvCapacity,
	
	// will be set when set_container_cfg is called
	pub cfgs_context: Option<Rc<Vec<ContainerConfig>>>,
	// dummy_cfg is used when cfgs_context is not ready yet
	pub dummy_cfg: ContainerConfig,
	pub my_idx_in_context: Option<usize>,
	_f: PhantomData<F>,
}



// -----------------------------------------------
//		Implementations	
// -----------------------------------------------
impl Capacity for WordExtractAdvCapacity{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>) -> bool{
		let other = r_other.as_any().downcast_ref::<WordExtractAdvCapacity>()
			.expect("downcast err"); 

		self.max_word_len>= other.max_word_len

	}

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity in Rc),
	fn clone(&self) -> Rc<dyn Capacity>{
		Rc::new(WordExtractAdvCapacity{
			max_word_len: self.max_word_len,
		})
	}

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any { self }
}

impl <F: PrimeField> NdAdvice for WordExtractAdvAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> WordExtractAdvAdvice<F>{
	/// word_seg is the one with max compacity, actual size
	/// is the actual word len. We convert all remaining 
	/// as 0.
	pub fn new(word_seg: &Vec<F>, actual_size: usize)->Self{
		//1. normalize the input
		let mut word = word_seg.clone();
		for i in actual_size..word_seg.len(){ word[i] = F::zero(); }

		//2. do the conversion
		let nibbles = packed_to_nibbles(&word);
		assert!(nibbles.len() == LEGS * word.len());
		#[cfg(test)]{ 
			use utils::data::{pack_nibbles};
			let packed = pack_nibbles(&nibbles);
			assert!(packed.len() == word.len());
			for i in 0..word.len(){
				assert!(word[i]==packed[i]);
			}
		}
		let f_act_size = F::from(actual_size as u32);

		//3. construct the problem statement container for serialization
		let nlen = nibbles.len();
		let col_word = Col::<F>::new(word, "word", IDX_WORD);
		let col_nibbles= Col::<F>::new(nibbles, "nibbles", IDX_DATA);
		let col_si_nibbles= Col::<F>::new(
			vec![F::from(CHAR); nlen], "si_nibbles", IDX_SI_DATA);
		let col_act_size= Col::<F>::new(vec![f_act_size], "act_size", 
			IDX_DATA);
		let col_si_act_size = Col::<F>::new(vec![F::zero()], "si_act_size",
			IDX_SI_DATA); //as it's zero no need to check actually

		
		let stmt_container = Container::new("word_extract_stmt");
		stmt_container.borrow_mut().add_col(col_word);
		stmt_container.borrow_mut().add_col(col_act_size);
		stmt_container.borrow_mut().add_col(col_nibbles);
		stmt_container.borrow_mut().add_col(col_si_act_size);
		stmt_container.borrow_mut().add_col(col_si_nibbles);
		Self{stmt_container}
	}
}

impl <F: PrimeField> ComponentAdvice<F> for WordExtractAdvAdvice<F>{
	fn get_container(&self)->Rc<RefCell<Container<F>>>{
		self.stmt_container.clone()
	}
}


impl <F:PrimeField> WordExtractAdvGadget<F>{
	/// constructor
	pub fn new(max_word_len: usize) -> Self{
		let capacity = WordExtractAdvCapacity{max_word_len};
		let dummy_wd = vec![F::zero(); max_word_len];
		let dummy_adv = WordExtractAdvAdvice::new(&dummy_wd, max_word_len);
		let mut vec_cfg = vec![dummy_adv.stmt_container.borrow().get_cfg()];
		ContainerConfig::adjust_locations(&mut vec_cfg);
		//even it's false, it's good enough for generating statement_structure
		let dummy_cfg = vec_cfg[0].clone();

		Self{_f: PhantomData, capacity: capacity, cfgs_context: None,
			my_idx_in_context: None, dummy_cfg}
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

impl <F:PrimeField> SigmaGadget<F> for WordExtractAdvGadget<F>{
	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, cfgs_context: Rc<Vec<ContainerConfig>>, idx: usize){
		self.cfgs_context = Some(cfgs_context);
		self.my_idx_in_context = Some(idx);
	}

	/// Get the instructions for build its statement.
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		//1. retrieve my cfg
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let res = cfg.gen_stmt_map_instructions();

		res
	}

	/// return the sizes of inp/oup/data to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize){
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let to_add = cfg.get_to_add_size();
		for i in 0..3 {assert!(to_add[i+1] == to_add[4+i]);}

		(to_add[IDX_INP], to_add[IDX_OUP], to_add[IDX_DATA])
	}

	/// estimated cost
	fn est_cost(&self)->usize{
		// obtain the value by actually measure the size of R1CS
		// in assert_msg3
		let est = self.capacity.max_word_len * 68;
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

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, wtns_cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(),SynthesisError>{
		//1. retrive the statement instance and get all parts
		let cfg = self.get_container_cfg().expect("container cfg not set!");
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg, wtns, &cfg)?;

		//2. get the parts of the statement
		let col_word = stmt.get_col("word")?;
		let word_seg= &col_word.borrow().data;
		assert!(word_seg.len()==self.capacity.max_word_len);
		let col_nibble = stmt.get_col("nibbles")?;
		let nibbles = &col_nibble.borrow().data;
		let act_seg_len= stmt.get_col("act_size")?.borrow().data[0].clone();
		let col_si_nibbles = stmt.get_col("si_nibbles")?;
		let si_nibbles= &col_si_nibbles.borrow().data;
		//actually no need to check si_act_size (it's tagged with 0 don't care)
		let _si_act_size= stmt.get_col("si_act_size")?.borrow()
			.data[0].clone(); 
		let mut remain =  act_seg_len.clone();

		//3. build the power of 4's
		let zero_var = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?;
		let f4 = FpVar::<F>::new_constant(cs.clone(), F::from(16u32))?;
		let f1 = FpVar::<F>::new_constant(cs.clone(), F::from(1u32))?;
		let mut vec_pows = vec![f1; LEGS];
		for i in 1..LEGS{ vec_pows[i]	 = &vec_pows[i-1] * &f4; }

		//4. check extraction correct
		let wlen = self.capacity.max_word_len;
		for i in 0..wlen{
			let b_remain_zero = remain.is_zero()?;
			let wd = b_remain_zero.select(&zero_var, &word_seg[i])?;
			let mut wsum = zero_var.clone();
			for j in 0..LEGS{
				let idx = i*LEGS + j;
				wsum += &vec_pows[j] * &nibbles[idx];
			}
			wsum.enforce_equal(&wd)?;
			#[cfg(test)]{
				use ark_r1cs_std::R1CSVar;
				if wsum.value().is_ok(){
					assert!(wsum.value()?==wd.value()?);
				}
			}
			remain = b_remain_zero.select(&zero_var, &(&remain - &one_var))?;
		}

		//5. check the sub-tbl_ids
		let char_tbl = FpVar::<F>::new_constant(cs.clone(), F::from(CHAR))?;
		check_arr_eq(&si_nibbles, &char_tbl, "failing check of si_nibbles")?;

		Ok(())
	}
}


#[cfg(test)]
pub mod tests_word_extract_adv_gadget{
	//use ark_crypto_primitives::sponge::Absorb;
	//use ark_relations::r1cs::ConstraintSystem;
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use folding_schemes::{
		folding::foldpot::sigma_ir1cs::{
			SigmaGadget, 
	//WitnessSigmaIR1CS,
	//		WitnessSigmaIR1CSConfig, WitnessSigmaIR1CSVar,
	//		ZiPartTwoInst,
		}
	};
	use crate::gadgets::word_extract_adv::{WordExtractAdvGadget,WordExtractAdvAdvice};
	use utils::data::{rand_fe_by_bits};
	use crate::gadgets::word_extract::tests_word_extract_gadget::test_gadget;



	#[test]
	fn test_word_extract_adv(){
		//1. create adivce and input container
		let mut rng = ark_std::test_rng();
		let (wlen, act_size) = (8usize, 6usize);
		let word = vec![rand_fe_by_bits(248, &mut rng); wlen];
		let adv = WordExtractAdvAdvice::new(&word, act_size);
		let stmt_cont = adv.stmt_container; 

		//2. create gadget
		let cfg = stmt_cont.borrow().get_cfg();
		let vec_cfg = Rc::new(vec![cfg]);
		let cps = stmt_cont.borrow().gen_stmt_components(); //from inp to si_data
		let lkup_share_size = 4usize;
		let mut weg = WordExtractAdvGadget::<Fr>::new(wlen);
		weg.set_container_cfg(vec_cfg, 0); 
		let rg = Rc::new(weg);

		//3. test it
		test_gadget::<Fr>(rg, &word, &cps[0], &cps[1], &cps[2],
			&vec![//subtbl_id (concats of si_inp, si_oup, si_data)
				cps[3].clone(), 
				cps[4].clone(), 
				cps[5].clone()
			].concat(), lkup_share_size);
	}
}
