/* Created 02/16/2025
*/

use std::rc::{Rc};
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig,NdAdvice},
	container_config::{ContainerConfig},
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{FieldVar,fp::FpVar},
	alloc::AllocVar,
	eq::EqGadget,
};
use std::any::Any;
use data_processor::{clam_db::CHAR};


/// This gadget is used for testing purpose. It performs
/// sum of each element of a word segment, which is provided
/// with a verified subtable_id 1. (If an element is indeed in table 1
/// but the non-deterministic advice did not show it, it is not summmed).
#[derive(Clone,Debug)]
pub struct SumWordGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	max_word_len: usize,
}

impl <F:PrimeField> SumWordGadget<F>{
	pub fn new(max_word_len: usize) -> Self{
		Self{_f: PhantomData, max_word_len: max_word_len}
	}
}

impl <F:PrimeField> SigmaGadget<F> for SumWordGadget<F>{
	fn get_name(&self)->&str {"SumWordGadget"}

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

	/// return the sizes of inp/oup/data to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		unimplemented!("no need to implement. legacy of caller handles it");
	}

	fn est_cost(&self)->usize{
		4* self.max_word_len
	}
	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) entire_word_seg:  mapped from upper level gadget manager
		//  (2) subtable_id of entire_word part -> stored in data (need extra 
		//                                        constraints by mapper)
		//  (3) act_seg_len:  non-determinitic advice (check by mapper) -> mapped to data
		//  (4) input_sum: mapped from input  -> inp_buf
		//  (5) output_sum: mapped to output -> inp_buf
		//  (6) its own subtable_id for all: mapped from subtabl_id
		// ]
		let p1_len = self.max_word_len;
		let p2_len = self.max_word_len;
		let p3_len = 1;
		let p4_len = 1;
		let p5_len = 1;
		let stat_len = (p1_len + p2_len + p3_len + p4_len + p5_len) +
			(p2_len + p3_len + p4_len + p5_len);
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
		vec![]
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		//1. retrive the statement instance and get all parts
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		assert!(my_stmt.len()==self.get_msg_size().0);
		let wlen = self.max_word_len;
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		let word_seg = my_stmt[0..wlen].to_vec(); //from word
		let inp_sum = my_stmt[wlen+1].clone(); //from inp
		let oup_sum = my_stmt[wlen+2].clone(); //from oup
		let subtbl_id = my_stmt[wlen+2..wlen+2+wlen].to_vec(); //from data
		let act_seg_len = my_stmt[2*wlen+3].clone(); //from data
		let mut acc_sum = inp_sum.clone();
		let mut remain =  act_seg_len.clone();

		let zero = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let one= FpVar::<F>::new_constant(cs.clone(), F::one())?;
		for _i in 0..wlen{
			let b_add = subtbl_id[i].is_zero()?;
			let to_add =b_add.select(&zero, &word_seg[i])?;
			let to_add2 = remain.is_zero()?.select(&zero, &to_add)?;
			acc_sum = &acc_sum + &to_add2;
			remain = &remain - &one;
		}
		acc_sum.enforce_equal(&oup_sum)?;
		#[cfg(test)]{
			use ark_r1cs_std::{R1CSVar}; 
			if acc_sum.value().is_ok(){
				assert!(acc_sum.value()?==oup_sum.value()?);
			}
		}

		Ok(())
	}
}

/// Advice for SumGadget.
/// Subtable ID: 1.
/// For whoever the value is "3", set subtable ID to CHAR, otherwise "0"
#[derive(Debug)]
pub struct SumWordAdvice<F: PrimeField>{
	pub subtbl_id: Vec<F>,
	pub sum: F,
}

impl <F: PrimeField> NdAdvice for SumWordAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> SumWordAdvice<F>{
	/// word_seg is reaching max capacity with padded elements.
	/// actual size is the actual one to process
	pub fn new(word_seg: &Vec<F>, actual_size: usize)->Self{
		let three = F::from(3u32);
		let word = word_seg[0..actual_size].to_vec();
		let (char_id, zero) = (F::from(CHAR), F::from(0u32));
		let mut subtbl_id = word.iter().map(|x|{
			if *x==three { char_id } else {zero} 
		}).collect::<Vec<F>>();
		let mut remain = vec![zero; word_seg.len()-word.len()];
		subtbl_id.append(&mut remain);

		let res = word.iter().map(|x| 
			if *x==three { *x} else {zero}
		).sum();
		Self{subtbl_id, sum: res}
	}
}

