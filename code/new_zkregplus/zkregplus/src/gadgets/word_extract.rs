/* Created 02/26/2025 */

use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice},
	container_config::{ContainerConfig},
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	fields::{FieldVar,fp::FpVar},
	alloc::AllocVar,
	eq::EqGadget,
};
use data_processor::{clam_db::CHAR};
use std::any::Any;
use utils::{data::{packed_to_nibbles}};
use std::rc::{Rc};

pub const LEGS:usize = 62;
/// This gadget is responsible for extract a word (248-bit)
/// into 62 field elements. The basic idea is to simply
/// break it using power operations and then assert the range of each
#[derive(Clone,Debug)]
pub struct WordExtractGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	max_word_len: usize,
}

impl <F:PrimeField> WordExtractGadget<F>{
	pub fn new(max_word_len: usize) -> Self{
		Self{_f: PhantomData, max_word_len: max_word_len}
	}
}

impl <F:PrimeField> SigmaGadget<F> for WordExtractGadget<F>{
	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: Rc<Vec<ContainerConfig>>, _idx: usize){
		unimplemented!("not needed. handled by legacy code");
	}

	/// Get the instructions for build its statement.
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
		let wlen = self.max_word_len;
		vec![
			// word (special) - relative gadget id does not apply
			// only first gadget allows non-zero for 4'th entry (len)
			(0, 0, 0, wlen),
			// input (self, full input segment allocated by its size)
			(0, 1, 0, 0),
			// output (self, full output allocated
			(0, 2, 0, 0),
			// data (full data allocated)
			(0, 3, 0, 1+wlen * LEGS),
			// subtbl id for input (no check)
			(0, 4, 0, 0),
			// subtbl id for output (no check)
			(0, 5, 0, 0),
			// subtbl id for data  (all of the data)
			(0, 6, 0, 1+wlen*LEGS),
		]
	}

	/// return the sizes of inp/oup/data to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize){
		(0, 0, 1 + self.max_word_len * LEGS)
	}

	fn est_cost(&self)->usize{

		let est = self.max_word_len * 68;
		est
	}

	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		// Its statement is structured as follows:
		// [(1) entire_word_seg:  mapped from upper level gadget manager
		//  (2) data: act_word_len: 1 field element. which needs to be
		//      checked by the caller.
		//      extracted word_seg: mapped to data
		//  (3) NO input/output
		//  (4) its own subtbl_id for all except word_seg
		// ]
		// NO msg1,2,3
		let word_len = self.max_word_len;
		let data_len = 1 + self.max_word_len * LEGS;
		let inp_len = 0;
		let oup_len = 0;
		let subtbl_id_len = data_len + inp_len + oup_len;
		let stat_len = word_len + data_len +inp_len + oup_len + subtbl_id_len;
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
		let data_len = 1 + wlen * LEGS;
		let inp_len = 0;
		let oup_len = 0;
		let subtbl_id_len = data_len + inp_len + oup_len;

		//2. get the parts of the statement
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		// NOTE: no input and output
		let word_seg = my_stmt[0..wlen].to_vec(); //from word
		let act_seg_len = my_stmt[wlen].clone(); //from data
		let extracted_word = my_stmt[wlen+1..wlen+1+LEGS*wlen].to_vec();
		let subtbl_id = my_stmt[wlen+1+LEGS*wlen..
			wlen+1+LEGS*wlen+subtbl_id_len].to_vec();
		let mut remain =  act_seg_len.clone();

		//3. build the power of 4's
		let f4 = FpVar::<F>::new_constant(cs.clone(), F::from(16u32))?;
		let f1 = FpVar::<F>::new_constant(cs.clone(), F::from(1u32))?;
		let mut vec_pows = vec![f1; LEGS];
		for i in 1..LEGS{ vec_pows[i]	 = &vec_pows[i-1] * &f4; }

		//4. assert the validity of extracted word
		let zero_var = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
		let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?;
		for i in 0..wlen{
			let b_remain_zero = remain.is_zero()?;
			let wd = b_remain_zero.select(&zero_var, &word_seg[i])?;
			let mut wsum = zero_var.clone();
			for j in 0..LEGS{
				let idx = i*LEGS + j;
				wsum += &vec_pows[j] * &extracted_word[idx];
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

		//5. assert the range of all chars should be CHAR range
		// note we are asserting data[1..]
		let char_tbl = FpVar::<F>::new_constant(cs.clone(), F::from(CHAR))?;
		for i in 1..data_len{
			subtbl_id[i].enforce_equal(&char_tbl)?;
			#[cfg(test)]{
				use ark_r1cs_std::{R1CSVar};
				if subtbl_id[i].value().is_ok(){
					assert!(subtbl_id[i].value()?==char_tbl.value()?);
				}
			}
		}

		Ok(())
	}
}

/// Advice for the WordExtract Gadget.
pub struct WordExtractAdvice<F:PrimeField>{
	/// consists of act_word_len and then the extracted legs
	pub data: Vec<F>,
}

impl <F: PrimeField> NdAdvice for WordExtractAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField> WordExtractAdvice<F>{
	/// word_seg is the one with max compacity, actual size
	/// is the actual word len. We convert all remaining 
	/// as 0.
	pub fn new(word_seg: &Vec<F>, actual_size: usize)->Self{
		//1. normalize the input
		let mut word = word_seg.clone();
		for i in actual_size..word_seg.len(){ word[i] = F::zero(); }

		//2. do the conversion
		let mut nibbles = packed_to_nibbles(&word);
		assert!(nibbles.len() == LEGS * word.len());
		#[cfg(test)]{ 
			use utils::data::{pack_nibbles};
			let packed = pack_nibbles(&nibbles);
			assert!(packed.len() == word.len());
			for i in 0..word.len(){
				assert!(word[i]==packed[i]);
			}
		}
		let mut data = vec![ F::from(actual_size as u32) ];
		data.append(&mut nibbles);


		Self{data}
	}
}

#[cfg(test)]
pub mod tests_word_extract_gadget{
	use ark_crypto_primitives::sponge::Absorb;
	use ark_ff::{PrimeField,Zero};
	use ark_relations::r1cs::ConstraintSystem;
	use std::{rc::Rc};
	use ark_bn254::{Fr};
	use folding_schemes::{
		folding::foldpot::{
			sigma_ir1cs::{
				SigmaGadget, WitnessSigmaIR1CS,
				WitnessSigmaIR1CSConfig, WitnessSigmaIR1CSVar,
				ZiPartTwoInst,
			},
			container_config::ContainerConfig,
		},
	};
	use crate::gadgets::word_extract::{WordExtractGadget,WordExtractAdvice};
	use utils::data::{rand_fe_by_bits};
	use data_processor::clam_db::CHAR;

	pub fn test_gadget<F:PrimeField + Absorb> (
		g: Rc<dyn SigmaGadget<F>>, 
		word: &Vec<F>,
		inp: &Vec<F>,
		oup: &Vec<F>,
		data: &Vec<F>,
		subtbl_id: &Vec<F>, //should not include word (covering inp/oup/data)
		lkup_share_size: usize){
		test_gadget_adv(g, word, inp, oup, data, subtbl_id, lkup_share_size, 
			true, None);
	}

	/// Given a gadget, and a statement vector
	/// generate its msg1 to 3 and call assert3_msg3
	/// Check if the generated constraint system is satisfiable.
	pub fn test_gadget_adv<F:PrimeField + Absorb> (
		g: Rc<dyn SigmaGadget<F>>, 
		word: &Vec<F>,
		inp: &Vec<F>,
		oup: &Vec<F>,
		data: &Vec<F>,
		subtbl_id: &Vec<F>, //should not include word (covering inp/oup/data)
		lkup_share_size: usize,
		b_legacy: bool, //when true, the stmt_map is generated using simple way
						//true works for CP gadgets
						//false works for SED and later gadgets
		vec_cfgs: Option<Vec<ContainerConfig>>, //set when b_legacy false
	){
		//1. generate the msg1, msg2, and msg3
		//assert!(subtbl_id.len()== inp.len() + oup.len() + data.len());
		let mut rng = ark_std::test_rng();
		let stmt_vec = vec![word.clone(), inp.clone(), oup.clone(),
			data.clone(), subtbl_id.clone()].concat();

		let g = g.as_ref();
		let vec_msg_size = g.get_msg_size();
		let (_stmt_size, msg1_size, msg2_size, msg3_size)  = vec_msg_size;
		let stmt_size = stmt_vec.len(); //NOTE: overwrite because
		// stmt_vec might contain combined stmt_vec from multiple gadgets.

		//assert!(stmt_vec.len()==stmt_size); not ncessarily when
		// stmt_vec has MULTIPLE gadgets involved.
		let v_idx = if b_legacy {
			vec![(0, stmt_vec.len()-1)] //cp cases
		}else{
			// this pretty much simulate the implementation of
			// sed_mapper.rs get_gadgets_stmt_map
			//1.1 first compute the sizes of all segments
			let vec_cfgs = vec_cfgs.expect("vec_cfg null!");
			let mut total_sizes = vec![0usize; 7]; 
			for i in 0..vec_cfgs.len(){
				let sizes = vec_cfgs[i].get_to_add_size();
				// other than 1st gadget, no one adds for word
				if i>0 {assert!(sizes[0]==0);}
				total_sizes = total_sizes.into_iter().zip(
					sizes.into_iter()).map(|(x,y)| x+y)
					.collect::<Vec<usize>>();
			}
			let mut seg_starts = vec![0usize; 7];
			for i in 1..7{ seg_starts[i] = seg_starts[i-1] + total_sizes[i-1];}

			//1.2 based on start handle each 
			let instructions = g.get_stmt_map_instructions();
			let sizes = vec![word.len(), inp.len(), oup.len(), data.len(),
				inp.len(), oup.len(), data.len()];
			assert!(sizes[4] + sizes[5] + sizes[6]==subtbl_id.len());
			let res = instructions.into_iter().map(
				|(_gadget_offset, seg_id, start, len)|{
				let res = (seg_starts[seg_id] + start, seg_starts[seg_id] + start + len -1 );

				res
			}).collect::<Vec<(usize, usize)>>();
			res
		};

		let msg1 = g.gen_msg1(&stmt_vec, &v_idx); 
		assert!(msg1.len()==msg1_size);
		let mut msg2 = vec![];
		for _i in 0..msg2_size{ msg2.push(F::rand(&mut rng)); }
		assert!(msg2.len()==msg2_size);
		let msg3 = g.gen_msg3(&stmt_vec, &v_idx,  &msg1, 0, msg1.len(),
			&msg2, 0, msg2.len());
		assert!(msg3.len()==msg3_size);

		//2. generate the WitnessSigma instance
		let fq_bits = 256; //actually does not matter for this function
		let cmf_size = 4usize;
		let extra_var_size = 2usize;
		let inv_hab22_right_size = lkup_share_size;
		let inv_hab22_left_size = subtbl_id.len() + extra_var_size;
		let cfg = WitnessSigmaIR1CSConfig{
			cmF_size: cmf_size, //4 field elements for cmF
			extra_var_size: extra_var_size, 
				//unused_input_size, unused_output_size
			statement_size: stmt_size,
			stmt_map: vec![v_idx],
			msg1_size: msg1_size,
			msg2_size: msg2_size,
			msg3_size: msg3_size,
			vec_msg_sizes: vec![vec_msg_size],
			zi_part2_size: ZiPartTwoInst::<F>::size(true, fq_bits),
			inv_hab22_left_size: inv_hab22_left_size,
			inv_hab22_right_size: inv_hab22_right_size,
		};

		//3. construct the witness var
		let zero = F::zero();
		let wit = WitnessSigmaIR1CS::<F>{
			cmF: vec![zero; cmf_size],
			unused_input_size: zero,
			unused_output_size: zero,
			statement: stmt_vec,
			msg1: msg1,
			msg2: msg2,
			msg3: msg3,
			zi_part2: vec![zero; cfg.zi_part2_size],
			inv_hab22_left: vec![zero; cfg.inv_hab22_left_size],
			inv_hab22_right: vec![zero; cfg.inv_hab22_right_size],
		};
        let cs = ConstraintSystem::<F>::new_ref();
		let vec_var = wit.to_vec_fp_var(cs.clone());
		let witvar = WitnessSigmaIR1CSVar::from_vec(&cfg, &vec_var);
		g.assert_msg3(0, cs.clone(), &witvar, &cfg).expect("assert m3 fail");
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_word_extract(){
		println!("OK");
		let mut rng = ark_std::test_rng();
		let (wlen, act_size) = (8usize, 6usize);
		let word = vec![rand_fe_by_bits(248, &mut rng); wlen];
		let weg = WordExtractGadget::<Fr>::new(wlen);
		let rg = Rc::new(weg);
		let adv = WordExtractAdvice::new(&word, act_size);
		let inp = vec![];
		let oup = vec![];
		let data = adv.data.clone();
		let mut subtbl_id = vec![Fr::from(CHAR); 
			inp.len() + oup.len() + data.len()];
		subtbl_id[0] = Fr::zero(); //don't care for act_word_len
		let lkup_share_size = 4usize;
		test_gadget::<Fr>(rg, &word, &inp, &oup, &data, &subtbl_id, 
			lkup_share_size);
	}
}
