/* Created 02/26/2025 */

//use std::sync::{Arc, Mutex};
use folding_schemes::folding::foldpot::container_config::ColEle;
use ark_ff::{PrimeField};
use std::marker::{PhantomData};
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig, NdAdvice},
	container_config::{ContainerConfig},
};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::R1CSVar;
use crate::gadgets::commons::{sum_vec_vars_weighted};
use ark_r1cs_std::{
	fields::{fp::FpVar},
	alloc::AllocVar,
	eq::EqGadget,
};
use std::any::Any;
use utils::{data::{packed_to_nibbles}, consts::B_DEBUG};
use folding_schemes::{Error};

pub const LEGS:usize = 62;
/// This gadget is responsible for extract a word (248-bit)
/// into 62 field elements. The basic idea is to simply
/// break it using power operations and then assert the range of each
#[derive(Clone,Debug)]
pub struct WordExtractGadget<F:PrimeField + ColEle>{ 
	_f: PhantomData<F>,
	max_word_len: usize,
	pub job_id: usize,
}

impl <F:PrimeField + ColEle> WordExtractGadget<F>{
	pub fn new(max_word_len: usize) -> Self{
		Self{_f: PhantomData, max_word_len: max_word_len, job_id: 0}
	}
}

impl <F:PrimeField + ColEle> SigmaGadget<F> for WordExtractGadget<F>{
	fn get_name(&self)->&str {"WordExtractGadget"}

	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
	}
	fn get_job_id(&self)->usize{
		self.job_id
	}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: std::sync::Arc<Vec<ContainerConfig>>, _idx: usize){
		unimplemented!("not needed. handled by legacy code");
	}

	fn get_container_config(&self)->ContainerConfig{
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

	/// return the sizes of inp/oup/data/failed_sigs/discharged_sigs
	/// to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		(0, 0, 1 + self.max_word_len * LEGS, 0, 0)
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

	/// COST:
	/// r1cs: 6*word_len (note: not nibbles), vasr: 4*word_len
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig, 
		_word_id: FpVar<F>, _subseg_id: FpVar<F>) 
		-> Result<(), SynthesisError>{
		let b_debug = B_DEBUG;
		let nc = cs.num_constraints();
		let nv = cs.num_witness_variables();

		//1. retrive the statement instance and get all parts
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		let my_stmt = stmt_idx.iter().map(|(a,b)|
			wtns.statement[*a..*b+1].to_vec()).flatten()
			.collect::<Vec<FpVar<F>>>();
		//assert!(my_stmt.len()==self.get_msg_size().0); to make test case
		//happy
		let wlen = self.max_word_len;
		let data_len = 1 + wlen * LEGS;
		let inp_len = 0;
		let oup_len = 0;
		let _subtbl_id_len = data_len + inp_len + oup_len;

		//2. get the parts of the statement
		//organize statement: structured as
		// [word, inp, output, data, subtbl_id]
		// NOTE: no input and output
		let word_seg = my_stmt[0..wlen].to_vec(); //from word
		let act_seg_len = my_stmt[wlen].clone(); //from data
		let extracted_word = my_stmt[wlen+1..wlen+1+LEGS*wlen].to_vec();
		let _subtbl_id = my_stmt[wlen+1+LEGS*wlen..
			wlen+1+LEGS*wlen+ _subtbl_id_len].to_vec();

		//3. build the power of 4's
		let f4 = F::from(16u32);
		let f1 = F::one();
		let mut vec_pows = vec![f1; LEGS];
		for i in 1..LEGS{ vec_pows[i]	 = vec_pows[i-1] * f4; }

		//4. New invariant (Step 2 of pad-invariant rework):
		// every frag is padded to max_word_len so act_seg_len ==
		// word_seg.len() == wlen always. We enforce this in-circuit
		// and drop the per-position conditional select that used to
		// mask out the pad region. The pad nibbles (when present at
		// the tail of the last real F-element or in fully-padded
		// F-elements) are now bound to whatever pseudo-random value
		// the prover supplied in word_seg — same as on the
		// discharge_prover side — so the DFA's view is consistent.
		let wlen_const = FpVar::<F>::new_constant(cs.clone(),
			F::from(wlen as u32))?;
		act_seg_len.enforce_equal(&wlen_const)?;
		for i in 0..wlen{
			let wsum = sum_vec_vars_weighted(
				&extracted_word[i*LEGS..(i+1)*LEGS], &vec_pows);
			wsum.enforce_equal(&word_seg[i])?;
			if B_DEBUG {
				if wsum.value().is_ok(){
					assert!(wsum.value()?==word_seg[i].value()?);
				}
			}
		}

		//5. assert the range of all chars should be CHAR range
		// note we are asserting data[1..]
		//NO need anymore as all subtbl IDs are CONSTANT.
		//They are fixed in circuit
		// This leads to logup check from 3 constraints -> 1 constraint
		// Also we do not need to check them here as they are 
		// constants.
		// in fact even if excuting them does not generate new constraints.
// 		use data_processor::clam_db::CHAR;
//  		let char_tbl = FpVar::<F>::new_constant(cs.clone(), F::from(CHAR))?;
//  		for i in 1..data_len{
//  			_subtbl_id[i].enforce_equal(&char_tbl)?;
//  			#[cfg(test)]{
//  				use ark_r1cs_std::{R1CSVar};
//  				if _subtbl_id[i].value().is_ok(){
//  					assert!(_subtbl_id[i].value()?==char_tbl.value()?);
//  				}
//  			}
//  		}
		if b_debug{
			println!("## word_extract cost for word_len: {}, nibbles: {}, r1cs: {}, vars: {}", wlen, wlen*LEGS, cs.num_constraints()-nc, cs.num_witness_variables()-nv);
		}

		Ok(())
	}
}

/// Advice for the WordExtract Gadget.
#[derive(Debug)]
pub struct WordExtractAdvice<F:PrimeField + ColEle>{
	/// consists of act_word_len and then the extracted legs
	pub data: Vec<F>,
}

impl <F: PrimeField + ColEle> NdAdvice for WordExtractAdvice<F>{
	fn as_any(&self) -> &dyn Any {self}
}

impl <F: PrimeField + ColEle> WordExtractAdvice<F>{
	/// word_seg has length == max_word_len; actual_size MUST equal
	/// word_seg.len() under the pad-invariant rework (Step 2). Every
	/// frag is padded to max_word_len by `pad_word_to_multiple` (and
	/// `pack_nibbles` for the sub-F tail) before reaching the
	/// mapper, so there is no longer a "trim then zero-fill" step.
	pub fn new(word_seg: &Vec<F>, actual_size: usize)->Result<Self, Error>{
		//1. normalize the input
		assert!(actual_size == word_seg.len(),
			"WordExtractAdvice::new: actual_size ({}) must equal \
			 word_seg.len() ({}) under the pad-invariant rework",
			actual_size, word_seg.len());
		let word = word_seg.clone();

		//2. do the conversion
		let mut nibbles = packed_to_nibbles(&word);
		assert!(nibbles.len() == LEGS * word.len());
		if B_DEBUG {
			use utils::data::{pack_nibbles};
			let packed = pack_nibbles(&nibbles);
			assert!(packed.len() == word.len());
			for i in 0..word.len(){
				assert!(word[i]==packed[i]);
			}
		}
		let mut data = vec![ F::from(actual_size as u32) ];
		data.append(&mut nibbles);


		Ok(Self{data}) //no capacity issue always return Ok.
	}
}

#[cfg(test)]
pub mod tests_word_extract_gadget{
	use ark_crypto_primitives::sponge::Absorb;
	use ark_ff::{PrimeField,Zero};
	use ark_relations::r1cs::ConstraintSystem;
	use std::{sync::Arc};
	use ark_bn254::{Fr};
	use crate::gadgets::commons::{gen_m_table};
	use folding_schemes::{
		folding::foldpot::{
			sigma_ir1cs::{
				SigmaGadget, WitnessSigmaIR1CS,
				WitnessSigmaIR1CSConfig, WitnessSigmaIR1CSVar,
				ZiPartTwoInst, StatementConfig,
				StatementInst,
				LookupTableTwoCol_Inst,
			},
			container_config::ContainerConfig,
		},
	};
	use folding_schemes::folding::foldpot::container_config::ColEle;
	use crate::gadgets::word_extract::{WordExtractGadget,WordExtractAdvice};
	use utils::data::{rand_fe_by_bits};
	use data_processor::clam_db::CHAR;
	use ark_std::marker::PhantomData;
	use ark_r1cs_std::{fields::fp::FpVar,alloc::AllocVar};

	pub fn test_gadget<F:PrimeField + Absorb + ColEle> (
		g: Arc<dyn SigmaGadget<F> + Send + Sync>, 
		word: &Vec<F>,
		inp: &Vec<F>,
		oup: &Vec<F>,
		data: &Vec<F>,
		subtbl_id: &Vec<F>, //should not include word (covering inp/oup/data)
		lkup_share_size: usize){
		//use empty vec for failed_sigs and discharged_sigs
		test_gadget_adv(g, word, inp, oup, data, &vec![], &vec![], subtbl_id, lkup_share_size, 
			true, None);
	}

	/// Given a gadget, and a statement vector
	/// generate its msg1 to 3 and call assert3_msg3
	/// Check if the generated constraint system is satisfiable.
	///
	/// we are assuming g is the "LAST" of the vec_cfgs
	/// NOTE THAT for legacy case: inp/... data has the info for
	///     the LAST gadget (g) only.
	/// For non-legacy case, word/inp/...data has the infor for 
	/// ALL gadgets (in a CompositeComponent)
	pub fn test_gadget_adv<F:PrimeField + Absorb + ColEle> (
		g: Arc<dyn SigmaGadget<F> + Send + Sync>, 
		word: &Vec<F>,
		inp: &Vec<F>,
		oup: &Vec<F>,
		data: &Vec<F>,
		failed_sigs: &Vec<F>,
		discharged_sigs: &Vec<F>,
		subtbl_id: &Vec<F>, //should not include word (covering inp/oup/data)
		lkup_share_size: usize,
		b_legacy: bool, //when true, the stmt_map is generated using simple way
						//true works for CP gadgets
						//false works for SED and later gadgets
		vec_cfgs: Option<Vec<ContainerConfig>>, //set when b_legacy false
	){
		//1. generate the statement
		//1.1 generate StatementConfig
		let inp_size = inp.len();
		let oup_size = oup.len();
		let word_subseg_size = word.len();
		let data_size = data.len();
		let failed_sig_size = failed_sigs.len();
		let discharged_sig_size = discharged_sigs.len();
		assert!(inp_size + oup_size + data_size == subtbl_id.len());
		let b_cyclepair = false;
		let stmt_cfg = StatementConfig::new(
			inp_size, oup_size, word_subseg_size,
			data_size, lkup_share_size, failed_sig_size, discharged_sig_size,
			b_cyclepair);
		assert!(subtbl_id.len()== inp.len() + oup.len() + data.len());
		let mut rng = ark_std::test_rng();

		//1.2 generate the statement
		let (zero,one) = (F::zero(),F::one());
		let mtbl_sigs = gen_m_table(&failed_sigs, &discharged_sigs);
		let stmt = StatementInst::<F,LookupTableTwoCol_Inst<F>>{
			pc_i: zero,
			pc_i1: zero,
			n_circ: one,
			n_circ_minus_pc: one,
			act_input_size: F::from(inp.len() as u32),
			act_output_size: F::from(oup.len() as u32),
			act_lookup_share_size: F::from(lkup_share_size as u32),
			act_word_subseg_size: F::from(word.len() as u32),
			word_id: zero,
			subseg_id: zero,
			total_word_len: F::from(word.len() as u32),
			total_word_segs: one,
			total_words: one,
			r_F: F::from(2u32), //temp for debug

			batch_r: zero,
			batch_v: zero,
			r_all_words: zero,
			r_kzg_len: zero,
			r_vec_r: zero,
			r_vec_v: zero,
			r_word_i: zero,
			accumulated_word_len: zero,
			f_result: zero,

			inp_buf: inp.to_vec(),
			oup_buf: oup.to_vec(),
			word_subseg: word.clone(),
			data: data.to_vec(),
			subtable_id: subtbl_id.clone(),
			col1_share: vec![zero; lkup_share_size], //will be filled 
			col2_share: vec![zero; lkup_share_size], //to be updated
			m_share: vec![zero; lkup_share_size],//will be filled

			failed_sigs: failed_sigs.to_vec(),
			discharged_sigs: discharged_sigs.to_vec(),
			mtbl_sigs: mtbl_sigs.to_vec(),

			_lk: PhantomData,
		};

		let stmt_vec = if b_legacy{//NOTE for legacy we do not
			//rely on WitnessConfig to generate stmt_maps
			//just follow the order of word/inp/oup/.../discharged_sigs
			//which is MANUALLY constructed and supplied 
			//to the test_gadget_function
			//in the test code
			let real_data = vec![word.clone(), inp.clone(), oup.clone(),
				data.clone(), subtbl_id.clone(), failed_sigs.clone(),
				discharged_sigs.clone()].concat();
			let to_pad_size = stmt_cfg.total_size() - real_data.len();

			//just make it of the same size as config to make
			//WitnessSigmaIR1CS:to_vec_fp_var happy
			let res = [&real_data[..], &vec![zero; to_pad_size][..]].concat();
			res

		}else{
			stmt.to_vec()
		};

		//2. genearte the statement map for all gagets
		// NOTE that there might be multiple gadgets invovled
		// for legacy case: only one gadget is involved.
		//todo: reset its si_data_info

		//2.2 generate the allocation space of each segment
		//HERE: we have only one ComposbleComponent here consisting
		//of one or more gadgets (legacy case, one gadget)
		let rg_word = (stmt_cfg.idx_word_subseg, 
			stmt_cfg.idx_word_subseg+word_subseg_size-1);
		let rg_inp = (stmt_cfg.idx_inp, stmt_cfg.idx_inp + inp_size-1);
		let rg_oup = (stmt_cfg.idx_oup, stmt_cfg.idx_oup + oup_size-1);
		let rg_data = (stmt_cfg.idx_data, stmt_cfg.idx_data + data_size-1);
		let rg_failed_sigs= (stmt_cfg.idx_failed_sigs,
			stmt_cfg.idx_failed_sigs + failed_sig_size-1);
		let rg_discharged_sigs= (stmt_cfg.idx_discharged_sigs,
			stmt_cfg.idx_discharged_sigs + discharged_sig_size-1);

		let idx_inp_in_subtbl_id = stmt_cfg.idx_subtable_id + 0;
		let idx_oup_in_subtbl_id = stmt_cfg.idx_subtable_id + 
			stmt_cfg.input_size;
		let idx_data_in_subtbl_id = stmt_cfg.idx_subtable_id + 
			stmt_cfg.input_size + stmt_cfg.output_size;
		let rg_subtbl_id_inp = (idx_inp_in_subtbl_id,
			idx_inp_in_subtbl_id + inp_size-1);
		let rg_subtbl_id_oup = (idx_oup_in_subtbl_id,
			idx_oup_in_subtbl_id + oup_size-1);
		let rg_subtbl_id_data = (idx_data_in_subtbl_id, 
			idx_data_in_subtbl_id + data_size-1);

		let cur_alloc= vec![//the range of each segment
			rg_word, rg_inp, rg_oup, rg_data,
			rg_subtbl_id_inp, rg_subtbl_id_oup, rg_subtbl_id_data,
			rg_failed_sigs, rg_discharged_sigs,
		];
		let seg_starts = cur_alloc.iter().map(|r| r.0).collect::<Vec<usize>>();
		assert!(seg_starts.len()==9);

		//2.3 simulate sed_mapper.rs: get_gadgets_stmt_map to 
		//stmt_map has multiple gadgets, but we assume only
		//one composable component.

		let g = g.as_ref();
		let vec_stmt_map = if b_legacy {
			vec![vec![ (0, stmt_vec.len()-1)]] //we assume the the tester
				//has manually prepared word/inp/.... in order
				//instead of relying stmt_maps where fsm, sig, pack
				//don't have
		}else{
			// this pretty much simulate the implementation of
			// sed_mapper.rs get_gadgets_stmt_map
			// (1) collect my_maps note htat compared with
			let vec_cfgs = vec_cfgs.expect("vec_cfg null!");
			let mut vec_stmt_map = vec![];
			for i in 0..vec_cfgs.len(){
				let cfg = &vec_cfgs[i];
				let instructions = cfg.gen_stmt_map_instructions();
				let my_maps = instructions.into_iter().map(|instruction|{
					let (_gadget_offset, seg_id, start, len) = instruction;
					//let idx_gadget = ((i as i32) + gadget_offset) as usize;
					//it's already adjusted by adjust_locations of
					//container_config, so there is no need to perform adjust
					let res = (seg_starts[seg_id] + start, 
						seg_starts[seg_id] + start + len -1);

					res
				}).collect::<Vec<(usize,usize)>>();
				vec_stmt_map.push(my_maps);
			}
			vec_stmt_map
		};

		//2.4 construct the msg1, msg2, msg3
		let vec_msg_size = g.get_msg_size();
		let (_stmt_size, msg1_size, msg2_size, msg3_size)  = vec_msg_size;
		let stmt_size = stmt_vec.len(); //NOTE: overwrite because
		let last_id = vec_stmt_map.len()-1;
		let msg1 = g.gen_msg1(&stmt_vec, &vec_stmt_map[last_id]); 
		assert!(msg1.len()==msg1_size);
		let mut msg2 = vec![];
		for _i in 0..msg2_size{ msg2.push(F::rand(&mut rng)); }
		assert!(msg2.len()==msg2_size);
		let msg3 = g.gen_msg3(&stmt_vec, &vec_stmt_map[last_id], 
			&msg1, 0, msg1.len(), &msg2, 0, msg2.len());

		//2. generate the WitnessSigma instance
		let fq_bits = 256; //actually does not matter for this function
		let cmf_size = 4usize;
		let extra_var_size = 2usize;
		let inv_hab22_right_size = lkup_share_size;
		let inv_hab22_left_size = subtbl_id.len() + extra_var_size;
		let n_gadgets = vec_stmt_map.len();
		let cfg = WitnessSigmaIR1CSConfig{
			cmF_size: cmf_size, //4 field elements for cmF
			extra_var_size: extra_var_size, 
				//unused_input_size, unused_output_size
			statement_size: stmt_size,
			stmt_map: vec_stmt_map, 
			msg1_size: msg1_size,
			msg2_size: msg2_size,
			msg3_size: msg3_size,
			vec_msg_sizes: vec![vec_msg_size; n_gadgets], //this is simulated
				//as ContainerConfig cannot generate vec_messages (only gadget
				//can). But to avoid changing the interfaces, we populate
				//all as the same vec_msg_size for the LAST gadget g.
				//this is ok, as get_gadget_indices() later is called
				//on building assert_msg3, but it only needs the stmt_size
				//not the msg1-3 sizes. So this should be ok.
			zi_part2_size: ZiPartTwoInst::<F>::size(true, fq_bits),
			inv_hab22_left_size: inv_hab22_left_size,
			inv_hab22_right_size: inv_hab22_right_size,
			stmt_cfg,
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
		let vec_var = wit.to_vec_fp_var(cs.clone(), &cfg);
		let witvar = WitnessSigmaIR1CSVar::from_vec(&cfg, &vec_var);
		let last_idx = cfg.stmt_map.len()-1;
		let w_id = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
		let s_id = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
		g.assert_msg3(last_idx, cs.clone(), &witvar, &cfg, w_id, s_id).expect("assert m3 fail");
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_word_extract(){
		println!("OK");
		let mut rng = ark_std::test_rng();
		// Pad-invariant rework (Step 5): actual_size MUST equal wlen
		// now. Tests construct full-length random words; pad slots
		// (when present) would carry pseudo-random bytes from the
		// canonical pad stream, but we just fill everything random.
		let wlen = 8usize;
		let act_size = wlen;
		let word = vec![rand_fe_by_bits(248, &mut rng); wlen];
		let weg = WordExtractGadget::<Fr>::new(wlen);
		let rg = Arc::new(weg);
		let adv = WordExtractAdvice::new(&word, act_size);
		let inp = vec![];
		let oup = vec![];
		let data = adv.unwrap().data.clone();
		let mut subtbl_id = vec![Fr::from(CHAR);
			inp.len() + oup.len() + data.len()];
		subtbl_id[0] = Fr::zero(); //don't care for act_word_len
		let lkup_share_size = 4usize;
		test_gadget::<Fr>(rg, &word, &inp, &oup, &data, &subtbl_id,
			lkup_share_size);
	}
}
