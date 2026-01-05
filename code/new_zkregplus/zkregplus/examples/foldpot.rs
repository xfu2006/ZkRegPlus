/* Created 01/23/2025
   Show an example how foldpot framework works
*/
use folding_schemes::{Error,commitment::{pedersen::Pedersen, kzg::KZG}};
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{
		GadgetMapper,SigmaGadget,WitnessSigmaIR1CSVar,
		WitnessSigmaIR1CSConfig, StatementConfig,
		StatementInst, LookupTableTwoCol_Inst, SigmaIR1CS_Inst,
		LookupTableTwoCol, StatementExtraInfo, SigmaIR1CS,
		DummyNdAdvice,DummyCapacity,WordInfo,Capacity,NdAdvice
	},
	container_config::ContainerConfig,
	utils::{Timer,expand2},
	driver::{foldpot_main},
	circuits_super::{field_to_usize},
};
use std::{rc::Rc, cell::RefCell};
use ark_groth16::Groth16;
use ark_ff::{PrimeField};
use ark_std::marker::PhantomData;
use ark_relations::r1cs::{ConstraintSystemRef,SynthesisError};
use ark_r1cs_std::{
	alloc::{AllocVar},
	eq::EqGadget,
	fields::{fp::FpVar},
};

use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
//type CS1 = KZG<'static, Bn254>; //TO REMOVE
type CS1 = Pedersen<Projective>;
//EXTERNAL commitment KZG for decider
type CS1E = KZG<'static, Bn254>;
type CS2 = Pedersen<Projective2>;
type C1 = Projective;
type C2 = Projective2;
type F = Fr;
type GC1 = GVar;
type GC2 = GVar2;
type LK = LookupTableTwoCol_Inst<Fr>;
//type FC = SigmaIR1CS_Inst<Fr,Projective,KZG<'static,Bn254>,LK>;
type GM = SumMapper<F,LK>; 
type FC = SigmaIR1CS_Inst<Fr,Projective,Pedersen<Projective>,LK,GM>;
type S = Groth16<Bn254>;
type C2G2 = ProjectiveG2;

/// a gadget that computes the sum of inputs as long as
/// they are contained in SubTable 2. Note that this is the
/// ``best effort" sum, the prover has to provide the 
/// correct subtable ID (2) for those in sub-table 2.
/// If one element is indeed in sub-table 2, but provided
/// with a subtable ID 0, we do NOT count (sum) it. So in this sense,
/// the gadget returns a sum of a subset of the
/// inputs in subtable 2.
/// 
/// The gadget is parameterized by a size n:
/// Statement (x_1, x_2 ...x_n ;w_i, ..., w_n; sum_in; sum_out): 
/// where x_i is the number to verify 
/// and w_i is the subtable_id (either 0 or 2).
/// The gadget works by sending a dummy msg1, 
/// receiving a dummy msg2, and then
/// copying w as msg3. Note that the Gadget mapper needs
/// to map the witness part to the subtable_id in the StatementInstance
#[derive(Clone,Debug)]
pub struct SumGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	/// the number of elements to handle
	n: usize,
}

impl <F:PrimeField> SigmaGadget<F> for SumGadget<F>{
	/// return its name
	fn get_name(&self)->&str {"SumGadget"}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self,_cfg: Rc<Vec<ContainerConfig>>,_idx: usize){
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

	/// return the sizes of inp/oup/data/failed/discharged_sigs to append to the
	/// buffer of GadgetMapper.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
		unimplemented!("no need to implement. legacy of caller handles it");
	}
	fn est_cost(&self)->usize{ 3*self.n }

	/// statment `(x;w;sum_in;sum_out)` where x has n elements, w has
	/// n elements. msg1, and msg1 are dummy single element.
	/// msg3 is the w part retrieved from the statment
	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		//statment part has n elements for x, n for w, and 2 extra for
		//sum_in and sum_out
		(2*self.n + 2, 1, 1, self.n)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>)
	-> Vec<F>{
		// dummy
		vec![F::one()]	
	}

	fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: 
		&Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		let n = self.n;
		let w = stmt_idx[n..2*n].iter().map(|i| stmt_vec[(*i).0]).
			collect::<Vec<F>>();

		w
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		let (stmt_idx, _m1_idx, _m2_idx, _m3_idx) = cfg.get_gadget_indices(i);
		let n = self.n;
		let x = stmt_idx[0..n].iter().map(|i| wtns.statement[(*i).0].clone()).
			collect::<Vec<FpVar<F>>>();
		let w = stmt_idx[n..2*n].iter().map(|i| wtns.statement[(*i).0].clone()).
			collect::<Vec<FpVar<F>>>();
		let sum_in = &wtns.statement[stmt_idx[2*n].0];
		let sum_out = &wtns.statement[stmt_idx[2*n+1].0];
		let diff = sum_out - sum_in;

		let mut exp_diff = FpVar::<F>::new_witness(cs.clone(),
			||  Ok(F::zero()) )?;
		let zero_var= FpVar::<F>::new_constant(cs.clone(), F::zero() )?;
		let two_var= FpVar::<F>::new_constant(cs.clone(), F::from(2u32))?;
		for i in 0..n{
			let b_add = w[i].is_eq(&two_var)?;
			let to_sum = b_add.select(&x[i], &zero_var)?; 
			exp_diff = &exp_diff + &to_sum;
		}
		exp_diff.enforce_equal(&diff)?;
		#[cfg(test)]{
			assert!(exp_diff.value()?==diff.value()?,
				"exp_diff: {} != diff: {}", exp_diff.value()?, 
				diff.value()?);
		}

		Ok(())
	}
}

/// Two modes: even mode or odd mode. In odd mode, it processes
/// one field element; in even mode, it processes up to two elements.
/// For instance, in odd mode, if the element is not an odd number,
/// it will not generate the StaementInstance; in even mode,
/// it checks if the first element is even.
#[derive(Clone,Debug)]
pub struct SumMapper<F:PrimeField, LK: LookupTableTwoCol<F>>{
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub b_odd: bool,
}

impl <F:PrimeField, LK:LookupTableTwoCol<F>> SumMapper<F,LK>{
	pub fn new(b_odd: bool)->Self{
		Self{_f: PhantomData, _lk: PhantomData, b_odd: b_odd }
	}
	pub fn can_handle(&self, w0: F)->bool{
		let w0_val = field_to_usize(&w0);
		let b_odd_w = w0_val%2==1;
		b_odd_w == self.b_odd
	}
}


impl <F:PrimeField, LK: LookupTableTwoCol<F>> 
GadgetMapper<F,LK> for SumMapper<F, LK>{
	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, _advice: &Rc<dyn NdAdvice>){ 
		//not needed, handled by legacy code
	}

	/// the capacity is the word length that can be handled by
	/// the circuit
	fn get_capacity(&self)->Rc<dyn Capacity>{
		let word_seg_len = self.max_word_len();
		Rc::new(DummyCapacity{word_seg_len})
	}

	/// given a vector of circuits' gadget mapper, given a word
	/// return the (steps, Vec<pci>, ND_Advice object)
	fn gen_nd_advice_no_limit(&self, word: &Vec<F>, _wi: &WordInfo,
		_prev_advice: Option<Rc<dyn NdAdvice>>)
		-> Option<(Rc<dyn Capacity>, Rc<dyn NdAdvice>)>{
			if word.len()<=self.max_word_len(){
				let w0_val = field_to_usize(&word[0]);
				if (w0_val%2==1) != self.b_odd { return None; }
				Some((
					Rc::new(DummyCapacity{word_seg_len: word.len()}), 
			 		Rc::new(DummyNdAdvice{})
				))
			}else{None }
	}

	fn get_name(&self) -> String{
		if self.b_odd {"OddSum".to_string()} else {"EvenSum".to_string()}
	}

	fn max_word_len(&self)->usize{ 
		if self.b_odd {1} else {2} 
	}

	fn get_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>{ 
		let gadget = if self.b_odd {SumGadget::<F>{_f: PhantomData, n: 1}}
			else {SumGadget::<F>{_f: PhantomData, n:2}};
		vec![Rc::new(RefCell::new(gadget))]
	}

	/// expecting [x_1] or [x_1, x_2], depending on if
	/// its odd/even case. If x_1 is not even (for even circ), throw error
	/// similarly throw error for odd circ if x_1 is not odd.
	/// This is for testing the "best fit" circ in multiple non-uniform
	/// circ environment in supernova.
	fn build_statement(&self, word: &Vec<F>, prev_wit: &Option<StatementInst<F,LK>>, lkup: Rc<RefCell<LK>>, ea: &StatementExtraInfo<F>, 
	_adv: Rc<dyn NdAdvice>, _lkup_share_size: usize, _b_dummy: bool) 
	-> Result<StatementInst<F,LK>, Error>{
		//1. making check on odd/even case
		assert!(word.len()>=1);
		let w0_val = field_to_usize(&word[0]);
		if (w0_val%2==1) != self.b_odd {
		  return Err(Error::Other("Odd/Even case not match.".to_string()));
		}

		//2. compute the actual n
		assert!(word.len()<=2, "word len must be <2");
		let n = if self.b_odd {1} else{
			if word.len()==2 {2} else {word.len()}
		};
		//println!("DEBUG USE 501: word: {:?}, odd: {}, n: {}", word, self.b_odd, n);

		//3. check if the word is in table
		let mut subtbl_id = vec![];
		let (zero, two) = (F::zero(), F::from(2u32));
		for i in 0..n{
			let res = lkup.borrow().find(two, word[i]);
			let sid = if res.is_ok() {two} else {zero};
			subtbl_id.push(sid);
		}
		//println!("DEBUG USE 502: subtbl_id: {:?}", subtbl_id);

		//4. retrieve the previous sum
		let prev_sum = prev_wit.as_ref().map_or(zero, |stmt|{
			let prev_sum =stmt.oup_buf[0];
			prev_sum
		});
		//println!("DEBUG USE 503: word: {:?}, prev_sum: {}", word, prev_sum);

		//5. compute the new sum
		let mut new_sum = prev_sum.clone();
		for i in 0..n{ new_sum+=if subtbl_id[i]==two {word[i]}else{zero}; }
		//println!("DEBUG USE 503: new_sum: {}", new_sum);

		//6. construct the StatmentInstance
		let mut vec_word = vec![zero; 2];
		let mut vec_data = vec![zero; 2];
		for i in 0..n {
			vec_word[i] = word[i];
			vec_data[i] = subtbl_id[i];
		}
		let ncirc_minus_pci = ea.n_circ -ea.pc_i;
		let (zero, one) = (F::zero(), F::one());
		let stmt = StatementInst{
			pc_i: ea.pc_i,
			pc_i1: ea.pc_i1, //will be reset later
			n_circ: ea.n_circ,
			n_circ_minus_pc: ncirc_minus_pci,
			act_input_size: one,
			act_output_size: one,
			act_lookup_share_size: F::from(4u32),
			act_word_subseg_size: F::from(n as u32),
			word_id: ea.word_id,
			subseg_id: ea.subseg_id,
			total_word_len: ea.total_word_len,
			total_word_segs: ea.total_word_segs,
			total_words: ea.total_words,
			r_F: two, //for debug

			batch_r: ea.batch_r,
			batch_v: ea.batch_v,
			r_all_words: ea.r_all_words,
			r_kzg_len: ea.r_kzg_len,
			r_vec_r: ea.r_vec_r,
			r_vec_v: ea.r_vec_v,
			r_word_i: ea.r_word_i,
			accumulated_word_len: ea.accumulated_word_len,
			f_result: new_sum,

			inp_buf: vec![prev_sum],
			oup_buf: vec![new_sum],
			word_subseg: vec_word, //always 2 elements if only 1, pad 0
			data: vec_data.clone(), //always 2 elements, pad 0 if necessary
			subtable_id: vec![
				zero,  //inp_buf don't care
				zero, //oup_buf don't care
				vec_data[0], vec_data[1], //for vec_word
				zero, zero, //don't care for others (for data)
			],
			col1_share: vec![zero; 4], //to be updated, capcity 4
			col2_share: vec![zero; 4], //to be updated
			m_share: vec![zero; 4],//to be updated
			failed_sigs: vec![zero],
			discharged_sigs: vec![zero],
			mtbl_sigs: vec![one],

			_lk: PhantomData,
		};
			
		Ok(stmt)
	}

	fn gen_statement_structure(&self, _lkup_share_size: usize) -> 
		(usize, StatementConfig, Vec<Vec<(usize,usize)>>, 
			Vec<( (usize,usize), (usize,usize) )>, 
			Vec<usize>){
		//1. a sample statemnet structure
		let input_size = 1;
		let output_size = 1;
		let word_subseg_size = 2;
		let data_size = 2;
		let failed_sigs_size = 0;
		let discharged_sigs_size = 0;
		let lookup_share_size = 4; //ignore the input use legacy logic
		let cfg = StatementConfig::new(
			input_size, output_size, word_subseg_size,
			data_size, lookup_share_size,
			failed_sigs_size, discharged_sigs_size,
			false, //b_cyclepair
		);

		//2. generate the result to return
		let n = if self.b_odd {1} else {2};
		// n elements in word, n subtbl_id in data
		// inp_sum in input and oup_sum in output
		let word_subseg_map = (0..n).into_iter().map(|i| //x_i
			cfg.idx_word_subseg + i).collect::<Vec<usize>>();
		let wit_map= (0..n).into_iter().map(|i| //w_i in subtbl ID
			cfg.idx_subtable_id + input_size + output_size + i)
			.collect::<Vec<usize>>();
		let inp_map = vec![cfg.idx_inp]; //inp_sum
		let oup_map = vec![cfg.idx_oup]; //oup_sum

		//3. construct the statment mapping to the problem statement
		// for the odd/even components depending on n
		// n elements x (mapped to word_subseg)
		// n elements of witness (sub-table IDs) - mapped to subtbl_id
		// 1 element of prev_sum mapped to inp_buf
		// 1 element of next_sum mapped to putput_buf 
		let sum_map = vec![
			word_subseg_map,
			wit_map,
			inp_map,
			oup_map
		].concat();

		//3. return
		let opt_joins = vec![];
		let ci_maps = vec![];
		(cfg.total_size(), cfg, vec![expand2(&sum_map)], opt_joins, ci_maps)
	}
}


fn main(){
	let mut t1 = Timer::new("main", 0);
	const H: bool = false;
	let lk = LK::new(vec![
		(F::from(0u32), F::from(0u32)), //0, null entry
		(F::from(1u32), F::from(0u32)), //First, we have 5 entries [0,4]
		(F::from(1u32), F::from(1u32)), 
		(F::from(2u32), F::from(0u32)), //real table to look for sum gadget
		(F::from(2u32), F::from(1u32)), 
		(F::from(2u32), F::from(2u32)), 
		(F::from(2u32), F::from(3u32)), 
		(F::from(2u32), F::from(4u32)), 
	]);
	let lkup = Rc::new(RefCell::new(lk.clone()));
	let (odd_mapper, even_mapper) =  
		(SumMapper::<Fr,LK>::new(true), SumMapper::<Fr,LK>::new(false));
	let _rng = rand::rngs::OsRng;
	let poseidon_config = poseidon_canonical_config::<Fr>();
	let lk_share_size = 4; //does not matter, will be adjusted in driver 
	let vec_circ = vec![
		vec![	SigmaIR1CS_Inst::<Fr,C1,CS1,LK,GM,H>::new_adv("oddsum".to_string(), poseidon_config.clone(), Rc::new(RefCell::new(odd_mapper)), false, lk_share_size, false, true).unwrap()],
		vec![SigmaIR1CS_Inst::<Fr,C1,CS1,LK,GM,H>::new_adv("evensum".to_string(), poseidon_config.clone(), Rc::new(RefCell::new(even_mapper)), false, lk_share_size, false, true).unwrap()]];
	let _n_circs = vec_circ.len();
	t1.prt("Step 0. setup sigma_ir1cs odd/eve sum instance");


	//2. create the driver
	// as lookup table 2 contains 0 to 4 will compute sum of
	// 1 + 2 +  4 + 2 + 2 = 11
	let _num_steps = 2; //will change
	let vec_words= vec![
		vec![Fr::from(1), Fr::from(2), Fr::from(100)],
		vec![Fr::from(4), Fr::from(2), From::from(2)]
	];
	let vec_word_fnames = vec![
		format!("a1.txt"),
		format!("a2.txt")
	];
	let vec_word_info = vec![WordInfo::dummy(); vec_words.len()];
	let sample_individual_prf = 1; //generate individual proof 1
	foldpot_main::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC,S,LK,GM,false>(lkup, vec_circ, vec_words, vec_word_info, sample_individual_prf, vec_word_fnames).expect("err foldpot");
}
