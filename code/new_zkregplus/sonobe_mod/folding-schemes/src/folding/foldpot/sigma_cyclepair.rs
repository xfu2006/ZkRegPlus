/* Created 10/02/2024, Revised 10/15/2024 */


use std::{rc::Rc, cell::RefCell,fmt::Debug};
use core::marker::PhantomData;
use crate::commitment::CommitmentScheme;
use crate::{
	folding::{
		foldpot::{
			sigma_ir1cs::{LookupTableTwoCol,SigmaIR1CS,SigmaIR1CS_Inst,SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig,StatementInst,StatementExtraInfo,StatementConfig,DummyNdAdvice,GadgetMapper, DummyCapacity,NdAdvice,Capacity,WordInfo},
			utils::{expand2},
			container_config::{ContainerConfig},
		},
	},
	Error
};
use ark_ec::{CurveGroup};
use ark_ff::{PrimeField};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_crypto_primitives::sponge::{
	constraints::CryptographicSpongeVar,
    poseidon::{PoseidonConfig, PoseidonSponge, constraints::PoseidonSpongeVar},
    Absorb, CryptographicSponge,
};
use ark_r1cs_std::{
	fields::{fp::FpVar},
	eq::EqGadget,
};


/// compute hash_chain using native Poseidon.
pub fn compute_hc<F:PrimeField + Absorb>(cfg: &PoseidonConfig<F>, hc: &F, 
	a: &Vec<F>)-> F
{
        let mut sponge = PoseidonSponge::<F>::new(cfg);
		sponge.absorb(hc);
		sponge.absorb(a);
		let res = sponge.squeeze_field_elements(1)[0];
		res
}

pub fn hash<F:PrimeField + Absorb>(cfg: &PoseidonConfig<F>, a: &Vec<F>)-> F
{
        let mut sponge = PoseidonSponge::<F>::new(cfg);
		sponge.absorb(a);
		let res = sponge.squeeze_field_elements(1)[0];
		res
}
pub fn hash_var<F:PrimeField + Absorb>(cfg: &PoseidonConfig<F>, a: &Vec<FpVar<F>>, cs: ConstraintSystemRef<F>)-> FpVar<F>
{
        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), cfg);
		sponge.absorb(a).expect("absort err");
		let res = sponge.squeeze_field_elements(1).unwrap()[0].clone();
		res
}


/// This works for Var in native arithmetics.
pub fn compute_hc_var<F:PrimeField>(
	cfg: &PoseidonConfig<F>,
	hc: &FpVar<F>,
	a: &Vec<FpVar<F>>, 
	cs: ConstraintSystemRef<F>)->FpVar<F>{

	let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &cfg);
	sponge.absorb(hc).expect("absorb hc err");
	sponge.absorb(a).expect("absorb a err");
	let res = sponge.squeeze_field_elements(1).unwrap()[0].clone();
	res
}


/// A gadget that computes the hashchain(a) and hashchain(b) for
/// a,b in e(a,b). Statement structure is shown below:
/// 
/// statement [gt1, a, b, gt2, hc(a)_in, hc(b)_in, hc(a)_out, hc(b)_out].
///
/// Where: gt2 = gt1 + e(a,b).
/// gt1 and gt2 are 12 Fq field elements each, a is 3 Fq, and b is 5 Fq
/// field elements. hashchain related are each 1Fr element.
///
/// hc(a) and hc(b) are hashchain(a) and hashcain(b),
/// the _in and _out will be mapped to input and output buffer
/// respectively. hashchain(a)_out = hash(hashchain(a)_in, a).
///
/// Each Fq is represented non-natively as 5 Fr (as each limb
/// is 55 bits). Note that the [gt1, a, b, gt2] part is actually
/// will be mapped to zi_part2.cyclepair part (which is 160 Fr elements)
///
/// Total: (12 + 3 + 5 + 12)*5 + 1 + 1 + 1 + 1 = 164 Fr elements.
/// Total cost: main circuit: 45k R1CS (because there are 164 Fr elements
/// to apply Poseidon). More compact to 2Fr for 1Fq, might cut the cost 
/// to 20k (but stay with it for saving implementation cost).
#[derive(Clone,Debug)]
pub struct FoldPairGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	pub poseidon_config: PoseidonConfig<F>
}

impl <F:PrimeField + Absorb> SigmaGadget<F> for FoldPairGadget<F>{
		fn get_name(&self)->&str{
			"FoldPairGadget"
		}

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

	/// return the estimated cost in number of constraints
	fn est_cost(&self)->usize{
		500
	}

	/// statment size: 164, and all messages are 0.
	fn get_msg_size(&self) -> (usize, usize, usize, usize){
		(164, 0, 0, 0)
	}

	fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) -> Vec<F>{
		vec![]
	}

	fn gen_msg3(&self, _stmt_vec: &Vec<F>, _stmt_idx: 
		&Vec<(usize,usize)>, 
		_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
		_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
		vec![]
	}

	/// leave the gt2 = gt1 + e(a,b) to cyclepair component.
	/// compute hc(a)_out = hash(hc(a)_in, a), and
	/// hc(b)_out = hash(hc(b)_in, b)
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig) 
		-> Result<(), SynthesisError>{
		let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
		//Given: statement [gt1,a,b,gt2,hc(a)_in,hc(b)_in,hc(a)_out,hc(b)_out].
		let idx_hc = 160;
		let hc_a_in = wtns.statement[stmt_idx[idx_hc].0].clone();
		let hc_b_in = wtns.statement[stmt_idx[idx_hc+1].0].clone();
		let hc_a_out = wtns.statement[stmt_idx[idx_hc+2].0].clone();
		let hc_b_out = wtns.statement[stmt_idx[idx_hc+3].0].clone();

		//a has 3 elements and starts at idx 12
		let a_idx = stmt_idx[12*5..12*5+3*5].to_vec();
		let a = a_idx.into_iter().map(|idx| 
			wtns.statement[idx.0].clone())
			.collect::<Vec<FpVar<F>>>();
		let b_idx = stmt_idx[15*5..20*5].to_vec();
		let b = b_idx.into_iter().map(|idx| 
			wtns.statement[idx.0].clone())
			.collect::<Vec<FpVar<F>>>();

		let computed_ha_out = compute_hc_var(&self.poseidon_config,
			&hc_a_in, &a, cs.clone());
		let computed_hb_out = compute_hc_var(&self.poseidon_config,
			&hc_b_in, &b, cs.clone());
		#[cfg(test)]{
		 use ark_r1cs_std::R1CSVar;
		 assert!(computed_ha_out.value().unwrap()==
		 	hc_a_out.value().unwrap());
		 assert!(computed_hb_out.value().unwrap()==
		 	hc_b_out.value().unwrap());
		}
		computed_ha_out.enforce_equal(&hc_a_out)?;
		computed_hb_out.enforce_equal(&hc_b_out)?;

		Ok(())
	}
}

/// FoldPairMapper consists of one gadget,
/// which computes the hash chain of a and b in e(a,b)
/// and relays the computation of pairing to CyclePair component.
/// We do not use lookup in FoldPair.
#[derive(Clone,Debug)]
pub struct FoldPairMapper<F:PrimeField, LK:LookupTableTwoCol<F>>{
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub poseidon_config: PoseidonConfig<F>
}

impl <F:PrimeField + Absorb, LK: LookupTableTwoCol<F>> 
GadgetMapper<F,LK> for FoldPairMapper<F, LK>{
	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, _advice: &Rc<dyn NdAdvice>){ 
		//not needed, handled by legacy code
	}

	fn get_capacity(&self) -> Rc<dyn Capacity>{
		Rc::new(DummyCapacity{word_seg_len: self.max_word_len()})
	}

	fn gen_nd_advice_no_limit(&self, word: &Vec<F>, _wi: &WordInfo,
		_prev_adv: Option<Rc<dyn NdAdvice>>) 
		-> Option<(Rc<dyn Capacity>, Rc<dyn NdAdvice>)>{
		if word.len()<=self.max_word_len(){
			Some((Rc::new(DummyCapacity{word_seg_len: word.len()}), 
				  Rc::new(DummyNdAdvice{}) ))
		}else{None }
	}


	fn get_name(&self) -> String { "FoldPairMapper".to_string() }

	/// expect [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out]
	/// total: 164 Fr elements
	fn max_word_len(&self)->usize{ 164 }

	fn get_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>{ 
		let f_gadget= FoldPairGadget::<F>{
			_f:PhantomData, 
			poseidon_config: self.poseidon_config.clone()
		};
		vec![Rc::new(RefCell::new(f_gadget))]
	}

	/// expecting full statement (constructed by the caller):
	/// [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out].
	/// maps them to:
	/// inp: gt1, hc_a_in, hc_b_in (size 62 = 12*5 + 1 + 1 Fr)
	/// oup: gt2, hc_a_out, hc_b_out (size 62 Fr)
	/// word: a and b (size 8*5 = 40 Fr)
	/// [gt1, a, b, gt2] 160Fr maps to zi_inp.cyclepair_input
	/// We do not rely on prev_stmt
	fn build_statement(&self, word: &Vec<F>, _prev_stmt: &Option<StatementInst<F,LK>>, _lkup: Rc<RefCell<LK>>, ea: &StatementExtraInfo<F>, _advice: Rc<dyn NdAdvice>, _lkup_size: usize, _b_dummy: bool) -> Result<StatementInst<F,LK>, Error>{
		//1. retrieve the information
		assert!(word.len()==164);
		let gt1 = word[0..12*5].to_vec();
		let a = word[12*5..15*5].to_vec();
		let b = word[15*5..20*5].to_vec();
		let gt2 = word[20*5..32*5].to_vec();
		let hc_a_in = word[160].clone(); 
		let hc_b_in = word[161].clone(); 
		let hc_a_out = word[162].clone(); 
		let hc_b_out = word[163].clone(); 
		let hash_a_b = hash(&self.poseidon_config, &vec![hc_a_out, hc_b_out]);
		let lkup_share_size = 0; // no need

		//2. build up the statement instance.
		let (zero, _one) = (F::zero(), F::one());
		let f_n_circ = ea.n_circ;
		let ncirc_minus_pci = f_n_circ-ea.pc_i;
		let failed_sigs = vec![F::zero()];
		let discharged_sigs = vec![F::zero()];
		let mtbl_sigs= vec![F::one()]; //coz 0 appeared once in failed sigs
		let stmt = StatementInst{
			pc_i: ea.pc_i,
			pc_i1: ea.pc_i1, 
			n_circ: f_n_circ,
			n_circ_minus_pc: ncirc_minus_pci,
			act_input_size: F::from(62u32),
			act_output_size: F::from(62u32),
			act_lookup_share_size: F::from(lkup_share_size as u32),
			act_word_subseg_size: F::from(164u32),
			word_id: ea.word_id,
			subseg_id: ea.subseg_id,
			total_word_len: ea.total_word_len,
			total_word_segs: ea.total_word_segs,
			total_words: ea.total_words,
			r_F: zero, //for debug
			batch_r: ea.batch_r,
			batch_v: ea.batch_v,
			r_all_words: ea.r_all_words,
			r_kzg_len: ea.r_kzg_len,
			r_vec_r: ea.r_vec_r,
			r_vec_v: ea.r_vec_v,
			r_word_i: ea.r_word_i,
			accumulated_word_len: ea.accumulated_word_len,
			f_result: hash_a_b,

			inp_buf: vec![gt1.clone(), vec![hc_a_in, hc_b_in]].concat(), 
			oup_buf: vec![gt2.clone(), vec![hc_a_out, hc_b_out]].concat(),  				word_subseg: vec![a, b].concat(), 
			data: vec![], //empty
			//subtable_id: vec![zero; 62 + 62 + 40 +  0],
			subtable_id: vec![zero; 62 + 62 +  0], //removed word
			col1_share: vec![zero; lkup_share_size],  
			col2_share: vec![zero; lkup_share_size], 
			m_share: vec![zero; lkup_share_size],
			failed_sigs,
			discharged_sigs,
			mtbl_sigs,

			_lk: PhantomData,
		};
			
		Ok(stmt)
	}

	fn gen_statement_structure(&self, _lookup_share_size: usize) -> 
		(usize, StatementConfig, Vec<Vec<(usize,usize)>>, Vec<((usize,usize),(usize,usize))>, Vec<usize>){
		//1. a sample statemnet structure
		let input_size = 62;
		let output_size = 62;
		let word_subseg_size = 40;
		let data_size = 0;
		let lkup_share_size = 0;
		let failed_sigs_size= 1; //empty 0
		let discharged_sigs_size= 1; //empty 0
		let b_cyclepair = true;
		let cfg = StatementConfig::new(
			input_size, output_size, word_subseg_size,
			data_size,lkup_share_size ,
			failed_sigs_size, discharged_sigs_size,
			b_cyclepair
		);

		//2. generate the result to return
		// problem statement the entire statement
		// [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out].
		// inp: gt1, hc_a_in, hc_b_in (size 62 = 12*5 + 1 + 1 Fr)
		// oup: gt2, hc_a_out, hc_b_out (size 62 Fr)
		// word: a and b (size 8*5 = 40 Fr)
		// [gt1, a, b, gt2] 160Fr maps to zi_inp.cyclepair_input

		let opt_join_constraints = vec![];
		let gt1_idx = (0..12*5).into_iter().map(
			|i| cfg.idx_inp + i).collect::<Vec<usize>>();
		let a_idx = (0..3*5).into_iter().map(
			|i| cfg.idx_word_subseg + i).collect::<Vec<usize>>();
		let b_idx = (0..5*5).into_iter().map(
			|i| cfg.idx_word_subseg + 3*5 + i).collect::<Vec<usize>>();
		let gt2_idx = (0..12*5).into_iter().map(
			|i| cfg.idx_oup + i).collect::<Vec<usize>>();
		let hc_a_in_idx = vec![cfg.idx_inp + 12*5];
		let hc_b_in_idx = vec![cfg.idx_inp + 12*5 + 1];
		let hc_a_out_idx = vec![cfg.idx_oup + 12*5];
		let hc_b_out_idx = vec![cfg.idx_oup + 12*5 + 1];
		let cyclepair_map = vec![gt1_idx.clone(), a_idx.clone(), 
			b_idx.clone(), gt2_idx.clone()].concat();
		let comp_map = vec![ gt1_idx, a_idx, b_idx, gt2_idx, hc_a_in_idx, hc_b_in_idx, hc_a_out_idx, hc_b_out_idx].concat();

		//3. return
		let stmt_len = cfg.total_size();
		(stmt_len, cfg, vec![expand2(&comp_map)], opt_join_constraints, cyclepair_map)
	}

}


/// create the sigma_ir1cs instance for folding qa-nizk for
/// k circuits. It will eventually perform 3k+1 folding steps.
/// Becaues for each circuit, need to reason about commitments of
/// W_i, E_i, and F_i.
pub fn create_sigma_fold_pair<F,C,CS,LK,const H: bool>(_k: usize, poseidon_config: PoseidonConfig<F>)-> SigmaIR1CS_Inst<F,C,CS,LK,FoldPairMapper<F,LK>,H> 
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		LK: LookupTableTwoCol<F> + 'static,
		F: PrimeField + Absorb,
{
	//1. create a sigma instance
	let mapper = FoldPairMapper::<F,LK>{_f: PhantomData, _lk: PhantomData, poseidon_config: poseidon_config.clone()};
	let lkup_share_size = 0;
	let mut sigma = SigmaIR1CS_Inst::<F, C, CS, LK, FoldPairMapper<F,LK>, H>::new_adv("paircycle".to_string(), poseidon_config.clone(), Rc::new(RefCell::new(mapper)), true, lkup_share_size, true).expect("error new sigma"); 
	//set true for b_cyclepair 

	//2. set up a dummy external input (witness) 
	// because hc and hc_out is not zero
	let hc = F::zero();
	let vec_a = vec![F::zero(); 3*5];
	let vec_b = vec![F::zero(); 5*5]; 
	let ha_out = compute_hc(&poseidon_config, &hc, &vec_a);
	let hb_out = compute_hc(&poseidon_config, &hc, &vec_b);
	let mut dummy_input = vec![F::zero(); 164];
	dummy_input[162] = ha_out;
	dummy_input[163] = hb_out;

	//3. build the dummy stmt
	// dummy extra info 
	let ea = StatementExtraInfo::<F>{
			total_words: F::one(),
			word_id: F::one(),
			subseg_id: F::one(),
			total_word_len: F::from(164u32),
			total_word_segs: F::one(),
			n_circ: F::one(),
			pc_i: F::zero(),
			pc_i1: F::zero(),
			act_word_subseg_size: F::from(164u32),
			batch_r: F::zero(),
			batch_v: F::zero(),
			r_all_words: F::zero(),
			r_kzg_len: F::zero(),
			r_vec_r: F::zero(),
			r_vec_v: F::zero(),
			r_word_i: F::zero(),
			accumulated_word_len: F::from(164u32),
		};
	let lk = LK::new(vec![
		(F::from(0u32), F::from(0u32)), //0, null entry
	]);
	let lkup = Rc::new(RefCell::new(lk));

	let dummy_adv = Rc::new(DummyNdAdvice{});
	let lkup_share_size = 4;
	let stmt_vec =sigma.get_mapper().borrow()
		.build_statement(&dummy_input, &None, lkup, &ea, dummy_adv, lkup_share_size, false).unwrap().to_vec();
	sigma.dummy_stmt = Some(stmt_vec);

	sigma
}


#[cfg(test)]
pub mod tests_sigma_cyclepair{
	use crate::{
		folding::{
			foldpot::{
				sigma_ir1cs::{LookupTableTwoCol_Inst,StatementExtraInfo,LookupTableTwoCol,ZiPartTwoInst,SigmaIR1CS,GadgetMapper,DummyNdAdvice}, 
				utils::{f1_to_f2_limbs},
				sigma_cyclepair::{create_sigma_fold_pair, compute_hc, compute_hc_var},
			},
		}
	};
    use ark_bn254::{Bn254, Fr, Fq, G1Projective as Bn254G1, G2Projective as Bn254G2};

	use ark_ec::{pairing::Pairing};
	use crate::{
		frontend::{FCircuit},
		commitment::{pedersen::Pedersen},
		transcript::poseidon::poseidon_canonical_config,
	};
	use ark_std::{UniformRand,test_rng,One,Zero};
	use ark_ff::{PrimeField,ToConstraintField};
	use std::{rc::{Rc}, cell::{RefCell}};
	use ark_relations::r1cs::{ConstraintSystem};
	use ark_r1cs_std::{
		R1CSVar,
		fields::{fp::FpVar},
		alloc::AllocVar, 
	};

	type F = Fr;
	type C = Bn254G1;
	type CS = Pedersen<C>;
	type LK = LookupTableTwoCol_Inst<F>;

	#[test]
	fn test_sha2(){
		//1. test the native version
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let mut rng = test_rng();
		let cs = ConstraintSystem::<Fr>::new_ref();
		let hc = Fr::rand(&mut rng); 
		let hc_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(hc)).unwrap();
		let a = vec![Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng)];
		let a_var = a.clone().into_iter().map(|v|
			FpVar::<Fr>::new_witness(cs.clone(), || Ok(v)).unwrap())
				.collect::<Vec<FpVar<Fr>>>();
		let res = compute_hc(&poseidon_config, &hc, &a);
		let res_var = compute_hc_var(&poseidon_config, &hc_var, &a_var, cs.clone());
		assert!(res_var.value().unwrap()==res);
	}


	#[test]
	fn test_sigma_cyclepair(){
        let cfg= poseidon_canonical_config::<Fr>();
		let sigma = create_sigma_fold_pair::<Fr,C,CS,LK,false>(5, cfg.clone());
		let mapper = sigma.get_mapper();
		let lk = LK::new(vec![
			(F::from(0u32), F::from(0u32)), //0, null entry
		]);
		let lkup = Rc::new(RefCell::new(lk));
		let ea = StatementExtraInfo::<F>{
				total_words: F::one(),
				word_id: F::one(),
				subseg_id: F::one(),
				total_word_len: F::from(164 as u32),
				total_word_segs: F::one(),
				n_circ: F::one(),
				pc_i: F::zero(),
				pc_i1: F::zero(),
				act_word_subseg_size: F::from(164u32),

				batch_r: F::zero(),
				batch_v: F::zero(),
				r_all_words: F::from(3u32),
				r_kzg_len: F::from(3u32),
				r_vec_r: F::from(3u32),
				r_vec_v: F::from(3u32),
				r_word_i: F::from(3u32),
				accumulated_word_len: F::from(164u32),
			};
		let mut rng = test_rng();
		let a =  Bn254G1::rand(&mut rng);
		let b =  Bn254G2::rand(&mut rng);

		let t1 =  Bn254G1::rand(&mut rng);
		let t2 =  Bn254G2::rand(&mut rng);
		let gt1 = Bn254::pairing(t1, t2).0;
		let gt2 = gt1 * Bn254::pairing(a,b).0;
		let vec_a_raw:Vec<Fq> = a.to_field_elements().unwrap(); 
		let vec_a = vec_a_raw.into_iter().map(|a|
			f1_to_f2_limbs::<Fq,Fr>(&a) ).collect::<Vec<Vec<Fr>>>()
			.concat();
		assert!(vec_a.len()==3*5);

		let vec_b_raw:Vec<Fq> = b.to_field_elements().unwrap(); 
		let vec_b = vec_b_raw.into_iter().map(|a|
			f1_to_f2_limbs::<Fq,Fr>(&a) ).collect::<Vec<Vec<Fr>>>()
			.concat();
		assert!(vec_b.len()==5*5);

		let vec_gt1_raw:Vec<Fq> = gt1.to_field_elements().unwrap(); 
		let vec_gt1 = vec_gt1_raw.into_iter().map(|a|
			f1_to_f2_limbs::<Fq,Fr>(&a) ).collect::<Vec<Vec<Fr>>>()
			.concat();
		assert!(vec_gt1.len()==12*5);

		let vec_gt2_raw:Vec<Fq> = gt2.to_field_elements().unwrap(); 
		let vec_gt2 = vec_gt2_raw.into_iter().map(|a|
			f1_to_f2_limbs::<Fq,Fr>(&a) ).collect::<Vec<Vec<Fr>>>()
			.concat();
		assert!(vec_gt2.len()==12*5);

		let hc_a_in = Fr::rand(&mut rng);
		let hc_b_in = Fr::rand(&mut rng);
		let hc_a_out = compute_hc::<Fr>(&cfg, &hc_a_in, &vec_a);
		let hc_b_out = compute_hc::<Fr>(&cfg, &hc_b_in, &vec_b);

		let inp = vec![vec_gt1, vec_a, vec_b, vec_gt2, 
			vec![hc_a_in, hc_b_in, hc_a_out, hc_b_out]].concat();
		let dummy_adv = Rc::new(DummyNdAdvice{});
		let lkup_share_size = 4;
		let stmt = mapper.borrow().build_statement(&inp, &None, lkup,&ea, dummy_adv, lkup_share_size, false).unwrap();

		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let b_full = true;
		let zi_part2_inst = ZiPartTwoInst::<F>::dummy(b_full, fq_bits);
		let precomputed_grp_cmf = None;
		let (wtns, wtns_cfg, _zipart2) = sigma.gen_witness(&stmt.to_vec(), 
			&zi_part2_inst, precomputed_grp_cmf);

		let cs = ConstraintSystem::<F>::new_ref();
		let external_inputs = wtns.to_vec_fp_var(cs.clone(), &wtns_cfg);
		let zero = Fr::zero();
		let num_words = 1;
		let z0_part2 = ZiPartTwoInst::<Fr>::new(zero, zero, 
			&cfg, b_full, fq_bits, num_words);
		let z0_part2_hash = z0_part2.hash(&cfg);
		let z_0 = vec![zero, z0_part2_hash];
		let z_0_var = z_0.into_iter().map(|z| FpVar::new_witness(cs.clone(),
			|| Ok(z)).unwrap() ).collect::<Vec<FpVar<Fr>>>();
		sigma.generate_step_constraints(cs.clone(), 0, z_0_var, 
			external_inputs).expect("gen step err");

		assert!(cs.is_satisfied().unwrap());
	}
}
