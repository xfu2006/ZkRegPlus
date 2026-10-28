use std::{sync::{Arc, Mutex}, fmt::Debug};
/* Created 10/02/2024, Revised 10/15/2024 */


use core::marker::PhantomData;
use crate::commitment::CommitmentScheme;
use crate::{
	folding::{
		foldpot::{
			sigma_ir1cs::{LookupTableTwoCol,SigmaIR1CS,SigmaIR1CS_Inst,SigmaGadget,WitnessSigmaIR1CSVar,WitnessSigmaIR1CSConfig,StatementInst,StatementExtraInfo,StatementConfig,DummyNdAdvice,GadgetMapper, DummyCapacity,NdAdvice,Capacity,WordInfo},
			utils::{expand2, B_DEBUG},
			container_config::{ContainerConfig,ColEle},
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
/// is 55 bits). Note that the [gt1, a, b, gt2] part (160 Fr elements)
/// is the x of the folded CyclePair instance (T931, circuits_super.rs H4)
///
/// Total: (12 + 3 + 5 + 12)*5 + 1 + 1 + 1 + 1 = 164 Fr elements.
/// Total cost: main circuit: 45k R1CS (because there are 164 Fr elements
/// to apply Poseidon). More compact to 2Fr for 1Fq, might cut the cost 
/// to 20k (but stay with it for saving implementation cost).
#[derive(Clone,Debug)]
pub struct FoldPairGadget<F:PrimeField>{ 
	_f: PhantomData<F>,
	pub poseidon_config: PoseidonConfig<F>,
	pub job_id: usize,
}

impl <F:PrimeField + Absorb> SigmaGadget<F> for FoldPairGadget<F>{
		fn get_name(&self)->&str{
			"FoldPairGadget"
		}

	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
	}
	fn get_job_id(&self)->usize{
		self.job_id
	}

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach
	fn set_container_cfg(&mut self, _cfgs_context: Arc<Vec<ContainerConfig>>, _idx: usize){
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
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
		_word_id: FpVar<F>, _subsig_id: FpVar<F>,
		_virt_vals: &mut Vec<FpVar<F>>)
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
		if B_DEBUG {
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
	pub poseidon_config: PoseidonConfig<F>,
	pub job_id: usize,
}

impl <F:PrimeField + Absorb, LK: LookupTableTwoCol<F>>
GadgetMapper<F,LK> for FoldPairMapper<F, LK>{
	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
	}
	fn get_job_id(&self)->usize{
		self.job_id
	}

	/// use advice to generate container config and set it for

	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, _advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		//not needed, handled by legacy code
	}

	fn get_capacity(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(DummyCapacity{word_seg_len: self.max_word_len()})
	}

	fn gen_nd_advice(&self, word: &Vec<F>, _wi: &WordInfo,
		_prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, _seg_id: usize, _job_id: usize) 
		-> Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
		if word.len()<=self.max_word_len(){
			Ok( Arc::new(DummyNdAdvice{}) )
		}else{
			Err(Error::CapErr(vec![(format!("max_word_len"), word.len())]))
		}
	}


	fn get_name(&self) -> String { "FoldPairMapper".to_string() }

	/// expect [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out]
	/// total: 164 Fr elements
	fn max_word_len(&self)->usize{ 164 }

	fn get_gadgets(&self) -> Vec<Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>>{ 
		let f_gadget= FoldPairGadget::<F>{
			_f:PhantomData, 
			poseidon_config: self.poseidon_config.clone(),
			job_id: self.job_id
		};
		vec![Arc::new(Mutex::new(f_gadget))]
	}

	/// expecting full statement (constructed by the caller):
	/// [gt1, a, b, gt2, hc_a_in, ha_b_in, hc_a_out, hc_b_out].
	/// maps them to:
	/// inp: gt1, hc_a_in, hc_b_in (size 62 = 12*5 + 1 + 1 Fr)
	/// oup: gt2, hc_a_out, hc_b_out (size 62 Fr)
	/// word: a and b (size 8*5 = 40 Fr)
	/// [gt1, a, b, gt2] 160Fr is the folded CyclePair x (T931)
	/// We do not rely on prev_stmt
	fn build_statement(&self, word: &Vec<F>, _prev_stmt: &Option<StatementInst<F,LK>>, _lkup: Arc<LK>, ea: &StatementExtraInfo<F>, _advice: Arc<dyn NdAdvice + Send + Sync>, _lkup_size: usize, _b_dummy: bool, _job_id: usize) -> Result<StatementInst<F,LK>, Error>{
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
			r_word_i2: ea.r_word_i2,
			r_all_words2: ea.r_all_words2,
			r_kzg_len2: ea.r_kzg_len2,
			r_vec_r2: ea.r_vec_r2,
			r_vec_v2: ea.r_vec_v2,
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
		// [gt1, a, b, gt2] 160Fr is the folded CyclePair x (T931)

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
		let comp_map = vec![ gt1_idx, a_idx, b_idx, gt2_idx, hc_a_in_idx, hc_b_in_idx, hc_a_out_idx, hc_b_out_idx].concat();
		//T931 D2: the whole row, hc indices included (164). Builders of
		//the 160-limb CyclePair x take [..160].
		let cyclepair_map = comp_map.clone();

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
		F: PrimeField + Absorb + ColEle,
{
	//1. create a sigma instance
	let mapper = FoldPairMapper::<F,LK>{_f: PhantomData, _lk: PhantomData, 
		poseidon_config: poseidon_config.clone(), job_id: 0};
	let lkup_share_size = 0;
	let b_check_lkup = true;
	let mut sigma = SigmaIR1CS_Inst::<F, C, CS, LK, FoldPairMapper<F,LK>, H>::new_adv("paircycle".to_string(), poseidon_config.clone(), Arc::new(Mutex::new(mapper)), true, lkup_share_size, true, b_check_lkup).expect("error new sigma"); 
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
			r_word_i2: F::zero(),
			r_all_words2: F::zero(),
			r_kzg_len2: F::zero(),
			r_vec_r2: F::zero(),
			r_vec_v2: F::zero(),
			accumulated_word_len: F::from(164u32),
		};
	let lk = LK::new(vec![
		(F::from(0u32), F::from(0u32)), //0, null entry
	]);
	let lkup = Arc::new(lk);

	let dummy_adv = Arc::new(DummyNdAdvice{});
	let lkup_share_size = 4;
	let stmt_vec =sigma.get_mapper().lock().unwrap()
		.build_statement(&dummy_input, &None, lkup, &ea, dummy_adv, lkup_share_size, false, 0).unwrap().to_vec();
	sigma.dummy_stmt = Some(stmt_vec);

	sigma
}


#[cfg(test)]
pub mod tests_sigma_cyclepair{
	use std::sync::Arc;
	use crate::{
		folding::{
			foldpot::{
				sigma_ir1cs::{LookupTableTwoCol_Inst,StatementExtraInfo,LookupTableTwoCol,ZiPartTwoInst,SigmaIR1CS,GadgetMapper,DummyNdAdvice}, 
				utils::{f1_to_f2_limbs},
				sigma_cyclepair::{create_sigma_fold_pair, compute_hc, compute_hc_var, FoldPairMapper},
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
	//use std::{rc::{Rc}, cell::{RefCell}};
	use ark_relations::r1cs::{ConstraintSystem, ConstraintMatrices};
	use core::marker::PhantomData;
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
		let lkup = Arc::new(lk);
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
				r_word_i2: F::from(3u32),
				r_all_words2: F::from(3u32),
				r_kzg_len2: F::from(3u32),
				r_vec_r2: F::from(3u32),
				r_vec_v2: F::from(3u32),
				accumulated_word_len: F::from(164u32),
			};
		let mut rng = test_rng();
		let a =  Bn254G1::rand(&mut rng);
		let b =  Bn254G2::rand(&mut rng);

		//T931: z_0 pins row 0 to gt1 = [0]_T and hc_in = 0
		let gt1 = Fq12::one();
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

		let (hc_a_in, hc_b_in) = (Fr::zero(), Fr::zero());
		let hc_a_out = compute_hc::<Fr>(&cfg, &hc_a_in, &vec_a);
		let hc_b_out = compute_hc::<Fr>(&cfg, &hc_b_in, &vec_b);

		let inp = vec![vec_gt1, vec_a, vec_b, vec_gt2, 
			vec![hc_a_in, hc_b_in, hc_a_out, hc_b_out]].concat();
		let dummy_adv = Arc::new(DummyNdAdvice{});
		let lkup_share_size = 4;
		let stmt = mapper.lock().unwrap().build_statement(&inp, &None, lkup,&ea, dummy_adv, lkup_share_size, false, 0).unwrap();

		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let b_full = true;
		let zero = Fr::zero();
		let num_words = 1;
		//S104: the witness input state and z_0[1] must be the SAME
		//state -- the step circuit now enforces
		//hash(input state) == z_i[1]. This test used ::dummy here
		//(total_words=0) against a z_0 built with num_words=1 and still
		//passed; that mismatch was the standing falsifier for S104.
		let z0_part2 = ZiPartTwoInst::<Fr>::new(zero, zero,
			&cfg, b_full, fq_bits, num_words);
		let zi_part2_inst = z0_part2.clone();
		let precomputed_grp_cmf = None;
		let (wtns, wtns_cfg, _zipart2) = sigma.gen_witness(&stmt.to_vec(),
			&zi_part2_inst, precomputed_grp_cmf);

		let cs = ConstraintSystem::<F>::new_ref();
		let external_inputs = wtns.to_vec_fp_var(cs.clone(), &wtns_cfg);
		let z0_part2_hash = z0_part2.hash(&cfg);
		//S107: z is now 6 wide (2 + cmF limbs x4).
		let z_0 = [vec![zero, z0_part2_hash],
			vec![zero; 4]].concat();
		let z_0_var = z_0.into_iter().map(|z| FpVar::new_witness(cs.clone(),
			|| Ok(z)).unwrap() ).collect::<Vec<FpVar<Fr>>>();
		sigma.generate_step_constraints(cs.clone(), 0, z_0_var, 
			external_inputs).expect("gen step err");

		assert!(cs.is_satisfied().unwrap());
	}

	// ---------------------------------------------------------------
	// T931 (TASK_T931 s7). Stage-2 row chaining on the sigma step. Arms
	// differ in witness values only, so their rows compare.
	// ---------------------------------------------------------------
	pub type Fq12 = <Bn254 as Pairing>::TargetField;

	/// T931: limbs of a pairing-side element, laid out as the
	/// mod_super.rs row encoder does (to_field_elements, f1_to_f2_limbs).
	pub fn t931_enc<T: ToConstraintField<Fq>>(x: &T) -> Vec<Fr>{
		x.to_field_elements().unwrap().iter()
			.flat_map(|f| f1_to_f2_limbs::<Fq, Fr>(f)).collect()
	}

	/// T931: g_k = sum_t 2^(55t) limb[4k+t], computed independently.
	pub fn t931_pack4(l: &[Fr]) -> Vec<Fr>{
		l.chunks(4).map(|c| c.iter().rev()
			.fold(Fr::zero(), |s, x| s * Fr::from(1u64 << 55) + x)).collect()
	}

	/// T931: re-run both hash chains over rows, from `hc`.
	pub fn t931_rechain(rows: &mut [Vec<Fr>], hc: (Fr, Fr)){
		let cfg = poseidon_canonical_config::<Fr>();
		let (mut ha, mut hb) = hc;
		for r in rows.iter_mut(){
			(r[160], r[161]) = (ha, hb);
			ha = compute_hc(&cfg, &ha, &r[60..75].to_vec());
			hb = compute_hc(&cfg, &hb, &r[75..100].to_vec());
			(r[162], r[163]) = (ha, hb);
		}
	}

	/// T931: honest row [gt1, a, b, gt1 e(a,b), hc_in (2), hc_out (2)].
	pub fn t931_row(gt1: Fq12, a: Bn254G1, b: Bn254G2, hc: (Fr, Fr)) -> Vec<Fr>{
		let mut r = [t931_enc(&gt1), t931_enc(&a), t931_enc(&b),
			t931_enc(&(gt1 * Bn254::pairing(a, b).0)), vec![Fr::zero(); 4]].concat();
		t931_rechain(std::slice::from_mut(&mut r), hc);
		r
	}

	/// T931: statement of row w (1-based) of n, fields as driver.rs pass_all.
	pub fn t931_stmt(row: &Vec<Fr>, w: usize, n: usize) -> Vec<Fr>{
		let (zero, one, len) = (Fr::zero(), Fr::one(), Fr::from(164u32));
		let ea = StatementExtraInfo::<Fr>{ total_words: Fr::from(n as u32),
			word_id: Fr::from(w as u32), subseg_id: one, total_word_len: len,
			total_word_segs: one, n_circ: one, pc_i: zero, pc_i1: zero,
			act_word_subseg_size: len, batch_r: zero, batch_v: zero,
			r_all_words: zero, r_kzg_len: zero, r_vec_r: zero, r_vec_v: zero,
			r_word_i: zero, r_word_i2: zero, r_all_words2: zero, r_kzg_len2: zero,
			r_vec_r2: zero, r_vec_v2: zero, accumulated_word_len: len };
		let m = FoldPairMapper::<Fr, LK>{_f: PhantomData, _lk: PhantomData,
			poseidon_config: poseidon_canonical_config::<Fr>(), job_id: 0};
		m.build_statement(row, &None, Arc::new(LK::new(vec![])), &ea,
			Arc::new(DummyNdAdvice{}), 0, false, 0).unwrap().to_vec()
	}

	/// T931: rows of m that z leaves unsatisfied.
	pub fn t931_unsat(m: &ConstraintMatrices<Fr>, z: &[Fr]) -> Vec<usize>{
		let dot = |r: &Vec<(Fr, usize)>| r.iter().map(|(c, i)| *c * z[*i]).sum::<Fr>();
		(0..m.num_constraints).filter(|&r| dot(&m.a[r]) * dot(&m.b[r]) != dot(&m.c[r]))
			.collect()
	}

	/// T931: Stage-2 sigma step 0 on (row, input state zi, z_i[1]). Returns
	/// (matrices, z, native output state, in-circuit z_{i+1}[1]).
	pub fn t931_step(row: &Vec<Fr>, zi: &ZiPartTwoInst<Fr>, z1: Fr)
		-> (ConstraintMatrices<Fr>, Vec<Fr>, ZiPartTwoInst<Fr>, Fr){
		let sigma = create_sigma_fold_pair::<Fr,C,CS,LK,false>(1,
			poseidon_canonical_config::<Fr>());
		let (wtns, wcfg, out) = sigma.gen_witness(&t931_stmt(row, 1, 1), zi, None);
		let cs = ConstraintSystem::<Fr>::new_ref();
		let ext = wtns.to_vec_fp_var(cs.clone(), &wcfg);
		let z_i = [vec![Fr::zero(), z1], vec![Fr::zero(); 4]].concat().into_iter()
			.map(|v| FpVar::new_witness(cs.clone(), || Ok(v)).unwrap()).collect();
		let h = sigma.generate_step_constraints(cs.clone(), 0, z_i, ext)
			.expect("gen step err")[1].value().unwrap();
		cs.finalize();
		let m = cs.to_matrices().unwrap();
		let g = cs.borrow().unwrap();
		let z = [g.instance_assignment.clone(), g.witness_assignment.clone()].concat();
		(m, z, out, h)
	}

	/// T931 T-10 (N3, P1) and the H3 export on the Stage-2 sigma step.
	/// The input state is bound whole (no free split digest) and chained
	/// to the row: gt1 == z_i.g, hc_in == z_i.hc_out. z_{i+1} carries the
	/// row's hc_out and pack4(gt2). Baseline: every tampered arm is SAT.
	#[test]
	fn test_t931_t10_step_chain(){
		let (cfg, fq_bits) = (poseidon_canonical_config::<Fr>(), Fq::MODULUS_BIT_SIZE as usize);
		let (zero, mut rng) = (Fr::zero(), test_rng());
		let (a, b) = (Bn254G1::rand(&mut rng), Bn254G2::rand(&mut rng));
		let row = t931_row(Fq12::one(), a, b, (zero, zero));
		let z0 = ZiPartTwoInst::<Fr>::new(zero, zero, &cfg, true, fq_bits, 1);
		let (m, z, out, h_out) = t931_step(&row, &z0, z0.hash(&cfg));
		println!("T931 T-13 Stage-2 sigma step: cs {}, witness {}",
			m.num_constraints, m.num_witness_variables);
		assert!(t931_unsat(&m, &z).is_empty(), "T931: honest Stage-2 step 0 not SAT");
		//H3 export: z_{i+1} = [21 fixed, hc_a_out, hc_b_out, pack4(gt2)]
		let v = out.to_vec();
		let exp = [row[162..164].to_vec(), t931_pack4(&row[100..160])].concat();
		let b_exp = v.len() == 38 && v[21..] == exp[..] && h_out == out.hash(&cfg);
		//carried arms: z_i's entry len-k moved, digest consistent
		//(k = 17 hc_a_out, 16 hc_b_out, 15 g[0])
		let carried = |k: usize| {
			let mut v = z0.to_vec();
			let j = v.len() - k;
			v[j] += Fr::one();
			let zi = ZiPartTwoInst::<Fr>::from_vec(&v, fq_bits);
			let (m2, z2, _, _) = t931_step(&row, &zi, zi.hash(&cfg));
			assert_eq!(m2.num_constraints, m.num_constraints, "T931: arms not shape-identical");
			(t931_unsat(&m2, &z2).len(), z2)
		};
		let ((n_ha, _), (n_hb, _), (n_g, z_g)) = (carried(17), carried(16), carried(15));
		//row side: gt1 != z_i.g with z_0 honest
		let (m3, z3, _, _) = t931_step(&t931_row(Bn254::pairing(a, b).0, a, b,
			(zero, zero)), &z0, z0.hash(&cfg));
		let n_row = t931_unsat(&m3, &z3).len();
		//stale digest: the honest assignment with only the carried g[0]
		//column moved (the first column where the g arm differs)
		let c = (0..z.len()).find(|&i| z[i] != z_g[i]).unwrap();
		let mut z4 = z.clone();
		z4[c] = z_g[c];
		let n_stale = t931_unsat(&m, &z4).len();
		println!("T931 T-10: export {} | unsat rows: hc_a {} hc_b {} g {} row gt1 {} \
			stale digest (col {}) {}", b_exp, n_ha, n_hb, n_g, n_row, c, n_stale);
		assert!(b_exp, "T931 H3: z_(i+1) does not carry (hc_out, pack4(gt2)), len {}", v.len());
		assert!(n_ha > 0 && n_hb > 0, "T931 P1: hc_in != z_i.hc_out accepted");
		assert!(n_g > 0 && n_row > 0, "T931 P1: gt1 != z_i.g accepted");
		//P1 alone rejects the moved g[0] (n_g rows), so the digest must add rows
		assert!(n_stale > n_g, "T931 N3: input state column unbound by the digest");
	}
}
