use std::{sync::{Arc, Mutex}, fmt::{Debug,Formatter}};
/* 
	Created 08/27/2024 
	Modified 12/25/2024: added snark_rand_input structure
	Modified 01/08/2025: added main workflow foldpot_main
	Modified 11/24/2025: merge pass1 to pass3 to save memory
	Modified 02/22/2026: further improve memory consumption
*/

extern crate utils;
use utils::{logger::{log, log_perf, ERR, LOG1,LOG_LEVEL,LOG2}, timer::Timer as GTimer};
use std::{
    //process::{Stdio,Command},
    //fs::{read_to_string,OpenOptions,remove_file,File,metadata},
	fs::{metadata,File,OpenOptions,remove_file},
    path::{Path},
    io::{Write,Read},
	collections::{HashMap},
	time::Instant,
};
use ark_std::{Zero,One,UniformRand};
use ark_std::{rand};
use ark_std::{rand::{RngCore,CryptoRng}};
use ark_r1cs_std::{
    prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
    ToConstraintFieldGadget,
};
use ark_ec::{Group, CurveGroup,
	pairing::{Pairing},
	short_weierstrass::SWCurveConfig
};
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig},
    Absorb,
};
use crate::transcript::poseidon::poseidon_canonical_config;
use ark_ff::{PrimeField, Field,ToConstraintField};
use crate::folding::foldpot::from_field::{AffineFromField};
use crate::{
	Error,
	folding::{
		circuits::{CF1, CF2, CF3},
		foldpot::{
			container_config::{ColEle},
			qa_nizk::{QaNizkProof},
			utils::{Timer,get_mem_usage,get_mem_usage_mb,format_bytes,B_DEBUG},
			circuits_super::{field_to_usize},
			mod_super::{PreprocessorParamFoldPotSuper,FoldPotSuper,
				compute_step_hc_cmF_adv},
			sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,StatementExtraInfo,GadgetMapper,Capacity,NdAdvice,WordInfo},
			sigma_cyclepair::{create_sigma_fold_pair,FoldPairMapper},
			//decider_eth_super::{DeciderFoldPotSuper},
			decider_eth_circuit_super::{CyclePairCircuit, CircPubInput, MainDeciderCircuit},
			batch_proc::{BatchProcessorProverParams,BatchProcessorVerifierParams,BatchProcessor,BatchClaim,BatchProof,IndividualClaim,IndividualProof,SnarkAdvice,SnarkRandInput}
		}
	},
};
use core::marker::PhantomData;
use crate::frontend::FCircuit;
use crate::{FoldingScheme};
use rayon::prelude::*;

/// Struct to encapsulate a folding job (one list-file)
pub struct FoldPotJob<F: PrimeField> {
	pub vec_words: Vec<Vec<F>>,
	pub vec_word_info: Vec<WordInfo>,
	pub vec_word_fnames: Vec<String>,
	pub idx_individual_prf: usize,
}

//pub use super::decider_eth_circuit::{DeciderEthCircuit, KZGChallengesGadget};
use ark_snark::SNARK;
use crate::commitment::{
    kzg::{Proof as KZGProof },
    pedersen::Params as PedersenParams,
    CommitmentScheme,
};


/// This file defines the FoldPot Driver. All invocation of fold pot
/// prover needs to go through the Driver. It works in two phases.
/// (1) generate the commitments (to words, word fragment, and hashchain
/// that are used as Fiat-Shamir), (2) the two-stage proof, which consists
/// of a batch proof for all, and individual proof for each. Considering
/// that input files are huge, it works in streaming mode to save memory.
/// Here we fix the curve and commitment schemes used.
#[derive(Clone)]
pub struct Driver<'c, E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool> 
where
//    C1: CurveGroup,
 //   C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1> + Send + Sync,
	LK: LookupTableTwoCol<C1::ScalarField> + Send + Sync,
    // CS1E is a KZG commitment, where challenge is C1::Fr elem
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	<CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync,
    CS1: CommitmentScheme<C1,H, ProverParams = PedersenParams<C1>>,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2,H, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    //C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{

	/// Poseidon Config
	poseidon_config: PoseidonConfig<C1::ScalarField>,
	/// list of circuits (ordered by preference in descending order)
	layered_circs: Vec<Vec<FC>>,
	/// flattened circuits
	circuits: Vec<FC>,
	/// lookup table
	lkup: Arc<LK>,
	/// the prover/verifier parameters
	pub nova_param: (<FoldPotSuper<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H> as FoldingScheme<C1,C2,FC>>::ProverParam, <FoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK,GM, H> as FoldingScheme<C1,C2,FC>>::VerifierParam),

	/// the decidider parameters
	/*
	pub decider_param: 
		(<DeciderFoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, S, FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>,LK> as DeciderTrait<C1,C2,FC,FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>>>::ProverParam,
		<DeciderFoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, S, FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>,LK> as DeciderTrait<C1,C2,FC,FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>>>::VerifierParam),
	*/

	pub batch_pk: Option<BatchProcessorProverParams<'c,E>>,
	pub batch_vk: Option<BatchProcessorVerifierParams<'c,E,CS1E,H>>,

	/// when true, the cyclepair instance is supported
	pub b_full_mode: bool,

	/// phantom data
    _gc1: PhantomData<fn() -> GC1>,
    _c2: PhantomData<fn() -> C2>,
    _gc2: PhantomData<fn() -> GC2>,
    _cs2: PhantomData<fn() -> CS2>,
    _s: PhantomData<fn() -> S>,
}



impl <'c, E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool> Debug for
Driver <'c, E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, H> 
where
//    C1: CurveGroup,
 //   C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1> + Send + Sync,
	LK: LookupTableTwoCol<C1::ScalarField> + Send + Sync,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
	/*
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	<CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync,
	*/
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS1: CommitmentScheme<C1, H, ProverParams = PedersenParams<C1>>,
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	<CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync,
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    //C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{
	fn fmt(&self, f: &mut Formatter<'_>)-> std::fmt::Result{
		f.debug_struct("Driver")
			.finish()
	}
}

impl <'c, E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug+Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool> Driver <'c, E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, H> 
where
    //C1: CurveGroup,
    //C2: CurveGroup,
	<E as Pairing>::ScalarField: ColEle,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1> + Send + Sync,
	LK: LookupTableTwoCol<C1::ScalarField> + Send + Sync,
    CS1: CommitmentScheme<C1,H, ProverParams = PedersenParams<C1>>,
    CS1E: CommitmentScheme<
        C1,H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	<CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    //C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    //C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{

	/// create a new instance of driver. Need the list of F_circuits.
	/// b_full_mode indicates whether to support cycle pair.
	/// max_total_n is the combined length of all words, and 
	/// n_words is the number of words.
	///
	/// NOTE: we require the F_circuits to be classified
	/// by priority (preferred first). Each vec should have
	/// EXACTLY the same type of circuits that can handle
	/// EXACTLY the same max_word_len, also ordered with preferred first (
	///  low cost)
	pub fn new(poseidon_config: PoseidonConfig<C1::ScalarField>,
	  lkup_inp: Arc<LK>,
	  F_circuits: Vec<Vec<FC>>, 
	  mut rng: impl RngCore +  CryptoRng, 
	  b_full_mode: bool,
	  max_total_n: usize,
	  n_words: usize,
	  )->Self{
		let log_level = LOG2;
		let b_perf = LOG_LEVEL >= log_level;
		let mut gt1 = GTimer::new();
	  	//1. set up the parameters
        let _start = Instant::now();
		let _b_debug = false;
		let layered_circuits = F_circuits;
		let circuits = layered_circuits.concat(); 
		let size_F = circuits.iter().map(|f| f.get_size_f())
			.collect::<Vec<usize>>();
		if b_perf{
			log_perf(0, log_level, &format!("Driver New: Step 1: foldpot keys"), 
				&mut gt1);
			for i in 0..size_F.len(){
				log(0, log_level, &format!(" -- circ {} size: {}", i, size_F[i]));
			}
		}
        let prep_param =
            PreprocessorParamFoldPotSuper::<C1, C2, 
				FC, CS1, CS2, LK, GM, H>
			::new(
				poseidon_config.clone(), 
				circuits.clone(),
				lkup_inp.clone(),
				size_F.clone(),
				b_full_mode
			);
		log_perf(0, log_level, &format!(
			"Driver New: Step 2: foldpot params.", ), &mut gt1);


        let nova_params = FoldPotSuper::<
			E, P, C2G2,
			C1,
			GC1,
			C2,
			GC2,
			FC,
            CS1,
            CS2,
			CS1E,
			LK,
			GM,
            H,
        >::preprocess(&mut rng, &prep_param)
        .unwrap();
		log_perf(0, log_level, &format!(
			"Driver New: Step 3: preprocess keys"), 
			&mut gt1);

		//2. create adummy FoldPotSuper instance
		assert!(circuits.len() == size_F.len());
		assert!(circuits.len() == prep_param.vec_pp.len());
		let _pc_0_val = 0usize;
		let hash_cmF = C1::ScalarField::zero();
		let ch = C1::ScalarField::zero();
		let rc = C1::ScalarField::zero();

		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(ch, rc, &poseidon_config, b_full_mode, fq_bits, n_words);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);
        let _z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
		log_perf(0, log_level, &format!(
			"Driver New: Step 3.5: create default z0"), 
			&mut gt1);

		//4. set up the batch processor if it is NOT full mode (1st stage)
		let max_w_lk = if max_total_n > lkup_inp.get_size() 
			{max_total_n+1} else {lkup_inp.get_size()+1};
		let batch_param = BatchProcessor::<E,LK,S,CS1E,H>
				::setup(&mut rng, max_w_lk, n_words, poseidon_config.clone(), 0); 

		log_perf(0, log_level, &format!(
			"Driver New: Step 4: batch param"), 
			&mut gt1);

		Self{
			lkup: lkup_inp.clone(),
			layered_circs: layered_circuits,
			circuits: circuits,
			poseidon_config: poseidon_config,
			//prep_param: prep_param,
			nova_param: nova_params, 
			//decider_param: decider_params,
			batch_pk: Some(batch_param.0),
			batch_vk: Some(batch_param.1),

			_gc1: PhantomData,
			_c2: PhantomData,
			_gc2: PhantomData,
			_cs2: PhantomData,
			_s: PhantomData,

			b_full_mode: b_full_mode, }
	}

	/// generate the advice using the circuit at layer_i
	/// return if success (num_steps, vec<size of word seg>, vec<PCI>
	/// 	vec<capacity needed>, vec<advice>)
	fn gen_nd_advice_at_layer(&self, job_id: usize, layer_i: usize,
		_log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
		//let mut gt1 = GTimer::new();
		let mut vec_pci = vec![];
		let mut vec_size = vec![];
		let mut vec_cap = vec![];
		let mut vec_adv:Vec<Arc<dyn NdAdvice + Send + Sync>> = vec![];
		let layer = &self.layered_circs[layer_i]; 
		let circ = &layer[0];
		let max_wlen = circ.get_mapper().lock().unwrap().max_word_len();
		let wlen = word.len();
		let num_segs = if wlen % max_wlen==0{wlen/max_wlen} 
			else {wlen/max_wlen+1};
		let pci = layer_i; //because every layer has only one circ
		let cap = circ.get_mapper().lock().unwrap().get_capacity();
		let mut prev_adv = None;
		for i in 0..num_segs{
			let start = i*max_wlen;
			let end = if (i+1)*max_wlen>wlen {wlen} else {(i+1)*max_wlen};
			let seg = word[start..end].to_vec();
			let advice = circ.get_mapper().lock().unwrap()
				.gen_nd_advice(&seg, &word_info, prev_adv, i, job_id)?;
			vec_pci.push(pci);
			vec_size.push(end-start);
			vec_cap.push(cap.clone());
			prev_adv = Some(advice.clone());
			if b_save_advice{ vec_adv.push(advice); }
		}
		Ok ((num_segs, vec_size, vec_pci, vec_cap, vec_adv))
	}

	/// find a working layer that would successfully generate
	/// return if success (LAYER_ID, num_steps, vec<size of word seg>, vec<PCI>
	/// 	vec<capacity needed>, vec<advice>)
	///
	/// This function uses heurstics here to find a working layer for
	/// the word as fast as possible. The idea is to take a "mid" seg
	/// of the word and use it to binary search a working layer.
	/// if the word itself is very short or very long, just 
	/// return the max ID (as this fiding_working_layer step is
	/// not going to save much anyway)
	fn find_working_layer_for_wd(&self, job_id: usize, log_level: usize, b_save_advice: bool, word: &Vec<CF1<C1>>, word_info: &WordInfo)-> Result<(usize, usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
		let full_len = word.len();
		let max_wlen = self.layered_circs[0][0].get_mapper().lock().unwrap()
			.max_word_len();
		let long_bar = 1024 * 1024 / 31 * 4; //4MB of data
		let max_layer_id = self.layered_circs.len()-1;

		//1. compute guessed_layer
		let guessed_layer = if full_len < 4 * max_wlen || full_len > long_bar{
			max_layer_id
		}else{//sample a segment and binary search (on the seg
			//but not the entire word to save cost
			let seg = word[full_len/2..full_len/2+max_wlen].to_vec();
			let min_layer = 0;
			let res = self.gen_nd_advice_at_layer(job_id, max_layer_id,
				log_level, b_save_advice, &seg, word_info)?;
			let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) = res;
			let (best_layer, _num_segs, _vec_seg_size, 
				_vec_pci, _vec_cap, _vec_adv) = self.bin_search_best_layer(
					job_id, log_level, b_save_advice, &seg, word_info, 
					min_layer, max_layer_id,
					num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)?;

			best_layer
		};

		//2. check if guessed layer works for the full word 
		let res = self.gen_nd_advice_at_layer(job_id, guessed_layer,
			log_level, b_save_advice, &word, word_info);
		if res.is_ok(){ 
			let (num_segs, vec_seg_size, vec_pci, 
				vec_cap,vec_adv)=res.unwrap();
			Ok( (guessed_layer, num_segs, vec_seg_size, vec_pci, vec_cap, 
				vec_adv) )
		}else{//try the max id
			let res2 = self.gen_nd_advice_at_layer(job_id, max_layer_id,
				log_level, b_save_advice, &word, word_info)?;
			let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) = res2;
			Ok( (max_layer_id, num_segs, vec_seg_size, vec_pci, vec_cap
				, vec_adv) )
		}
	}


	/// Given a word, and given its circuits, plan the steps to
	/// prove the word (free of malware sigs). Use estimate of
	/// cost to determine the pc_i of each step.
	/// Returns:
	///( num_steps, 
	///      Vec<size of word seg>, 
	///      Vec<PCI>, 
	///      Vec<Capacity Needed for circs[pci]>,
	///      Vec<Advice for the circuits[pci]>
	///)
	/// NOTE: theoretically, we could generate it while building
	/// statement, however, it's going to slow down the folding.
	/// IDEALLY, we should generate as much info as possible,
	/// so build_statement will be most likely copying over info.
	/// TO save memomry, b_save_nd_adivce indicates whether
	/// to push advice into vec<nd_advice>
	pub fn plan_nd_advice(&self, job_id: usize, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo, word_fname: &str)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
		let b_new = true;
		if b_new{
			self.plan_nd_advice_new(job_id, log_level, b_save_advice, word, word_info, word_fname)
		}else{
			self.plan_nd_advice_old(job_id, log_level, b_save_advice, word, word_info, word_fname)
		}
	}


	/// return if success (LAYER_ID, num_steps, vec<size of word seg>,
	///     vec<pci>,	vec<capacity needed>, vec<advice>)
	/// we do NOT know the result for min_layer, but for sure
	/// max_layer is a WORKING layer for word. We need to find
	/// the minimum working layer for the word to save cost
	/// (the corresponding info is attached).
	/// The function will ALWAYS be successful, as the worst case is
	/// max layer info
	/// Returns:
	///( best_layer, num_steps, 
	///      Vec<size of word seg>, 
	///      Vec<PCI>, 
	///      Vec<Capacity Needed for circs[pci]>,
	///      Vec<Advice for the circuits[pci]>
	///)
	fn bin_search_best_layer(&self, job_id: usize, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo, 
		min_layer: usize, 
		max_layer: usize,
		max_layer_num_segs: usize,
		max_layer_vec_seg_size: Vec<usize>,
		max_layer_vec_pci: Vec<usize>,
		max_layer_vec_cap: Vec<Arc<dyn Capacity + Send + Sync>>,
		max_layer_vec_adv: Vec<Arc<dyn NdAdvice + Send + Sync>>)
		-> Result<(usize, usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>), Error>
		where <CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync {
		let mut gt1 = GTimer::new();
		let mut min_layer_id = min_layer;
		let (mut best_layer,mut max_layer_id) = (max_layer, max_layer);
		let (mut num_segs, mut vec_seg_size, mut vec_pci,
			mut vec_cap, mut vec_adv) = (max_layer_num_segs,
			max_layer_vec_seg_size, max_layer_vec_pci, 
				max_layer_vec_cap, max_layer_vec_adv);
		while min_layer_id <= max_layer_id && max_layer_id>0{
			let mid_id = (min_layer_id + max_layer_id)/2;
			let res = self.gen_nd_advice_at_layer(job_id, mid_id,
				log_level, b_save_advice, word, word_info);
			if res.is_ok(){
				(num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) 
					= res.unwrap();
				best_layer = mid_id;
				if mid_id==0 { break; }else{ max_layer_id = mid_id - 1; }
			}else{
				min_layer_id = mid_id + 1;
			}
			log_perf(job_id, log_level, &format!("bin_search: min_id: {}, max_id: {}, mid_id: {}.  word.len(): {}.", min_layer_id, max_layer_id, mid_id, word.len()), &mut gt1);
		}

		Ok((best_layer, num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv))
	}

	/// Almost the same of bin_search_best_layer, the difference
	/// is that we run all circuits in parallel, and pick
	/// the minimum one
	/// `job_id`: The ID of the job being processed.
	fn par_search_best_layer(&self, job_id: usize, log_level: usize, b_save_advice: bool,
	    word: &Vec<CF1<C1>>, word_info: &WordInfo, 
	    min_layer: usize, 
	    max_layer: usize,
		_dummy_job_id: usize

	) -> Result<(usize, usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>), Error>
		where <CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync {
		use rayon::prelude::*;

		let results: Vec<_> = (min_layer..=max_layer)
				.into_par_iter().map(|layer_id| (
				layer_id, 
				self.gen_nd_advice_at_layer(job_id, layer_id, log_level, 
					b_save_advice, word, word_info)))
				.collect();

		let best_result = results
				.iter()
				.filter_map(|(layer_id, res)| res.as_ref().ok().map(|val| 
					(*layer_id, val)))
					.min_by_key(|(layer_id, _)| *layer_id);

		match best_result {
			Some((best_layer, (num_segs, vec_seg_size, vec_pci, 
					vec_cap, vec_adv))) => { 
						Ok((best_layer, *num_segs, vec_seg_size.clone(), 
							vec_pci.clone(), vec_cap.clone(), vec_adv.clone()))
			},
			None => {
				//return the error of the VERY last circuit (max_layer)
				let mut err = Error::NotSupported("No suitable layer found".to_string()); //default
				for (layer_id, res) in results.into_iter(){
					if layer_id == max_layer {
						err = res.err().unwrap();
						break;
					}
				}
				Err(err)
			}
		}
	}

	/// generate the nd_advice by picking up the circ.
	/// Here we assume that layer of circs are sorted by the cost (increasing).
	/// and each layer has ONLY ONE circ (so we do not have to worry about
	/// ensuring same inp/oup buffer).
	///
	/// We first pick the first segment of the word to figure out the
	/// minimum capacity needed (by calling gen_nd_advice_no_limit).
	/// We then use a binary search method to locate the MINIMUM layer
	/// of circ that is needed (and call gen_nd_advice) to verify it works
	/// for ALL segements of a word.
	pub fn plan_nd_advice_new(&self, job_id: usize, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo, word_fname: &str)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
		let b_fast = true; 
		//0. verify each layer has only one circ
		let mut gt1 = GTimer::new();
		let mut gt2 = GTimer::new();
		log_perf(job_id, log_level, &format!("plan_nd_advice step 0. layers: {}, word.len(): {}, b_save_adivce: {}", self.layered_circs.len(), word.len(), b_save_advice), &mut gt1);
		let mwl = self.layered_circs[0][0].get_mapper().lock().unwrap().max_word_len();
		for i in 0..self.layered_circs.len(){
			assert!(self.layered_circs[i].len()==1, "only 1 circ per layer!");
			assert!(self.layered_circs[i][0]
				.get_mapper().lock().unwrap().max_word_len() == mwl); 
				//all circ should support same max word len
		}

		//1. depending on the b_fast mode, call bin_search or parallel search
		let (_best_layer, num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) =
		   if !b_fast{//using binary search, slow but low RAM cost
			//1. quickly identify the MAX working layer needed
			let res = self.find_working_layer_for_wd(job_id, log_level, b_save_advice,
				word, word_info)?;
			let (max_layer_id, num_segs, vec_seg_size, vec_pci,
				vec_cap, vec_adv) = res;

			//2. binary search to identify the MINIMUM layer that works
			let min_layer = 0;
			self.bin_search_best_layer(job_id, log_level+2, b_save_advice,
					word, word_info, min_layer, max_layer_id,
					num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)
		}else{
			let min_layer = 0;
			let max_layer = self.circuits.len()-1;
			self.par_search_best_layer(job_id, log_level+2, b_save_advice,
					word, word_info, min_layer, max_layer, 0)
		}?;
		//2. double check and return
		let pci = vec_pci[0];
		for x in &vec_pci{assert!(*x==pci);} //should all be same
		log_perf(job_id, log_level, &format!("PERF 1001: plan_nd_advice for {}, search_mode (fast): {}, Total:  best_layer: {}, pci: {}, word.len(): {}.", word_fname, b_fast,  _best_layer, pci, word.len()), &mut gt2);

		Ok( (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv ) )
	}

	/// old version: it assues multiple circs in one layer
	pub fn plan_nd_advice_old(&self, job_id: usize, log_level: usize, _b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo, _word_fname: &str)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
			if 1>0 {panic!("should not call this function. It is invalid. Keep the legacy code for future improvement.");}
			let mut gt1 = GTimer::new();
			log_perf(job_id, log_level, &format!("Entering plan_nd_advice, layers: {}, word.len(): {}.", self.layered_circs.len(), word.len()), &mut gt1);
			let remaining = word.clone();
			#[cfg(test)]{//check if all circs have the same inp/oup
				// check the max_word_len is decreasing (thus avg cost
				//increasing
				for i in 0..self.layered_circs.len(){
					let layer = &self.layered_circs[i];
					println!("DEBUG USE 311: layer i: {}, len: {}", i, layer.len());
					for j in 1..layer.len(){
						let circ1 = &layer[j-1];	
						let circ2 = &layer[j];	
						let cfg1 = circ1.get_stmt_config();
						let cfg2 = circ2.get_stmt_config();
						assert!(circ1.max_word_len()>=circ2.max_word_len());
						assert!(circ1.est_cost()>=circ2.est_cost());
						assert!(cfg1.input_size == cfg2.input_size);
						assert!(cfg1.output_size== cfg2.output_size);
					}
				}
			}

			//1. build the start index for each layer
			let vec_len = self.layered_circs.iter().map(|v| v.len()).
				collect::<Vec<usize>>();
			let mut vec_start = vec![0usize; vec_len.len()];
			for i in 1..vec_start.len(){
				vec_start[i] = vec_start[i-1] + vec_len[i-1];
			}

			//2. chunk the words and plan
			let vec_pci = vec![];
			let vec_size = vec![];
			let vec_cap = vec![];
			let vec_adv:Vec<Arc<dyn NdAdvice + Send + Sync>> = vec![];
			log_perf(job_id, log_level, &format!("plan_nd_advice step 1: check circs."),
				&mut gt1);

			//2.1 Determine the LAYER of circuit to work with. 
			// Here: we assume layers are arranged in descending
			// order of preference:
			// (1) CP + SED with small inp/oup
			// (2) CP + SED with large inp/oup
			// (3) CP + SED + DFA
			// (4) CP + SED + DFA + ISED
			//  ...
			// We test the 1st circuit of each layer (pick up the
			//   most `expensive` circit - the last one, but
			//   maybe handling the shortest max-word - thus fastest), 
			//   if fails, no need
			//   to play with rest of circuits.
			// NOTE: in FACT TO SIMPLIFY CIRCUIT DESIGN, each layer will
			// ONLY hae one circ (as to make inp/oup for circuits exactly
			// the same will take too much design time)
			let b_found = false;
			let selected_layer = 0;
			for layer_id in 0..self.layered_circs.len(){
				//2.1.1 try generate advice by the first circ
				// without any resource limits
				let layer = &self.layered_circs[layer_id];
				let circ1 = &layer[layer.len()-1];
				//we assume all circs have the same max_word_len
				let max_word_len = circ1.get_mapper().lock().unwrap().max_word_len();
				let word_len = if max_word_len>remaining.len(){
					remaining.len()}else {max_word_len};
				let word = remaining[0..word_len].to_vec();
				#[cfg(test)]{
					for circ in layer{assert!(circ.get_mapper().lock().unwrap().
						max_word_len()==max_word_len);
					}
				}
				let prev_adv = if vec_adv.len()==0 {None}
					else {Some(vec_adv[vec_adv.len()-1].clone())};
				//PASS 0 as seg_id just to make syntax ok
				if 1>0 {panic!("should not call this function");}
				let res = circ1.get_mapper().lock().unwrap()
					.gen_nd_advice(&word, &word_info, prev_adv, 0, 0);
				if !res.is_ok() {
					//quick elimination of apparent non-working layer
					//this is usually quickly decided by looking at
					//word_info in gen_nd_advice_no_limit
					continue;
				}

				//if structure wise ok, still need to check details
				//of buffer capacity ok, so do have to run a real
				//instance of capacity check
				//let (cap, _advice) = res.unwrap();
				//let circ = &layer[0];
				//if circ.get_mapper().lock().unwrap()
				//	.get_capacity().can_satisfy(&cap){
				//	b_found = true;
				//	selected_layer = layer_id;
				//	break;
				//}else{
				//	if layer_id == self.layered_circs.len()-1{
				//		println!("UNABLE to find circ: cap needed: {:#?} and last circ capacility: {:#?}", cap, circ.get_mapper().lock().unwrap().get_capacity());
				//	}
				//}
			}
			assert!(b_found, "UNABLE to find any layer of circuits working!");
			log_perf(job_id, log_level, &format!("plan_nd_advice step 2: select layer. selected layer: {}.", selected_layer), &mut gt1);

			//2.2. For each step, determine which circuit in the 
			// selected layer to work for a partial fragement of the remaining
			// word.
			// We assume all circuits in each layer have 
			// the SAME input/output buffer structure so that they
			// can talk with each other. They may differ in:
			// (1) max_word_len, and (2) internal data buffer size
			// which affects the cost. 
			// These circuits should also be sorted in DESCENDING order
			// of the average cost (usually large max_word_len and small
			// buffer circuit should be arranged earlier in the sequence).
			// Note that there are cases that remaining.len() is less than
			// the max_word_len of a circuit (then a next smaller circuit)
			// might yield a better performance. We continue the search
			// until a circuit in the layer cannot satisfy the processing
			// resource request of the remaining fragement, and keep track
			// the minimal resource demanding one and decide the
			// circuit to workwith.

			let layer = &self.layered_circs[selected_layer];
			while remaining.len()>0{
				//2.2.1. identify the circ with the smallest cost given
				// the remaining.len
				let mut min_id = 0;
				let mut min_avg_cost = layer[0].est_cost(); 
				for id in 0..layer.len(){
					let circ = &layer[id];
					let max_word_len = circ.get_mapper().lock().unwrap()
						.max_word_len();
					let word_len = if max_word_len>remaining.len(){
						remaining.len()}else {max_word_len};
					let avg_cost = circ.est_cost()/word_len;
					if avg_cost<min_avg_cost{
						min_id = id;
						min_avg_cost = avg_cost;
					}
				}

				//2.2.2 now search forward until capacity is satisfied.
				//Stop immediately once capacity can be satisfied
				let mut last_word_len = 0;
				let mut _last_res = None;
				let b_found = false;
				for idx in min_id..layer.len(){
					//for every word_len try generating the unlimited resource
					//request
					let circ = &layer[idx];
					let max_word_len = circ.get_mapper().lock().unwrap()
						.max_word_len();
					let word_len = if max_word_len>remaining.len(){
						remaining.len()}else {max_word_len};
					let word = remaining[0..word_len].to_vec();
					let prev_adv = if vec_adv.len()==0 {None}
						else {Some(vec_adv[vec_adv.len()-1].clone())};
					if last_word_len!=word_len {
						//NOTE: the seg_id passed is not correct
						//but since this is an OLD-deprecated function
						//we just fix syntax here.
						if 1>0 {panic!("this function should not be called");}
						last_word_len = word_len;
						_last_res = Some(circ.get_mapper().lock().unwrap()
						  .gen_nd_advice(&word, &word_info, prev_adv, 0, 0)
						  .unwrap());
					}
				
					//verify the circ does can satisfy the request
 // 					if circ.get_mapper().lock().unwrap().get_capacity()
 // 						.can_satisfy(&last_res.as_ref().unwrap().0){
 // 						let (cap, advice) = last_res.unwrap();
 // 						let pci = vec_start[selected_layer] + idx;
 // 						pec_pci.push(pci);
 // 						vec_size.push(word_len);
 // 						vec_cap.push(cap);
 // 						if b_save_advice{ //to save memory
 // 							//advice will then have to be re-generated later.
 // 							vec_adv.push(advice);
 // 						}
 // 						remaining = remaining[word_len..].to_vec();
 // 						b_found = true;
 // 						break;
 // 					}
 // 					if b_found {break;}
				}
				assert!(b_found, "CANNOT find satisfying circ for remaining length: {}!", remaining.len());
			}//end of while remaining loop
			log_perf(job_id, log_level, &format!("plan_nd_advice step 3: gen advice and try each circ. circs: {}, wordlen: {}.", vec_pci.len(), format_bytes(word.len()*31)), &mut gt1);

			Ok( (vec_pci.len(), vec_size, vec_pci, vec_cap, vec_adv  ))
}

	/// It processes a collection of words, and collect
	/// a vector of StatementExtraInfo, mainly for sequence (word_id, seg_id)
	/// except the last hash_cmF in each record.
	/// It also computes the non-deterministic advice (for each word),
	/// which contains the hints for generating witness.
	/// For each word, it selects circuits to process its fragements, 
	/// using circuit's capacity to determine which circuit to use.
	/// It finally 
	/// outputs the (word_id, segment_id) information.
	/// The length of the returned vector is equal to the total number of words
	/// NOTE: pc_i is actually the LAST step's circuit which performs
	/// the operation, and uses to fold in this step
	/// pc_i1 is actually the circuit to compute z_i1. So pc_i1 is
	/// the ``j" in super-nova's paper which performs the calculation
	/// `z_{i+1} = F_j(z_i, w_i)`, and pc_i is the circuit id to
	/// fold (U_i, u_i).
	/// `job_id`: The ID of the job being processed.
	pub fn pass_one(&mut self, 
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		idx_ind_proof: usize,
	  	mut rng: impl RngCore +  CryptoRng,
		vec_word_info: &Vec<WordInfo>, job_id: usize) ->
		(Vec<StatementExtraInfo<C1::ScalarField>>, HashMap<usize,usize>,
		 Vec<Vec<Arc<dyn NdAdvice + Send + Sync>>>,
		 Option<(BatchClaim<E>, IndividualClaim<E>, SnarkAdvice<E::ScalarField>
		)>){
		//0. generate the claim first
		if 1>0 {panic!("do not call pass_one - call pass_all.");}
		let log_level = LOG2;
		let mut t2 = Timer::new("PassOne", 1);
		let words = {
			iter_words2.map(|v| v.to_vec())
			.collect::<Vec<Vec<C1::ScalarField>>>()
		};
		t2.prt(&format!("step 1: word len: {}", words.len()));

		let batch_pack = if !self.b_full_mode{
			assert!(self.batch_pk.is_some());
			let pk = &self.batch_pk.as_ref().unwrap();
			let _vk = &self.batch_vk.as_ref().unwrap();
			let (global_claim, ind_claims, snark_inp) = 
				BatchProcessor::<E,LK,S,CS1E,H>::gen_claims(pk, &mut rng, &words, self.lkup.clone()).unwrap();
			Some( (global_claim, ind_claims[idx_ind_proof].clone(), snark_inp) )
		}else{
			None
		};
		t2.prt("step 2: generate batch and individual claims");

		let snark_inp = if !self.b_full_mode
			{batch_pack.as_ref().unwrap().2.clone()}
			else {SnarkAdvice::empty(&words)};



		//1. init
		let mut vec_res = Vec::<StatementExtraInfo<C1::ScalarField>>::new();
		let zero = C1::ScalarField::zero();
		let b_full_mode = self.b_full_mode;
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		//println!("DEBUG USE 889.0.2");
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(zero, zero, &self.poseidon_config, b_full_mode, fq_bits, total_words);
		let z0_part2_hash = z0_part2.hash(&self.poseidon_config);
		let _z_0 = vec![zero, z0_part2_hash]; //will replaced
		let mut m_map = HashMap::<usize,usize>::new();
		t2.prt("step 3: generate z0");

		let pc_0_val = 0;
		let _pc_0 = C1::ScalarField::from(pc_0_val as u32);
		t2.prt("step 4: generate nova1");

		//2. while loop to process words one by one
		// figure out the num_steps (and reset in self)
		// compute the final hash_cmF
		let mut word_id = 1;
		let n_circ = self.circuits.len();
		let _vec_mapper= self.circuits.iter().map(|c| c.get_mapper()).
			collect::<Vec<Arc<Mutex<GM>>>>();
		let mut vec_advice = vec![];
		let mut prev_stmt = None;
		let lkup_len= self.lkup.get_size();
		let mut total_lkup_covered = 0;
		for word in iter_words{
			//2.1 first try out and determine the length info for each
			let mut remaining = word.clone();
			let mut subseg_id = 0;
			let total_word_len = word.len();
			let mut acc_wd_len = 0;
			let _mapper = self.circuits[0].get_mapper();
			let (steps, vec_len, vec_pci, _vec_cap_req, advice) = self.plan_nd_advice(0, log_level+1, true, &word, &vec_word_info[word_id-1],
				&format!("word_{}", word_id)).expect("Planning advice fails!"); 
			for i in 0..steps{
				let pc_i = if i==0 {0} else {vec_pci[i-1]};
				let pc_i1 = vec_pci[i]; //this is actually pc_i1 for this circ
				let circ = &self.circuits[pc_i1];
				let _max_len = circ.max_word_len();
				let act_len = vec_len[i];
				acc_wd_len += act_len;
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();
				#[cfg(test)]{
					//use crate::folding::foldpot::sigma_ir1cs::{Capacity};
					assert!(act_len<=_max_len);
					let rc_cap = _vec_cap_req[i].clone();
					assert!(circ.get_mapper().lock().unwrap().get_capacity()
						.can_satisfy(&rc_cap));
					if i==steps-1 {assert!(remaining.len()==0);}
				}
				let lk_share_size = circ.get_lkup_share_size();

				let ei = StatementExtraInfo::<C1::ScalarField>{
					total_words: C1::ScalarField::from(total_words as u32),
					word_id: C1::ScalarField::from(word_id as u32),
					subseg_id: C1::ScalarField::from(subseg_id as u32),
					total_word_len: C1::ScalarField::from(total_word_len as u32),
					total_word_segs: C1::ScalarField::from(steps as u32),
					n_circ: C1::ScalarField::from(n_circ as u32),
					pc_i:  C1::ScalarField::from(pc_i as u32), 
					pc_i1:  C1::ScalarField::from(pc_i1 as u32), //update later
					act_word_subseg_size: C1::ScalarField::from(act_len as u32),
					batch_r: snark_inp.vec_r[(word_id as usize)-1],
					batch_v: snark_inp.vec_v[(word_id as usize)-1],
					r_all_words: snark_inp.r_all_words,
					r_kzg_len: snark_inp.r_kzg_len,
					r_vec_r: snark_inp.r_vec_r_kzg,
					r_vec_v: snark_inp.r_vec_v_kzg,
					r_word_i: snark_inp.rands[(word_id as usize)-1],
					accumulated_word_len: C1::ScalarField::from(acc_wd_len as u32),
				};//end constructor StatementExtraInfo

				//need to build the statement to fill the m_map
				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(&frag, &prev_stmt, self.lkup.clone(), &ei, advice[subseg_id-1].clone(), lk_share_size, false, job_id);
				assert!(stmt_res.is_ok());
				let stmt = stmt_res.unwrap();
				stmt.fill_lkup_mvec(&mut m_map, &self.lkup); //needed here!
				let ea = stmt.to_extra_info();
				vec_res.push(ea);
				prev_stmt= Some(stmt);


				subseg_id +=1;
				total_lkup_covered += lk_share_size;
			}

			vec_advice.push(advice);
			word_id +=1;
		}
		t2.prt("step 5: dispatch w");

		assert!(total_lkup_covered >= lkup_len, "total: {}, lkup_len: {}", total_lkup_covered, lkup_len);
		(vec_res, m_map, vec_advice, batch_pack)
	}

	/// Takes, the information of word_id and segment_id.
	/// This time computes the cm_F, which generates the random
	/// and put that into the
	/// StatementExtraInfo for pass_three.
	/// idx_individual_proof indicates which individual proof to generate
	/// as sample. We have 2 iterators, to the same vector of words (will
	///   improve later)
	/// return the StatementExtraInfo for pass_three and 
	/// the computed final hash_cmF for all fixed memory segments along steps.
	pub fn pass_two(&self, 
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		_iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		vea: &Vec<StatementExtraInfo<C1::ScalarField>>,
		m_map: &HashMap<usize,usize>,
		vec_advice: &Vec<Vec<Arc<dyn NdAdvice + Send + Sync>>>,
		job_id: usize)
	-> (Vec<StatementExtraInfo<C1::ScalarField>>, C1::ScalarField){
		//1. prep the data
		let mut timer = Timer::new("pass_two", 0);
		let n_steps = vea.len();
		let mut v_res = vec![];
		let zero = C1::ScalarField::zero();
		let b_full_mode = self.b_full_mode;
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(zero, zero, &self.poseidon_config, 
			b_full_mode, fq_bits,total_words);
		let z0_part2_hash = z0_part2.hash(&&self.poseidon_config);
		let z_0 = vec![zero, z0_part2_hash];
		let _n_circ = field_to_usize(&vea[0].n_circ);
		let mut hash_cmF= C1::ScalarField::zero();
		let (ch, rc) = (zero, zero);
		timer.prt("pass_two: step 0: init");

		//2. create nova1
		println!("DEBUG USE 5017.1:  n_steps: {}", n_steps);
		let pc_0 = zero;
		let pc_0_val = field_to_usize(&pc_0);
		let precomputed_cmF = None;
        let mut nova1 =
            FoldPotSuper::<E,P, C2G2, C1, GC1, C2, GC2, FC,
			CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &self.nova_param,
				self.circuits.clone(),
                z_0.clone(),
				self.circuits.len(), 
				pc_0_val,
				self.b_full_mode,
				ch, 
				rc,
				total_words,
				precomputed_cmF
            )
            .unwrap();
		timer.prt("pass_two: step 2: init nova1");

		//2. process the words one by one
		let mut idx = 0;
		let mut prev_stmt = None;
		let mut num_steps = 0;
		let mut wi = 0;
		let mut start = 0;
		let lk_len = self.lkup.get_size();
		for word in iter_words{
			let mut remaining = word.clone();
			let mut subseg_id = 0;
			while remaining.len()>0{
				//2.1 compute the problem statement instance again
				// with the correct word/segment data
				let _pc_i = field_to_usize(&vea[idx].pc_i);
				let pc_i1 = field_to_usize(&vea[idx].pc_i1);
				let circ = &self.circuits[pc_i1];
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let share_size= circ.get_lkup_share_size();
				let frag = remaining[0..act_len].to_vec();
				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, vec_advice[wi][subseg_id-1].clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				let mut stmt = stmt_res.unwrap();

				if idx==n_steps-1{ assert!(start+share_size>=lk_len); }
				stmt.update_lookup(start, start+share_size, &self.lkup, m_map);
				start += share_size;

				//2.2 compute hash_cmF
				nova1.pc_i = stmt.pc_i;
				nova1.pc_i1 = stmt.pc_i1;
				(hash_cmF,_) = nova1.compute_step_hc_cmF(hash_cmF, &stmt)
				.expect("hash_cmf generation error");
				//println!("DEBUG USE 402.1: hash_cmF: {}", hash_cmF);

				//2.3 update 
				subseg_id +=1;
				remaining = remaining[act_len..].to_vec();
				v_res.push(stmt.to_extra_info());
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				timer.prt(&format!("pass_two: subseg_id: {}", subseg_id)); 
			}//end for while remaining word 
			let total_subsegs = subseg_id - 1;
			assert!(total_subsegs == 
				field_to_usize(&v_res[v_res.len()-1].total_word_segs), 
				"total_word_segs incorrect");
			wi += 1;
		}

		println!("DEBUG USE 402.5 num_steps: {}, vea.len: {}", num_steps, vea.len());
		assert!(num_steps==vea.len(), "ERROR: pass2 num_steps incorrect, num_steps: {}, vea.len: {}", num_steps, vea.len());

	
		//3. update all extra info record
		(v_res, hash_cmF)
	}

	/// basically run steps and return nova instance,
	/// where the running and incoming instances can be extracted.
	/// It also (optinally) returns the batch proof, number of steps,
	/// and one sample individual
	/// proof (as specified by the idx of individual proof).
	/// Note that we'll dispatch lookup table again (alternatively,
	///   one could pass all allocted table, but here we try to save memory).
	pub fn pass_three(&self, 
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		vea: &Vec<StatementExtraInfo<C1::ScalarField>>,
		m_map: &HashMap<usize, usize>, 
		idx_individual_prf: usize,
	  	mut _rng: impl RngCore +  CryptoRng, 
		hash_cmF: C1::ScalarField,
		claim_pack: &Option<(BatchClaim<E>, IndividualClaim<E>, SnarkAdvice<E::ScalarField>)>,
		job_id: usize,
		vec_advice: &Vec<Vec<Arc<dyn NdAdvice + Send + Sync>>>)
	-> (FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E, LK, GM, H>,
		usize, Option<(BatchProof<E,S>,IndividualProof<E>)>
			)
	{
		if 1>0 {panic!("pass_three is deprecated. Call pass_all insetead");}
		let mut t1 = Timer::new("pass_three", 1);
		//1. build the batch proof and individual proof
		let batch_prfs = if !self.b_full_mode{
			let words = {
				iter_words2.map(|v| v.to_vec())
				.collect::<Vec<Vec<C1::ScalarField>>>()
			};
			assert!(self.batch_pk.is_some());
			let pk = &self.batch_pk.as_ref().unwrap();
			let vk = &self.batch_vk.as_ref().unwrap();
			let _zero = E::ScalarField::zero();
			let (global_claim, ind_claim, snark_inp) = 
				(&claim_pack.as_ref().unwrap().0, &claim_pack.as_ref().unwrap().1, &claim_pack.as_ref().unwrap().2);
			let rand_inp = SnarkRandInput{
				hash_cmF, 
				kzg_all_words: global_claim.kzg_all_words.clone(), 
				kzg_length: global_claim.kzg_length.clone(), 
				kzg_lk_col1: global_claim.kzg_lk_col1.clone(),
				kzg_lk_col2: global_claim.kzg_lk_col2.clone(),
				kzg_vec_r: E::G1::generator(),  //default val
				kzg_vec_v: E::G1::generator(), //default val
				poseidon_config: self.poseidon_config.clone(),
			};

			let (batch_proof, _rand_inp2) = BatchProcessor::<E,LK,S,CS1E,H>
			        ::prove_batch(pk, &snark_inp, &words, self.lkup.clone(),
			        &rand_inp);			assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_batch(vk, 
				None, None, None, None,
				&global_claim, &batch_proof, &self.poseidon_config, 
				false, None)); //note part2 of the proof will be checked later
			let ind_prf = BatchProcessor::<E,LK,S,CS1E,H>::prove_individual(pk, 
				&snark_inp, &words, &ind_claim,
				idx_individual_prf);
			let _res = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(vk, idx_individual_prf, &ind_claim, &batch_proof, &ind_prf);
			#[cfg(test)] {assert!(_res);}
			Some((batch_proof, ind_prf))
		}else{
			None
		};
		t1.prt("Step 1: build batch prf");

		//2. build up the initial z_0
		let zero = E::ScalarField::zero();
		let (ch,rc) = if !self.b_full_mode{
			(batch_prfs.as_ref().unwrap().0.ch, 
			 batch_prfs.as_ref().unwrap().0.rc)
		}else{ (zero, zero)};
		let vea = vea.clone();
		let pc_0 = vea[0].pc_i;
		let pc_0_val = field_to_usize(&pc_0);
		let b_full_mode = self.b_full_mode;
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(ch,rc,&self.poseidon_config,b_full_mode,fq_bits,total_words);
		let z0_part2_hash = z0_part2.hash(&self.poseidon_config);
        let z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
		let _n_steps = vea.len();
		t1.prt("Step 2: build initial z0");

		//3. build the nova instance
		let precomputed_cmF = None;
        let mut nova =
            FoldPotSuper::<E,P, C2G2, C1, GC1, C2, GC2, FC,
			CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &self.nova_param,
				self.circuits.clone(),
                z_0.clone(),
				self.circuits.len(), 
				pc_0_val,
				self.b_full_mode,
				ch,
				rc,
				total_words,
				precomputed_cmF
            )
            .unwrap();
		t1.prt("Step 3: build nova");

		//3. prove steps
        let mut rng = ark_std::test_rng();
		let mut idx = 0;
		let mut prev_stmt = None;
		let mut num_steps = 0;
		let _lk_len = self.lkup.get_size();
		let mut wi = 0;
		let mut start = 0;
		for word in iter_words{
			let mut remaining = word.clone();
			let mut subseg_id = 0;
			while remaining.len()>0{
				//2.1 compute the problem statement instance again
				// with the correct cmF
				let j = field_to_usize(&vea[idx].pc_i1);
				let circ = &self.circuits[j];
				let share_size = circ.get_stmt_config().lookup_share_size;
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();
				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, vec_advice[wi][subseg_id].clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				let mut stmt = stmt_res.unwrap();
				stmt.update_lookup(start, start+share_size, &self.lkup, m_map);
				start += share_size;

				//2.2. prove step
				let v_stmt = stmt.to_vec();
				let other_inst = None;
				nova.pc_i = vea[idx].pc_i;
				nova.pc_i1 = vea[idx].pc_i1;
            	nova.prove_step(&mut rng, v_stmt, other_inst)
					.expect("prove step error");

				//2.3 update 
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
			}//end for while remaining word 
			wi += 1;
		} //for each word
		assert!(num_steps==vea.len());
        assert_eq!(C1::ScalarField::from(num_steps as u32), nova.i);
		t1.prt(&format!("Step 4: prove steps: {}", num_steps));

		//4. generate the output
		let _verifier_param = self.nova_param.1.clone();

		//5. test and verify
		#[cfg(test)]{
        	let (r1, r2, r3, r4) = nova.instances();
        	FoldPotSuper::<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H>::verify(
				_verifier_param,
				z_0,
				nova.z_i.clone(),
				nova.i.clone(),
				r1, r2, r3, r4).unwrap();
		}
		t1.prt(&format!("Step 5: verify steps: {}", num_steps));

		
		(nova, num_steps, batch_prfs)
	}


	/// integrates all three passes together so that
	/// we do not have to generate all advices all at one time.
	pub fn pass_all(&self,
		phase_name: &str, //below 3 copies of the same iterator
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words3: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		idx_ind_proof: usize,
	  	mut rng: impl RngCore +  CryptoRng,
		vec_word_info: &Vec<WordInfo>,
		vec_word_fnames: &Vec<String>,
		job_id: usize
	) -> Result<(
		FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E, LK, GM, H>,
		usize,
		Option<(BatchProof<E,S>,IndividualProof<E>)>,
	    Option<(BatchClaim<E>, IndividualClaim<E>,
			SnarkAdvice<E::ScalarField>)>
		), Error>{
		//0. generate the claim first
		//estimate: 700M data = 700M/31 = 23M field elements in words
		//given 62 nibbles per word.
		//words = 23M * 32 byte = 700M data
		//each claim is small, up to 300 claims. So small.
		let log_level = LOG2;
		let b_debug = B_DEBUG;
		let mut gt1 = GTimer::new();

		let m1 = get_mem_usage_mb();
		let words = {
			iter_words2.map(|v| v.to_vec())
			.collect::<Vec<Vec<C1::ScalarField>>>()
		};
		let _n_words = words.len();
		let total_wd_len = words.iter().map(|x| x.len()).sum::<usize>();

		let claim_pack = if !self.b_full_mode{
			assert!(self.batch_pk.is_some());
			let pk = &self.batch_pk.as_ref().unwrap();
			let (global_claim, ind_claims, snark_inp) = 
				BatchProcessor::<E,LK,S,CS1E,H>::gen_claims(pk, &mut rng, &words, self.lkup.clone()).unwrap();
			Some( (global_claim, ind_claims[idx_ind_proof].clone(), snark_inp) )
		}else{
			None
		};
		let snark_inp = if !self.b_full_mode
			{claim_pack.as_ref().unwrap().2.clone()}
			else {SnarkAdvice::empty(&words)};
		let m2 = get_mem_usage_mb();

		//1. init
		let mut vec_res = Vec::<StatementExtraInfo<C1::ScalarField>>::new();
		let zero = C1::ScalarField::zero();
		let b_full_mode = self.b_full_mode;
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(zero, zero, &self.poseidon_config, b_full_mode, fq_bits, total_words);
		let z0_part2_hash = z0_part2.hash(&self.poseidon_config);
		let _z_0 = vec![zero, z0_part2_hash]; //will replaced
		let mut m_map = HashMap::<usize,usize>::new();
		let pc_0_val = 0;
		let _pc_0 = C1::ScalarField::from(pc_0_val as u32);
		log_perf(job_id, log_level, &format!(
			"{} step 1: generate batch/ind claims. mem: {} GB, increased mem: {} MB, for words: {}, total_word_len: {} packed fields.", phase_name, m2/1024, 
				if m2>m1 {m2-m1} else {0}, total_words, total_wd_len), 
			&mut gt1);


		//------------------------------------------
		//2. PASS-1: while loop to process words one by one
		// figure out the num_steps (and reset in self),
		// DISPATCH the lookup table.
		// Unfortunately, we cannot generate the cmF yet
		// as vec_m for shared lookup is not computed yet
		// until lookup table is distributed and couter index
		// computed.
		//------------------------------------------
		let mut word_id = 1;

		let n_circ = self.circuits.len();
		let _vec_mapper= self.circuits.iter().map(|c| c.get_mapper()).
			collect::<Vec<Arc<Mutex<GM>>>>();
		let lkup_len= self.lkup.get_size();
		let mut total_lkup_covered = 0;
		let m3 = get_mem_usage_mb();
		let mut gtw = GTimer::new();
		let mut last_pci1 = 0;
		for (word, word_fname) in iter_words.zip(vec_word_fnames.iter()){
			let mut prev_stmt = None;
			let mut prev_adv = None;
			let mut gt2 = GTimer::new();

			//2.1 first try out and determine the length info for each
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let total_word_len = word.len();
			let mut acc_wd_len = 0;
			let _mapper = self.circuits[0].get_mapper();
			let word_info = &vec_word_info[word_id-1];
			let (steps, vec_len, vec_pci, _vec_cap_req, _advice) = self.plan_nd_advice(job_id, log_level+2, false, &word, word_info, word_fname)?;
			log_perf(job_id, log_level+2, &format!("{} - Pass 1: START decide circ alloc for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(total_word_len*31)), &mut gt2);
			for i in 0..steps{
				//2.1 set up params
				let pc_i = if i==0 {last_pci1} else {vec_pci[i-1]};
				let pc_i1 = vec_pci[i]; //this is actually pc_i1 for this circ
				last_pci1 = pc_i1;
				let circ = &self.circuits[pc_i1];
				let _max_len = circ.max_word_len();
				let act_len = vec_len[i];
				acc_wd_len += act_len;
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();
				#[cfg(test)]{
					//use crate::folding::foldpot::sigma_ir1cs::{Capacity};
					assert!(act_len<=_max_len);
					let rc_cap = _vec_cap_req[i].clone();
					assert!(circ.get_mapper().lock().unwrap().get_capacity()
						.can_satisfy(&rc_cap));
					if i==steps-1 {assert!(remaining.len()==0);}
				}
				let lk_share_size = circ.get_lkup_share_size();

				//2.2 build the StatementExtraInfo
				let ei = StatementExtraInfo::<C1::ScalarField>{
					total_words: C1::ScalarField::from(total_words as u32),
					word_id: C1::ScalarField::from(word_id as u32),
					subseg_id: C1::ScalarField::from(subseg_id as u32),
					total_word_len: C1::ScalarField::from(total_word_len as u32),
					total_word_segs: C1::ScalarField::from(steps as u32),
					n_circ: C1::ScalarField::from(n_circ as u32),
					pc_i:  C1::ScalarField::from(pc_i as u32), 
					pc_i1:  C1::ScalarField::from(pc_i1 as u32), //update later
					act_word_subseg_size: C1::ScalarField::from(act_len as u32),
					batch_r: snark_inp.vec_r[(word_id as usize)-1],
					batch_v: snark_inp.vec_v[(word_id as usize)-1],
					r_all_words: snark_inp.r_all_words,
					r_kzg_len: snark_inp.r_kzg_len,
					r_vec_r: snark_inp.r_vec_r_kzg,
					r_vec_v: snark_inp.r_vec_v_kzg,
					r_word_i: snark_inp.rands[(word_id as usize)-1],
					accumulated_word_len: C1::ScalarField::from(acc_wd_len as u32),
				};//end constructor StatementExtraInfo
				log_perf(job_id, log_level+2, &format!("-- Pass 1. For wd: {}, subseg_id: {} gen_statment_extra_info.", word_fname, subseg_id), &mut gt2);

				//2.3 generate the advice and statement
				//need to build the statement to fill the m_map
				let res = circ.get_mapper().lock().unwrap()
					.gen_nd_advice(&frag, word_info, prev_adv, subseg_id - 1, job_id);
				assert!(res.is_ok(), "\n\n===== **** =====\nUNABLE to generate advice for word: {}, segment_id: {}, ERROR: {:#?}\n==============\n", word_fname, subseg_id, res); 
				let cur_adv = res.unwrap();

				log_perf(job_id, log_level+2, &format!("-- Pass 1. gen_advice."), &mut gt2);
				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(
					&frag, &prev_stmt, self.lkup.clone(), &ei,
					//	advice[subseg_id-1].clone(), 
						cur_adv.clone(),
						lk_share_size, false, 0);
				assert!(stmt_res.is_ok(), "\n\n === *** === \nUNABLE to generate statement for word id: {}, segment _id: {}, ERR: {:#?}. *** SHOULD IMPROVE the CapErr framework. Exception should be thrown in gen_nd_advice instead of build_stmt ***", word_fname, subseg_id, stmt_res);
				prev_adv = Some(cur_adv);
				log_perf(job_id, log_level+2, &format!("-- Pass 1. build stmt."), &mut gt2);
				let stmt = stmt_res.unwrap();
				stmt.fill_lkup_mvec(&mut m_map, &self.lkup); //needed here!
					//for updating couners of lookup
					//later in PASS2 it generates the m_table for
					//each lookup for the corresponding lookup shares.


				//2.5 making updates
				let ea = stmt.to_extra_info();
				vec_res.push(ea);
				prev_stmt= Some(stmt);
				subseg_id +=1;
				total_lkup_covered += lk_share_size;
				log_perf(job_id, log_level+2, &format!("-- Pass 1. update. "), &mut gt2);
			}

			log_perf(job_id, log_level+1, &format!("{} Pass 1. END generate advice word: fname: {} of size: {}.", phase_name, word_fname, format_bytes(total_word_len*31)), &mut gtw);
			word_id +=1;
		}
		let m4 = get_mem_usage_mb();
		let b_check_lkup = self.layered_circs[0][0].is_check_lkup(); //assume
			//all circ have the same
		if b_check_lkup{
			assert!(total_lkup_covered >= lkup_len, "total: {}, lkup_len: {}", total_lkup_covered, lkup_len);
		}
		log_perf(job_id, log_level, &format!(
			"{} step 2: dispatch w into steps. mem: {} MB for total_word_len: {}: ", phase_name, if m4>m3 {m4-m3} else {0}, format_bytes(total_wd_len*31))
			, &mut gt1);

		
		//------------------------------------------
		//3. PASS-2: now with the m_map defined, distributing
		//lkup and update m_table for query tables in each 
		//statement. To avoid consuming memory, we regenerate
		//all advice again.
		//------------------------------------------
		let m_pass2_1 = get_mem_usage_mb();
		let mut vea = vec_res; //just rename var for the code from pass_three
		let mut idx = 0;
		let mut num_steps = 0;
		let _lk_len = self.lkup.get_size();
		let mut gtw2 = GTimer::new();
		let mut word_id = 1;
		let mut start = 0; //global position in ENTIRE sequence for update lkup
							//share in each statement
		let mut vec_grp_cmF = vec![]; //does not cost much to save
			//estimate 64 bytes * 700MB/128kb = 
			//64 * 5.6k = 330kb,
			//so we can use it to cut prove_step time to avoid computing
		let mut hash_cmF= C1::ScalarField::zero();

		for word in &words{
			let mut prev_adv = None;
			let mut prev_stmt = None;
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let word_info = &vec_word_info[word_id-1];
			let word_fname = &vec_word_fnames[word_id-1];
			log_perf(job_id, log_level+2, &format!("{} - Pass 2. START generate cmF for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw2); 
			while remaining.len()>0{
				//3.1 compute the problem statement instance 
				let j = field_to_usize(&vea[idx].pc_i1);
				let circ = &self.circuits[j];
				let share_size = circ.get_stmt_config().lookup_share_size;
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();

				//3.2 generate the adice again
				let res = circ.get_mapper().lock().unwrap()
					.gen_nd_advice(&frag, word_info, prev_adv, subseg_id - 1, job_id);
				assert!(res.is_ok(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id); 
				let cur_adv = res.unwrap();
				log_perf(job_id, log_level+2, &format!("-- Pass2. gen advice. sugseg_id: {}", subseg_id), &mut gtw2);

				//3.3 generate the statement again
				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, cur_adv.clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				let mut stmt = stmt_res.unwrap();
				log_perf(job_id, log_level+2, &format!("-- Pass2. gen statement"), &mut gtw2);
				stmt.update_lookup(start,start+share_size, &self.lkup, &m_map);
				start += share_size;
				log_perf(job_id, log_level+2, &format!("-- Pass 2. update lkup, share_size: {}", share_size), &mut gtw2);

				//3.4 update the hash_cmF
				let pc_i1 = field_to_usize(&vea[idx].pc_i1);
				let cs_pp = &self.nova_param.0.vec_pp[pc_i1].cs_pp;
				let poseidon_config = &self.nova_param.0.vec_pp[0].poseidon_config; //to imitate what FoldPotSuper.init_adv takes vec_pp[0].poseidon_config
				let res =  compute_step_hc_cmF_adv
						::<C1,LK,CS1,GM,FC,H>(
						hash_cmF, &stmt, circ, cs_pp, poseidon_config, job_id)
						.expect("compute step hc cmF err");
				hash_cmF = res.0;
				vec_grp_cmF.push(res.1);
				log_perf(job_id, log_level+2, &format!("-- Pass 2. compute cmF. "), &mut gtw2);

				//3.5 update 
				let ea = stmt.to_extra_info();
				vea[idx] = ea; //UPDATE.
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
				log_perf(job_id, log_level+2, &format!("-- Pass 2. update extra info. "), &mut gtw2);
			}//end for while remaining word 
			log_perf(job_id, log_level+2, &format!("{} - Pass 2. END generate cmF for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw2); 
			word_id += 1;
		} //for each word
		assert!(num_steps==vea.len(), "num_steps: {}, vea.len: {}", num_steps, vea.len());


		let m_pass2_2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!(
			"{} step 3: generate cmF, mem: {} MB for total_word_len: {}: ", phase_name, if m_pass2_2>m_pass2_1 {m_pass2_2-m_pass2_1} else {0}, format_bytes(total_wd_len*31)) , &mut gt1);

		//------------------------------------------
		//4. PASS-3: now do the prove_step
		//------------------------------------------
		let m5 = get_mem_usage_mb();
		let n_steps = vea.len();
		let batch_prfs = if !self.b_full_mode{
			assert!(self.batch_pk.is_some());
			let pk = &self.batch_pk.as_ref().unwrap();
			let vk = &self.batch_vk.as_ref().unwrap();
			let _zero = E::ScalarField::zero();
			let (global_claim, ind_claim, snark_inp) = 
				(&claim_pack.as_ref().unwrap().0, &claim_pack.as_ref().unwrap().1, &claim_pack.as_ref().unwrap().2);
			let rand_inp = SnarkRandInput{
				hash_cmF, 
				kzg_all_words: global_claim.kzg_all_words.clone(), 
				kzg_length: global_claim.kzg_length.clone(), 
				kzg_lk_col1: global_claim.kzg_lk_col1.clone(),
				kzg_lk_col2: global_claim.kzg_lk_col2.clone(),
				kzg_vec_r: E::G1::generator(),  //default val
				kzg_vec_v: E::G1::generator(), //default val
				poseidon_config: self.poseidon_config.clone(),
			};

			let (batch_proof, _rand_inp2) = BatchProcessor::<E,LK,S,CS1E,H>
				::prove_batch(pk, &snark_inp, &words, self.lkup.clone(),
				&rand_inp);
			assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_batch(vk, 
				None, None, None,None,
				&global_claim, &batch_proof, &self.poseidon_config, 
				false,None)); //note part2 of the proof will be checked lateri
			let ind_prf = BatchProcessor::<E,LK,S,CS1E,H>::prove_individual(pk, 
				&snark_inp, &words, &ind_claim,
				idx_ind_proof);
			let _res = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(vk, idx_ind_proof, &ind_claim, &batch_proof, &ind_prf);
			#[cfg(test)] {assert!(_res);}
			Some((batch_proof, ind_prf))
		}else{
			None
		};
		//self.batch_pk = None; //clear the RAM removed because &self is used and Arc handles cleanup
		let m6 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!(
			"{} step 4: generate batch prf, mem: {} MB for words: {}, n_steps: {}: ", phase_name, if m6>m5 {m6-m5} else {0}, words.len(), n_steps) , &mut gt1);

		//5. re-intialize with the newly computed ch and rc (challenges)
		let (ch,rc) = if !self.b_full_mode{
			(batch_prfs.as_ref().unwrap().0.ch, 
			 batch_prfs.as_ref().unwrap().0.rc)
		}else{ (zero, zero)};
		let pc_0 = vea[0].pc_i;
		let pc_0_val = field_to_usize(&pc_0);
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(ch,rc,&self.poseidon_config,b_full_mode,fq_bits,total_words);
		let z0_part2_hash = z0_part2.hash(&self.poseidon_config);
        let z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
		log_perf(job_id, log_level, &format!(
			"{} step 5: prep for proving steps words: {}, n_steps: {}: total_word_len: {}. ", phase_name,  words.len(), n_steps, total_wd_len) , &mut gt1);

		//6. build the nova instance
        let mut nova =
            FoldPotSuper::<E,P, C2G2, C1, GC1, C2, GC2, FC,
			CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &self.nova_param,
				self.circuits.clone(),
                z_0.clone(),
				self.circuits.len(), 
				pc_0_val,
				self.b_full_mode,
				ch,
				rc,
				total_words,
				Some(vec_grp_cmF)
				//None,
            )
            .unwrap();
		log_perf(job_id, log_level, &format!(
			"{} step 6: build nova. Cost depends on cs1e.len. Now proving ...", phase_name) , &mut gt1);


		//6. LOOP prove steps
        let mut rng = ark_std::test_rng();
		let mut idx = 0;
		let mut num_steps = 0;
		let _lk_len = self.lkup.get_size();
		//let mut wi = 0;
		let mut gtw2 = GTimer::new();
		let m7 = get_mem_usage_mb();
		let mut word_id = 1;
		let mut _start = 0; //global position in ENTIRE sequence for update lkup
							//share in each statement
		for word in iter_words3{
			let mut prev_adv = None;
			let mut prev_stmt = None;
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let word_info = &vec_word_info[word_id-1];
			let word_fname = &vec_word_fnames[word_id-1];
			log_perf(job_id, log_level+2, &format!("{} - Pass 3. START prove steps for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw2); 
			while remaining.len()>0{
				//6.1 compute the problem statement instance again
				// with the correct cmF
				let j = field_to_usize(&vea[idx].pc_i1);
				let circ = &self.circuits[j];
				let share_size = circ.get_stmt_config().lookup_share_size;
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();

				let res = circ.get_mapper().lock().unwrap()
					.gen_nd_advice(&frag, word_info, prev_adv, subseg_id - 1, job_id);
				assert!(res.is_ok(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id); 
				let cur_adv = res.unwrap();
				log_perf(job_id, log_level+1, &format!("-- Pass 3. gen advice for word_id: {}, seg_id: {}", word_id, subseg_id), &mut gtw2);

				let stmt_res = circ.get_mapper().lock().unwrap().build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, cur_adv.clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				let mut stmt = stmt_res.unwrap();
				log_perf(job_id, log_level+1, &format!("-- Pass 3. gen stmt"), 
					&mut gtw2);

				stmt.update_lookup(_start,_start+share_size, &self.lkup, &m_map);
				_start += share_size;
				log_perf(job_id, log_level+1, &format!("-- Pass 3. update lkup: share size: {}", share_size), &mut gtw2);

				//2.2. prove step
				let v_stmt = stmt.to_vec();
				let stmt_len = v_stmt.len();
				let other_inst = None;
				nova.pc_i = vea[idx].pc_i;
				nova.pc_i1 = vea[idx].pc_i1;
            	nova.prove_step(&mut rng, v_stmt, other_inst)
					.expect("prove step error");
				log_perf(job_id, log_level+1, &format!("-- Pass 3. prove_step cost for word_id: {}, seg_id: {}, stmt_len: {}", word_id, subseg_id, stmt_len), &mut gtw2);

				//2.3 update 
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
			}//end for while remaining word 
			word_id += 1;
			log_perf(job_id, log_level+2, &format!("{} - Pass 3. END prove steps for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw2); 
		} //for each word
		assert!(num_steps==vea.len(), "num_steps: {}, vea.len: {}", num_steps, vea.len());
        assert_eq!(C1::ScalarField::from(num_steps as u32), nova.i);
		let m8 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!(
			"{} step 6: PROVE STEPS done for n_steps: {}. total_word_len: {}. RAM increased: {} MB. Total RAM: {} GB.", phase_name,  n_steps, total_wd_len, if m8>m7 {m8-m7} else {0}, m8/1024) , &mut gt1);

		//4. generate the output
		let _verifier_param = self.nova_param.1.clone();

		//5. test and verify
		if b_debug{
        	let (r1, r2, r3, r4) = nova.instances();
        	FoldPotSuper::<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H>::verify(
				_verifier_param,
				z_0,
				nova.z_i.clone(),
				nova.i.clone(),
				r1, r2, r3, r4).unwrap();
		}
		log_perf(job_id, log_level, &format!(
			"{} step 7: verify. ", phase_name ) , &mut gt1);

		Ok((nova, num_steps, batch_prfs, claim_pack))

	}

	
}

// -- Utility Functions --
/// read all binary contents and return as a hex string
pub fn read_nibbles<F:PrimeField>(fpath: &str) -> Vec<F>{
    //1. read the file
    let mut file = File::open(fpath).expect(
        &format!("can't open file: {}", fpath));
    let metadata = metadata(fpath).expect("unable to read");
    let size = metadata.len() as usize;
    let mut buffer = vec![0; size];
    file.read(&mut buffer).expect("buffer overflow");

    //2. collet string
    let mut vres = vec![];
    for num in buffer{
        vres.push(num/16);
        vres.push(num%16);
    }

    //3. convert
	let vres2 = vres.iter().map(|x| F::from(*x)).collect::<Vec<F>>();
	vres2
}

/// write a line to a file (erase contents if it exists)
pub fn write_to_file(fname: &str, line: &str){
	if Path::new(fname).exists(){
		remove_file(fname).unwrap();
	}
    let mut fh = OpenOptions::new().create_new(true).write(true).open(fname)
		.expect(&format!("open {} failed", fname));
   	fh.write(line.as_bytes()).expect("write failed");
}


/// This function is the main workflow of foldpot.
/// It takes a sequence of circuits, and a sequence of words.
/// Run driver in two phases, builds the DeciderProof and verifies it.
/// Inputs: lkup which encodes the regex automata, 
/// jobs: a collection of jobs where each job has:
/// (1) vec_words: the vector of words to process,
/// (2) idx_individual_prf: the index of the SAMPLE individual proof to produce.
/// (3) the corresponding word_info for each word in vec_words.
///
/// NOTE: vec_circ should be ordered as required by Driver (see its doc)
pub fn foldpot_main<E:Pairing<G1=C1,G2=C2G2>,P:PairingVar<E,CF3<C2G2>>+std::fmt::Debug+Clone,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool>(
	lkup: Arc<LK>, //the lookup table defines the regex automatas
	vec_circ: Vec<Vec<FC>>,
	jobs: Vec<FoldPotJob<E::ScalarField>>,
) -> Result<(), Error>
where
	<E as Pairing>::ScalarField: ColEle,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1> + Clone + Send + Sync,
    //FC: SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, false>,
	LK: LookupTableTwoCol<C1::ScalarField> + 'static + Send + Sync,
    CS1: CommitmentScheme<C1, H, ProverParams = PedersenParams<C1>> +
		CommitmentScheme<C1, ProverParams=PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1, H>>::VerifierParams: Send + Sync,
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	<CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1, H>>::VerifierParams: Send + Sync,
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2, H>>::VerifierParams: Send + Sync,
    S: SNARK<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	<E as Pairing>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug + Send + Sync,
{
	//0. Fix the circuit with dummy statements
	// here we assume that each circuit can always handle
	// words of zeros, and set its dummy_statement for preprocess()
	// to build keys.
	let log_level: usize = LOG1;
	let mut gt_all = GTimer::new();
	log(0, log_level, &format!("===== fold_pot starts with {} jobs =====", 
		jobs.len()));
	let global_max_words = jobs.iter().map(|job| job.vec_words.len())
		.max().unwrap_or(0);
	let global_max_total_n = jobs.iter().map(|job| job.vec_words.iter()
		.map(|x| x.len()).sum::<usize>()).max().unwrap_or(0);

	let mut vec_circ = vec_circ.clone();
	let n_circ = vec_circ.iter().map(|row| row.len()).sum::<usize>();
	let mut id = 0;
	let (zero, one) = (C1::ScalarField::zero(), C1::ScalarField::one());
	let word_info = WordInfo::dummy();
	for i in 0..vec_circ.len(){
		for j in 0..vec_circ[i].len(){
			let circ = &mut vec_circ[i][j];
			let lk_share_size = circ.get_lkup_share_size();
			let prev_stmt = None;
			let wlen = circ.get_mapper().lock().unwrap().max_word_len();
			let frag = vec![zero; wlen];
			let prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>> = None; //fine to set None
			let r_advice= circ.get_mapper().lock().unwrap()
					.gen_nd_advice(&frag, &word_info, prev_adv, 0, 0); //use its own capacity
			assert!(r_advice.is_ok(), "\n\n===== **** ====== \nUNABLE to generate advice for circ at layer {} for full 0-word. This is a system-wide change needed. Needs to adjust capacity: {:#?}", i, r_advice);

			let advice = r_advice.unwrap();
			let ei = StatementExtraInfo::<C1::ScalarField>{
				total_words: one,
				word_id: one,
				subseg_id: one,
				total_word_len: C1::ScalarField::from(wlen as u32),
				total_word_segs: one,
				n_circ: C1::ScalarField::from(n_circ as u32),
				pc_i:  C1::ScalarField::from(id as u32),
				pc_i1:  C1::ScalarField::from(id as u32), //update later
				act_word_subseg_size: C1::ScalarField::from(wlen as u32),
				batch_r: zero,
				batch_v: zero,
				r_all_words: zero,
				r_kzg_len: zero,
				r_vec_r: zero,
				r_vec_v: zero,
				r_word_i: zero,
				accumulated_word_len: C1::ScalarField::from(wlen as u32),
			};//end constructor StatementExtraInfo
			circ.set_container_config(&advice);
			let stmt_res = circ.get_mapper().lock().unwrap()
				.build_statement(&frag, &prev_stmt, lkup.clone(), &ei, advice, //REMOVE LATER clone()
				lk_share_size, true, 0); //dummy mode
			assert!(stmt_res.is_ok());
			circ.set_dummy_stmt(stmt_res.unwrap());
			id += 1;
		}
	}
	log_perf(0, log_level, 
		&format!("FoldPot Step 1: build dummy stmt for all circs"), &mut gt_all
	);


	//2. create the driver1 for the 1st phase
	let poseidon_config_global = poseidon_canonical_config::<C1::ScalarField>();
	let b_full1 = false;
	let driver1 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,FC,S,LK,GM,H> 
	::new(poseidon_config_global.clone(), lkup.clone(), 
		vec_circ.clone(), rand::rngs::OsRng, b_full1, 
		global_max_total_n, global_max_words
	);
	log_perf(0, log_level, &format!("FoldPot: Step 2: set up driver 1"),
		&mut gt_all);

	//3. create the driver2 for Phase2 CyclePair Circ
	let n_circs_cp = 1;
	let circ_cyclepair = create_sigma_fold_pair::<C1::ScalarField, C1, CS1, LK, H>(n_circs_cp, poseidon_config_global.clone());
	let vec_circ_cp = vec![vec![ circ_cyclepair] ];
	let b_full2 = true;
	let lk_p2 = LK::new(vec![]);
	let lkup_p2 = Arc::new(lk_p2);
	let driver2 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, FoldPairMapper<CF1<C1>,LK>,H>,S,LK,FoldPairMapper<CF1<C1>,LK>,H>
		::new(poseidon_config_global.clone(), lkup_p2, vec_circ_cp, rand::rngs::OsRng, b_full2, global_max_total_n, global_max_words);
	log_perf(0, log_level, &format!("FoldPot: Step 3: set up driver 2.\n=== Now Execute All Jobs =====\n"), &mut gt_all);

	jobs.into_par_iter().enumerate().for_each(|(job_id, job)| {
		let res = (|| -> Result<(), Error> {
		//0. retrieve the words and word_info
	  	log(job_id, log_level, &format!("--- Job {} starts ---", job_id));
	  	let mut gt1 = GTimer::new();
	  	let vec_words = job.vec_words;
	  	let vec_words_info = job.vec_word_info;
	  	let idx_individual_prf = job.idx_individual_prf;
	  	let vec_word_fnames = job.vec_word_fnames;
	  	assert!(vec_word_fnames.len()==vec_words.len());
	  	let mut rng = rand::rngs::OsRng;
	  	let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();
	  	let max_total_n:usize = vec_words.iter().map(|x| x.len()).sum();

	  	//put in one block to avoid do two snarks at the same time to
	  	//save RAM.
	  	let (snark_proof_main,mainres,mainres_hash, g16_vk_main, 
				cyclepair_inputs,
	  			kzg_sum1, ch1, rc1, _randf,
	  			prf_kzg, kzg_all_com_ch, qa_nizk_vkey_hash1,
	  			com_all_w, r_all_w, mut batch_prf,
	  			mut batch_ver_param, batch_claims, b_check_lkup,
	  			driver1_poseidon_config, ind_prf
	  		) 
	  	= {
	  		//3. phase 1 pass 1
	  		let mut iter = vec_words.iter();
	  		let mut iter_2 = vec_words.iter();
	  		let mut iter_3 = vec_words.iter();
	  		let (nova1, _num_steps, batch_ind_prfs, batch_claims) 
	  		  = driver1.pass_all(
	  			"Phase 1",
	  			&mut iter,
	  			&mut iter_2, 
	  			&mut iter_3, 
	  			vec_words.len(), 
	  			idx_individual_prf, 
	  			&mut rng, 
	  			&vec_words_info,
	  			&vec_word_fnames,
				job_id
	  		)?;
	  		let Some((batch_prf, ind_prf)) = batch_ind_prfs.map(|x| (x.0, x.1))
	  			else {return Err(Error::Other("batch proof is none!".to_string()));};
	  		log_perf(job_id, log_level, &format!("FoldPot: Step 3: Phase 1: main circuits IVC PROVE STEPS (Folding) DONE. total_word_len: {}, steps: {}.", format_bytes(max_total_n * 31), _num_steps),
	  			&mut gt1);
	  	
	  		//5. generate the inputs for cyclepair
	  		let qa_nizk_pkey = driver1.nova_param.0
				.qa_pp.as_ref().expect("qa_pp null!"); 
	  		let qa_nizk_vkey = driver1.nova_param.1
				.qa_vp.as_ref().expect("qa_vp null!"); 
	  		let qa_nizk_vkey_hash = qa_nizk_vkey.hash(&driver1.poseidon_config);
	  		let qa_nizk_vkey_hash1 = qa_nizk_vkey_hash.clone();
	  		let (U_i1, W_i1, _r_Fr, _cmT)= nova1.gen_next_folded().unwrap();
	  		let (com_all_w, prf_qa_nizk, r_all_w, prf_kzg, kzg_all_com_ch) = 
				W_i1.gen_com_all_w_and_qa_nizk_prf::<E, CS1E, H>(
					&qa_nizk_pkey, 
					&driver1.nova_param.0.cs1e_pp, 
					&qa_nizk_vkey, &U_i1, &driver1.poseidon_config
			);
	  		let cyclepair_inputs = U_i1
	  			.generate_cyclepair_inputs::<E>(qa_nizk_pkey, qa_nizk_vkey,
	  				&com_all_w, &prf_qa_nizk, &poseidon_config); 
	  	
	  		//6. now bulid the main circuit, which execues
	  		//the main logic: verifies the ZkregPlus relation
	  		//and verifies the all witness + e_vec evaluates to a value
	  		//at a given random point
	  		// it later generates a cyclepair-input (a collection of
	  		// pairing equations to be passed to CyclePair circuit)
	  		let kzg_sum1 = nova1.zi_part2_inst.sum_kzg_eval_lk
	  					+ nova1.zi_part2_inst.sum_kzg_eval_word
	  					+ nova1.zi_part2_inst.sum_kzg_eval_others;
	  		let ch1 = nova1.zi_part2_inst.ch.clone();
	  		let rc1 = nova1.zi_part2_inst.rc.clone();
	  		let randf = C1::ScalarField::rand(&mut rng);
	  	
	  		let (snark_proof_main,mainres,mainres_hash, g16_vk_main) = {
	  			let main_circ = MainDeciderCircuit::from_nova::<FC>(nova1,
	  				com_all_w.clone(), r_all_w.clone(), randf).unwrap();
	  			let mainres = main_circ.res.clone();
	  			let mainres_hash = main_circ.res_hash.clone(); 
	  			log_perf(job_id, log_level, &format!("FoldPot Step 4: build MAIN decider circuit. MEM: {} GB", get_mem_usage()), &mut gt1);
	  	
	  			let (g16_pk, g16_vk) = {//to save ram, clone will be freed
	  				let (g16_pk, g16_vk) = S::circuit_specific_setup(
	  					main_circ.clone(), 
	  					&mut rng).unwrap();
	  				(g16_pk, g16_vk)
	  			};
	  			log_perf(job_id, log_level, &format!("FoldPot Step 5: setup Groth16. MEM: {} GB.",  get_mem_usage()), &mut gt1);
	  	
	  			let snark_proof_main: S::Proof = S::prove(&g16_pk, 
	  				main_circ, &mut rng)
	  				.map_err(|e| Error::Other(e.to_string())).unwrap();
	  			log_perf(job_id, log_level, &format!("FoldPot Step 6: Gen Groth16 Proof for MainCirc. MEM: {} GB.",  get_mem_usage()), &mut gt1);
	  	
	  			(snark_proof_main, mainres, mainres_hash, g16_vk)
	  		};
	  
	  		//7. prepare the other data.
	  		let mut batch_ver_param = driver1.batch_vk.clone().unwrap().clone();
	  		batch_ver_param.kzg_driver1 = Some(
	  			driver1.nova_param.1.cs1e_vp.clone());
	  		let b_check_lkup = driver1.layered_circs[0][0].is_check_lkup(); 
	  		let driver1_poseidon_config = driver1.poseidon_config.clone();
	  		(snark_proof_main, mainres, mainres_hash, g16_vk_main, 
	  			cyclepair_inputs,
	  			kzg_sum1, ch1, rc1, randf,
	  			prf_kzg, kzg_all_com_ch, qa_nizk_vkey_hash1,
	  			com_all_w, r_all_w, batch_prf, 
	  			batch_ver_param, batch_claims, b_check_lkup,
	  			driver1_poseidon_config, ind_prf
	  		)
	};


	//6. another three rounds for Phase2 CyclePair Circ its proof
	let vec_words = cyclepair_inputs.clone();
	let vec_word_fnames2 = (0..vec_words.len()).collect::<Vec<_>>()
	.iter().map(|i|
		format!("cyclepair inst {}", i)
	).collect::<Vec<String>>();
	let mut iter = vec_words.iter();
	let mut iter_2 = vec_words.iter();
	let mut iter_3 = vec_words.iter();
	let vec_word_info = vec![WordInfo::dummy(); vec_words.len()];
	let (nova2, _num_steps, _batch_prfs, _bt_claims) = driver2.pass_all(
		"Phase 2",
		&mut iter,
		&mut iter_2, 
		&mut iter_3, 
		vec_words.len(), 
		idx_individual_prf, 
		&mut rng, 
		&vec_word_info,
		&vec_word_fnames2, 
		job_id
	)?;

	let qa_nizk_pkey = driver2.nova_param.0.qa_pp.as_ref().expect("qa_pp null!"); 
	let qa_nizk_vkey = driver2.nova_param.1.qa_vp.as_ref()
		.expect("qa_vp null!").clone();
	let qa_nizk_vkey_hash = qa_nizk_vkey.hash(&driver2.poseidon_config);
	let (nova2_U_i1, nova2_W_i1, _nova2_r_Fr, _nova2__cmT)= 
		nova2.gen_next_folded().unwrap();
	let (nova2_com_all_w, nova2_prf_qa_nizk, nova2_r_all_w, nova2_prf_kzg, nova2_kzg_all_com_ch) = nova2_W_i1.gen_com_all_w_and_qa_nizk_prf::<E, CS1E, H>( &qa_nizk_pkey, &driver2.nova_param.0.cs1e_pp, &qa_nizk_vkey, &nova2_U_i1, &driver2.poseidon_config);
	log_perf(job_id, log_level, &format!("FoldPot: Step 7: Phase 2: cyclefold and cyclepair IVC PROVE STEPS (folding) DONE. num_steps: {}", _num_steps), &mut gt1);


	//8. now build up the CyclePair circuit which processes
	// the pairing equations generated by the first circuit (e.g., qa-nizk ones)
	// it uses the Phase1Ret.hash() to link with the output of
	// the MainCircuit
	let inp = CircPubInput{
			ch1: ch1,
			rc1: rc1,
			kzg_sum1: kzg_sum1,
			kzg_all_com_ch1: kzg_all_com_ch,
			eval_w_e1: prf_kzg.eval,
			mainres_hash: mainres_hash,

			kzg_all_com_ch2: nova2_kzg_all_com_ch,
			eval_w_e2: nova2_prf_kzg.eval,

			comE2: nova2_U_i1.vec_inst[0].cmE.clone(),
			comW2: nova2_U_i1.vec_inst[0].cmW.clone(),
			comF2: nova2_U_i1.vec_inst[0].cmF.clone(),

			qa_nizk_vkey_hash: qa_nizk_vkey_hash1, 
	};
	let (snark_proof_cp, g16_vk_cp) = {
		let cp_circuit = CyclePairCircuit
			::from_nova(nova2, 
				cyclepair_inputs, qa_nizk_vkey_hash.clone(), 
				driver2.poseidon_config.clone(),
				com_all_w, r_all_w, nova2_com_all_w, nova2_r_all_w, mainres,
				inp).unwrap(); 
		log_perf(job_id, log_level, &format!("FoldPot Step 8: build CyclePair circuit. MEM: {} GB", get_mem_usage()), &mut gt1);

		//9. set up the keys (maybe later can be cached)
		let (g16_pk, g16_vk) = {//to save ram, clone will be freed
			let (g16_pk, g16_vk) = S::circuit_specific_setup(
				cp_circuit.clone(), 
				&mut rng).unwrap();
			(g16_pk, g16_vk)
		};
		log_perf(job_id, log_level, &format!("FoldPot Step 9: setup Groth16 for CpCircuit. MEM: {} GB.",  get_mem_usage()), &mut gt1);

		//10. produce the groth16 snark
		let snark_proof_cp: S::Proof = S::prove(&g16_pk, cp_circuit, &mut rng)
			.map_err(|e| Error::Other(e.to_string())).unwrap();
		log_perf(job_id, log_level, &format!("FoldPot Step 10: Generate Groth16 proof. MEM: {} GB.",  get_mem_usage()), &mut gt1);

		(snark_proof_cp, g16_vk)
	};

	batch_prf.add_part2(
		com_all_w.clone(),
		kzg_all_com_ch.clone(),
		prf_kzg.clone(),

		nova2_com_all_w.clone(),
		nova2_kzg_all_com_ch,
		nova2_prf_kzg,

		nova2_U_i1.vec_inst[0].cmE.clone(),
		nova2_U_i1.vec_inst[0].cmW.clone(),
		nova2_U_i1.vec_inst[0].cmF.clone(),
		QaNizkProof::<E>{prf: nova2_prf_qa_nizk},

		snark_proof_main,
		snark_proof_cp,
		mainres_hash,
	);
	log_perf(job_id, log_level, &format!("FoldPot Step 11: Assmeble Batch Proof for CpCircuit. MEM: {} GB.",  get_mem_usage()), &mut gt1);

	//11. verify the batch proof
	let qa_nizk_vkey2 = driver2.nova_param.1.qa_vp.as_ref().expect("qa_vp null!").clone(); 
	batch_ver_param.kzg_driver2 = Some(driver2.nova_param.1.cs1e_vp.clone());
	let (batch_claim, ind_claim, _) = batch_claims.unwrap();
	let opt_kzg_sum1 = if b_check_lkup {None} else {Some(kzg_sum1)};
	assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_batch(
		&batch_ver_param,
		Some(qa_nizk_vkey_hash1),
		Some(qa_nizk_vkey2.clone()), //needs to be from nova qa_nizk
		Some(g16_vk_main),
		Some(g16_vk_cp),
		&batch_claim,
		&batch_prf, 
		&driver1_poseidon_config,
		true, //now full verification
		opt_kzg_sum1
	)); //note
	log_perf(job_id, log_level, &format!("FoldPot Step 12: Verify Batch Proof."), 
		&mut gt1);

	//12. verify the individual proof
	assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(
		//&driver1.batch_vk.as_ref().unwrap(),
		&batch_ver_param,
		idx_individual_prf, 
		&ind_claim,
		&batch_prf, 
		&ind_prf)
	);
	log_perf(job_id, log_level, &format!("FOLDPOT Step 13. Verify Individual Proof."), 
		&mut gt1);
	log_perf(job_id, log_level, &format!("**** Job {} Complete ***** MEM: {} GB.", job_id, get_mem_usage()), &mut gt1);

	Ok(())
	})();
	if let Err(e) = res {
		log(job_id, ERR, &format!("Job {} FAILED with error: {:?}", job_id, e));
	}
	});

	log_perf(0, log_level, "===== all fold_pot jobs finished =====", &mut gt_all);
	Ok(())
}


#[cfg(test)]
pub mod tests_driver{
	use super::*;	
    use crate::commitment::{pedersen::Pedersen,kzg::KZG};
    use crate::transcript::poseidon::poseidon_canonical_config;
	use crate::folding::foldpot::{
		sigma_ir1cs::{
			GadgetMapper,SigmaGadget,WitnessSigmaIR1CSVar,
			WitnessSigmaIR1CSConfig, StatementConfig,
			StatementInst,LookupTableTwoCol_Inst,
			DummyNdAdvice,DummyCapacity 
		},
		utils::{Timer,expand2},
		container_config::{ContainerConfig},
	};
	use ark_groth16::Groth16;
	use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
	use ark_r1cs_std::{
		alloc::{AllocVar},
		eq::EqGadget,
		fields::{fp::FpVar},
		R1CSVar, 
	};
	use std::{sync::Arc};


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
	//type FC = SigmaIR1CS_Inst<Fr,Projective,Pedersen<Projective>,LK, GM>;
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
		fn get_container_config(&self)->ContainerConfig{
			unimplemented!("not needed. legacy code")
		}
		fn get_name(&self)->&str{
			"SumGadget"
		}

		/// set the container cfg. This is only needed for those gadgets
		/// in SED approach
		fn set_container_cfg(&mut self, _cfgs_context: Arc<Vec<ContainerConfig>>, _idx: usize){
			unimplemented!("not needed. handled by legacy code");
		}

		/// Get the instructions for build its statement.
		/// NOTE: this is only needed for those used in SedGadgetMapper.
		/// Others are handled by legacy code in their gadget mapper.
		fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the sizes of inp/oup/data/failed/discharged sigs
		/// to append to the
		/// buffer of GadgetMapper.
		fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the estimated cost in number of constraints
		fn est_cost(&self)->usize{
			self.n * 5	
		}

		/// statment `(x;w;sum_in;sum_out)` where x has n elements, w has
		/// n elements. msg1, and msg1 are dummy single element.
		/// msg3 is the w part retrieved from the statment
		fn get_msg_size(&self) -> (usize, usize, usize, usize){
			//statment part has n elements for x, n for w, and 2 extra for
			//sum_in and sum_out
			(2*self.n + 2, 1, 1, self.n)
		}

		fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) -> Vec<F>{
			vec![F::one()]	// dummy
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
			wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
			_word_id: FpVar<F>, _subsig_id: FpVar<F>) 
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
			let zeroVar= FpVar::<F>::new_constant(cs.clone(), F::zero() )?;
			let twoVar= FpVar::<F>::new_constant(cs.clone(), F::from(2u32))?;
			for i in 0..n{
				let b_add = w[i].is_eq(&twoVar)?;
				let to_sum = b_add.select(&x[i], &zeroVar)?; 
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
		fn set_container_config(&mut self, _advice: &Arc<dyn NdAdvice + Send + Sync>){ 
			//not needed, handled by legacy code
		}

		/// the capacity is the word length that can be handled by
		/// the circuit
		fn get_capacity(&self)->Arc<dyn Capacity + Send + Sync>{
			let word_seg_len = self.max_word_len();
			Arc::new(DummyCapacity{word_seg_len})
		}

		fn gen_nd_advice(&self, word: &Vec<F>, _word_info: &WordInfo,
			_prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, _seg_id: usize, _job_id: usize)
			-> Result<Arc<dyn NdAdvice + Send + Sync>, Error>{

			if word.len()<=self.max_word_len(){
				let w0_val = field_to_usize(&word[0]);
				if (w0_val%2==1) != self.b_odd { 
					Err( 
						Error::CapErr(
							vec![(format!("w0_val%2==1 != b_odd"), word.len())])
					)
				}else{
					Ok( Arc::new(DummyNdAdvice{}))
				}
			}else{ 
				Err( Error::CapErr(vec![(format!("max_word_len"), word.len())]))
			}
		}


		fn get_name(&self) -> String{
			if self.b_odd {"OddSum".to_string()} else {"EvenSum".to_string()}
		}

		fn max_word_len(&self)->usize{ 
			if self.b_odd {1} else {2} 
		}

		fn get_gadgets(&self) -> Vec<Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>>{ 
			let gadget = if self.b_odd {SumGadget::<F>{_f: PhantomData, n: 1}}
				else {SumGadget::<F>{_f: PhantomData, n:2}};
			vec![Arc::new(Mutex::new(gadget))]
		}

		/// expecting [x_1] or [x_1, x_2], depending on if
		/// its odd/even case. If x_1 is not even (for even circ), throw error
		/// similarly throw error for odd circ if x_1 is not odd.
		/// This is for testing the "best fit" circ in multiple non-uniform
		/// circ environment in supernova.
		fn build_statement(&self, word: &Vec<F>, prev_wit: &Option<StatementInst<F,LK>>, lkup: Arc<LK>, ea: &StatementExtraInfo<F>, _advice: Arc<dyn NdAdvice + Send + Sync>, _lkup_share_size: usize, _b_dummy: bool, _job_id: usize) 
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
				let res = lkup.find(two, word[i]);
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
			let failed_sigs = vec![F::zero()];
			let discharged_sigs = vec![F::zero()];
			let mtbl_sigs= vec![F::one()]; //coz 0 appeared once in failed sigs
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

				failed_sigs,
				discharged_sigs,
				mtbl_sigs,

				_lk: PhantomData,
			};
				
			Ok(stmt)
		}

		fn gen_statement_structure(&self, _lookup_share_size: usize) -> 
			(usize, StatementConfig, Vec<Vec<(usize,usize)>>, 
				Vec<((usize,usize),(usize,usize))>, 
				Vec<usize>){
			//1. a sample statemnet structure
			let input_size = 1;
			let output_size = 1;
			let word_subseg_size = 2;
			let data_size = 2;
			let lookup_share_size = 4; //overwrite it here keep the original size
			let failed_sig_size = 1;
			let discharged_sig_size = 1;  //dummy sigs table of len 1.
			let b_cyclepair = false;
			let cfg = StatementConfig::new(
				input_size, output_size, word_subseg_size,
				data_size, lookup_share_size,
				failed_sig_size, discharged_sig_size,
				b_cyclepair
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

	#[test]
	fn test_iterator(){
		//1. create instance
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
		let lkup = Arc::new(lk.clone());
		let (odd_mapper, even_mapper) =  
			(SumMapper::<Fr,LK>::new(true), SumMapper::<Fr,LK>::new(false));
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let lkup_share_size = 4;
		let b_check_lkup = true;
		let vec_circ = vec![
			vec![
				SigmaIR1CS_Inst::<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>::new_adv("oddsum".to_string(), poseidon_config.clone(), Arc::new(Mutex::new(odd_mapper)), false, lkup_share_size, true, b_check_lkup).unwrap(),
			],
			vec![
				SigmaIR1CS_Inst::<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>::new_adv("evensum".to_string(), poseidon_config.clone(), Arc::new(Mutex::new(even_mapper)), false, lkup_share_size, true, b_check_lkup)
			.unwrap()]
		];
		t1.prt("Step 0. setup sigma_ir1cs odd/eve sum instance");


		//2. create the driver
		// as lookup table 2 contains 0 to 4 will compute sum of
		// 1 + 2 +  4 + 2 + 2 = 11
		let vec_words= vec![
			vec![Fr::from(1), Fr::from(2), Fr::from(100)],
			vec![Fr::from(4), Fr::from(2), From::from(2)]
		];
		let vec_word_fnames = vec![
			format!("file1"),
			format!("file2"),
		];
		let sample_individual_prf = 1; //generate individual proof 1
		let vec_word_info = vec![WordInfo::dummy(); vec_words.len()];
		let jobs = vec![FoldPotJob{
			vec_words,
			vec_word_info,
			vec_word_fnames,
			idx_individual_prf: sample_individual_prf,
		}];
		let _prf = foldpot_main::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>,S,LK,SumMapper<Fr,LK>, false>(lkup, vec_circ, jobs);
	}

}






