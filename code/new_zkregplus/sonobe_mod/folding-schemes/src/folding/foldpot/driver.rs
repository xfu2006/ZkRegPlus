/* 
	Created 08/27/2024 
	Modified 12/25/2024: added snark_rand_input structure
	Modified 01/08/2025: added main workflow foldpot_main
	Modified 11/24/2025: merge pass1 to pass3 to save memory
*/

extern crate utils;
use utils::{logger::{log, log_perf, LOG1,LOG_LEVEL,LOG2}, timer::Timer as GTimer};
use std::{
    //process::{Stdio,Command},
    //fs::{read_to_string,OpenOptions,remove_file,File,metadata},
	fs::{metadata,File,OpenOptions,remove_file},
    path::{Path},
    io::{Write,Read},
	collections::{HashMap},
	time::Instant,
};
use std::{rc::Rc, cell::RefCell, fmt::{Debug,Formatter}};
use ark_std::{Zero,One};
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
			qa_nizk::{QaNizkProof},
			utils::{Timer,get_mem_usage,get_mem_usage_mb,format_bytes},
			circuits_super::{field_to_usize},
			mod_super::{PreprocessorParamFoldPotSuper,FoldPotSuper,
				compute_step_hc_cmF_adv},
			sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,StatementExtraInfo,GadgetMapper,Capacity,NdAdvice,WordInfo},
			sigma_cyclepair::{create_sigma_fold_pair,FoldPairMapper},
			//decider_eth_super::{DeciderFoldPotSuper},
			decider_eth_circuit_super::{TwoPhaseDeciderEthCircuitSuper, TwoPhaseCircInput},
			batch_proc::{BatchProcessorProverParams,BatchProcessorVerifierParams,BatchProcessor,BatchClaim,BatchProof,IndividualClaim,IndividualProof,SnarkAdvice,SnarkRandInput}
		}
	},
};
use core::marker::PhantomData;
use crate::frontend::FCircuit;
use crate::{FoldingScheme};
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
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    // CS1E is a KZG commitment, where challenge is C1::Fr elem
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
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
	lkup: Rc<RefCell<LK>>,
	/// the prover/verifier parameters
	pub nova_param: (<FoldPotSuper<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H> as FoldingScheme<C1,C2,FC>>::ProverParam, <FoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK,GM, H> as FoldingScheme<C1,C2,FC>>::VerifierParam),

	/// the decidider parameters
	/*
	pub decider_param: 
		(<DeciderFoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, S, FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>,LK> as DeciderTrait<C1,C2,FC,FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>>>::ProverParam,
		<DeciderFoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, S, FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>,LK> as DeciderTrait<C1,C2,FC,FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,LK>>>::VerifierParam),
	*/

	pub batch_param: Option<(BatchProcessorProverParams<'c,E>,
		BatchProcessorVerifierParams<'c,E,CS1E,H>)>,

	/// when true, the cyclepair instance is supported
	pub b_full_mode: bool,

	/// phantom data
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
}



impl <'c, E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool> Debug for
Driver <'c, E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, H> 
where
//    C1: CurveGroup,
 //   C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
	/*
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	*/
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS1: CommitmentScheme<C1, H, ProverParams = PedersenParams<C1>>,
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
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
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1,H, ProverParams = PedersenParams<C1>>,
    CS1E: CommitmentScheme<
        C1,H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
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
	  lkup_inp: Rc<RefCell<LK>>,
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
		let _b_debug = true;
		let layered_circuits = F_circuits;
		let circuits = layered_circuits.concat(); 
		let size_F = circuits.iter().map(|f| f.get_size_f())
			.collect::<Vec<usize>>();
		if b_perf{
			log_perf(log_level, &format!("Driver New: Step 1: foldpot keys"), 
				&mut gt1);
			for i in 0..size_F.len(){
				log(log_level, &format!(" -- circ {} size: {}", i, size_F[i]));
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
		log_perf(log_level, &format!(
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
		log_perf(log_level, &format!(
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
		log_perf(log_level, &format!(
			"Driver New: Step 3.5: create default z0"), 
			&mut gt1);

		//4. set up the batch processor if it is NOT full mode (1st stage)
		let max_w_lk = if max_total_n > lkup_inp.borrow().get_size() 
			{max_total_n+1} else {lkup_inp.borrow().get_size()+1};
		let batch_param = Some(BatchProcessor::<E,LK,S,CS1E,H>
				::setup(&mut rng, max_w_lk, n_words,
				poseidon_config.clone()));

		log_perf(log_level, &format!(
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
			batch_param: batch_param,

			_gc1: PhantomData,
			_c2: PhantomData,
			_gc2: PhantomData,
			_cs2: PhantomData,
			_s: PhantomData,

			b_full_mode: b_full_mode, }
	}


	/// Given a word, and given its circuits, plan the steps to
	/// prove the word (free of malware sigs). Use estimate of
	/// cost to determine the pc_i of each step.
	/// Returns:
	///( num_steps, 
	///      Vec<PCI>, 
	///      Vec<size of word seg>, 
	///      Vec<Capacity Needed for circs[pci]>,
	///      Vec<Advice for the circuits[pci]>
	///)
	/// NOTE: theoretically, we could generate it while building
	/// statement, however, it's going to slow down the folding.
	/// IDEALLY, we should generate as much info as possible,
	/// so build_statement will be most likely copying over info.
	/// TO save memomry, b_save_nd_adivce indicates whether
	/// to push advice into vec<nd_advice>
	pub fn plan_nd_advice(&self, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Rc<dyn Capacity>>, Vec<Rc<dyn NdAdvice>>),Error>{
			let mut gt1 = GTimer::new();
			log_perf(log_level, &format!("Entering plan_nd_advice, layers: {}, word.len(): {}.", self.layered_circs.len(), word.len()), &mut gt1);
			let mut remaining = word.clone();
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
			let mut vec_pci = vec![];
			let mut vec_size = vec![];
			let mut vec_cap = vec![];
			let mut vec_adv:Vec<Rc<dyn NdAdvice>> = vec![];
			log_perf(log_level, &format!("plan_nd_advice step 1: check circs."),
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
			let mut b_found = false;
			let mut selected_layer = 0;
			for layer_id in 0..self.layered_circs.len(){
				//2.1.1 try generate advice by the first circ
				// without any resource limits
				let layer = &self.layered_circs[layer_id];
				let circ1 = &layer[layer.len()-1];
				//we assume all circs have the same max_word_len
				let max_word_len = circ1.get_mapper().borrow().max_word_len();
				let word_len = if max_word_len>remaining.len(){
					remaining.len()}else {max_word_len};
				let word = remaining[0..word_len].to_vec();
				#[cfg(test)]{
					for circ in layer{assert!(circ.get_mapper().borrow().
						max_word_len()==max_word_len);
					}
				}
				let prev_adv = if vec_adv.len()==0 {None}
					else {Some(vec_adv[vec_adv.len()-1].clone())};
				let res = circ1.get_mapper().borrow()
					.gen_nd_advice_no_limit(&word, &word_info, prev_adv);
				if !res.is_some() {
					//quick elimination of apparent non-working layer
					//this is usually quickly decided by looking at
					//word_info in gen_nd_advice_no_limit
					continue;
				}

				//if structure wise ok, still need to check details
				//of buffer capacity ok, so do have to run a real
				//instance of capacity check
				let (cap, _advice) = res.unwrap();
				let circ = &layer[0];
				if circ.get_mapper().borrow()
					.get_capacity().can_satisfy(&cap){
					b_found = true;
					selected_layer = layer_id;
					break;
				}
			}
			assert!(b_found, "UNABLE to find any layer of circuits working!");
			log_perf(log_level, &format!("plan_nd_advice step 2: select layer. selected layer: {}.", selected_layer), &mut gt1);

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
					let max_word_len = circ.get_mapper().borrow()
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
				let mut last_res = None;
				let mut b_found = false;
				for idx in min_id..layer.len(){
					//for every word_len try generating the unlimited resource
					//request
					let circ = &layer[idx];
					let max_word_len = circ.get_mapper().borrow()
						.max_word_len();
					let word_len = if max_word_len>remaining.len(){
						remaining.len()}else {max_word_len};
					let word = remaining[0..word_len].to_vec();
					let prev_adv = if vec_adv.len()==0 {None}
						else {Some(vec_adv[vec_adv.len()-1].clone())};
					if last_word_len!=word_len {
						last_word_len = word_len;
						last_res = circ.get_mapper().borrow()
						  .gen_nd_advice_no_limit(&word, &word_info, prev_adv);
					}
					assert!(last_res.is_some());
				
					//verify the circ does can satisfy the request
					if circ.get_mapper().borrow().get_capacity()
						.can_satisfy(&last_res.as_ref().unwrap().0){
						let (cap, advice) = last_res.unwrap();
						let pci = vec_start[selected_layer] + idx;
						vec_pci.push(pci);
						vec_size.push(word_len);
						vec_cap.push(cap);
						if b_save_advice{ //to save memory
							//advice will then have to be re-generated later.
							vec_adv.push(advice);
						}
						remaining = remaining[word_len..].to_vec();
						b_found = true;
						break;
					}
					if b_found {break;}
				}
				assert!(b_found, "CANNOT find satisfying circ for remaining length: {}!", remaining.len());
			}//end of while remaining loop
			log_perf(log_level, &format!("plan_nd_advice step 3: gen advice and try each circ. circs: {}, wordlen: {}.", vec_pci.len(), format_bytes(word.len()*31)), &mut gt1);

			Ok( (vec_pci.len(), vec_pci, vec_size, vec_cap, vec_adv  ))
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
	pub fn pass_one(&mut self, 
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		idx_ind_proof: usize,
	  	mut rng: impl RngCore +  CryptoRng,
		vec_word_info: &Vec<WordInfo>) ->
		(Vec<StatementExtraInfo<C1::ScalarField>>, HashMap<usize,usize>,
		 Vec<Vec<Rc<dyn NdAdvice>>>,
		 Option<(BatchClaim<E>, IndividualClaim<E>, SnarkAdvice<E::ScalarField>
		)>){
		//0. generate the claim first
		let log_level = LOG2;
		let mut t2 = Timer::new("PassOne", 1);
		let words = {
			iter_words2.map(|v| v.to_vec())
			.collect::<Vec<Vec<C1::ScalarField>>>()
		};
		t2.prt(&format!("step 1: word len: {}", words.len()));

		let batch_pack = if !self.b_full_mode{
			assert!(self.batch_param.is_some());
			let pk = &self.batch_param.as_ref().unwrap().0;
			let _vk = &self.batch_param.as_ref().unwrap().1;
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
			collect::<Vec<Rc<RefCell<GM>>>>();
		let mut vec_advice = vec![];
		let mut prev_stmt = None;
		let lkup_len= self.lkup.borrow().get_size();
		let mut total_lkup_covered = 0;
		for word in iter_words{
			//2.1 first try out and determine the length info for each
			let mut remaining = word.clone();
			let mut subseg_id = 0;
			let total_word_len = word.len();
			let mut acc_wd_len = 0;
			let _mapper = self.circuits[0].get_mapper();
			let (steps, vec_pci, vec_len, _vec_cap_req, advice) = self.plan_nd_advice(log_level+1, true, &word, &vec_word_info[word_id-1]).expect("Planning advice fails!"); 
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
					assert!(circ.get_mapper().borrow().get_capacity()
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
				let stmt_res = circ.get_mapper().borrow().build_statement(
					&frag, &prev_stmt, self.lkup.clone(), &ei,
						advice[subseg_id-1].clone(), lk_share_size, false);
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
		vec_advice: &Vec<Vec<Rc<dyn NdAdvice>>>)
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
		let lk_len = self.lkup.borrow().get_size();
		println!("DEBUG USE 6702: lk_len: {}", lk_len);
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
				let stmt_res = circ.get_mapper().borrow().build_statement(
					&frag, &prev_stmt, self.lkup.clone(), ei, 
					vec_advice[wi][subseg_id-1].clone(),
					share_size, false);
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
		vec_advice: &Vec<Vec<Rc<dyn NdAdvice>>>)
	-> (FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E, LK, GM, H>,
		usize, Option<(BatchProof<E,S>,IndividualProof<E>)>
			)
	{

		let mut t1 = Timer::new("pass_three", 1);
		//1. build the batch proof and individual proof
		let batch_prfs = if !self.b_full_mode{
			let words = {
				iter_words2.map(|v| v.to_vec())
				.collect::<Vec<Vec<C1::ScalarField>>>()
			};
			assert!(self.batch_param.is_some());
			let pk = &self.batch_param.as_ref().unwrap().0;
			let vk = &self.batch_param.as_ref().unwrap().1;
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
				None, None, None,
				&global_claim, &batch_proof, &self.poseidon_config, 
				false)); //note part2 of the proof will be checked later
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
		let _lk_len = self.lkup.borrow().get_size();
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
				let stmt_res = circ.get_mapper().borrow().build_statement(
						&frag, &prev_stmt, self.lkup.clone(), 
						ei, vec_advice[wi][subseg_id].clone(), share_size,
						false);
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
	pub fn pass_all(&mut self, 
		phase_name: &str, //below 3 copies of the same iterator
		iter_words: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words2: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		iter_words3: &mut dyn Iterator<Item = &Vec<C1::ScalarField>>,
		total_words: usize,
		idx_ind_proof: usize,
	  	mut rng: impl RngCore +  CryptoRng,
		vec_word_info: &Vec<WordInfo>) 
	-> (
		FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E, LK, GM, H>,
		usize, 
		Option<(BatchProof<E,S>,IndividualProof<E>)>,
	    Option<(BatchClaim<E>, IndividualClaim<E>, 
			SnarkAdvice<E::ScalarField>)>
		){
		//0. generate the claim first
		//estimate: 700M data = 700M/31 = 23M field elements in words
		//given 62 nibbles per word.
		//words = 23M * 32 byte = 700M data
		//each claim is small, up to 300 claims. So small.
		let log_level = LOG2;
		let b_debug = true;
		let mut gt1 = GTimer::new();
		let m1 = get_mem_usage_mb(); 
		let words = {
			iter_words2.map(|v| v.to_vec())
			.collect::<Vec<Vec<C1::ScalarField>>>()
		};
		let _n_words = words.len();
		let total_wd_len = words.iter().map(|x| x.len()).sum::<usize>();

		let claim_pack = if !self.b_full_mode{
			assert!(self.batch_param.is_some());
			let pk = &self.batch_param.as_ref().unwrap().0;
			let _vk = &self.batch_param.as_ref().unwrap().1;
			let (global_claim, ind_claims, snark_inp) = 
				BatchProcessor::<E,LK,S,CS1E,H>::gen_claims(pk, &mut rng, &words, self.lkup.clone()).unwrap();
			Some( (global_claim, ind_claims[idx_ind_proof].clone(), snark_inp) )
		}else{
			None
		};
		let m2 = get_mem_usage_mb();
		let snark_inp = if !self.b_full_mode
			{claim_pack.as_ref().unwrap().2.clone()}
			else {SnarkAdvice::empty(&words)};
		log_perf(log_level, &format!(
			"{} step 1: generate batch/ind claims. mem: {} GB, increased mem: {} MB, for words: {}, total_word_len: {} packed fields.", phase_name, m2/1024, m2-m1, total_words, total_wd_len), 
			&mut gt1);

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
		log_perf(log_level, &format!(
			"{} step 2: generate z0", phase_name), &mut gt1);


		//------------------------------------------
		//2. PASS1-2 combined: while loop to process words one by one
		// figure out the num_steps (and reset in self)
		// compute the final hash_cmF
		//------------------------------------------
		let mut word_id = 1;
		let mut vec_grp_cmF = vec![]; //does not cost much to save
			//estimate 64 bytes * 700MB/128kb = 
			//64 * 5.6k = 330kb,
			//so we can use it to cut prove_step time to avoid computing

		let n_circ = self.circuits.len();
		let _vec_mapper= self.circuits.iter().map(|c| c.get_mapper()).
			collect::<Vec<Rc<RefCell<GM>>>>();
		let lkup_len= self.lkup.borrow().get_size();
		let mut total_lkup_covered = 0;
		let m3 = get_mem_usage_mb();
		let mut gtw = GTimer::new();
		let mut hash_cmF= C1::ScalarField::zero();
		for word in iter_words{
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
			let (steps, vec_pci, vec_len, _vec_cap_req, _advice) = self.plan_nd_advice(log_level+2, false, &word, word_info).expect("Planning advice fails!"); //note: empty advice will be returned
			log_perf(log_level+2, &format!("{} decide circ alloc for word_id: {}, word_len: {}. ", phase_name, word_id, format_bytes(total_word_len*31)), 
				&mut gt2);
			for i in 0..steps{
				//2.1 set up params
				let pc_i = if i==0 {0} else {vec_pci[i-1]};
				let pc_i1 = vec_pci[i]; //this is actually pc_i1 for this circ
				let circ = &self.circuits[pc_i1];
				let cs_pp = &self.nova_param.0.vec_pp[pc_i1].cs_pp;
				let poseidon_config = &self.nova_param.0.vec_pp[0].poseidon_config; //to imitate what FoldPotSuper.init_adv takes vec_pp[0].poseidon_config
				let _max_len = circ.max_word_len();
				let act_len = vec_len[i];
				acc_wd_len += act_len;
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();
				#[cfg(test)]{
					//use crate::folding::foldpot::sigma_ir1cs::{Capacity};
					assert!(act_len<=_max_len);
					let rc_cap = _vec_cap_req[i].clone();
					assert!(circ.get_mapper().borrow().get_capacity()
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
				log_perf(log_level+2, &format!("-- For subseg_id: {} gen_statment_extra_info.", subseg_id), &mut gt2);

				//2.3 generate the advice and statement
				//need to build the statement to fill the m_map
				let res = circ.get_mapper().borrow()
					.gen_nd_advice_no_limit(&frag, word_info, prev_adv);
				assert!(res.is_some(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id); 
				let cur_adv = res.unwrap().1;

				log_perf(log_level+2, &format!("-- For subseg_id: {} gen_advice.", subseg_id), &mut gt2);
				let stmt_res = circ.get_mapper().borrow().build_statement(
					&frag, &prev_stmt, self.lkup.clone(), &ei,
					//	advice[subseg_id-1].clone(), 
						cur_adv.clone(),
						lk_share_size, false);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				log_perf(log_level+2, &format!("-- For subseg_id: {} build stmt.", subseg_id), &mut gt2);
				let stmt = stmt_res.unwrap();
				stmt.fill_lkup_mvec(&mut m_map, &self.lkup); //needed here!

				//2.4 update the hash_cmF
				let res =  compute_step_hc_cmF_adv
						::<C1,LK,CS1,GM,FC,H>(
						hash_cmF, &stmt, circ, cs_pp, poseidon_config)
						.expect("compute step hc cmF err");
				hash_cmF = res.0;
				vec_grp_cmF.push(res.1);

				//2.5 making updates
				let ea = stmt.to_extra_info();
				vec_res.push(ea);
				prev_stmt= Some(stmt);
				subseg_id +=1;
				total_lkup_covered += lk_share_size;
				log_perf(log_level+2, &format!("-- For subseg_id: {} gen_cmf and update. ", subseg_id), &mut gt2);
			}

			log_perf(log_level+1, &format!("{} generate advice and com_F for word: {} of size: {}.", phase_name, word_id, format_bytes(total_word_len*31)), 
				&mut gtw);
			word_id +=1;
		}
		let m4 = get_mem_usage_mb();
		assert!(vec_grp_cmF.len()==vec_res.len());
		assert!(total_lkup_covered >= lkup_len, "total: {}, lkup_len: {}", total_lkup_covered, lkup_len);
		log_perf(log_level, &format!(
			"{} step 3: dispatch w and generate cmF, mem: {} MB for total_word_len: {}: ", phase_name, m4-m3, format_bytes(total_wd_len*31))
			, &mut gt1);

		//------------------------------------------
		//3. PASS-3: now do the prove_step
		//------------------------------------------
		let m5 = get_mem_usage_mb();
		let vea = vec_res; //just rename var for the code from pass_three
		let n_steps = vea.len();
		let batch_prfs = if !self.b_full_mode{
			assert!(self.batch_param.is_some());
			let pk = &self.batch_param.as_ref().unwrap().0;
			let vk = &self.batch_param.as_ref().unwrap().1;
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
				None, None, None,
				&global_claim, &batch_proof, &self.poseidon_config, 
				false)); //note part2 of the proof will be checked later
			let ind_prf = BatchProcessor::<E,LK,S,CS1E,H>::prove_individual(pk, 
				&snark_inp, &words, &ind_claim,
				idx_ind_proof);
			let _res = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(vk, idx_ind_proof, &ind_claim, &batch_proof, &ind_prf);
			#[cfg(test)] {assert!(_res);}
			Some((batch_proof, ind_prf))
		}else{
			None
		};
		let m6 = get_mem_usage_mb();
		log_perf(log_level, &format!(
			"{} step 4: generate batch prf, mem: {} MB for words: {}, n_steps: {}: ", phase_name, m6-m5, words.len(), n_steps) , &mut gt1);

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
		log_perf(log_level, &format!(
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
				//Some(vec_grp_cmF)snark_inp
				None,
            )
            .unwrap();
		log_perf(log_level, &format!(
			"{} step 6: build nova. Cost depends on cs1e.len. Now proving ...", phase_name) , &mut gt1);


		//6. LOOP prove steps
        let mut rng = ark_std::test_rng();
		let mut idx = 0;
		let mut num_steps = 0;
		let _lk_len = self.lkup.borrow().get_size();
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

				let res = circ.get_mapper().borrow()
					.gen_nd_advice_no_limit(&frag, word_info, prev_adv);
				assert!(res.is_some(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id); 
				let cur_adv = res.unwrap().1;

				let stmt_res = circ.get_mapper().borrow().build_statement(
						&frag, &prev_stmt, self.lkup.clone(), 
						ei, cur_adv.clone(), share_size,
						false);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				let mut stmt = stmt_res.unwrap();
				//NOTE: should not do update_lookup as it
				//make duplicates counting of lookup elements for a second time
				stmt.update_lookup(_start,_start+share_size, &self.lkup, &m_map);
				_start += share_size;
				log_perf(log_level+1, &format!("-- gen advice for word_id: {}, seg_id: {}", word_id, subseg_id), &mut gtw2);

				//2.2. prove step
				let v_stmt = stmt.to_vec();
				let stmt_len = v_stmt.len();
				let other_inst = None;
				nova.pc_i = vea[idx].pc_i;
				nova.pc_i1 = vea[idx].pc_i1;
            	nova.prove_step(&mut rng, v_stmt, other_inst)
					.expect("prove step error");
				log_perf(log_level+1, &format!("prove_step for word_id: {}, seg_id: {}, stmt_len: {}", word_id, subseg_id, stmt_len), &mut gtw2);

				//2.3 update 
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
			}//end for while remaining word 
			word_id += 1;
		} //for each word
		assert!(num_steps==vea.len(), "num_steps: {}, vea.len: {}", num_steps, vea.len());
        assert_eq!(C1::ScalarField::from(num_steps as u32), nova.i);
		let m8 = get_mem_usage_mb();
		log_perf(log_level, &format!(
			"{} step 6: PROVE STEPS done for n_steps: {}. total_word_len: {}. RAM increased: {} MB. Total RAM: {} GB.", phase_name,  n_steps, total_wd_len, m8-m7, m8/1024) , &mut gt1);

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
		log_perf(log_level, &format!(
			"{} step 7: verify. ", phase_name ) , &mut gt1);

		(nova, num_steps, batch_prfs, claim_pack)

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
/// Inputs: lkup which encodes the regex automata, vec_circ: the
/// circ which performs checks, vec_words: the vector of words to process,
/// idx_individual_prf: the index of the SAMPLE individual proof to produce.
///
/// NOTE that this function can be better streamlined into three parts:
/// set up the keys, prove and verify. Here, we mix them together
/// because we want to delay the key generation of groth16 later to see
/// testing results early. This function can be split into 3 (set up
/// using dummy instances), later.
///
/// NOTE: vec_circ should be ordered as required by Driver (see its doc)
pub fn foldpot_main<E:Pairing<G1=C1,G2=C2G2>,P:PairingVar<E,CF3<C2G2>>+std::fmt::Debug+Clone,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool>(
	lkup: Rc<RefCell<LK>>, //the lookup table defines the regex automatas
	vec_circ: Vec<Vec<FC>>,
	vec_words: Vec<Vec<E::ScalarField>>,
	vec_words_info: Vec<WordInfo>,
	idx_individual_prf: usize, 
) -> Result<(), Error>
where
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
    //FC: SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, false>,
	LK: LookupTableTwoCol<C1::ScalarField> + 'static,
    CS1: CommitmentScheme<C1, H, ProverParams = PedersenParams<C1>> +
		CommitmentScheme<C1, ProverParams=PedersenParams<C1>>,
    CS1E: CommitmentScheme<
        C1, H,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
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
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{
	//0. Fix the circuit swith dummy statements
	// here we assume that each circuit can always handle
	// words of zeros, and set its dummy_statement for preprocess()
	// to build keys.
	let log_level: usize = LOG1;
	let mut gt1 = GTimer::new();
	let mut gt_all = GTimer::new();
	log(log_level, &format!("===== fold_pot starts ====="));
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
			let wlen = circ.get_mapper().borrow().max_word_len();
			let frag = vec![zero; wlen];
			let prev_adv: Option<Rc<dyn NdAdvice>> = None; //fine to set None
			let r_advice= circ.get_mapper().borrow()
					.gen_nd_advice_no_limit(&frag, &word_info,prev_adv);
			if r_advice.is_some(){//advice is generated
				let advice = r_advice.unwrap().1;
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
				let stmt_res = circ.get_mapper().borrow().build_statement(
					&frag, 
					&prev_stmt, 
					lkup.clone(), 
					&ei,
					advice, 
					lk_share_size,
					true); //dummy mode
				assert!(stmt_res.is_ok());
				circ.set_dummy_stmt(stmt_res.unwrap().to_vec());
			}else{
				//do nothing, just let the circ's gen_dummy_statement
				//later to return zero vec
			}
			id += 1;
		}
	}
	log_perf(log_level, &format!("FoldPot Step 1: build dummy stmt for all circs"),
		&mut gt1);


	//1. create instance
	let mut rng = rand::rngs::OsRng;
	let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();
	let _n_circs = vec_circ.len();

	//2. create the driver1 for the 1st phase
	let mut _num_steps = 2; //will change
	let b_full = false;
	let n_words = vec_words.len();
	let max_total_n:usize = vec_words.iter().map(|x| x.len()).sum();
	let mut driver1 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,FC,S,LK,GM,H> ::new(poseidon_config.clone(), 
			lkup, vec_circ, rng, b_full, max_total_n, n_words);
	log_perf(log_level, &format!("FoldPot: Step 2: set up driver 1"),
		&mut gt1);

	//3. phase 1 pass 1
	let mut iter = vec_words.iter();
	let mut iter_2 = vec_words.iter();
	let mut iter_3 = vec_words.iter();
	let (nova1, _num_steps, batch_ind_prfs, batch_claims) = driver1.pass_all(
		"Phase 1",
		&mut iter,
		&mut iter_2, 
		&mut iter_3, 
		vec_words.len(), 
		idx_individual_prf, 
		&mut rng, 
		&vec_words_info
	);
	let Some((mut batch_prf, ind_prf)) = batch_ind_prfs.map(|x| (x.0, x.1))
		else {panic!("batch proof is none!");};
	log_perf(log_level, &format!("FoldPot: Step 3: Phase 1: main circuits IVC PROVE STEPS (Folding) DONE. total_word_len: {}, steps: {}.", format_bytes(max_total_n * 31), _num_steps),
		&mut gt1);


	//5. generate the inputs for cyclepair
	let qa_nizk_pkey = &driver1.nova_param.0.qa_pp.expect("qa_pp null!"); 
	let qa_nizk_vkey = &driver1.nova_param.1.qa_vp.expect("qa_vp null!"); 
	let qa_nizk_vkey_hash = qa_nizk_vkey.hash(&driver1.poseidon_config);
	let qa_nizk_vkey_hash1 = qa_nizk_vkey_hash.clone();
	let (U_i1, W_i1, _r_Fr, _cmT)= nova1.gen_next_folded()?;
	let (com_all_w, prf_qa_nizk, r_all_w, prf_kzg, kzg_all_com_ch) = W_i1.gen_com_all_w_and_qa_nizk_prf::<E, CS1E, H>(&qa_nizk_pkey, &driver1.nova_param.0.cs1e_pp, &qa_nizk_vkey, &U_i1, &driver1.poseidon_config);
	let cyclepair_inputs = U_i1
		.generate_cyclepair_inputs::<E>(qa_nizk_pkey, qa_nizk_vkey,
			&com_all_w, &prf_qa_nizk, &poseidon_config); 

	let n_circs = 1;
	let circ_cyclepair = create_sigma_fold_pair::<C1::ScalarField, C1, CS1, LK, H>(n_circs, poseidon_config.clone());
	
	//6. another three rounds
	let vec_words = cyclepair_inputs.clone();
	let mut iter = vec_words.iter();
	let mut iter_2 = vec_words.iter();
	let mut iter_3 = vec_words.iter();
	let vec_circ = vec![vec![ circ_cyclepair] ];
	let _n_circs = vec_circ.len();
	let b_full = true;
	let lk = LK::new(vec![]);
	let lkup = Rc::new(RefCell::new(lk));
	//let driver2 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,FC,S,LK>
	let mut driver2 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, FoldPairMapper<CF1<C1>,LK>,H>,S,LK,FoldPairMapper<CF1<C1>,LK>,H>
		::new(poseidon_config.clone(), lkup, vec_circ, rng, b_full, max_total_n, n_words);
	let vec_word_info = vec![WordInfo::dummy(); vec_words.len()];
	let (nova2, _num_steps, _batch_prfs, _bt_claims) = driver2.pass_all(
		"Phase 2",
		&mut iter,
		&mut iter_2, 
		&mut iter_3, 
		vec_words.len(), 
		idx_individual_prf, 
		&mut rng, 
		&vec_word_info
	);

	let qa_nizk_pkey = &driver2.nova_param.0.qa_pp.expect("qa_pp null!"); 
	let qa_nizk_vkey = driver2.nova_param.1.qa_vp.as_ref()
		.expect("qa_vp null!").clone();
	let qa_nizk_vkey_hash = qa_nizk_vkey.hash(&driver2.poseidon_config);
	let (nova2_U_i1, nova2_W_i1, _nova2_r_Fr, _nova2__cmT)= 
		nova2.gen_next_folded()?;
	let (nova2_com_all_w, nova2_prf_qa_nizk, nova2_r_all_w, nova2_prf_kzg, nova2_kzg_all_com_ch) = nova2_W_i1.gen_com_all_w_and_qa_nizk_prf::<E, CS1E, H>( &qa_nizk_pkey, &driver2.nova_param.0.cs1e_pp, &qa_nizk_vkey, &nova2_U_i1, &driver2.poseidon_config);
	log_perf(log_level, &format!("FoldPot: Step 4: Phase 2: cyclefold and cyclepair IVC PROVE STEPS (folding) DONE. num_steps: {}", _num_steps), &mut gt1);

	//7. now build up the TwoPhaseDeciderCircuit.
	let inp = TwoPhaseCircInput{
			ch1: nova1.zi_part2_inst.ch.clone(),
			rc1: nova1.zi_part2_inst.rc.clone(),
			kzg_sum1: nova1.zi_part2_inst.sum_kzg_eval_lk
				+ nova1.zi_part2_inst.sum_kzg_eval_word
				+ nova1.zi_part2_inst.sum_kzg_eval_others,
			kzg_all_com_ch1: kzg_all_com_ch,
			eval_w_e1: prf_kzg.eval,

			kzg_all_com_ch2: nova2_kzg_all_com_ch,
			eval_w_e2: nova2_prf_kzg.eval,

			comE2: nova2_U_i1.vec_inst[0].cmE.clone(),
			comW2: nova2_U_i1.vec_inst[0].cmW.clone(),
			comF2: nova2_U_i1.vec_inst[0].cmF.clone(),

			qa_nizk_vkey_hash: qa_nizk_vkey_hash1, 
	};
	println!("DEBUG USE 6602.1: snark_inp: {:#?}", inp);
	let decider_circuit = TwoPhaseDeciderEthCircuitSuper
		::from_nova::<FC>(nova1, nova2, 
			cyclepair_inputs, qa_nizk_vkey_hash.clone(), 
			driver2.poseidon_config.clone(),
			com_all_w, r_all_w, nova2_com_all_w, nova2_r_all_w, inp)?; 
	log_perf(log_level, &format!("FoldPot Step 5: build decider circuit. MEM: {} GB", get_mem_usage()), &mut gt1);



	//8. build the constraints (this step is actually NOT needed)
	// because constraints will be generated for dummy
	/* RECOVER for debug. Saves about 20GB and 5 minutes
		for partial system (40M R1CS -> 40G) from 60M (60GB)
	let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
	decider_circuit.clone().generate_constraints(cs.clone()).unwrap();
	t1.prt(&format!("Step 10. Generate All Constraints: {}", 
		cs.num_constraints()));
	#[cfg(test)]{ assert!(cs.is_satisfied().unwrap()); }
	*/

	//9. set up the keys (maybe later can be cached)
	let (g16_pk, g16_vk) = {//to save ram, clone will be freed
		let (g16_pk, g16_vk) = S::circuit_specific_setup(
			decider_circuit.clone(), 
			&mut rng).unwrap();
		(g16_pk, g16_vk)
	};
	log_perf(log_level, &format!("FoldPot Step 6: setup Groth16. MEM: {} GB.",  get_mem_usage()), &mut gt1);

	//10. produce the groth16 snark
	let snark_proof: S::Proof = S::prove(&g16_pk, decider_circuit, &mut rng)
		.map_err(|e| Error::Other(e.to_string()))?;

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

		snark_proof,
	);
	log_perf(log_level, &format!("FoldPot Step 7: Gen Groth16 Proof. MEM: {} GB.",  get_mem_usage()), &mut gt1);

	//11. verify the batch proof
	let mut batch_ver_param = driver1.batch_param.as_ref().unwrap().1.clone();
	batch_ver_param.kzg_driver1 = Some(driver1.nova_param.1.cs1e_vp.clone());
	batch_ver_param.kzg_driver2 = Some(driver2.nova_param.1.cs1e_vp.clone());
	let qa_nizk_vkey2 = driver2.nova_param.1.qa_vp.expect("qa_vp null!"); 
	let (batch_claim, ind_claim, _) = batch_claims.unwrap();
	assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_batch(
		&batch_ver_param,
		Some(qa_nizk_vkey_hash1),
		Some(qa_nizk_vkey2.clone()), //needs to be from nova qa_nizk
		Some(g16_vk),
		&batch_claim,
		&batch_prf, 
		&driver1.poseidon_config,
		true //now full verification
	)); //note
	log_perf(log_level, &format!("FoldPot Step 8: Verify Batch Proof."), 
		&mut gt1);

	//12. verify the individual proof
	assert!(BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(
		&driver1.batch_param.as_ref().unwrap().1, 
		idx_individual_prf, 
		&ind_claim,
		&batch_prf, 
		&ind_prf)
	);
	log_perf(log_level, &format!("FOLDPOT Step 9. Verify Individual Proof."), 
		&mut gt1);
	log_perf(log_level, &format!("**** FOLDPOT Now Complete ***** MEM: {} GB.",  get_mem_usage()), &mut gt_all);

	Ok( () )
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
		fn set_container_cfg(&mut self, _cfgs_context: Rc<Vec<ContainerConfig>>, _idx: usize){
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
		fn set_container_config(&mut self, _advice: &Rc<dyn NdAdvice>){ 
			//not needed, handled by legacy code
		}

		/// the capacity is the word length that can be handled by
		/// the circuit
		fn get_capacity(&self)->Rc<dyn Capacity>{
			let word_seg_len = self.max_word_len();
			Rc::new(DummyCapacity{word_seg_len})
		}

		fn gen_nd_advice_no_limit(&self, word: &Vec<F>, _word_info: &WordInfo,
			_prev_adv: Option<Rc<dyn NdAdvice>>) 
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
		fn build_statement(&self, word: &Vec<F>, prev_wit: &Option<StatementInst<F,LK>>, lkup: Rc<RefCell<LK>>, ea: &StatementExtraInfo<F>, _advice: Rc<dyn NdAdvice>, _lkup_share_size: usize, _b_dummy: bool) 
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
		let lkup = Rc::new(RefCell::new(lk.clone()));
		let (odd_mapper, even_mapper) =  
			(SumMapper::<Fr,LK>::new(true), SumMapper::<Fr,LK>::new(false));
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let lkup_share_size = 4;
		let vec_circ = vec![
			vec![
				SigmaIR1CS_Inst::<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>::new_adv("oddsum".to_string(), poseidon_config.clone(), Rc::new(RefCell::new(odd_mapper)), false, lkup_share_size, true).unwrap(),
			],
			vec![
				SigmaIR1CS_Inst::<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>::new_adv("evensum".to_string(), poseidon_config.clone(), Rc::new(RefCell::new(even_mapper)), false, lkup_share_size, true)
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
		let sample_individual_prf = 1; //generate individual proof 1
		let vec_word_info = vec![WordInfo::dummy(); vec_words.len()];
		let _prf = foldpot_main::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>,S,LK,SumMapper<Fr,LK>, false>(lkup, vec_circ, vec_words, vec_word_info, sample_individual_prf);
	}

}
