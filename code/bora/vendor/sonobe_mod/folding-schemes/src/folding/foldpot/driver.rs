use std::any::Any;
use ark_bn254::Bn254;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use std::{sync::{Arc, Mutex, Condvar, RwLock,
    atomic::{AtomicUsize, Ordering}}, fmt::{Debug,Formatter}};
/* 
	Created 08/27/2024 
	Modified 12/25/2024: added snark_rand_input structure
	Modified 01/08/2025: added main workflow foldpot_main
	Modified 11/24/2025: merge pass1 to pass3 to save memory
	Modified 02/22/2026: further improve memory consumption
*/

extern crate utils;
use utils::{logger::{log, log_perf, emit_stdout, ERR, LOG1,LOG2,LOG3}, timer::Timer as GTimer, consts::{read_global_config, get_global_config}, data::{pad_word_to_multiple, gen_pad_nibbles_fe, pack_nibbles}};
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
			qa_nizk::{QaNizkProof,QaNizkProverParams},
			utils::{Timer,get_mem_usage,get_mem_usage_mb,format_bytes,B_DEBUG},
			circuits_super::{field_to_usize},
			mod_super::{PreprocessorParamFoldPotSuper,FoldPotSuper,
				compute_step_hc_cmF_adv},
			sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,StatementExtraInfo,GadgetMapper,Capacity,NdAdvice,WordInfo,CloneDeep},
			sigma_cyclepair::{create_sigma_fold_pair,FoldPairMapper},
			//decider_eth_super::{DeciderFoldPotSuper},
			decider_eth_circuit_super::{CyclePairCircuit, CircPubInput, MainDeciderCircuit},
			batch_proc::{BatchProcessorProverParams,BatchProcessorVerifierParams,BatchProcessor,BatchClaim,BatchProof,IndividualClaim,IndividualProof,SnarkAdvice,SnarkRandInput}
		}
	},
};


macro_rules! lock_unwrap {
    ($mutex:expr) => {
        $mutex.lock().unwrap_or_else(|e| panic!("Mutex poisoned at {}:{}: {}", file!(), line!(), e))
    };
}


fn get_a_query_len<PK: Any>(pk: &PK) -> String {
    if let Some(pk_g16) = (pk as &dyn Any).downcast_ref::<ark_groth16::ProvingKey<Bn254>>() {
        pk_g16.a_query.len().to_string()
    } else {
        "N/A".to_string()
    }
}

fn old_write_g16key<F: PrimeField, S: SNARK<F>>(path: &Path, pk: &S::ProvingKey, vk: &S::VerifyingKey, job_id: usize) 
where S::ProvingKey: CanonicalSerialize + 'static, S::VerifyingKey: CanonicalSerialize 
{
    let mut timer = GTimer::new();
    let start = Instant::now();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("failed to create cache dir");
    }
    let mut f = File::create(path).expect(&format!("Failed to create key file at {:?}", path));
    pk.serialize_compressed(&mut f).expect("pk ser err");
    vk.serialize_compressed(&mut f).expect("vk ser err");
    let size = metadata(path).map(|m| m.len()).unwrap_or(0);
    log_perf(job_id, 1, &format!("PERF 1003: [write_g16key] path: {:?}, elements: {}, size: {} bytes, time: {:?}", path, get_a_query_len(pk), size, start.elapsed()), &mut timer);
}

fn old_read_g16key<F: PrimeField, S: SNARK<F>>(path: &Path, job_id: usize) -> Result<(S::ProvingKey, S::VerifyingKey), Error>
where S::ProvingKey: CanonicalSerialize + 'static, S::VerifyingKey: CanonicalSerialize 
{
    let mut timer = GTimer::new();
    let start = Instant::now();
    let mut f = File::open(path).map_err(|e| Error::Other(format!("Failed to open key file at {:?}: {}", path, e)))?;
    let pk = S::ProvingKey::deserialize_compressed(&mut f).map_err(|e| Error::Other(format!("pk deserr: {}", e)))?;
    let vk = S::VerifyingKey::deserialize_compressed(&mut f).map_err(|e| Error::Other(format!("vk deserr: {}", e)))?;
    let size = metadata(path).map(|m| m.len()).unwrap_or(0);
    log_perf(job_id, 1, &format!("PERF 1003: [read_g16key] path: {:?}, elements: {}, size: {} bytes, time: {:?}", path, get_a_query_len(&pk), size, start.elapsed()), &mut timer);
    Ok((pk, vk))
}



/// Sidecar-meta binary layout: write a list of 32-byte r1cs hashes
/// plus a single 32-byte cf_r1cs hash. Used together with the
/// Pedersen-param sidecar files to keep circuit constants stable
/// across snark-cache runs.
fn write_sidecar_meta(path: &Path, r1cs_hashes: &[[u8; 32]], cf_r1cs_hash: [u8; 32]) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create sidecar dir err");
    }
    let mut f = File::create(path).expect("create sidecar meta err");
    let n = r1cs_hashes.len() as u32;
    f.write_all(&n.to_le_bytes()).expect("write n err");
    for h in r1cs_hashes {
        f.write_all(h).expect("write hash err");
    }
    f.write_all(&cf_r1cs_hash).expect("write cf hash err");
}

fn read_sidecar_meta(path: &Path) -> (Vec<[u8; 32]>, [u8; 32]) {
    let mut f = File::open(path)
        .unwrap_or_else(|e| panic!("open sidecar meta {:?}: {}", path, e));
    let mut n_buf = [0u8; 4];
    f.read_exact(&mut n_buf).expect("read n err");
    let n = u32::from_le_bytes(n_buf) as usize;
    let mut hashes = vec![[0u8; 32]; n];
    for h in hashes.iter_mut() {
        f.read_exact(h).expect("read hash err");
    }
    let mut cf = [0u8; 32];
    f.read_exact(&mut cf).expect("read cf hash err");
    (hashes, cf)
}

fn write_g16key<F: PrimeField, S: SNARK<F>>(path: &Path, pk: &S::ProvingKey, vk: &S::VerifyingKey, job_id: usize)
where S::ProvingKey: CanonicalSerialize + 'static, S::VerifyingKey: CanonicalSerialize + 'static
{
    if let (Some(pk_g16), Some(vk_g16)) = ((pk as &dyn Any).downcast_ref::<ark_groth16::ProvingKey<Bn254>>(), (vk as &dyn Any).downcast_ref::<ark_groth16::VerifyingKey<Bn254>>()) {
        crate::folding::foldpot::utils::write_g16_optimized_bn254(path, pk_g16, vk_g16);
    } else {
        old_write_g16key::<F, S>(path, pk, vk, job_id);
    }
}

fn read_g16key<F: PrimeField, S: SNARK<F>>(path: &Path, job_id: usize) -> Result<(S::ProvingKey, S::VerifyingKey), Error>
where S::ProvingKey: CanonicalSerialize + 'static, S::VerifyingKey: CanonicalSerialize + 'static
{
    if std::any::TypeId::of::<S::ProvingKey>() == std::any::TypeId::of::<ark_groth16::ProvingKey<Bn254>>() {
        let (pk_g16, vk_g16) = crate::folding::foldpot::utils::read_g16_optimized_bn254(path);
        let pk_any: Box<dyn Any> = Box::new(pk_g16);
        let vk_any: Box<dyn Any> = Box::new(vk_g16);
        
        let pk_s = *pk_any.downcast::<S::ProvingKey>().expect("downcast pk error");
        let vk_s = *vk_any.downcast::<S::VerifyingKey>().expect("downcast vk error");
        
        Ok((pk_s, vk_s))
    } else {
        old_read_g16key::<F, S>(path, job_id)
    }
}


use core::marker::PhantomData;
use crate::frontend::FCircuit;
use crate::{FoldingScheme};
use rayon::prelude::*;

pub type Semaphore = Arc<(Mutex<usize>, Condvar)>;

pub struct SemaphoreGuard { pub lock: Semaphore }
impl Drop for SemaphoreGuard {
	fn drop(&mut self) {
		let (mutex, cvar) = &*self.lock;
		let mut count = lock_unwrap!(mutex);
		*count += 1;
		cvar.notify_one();
	}
}

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
	//S107: CS=CS1 -- init_adv installs the FOLDING cmF key
	//into each circuit, so the circuits' scheme must BE CS1.
    FC: FCircuit<C1::ScalarField>
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1,CS=CS1>
		+ Send + Sync,
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
		let b_perf = read_global_config().log_level >= log_level;
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
        >::preprocess(&mut rng, &prep_param, 0)
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
        let _z_0 = [vec![hash_cmF, z0_part2_hash],
			vec![C1::ScalarField::zero(); 4]].concat();
			//[stage hc_cmF, z_0, cmF limbs x4]
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
		let max_wlen = lock_unwrap!(circ.get_mapper()).max_word_len();
		let wlen = word.len();
		let num_segs = if wlen % max_wlen==0{wlen/max_wlen} 
			else {wlen/max_wlen+1};
		let pci = layer_i; //because every layer has only one circ
		let cap = lock_unwrap!(circ.get_mapper()).get_capacity();
		let mut prev_adv = None;
		for i in 0..num_segs{
			//Probe hook: publish chunk_id for the 64008 dump.
			if std::env::var("ZKR_PROBE_64008").is_ok() {
				utils::consts::PROBE_CHUNK_ID
					.store(i, Ordering::Relaxed);
			}
			let start = i*max_wlen;
			let end = if (i+1)*max_wlen>wlen {wlen} else {(i+1)*max_wlen};
			let seg = word[start..end].to_vec();
			//aggressive forward halo: per-seg look-ahead = successor's
			//first M nibbles as raw u8 (empty for last seg / non-aggr
			//⇒ SED pads). Threaded via a per-seg WordInfo clone.
			let m_halo = cap.halo_nibbles();
			let wi_owned;
			let wi_ref = if m_halo>0 && end<wlen {
				let n_end = if end+max_wlen>wlen {wlen}
					else {end+max_wlen};
				let nxt = utils::data::packed_to_nibbles(
					&word[end..n_end].to_vec());
				let take = m_halo.min(nxt.len());
				let mut wi = word_info.clone();
				wi.halo_nibbles = nxt[0..take].iter()
					.map(|f| field_to_usize(f) as u8).collect();
				wi_owned = wi;
				&wi_owned
			} else { word_info };
			let advice = lock_unwrap!(circ.get_mapper())
				.gen_nd_advice(&seg, wi_ref, prev_adv, i, job_id)?;
			vec_pci.push(pci);
			vec_size.push(end-start);
			vec_cap.push(cap.clone());
			prev_adv = Some(advice.clone());
			if b_save_advice{ vec_adv.push(advice); }
		}
		Ok ((num_segs, vec_size, vec_pci, vec_cap, vec_adv))
	}

	/// Aggressive forward halo: clone word_info with halo_nibbles set to
	/// the successor's first m_halo nibbles, unpacked from the remaining
	/// packed words. None when m_halo==0 or no successor (caller uses the
	/// bare word_info; SED then pads with the canonical stream). Mirrors
	/// the inline block in gen_nd_advice_at_layer so the cmF / prove
	/// passes emit the same halo the planning pass authenticates.
	fn with_chunk_halo(word_info: &WordInfo, remaining: &[CF1<C1>],
		m_halo: usize) -> Option<WordInfo> {
		if m_halo==0 || remaining.is_empty() { return None; }
		let n_take = (m_halo/62 + 1).min(remaining.len()); //62=LEGS nib/F
		let nxt = utils::data::packed_to_nibbles(
			&remaining[0..n_take].to_vec());
		let take = m_halo.min(nxt.len());
		let mut wi = word_info.clone();
		wi.halo_nibbles = nxt[0..take].iter()
			.map(|f| field_to_usize(f) as u8).collect();
		Some(wi)
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
		let max_wlen = lock_unwrap!(self.layered_circs[0][0].get_mapper())
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
		let b_debug = B_DEBUG;

		let results: Vec<_> = (min_layer..=max_layer)
				.into_par_iter().map(|layer_id| (
				layer_id,
				std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
					self.gen_nd_advice_at_layer(job_id, layer_id, log_level,
						b_save_advice, word, word_info)
				})).unwrap_or_else(|e| {
					let msg = if let Some(s) = e.downcast_ref::<&str>() {
						s.to_string()
					} else if let Some(s) = e.downcast_ref::<String>() {
						s.clone()
					} else {
						"Unknown panic".to_string()
					};
					Err(Error::Other(format!("Thread panicked in gen_nd_advice_at_layer for layer {}: {}", layer_id, msg)))
				})))
				.collect();
		// (smallest circ) was selectable. Byte estimate matches the
		// PERF 1001 convention (word.len * 63/2).
		let approx_bytes = word.len() * 63 / 2;
		if approx_bytes < 200 * 1024 {
			for (layer_id, res) in results.iter() {
			}
		}
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
		let mwl = lock_unwrap!(self.layered_circs[0][0].get_mapper()).max_word_len();
		for i in 0..self.layered_circs.len(){
			assert!(self.layered_circs[i].len()==1, "only 1 circ per layer!");
			assert!(lock_unwrap!(self.layered_circs[i][0]
				.get_mapper()).max_word_len() == mwl); 
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
		log_perf(job_id, log_level, &format!("PERF 1001: plan_nd_advice for {}, search_mode (fast): {}, best_layer: {}, pci: {}, word.len in rounded bytes: {}.", word_fname, b_fast,  _best_layer, pci, word.len() * 63/2), &mut gt2); //file size
			//is ROUNDED to 63 nibbles/2  * word.len() bytes.

		Ok( (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv ) )
	}

	// ============================================================
	// `_pll` variants: same logic but read `p_layered` (per-job
	// deep-cloned circuits passed by `pass_all`) instead of the
	// shared `self.layered_circs`. This eliminates the Mutex
	// contention on `Arc<Mutex<GM>>` mappers across the 8 outer
	// jobs that share `&driver1`. See driver.rs:2372 for the clone
	// and pass_all:1594 for the call site.
	// All three are near-copies of the originals with `self.*` →
	// `p_layered.*`. Kept separate so non-parallel callers (e.g.
	// driver.rs:1120 `gen_advice`) keep their existing behavior.
	// ============================================================

	fn gen_nd_advice_at_layer_pll(
		p_layered: &Vec<Vec<FC>>,
		job_id: usize, layer_i: usize,
		_log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo)
		-> Result<(usize, Vec<usize>, Vec<usize>,
			Vec<Arc<dyn Capacity + Send + Sync>>,
			Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>
	{
		let mut vec_pci = vec![];
		let mut vec_size = vec![];
		let mut vec_cap = vec![];
		let mut vec_adv:Vec<Arc<dyn NdAdvice + Send + Sync>> = vec![];
		let layer = &p_layered[layer_i];
		let circ = &layer[0];
		let max_wlen = lock_unwrap!(circ.get_mapper()).max_word_len();
		let wlen = word.len();
		let num_segs = if wlen % max_wlen==0{wlen/max_wlen}
			else {wlen/max_wlen+1};
		let pci = layer_i;
		let cap = lock_unwrap!(circ.get_mapper()).get_capacity();
		let mut prev_adv = None;
		for i in 0..num_segs{
			//Probe hook: publish chunk_id for the 64008 dump.
			if std::env::var("ZKR_PROBE_64008").is_ok() {
				utils::consts::PROBE_CHUNK_ID
					.store(i, Ordering::Relaxed);
			}
			let start = i*max_wlen;
			let end = if (i+1)*max_wlen>wlen {wlen} else {(i+1)*max_wlen};
			let seg = word[start..end].to_vec();
			//aggressive forward halo: per-seg look-ahead = successor's
			//first M nibbles as raw u8 (empty for last seg / non-aggr
			//⇒ SED pads). Threaded via a per-seg WordInfo clone.
			let m_halo = cap.halo_nibbles();
			let wi_owned;
			let wi_ref = if m_halo>0 && end<wlen {
				let n_end = if end+max_wlen>wlen {wlen}
					else {end+max_wlen};
				let nxt = utils::data::packed_to_nibbles(
					&word[end..n_end].to_vec());
				let take = m_halo.min(nxt.len());
				let mut wi = word_info.clone();
				wi.halo_nibbles = nxt[0..take].iter()
					.map(|f| field_to_usize(f) as u8).collect();
				wi_owned = wi;
				&wi_owned
			} else { word_info };
			let advice = lock_unwrap!(circ.get_mapper())
				.gen_nd_advice(&seg, wi_ref, prev_adv, i, job_id)?;
			vec_pci.push(pci);
			vec_size.push(end-start);
			vec_cap.push(cap.clone());
			prev_adv = Some(advice.clone());
			if b_save_advice{ vec_adv.push(advice); }
		}
		Ok((num_segs, vec_size, vec_pci, vec_cap, vec_adv))
	}

	/// Aggressive: per-segment circuit selection. Each segment uses
	/// the cheapest rung (layer) whose gen_nd_advice succeeds, bumping
	/// up on any CapErr. Carry threads across rungs (state-only).
	fn gen_nd_advice_per_seg_pll(
		p_layered: &Vec<Vec<FC>>,
		job_id: usize, _log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo)
		-> Result<(usize, Vec<usize>, Vec<usize>,
			Vec<Arc<dyn Capacity + Send + Sync>>,
			Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>
	{
		let mut vec_pci = vec![];
		let mut vec_size = vec![];
		let mut vec_cap = vec![];
		let mut vec_adv:Vec<Arc<dyn NdAdvice + Send + Sync>> = vec![];
		let max_layer = p_layered.len()-1;
		let max_wlen = lock_unwrap!(p_layered[0][0].get_mapper())
			.max_word_len();
		let wlen = word.len();
		let num_segs = if wlen % max_wlen==0{wlen/max_wlen}
			else {wlen/max_wlen+1};
		let mut prev_adv = None;
		//DEBUG USE 69120.7: V1 attribution for part A (per-seg rung
		//router): halo build vs failed rung tries vs the chosen
		//rung's advice call. Prints every ZKR_V1_CAD chunks (def 64).
		use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
		static V1_A_HALO_US: AtomicUsize = AtomicUsize::new(0);
		static V1_A_OK_US: AtomicUsize = AtomicUsize::new(0);
		static V1_A_FAIL_US: AtomicUsize = AtomicUsize::new(0);
		static V1_A_TRIES: AtomicUsize = AtomicUsize::new(0);
		static V1_A_CHUNKS: AtomicUsize = AtomicUsize::new(0);
		static V1_CAD: std::sync::OnceLock<usize> =
			std::sync::OnceLock::new();
		let v1_cad = *V1_CAD.get_or_init(||
			std::env::var("ZKR_V1_CAD").ok()
				.and_then(|s| s.parse().ok()).unwrap_or(64));
		for i in 0..num_segs{
			let start = i*max_wlen;
			let end = if (i+1)*max_wlen>wlen {wlen} else {(i+1)*max_wlen};
			let seg = word[start..end].to_vec();
			//T309 test hook: ZKR_T309_INJECT="name:req" forces ONE
			//fold-time CapErr on the last segment (as if no rung
			//fit) to exercise the tuner's rung-attribution retry.
			//One-shot per process; unreachable from the capacity
			//probe (CapacityPlanner) or the 0-word finalize check
			//(neither calls this fn).
			if i == num_segs-1 {
				if let Ok(spec) = std::env::var("ZKR_T309_INJECT") {
					static T309_DONE: std::sync::atomic::AtomicBool =
						std::sync::atomic::AtomicBool::new(false);
					if !T309_DONE.swap(true,
						std::sync::atomic::Ordering::SeqCst) {
						//rsplit: CapErr names contain "::" (e.g.
						//"dis_adv::prod_pats_expansion"), so split
						//at the LAST colon, not the first.
						if let Some((n, r)) = spec.rsplit_once(':') {
							return Err(Error::CapErr(vec![
								(n.to_string(),
								 r.parse().unwrap_or(0))]));
						}
					}
				}
			}
			let t_halo = std::time::Instant::now(); //DEBUG USE 69120.7
			//halo is rung-independent (M = db max span); build once.
			let m_halo = lock_unwrap!(p_layered[0][0].get_mapper())
				.get_capacity().halo_nibbles();
			let wi_owned;
			let wi_ref = if m_halo>0 && end<wlen {
				let n_end = if end+max_wlen>wlen {wlen}
					else {end+max_wlen};
				let nxt = utils::data::packed_to_nibbles(
					&word[end..n_end].to_vec());
				let take = m_halo.min(nxt.len());
				let mut wi = word_info.clone();
				wi.halo_nibbles = nxt[0..take].iter()
					.map(|f| field_to_usize(f) as u8).collect();
				wi_owned = wi;
				&wi_owned
			} else { word_info };
			//DEBUG USE 69120.7: halo span ends here.
			let halo_us = t_halo.elapsed().as_micros() as usize;
			//bump from cheapest rung until the segment fits. Capacity
			//overflow can surface as a panic (CapErr is not uniformly
			//propagated), so catch it and treat as "rung too small",
			//mirroring par_search_best_layer_pll.
			let mut chosen = None;
			let mut last_err = None;
			for l in 0..=max_layer{
				let circ = &p_layered[l][0];
				let cap = lock_unwrap!(circ.get_mapper()).get_capacity();
				let t_try = std::time::Instant::now(); //DEBUG USE 69120.7
				let r = std::panic::catch_unwind(
					std::panic::AssertUnwindSafe(|| {
					lock_unwrap!(circ.get_mapper()).gen_nd_advice(
						&seg, wi_ref, prev_adv.clone(), i, job_id)
				})).unwrap_or_else(|e| {
					let msg = if let Some(s)=e.downcast_ref::<&str>(){
						s.to_string()
					} else if let Some(s)=e.downcast_ref::<String>(){
						s.clone()
					} else { "Unknown panic".to_string() };
					Err(Error::Other(format!(
						"per-seg rung {} panic: {}", l, msg)))
				});
				//DEBUG USE 69120.7: split try cost by outcome.
				let try_us = t_try.elapsed().as_micros() as usize;
				if r.is_ok() {
					V1_A_OK_US.fetch_add(try_us, Relaxed);
				} else {
					V1_A_FAIL_US.fetch_add(try_us, Relaxed);
				}
				V1_A_TRIES.fetch_add(1, Relaxed);
				match r{
					Ok(adv) => {chosen=Some((l, cap.clone(), adv)); break;},
					Err(e) => {
						last_err=Some(e);
					},
				}
			}
			let (l, cap, adv) = match chosen{
				Some(t) => t,
				None => return Err(last_err.unwrap_or(
					Error::NotSupported(
						"no rung fits segment".to_string()))),
			};
			//DEBUG USE 69120.7: per-chunk roll-up + cadence print.
			V1_A_HALO_US.fetch_add(halo_us, Relaxed);
			let nc = V1_A_CHUNKS.fetch_add(1, Relaxed) + 1;
			if nc % v1_cad == 0 {
				println!("DEBUG USE 69120.7: partA chunks={} tries={} \
halo_us={} ok_us={} fail_us={}",
					nc, V1_A_TRIES.load(Relaxed),
					V1_A_HALO_US.load(Relaxed),
					V1_A_OK_US.load(Relaxed),
					V1_A_FAIL_US.load(Relaxed));
			}
			vec_pci.push(l);
			vec_size.push(end-start);
			vec_cap.push(cap);
			prev_adv = Some(adv.clone());
			if b_save_advice{ vec_adv.push(adv); }
		}
		Ok((num_segs, vec_size, vec_pci, vec_cap, vec_adv))
	}

	fn par_search_best_layer_pll(
		p_layered: &Vec<Vec<FC>>,
		job_id: usize, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo,
		min_layer: usize, max_layer: usize)
		-> Result<(usize, usize, Vec<usize>, Vec<usize>,
			Vec<Arc<dyn Capacity + Send + Sync>>,
			Vec<Arc<dyn NdAdvice + Send + Sync>>), Error>
		where <CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync
	{
		use rayon::prelude::*;
		let results: Vec<_> = (min_layer..=max_layer)
			.into_par_iter().map(|layer_id| {
				let r = std::panic::catch_unwind(
					std::panic::AssertUnwindSafe(|| {
					Self::gen_nd_advice_at_layer_pll(
						p_layered, job_id, layer_id, log_level,
						b_save_advice, word, word_info)
				})).unwrap_or_else(|e| {
					let msg = if let Some(s) = e.downcast_ref::<&str>() {
						s.to_string()
					} else if let Some(s) = e.downcast_ref::<String>() {
						s.clone()
					} else {
						"Unknown panic".to_string()
					};
					Err(Error::Other(format!(
						"Thread panicked in gen_nd_advice_at_layer_pll \
						 for layer {}: {}", layer_id, msg)))
				});
				(layer_id, r)
			})
			.collect();
		let best_result = results.iter()
			.filter_map(|(layer_id, res)| res.as_ref().ok()
				.map(|val| (*layer_id, val)))
			.min_by_key(|(layer_id, _)| *layer_id);
		match best_result {
			Some((best_layer, (num_segs, vec_seg_size, vec_pci,
					vec_cap, vec_adv))) => {
				Ok((best_layer, *num_segs, vec_seg_size.clone(),
					vec_pci.clone(), vec_cap.clone(), vec_adv.clone()))
			},
			None => {
				let mut err = Error::NotSupported(
					"No suitable layer found".to_string());
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

	pub fn plan_nd_advice_new_pll(
		p_layered: &Vec<Vec<FC>>,
		job_id: usize, log_level: usize, b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo,
		word_fname: &str)
		-> Result<(usize, Vec<usize>, Vec<usize>,
			Vec<Arc<dyn Capacity + Send + Sync>>,
			Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>
		where <CS1E as CommitmentScheme<C1, H>>::ProverParams: Send + Sync
	{
		let b_fast = true;
		let mut gt1 = GTimer::new();
		let mut gt2 = GTimer::new();
		log_perf(job_id, log_level, &format!(
			"plan_nd_advice_pll step 0. layers: {}, word.len(): {}, \
			 b_save_adivce: {}",
			p_layered.len(), word.len(), b_save_advice), &mut gt1);
		let mwl = lock_unwrap!(p_layered[0][0].get_mapper())
			.max_word_len();
		for i in 0..p_layered.len(){
			assert!(p_layered[i].len()==1, "only 1 circ per layer!");
			assert!(lock_unwrap!(p_layered[i][0]
				.get_mapper()).max_word_len() == mwl);
		}
		let aggr = utils::consts::read_global_config()
			.clamav_cfg.b_aggressive_sde_for_rep;
		let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) = if aggr {
			let r = Self::gen_nd_advice_per_seg_pll(
				p_layered, job_id, log_level+2, b_save_advice,
				word, word_info)?;
			r
		} else {
			let (_best_layer, num_segs, vec_seg_size, vec_pci,
					vec_cap, vec_adv) = {
				let min_layer = 0;
				let max_layer = p_layered.len()-1;
				Self::par_search_best_layer_pll(
					p_layered, job_id, log_level+2, b_save_advice,
					word, word_info, min_layer, max_layer)
			}?;
			let pci = vec_pci[0];
			for x in &vec_pci{assert!(*x==pci);}
			log_perf(job_id, log_level, &format!(
				"PERF 1001: plan_nd_advice_pll for {}, fast: {}, \
				 best_layer: {}, pci: {}, word.len: {} bytes.",
				word_fname, b_fast, _best_layer, pci,
				word.len() * 63/2), &mut gt2);
			(num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)
		};
		Ok((num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv))
	}

	/// old version: it assues multiple circs in one layer
	pub fn plan_nd_advice_old(&self, job_id: usize, log_level: usize, _b_save_advice: bool,
		word: &Vec<CF1<C1>>, word_info: &WordInfo, _word_fname: &str)
		-> Result<(usize, Vec<usize>, Vec<usize>, Vec<Arc<dyn Capacity + Send + Sync>>, Vec<Arc<dyn NdAdvice + Send + Sync>>),Error>{
			if 1>0 {panic!("should not call this function. It is invalid. Keep the legacy code for future improvement.");}
			let mut gt1 = GTimer::new();
			log_perf(job_id, log_level, &format!("Entering plan_nd_advice, layers: {}, word.len(): {}.", self.layered_circs.len(), word.len()), &mut gt1);
			let remaining = word.clone();
			if B_DEBUG {//check if all circs have the same inp/oup
				// check the max_word_len is decreasing (thus avg cost
				//increasing
				for i in 0..self.layered_circs.len(){
					let layer = &self.layered_circs[i];
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
				let max_word_len = lock_unwrap!(circ1.get_mapper()).max_word_len();
				let word_len = if max_word_len>remaining.len(){
					remaining.len()}else {max_word_len};
				let word = remaining[0..word_len].to_vec();
				if B_DEBUG {
					for circ in layer{assert!(lock_unwrap!(circ.get_mapper()).
						max_word_len()==max_word_len);
					}
				}
				let prev_adv = if vec_adv.len()==0 {None}
					else {Some(vec_adv[vec_adv.len()-1].clone())};
				//PASS 0 as seg_id just to make syntax ok
				if 1>0 {panic!("should not call this function");}
				let res = lock_unwrap!(circ1.get_mapper())
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
				//if lock_unwrap!(circ.get_mapper())
				//	.get_capacity().can_satisfy(&cap){
				//	b_found = true;
				//	selected_layer = layer_id;
				//	break;
				//}else{
				//	if layer_id == self.layered_circs.len()-1{
				//		println!("UNABLE to find circ: cap needed: {:#?} and last circ capacility: {:#?}", cap, lock_unwrap!(circ.get_mapper()).get_capacity());
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
					let max_word_len = lock_unwrap!(circ.get_mapper())
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
					let max_word_len = lock_unwrap!(circ.get_mapper())
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
						_last_res = Some(lock_unwrap!(circ.get_mapper())
						  .gen_nd_advice(&word, &word_info, prev_adv, 0, 0)
						  .unwrap());
					}
				
					//verify the circ does can satisfy the request
 // 					if lock_unwrap!(circ.get_mapper()).get_capacity()
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
		let z0_part2 = ZiPartTwoInst::<C1::ScalarField>
			::new(zero, zero, &self.poseidon_config, b_full_mode, fq_bits, total_words);
		let z0_part2_hash = z0_part2.hash(&self.poseidon_config);
		let _z_0 = [vec![zero, z0_part2_hash],
			vec![zero; 4]].concat(); //will replaced
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
				if B_DEBUG {
					//use crate::folding::foldpot::sigma_ir1cs::{Capacity};
					assert!(act_len<=_max_len);
					let rc_cap = _vec_cap_req[i].clone();
					assert!(lock_unwrap!(circ.get_mapper()).get_capacity()
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
					r_vec_r: snark_inp.r_vec_r,
					r_vec_v: snark_inp.r_vec_v,
					r_word_i: snark_inp.rands[(word_id as usize)-1],
					accumulated_word_len: C1::ScalarField::from(acc_wd_len as u32),
				};//end constructor StatementExtraInfo

				//need to build the statement to fill the m_map
				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(&frag, &prev_stmt, self.lkup.clone(), &ei, advice[subseg_id-1].clone(), lk_share_size, false, job_id);
				assert!(stmt_res.is_ok());
				let stmt = stmt_res.unwrap();
				//T703a: virtual slots counted with the SAME
				//evaluator gen_witness uses (never disagree).
				let virt_extra = circ
					.eval_virt_queries_all(&stmt.to_vec());
				stmt.fill_lkup_mvec(&mut m_map, &self.lkup,
					&virt_extra); //needed here!
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
		let z_0 = [vec![zero, z0_part2_hash],
			vec![zero; 4]].concat();
		let _n_circ = field_to_usize(&vea[0].n_circ);
		let mut hash_cmF= C1::ScalarField::zero();
		let (ch, rc) = (zero, zero);
		timer.prt("pass_two: step 0: init");

		//2. create nova1
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
				precomputed_cmF,
				job_id
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
				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, vec_advice[wi][subseg_id-1].clone(), share_size, false, job_id);
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
				false, None, Some(job_id), "self")); //note part2 checked later
			let ind_prf = BatchProcessor::<E,LK,S,CS1E,H>::prove_individual(pk, 
				&snark_inp, &words, &ind_claim,
				idx_individual_prf);
			let _res = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(vk, idx_individual_prf, &ind_claim, &batch_proof, &ind_prf,
				Some(job_id), "self");
			if B_DEBUG { assert!(_res); }
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
		//S107: seed the in-circuit chain at ZERO so the final
		//state z_n[0] equals the pass-1 hash_cmF that seeded
		//ch/rc; the decider discloses z_n[0] (Phase1CircuitRet).
		let z_0 = [vec![zero, z0_part2_hash], vec![zero; 4]].concat();
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
				precomputed_cmF,
				job_id
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
				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, vec_advice[wi][subseg_id].clone(), share_size, false, job_id);
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
		if B_DEBUG {
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
		job_id: usize,
		semaphore_batch_claim: Semaphore,
		// Per-job circuits override. Callers in the single-job code
		// paths pass `&self.layered_circs, &self.circuits`. The
		// parallel `foldpot_main` closure passes per-job deep-cloned
		// vectors so each job has its own mapper locks.
		p_layered: &Vec<Vec<FC>>,
		p_circuits: &Vec<FC>,
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

			let _guard = {
				let (lock, cvar) = &*semaphore_batch_claim;
				let mut count = lock_unwrap!(lock);
				while *count == 0 {
					count = cvar.wait(count).unwrap();
				}
				*count -= 1;
				SemaphoreGuard { lock: semaphore_batch_claim.clone() }
			};

			let (global_claim, ind_claims, snark_inp) =
				BatchProcessor::<E,LK,S,CS1E,H>::gen_claims(pk, &mut rng, &words, self.lkup.clone()).unwrap();
			Some( (global_claim, ind_claims[idx_ind_proof].clone(), snark_inp) )
		}else{			None
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
		let _z_0 = [vec![zero, z0_part2_hash],
			vec![zero; 4]].concat(); //will replaced
		let mut m_map = HashMap::<usize,usize>::new();
		let pc_0_val = 0;
		let _pc_0 = C1::ScalarField::from(pc_0_val as u32);
		log_perf(job_id, log_level, &format!(
			"PERF 1007. {} step 1: generate batch/ind claims. mem: {} GB, increased mem: {} MB, for words: {}, total_word_len: {} packed fields.", phase_name, m2/1024, if m2>m1 {m2-m1} else {0}, total_words, total_wd_len),
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

		let n_circ = p_circuits.len();
		let _vec_mapper= p_circuits.iter().map(|c| c.get_mapper()).
			collect::<Vec<Arc<Mutex<GM>>>>();
		let lkup_len= self.lkup.get_size();
		let mut total_lkup_covered = 0;
		let m3 = get_mem_usage_mb();
		let mut gtw = GTimer::new();
		let mut last_pci1 = 0;
		let num_words = vec_word_fnames.len();
		// DEBUG/diagnostic: optional per-job word cap. 0 = unlimited.
		let _word_cap = read_global_config().word_cap_per_job;
		// aggressive-only: read once. Gates the per-chunk LOG3
		// selection log AND the S5 advice reuse below (the non-aggr
		// path keeps its recompute arm, byte-identical).
		let b_aggr = read_global_config()
			.clamav_cfg.b_aggressive_sde_for_rep;
		for (word, word_fname) in iter_words.zip(vec_word_fnames.iter()){
			if _word_cap > 0 && word_id > _word_cap {
				break;
			}
			let mut prev_stmt = None;
			let mut prev_adv = None;
			let mut gt2 = GTimer::new();

			//2.1 first try out and determine the length info for each
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let total_word_len = word.len();
			let mut acc_wd_len = 0;
			let _mapper = p_circuits[0].get_mapper();
			let word_info = &vec_word_info[word_id-1];
			// Route through per-job-cloned `p_layered` to avoid
			// shared mapper Mutex contention (was driver1.layered_circs
			// before). See plan_nd_advice_new_pll above.
			// S5 (aggr): save the router's advice (one word's worth,
			// <= ~160 Arcs) so the loop below reuses it instead of
			// recomputing it per segment.
			let (steps, vec_len, vec_pci, _vec_cap_req, vec_adv) =
				Self::plan_nd_advice_new_pll(
					p_layered, job_id, log_level+2, b_aggr,
					&word, word_info, word_fname).map_err(|e| {
					e
				})?;
			if b_aggr {
				assert!(vec_adv.len() == steps,
					"S5: saved advice {} != steps {}",
					vec_adv.len(), steps);
			}
			log_perf(job_id, log_level+2, &format!("PERF 1008: {} - Pass 1: START decide circ alloc for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(total_word_len*31)), &mut gt2);
			for i in 0..steps{
				//2.1 set up params
				let mut gt3 = GTimer::new();
				let pc_i = if i==0 {last_pci1} else {vec_pci[i-1]};
				let pc_i1 = vec_pci[i]; //this is actually pc_i1 for this circ
				last_pci1 = pc_i1;
				let circ = &p_circuits[pc_i1];
				let _max_len = circ.max_word_len();
				let act_len = vec_len[i];
				// LOG3 per-chunk circ selection (aggressive only):
				// one line per segment, real post-bump pci. fname
				// gives the per-file attribution cost.txt lacks.
				if b_aggr {
					log(job_id, LOG3, &format!("PERF 1001: per-chunk circ sel. {} word_id: {}, subseg_id: {}, fname: {}, pci: {}, seg_len: {}", phase_name, word_id, subseg_id, word_fname, pc_i1, act_len));
				}
				acc_wd_len += act_len;
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();
				if B_DEBUG {
					//use crate::folding::foldpot::sigma_ir1cs::{Capacity};
					assert!(act_len<=_max_len);
					let rc_cap = _vec_cap_req[i].clone();
					assert!(lock_unwrap!(circ.get_mapper()).get_capacity()
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
					r_vec_r: snark_inp.r_vec_r,
					r_vec_v: snark_inp.r_vec_v,
					r_word_i: snark_inp.rands[(word_id as usize)-1],
					accumulated_word_len: C1::ScalarField::from(acc_wd_len as u32),
				};//end constructor StatementExtraInfo
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass 1. For wd: {}, subseg_id: {} gen_statment_extra_info.", word_fname, subseg_id), &mut gt3);

				//2.3 generate the advice and statement
				//need to build the statement to fill the m_map
				//aggressive forward halo: feed the successor prefix so this
				//pass back-solves the same caps the per-seg router validated
				//(else no-halo boundary pats inflate basis_* past the rung).
				let t_bh = std::time::Instant::now(); //DEBUG USE 69120.8
				let m_halo = lock_unwrap!(circ.get_mapper())
					.get_capacity().halo_nibbles();
				let wi_owned = Self::with_chunk_halo(word_info,
					&remaining, m_halo);
				let wi_ref = wi_owned.as_ref().unwrap_or(word_info);
				//DEBUG USE 69120.8: halo span ends, advice span starts.
				let bh_us = t_bh.elapsed().as_micros() as usize;
				let t_adv = std::time::Instant::now();
				//S5 (aggr): reuse the advice the per-seg router
				//generated at this rung -- same frag, halo, seg_id
				//and prev chain -- instead of recomputing it.
				//ZKR_S5_ORACLE=1 recomputes and requires a byte-
				//identical statement (checked after build below).
				static S5_ORACLE: std::sync::OnceLock<bool> =
					std::sync::OnceLock::new();
				let b_orc = b_aggr && *S5_ORACLE.get_or_init(||
					std::env::var("ZKR_S5_ORACLE")
						.map(|v| v == "1").unwrap_or(false));
				let mut orc_adv = None;
				let cur_adv = if b_aggr {
					if b_orc {
						orc_adv = Some(lock_unwrap!(
							circ.get_mapper()).gen_nd_advice(
							&frag, wi_ref, prev_adv.clone(),
							subseg_id - 1, job_id).unwrap());
					}
					vec_adv[i].clone()
				} else {
					let res = lock_unwrap!(circ.get_mapper())
						.gen_nd_advice(&frag, wi_ref, prev_adv,
							subseg_id - 1, job_id);
					assert!(res.is_ok(), "\n\n===== **** =====\nUNABLE to generate advice for word: {}, segment_id: {}, at layer {}, ERROR: {:#?}\n==============\n", word_fname, subseg_id, pc_i1, res);
					res.unwrap()
				};
				//DEBUG USE 69120.8: advice span ends.
				let adv_us = t_adv.elapsed().as_micros() as usize;

				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass 1. gen_advice."), &mut gt3);
				let t_stmt = std::time::Instant::now(); //DEBUG USE 69120.8
				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(
					&frag, &prev_stmt, self.lkup.clone(), &ei,
					//	advice[subseg_id-1].clone(),
						cur_adv.clone(),
						lk_share_size, false, 0);
				assert!(stmt_res.is_ok(), "\n\n === *** === \nUNABLE to generate statement for word id: {}, segment _id: {}, at layer {}, ERR: {:#?}. *** SHOULD IMPROVE the CapErr framework. Exception should be thrown in gen_nd_advice instead of build_stmt ***", word_fname, subseg_id, pc_i1, stmt_res);
				//DEBUG USE 69120.8: stmt span ends (incl. the is_ok
				//assert, which is cheap).
				let stmt_us = t_stmt.elapsed().as_micros() as usize;
				prev_adv = Some(cur_adv);
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass 1. build stmt."), &mut gt3);
				let stmt = stmt_res.unwrap();
				if let Some(oa) = orc_adv {
					//S5 oracle: identical statement from the
					//recomputed advice, or abort.
					let s2 = lock_unwrap!(circ.get_mapper())
						.build_statement(&frag, &prev_stmt,
							self.lkup.clone(), &ei, oa,
							lk_share_size, false, 0)
						.unwrap();
					assert!(stmt.to_vec() == s2.to_vec(),
						"S5 oracle diverged: word {} seg {}",
						word_fname, subseg_id);
				}
				let t_lk = std::time::Instant::now(); //DEBUG USE 69120.8
				//T703a: virtual slots counted with the SAME
				//evaluator gen_witness uses (never disagree).
				let virt_extra = circ
					.eval_virt_queries_all(&stmt.to_vec());
				stmt.fill_lkup_mvec(&mut m_map, &self.lkup,
					&virt_extra); //needed here!
					//for updating couners of lookup
					//later in PASS2 it generates the m_table for
					//each lookup for the corresponding lookup shares.
				//DEBUG USE 69120.8: lkup span ends; roll up + print.
				{
					use std::sync::atomic::{AtomicUsize,
						Ordering::Relaxed};
					static V1_B_HALO_US: AtomicUsize =
						AtomicUsize::new(0);
					static V1_B_ADV_US: AtomicUsize =
						AtomicUsize::new(0);
					static V1_B_STMT_US: AtomicUsize =
						AtomicUsize::new(0);
					static V1_B_LK_US: AtomicUsize =
						AtomicUsize::new(0);
					static V1_B_N: AtomicUsize = AtomicUsize::new(0);
					static V1_CAD: std::sync::OnceLock<usize> =
						std::sync::OnceLock::new();
					let cad = *V1_CAD.get_or_init(||
						std::env::var("ZKR_V1_CAD").ok()
							.and_then(|s| s.parse().ok())
							.unwrap_or(64));
					let lk_us = t_lk.elapsed().as_micros() as usize;
					V1_B_HALO_US.fetch_add(bh_us, Relaxed);
					V1_B_ADV_US.fetch_add(adv_us, Relaxed);
					V1_B_STMT_US.fetch_add(stmt_us, Relaxed);
					V1_B_LK_US.fetch_add(lk_us, Relaxed);
					let n = V1_B_N.fetch_add(1, Relaxed) + 1;
					if n % cad == 0 {
						println!("DEBUG USE 69120.8: partB n={} \
halo_us={} adv_us={} stmt_us={} lkup_us={}",
							n, V1_B_HALO_US.load(Relaxed),
							V1_B_ADV_US.load(Relaxed),
							V1_B_STMT_US.load(Relaxed),
							V1_B_LK_US.load(Relaxed));
					}
				}


				//2.5 making updates
				let ea = stmt.to_extra_info();
				vec_res.push(ea);
				prev_stmt= Some(stmt);
				subseg_id +=1;
				total_lkup_covered += lk_share_size;
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass 1. update, END of dispatching lkup for step {} of {} . ", i, steps), &mut gt3);
			}

			log_perf(job_id, log_level+1, &format!("PERF 1008: {} Pass 1. END generate advice word {} of {}: fname: {} of size: {}.", phase_name, word_id, num_words, word_fname, format_bytes(total_word_len*31)), &mut gtw);
			word_id +=1;
		}
		let m4 = get_mem_usage_mb();
		let b_check_lkup = p_layered[0][0].is_check_lkup(); //assume
			//all circ have the same
		// intentionally truncate Pass 1 so total_lkup_covered cannot
		// reach the full lkup_len. Skip the coverage assert in that case.
		if b_check_lkup && _word_cap == 0 {
			assert!(total_lkup_covered >= lkup_len, "total: {}, lkup_len: {}", total_lkup_covered, lkup_len);
		} else if b_check_lkup && _word_cap > 0 {
		}
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 2: dispatch w into steps. mem: {} MB for total_word_len: {}: ", phase_name, if m4>m3 {m4-m3} else {0}, format_bytes(total_wd_len*31)) , &mut gt1);

		
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

		// DEBUG USE 69801.15: pass2-vs-pass3 statement comparison,
		// armed by ZKR_GADGET_CHECK (dna_debug runs only; prod is
		// unaffected). .15.1 chunk-hash mismatch (all steps),
		// .15.2 exact element diff (first PROBE15_FULL_CAP steps),
		// .15.3 ok heartbeat, .15.4 pass-2 double-build check
		// (extra gate ZKR_PROBE15_DOUBLE -- keep OFF on the clean
		// server run, it re-runs advice+statement generation),
		// .15.5 extra-info overwrite delta. Remove by tag 69801.
		let b_probe15 = std::env::var("ZKR_GADGET_CHECK").is_ok();
		let b_probe15_dbl =
			std::env::var("ZKR_PROBE15_DOUBLE").is_ok();
		const PROBE15_FULL_CAP: usize = 40;
		const PROBE15_CHUNK: usize = 4096;
		let mut probe15_hashes: Vec<Vec<u64>> = vec![];
		let mut probe15_full: Vec<Vec<C1::ScalarField>> = vec![];
		let probe15_hash = |v: &[C1::ScalarField]| -> Vec<u64> {
			use std::hash::{Hash, Hasher};
			v.chunks(PROBE15_CHUNK).map(|ch| {
				let mut h = std::collections::hash_map
					::DefaultHasher::new();
				for e in ch {
					e.into_bigint().as_ref().hash(&mut h);
				}
				h.finish()
			}).collect()
		};

		for word in &words{
			if _word_cap > 0 && word_id > _word_cap {
				break;
			}
			let mut prev_adv = None;
			let mut prev_stmt = None;
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let word_info = &vec_word_info[word_id-1];
			let word_fname = &vec_word_fnames[word_id-1];
			log_perf(job_id, log_level+2, &format!("PERF 1009: {} - Pass 2. START generate cmF for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw2);
			while remaining.len()>0{
				//3.1 compute the problem statement instance
				let mut gt_p2 = GTimer::new();
				let j = field_to_usize(&vea[idx].pc_i1);
				let circ = &p_circuits[j];
				let share_size = circ.get_stmt_config().lookup_share_size;
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();

				//aggressive forward halo: emit the successor prefix so
				//this chunk's IDX_OUP halo matches the next chunk's
				//authenticated IDX_INP prefix (else sum_inp!=sum_oup).
				let m_halo = lock_unwrap!(circ.get_mapper())
					.get_capacity().halo_nibbles();
				let wi_owned = Self::with_chunk_halo(word_info,
					&remaining, m_halo);
				let wi_ref = wi_owned.as_ref().unwrap_or(word_info);
				// DEBUG USE 69801.15.4: keep the pre-call advice arc
				// so the double-build below re-runs from the same
				// prev state. Remove by tag 69801.
				let p15_prev_adv = if b_probe15_dbl
					{prev_adv.clone()} else {None};
				//3.2 generate the adice again
				let res = lock_unwrap!(circ.get_mapper())
					.gen_nd_advice(&frag, wi_ref, prev_adv, subseg_id - 1, job_id);
				assert!(res.is_ok(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id); 
				let cur_adv = res.unwrap();
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass2. gen advice. sugseg_id: {}", subseg_id), &mut gt_p2);

				//3.3 generate the statement again
				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, cur_adv.clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				let mut stmt = stmt_res.unwrap();
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass2. gen statement"), &mut gt_p2);
				stmt.update_lookup(start,start+share_size, &self.lkup, &m_map);
				// DEBUG USE 69801.15: record the pass-2 statement
				// digest (full vec for early steps); optional
				// double-build determinism check. Remove by 69801.
				if b_probe15 {
					let v2 = stmt.to_vec();
					probe15_hashes.push(probe15_hash(&v2));
					if idx < PROBE15_FULL_CAP {
						probe15_full.push(v2.clone());
					}
					if b_probe15_dbl {
						let r2 = lock_unwrap!(circ.get_mapper())
							.gen_nd_advice(&frag, wi_ref,
							p15_prev_adv, subseg_id - 1, job_id);
						let adv2 = r2.expect("p15 re-advice fails");
						let s2 = lock_unwrap!(circ.get_mapper())
							.build_statement(&frag, &prev_stmt,
							self.lkup.clone(), ei, adv2,
							share_size, false, job_id);
						let mut s2 = s2.expect("p15 re-stmt fails");
						s2.update_lookup(start, start + share_size,
							&self.lkup, &m_map);
						let v2b = s2.to_vec();
						let nd = v2.iter().zip(v2b.iter())
							.filter(|(a, b)| a != b).count();
						if nd > 0 {
							let mut det = String::new();
							let mut shown = 0usize;
							for (k, (a, b)) in v2.iter()
								.zip(v2b.iter()).enumerate() {
								if a != b && shown < 4 {
									det.push_str(&format!(
										" [{} {} {}]", k, a, b));
									shown += 1;
								}
							}
							emit_stdout(format!(
								"DEBUG USE 69801.15.4: idx={} \
								rebuild n_diff={} det:{}",
								idx, nd, det));
						} else if idx % 32 == 0 {
							emit_stdout(format!(
								"DEBUG USE 69801.15.4: idx={} \
								rebuild ok", idx));
						}
					}
				}
				start += share_size;
				log_perf(job_id, log_level+2, &format!("PERF 1009: -- Pass 2. update lkup, share_size: {}", share_size), &mut gt_p2);

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
				log_perf(job_id, log_level+2, &format!("PERF 1009 -- Pass 2. compute cmF. "), &mut gt_p2);

				//3.5 update
				let ea = stmt.to_extra_info();
				// DEBUG USE 69801.15.5: which extra-info fields the
				// overwrite changes (pass-2 built from the OLD row,
				// pass-3 will build from the NEW). Remove by 69801.
				if b_probe15 {
					let o = &vea[idx];
					let pairs = [
						("pc_i", o.pc_i, ea.pc_i),
						("pc_i1", o.pc_i1, ea.pc_i1),
						("total_words", o.total_words,
							ea.total_words),
						("subseg_id", o.subseg_id, ea.subseg_id),
						("total_word_len", o.total_word_len,
							ea.total_word_len),
						("word_id", o.word_id, ea.word_id),
						("n_circ", o.n_circ, ea.n_circ),
						("total_word_segs", o.total_word_segs,
							ea.total_word_segs),
						("act_word_subseg_size",
							o.act_word_subseg_size,
							ea.act_word_subseg_size),
						("batch_r", o.batch_r, ea.batch_r),
						("batch_v", o.batch_v, ea.batch_v),
						("r_all_words", o.r_all_words,
							ea.r_all_words),
						("r_kzg_len", o.r_kzg_len, ea.r_kzg_len),
						("r_vec_r", o.r_vec_r, ea.r_vec_r),
						("r_vec_v", o.r_vec_v, ea.r_vec_v),
						("r_word_i", o.r_word_i, ea.r_word_i),
						("accumulated_word_len",
							o.accumulated_word_len,
							ea.accumulated_word_len),
					];
					let mut det = String::new();
					for (n, a, b) in pairs.iter() {
						if a != b {
							det.push_str(&format!(
								" {}:{}->{}", n, a, b));
						}
					}
					if !det.is_empty() {
						emit_stdout(format!(
							"DEBUG USE 69801.15.5: idx={} \
							ei overwrite delta:{}", idx, det));
					}
				}
				vea[idx] = ea; //UPDATE.
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
				log_perf(job_id, log_level+2, &format!("PERF 1009 -- Pass 2. update extra info. "), &mut gt_p2);
			}//end for while remaining word 
			log_perf(job_id, log_level+2, &format!("PERF 1008: {} - Pass 2. END generate cmF for word_id: {} of {}, fname: {}, word_len: {}. ", phase_name, word_id, num_words, word_fname, format_bytes(word.len()*31)), &mut gtw2);
			word_id += 1;
		} //for each word
		assert!(num_steps==vea.len(), "num_steps: {}, vea.len: {}", num_steps, vea.len());


		let m_pass2_2 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 3: generate cmF, mem: {} MB for total_word_len: {}: ", phase_name, if m_pass2_2>m_pass2_1 {m_pass2_2-m_pass2_1} else {0}, format_bytes(total_wd_len*31)) , &mut gt1);

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
				false,None,Some(job_id), "self")); //note part2 checked later
			let ind_prf = BatchProcessor::<E,LK,S,CS1E,H>::prove_individual(pk, 
				&snark_inp, &words, &ind_claim,
				idx_ind_proof);
			let _res = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(vk, idx_ind_proof, &ind_claim, &batch_proof, &ind_prf,
				Some(job_id), "self");
			if B_DEBUG { assert!(_res); }
			Some((batch_proof, ind_prf))
		}else{
			None
		};
		//self.batch_pk = None; //clear the RAM removed because &self is used and Arc handles cleanup
		let m6 = get_mem_usage_mb();
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 4: generate batch prf, mem: {} MB for words: {}, n_steps: {}: ", phase_name, if m6>m5 {m6-m5} else {0}, words.len(), n_steps) , &mut gt1);

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
		//S107: seed the in-circuit chain at ZERO so the final
		//state z_n[0] equals the pass-1 hash_cmF that seeded
		//ch/rc; the decider discloses z_n[0] (Phase1CircuitRet).
		let z_0 = [vec![zero, z0_part2_hash], vec![zero; 4]].concat();
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 5: prep for proving steps words: {}, n_steps: {}: total_word_len: {}. ", phase_name,  words.len(), n_steps, total_wd_len) , &mut gt1);

		//6. build the nova instance
        let mut nova =
            FoldPotSuper::<E,P, C2G2, C1, GC1, C2, GC2, FC,
			CS1, CS2, CS1E, LK, GM, H>::init_adv(
                &self.nova_param,
				p_circuits.clone(),
                z_0.clone(),
				p_circuits.len(),
				pc_0_val,
				self.b_full_mode,
				ch,
				rc,
				total_words,
				Some(vec_grp_cmF),
				job_id
				//None,
            )
            .unwrap();
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 6: build nova. Cost depends on cs1e.len. Now proving ...", phase_name) , &mut gt1);


		//6. LOOP prove steps
        let mut rng = ark_std::test_rng();
		let mut idx = 0;
		let mut num_steps = 0;
		let _lk_len = self.lkup.get_size();
		//let mut wi = 0;
		let mut gt_prove_step = GTimer::new();
		let m7 = get_mem_usage_mb();
		let mut word_id = 1;
		let mut _start = 0; //global position in ENTIRE sequence for update lkup
							//share in each statement
		for word in iter_words3{
			if _word_cap > 0 && word_id > _word_cap {
				break;
			}
			let mut gtw_word = GTimer::new();
			let mut gtw_word0 = GTimer::new();
			let mut prev_adv = None;
			let mut prev_stmt = None;
			let mut remaining = word.clone();
			let mut subseg_id = 1;
			let word_info = &vec_word_info[word_id-1];
			let word_fname = &vec_word_fnames[word_id-1];
			if word_id == 1 || word_id % 100 == 0 || word_id == num_words {
				log(job_id, LOG1, &format!(
					"PROGRESS fold [{}] word {} of {}", phase_name,
					word_id, num_words));
			}
			log_perf(job_id, log_level+2, &format!("PERF 1008: {} - Pass 3. START prove steps for word_id: {}, fname: {}, word_len: {}. ", phase_name, word_id, word_fname, format_bytes(word.len()*31)), &mut gtw_word);
			while remaining.len()>0{
				let mut gt_fold = GTimer::new();
				//6.1 compute the problem statement instance again
				// with the correct cmF
				let j = field_to_usize(&vea[idx].pc_i1);
				let circ = &p_circuits[j];
				let share_size = circ.get_stmt_config().lookup_share_size;
				let ei = &vea[idx];
				let act_len = field_to_usize(&vea[idx].act_word_subseg_size);
				let frag = remaining[0..act_len].to_vec();
				remaining = remaining[act_len..].to_vec();

				//aggressive forward halo: emit the successor prefix so
				//this chunk's IDX_OUP halo matches the next chunk's
				//authenticated IDX_INP prefix (else sum_inp!=sum_oup).
				let m_halo = lock_unwrap!(circ.get_mapper())
					.get_capacity().halo_nibbles();
				let wi_owned = Self::with_chunk_halo(word_info,
					&remaining, m_halo);
				let wi_ref = wi_owned.as_ref().unwrap_or(word_info);
				let res = lock_unwrap!(circ.get_mapper())
					.gen_nd_advice(&frag, wi_ref, prev_adv, subseg_id - 1, job_id);
				assert!(res.is_ok(), "UNABLE to generate advice for word id: {}, segment_id: {}", word_id, subseg_id);
				let cur_adv = res.unwrap();
				log_perf(job_id, log_level+1, &format!("PERF 1009: -- Pass 3. gen advice for word_id: {}, seg_id: {}", word_id, subseg_id), &mut gt_fold);

				let stmt_res = lock_unwrap!(circ.get_mapper()).build_statement(&frag, &prev_stmt, self.lkup.clone(), ei, cur_adv.clone(), share_size, false, job_id);
				assert!(stmt_res.is_ok());
				prev_adv = Some(cur_adv);
				let mut stmt = stmt_res.unwrap();
				log_perf(job_id, log_level+1, &format!("PERF 1009: -- Pass 3. gen stmt"), &mut gt_fold);

				stmt.update_lookup(_start,_start+share_size, &self.lkup, &m_map);
				_start += share_size;
				// DEBUG USE 69801.15: compare the pass-3 statement
				// against the pass-2 digest; exact element diff for
				// the early steps. Remove by tag 69801.
				if b_probe15 && idx < probe15_hashes.len() {
					let v3 = stmt.to_vec();
					let h3 = probe15_hash(&v3);
					let h2 = &probe15_hashes[idx];
					let bad: Vec<usize> = h2.iter().zip(h3.iter())
						.enumerate().filter(|(_, (a, b))| a != b)
						.map(|(k, _)| k).collect();
					if !bad.is_empty() {
						let n_show = bad.len().min(8);
						emit_stdout(format!(
							"DEBUG USE 69801.15.1: idx={} pass2!=\
							pass3: bad_chunks={} of {} first={:?} \
							elem_starts={:?}",
							idx, bad.len(), h2.len(),
							&bad[..n_show],
							bad[..n_show].iter().map(|c|
								c * PROBE15_CHUNK)
								.collect::<Vec<usize>>()));
						if idx < probe15_full.len() {
							let v2 = &probe15_full[idx];
							let mut first: Vec<usize> = vec![];
							let mut det = String::new();
							let mut nd = 0usize;
							let n = v2.len().min(v3.len());
							for k in 0..n {
								if v2[k] != v3[k] {
									if first.len() < 8 {
										first.push(k);
									}
									if nd < 4 {
										det.push_str(&format!(
											" [{} {} {}]",
											k, v2[k], v3[k]));
									}
									nd += 1;
								}
							}
							emit_stdout(format!(
								"DEBUG USE 69801.15.2: idx={} \
								n_diff={} first8={:?} det:{}",
								idx, nd, first, det));
						}
					} else if idx % 32 == 0 {
						emit_stdout(format!(
							"DEBUG USE 69801.15.3: idx={} \
							pass2==pass3 ok", idx));
					}
				}
				log_perf(job_id, log_level+1, &format!("PERF 1009: -- Pass 3. update lkup: share size: {}", share_size), &mut gt_fold);

				//2.2. prove step
				let v_stmt = stmt.to_vec();
				let stmt_len = v_stmt.len();
				let other_inst = None;
				nova.pc_i = vea[idx].pc_i;
				nova.pc_i1 = vea[idx].pc_i1;
				//New8 P4: structured per-step fold cost for the
				//legacy-vs-neo comparison (the PERF 1009 line below is
				//log-only). Cleared by utils::consts::reset_sat().
				let t_step = std::time::Instant::now();
            	nova.prove_step(&mut rng, v_stmt, other_inst)
					.expect("prove step error");
				utils::consts::record_step_time(
					t_step.elapsed().as_micros() as usize);
				log_perf(job_id, log_level+1, &format!("PERF 1009: -- Pass 3. prove_step cost for word_id: {}, seg_id: {}, stmt_len: {}", word_id, subseg_id, stmt_len), &mut gt_fold);

				//2.3 update 
				prev_stmt = Some(stmt);
				idx += 1;
				num_steps +=1;
				subseg_id += 1;
			}//end for while remaining word 
			word_id += 1;
			log_perf(job_id, log_level+2, &format!("PERF 1008: {} - Pass 3. END prove steps for word_id: {} of {}, fname: {}, word_len: {}. ", phase_name, word_id, num_words, word_fname, format_bytes(word.len()*31)), &mut gtw_word0);
		} //for each word
		assert!(num_steps==vea.len(), "num_steps: {}, vea.len: {}", num_steps, vea.len());
        assert_eq!(C1::ScalarField::from(num_steps as u32), nova.i);
		let m8 = get_mem_usage_mb();
		let mb_speed = get_speed(total_wd_len, &mut gt_prove_step); 
		log_perf(job_id, log_level, &format!(
			"PERF 1007: {} step 7: PROVE STEPS done for n_steps: {}. total_word_len: {}. RAM increased: {} MB. Total RAM: {} GB. Speed: mb_speed {} MB/hr", phase_name,  n_steps, total_wd_len, if m8>m7 {m8-m7} else {0}, m8/1024, mb_speed) , &mut gt1);

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
			"PERF 1007: {} step 8: verify. ", phase_name ) , &mut gt1);

		Ok((nova, num_steps, batch_prfs, claim_pack))

	}

	
}

// -- Utility Functions --
/// return processing speed MB/hour
/// NOTE: we assume Bn254 (254-bit) - other curves need adjustment!
pub fn get_speed(word_len_in_fr: usize, timer: &mut GTimer)->f32{
	timer.stop();
	let ns = timer.time_ns();
	if ns == 0 { return 0.0; }
	let bytes = word_len_in_fr * 31; //31 bytes per 254-bit field element
									//(may need change if this is for a
									//different curve)
	let mb = (bytes as f64) / 1_000_000.0f64;
	let hr = (ns as f64) / ((3600usize*1000*1000*1000) as f64);
	(mb/hr) as f32
}
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
/// 2026-05-15: opt-in PR_SET_PTRACER_ANY so deadlock_detect.py
/// (a grandparent of the prover process) can gdb-attach despite
/// YAMA ptrace_scope=1 (Ubuntu default). No-op when env var is
/// unset, so production runs are unaffected. The unsafe block is
/// confined to one prctl call; the kernel has no safe Rust wrapper
/// in std, the call is bounded (sets one process flag), and failure
/// silently returns -1.
fn enable_ptrace_any() {
	if std::env::var("ZKR_ALLOW_PTRACE_ANY").is_err() {
		return;
	}
	extern "C" {
		fn prctl(opt: i32, a2: u64, a3: u64,
				 a4: u64, a5: u64) -> i32;
	}
	const PR_SET_PTRACER: i32 = 0x59616d61;
	unsafe { prctl(PR_SET_PTRACER, u64::MAX, 0, 0, 0); }
}

/// 2026-05-16: install a process-wide panic hook so any panic in any
/// rayon worker (e.g. check_logup assertion in utils.rs:619 / the
/// `gen_step_cs step 10.5` sigs-discharge check in sigma_ir1cs.rs)
/// prints file:line + message + thread name and then aborts the
/// WHOLE prover process. Without this, rayon's `for_each` in
/// foldpot_main buffers panics until all surviving job closures
/// drain, which can hang the process for hours behind the stall
/// watchdog. Default behavior is fail-fast; set ZKR_NO_FAIL_FAST=1
/// to opt out and restore rayon's buffered-panic behavior.
fn install_fail_fast_panic_hook() {
	// scale mode (b_scale_catch_caperr) needs panics to UNWIND so the
	// bump-retry's catch_unwind can catch the 0-word advice panic; don't abort.
	if std::env::var("ZKR_NO_FAIL_FAST").is_ok()
		|| read_global_config().b_scale_catch_caperr {
		return;
	}
	let default_hook = std::panic::take_hook();
	std::panic::set_hook(Box::new(move |info| {
		default_hook(info);
		let loc = info.location()
			.map(|l| format!("{}:{}:{}",
				l.file(), l.line(), l.column()))
			.unwrap_or_else(|| "<unknown>".to_string());
		let msg = info.payload()
			.downcast_ref::<&str>()
			.map(|s| s.to_string())
			.or_else(|| info.payload()
				.downcast_ref::<String>().cloned())
			.unwrap_or_else(||
				"<non-string panic payload>".to_string());
		let tname = std::thread::current().name()
			.unwrap_or("<unnamed>").to_string();
		eprintln!(
			"FAIL-FAST: prover panic in thread '{}' \
			 at {}: {}",
			tname, loc, msg);
		let _ = std::io::stderr().flush();
		let _ = std::io::stdout().flush();
		std::process::abort();
	}));
}

/// Preflight: a low vm.max_map_count makes mimalloc abort on a tiny
/// mmap once its purge fragments the address space. Seen on the
/// server: SIGABRT on a 192-byte alloc at 525 GB RSS with 8 parallel
/// provers and the kernel default 65530 (glibc never hit this: few
/// large arenas). Estimate the floor from job size: a small process
/// baseline plus a per-prover budget proportional to the largest
/// job's packed-field count, times the job count. Stop early with
/// the exact sysctl fix instead of dying hours in. Bypass with
/// ZKR_SKIP_MAP_COUNT_CHECK=1.
fn preflight_check_map_count(n_jobs: usize, max_job_fields: usize)
	-> Result<(), Error>
{
	if std::env::var("ZKR_SKIP_MAP_COUNT_CHECK").is_ok() {
		return Ok(());
	}
	#[cfg(not(target_os = "linux"))]
	let _ = (n_jobs, max_job_fields);
	#[cfg(target_os = "linux")]
	{
		let cur = match std::fs::read_to_string(
			"/proc/sys/vm/max_map_count")
			.ok()
			.and_then(|s| s.trim().parse::<usize>().ok()) {
			Some(v) => v,
			None => return Ok(()), // can't read: don't block
		};
		// Recalibrated from the 2026-05-25 server crash: 8 jobs of
		// 34071 fields each exhausted vm.max_map_count=1048576
		// (mimalloc ENOMEM on free/alloc OS memory -- a munmap/mmap
		// that splits/adds a VMA fails once the count hits the
		// ceiling, even with ~1 TB free). That run needed >1.05M
		// VMAs, i.e. >~4 per job*field; bias well above it (a false
		// abort just asks for a free sysctl bump, a false pass
		// crashes hours in). Small base so tiny jobs (small_data)
		// still pass on a default-65530 kernel.
		const VMA_BASE: usize = 32_768;
		const VMA_PER_FIELD: usize = 16;
		let needed = VMA_BASE
			+ n_jobs.max(1) * max_job_fields * VMA_PER_FIELD;
		if cur < needed {
			let want = needed.next_power_of_two();
			let msg = format!(
				"PREFLIGHT ABORT: vm.max_map_count={} < est need \
				 {} ({} job(s), {} packed fields each). mimalloc \
				 hits ENOMEM on mmap/munmap once the VMA count \
				 reaches vm.max_map_count (even with free RAM), \
				 aborting the run. Fix on the server \
				 (free, no memory cost):\n  \
				 sudo sysctl -w vm.max_map_count={}\n  \
				 # persist:\n  echo 'vm.max_map_count={}' | sudo \
				 tee /etc/sysctl.d/99-zkregplus.conf && sudo \
				 sysctl --system\n  \
				 # or bypass: export ZKR_SKIP_MAP_COUNT_CHECK=1",
				cur, needed, n_jobs, max_job_fields, want, want);
			emit_stdout(msg.clone());
			log(0, ERR, &msg);
			return Err(Error::Other(msg));
		}
		emit_stdout(format!(
			"PREFLIGHT ok: vm.max_map_count={} >= need {} ({} \
			 job(s), {} fields each)",
			cur, needed, n_jobs, max_job_fields));
		// Big-job breadcrumb: the estimate is a heuristic floor, so
		// a pass is not a guarantee. mimalloc frees RAM via many
		// small OS mappings and can still exhaust max_map_count;
		// leave a pointer so a later SIGABRT is diagnosed in seconds.
		const BIG_JOB_VMAS: usize = 524_288;
		if needed > BIG_JOB_VMAS {
			let mut rec = needed.next_power_of_two();
			if rec <= cur { rec = (cur + 1).next_power_of_two(); }
			let warn = format!(
				"WARN big job ({} job(s), {} fields, ~{} VMAs est): \
				 we use mimalloc, which frees RAM via many small OS \
				 mappings and can still exhaust vm.max_map_count \
				 (now {}). If this run aborts with 'memory \
				 allocation of N bytes failed' / SIGABRT while RAM \
				 is free, that's the VMA ceiling -- raise it and \
				 rerun:\n  \
				 sudo sysctl -w vm.max_map_count={}",
				n_jobs, max_job_fields, needed, cur, rec);
			emit_stdout(warn.clone());
			log(0, LOG1, &warn);
		}
	}
	Ok(())
}

/// Inputs: lkup which encodes the regex automata,
/// jobs: a collection of jobs where each job has:
/// (1) vec_words: the vector of words to process,
/// (2) idx_individual_prf: the index of the SAMPLE individual proof to produce.
/// (3) the corresponding word_info for each word in vec_words.
///
/// NOTE: vec_circ should be ordered as required by Driver (see its doc)
/// NOTE: jobs is mut because we might PAD all jobs so that they have
/// the same number of words.
pub fn foldpot_main<E:Pairing<G1=C1,G2=C2G2>,P:PairingVar<E,CF3<C2G2>>+std::fmt::Debug+Clone,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, FC, S, LK, GM, const H: bool>(
        lkup: Arc<LK>, //the lookup table defines the regex automatas
        vec_circ: Vec<Vec<FC>>,
        jobs: &mut Vec<FoldPotJob<E::ScalarField>>,
        cache_dir: &str,
) -> Result<(), Error>
where
	<E as Pairing>::ScalarField: ColEle,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	//S107: CS=CS1 -- Driver::new's impl block requires it.
    FC: FCircuit<C1::ScalarField>
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1,CS=CS1>
		+ Clone + Send + Sync + CloneDeep,
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
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2, H>>::VerifierParams: Send + Sync,
    S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
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
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	C1::Config: SWCurveConfig,
	C2::Config: SWCurveConfig,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug + Send + Sync,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	// 2026-05-21 (Lever 2+3): Send needed so Arc<RwLock<Option<keys>>>
	// is Sync across the rayon for_each. The bound is expressed via
	// E::ScalarField because that is how rustc projects S::ProvingKey
	// at the use site (C1::ScalarField is provably equal but not
	// automatically unified through the projection).
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
		// 2026-05-15: allow gdb attach from non-parent same-uid procs
		// (e.g. deadlock_detect.py). No-op unless ZKR_ALLOW_PTRACE_ANY
		// is set in env. See enable_ptrace_any() above.
		enable_ptrace_any();

		// 2026-05-16: abort the whole prover on any rayon-worker panic
		// (e.g. check_logup sums mismatch). Default ON; opt out with
		// env ZKR_NO_FAIL_FAST=1. See install_fail_fast_panic_hook().
		install_fail_fast_panic_hook();

		let mut gt_all = GTimer::new();
		let mut gt_all_0 = GTimer::new();
		let log_level = LOG1;
		log(0, log_level, &format!("===== fold_pot starts with {} jobs =====",
			jobs.len()));
		utils::os::print_computer_config(Some("foldpot_main"));

		// === env-var hook for diagnostic knobs (no-op when unset). ===
		// Set in deadlock_detect.py; defaults preserve regular runs.
		if let Ok(s) = std::env::var("ZKR_STALL_WATCHDOG_SECS") {
			if let Ok(n) = s.parse::<usize>() {
				get_global_config().stall_watchdog_secs = n;
			}
		}
		if let Ok(s) = std::env::var("ZKR_WORD_CAP_PER_JOB") {
			if let Ok(n) = s.parse::<usize>() {
				get_global_config().word_cap_per_job = n;
			}
		}

		// === preflight: vm.max_map_count vs mimalloc purge ===
		{
			let max_job_fields = jobs.iter()
				.map(|j| j.vec_words.iter()
					.map(|w| w.len()).sum::<usize>())
				.max().unwrap_or(0);
			preflight_check_map_count(
				jobs.len(), max_job_fields)?;
		}

		// === stall watchdog (diagnostic). Off when secs == 0. ===
		// Spawns a background thread that polls every 30s and checks
		// the mtimes of {proj_root}/data/cache/logs/log_job_<id>.txt
		// for every job. If AT LEAST 3 per-job logs have each been
		// silent for >= stall_watchdog_secs, dumps per-thread kernel
		// state to /tmp/stall_dump_<pid>.txt and aborts the process.
		// Catches partial wedges (e.g., 3 of 8 jobs stuck) without
		// waiting for all-jobs silence.
		{
			let secs = read_global_config().stall_watchdog_secs;
			let n_jobs = jobs.len();
			if secs > 0 && n_jobs > 0 {
				let pid = std::process::id();
				// Resolve project root ONCE on this thread, before the
				// initial sleep; proj_root() canonicalizes the CWD-based
				// path, so we capture it while the process CWD is the
				// known-good launch dir.
				let log_root = utils::os::proj_root();
				std::thread::spawn(move || {
					use std::time::{Duration, SystemTime};
					use std::fs;
					// Wait one threshold before first check so early
					// startup (key load, etc.) is not flagged.
					std::thread::sleep(Duration::from_secs(
						secs as u64));
					loop {
						std::thread::sleep(Duration::from_secs(30));
						let now = SystemTime::now();
						let mut silences: Vec<(usize, u64)> =
							Vec::with_capacity(n_jobs);
						let mut any_missing = false;
						for j in 0..n_jobs {
							let p = format!(
								"{}/data/cache/logs/log_job_{}.txt",
								log_root, j);
							match fs::metadata(&p)
								.and_then(|m| m.modified()) {
								Ok(t) => {
									let d = now.duration_since(t)
										.unwrap_or(Duration::ZERO)
										.as_secs();
									silences.push((j, d));
								},
								Err(_) => { any_missing = true; }
							}
						}
						if any_missing { continue; }
						let stalled: Vec<&(usize, u64)> = silences
							.iter()
							.filter(|(_, d)| (*d as usize) >= secs)
							.collect();
						if stalled.len() >= 3 {
							let dump = format!(
								"/tmp/stall_dump_{}.txt", pid);
							let mut s = String::new();
							s.push_str(&format!(
								"=== watchdog fire pid={} \
								 stalled={}/{} threshold={}s \
								 ===\n",
								pid, stalled.len(), n_jobs, secs));
							s.push_str("per-job silence(s): ");
							for (j, d) in &silences {
								s.push_str(&format!(
									"[j{}={}s]", j, d));
							}
							s.push('\n');
							let task_dir = format!(
								"/proc/{}/task", pid);
							if let Ok(rd) = fs::read_dir(&task_dir) {
								for ent in rd.flatten() {
									let p = ent.path();
									let tid = ent.file_name()
										.into_string()
										.unwrap_or_default();
									s.push_str(&format!(
										"\n=== tid={} ===\n", tid));
									if let Ok(w) = fs::read_to_string(
										p.join("wchan")) {
										s.push_str(&format!(
											"wchan: {}\n", w.trim()));
									}
									if let Ok(st) =
										fs::read_to_string(
											p.join("status")) {
										for ln in st.lines().take(3){
											s.push_str(&format!(
												"  {}\n", ln));
										}
									}
									if let Ok(stk) =
										fs::read_to_string(
											p.join("stack")) {
										s.push_str("stack:\n");
										for ln in stk.lines()
											.take(12) {
											s.push_str(&format!(
												"  {}\n", ln));
										}
									}
								}
							}
							let _ = fs::write(&dump, &s);
							// Best-effort flush of the stdout drainer.
							std::thread::sleep(Duration::from_secs(2));
							std::process::exit(1);
						}
					}
				});
			}
		}
		// === end stall watchdog ===
        let cache_base = std::path::Path::new(&utils::os::proj_root()).join("data/cache").join(cache_dir);
        if read_global_config().b_write_snark_cache && !cache_base.exists(){
           std::fs::create_dir_all(&cache_base).expect("create cache dir err");
        }
        // Auto-build on a cold/partial snark cache. Run-mode requests
        // b_read_snark_cache, but the decider keys + Pedersen sidecars
        // exist only after a prior write run. If any required file is
        // missing, regenerate everything THIS run by flipping to write
        // -mode: keys are built via circuit_specific_setup and keys +
        // sidecars persisted, so the next run reads them. A complete
        // cache flips nothing, so warm runs are byte-identical.
        if read_global_config().b_read_snark_cache {
            let need = ["g16_main.key", "g16_main.key.meta",
                "g16_cp.key", "g16_cp.key.meta",
                "g16_main.sidecar.cf", "g16_cp.sidecar.cf",
                "g16_cp.sidecar.cp"];
            let missing: Vec<&str> = need.iter().copied()
                .filter(|f| !cache_base.join(f).exists()).collect();
            if !missing.is_empty() {
                let _ = std::fs::create_dir_all(&cache_base);
                get_global_config().b_read_snark_cache = false;
                get_global_config().b_write_snark_cache = true;
                log(0, ERR, &format!(
                    "PERF 1004: snark cache cold/partial at {:?} \
                     (missing {:?}); building + persisting this run",
                    cache_base, missing));
            }
        }
        let b_read_snark_cache = read_global_config().b_read_snark_cache;
		let _b_write_snark_cache = read_global_config().b_write_snark_cache;
        // 2026-05-21 (Lever 2A): defer cp_key load until Phase 2 to free
        // ~77 GiB of RAM during all of Phase 1. cp_key meta existence is
        // still asserted upfront so a missing cache fails fast.
        let mut cached_main_keys_init: Option<(S::ProvingKey,
            S::VerifyingKey)> = None;

        if b_read_snark_cache {
			let main_path = cache_base.join("g16_main.key");
			let main_path_meta = cache_base.join("g16_main.key.meta");
			let cp_path_meta = cache_base.join("g16_cp.key.meta");
			assert!(main_path_meta.exists(),
				"main: {:?} not exist", main_path_meta);
			assert!(cp_path_meta.exists(), "cp_path: {:?} not exist",
				cp_path_meta);
			if let Ok(keys) = read_g16key::<C1::ScalarField, S>(&main_path, 0) {
				cached_main_keys_init = Some(keys);
			}
        }
        // 2026-05-21 (Lever 2+3): wrap both keys in Arc<RwLock> so the
        // last finisher of each phase can drop them in place. cp_key is
        // lazily loaded by the first job that reaches Phase 2.
        let cached_main_keys: Arc<RwLock<Option<(S::ProvingKey,
            S::VerifyingKey)>>> =
            Arc::new(RwLock::new(cached_main_keys_init));
        let cached_cp_keys: Arc<RwLock<Option<(S::ProvingKey,
            S::VerifyingKey)>>> = Arc::new(RwLock::new(None));
        let phase1_snark_done = Arc::new(AtomicUsize::new(0));
        let phase2_snark_done = Arc::new(AtomicUsize::new(0));


	//0. preprpcessing jobs to make sure that all have the
	//same number of words
	let global_max_words = jobs.iter().map(|job| job.vec_words.len())
		.max().unwrap_or(0);

	let (min_word, min_word_info, min_word_fname) = jobs.iter()
		.flat_map(|j| j.vec_words.iter()
			.zip(j.vec_word_info.iter())
			.zip(j.vec_word_fnames.iter()))
		.min_by_key(|((w, _), _)| w.len())
		.map(|((w, info), fname)| (w.clone(), info.clone(), fname.clone()))
		.unwrap_or((vec![], WordInfo::dummy(), "dummy".to_string()));

	for job in jobs.iter_mut() {
		while job.vec_words.len() < global_max_words {
			job.vec_words.push(min_word.clone());
			job.vec_word_info.push(min_word_info.clone());
			job.vec_word_fnames.push(min_word_fname.clone());
		}
	}

	// 0b. F-level pad: pad each word to a multiple of max_word_len
	// so every frag fed downstream has frag.len() == max_word_len,
	// i.e. act_seg_len == word_seg.len() always. The pad F-elements
	// come from the canonical pseudo-random stream so the gadget DFA
	// and discharge_prover see identical pad nibbles. NOTE the per
	// -word reported `total_word_len` and `accumulated_word_len` in
	// StatementExtraInfo still refer to the REAL (pre-pad) content
	// size — see Step 3 of the pad-invariant rework — so downstream
	// sig-position math is unaffected. For max_word_len == 1 this
	// loop is a no-op (sub-F pad already handled by pack_nibbles).
	let max_wlen_pad = lock_unwrap!(vec_circ[0][0].get_mapper())
		.max_word_len();
	for job in jobs.iter_mut() {
		for w in job.vec_words.iter_mut() {
			let padded = pad_word_to_multiple::<C1::ScalarField>(
				w, max_wlen_pad);
			*w = padded;
		}
	}

	let global_max_total_n = jobs.iter().map(|job| job.vec_words.iter()
		.map(|x| x.len()).sum::<usize>()).max().unwrap_or(0);

	log_perf(0, log_level,
		&format!("PERF 1005: FoldPot Step 0: Load Keys and Pad Jobs"),
			&mut gt_all
	);

	//1. Fix the circuit with dummy statements
	// We build a dummy word of max_word_len F-elements filled with
	// the canonical pseudo-random pad stream. Under the
	// pad-invariant rework the gadget no longer forces extracted
	// pad nibbles to zero, and an all-zero dummy would leave the
	// DFA in a degenerate state during preprocess (capacity
	// profile under-shoots). Pseudo-random pad exercises the
	// gadgets like a typical pad region in a real run.
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
			let wlen = lock_unwrap!(circ.get_mapper()).max_word_len();
			// Generate exactly wlen F-elements packed from
			// gen_pad_nibbles_fe(0, wlen*62) — full pseudo-random
			// pad word for preprocess (pad_word_to_multiple([],
			// wlen) would return empty since 0 is already a
			// multiple of anything).
			let frag = pack_nibbles(
				&gen_pad_nibbles_fe::<C1::ScalarField>(0, wlen * 62));
			let prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>> = None; //fine to set None
			let r_advice= lock_unwrap!(circ.get_mapper())
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
			let stmt_res = lock_unwrap!(circ.get_mapper())
				.build_statement(&frag, &prev_stmt, lkup.clone(), &ei, advice, //REMOVE LATER clone()
				lk_share_size, true, 0); //dummy mode
			assert!(stmt_res.is_ok());
			circ.set_dummy_stmt(stmt_res.unwrap());
			id += 1;
		}
	}
	log_perf(0, log_level, 
		&format!("PERF 1005: FoldPot Step 1: build dummy stmt for all circs"), &mut gt_all
	);


	//2. create the driver1 for the 1st phase
	let poseidon_config_global = poseidon_canonical_config::<C1::ScalarField>();
	let b_full1 = false;
	let mut driver1 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,FC,S,LK,GM,H>
	::new(poseidon_config_global.clone(), lkup.clone(),
		vec_circ.clone(), rand::rngs::OsRng, b_full1,
		global_max_total_n, global_max_words
	);
	log_perf(0, log_level, &format!("PERF 1005: FoldPot: Step 2: set up driver 1"), &mut gt_all);

	//3. create the driver2 for Phase2 CyclePair Circ
	let n_circs_cp = 1;
	let circ_cyclepair = create_sigma_fold_pair::<C1::ScalarField, C1, CS1, LK, H>(n_circs_cp, poseidon_config_global.clone());
	let vec_circ_cp = vec![vec![ circ_cyclepair] ];
	let b_full2 = true;
	let lk_p2 = LK::new(vec![]);
	let lkup_p2 = Arc::new(lk_p2);
	let mut driver2 = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, FoldPairMapper<CF1<C1>,LK>,H>,S,LK,FoldPairMapper<CF1<C1>,LK>,H>
		::new(poseidon_config_global.clone(), lkup_p2, vec_circ_cp, rand::rngs::OsRng, b_full2, global_max_total_n, global_max_words);

	//cols=variables, io_l=public io len). Removable measurement print.
	for (i,vp) in driver1.nova_param.1.vec_vp.iter().enumerate(){
	}

	//3.5 Sidecar: save/load Pedersen params + R1CS hashes to keep
	// circuit-constant data stable across snark-cache runs.
	// See decider_eth_circuit_super.rs lines 980-983, 1353-1356.
	{
		use crate::folding::foldpot::utils::{B_DEBUG3,
			read_pedersen_params, write_pedersen_params};
		let mut gt_sc = GTimer::new();
		let main_sc_meta = cache_base.join("g16_main.sidecar.meta");
		let cp_sc_meta = cache_base.join("g16_cp.sidecar.meta");
		let main_sc_cf = cache_base.join("g16_main.sidecar.cf");
		let cp_sc_cf = cache_base.join("g16_cp.sidecar.cf");
		let cp_sc_cp = cache_base.join("g16_cp.sidecar.cp");

		// R1CS drift-check hashes are only computed under B_DEBUG3.
		let (d1_r1cs_hashes, d1_cf_r1cs_hash,
			d2_r1cs_hashes, d2_cf_r1cs_hash):
			(Option<Vec<[u8;32]>>, Option<[u8;32]>,
			 Option<Vec<[u8;32]>>, Option<[u8;32]>) = if B_DEBUG3 {
			use crate::folding::foldpot::utils::hash_r1cs;
			let d1_r1cs_hashes: Vec<[u8;32]> = driver1.nova_param.1
				.vec_vp.iter().map(|vp| hash_r1cs(&*vp.r1cs))
				.collect();
			let d1_cf_r1cs_hash = hash_r1cs(&*driver1.nova_param.1
				.vec_vp[0].cf_r1cs);
			let d2_r1cs_hashes: Vec<[u8;32]> = driver2.nova_param.1
				.vec_vp.iter().map(|vp| hash_r1cs(&*vp.r1cs))
				.collect();
			let d2_cf_r1cs_hash = hash_r1cs(&*driver2.nova_param.1
				.vec_vp[0].cf_r1cs);
			log_perf(0, LOG2, &format!(
				"PERF 1004: sidecar hash_r1cs done. d1 circs: {}, d2 circs: {}",
				d1_r1cs_hashes.len(), d2_r1cs_hashes.len()),
				&mut gt_sc);
			(Some(d1_r1cs_hashes), Some(d1_cf_r1cs_hash),
			 Some(d2_r1cs_hashes), Some(d2_cf_r1cs_hash))
		} else {
			(None, None, None, None)
		};

		if read_global_config().b_write_snark_cache {
			write_pedersen_params::<C2>(&main_sc_cf,
				&*driver1.nova_param.0.vec_pp[0].cf_cs_pp);
			write_pedersen_params::<C2>(&cp_sc_cf,
				&*driver2.nova_param.0.vec_pp[0].cf_cs_pp);
			write_pedersen_params::<C2>(&cp_sc_cp,
				&*driver2.nova_param.0.vec_pp[0].cp_cs_pp);
			log_perf(0, LOG2, &format!(
				"PERF 1004: sidecar WRITE pedersen done"),
				&mut gt_sc);
			if B_DEBUG3 {
				write_sidecar_meta(&main_sc_meta,
					d1_r1cs_hashes.as_ref().unwrap(),
					d1_cf_r1cs_hash.unwrap());
				write_sidecar_meta(&cp_sc_meta,
					d2_r1cs_hashes.as_ref().unwrap(),
					d2_cf_r1cs_hash.unwrap());
				log_perf(0, LOG2, &format!(
					"PERF 1004: sidecar WRITE meta done. main={:?}, cp={:?}",
					main_sc_meta, cp_sc_meta), &mut gt_sc);
			}
		}

		if b_read_snark_cache {
			if B_DEBUG3 {
				let (m_r1cs_hashes, m_cf_hash) = read_sidecar_meta(
					&main_sc_meta);
				assert_eq!(&m_r1cs_hashes,
					d1_r1cs_hashes.as_ref().unwrap(),
					"MainDeciderCircuit r1cs hashes mismatch (R1CS drifted across runs)");
				assert_eq!(m_cf_hash, d1_cf_r1cs_hash.unwrap(),
					"MainDeciderCircuit cf_r1cs hash mismatch");
				let (c_r1cs_hashes, c_cf_hash) = read_sidecar_meta(
					&cp_sc_meta);
				assert_eq!(&c_r1cs_hashes,
					d2_r1cs_hashes.as_ref().unwrap(),
					"CyclePairCircuit r1cs hashes mismatch");
				assert_eq!(c_cf_hash, d2_cf_r1cs_hash.unwrap(),
					"CyclePairCircuit cf_r1cs hash mismatch");
				log_perf(0, LOG2, &format!(
					"PERF 1004: sidecar READ r1cs-hash verify passed"),
					&mut gt_sc);
			}

			let d1_cf: PedersenParams<C2> = read_pedersen_params(
				&main_sc_cf);
			let d2_cf: PedersenParams<C2> = read_pedersen_params(
				&cp_sc_cf);
			let d2_cp: PedersenParams<C2> = read_pedersen_params(
				&cp_sc_cp);

			let d1_cf_arc = Arc::new(d1_cf.clone());
			for pp in driver1.nova_param.0.vec_pp.iter_mut() {
				pp.cf_cs_pp = d1_cf_arc.clone();
			}
			for vp in driver1.nova_param.1.vec_vp.iter_mut() {
				vp.cf_cs_vp = d1_cf.clone();
			}
			let d2_cf_arc = Arc::new(d2_cf.clone());
			let d2_cp_arc = Arc::new(d2_cp.clone());
			for pp in driver2.nova_param.0.vec_pp.iter_mut() {
				pp.cf_cs_pp = d2_cf_arc.clone();
				pp.cp_cs_pp = d2_cp_arc.clone();
			}
			for vp in driver2.nova_param.1.vec_vp.iter_mut() {
				vp.cf_cs_vp = d2_cf.clone();
				vp.cp_cs_vp = d2_cp.clone();
			}
			log_perf(0, LOG2, &format!(
				"PERF 1004: sidecar READ override of Pedersen params done"),
				&mut gt_sc);
		}
	}

	//4. set up mutex semaphore of size n_par_snark
	let n_par_snark = read_global_config().n_par_snark;
	let semaphore = Arc::new((Mutex::new(n_par_snark), Condvar::new()));
	let n_par_snark_cp = read_global_config().n_par_snark_cp;
	let semaphore_cp: Semaphore = Arc::new((Mutex::new(n_par_snark_cp), Condvar::new()));
	// Outer sema caps the ENTIRE snark proof-generation region. Config 0
	// = auto (sum of inner caps, the legacy behaviour); a smaller value
	// forces fewer concurrent deciders (lower peak RAM). Clamped to sum.
	let n_par_snark_sum = n_par_snark + n_par_snark_cp;
	let cfg_outer = read_global_config().n_par_snark_total;
	let outer_cap = if cfg_outer == 0 { n_par_snark_sum }
		else { cfg_outer.min(n_par_snark_sum) };
	let semaphore_outer: Semaphore =
		Arc::new((Mutex::new(outer_cap), Condvar::new()));
	let n_par_batch_claim = read_global_config().n_par_batch_claim;
	let semaphore_batch_claim: Semaphore = Arc::new((Mutex::new(n_par_batch_claim), Condvar::new()));
	// qa_pp lifted out so last finisher of each phase can drop it.
	let qa_pp_d1: Arc<RwLock<Option<QaNizkProverParams<E>>>> =
		Arc::new(RwLock::new(driver1.nova_param.0.qa_pp.take()));
	let qa_pp_d2: Arc<RwLock<Option<QaNizkProverParams<E>>>> =
		Arc::new(RwLock::new(driver2.nova_param.0.qa_pp.take()));
	log_perf(0, log_level, &format!("PERF 1005: FoldPot: Step 3: set up driver 2.\n=== Now Execute All Jobs =====\n"), &mut gt_all);

	// 2026-05-21 (Lever 2+3): captured before into_par_iter consumes jobs.
	// Used by last-finisher logic for main_key and cp_key drops.
	let n_jobs_total = jobs.len();

	// SCALE-MODE (get_global_config().b_scale_catch_caperr, e.g.
	// collect_scale_data_dlp): stash a job CapErr here instead of process::exit,
	// so it propagates as a catchable main-thread panic for the scale
	// bump-retry. Flag false (full_dlp / full_clam / full_dna) -> unchanged
	// (process::exit below).
	let scale_job_err: std::sync::Mutex<Option<Error>> =
		std::sync::Mutex::new(None);

	jobs.into_par_iter().enumerate().for_each(|(job_id, job)| {
		// NUMA (ZKR_NUMA=perjob): pin this job's worker thread + its per-word
		// allocations to node (job_id % n_nodes). No-op unless multi-node + flag.
		super::numa::bind_thread_to_node(job_id);
		let res = (|| -> Result<(), Error> {
                        let (pk_main_owned, vk_main_owned);
                        let (pk_cp_owned, vk_cp_owned);
		//0. retrieve the words and word_info
	  	log(job_id, log_level, &format!("--- Job {} starts ---", job_id));
	  	let mut gt1_0 = GTimer::new();
	  	let mut gt1 = GTimer::new();
	  	// gt_mem times MEM checkpoints around the main S::prove so they
	  	// do not reset gt1 (else PERF 1006 Step 3 misses the proof).
	  	let mut gt_mem = GTimer::new();
	  	let vec_words = &job.vec_words;
	  	let vec_words_info = &job.vec_word_info;
	  	let idx_individual_prf = job.idx_individual_prf;
	  	let vec_word_fnames = &job.vec_word_fnames;
	  	assert!(vec_word_fnames.len()==vec_words.len());
	  	let mut rng = rand::rngs::OsRng;
	  	let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();
	  	let max_total_n:usize = vec_words.iter().map(|x| x.len()).sum();

	  	let mut guard_outer: Option<SemaphoreGuard> = None;

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
	  		// Deep-clone this driver's circuits so that the mapper
	  		// `Arc<Mutex<>>` locks touched inside `pass_all`'s
	  		// per-subseg loop are independent across the 8 jobs
	  		// running in parallel here. Heavy immutable data
	  		// (ClamavDB, etc.) remains shared via `Arc::clone`
	  		// inside each component's manual clone impl.
			let mut gt_prove_steps = GTimer::new();
	  		let mut per_job_layered: Vec<Vec<FC>> = driver1.layered_circs
	  			.iter().map(|layer|
	  				layer.iter().map(|c| c.clone_deep_self()).collect()
	  			).collect();
	  		// 2026-05-15: stamp every per-job clone with this job's
	  		// id through the SigmaIR1CS::set_job_id impl on
	  		// SigmaIR1CS_Inst (sigma_ir1cs.rs), which fans out to
	  		//   (1) the inst's own `job_id` field,
	  		//   (2) the inner `gadget_mapper` (and recursively each
	  		//       sub-mapper and its gadgets), and
	  		//   (3) the inst's own per-job `gadgets` vec (the fresh
	  		//       Arcs produced by Option A in `clone_deep`).
	  		// Routing all three is required so per-gadget
	  		// `log_perf(self.job_id,..)` and the inner
	  		// `generate_step_constraints` log lines land in the
	  		// right log_job_<id>.txt instead of all collapsing
	  		// onto log_job_0.txt.
	  		for layer in per_job_layered.iter_mut() {
	  			for c in layer.iter_mut() {
	  				c.set_job_id(job_id);
	  			}
	  		}
	  		let per_job_circuits: Vec<FC> =
	  			per_job_layered.iter().flat_map(|l| l.iter().cloned())
	  			.collect();
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
				job_id,
				semaphore_batch_claim.clone(),
				&per_job_layered,
				&per_job_circuits,
	  		)?;
	  		// 2026-05-21 (Lever 1): per_job_layered/per_job_circuits are
	  		// not used after pass_all returns. Drop them now to free
	  		// per-job gadget clones BEFORE the Phase 1 snark critical
	  		// section, where all 8 jobs would otherwise hold them.
	  		drop(per_job_layered);
	  		drop(per_job_circuits);
	  		let Some((batch_prf, ind_prf)) = batch_ind_prfs.map(|x| (x.0, x.1))
	  			else {return Err(Error::Other("batch proof is none!".to_string()));};
			let mb_speed = get_speed(max_total_n, &mut gt_prove_steps);
	  		// SPEED + folding time come from gt_prove_steps (already
	  		// stopped by get_speed); gt1's tail here is meaningless, so
	  		// log() the real ms and just reset gt1 for the next step.
	  		log(job_id, log_level, &format!("PERF 1006. Job Step 1: main circuits IVC PROVE STEPS (Folding) DONE. total_word_len: {}, steps: {}. SPEED: {} MB/hour {} ms", format_bytes(max_total_n * 31), _num_steps, mb_speed, gt_prove_steps.ms()));
	  		gt1.clear_start();

	  		// b_one_proof: only ONE job runs the SNARK deciders + Phase 2
	  		// + proof assembly/verify. Which job is configurable via
	  		// ZKR_SNARK_JOB_ID (default 0); the numa driver sets it so the
	  		// snark-carrying half's chosen job proves. All jobs still do
	  		// the Phase-1 folding above; the others return here so a single
	  		// full batch+individual proof is produced cheaply. Note: the
	  		// last-finisher key-drop (keyed on n_jobs_total) will not fire
	  		// in this mode, so g16 keys stay resident until return.
	  		let snark_job_id = std::env::var("ZKR_SNARK_JOB_ID").ok()
	  			.and_then(|s| s.parse::<usize>().ok()).unwrap_or(0);
	  		if read_global_config().b_one_proof && job_id != snark_job_id {
	  			log(job_id, log_level, &format!(
	  				"Job {} folding done; b_one_proof set -> skip SNARK \
	  				 (only Job {} proves).", job_id, snark_job_id));
	  			return Ok(());
	  		}
	  	
	  		//5. generate the inputs for cyclepair
	  		let qa_pp_d1_guard = qa_pp_d1.read().unwrap();
	  		let qa_nizk_pkey = qa_pp_d1_guard.as_ref()
				.expect("qa_pp_d1 null!");
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
	  		drop(W_i1);
	  		let cyclepair_inputs = U_i1
	  			.generate_cyclepair_inputs::<E>(qa_nizk_pkey, qa_nizk_vkey,
	  				&com_all_w, &prf_qa_nizk, &poseidon_config);
	  		drop(prf_qa_nizk);
	  		drop(U_i1);
	  		drop(qa_pp_d1_guard);

	  		if read_global_config().b_folding_only {
	  			log(job_id, log_level, &format!(
	  				"Job {}: b_folding_only set, no snark generated",
	  				job_id));
	  			return Ok(());
	  		}

	  		// Past the one_proof + fold_only gates: this job emits a SNARK
	  		// proof (the selected job under one_proof, else every job).
	  		log(job_id, log_level, &format!(
	  			"Job {} generating SNARK proof", job_id));

	  		// full_clam part-2 gate: wait until the driver frees the
	  		// fold-only half's RAM (flag file appears) before the decider.
	  		if let Some(flag) = read_global_config().snark_wait_flag.clone() {
	  			while !std::path::Path::new(&flag).exists() {
	  				log(job_id, log_level, &format!(
	  					"Job {}: waiting for snark-start flag {}",
	  					job_id, flag));
	  				std::thread::sleep(
	  					std::time::Duration::from_secs(10));
	  			}
	  			log(job_id, log_level, &format!(
	  				"Job {}: snark-start flag seen; proceeding", job_id));
	  		}

	  		// ------------- The following is the CRITICAL SECTION -------
	  		guard_outer = Some({
	  			let (lock, cvar) = &*semaphore_outer;
	  			let mut count = lock_unwrap!(lock);
	  			while *count == 0 {
	  				count = cvar.wait(count).unwrap();
	  			}
	  			*count -= 1;
	  			SemaphoreGuard { lock: semaphore_outer.clone() }
	  		});
			let _guard = {
				let (lock, cvar) = &*semaphore;
				let mut count = lock_unwrap!(lock);
				while *count == 0 {
					count = cvar.wait(count).unwrap();
				}
				*count -= 1;
				SemaphoreGuard { lock: semaphore.clone() }
			};

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

	  		//DEBUG probe 69801: ZKR_DECIDER_SAT arms the per-step
	  		//decider UNSAT checkpoints for from_nova + prove synths
	  		//(keygen synth is setup-mode and self-skips).
	  		let b_probe_sat = std::env::var("ZKR_DECIDER_SAT").is_ok();
	  		if b_probe_sat {
	  			use crate::folding::foldpot::utils::set_gadget_sat;
	  			set_gadget_sat(true);
	  		}
	  		let (snark_proof_main,mainres,mainres_hash, g16_vk_main) = {
				let main_circ = MainDeciderCircuit::from_nova::<FC>(nova1,
	  				com_all_w.clone(), r_all_w.clone(), randf).unwrap();
	  			let mainres = main_circ.res.clone();
	  			let mainres_hash = main_circ.res_hash.clone();
	  			log_perf(job_id, log_level, &format!("FoldPot Step 4: build MAIN decider circuit. MEM: {} GB", get_mem_usage()), &mut gt1);
	  	
				// 2026-05-21 (Lever 3): read main_pk under RwLock so the
				// last finisher can drop it after Phase 1 snark ends.
				// VK is cloned owned before releasing the guard so
				// downstream code does not borrow from the lock.
				let main_read_guard = cached_main_keys.read().unwrap();
				let (g16_pk, g16_vk): (&S::ProvingKey, &S::VerifyingKey) =
					if let Some(keys) = main_read_guard.as_ref() {
						(&keys.0, &keys.1)
					} else {
						let (pk, vk) = S::circuit_specific_setup(
								main_circ.clone(),
								&mut rng).unwrap();
						if job_id == 0 && read_global_config()
						.b_write_snark_cache {
							let main_path = cache_base
								.join("g16_main.key");
							write_g16key::<C1::ScalarField, S>(&main_path,
								&pk, &vk, job_id);
						}
						pk_main_owned = pk;
						vk_main_owned = vk;
						(&pk_main_owned, &vk_main_owned)
					};
	  			log_perf(job_id, log_level, &format!("PERF 1006: Job Step 2: setup Groth16. MEM: {} GB.",  get_mem_usage()), &mut gt1);

	  			let snark_proof_main: S::Proof = S::prove(&g16_pk,
	  				main_circ, &mut rng)
	  				.map_err(|e| Error::Other(e.to_string())).unwrap();

	  			//DEBUG probe 69801: immediate self-verify against the
	  			//from_nova public input, before Phase 2 can blur it.
	  			if std::env::var("ZKR_MAIN_SNARK_PROBE").is_ok(){
	  				let vres = S::verify(g16_vk,
	  					&vec![mainres_hash], &snark_proof_main);
	  				println!("DEBUG USE 69801.7: main snark immediate \
verify vs from_nova hash: {:?}", vres);
	  			}
	  			if b_probe_sat {
	  				use crate::folding::foldpot::utils::set_gadget_sat;
	  				set_gadget_sat(false);
	  			}
	  			if std::env::var("ZKR_STOP_AFTER_MAIN").is_ok(){
	  				println!("DEBUG USE 69801.9: ZKR_STOP_AFTER_MAIN \
set; exit(0) before Phase 2.");
	  				std::process::exit(0);
	  			}

	  			let g16_vk_owned: S::VerifyingKey = g16_vk.clone();
	  			drop(main_read_guard);

	  			// Lever 3: last-finisher drops main_pk in place.
	  			let prev_p1 = phase1_snark_done
	  				.fetch_add(1, Ordering::SeqCst);
	  			if prev_p1 + 1 == n_jobs_total {
	  				let _ = cached_main_keys.write().unwrap().take();
	  				let _ = qa_pp_d1.write().unwrap().take();
	  			}

	  			(snark_proof_main, mainres, mainres_hash, g16_vk_owned)
	  		};

	  		//7. prepare the other data.
	  		let mut batch_ver_param = driver1.batch_vk.clone().unwrap().clone();
	  		batch_ver_param.kzg_driver1 = Some(
	  			driver1.nova_param.1.cs1e_vp.clone());
	  		let b_check_lkup = driver1.layered_circs[0][0].is_check_lkup(); 
	  		let driver1_poseidon_config = driver1.poseidon_config.clone();
			log_perf(job_id, log_level, &format!("PERF 1006: Job Step 3: Gen Groth16 Proof for MainCirc. MEM: {} GB.",  get_mem_usage()), &mut gt1);
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
		job_id,
		semaphore_batch_claim.clone(),
		&driver2.layered_circs,
		&driver2.circuits
	)?;

	let qa_pp_d2_guard = qa_pp_d2.read().unwrap();
	let qa_nizk_pkey = qa_pp_d2_guard.as_ref().expect("qa_pp_d2 null!");
	let qa_nizk_vkey = driver2.nova_param.1.qa_vp.as_ref()
		.expect("qa_vp null!").clone();
	let qa_nizk_vkey_hash = qa_nizk_vkey.hash(&driver2.poseidon_config);
	let (nova2_U_i1, nova2_W_i1, _nova2_r_Fr, _nova2__cmT)= 
		nova2.gen_next_folded().unwrap();
	let (nova2_com_all_w, nova2_prf_qa_nizk, nova2_r_all_w, nova2_prf_kzg, nova2_kzg_all_com_ch) = nova2_W_i1.gen_com_all_w_and_qa_nizk_prf::<E, CS1E, H>( &qa_nizk_pkey, &driver2.nova_param.0.cs1e_pp, &qa_nizk_vkey, &nova2_U_i1, &driver2.poseidon_config);
	drop(nova2_W_i1);
	drop(qa_pp_d2_guard);
	log_perf(job_id, log_level, &format!("PERF 1006: Job Step 4: cyclefold and cyclepair IVC PROVE STEPS (folding) DONE. num_steps: {}", _num_steps), &mut gt1);


	//8. now build up the CyclePair circuit which processes
	// the pairing equations generated by the first circuit (e.g., qa-nizk ones)
	// it uses the Phase1Ret.hash() to link with the output of
	// the MainCircuit
	let inp = CircPubInput{
			ch1: ch1,
			rc1: rc1,
			hash_cmF1: mainres.hash_cmF, //== z_n[0], zero seed
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
		// ------------- The following is the CRITICAL SECTION -------
		let _guard_cp = {
			let (lock, cvar) = &*semaphore_cp;
			let mut count = lock_unwrap!(lock);
			while *count == 0 {
				count = cvar.wait(count).unwrap();
			}
			*count -= 1;
			SemaphoreGuard { lock: semaphore_cp.clone() }
		};

		let cp_circuit = CyclePairCircuit
			::from_nova(nova2,
				cyclepair_inputs, qa_nizk_vkey_hash.clone(),
				driver2.poseidon_config.clone(),
				com_all_w, r_all_w, nova2_com_all_w, nova2_r_all_w, mainres,
				inp).unwrap();
		log_perf(job_id, log_level, &format!("PERF 1006: Job Step 5: build CyclePair circuit. MEM: {} GB", get_mem_usage()), &mut gt1);



		// 2026-05-21 (Lever 2B): lazy-load cp_key the first time any
		// job reaches Phase 2 snark. Double-checked under the write
		// lock so only one job pays the disk + deserialize cost; all
		// others see Some after the first finisher's write.
		{
			let already = cached_cp_keys.read().unwrap().is_some();
			if !already && read_global_config().b_read_snark_cache {
				let mut w = cached_cp_keys.write().unwrap();
				if w.is_none() {
					let cp_path = cache_base.join("g16_cp.key");
					if let Ok(keys) =
						read_g16key::<C1::ScalarField, S>(&cp_path, 0) {
						*w = Some(keys);
					}
				}
			}
		}

		//9. set up the keys (maybe later can be cached)
		let cp_read_guard = cached_cp_keys.read().unwrap();
		let (g16_pk, g16_vk): (&S::ProvingKey, &S::VerifyingKey) =
			if let Some(keys) = cp_read_guard.as_ref() {
				(&keys.0, &keys.1)
			} else {
				let (pk, vk) = S::circuit_specific_setup(
						cp_circuit.clone(),
						&mut rng).unwrap();
				if job_id == 0 && read_global_config().b_write_snark_cache {
						let cp_path = cache_base.join("g16_cp.key");
						write_g16key::<C1::ScalarField, S>(
							&cp_path, &pk, &vk, job_id);
				}
				pk_cp_owned = pk;
				vk_cp_owned = vk;
				(&pk_cp_owned, &vk_cp_owned)
			};
		log_perf(job_id, log_level, &format!("PERF 1006: Job Step 6: setup Groth16 for CpCircuit. MEM: {} GB.",  get_mem_usage()), &mut gt1);

		//10. produce the groth16 snark
		let snark_proof_cp: S::Proof = S::prove(&g16_pk, cp_circuit, &mut rng)
			.map_err(|e| Error::Other(e.to_string())).unwrap();
		log_perf(job_id, log_level, &format!("PERF 1006: Job Step 7: Generate Groth16 proof. MEM: {} GB.",  get_mem_usage()), &mut gt1);

		let g16_vk_cp_owned: S::VerifyingKey = g16_vk.clone();
		drop(cp_read_guard);

		// Lever 2 finisher: last job drops cp_pk in place.
		let prev_p2 = phase2_snark_done
			.fetch_add(1, Ordering::SeqCst);
		if prev_p2 + 1 == n_jobs_total {
			let _ = cached_cp_keys.write().unwrap().take();
			let _ = qa_pp_d2.write().unwrap().take();
		}

		(snark_proof_cp, g16_vk_cp_owned)
	};
	drop(guard_outer);

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
	// Do NOT assert: a failed self-verification must not abort the whole
	// run -- the other jobs are very expensive and we still want their
	// timings. Log an ERROR and let this job finish normally.
	let ok_batch = BatchProcessor::<E,LK,S,CS1E,H>::verify_batch(
		&batch_ver_param,
		Some(qa_nizk_vkey_hash1),
		Some(qa_nizk_vkey2.clone()), //needs to be from nova qa_nizk
		Some(g16_vk_main.clone()),
		Some(g16_vk_cp.clone()),
		&batch_claim,
		&batch_prf,
		&driver1_poseidon_config,
		true, //now full verification
		opt_kzg_sum1,
		Some(job_id), //route each sub-check FAIL to this job's log
		"final", //distinguish from the prover's own self-check
	);
	if !ok_batch {
		//count it as well as log it: the no-abort policy above means a
		//failure is otherwise invisible to cargo, which still says `ok`.
		utils::consts::record_verify_fail();
		log(job_id, ERR, &format!(
			"Job {} BATCH PROOF VERIFICATION FAILED (verify_batch \
			returned false); continuing other jobs.", job_id));
	}
	log_perf(job_id, log_level, &format!("FoldPot Step 12: Verify Batch Proof."),
		&mut gt1);

	//12. verify the individual proof
	// Same policy as the batch proof: log an ERROR on failure, never abort
	// the run (the other jobs are very expensive).
	let ok_ind = BatchProcessor::<E,LK,S,CS1E,H>::verify_individual(
		//&driver1.batch_vk.as_ref().unwrap(),
		&batch_ver_param,
		idx_individual_prf,
		&ind_claim,
		&batch_prf,
		&ind_prf,
		Some(job_id),
		"final");
	if !ok_ind {
		//see the ok_batch site: counted so a test can fail on it.
		utils::consts::record_verify_fail();
		log(job_id, ERR, &format!(
			"Job {} INDIVIDUAL PROOF VERIFICATION FAILED \
			(verify_individual returned false); continuing other jobs.",
			job_id));
	}
	log_perf(job_id, log_level, &format!("FOLDPOT Step 13. Verify Individual Proof."),
		&mut gt1);
	// Report the proof structure + byte sizes once (this job holds a
	// complete batch+individual proof; under b_one_proof only Job 0
	// reaches here).
	batch_prf.print_size();
	ind_prf.print_size();
	log_perf(job_id, log_level, &format!("**** Job {} Complete ***** MEM: {} GB.", job_id, get_mem_usage()), &mut gt1_0);

	Ok(())
	})();
	if let Err(e) = res {
		log(job_id, ERR, &format!("Job {} FAILED with error: {:?}", job_id, e));
		let _ = std::io::stdout().flush();
		if read_global_config().b_scale_catch_caperr {
			// scale mode: stash + return; surfaced after the for_each.
			*scale_job_err.lock().unwrap() = Some(e);
			return;
		}
		std::process::exit(1);  // default: unchanged
	}
	});

	// scale mode: surface a stashed job CapErr as a normal Err -> the caller's
	// .expect("main err") panics on the main thread, which the scale bump-retry
	// catches. No-op on the default path (nothing stashed).
	if let Some(e) = scale_job_err.into_inner().unwrap() {
		return Err(e);
	}

	log_perf(0, log_level, "PERF 1005: FoldPot Step 4: parallel jobs of folding + nark generation", &mut gt_all);
	log_perf(0, log_level, "PERF 1005: === ALL JOBS ===", &mut gt_all_0);
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
		fn set_job_id(&mut self, _job_id: usize){}
		fn get_job_id(&self)->usize{0}
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
			_word_id: FpVar<F>, _subsig_id: FpVar<F>,
			_virt_vals: &mut Vec<FpVar<F>>)
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
	pub struct SumMapper<F:PrimeField, LK:LookupTableTwoCol<F>>{
		pub _f: PhantomData<F>,
		pub _lk: PhantomData<LK>,
		pub b_odd: bool,
		pub job_id: usize,
	}

	impl <F:PrimeField, LK:LookupTableTwoCol<F>> SumMapper<F,LK>{
		pub fn new(b_odd: bool)->Self{
			Self{_f: PhantomData, _lk: PhantomData, b_odd: b_odd, job_id: 0 }
		}


		pub fn can_handle(&self, w0: F)->bool{
			let w0_val = field_to_usize(&w0);
			let b_odd_w = w0_val%2==1;
			b_odd_w == self.b_odd
		}
	}

	// Test-only mapper: no internal `Arc<Mutex<>>` state to split
	// across jobs, so shallow clone via derived Clone is fine.
	impl <F:PrimeField, LK:LookupTableTwoCol<F>>
		crate::folding::foldpot::sigma_ir1cs::GadgetMapperDeepClone
		for SumMapper<F, LK>
	{
		fn clone_deep_mapper(&self) -> Self { self.clone() }
	}


	impl <F:PrimeField, LK: LookupTableTwoCol<F>> 
	GadgetMapper<F,LK> for SumMapper<F, LK>{
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

			//3. check if the word is in table
			let mut subtbl_id = vec![];
			let (zero, two) = (F::zero(), F::from(2u32));
			for i in 0..n{
				let res = lkup.find(two, word[i]);
				let sid = if res.is_ok() {two} else {zero};
				subtbl_id.push(sid);
			}

			//4. retrieve the previous sum
			let prev_sum = prev_wit.as_ref().map_or(zero, |stmt|{
				let prev_sum =stmt.oup_buf[0];
				prev_sum
			});

			//5. compute the new sum
			let mut new_sum = prev_sum.clone();
			for i in 0..n{ new_sum+=if subtbl_id[i]==two {word[i]}else{zero}; }

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
		let mut jobs = vec![FoldPotJob{
			vec_words,
			vec_word_info,
			vec_word_fnames,
			idx_individual_prf: sample_individual_prf,
		}];
		let _prf = foldpot_main::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,SigmaIR1CS_Inst<Fr,C1,CS1,LK,SumMapper<Fr,LK>,H>,S,LK,SumMapper<Fr,LK>, false>(lkup, vec_circ, &mut jobs, "cache");
	}

}






