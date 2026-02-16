/* Created 09/15/2024. Adaptation for super_nova 
   Changed 01/09/2025. Add TwoPhaseDeciderCircuit to accomodate to
   	the two phase cyclepair strategy.
*/

/// This file implements the onchain (Ethereum's EVM) decider circuit. 
/// For non-ethereum use cases,
/// other more efficient approaches can be used.
use utils::{logger::{log_perf, LOG2, LOG3}, timer::Timer as GTimer};
use std::fmt::{Debug};
use itertools::Itertools;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group, pairing::Pairing, short_weierstrass::SWCurveConfig};
use ark_ff::{PrimeField, Field, ToConstraintField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar,FieldVar},
    prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	//prelude::*,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{Zero};
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::foldpot::from_field::{AffineFromField};
use crate::folding::{
	foldpot::{
		CommittedInstanceFoldPot, WitnessFoldPot, 
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,ZiPartTwoInstVar,GadgetMapper},
		circuits::{CommittedInstanceVarFoldPot},
		//decider_eth_circuit::{RelaxedR1CSGadget, R1CSVar,WitnessVarFoldPot,CycleFoldWitnessVar},
		mod_super::{WitnessFoldPotSuper,CommittedInstanceFoldPotSuper, FoldPotSuper},
		circuits_super::{field_to_usize,CommittedInstanceVarFoldPotSuper},
		sigma_cyclepair::{compute_hc_var, hash_var},
		utils::{get_mem_usage,f1_limbs_to_f2, B_DEBUG},
	},
};
use crate::arith::r1cs::R1CS;
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::{
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,CF3,
};
use crate::folding::{
	nova::{CommittedInstance, Witness},
};
use crate::frontend::FCircuit;
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::{
    gadgets::{MatrixGadget, SparseMatrixVar, VectorGadget},
};
use crate::Error;

#[derive(Debug, Clone)]
pub struct RelaxedR1CSGadget {}
impl RelaxedR1CSGadget {
    /// performs the RelaxedR1CS check for native variables (Az∘Bz==uCz+E)
    pub fn check_native<F: PrimeField>(
        r1cs: R1CSVar<F, F, FpVar<F>>,
        E: Vec<FpVar<F>>,
        u: FpVar<F>,
        z: Vec<FpVar<F>>,
    ) -> Result<(), SynthesisError> {
        let Az = r1cs.A.mul_vector(&z)?;
        let Bz = r1cs.B.mul_vector(&z)?;
        let Cz = r1cs.C.mul_vector(&z)?;
        let uCzE = Cz.mul_scalar(&u)?.add(&E)?;
        let AzBz = Az.hadamard(&Bz)?;
        AzBz.enforce_equal(&uCzE)?;
        Ok(())
    }

    /// performs the RelaxedR1CS check for non-native variables (Az∘Bz==uCz+E)
    pub fn check_nonnative<F: PrimeField, CF: PrimeField>(
        r1cs: R1CSVar<F, CF, NonNativeUintVar<CF>>,
        E: Vec<NonNativeUintVar<CF>>,
        u: NonNativeUintVar<CF>,
        z: Vec<NonNativeUintVar<CF>>,
    ) -> Result<(), SynthesisError> {
        // First we do addition and multiplication without mod F's order
        let Az = r1cs.A.mul_vector(&z)?;
        let Bz = r1cs.B.mul_vector(&z)?;
        let Cz = r1cs.C.mul_vector(&z)?;
        let uCzE = Cz.mul_scalar(&u)?.add(&E)?;
        let AzBz = Az.hadamard(&Bz)?;

        // Then we compare the results by checking if they are congruent
        // modulo the field order
        AzBz.into_iter()
            .zip(uCzE)
            .try_for_each(|(a, b)| a.enforce_congruent::<F>(&b))
    }
}

#[derive(Debug, Clone)]
pub struct R1CSVar<F: PrimeField, CF: PrimeField, FV: AllocVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub A: SparseMatrixVar<F, CF, FV>,
    pub B: SparseMatrixVar<F, CF, FV>,
    pub C: SparseMatrixVar<F, CF, FV>,
}

impl<F, CF, FV> AllocVar<R1CS<F>, CF> for R1CSVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: AllocVar<F, CF>,
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let A = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().A)?;
            let B = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().B)?;
            let C = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().C)?;

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                A,
                B,
                C,
            })
        })
    }
}

/// In-circuit representation of the Witness associated 
/// to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVarFoldPot<C: CurveGroup> {
    pub E: Vec<FpVar<C::ScalarField>>,
    pub rE: FpVar<C::ScalarField>,
    pub W: Vec<FpVar<C::ScalarField>>,
    pub rW: FpVar<C::ScalarField>,
	pub size_F: usize, //size of fixed mem segment
	pub rF: FpVar<C::ScalarField>, //used for computing cmF
}

impl<C> AllocVar<WitnessFoldPot<C>, CF1<C>> for WitnessVarFoldPot<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<WitnessFoldPot<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;
            let rF =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rF), mode)?;
			let size_F = val.borrow().size_F;

            Ok(Self {E, rE, W, rW, size_F, rF})
        })
    }
}

/// In-circuit representation of the Witness associated 
/// to the CommittedInstance, but with
/// non-native representation, since it is used to 
/// represent the CycleFold witness.  No need to make change
/// as cyclefold witness is for standard R1CS
#[derive(Debug, Clone)]
pub struct CycleFoldWitnessVar<C: CurveGroup> 
where CF2<C>: PrimeField
{
    pub E: Vec<NonNativeUintVar<CF2<C>>>,
    pub rE: NonNativeUintVar<CF2<C>>,
    pub W: Vec<NonNativeUintVar<CF2<C>>>,
    pub rW: NonNativeUintVar<CF2<C>>,
}

impl<C> AllocVar<Witness<C>, CF2<C>> for CycleFoldWitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E = Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W = Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

/// In-circuit representation of the Witness associated 
/// to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVarFoldPotSuper<C: CurveGroup> {
	pub vec_wit: Vec<WitnessVarFoldPot<C>>,
}

impl<C> AllocVar<WitnessFoldPotSuper<C>, CF1<C>> for WitnessVarFoldPotSuper<C>
where 
	C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<WitnessFoldPotSuper<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();
			let mut vec_wit = vec![];
			for wit in &val.borrow().vec_wit{
				let witvar = WitnessVarFoldPot::new_variable(cs.clone(), || Ok(wit),mode)?;
				vec_wit.push(witvar);
			}

            Ok(Self {vec_wit})
        })
    }
}

/// Packs the wires returned by Phase1Circuit (most info
/// retrieved from the ZiPartTwo of the last running instance),
/// the vec_coms retrieved from U_i1's all instances.
/// NOTE that the ret (even though) has a lot of data members,
/// does not increase the total number of constraints
#[derive(Clone, Debug)]
pub struct Phase1CircuitRet<F:PrimeField, C: CurveGroup<ScalarField=F>>
where C::BaseField: PrimeField
{
	/// the ch (challenge)
	pub ch: FpVar<F>,
	/// the rc (combination)
	pub rc: FpVar<F>,
	/// kzg_sum: sum_kzg_eval_lk + sum_kzg_eval_word + sum_kzg_eval_others
	pub kzg_sum: FpVar<F>,
	/// rows of [com_all_w, (comW, comE, comF)] for all vec_inst of U_{i+1}
	pub vec_coms: Vec<NonNativeAffineVar<C>>,
	/// the final result of the last zi_part2_inst
	pub final_result: FpVar<F>,
	/// the u_i instance (last)
	pub u_i: CommittedInstanceVarFoldPot<C>,

	/// the challene used for evaluating all_W, all_E of circuit 1
	/// NOTE that this kzg is for the decider circuit, as 
	/// W and E are NOT available after the Fiat-Shamir randoms are put in
	/// So it's different from the kzg_sum in the above section for
	/// fixed memory.
	pub kzg_all_com_ch: FpVar<F>,
	/// the evaluation result of com_all_w_e
	pub eval_w_e: FpVar<F>,

	/// the cmE of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmE: NonNativeAffineVar<C>,
	/// the cmW of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmW: NonNativeAffineVar<C>,
	/// the cmF of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmF: NonNativeAffineVar<C>,
}

impl <F:PrimeField, C: CurveGroup<ScalarField=F>> Phase1CircuitRet<F,C>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig
{
	pub fn dummy(cs: ConstraintSystemRef<F>)->Self{
		let zvar = FpVar::<F>::new_witness(cs.clone(), 
			|| Ok(F::zero())).expect("create fpvar error");
		let avar = NonNativeAffineVar::<C>::zero_var(cs.clone());
		let ci = CommittedInstanceFoldPot::<C>::dummy(2);
		Self{
			ch: zvar.clone(),
			rc: zvar.clone(),
			kzg_sum: zvar.clone(),
			vec_coms: vec![avar.clone(); 7],
			final_result: zvar.clone(),
			u_i: CommittedInstanceVarFoldPot::<C>::new_witness(cs.clone(), ||
				Ok(ci)).expect("commited instane var error"),
			kzg_all_com_ch: zvar.clone(),
			eval_w_e: zvar.clone(),

			u_i1_0_cmE: avar.clone(),
			u_i1_0_cmW: avar.clone(),
			u_i1_0_cmF: avar.clone(),
		}
	}
}

/// Packs the wires returned by Phase2Circuit 
pub struct Phase2CircuitRet<F:PrimeField, C: CurveGroup<ScalarField=F>>
where C::BaseField: PrimeField{
	pub hashchain_b: FpVar<F>,
	pub main_ret: Phase1CircuitRet<F, C>,
}

impl <F:PrimeField, C: CurveGroup<ScalarField=F>> Phase2CircuitRet<F,C>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig
{
	pub fn dummy(cs: ConstraintSystemRef<F>)->Self{
		let zvar = FpVar::<F>::new_witness(cs.clone(), 
			|| Ok(F::zero())).expect("create fpvar error");
		Self{
			hashchain_b: zvar,
			main_ret: Phase1CircuitRet::<F,C>::dummy(cs.clone())
		}
	}
}


/// Circuit that implements the in-circuit checks 
/// for the Phase 1 (mainly check consistency with com_all kzg's evaluation).
/// It basically proves this:
/// There exists: [z_i, n, z_n, (U_i, W_i), (u_i, w_i), com_all_W, 
///                    kzg_eval, kzg_ch]
/// (1) (U_i, W_i), (u_i, w_i) is the valid IVC proof for the given
///          circuits (that enforce the regex check logic)
/// (2) kzg_ch is a fiat-shamir of (com_all_W and U_{i+1})
/// (3) All witness W_i || E_i of W_{i+1} evaluates the kzg_eval (
///          which later outside of the circuit confirms with com_all_W).
///     And they satisfies all the R1CS's for each circuit.
///     Later the qa_nizk proof proved by the Phase2 circuit proves that
///     they commits to U_{i+1}.
/// (4) the kzg_eval_sum for the word problem (sum of kzg_lk + kzg_word + kzg_others)
/// As this is a "sub-circuit", it does NOT have public I/O, instead,
/// It returns to the caller a Return Package of Wires (for consistency check)
/// [kzg_eval, kzg_ch, {com_E, com_W, com_F}_i^n, kzg_eval, kzg_eval_sum]
#[derive(Clone, Debug)]
pub struct Phase1Circuit<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + 
Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	LK: LookupTableTwoCol<C1::ScalarField>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
	_gm: PhantomData<GM>,
	_e: PhantomData<E>,
	_p: PhantomData<P>,
	_c2g2: PhantomData<C2G2>,
	_lk: PhantomData<LK>,
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _cs1e: PhantomData<CS1E>,

    /// E vector's length of the Nova instance witness (for each circuit)
    pub E_len: Vec<usize>,
    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// E vector's length of the CyclePair instance witness
    pub cp_E_len: usize,
    /// R1CS of the Augmented Function circuit (each)
    pub r1cs: Vec<R1CS<C1::ScalarField>>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
	/// R1CS of the CyclePair circuit
	pub cp_r1cs: R1CS<C2::ScalarField>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
    pub cp_pedersen_params: PedersenParams<C2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    /// public params hash
    pub pp_hash: Option<C1::ScalarField>,

    pub i: Option<CF1<C1>>,
    /// initial state
    pub z_0: Option<Vec<C1::ScalarField>>,
    /// current i-th state
    pub z_i: Option<Vec<C1::ScalarField>>,
    /// Nova instances
    pub u_i: Option<CommittedInstanceFoldPot<C1>>, //changed to FoldPot 
    pub w_i: Option<WitnessFoldPot<C1>>,
    pub U_i: Option<CommittedInstanceFoldPotSuper<C1>>,
    pub W_i: Option<WitnessFoldPotSuper<C1>>,
    pub U_i1: Option<CommittedInstanceFoldPotSuper<C1>>,
    pub W_i1: Option<WitnessFoldPotSuper<C1>>,
    pub cmT: Option<C1>,
    pub r: Option<C1::ScalarField>,

    /// CycleFold running instance
    pub cf_U_i: Option<CommittedInstance<C2>>, //no need of cmF (standard)
    pub cf_W_i: Option<Witness<C2>>,

	/// CyclePair running instance
    pub cp_U_i: Option<CommittedInstance<C2>>, //no need of cmF (standard)
    pub cp_W_i: Option<Witness<C2>>,

    /// used for computing KZG challenges (advice) - will be checked
	pub com_all_w: Option<C1>,
	/// the r_all_w used in generating com_all_w
	pub r_all_w: Option<C1::ScalarField>,

	// Added for super nova
	/// the number of circuits
	pub n_circ: C1::ScalarField, 
	/// the initial pc
	pub pc_0: C1::ScalarField,
	/// the current pc (must be less than the number of circuits)
	pub pc_i: C1::ScalarField,
	/// the circuit ID to perform the next step computation
	pub pc_i1: C1::ScalarField,

	pub zi_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>,

	pub b_full_mode: bool,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool> Phase1Circuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, H>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>, //should be kzg
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
	CF2<C1>: PrimeField,
	CF2<C2>: PrimeField,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. (noe: com_all_w is used
	/// to compute kzg_all_com_ch in circuit)
    pub fn from_nova<FC: FCircuit<C1::ScalarField> 
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM, C=C1>> 
		(nova: FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E,LK, GM, H>, 
		 com_all_w: C1,
		 r_all_w: C1::ScalarField) -> Result<Self, Error> {
        //1. compute the U_{i+1}, W_{i+1}
		let (U_i1, W_i1, r_Fr, cmT)= nova.gen_next_folded()?;

        Ok(Self {
			_gm: PhantomData,
			_e: PhantomData,
			_p: PhantomData,
			_c2g2: PhantomData,
			_lk: PhantomData,
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cs1: PhantomData,
            _cs1e: PhantomData,
            _cs2: PhantomData,

            E_len: nova.W_i.vec_wit.iter().map(|w| w.E.len())
				.collect::<Vec<usize>>(),
            cf_E_len: nova.cf_W_i.E.len(),
            cp_E_len: nova.cp_W_i.as_ref().map_or(0, |x| x.E.len()),
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cp_r1cs: nova.cp_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
            cp_pedersen_params: nova.cp_cs_pp,
            poseidon_config: nova.poseidon_config,
            pp_hash: Some(nova.pp_hash),
            i: Some(nova.i),
            z_0: Some(nova.z_0),
            z_i: Some(nova.z_i),
            u_i: Some(nova.u_i),
            w_i: Some(nova.w_i),
            U_i: Some(nova.U_i),
            W_i: Some(nova.W_i),
            U_i1: Some(U_i1),
            W_i1: Some(W_i1),
            cmT: Some(cmT),
            r: Some(r_Fr),
            cf_U_i: Some(nova.cf_U_i),
            cf_W_i: Some(nova.cf_W_i),

			cp_U_i: nova.cp_U_i,
			cp_W_i: nova.cp_W_i,

			n_circ: nova.n_circ,
			pc_0: nova.pc_0,
			pc_i: nova.pc_i,
			pc_i1: nova.pc_i1,

			zi_part2_inst: Some(nova.zi_part2_inst.clone()),

			com_all_w: Some(com_all_w),
			r_all_w: Some(r_all_w),

			b_full_mode: nova.b_full_mode,

        })
    }

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return the final_result = hash_a_b
    pub fn generate_constraints_adv(self, _dump_level: usize, cs: ConstraintSystemRef<CF1<C1>>) -> Result<Phase1CircuitRet<CF1<C1>,C1>, Error> {
		//1. generate Vector the R1CS var (one for each circuit)
		let log_level = LOG3;
		let b_debug = B_DEBUG;
		let mut t1 = GTimer::new();
		let c0 = cs.num_constraints();
		let mut c1 = cs.num_constraints();
		let _pc_i_val = field_to_usize(&self.pc_i); //for fold
		let _pc_i1_val = field_to_usize(&self.pc_i1); //for compute next (j)
		let pc_i_var = FpVar::new_witness(cs.clone(),  || Ok(self.pc_i))?;
        let vec_r1cs = self.r1cs.iter().map(|r1cs|
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>
			::new_witness(cs.clone(), || {
                Ok(r1cs.clone())
            }).unwrap()).collect::<Vec<
				R1CSVar::<C1::ScalarField,CF1<C1>,FpVar<CF1<C1>>>
			>>();
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 1: generae r1cs_var. INCREASSED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//2. generate Var version of pp_hash, z_0, z_i
		// U_i, u_i, U_i1, given the advice from nova instance
		// NOTE: they are private witness (some vars will be
		// returned to TwoPhaseCircuit for verification)
        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || 
			Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
		let _x_len = if self.b_full_mode {3} else {2};
        let u_dummy_native = CommittedInstanceFoldPot::<C1>::dummy(2);
        let u_i = CommittedInstanceVarFoldPot::<C1>::new_witness(cs.clone(), 
			|| { Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(cs.clone(), || { Ok(self.U_i.unwrap()) })?;
        let U_i1 = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(
			cs.clone(), || { Ok(self.U_i1.unwrap())
        })?;
        let W_i1 = WitnessVarFoldPotSuper::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i1.unwrap())
        })?;
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 2: igen Ui, Wi, Ui1, Wi1 witness: INCREASED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//3. compute the KZG challenge in circuit
		let com_all_w = NonNativeAffineVar::<C1>::new_witness(cs.clone(),
			|| Ok(self.com_all_w.expect("com_all null")))?;
		let com_all_w_clone = com_all_w.clone();
        let kzg_all_com_ch =
            KZGChallengesGadgetSuper::<C1>::get_challenge_gadget(cs.clone(),
				&self.poseidon_config, U_i1.clone(), com_all_w)?;
		let kzg_all_com_ch_clone= kzg_all_com_ch.clone();
		let r_all_w = FpVar::<C1::ScalarField>::new_witness(cs.clone(),
			|| Ok(self.r_all_w.expect("r_all_w null")))?;

		let mut all_w = W_i1.vec_wit.iter().map(|it| it.W.clone()
		).flatten().collect::<Vec<FpVar<C1::ScalarField>>>();
		let mut all_e = W_i1.vec_wit.iter().map(|it| it.E.clone()
		).flatten().collect::<Vec<FpVar<C1::ScalarField>>>();
		all_w.append(&mut all_e);
		all_w.push(r_all_w);
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 3: collect all_w_e. len: {}, : INCREASED: {} constraints.", 
			all_w.len(), cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		let one= FpVar::<C1::ScalarField>::new_witness(cs.clone(),  || 
			Ok(C1::ScalarField::from(1u32)) ).unwrap();
        let eval_w_e= evaluate_gadget::<CF1<C1>>(all_w, kzg_all_com_ch, one)?;
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 4: eval all_w_e. INCREASED {} constrains.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

        //4. u_i.cmE==cm(0), u_i.u==1
        // Here zero is the x & y coordinates of the 
		// zero point affine representation.
        let zero = NonNativeUintVar::new_constant(cs.clone(), 
			C1::BaseField::zero())?;
        u_i.cmE.x.enforce_equal_unaligned(&zero)?;
        u_i.cmE.y.enforce_equal_unaligned(&zero)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;


        //5. a u_i.x[0] == H(i, z_0, z_i, pc_i, U_i)
		// similar to mod_super.rs #6. but here i is already its (i+1)
        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut _transcript = sponge.clone();
        let (u_i_x, _U_i_vec) = U_i.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone(),
			pc_i_var.clone(),
            z_0.clone(),
            z_i.clone(),
        )?;
		let n_circ = field_to_usize(&self.n_circ);
        let u_dummy = if self.b_full_mode {//x has 3 elements for full version
         	CommittedInstanceFoldPotSuper::<C1>::dummy(3, 
				n_circ, self.b_full_mode)
        }else{
         	CommittedInstanceFoldPotSuper::<C1>::dummy(2, 
				n_circ, self.b_full_mode)
        };
        let (u_i1_x_base, _) = CommittedInstanceVarFoldPotSuper::
                new_constant(cs.clone(), u_dummy)?.hash(
            &sponge,
            pp_hash.clone(),
            i.clone(),
            pc_i_var.clone(),
            z_0.clone(),
            z_i.clone(),
        )?;
        let one_var = FpVar::<CF1<C1>>::new_constant(cs.clone(),
            C1::ScalarField::from(1u32))?;
        let i_minus_one = &i - &one_var;
		// REASON: when i (from nova) is 1, we are talking about verifying
		// u_1.x = hash(U_1, ...) where U_1 is really from the dummy case.
        let is_basecase = i_minus_one.is_zero()?;
        (u_i.x[0]).enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i_x)?)?;
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 5: Enforce u_i standard and hash. INCREASED r1cs: {}.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//6. Added check z_i is well-formed (and in-particular) its
		//r matches kzg_c_lkup, and its sum_lk_col1, sum_lk_col2 matches
		//the value of eval_lkup_col1, eval_lkup_col2 retrieved from
		//the public input
		let zi_part2_inst_var = ZiPartTwoInstVar::from::<C1>(
			&self.zi_part2_inst.expect("zi_part null"), cs.clone());
		let zi_p2 = zi_part2_inst_var.hash(&self.poseidon_config, cs.clone());
		#[cfg(test)]{
			use ark_r1cs_std::R1CSVar;
			if zi_p2.value().is_ok(){//incase circ setup no value
			assert!(zi_p2.value().unwrap()==z_i[1].value().unwrap());
		}}
		zi_p2.enforce_equal(&z_i[1])?;
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 6: verify zi_part2. INCREASED r1cs: {}, memory usage: {}.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
		c1 = cs.num_constraints();


        //7. check RelaxedR1CS of U_{i+1} for each circuit
		let n_circ = field_to_usize(&self.n_circ);
		for i in 0..n_circ{
        	let z_U1: Vec<FpVar<CF1<C1>>> =
            [vec![U_i1.vec_inst[i].u.clone()],
				U_i1.vec_inst[i].x.to_vec(), 
				W_i1.vec_wit[i].W.to_vec()].concat();
        	RelaxedR1CSGadget::check_native((&vec_r1cs)[i].clone(), 
				W_i1.vec_wit[i].E.clone(), 
				U_i1.vec_inst[i].u.clone(), 
				z_U1)?;
		}
		log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 7: check {} circs. INCREASED r1cs: {}", self.n_circ, cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ assert!(csat.unwrap(), "step 7 decidercirc1"); }
		}

        //#[cfg(feature = "light-test")]
        //println!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        //#[cfg(not(feature = "light-test"))]
		let b_light_test = false;
		if !b_light_test
        {
            use super::FOLDPOT_CF_N_POINTS;
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::circuits::{
				cyclefold::{cf_io_len, CycleFoldCommittedInstanceVar}
			};
			use crate::folding::foldpot::{
				circuits::{ChallengeGadgetFoldPot, NIFSGadgetFoldPot},
			};
            use ark_r1cs_std::ToBitsGadget;

			// 8. compute NIFS.V and KZG challenges.
			// NOTE: unlike sonobe which performs the folding of 3 commitments
			// outside of circuit. We treat running and incoming instances
			// as secret witness, so we DO HAVE TO fold 3 commitments in
			// the decider circuit (COSTLY! 1.6M each x 3 = 5M)
			let cmT = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
			let r_bits = ChallengeGadgetFoldPot::<C1>::get_challenge_gadget(
				&mut _transcript,
				pp_hash.clone(),
				_U_i_vec,
				u_i.clone(),
				cmT.clone(),
			)?;
			let r_Fr = Boolean::le_bits_to_fp_var(&r_bits)?;
			let mut Ui_pci = U_i.vec_inst[0].clone(); 
			let mut expected_Ui1_pci = U_i1.vec_inst[0].clone();
			for i in 0..n_circ{//this generate FIXED constraints
				let var_i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || Ok(
					C1::ScalarField::from(i as u32)))?;
				let b_sel = var_i.is_eq(&pc_i_var)?;
				Ui_pci = b_sel.select(&U_i.vec_inst[i], &Ui_pci)?;
				expected_Ui1_pci = b_sel.select(&U_i1.vec_inst[i], &expected_Ui1_pci)?;
			}
			// the expensive one: 6MB R1CS
			let Ui1_pci = NIFSGadgetFoldPot::<C1>
				::fold_committed_instance_full(
				r_Fr, 
				Ui_pci,
				u_i.clone(), 
				cmT
			)?;
			Ui1_pci.enforce_equal(&expected_Ui1_pci)?;
			log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 8: Verify U_i1 is folded U_i and u_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			//8. Verify cyclefold instance
			//(1) u_i.x[1] = cf_U_i.hash()
			//(2) cf_W_i satisfies the cyclefold R1CS
			//(3) cf_U_i is the commitment of cf_W_i
            let cf_u_dummy_native = CommittedInstance::<C2>
				::dummy(cf_io_len(FOLDPOT_CF_N_POINTS));
            let w_dummy_native =
                Witness::<C2>::dummy(self.cf_r1cs.A.n_cols 
					- 1 - self.cf_r1cs.l, self.cf_E_len);
            let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>
			::new_witness(cs.clone(), || {
                Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.unwrap_or(w_dummy_native.clone()))
            })?;
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            //9. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H2 = GC2::new_constant(cs.clone(), 
				self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), 
				self.cf_pedersen_params.generators)?;
            let cf_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cf_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
            let cf_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cf_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();
            let computed_cmE = PedersenGadget::<C2, GC2>::commit(
                H2.clone(),
                G.clone(),
                cf_W_i_E_bits?,
                cf_W_i.rE.to_bits_le()?,
            )?;
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
            let computed_cmW =
                PedersenGadget::<C2, GC2>::commit(H2, G, cf_W_i_W_bits?, cf_W_i.rW.to_bits_le()?)?;
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;
			log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 9: check cf_W_i commits to cf_U_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			//10. check cyclefold witness satisfy its r1cs
            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness( cs.clone(), || Ok(self.cf_r1cs.clone()),)?;
            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), 
				cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs, 
				cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;
			log_perf(log_level, &format!("Phase1 Circ gen_cs: Step 10: check cf_W_i satisfies cyclefold instance. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
        }

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ assert!(csat.unwrap(), "step 10 decidercirc1"); }
		}

		let mut vec_coms_part2 = U_i1.vec_inst.iter().map(|inst|
			vec![inst.cmW.clone(), inst.cmE.clone(), inst.cmF.clone()]
		).flatten().collect::<Vec<NonNativeAffineVar<C1>>>();
		let mut vec_coms = vec![com_all_w_clone];
		vec_coms.append(&mut vec_coms_part2);
		let res = Phase1CircuitRet::<C1::ScalarField, C1>{
			ch: zi_part2_inst_var.ch,
			rc: zi_part2_inst_var.rc,
			kzg_sum: zi_part2_inst_var.sum_kzg_eval_lk + 
					zi_part2_inst_var.sum_kzg_eval_word + 
					zi_part2_inst_var.sum_kzg_eval_others,
			vec_coms: vec_coms,
			final_result: zi_part2_inst_var.f_result,
			u_i: u_i,

			kzg_all_com_ch: kzg_all_com_ch_clone,
			eval_w_e: eval_w_e,

			u_i1_0_cmE: U_i1.vec_inst[0].cmE.clone(),
			u_i1_0_cmW: U_i1.vec_inst[0].cmW.clone(),
			u_i1_0_cmF: U_i1.vec_inst[0].cmF.clone(),
		};

		let _last_c1 = c1; //just to disable the warning on c1.
		log_perf(log_level, &format!("Phase1 Circ gen_cs: COMPLETED. TOTAL r1cs: {}, RAM: {} GB.", cs.num_constraints()-c0, get_mem_usage()), &mut t1);
		Ok( res )
	}
}

/// Phase 2 Circuit that implements the in-circuit checks 
/// It basically proves the same as Phase1 circuit (using its main_circ),
/// and some additional features:
/// There exists: [z_i, n, z_n, (U_i, W_i), (u_i, w_i), 
///          com_all_W,  {(com_W, com_E, com_F)}_i=1^k, prf_qa_nizk ]
/// (1) there exists (U_i, W_i), (u_i, w_i) that folds to (U_i1)
///  where (unlike Phase1. U_i1.{cmE, cmW, cmF} are DISCLOSED (by TwoPhaseCirc)
///  as public, such that via an external QA-NIZK proof, which proves
///  that com_all_W matches the cmE, cmW, cmF and its kzg evaluation
///  matches the internal calculation of all witness and error terms.
///  (this is because we don't have a 3rd circuit which checks the
///   qa-nizk proof, and we have to use the 'original' Sonobe approach
///   which checks kzg proof outside, but we improved it using qa-nizk
///   using just one kzg proof now).
///   
/// ---------------------------------------------------------
///  In additio, it proves the following.
/// (2) Verify the {(com_W, com_E, com_F)}_i=1^k sequence matches
///         the ones returned in Phase1 circuit
/// (3) compute the hashchain(G_1): [com_All_w, (comW, com_E, com_F)_i=1^k, prf]
///             hashchain(G_2): the qa-nizk key series
///     and verify that hash(hashchain(G_1), hashchain(G_2)) is the same
///     as computed by the cyclepair circuits's final result (in ZiPart2)
/// (4) verify that hashchain(G_2) is the same as the QA-NIZK verifier key
///     hash
/// --> the above essentially finishes the proof of circ1's com_all_w
///   matches the (W_i || E_i)_i=1^k for the comW, comE, comF of each subcirc
///   of circ1.
/// As this is a "sub-circuit", it does NOT have public I/O, instead,
/// It returns to the caller a Return Package of Wires 
///  In addition to the Phase1CircRet of its main circuit,
///  It returns (final_result_of_circ2, hashchain(b)) where
/// final_result_of_circ2 is hash(hashchain(a), hashchain(b))
#[derive(Clone, Debug)]
pub struct Phase2Circuit<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	LK: LookupTableTwoCol<C1::ScalarField>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
	_gm: PhantomData<GM>,

	/// main circuit which handles its own proof 
	main_circ:  Phase1Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM, H>,
	/// its own cyclepair_inputs, need to be consistent with the
	/// phase1circ return later in gen_constraints
    cyclepair_inputs: Vec<Vec<CF1<C1>>>,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool> Phase2Circuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, H>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>, //should be kzg
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
	CF2<C1>: PrimeField,
	CF2<C2>: PrimeField,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,

{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. (noe: com_all_w is used
	/// to compute kzg_all_com_ch in circuit)
	/// NOTE: we do not need com_all_w and r_all_w like circ1
	/// because we only have one circuit.
    pub fn from_nova<FC: FCircuit<C1::ScalarField> 
		+ SigmaIR1CS<H, C1::ScalarField, LK, GM, C=C1>> 
		(nova: FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E,LK, GM, H>, 
		 com_all_w_2: C1,
		 r_all_w_2: C1::ScalarField,
		 cyclepair_inputs: Vec<Vec<CF1<C1>>>,
	 	) -> Result<Self, Error> {
			let main_circ= Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM, H>::from_nova::<FC>(nova, com_all_w_2, r_all_w_2)?;
			Ok(Self {
				_gm: PhantomData,
				main_circ,
				cyclepair_inputs: cyclepair_inputs,
        	})
    }

	/// generate FpVar version of cyclepair_inputs and the 
	/// compute the hash(hash_chain(a), hash_chain(b))
	/// which will match the final_result of z_n output of 
	/// the last circuit.
	/// return (cyclapair_inputs_var, expected_final_result, hashchain(b))
	/// where hashchain(b) should match the hash of the qa_nizk_ver_key.hash()
	fn process_cyclepair_inp(&self, cs: ConstraintSystemRef<CF1<C1>>)->(Vec<Vec<FpVar<C1::ScalarField>>>, FpVar<C1::ScalarField>, FpVar<C1::ScalarField>){
		//1. build the cyclepair_inputs_var
		let cyclepair_inputs_var = self.cyclepair_inputs.iter().map(|row|
			Vec::<FpVar<C1::ScalarField>>::new_witness(cs.clone(), 
				|| Ok(row.clone())).unwrap()).
				collect::<Vec<Vec<FpVar<C1::ScalarField>>>>();

		//2. build the final result over the cycle_inputs_var just built
		// simulate what sigma_cyclepair computes hash chain
		assert!(cyclepair_inputs_var[0].len()==164); //check 
		let mut hc_a = FpVar::<C1::ScalarField>::zero(); 
		let mut hc_b = FpVar::<C1::ScalarField>::zero(); 
		for row in &cyclepair_inputs_var{
			//each row has 164 elements (gt1, a, b, gt2)
			//a has 3 elements and starts at idx 12
			let a = row[12*5..12*5+3*5].to_vec();
			let b = row[15*5..20*5].to_vec();
			hc_a = compute_hc_var(&self.main_circ.poseidon_config, 
				&hc_a, &a, cs.clone());
			hc_b = compute_hc_var(&self.main_circ.poseidon_config, 
				&hc_b, &b, cs.clone());
		}
		let final_result = hash_var(&self.main_circ.poseidon_config, &vec![hc_a, hc_b.clone()], cs.clone()); 
		(cyclepair_inputs_var, final_result, hc_b)
	}

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return the final_result = hash_a_b
    pub fn generate_constraints_adv(self, circ1_res: &Phase1CircuitRet<CF1<C1>,C1>, cs: ConstraintSystemRef<CF1<C1>>) -> Result<Phase2CircuitRet<CF1<C1>,C1>, Error> {
		//1. generate the cyclepair input and expected result 
		// expected result is hash(hashchain(a), hashchain(b))
		// which is the final result of last circuit
		let c0 = cs.num_constraints();
		let mut c1 = cs.num_constraints();
		let mut t1 = GTimer::new();
		let log_level = LOG3;
		let b_debug = B_DEBUG;
		let (cyclepair_inputs_var, expected_final_result, hashchain_b) = 
			self.process_cyclepair_inp(cs.clone());
		log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 1: gen_expected_final_result. r1cs: {}", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//2. perform consistency check (perform 0 to k-2 -> com_all_w,
		//  com_W, com_W, com_F for the 1st phase circuits,
		//  which is passed from the Phase1Ret of the 1st phase.
		let k = self.cyclepair_inputs.len(); 
		assert!(k-1 == circ1_res.vec_coms.len());
		for i in 0..k-1{
			let v2 = vec![circ1_res.vec_coms[i].x.clone(), 
				circ1_res.vec_coms[i].y.clone()];
			let vres = v2.iter().map(|x| x.0.iter().map(
				|limb| limb.v.clone()).collect::<Vec<FpVar::<CF1<C1>>>>())
				.collect::<Vec<Vec<FpVar::<CF1<C1>>>>>()
				.concat();
			assert!(vres.len()==10); //5 limbs each
			for j in 12*5..12*5+2*5{//ignore z coordinate which is 0
				#[cfg(test)]{ 
					use ark_r1cs_std::R1CSVar;
					if vres[j-12*5].value().is_ok(){
					assert!(vres[j-12*5].value()?==
						cyclepair_inputs_var[i][j].value()?);
				} }
				vres[j-12*5].enforce_equal(&cyclepair_inputs_var[i][j])?;
			}
		}
		log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 2: check cyclepair consistency. r1cs: {}", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//3. perform the main circuit to check its own validity
		assert!(self.main_circ.cp_U_i.is_some());  //2nd phase require it
		let my_phase1_ret={
			let main_circ2 = self.main_circ.clone();
			main_circ2.generate_constraints_adv(3,cs.clone()).unwrap()
		};
		log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 3: Main circ construction. r1cs: {}", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//4. validate the final_result
		if b_debug{
			use ark_r1cs_std::R1CSVar;
			if expected_final_result.value().is_ok(){
				assert!(expected_final_result.value()?
					==my_phase1_ret.final_result.value()?);
			} 
		}
		expected_final_result.enforce_equal(&my_phase1_ret.final_result)?;

		//5. perform an extra cyclepair check!
        //#[cfg(feature = "light-test")]
        //println!("[WARNING]: Running with the 'light-test' feature, skipping the cyclepair part of the DeciderEthCircuit.\n Only for testing purposes.");
        //#[cfg(not(feature = "light-test"))]
		let b_light_test = false;
		if !b_light_test
        {
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::circuits::cyclefold::{CycleFoldCommittedInstanceVar};
            use ark_r1cs_std::ToBitsGadget;
			//5. Verify cyclepair instance
			//(1) u_i.x[2] = cp_U_i.hash()
			//(2) cp_W_i satisfies the cyclepair R1CS
			//(3) cp_U_i is the commitment of cp_W_i
			//-- cost: 14M for commitment keys 
        	let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            	Ok(self.main_circ.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        	})?;
        	let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(
				cs.clone(), &self.main_circ.poseidon_config);
			assert!(self.main_circ.cp_U_i.is_some());
            let cp_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>
			::new_witness(cs.clone(), || { 
				Ok(self.main_circ.cp_U_i.unwrap())
            })?;
            let cp_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.main_circ.cp_W_i.unwrap())
            })?;
            let (cp_u_i_x, _) = cp_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (my_phase1_ret.u_i.x[2]).enforce_equal(&cp_u_i_x)?;
			#[cfg(test)]{
				use ark_r1cs_std::R1CSVar;
				if my_phase1_ret.u_i.x[2].value().is_ok(){
				assert!(my_phase1_ret.u_i.x[2].value()?==cp_u_i_x.value()?);
			} }
			log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 5: check u_i.x[2]=cp_U_i.hash(). r1cs: {}", cs.num_constraints()-c1), &mut t1);
			c1 = cs.num_constraints();

            //9. check Pedersen commitments of cp_U_i.{cmE, cmW}
			//48M (50G RAM) for cmW and 35M (40G) for cmW
			//check R1CS relation: 90MB (100GB) -> 241GB NOW. 
			//TOTAL: 217M constraints now!!!!. (about 1hr to this point)
			//*** set the debug_disable to true on real server
			let debug_enable1 = true;
			let debug_enable2 = false;

            let H2 = GC2::new_constant(cs.clone(), 
				self.main_circ.cp_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), 
				self.main_circ.cp_pedersen_params.generators)?;
			if debug_enable1{
				let cp_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cp_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
				let computed_cmE = PedersenGadget::<C2, GC2>::commit(
					H2.clone(),
					G.clone(),
					cp_W_i_E_bits?,
					cp_W_i.rE.to_bits_le()?,
				)?;
				cp_U_i.cmE.enforce_equal(&computed_cmE)?;
				#[cfg(test)]{if cp_U_i.cmE.value().is_ok(){
					assert!(cp_U_i.cmE.value()?== computed_cmE.value()?);
				} }
			}
			log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 6.1: check cp_W_i commits to cp_U_i. r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			if debug_enable2{
				let cp_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cp_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();
				let computed_cmW =
					PedersenGadget::<C2, GC2>::commit(H2, G, cp_W_i_W_bits?, cp_W_i.rW.to_bits_le()?)?;
				cp_U_i.cmW.enforce_equal(&computed_cmW)?;
				#[cfg(test)]{ if cp_U_i.cmW.value().is_ok(){
					assert!(cp_U_i.cmW.value()?== computed_cmW.value()?);
				} }
			}
			log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 6.2: check cp_E_i commits to cp_U_i. r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			//10. check cyclepair witness satisfy its r1cs
            let cp_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness( cs.clone(), || Ok(self.main_circ.cp_r1cs.clone()),)?;
            let cp_z_U = [vec![cp_U_i.u.clone()], cp_U_i.x.to_vec(), 
				cp_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cp_r1cs, 
				cp_W_i.E, cp_U_i.u.clone(), cp_z_U)?;
			log_perf(log_level, &format!("Phase2 Circ gen_cs: Step 7: check cp_W_i satisfies cyclepair instance. r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();
		}

		let res = Phase2CircuitRet::<C1::ScalarField, C1>{
			hashchain_b: hashchain_b,
			main_ret: my_phase1_ret.clone()
		};

		let _c1 = c1; //to disable warning
		log_perf(log_level, &format!("Phase2 Circ gen_cs: COMPLETE. TOTAL r1cs: {}, RAM: {} GB", cs.num_constraints()-c0, get_mem_usage()), &mut t1);

		Ok( res )
	}
}

/// Interpolates the polynomial from the given vector, 
/// and then returns it's evaluation at the
/// given point. NOTE: different from the original version,
/// we DO NOT interpret over domain. Just execute it as a polynomial.
/// NOTE: arkworks 4.0 has a bug: when linear combinations in 
/// R1CS is too long, it will overflow the stack.
/// Here, we introduce a witness one as a temporary patch.
/// The idea is that when we have a chain of adds of too long
/// e.g., v= v_1 + ... v_4096, we cut it as
/// v = (v_1 + ... v_1024) * 1 + (v_1025 + ... v_2048) * 1  + ... (v_3072+..v_4096) * 1
/// It comes at cost one more constraint per 1024 adds, which 
/// introduces a minimum cost. This can be dropped after arkworks
/// addresses the stack overflow issue. 
/// See <https://github.com/privacy-scaling-explorations/sonobe/issues/80>

#[allow(unused)] // unused while check 7 is disabled
fn evaluate_gadget<F: PrimeField>(
    v: Vec<FpVar<F>>,
    point: FpVar<F>,
	one: FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
	let mut eval = FpVar::<F>::zero();
	let mut prod = FpVar::<F>::one();
	let mut v2 = v.clone();
	v2.reverse();
	for i in 0..v2.len(){
		eval= &eval* &point + &v2[i];
		if i%1024==0{
			eval= &eval* &one;
		}
	}
	Ok(eval)
}

/// Gadget that computes the KZG challenges, also offers the rust native implementation compatible with the gadget.
pub struct KZGChallengesGadgetSuper<C: CurveGroup> {
    _c: PhantomData<C>,
}

#[allow(clippy::type_complexity)]
impl<C> KZGChallengesGadgetSuper<C>
where
    C: CurveGroup,
    C::ScalarField: PrimeField,
    <C as CurveGroup>::BaseField: PrimeField,
    C::ScalarField: Absorb,
{
    pub fn get_challenge_native(
		poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i: CommittedInstanceFoldPotSuper<C>, _com_all: C
    ) -> C::ScalarField{
        let mut transcript = PoseidonSponge::<C::ScalarField>
			::new(&poseidon_config);
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmW);
		}
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmE);
		}
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmF);
		}
        let challenge = transcript.get_challenge();
		challenge
    }

    // compatible with the native get_challenges_native
    pub fn get_challenge_gadget(
		cs: ConstraintSystemRef<CF1<C>>,
		poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i: CommittedInstanceVarFoldPotSuper<C>,
		_com_all: NonNativeAffineVar<C>, 
    ) -> Result<FpVar<C::ScalarField>, SynthesisError> {
        let mut transcript = PoseidonSpongeVar::<C::ScalarField>
			::new(cs.clone(), &poseidon_config);
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmW.to_constraint_field()?)?;
		}
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmE.to_constraint_field()?)?;
		}
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmF.to_constraint_field()?)?;
		}
        let challenge = transcript.get_challenge()?;

        Ok( challenge )
    }
}

/// Represents the public i/o of the TwoPhaseDeciderCircuit,
/// most elements can be retrieved from nova
#[derive(Clone, Debug, PartialEq)]
pub struct TwoPhaseCircInput<F: PrimeField,C: CurveGroup<ScalarField=F>>{
	/// the ch of circ1
	pub ch1: F,
	/// the rc of circ1
	pub rc1: F,
	/// the kzg sum of circ1
	pub kzg_sum1: F,
	/// the the challenge of kzg_all_com_e
	pub kzg_all_com_ch1: F,
	/// the evaluation of kzg_all_com at kzg_all_com_ch
	pub eval_w_e1: F,

	// the ch of circ2: removed (not needed): because the
	// circuit computes the hash(hashchain(a), hashchain(b))
	// which locks all cyclepair inputs, and the overall claim
	// does NOT include anything about the commitments to these cyclapir inputs.
	// no need to include them in public inputs.
	//pub ch2: F,
	// the rc of circ2: removed (not needed)
	//pub rc2: F,
	// the kzg sum of circ2
	//pub kzg_sum2: F,

	/// the the challenge of kzg_all_com_e (needed for decider circuit)
	pub kzg_all_com_ch2: F,
	/// the evaluation of kzg_all_com at kzg_all_com_ch
	pub eval_w_e2: F,

	/// hash of the qa_nizk_vkey
	pub qa_nizk_vkey_hash: F,

	/// the comE of U_{i+1} of circ2
	pub comE2: C,
	/// the comW of U_{i+1} of circ2
	pub comW2: C,
	/// the comF of U_{i+1} of circ2
	pub comF2: C,
}

impl <F: PrimeField, C: CurveGroup<ScalarField=F>> TwoPhaseCircInput<F,C>
where
C::Affine: AffineFromField<CF2<C>>,
CF2<C>: PrimeField
{
	pub fn to_vec(&self)->Result<Vec<F>,Error>{
		let mut res = vec![
			self.ch1.clone(),
			self.rc1.clone(),
			self.kzg_sum1.clone(),
			self.kzg_all_com_ch1.clone(),
			self.eval_w_e1.clone(),

			self.kzg_all_com_ch2.clone(),
			self.eval_w_e2.clone(),

			self.qa_nizk_vkey_hash.clone(),
		];
		let (comEx, comEy) = 	NonNativeAffineVar::inputize(self.comE2)?;
		let (comWx, comWy) = 	NonNativeAffineVar::inputize(self.comW2)?;
		let (comFx, comFy) = 	NonNativeAffineVar::inputize(self.comF2)?;
		let mut part2 = vec![comEx, comEy, comWx, comWy, comFx, comFy].concat();
		res.append(&mut part2);
		Ok(res)
	}

	/// parse from vector
	pub fn from_vec(v: &Vec<F>)->Self{
		let (ch1, rc1, kzg_sum1, kzg_all_com_ch1, eval_w_e1,
			  kzg_all_com_ch2, eval_w_e2) = 
			v[0..7].to_vec().into_iter().collect_tuple().unwrap();
		let qa_nizk_vkey_hash = v[7];
		let vec_rest = &v[8..v.len()];
		assert!(vec_rest.len()==5*6);
		let vec_fq = vec_rest.chunks(5).map(|chunk| {
			f1_limbs_to_f2::<F, CF2<C>>(&chunk.to_vec())
		}).collect::<Vec<CF2<C>>>();
		assert!(vec_fq.len()==6);
		let v_pt = vec_fq.chunks(2).map(|chunk|{
			C::Affine::from_fields(chunk[0], chunk[1])
		}
		).collect::<Vec<C::Affine>>();
		let (comE2, comW2, comF2): (C,C,C) = (v_pt[0].into(), 
			v_pt[1].into(), v_pt[2].into());
		Self{
			ch1, rc1, kzg_sum1, kzg_all_com_ch1, eval_w_e1,
			kzg_all_com_ch2, eval_w_e2,
			qa_nizk_vkey_hash,
			comE2, comW2, comF2
		}
	}
}

/// Circuit that implements the in-circuit checks for the two phase
/// Scheme. In fact, it employs two instances of DeciderEthCircuitSuper,
/// and pass the cyclepair_input in between to make sure that
/// they are consistent.
#[derive(Clone, Debug)]
pub struct TwoPhaseDeciderEthCircuitSuper<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, GM2, const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	LK: LookupTableTwoCol<C1::ScalarField>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
	/// circuit 1 for nova1
	circ1:  Phase1Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM,H>,
	/// circuit 2 for nova2
	circ2:  Phase2Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>,
	/// public input for the circuit
	inp:  TwoPhaseCircInput<CF1<C1>,C1>,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, GM2, const H: bool> TwoPhaseDeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, GM2, H>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    //CS1: CommitmentScheme<C1, H> + CommitmentScheme<C1>,
    CS1: CommitmentScheme<C1, H>,
    CS1E: CommitmentScheme<C1, H>, //should be kzg
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
	CF2<C1>: PrimeField,
	CF2<C2>: PrimeField,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. Basically,
	/// it builds two decider circuits, one for each nova,
	/// and builds up the checks to verify the consistency among the
	/// non-deterministic advice.
    pub fn from_nova<
	FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM,C=C1>,
		>
		(
        nova1: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, GM, H>,
        nova2: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, SigmaIR1CS_Inst<C1::ScalarField, C1, CS1,LK,GM2, H>, CS1, CS2, CS1E, LK, GM2, H>,

		cyclepair_inputs: Vec<Vec<C1::ScalarField>>,
		_qa_nizk_vkey_hash: C1::ScalarField,
		_poseidon_config: PoseidonConfig<C1::ScalarField>,
		com_all_w_1: C1,
		r_all_w_1: C1::ScalarField,
		com_all_w_2: C1,
		r_all_w_2: C1::ScalarField,
		inp: TwoPhaseCircInput<CF1<C1>,C1>,
    ) -> Result<Self, Error> {
		let circ1 = Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM,H>::from_nova::<FC>(nova1, com_all_w_1, r_all_w_1)?;
		let circ2 = Phase2Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>::from_nova::<SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, GM2, H>>(nova2, com_all_w_2, r_all_w_2, cyclepair_inputs)?;
		Ok( Self{ circ1, circ2, inp } )
    }

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, GM2, const H: bool> ConstraintSynthesizer<CF1<C1>> for TwoPhaseDeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, GM2, H>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H> + CommitmentScheme<C1>,
    CS1E: CommitmentScheme<C1, H>, //should be kzg
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
	CF2<C1>: PrimeField,
	CF2<C2>: PrimeField,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		let mut gt1 = GTimer::new();
		let mut gt2 = GTimer::new();
		let log_level = LOG2;
		let b_debug = B_DEBUG;

		//1. let the two circuits generate constraints first
		let c0 = cs.num_constraints();
		let phase1_ret=self.circ1
			.generate_constraints_adv(2,cs.clone()).unwrap();
		//let phase1_ret = Phase1CircuitRet::dummy(cs.clone());
		log_perf(log_level, &format!("TwoPhaseCirc build circ1: {} cs.",
			cs.num_constraints()-c0), &mut gt2);
		let c1 = cs.num_constraints();

		let phase2_ret = self.circ2.generate_constraints_adv(&phase1_ret, cs.clone()).unwrap();
		let c2 = cs.num_constraints();
		log_perf(log_level, &format!("TwoPhaseCirc build circ2: {} cs.",
			c2-c1), &mut gt2);


		//2. establish the public inputs and check the consistency
		// with the phase1 and phase2 returns.
		let _s_dbg = vec![
			"ch1", "rc1", "kzg_sum1", "kzg_all_com_ch1", "eval_w_e1",
			"kzg_all_com_ch2", "eval_w_2", "qa_nizk_vkey_hash",
		];
		let vec_inp = self.inp.to_vec().expect("Inp to Vec error")
			.into_iter().map(|x: C1::ScalarField|
				FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(x) )
					.expect("FpVar new input fails"))
			.collect::<Vec<FpVar<CF1<C1>>>>();

		let mut vec_ret = vec![
			phase1_ret.ch, phase1_ret.rc, phase1_ret.kzg_sum,
				phase1_ret.kzg_all_com_ch, phase1_ret.eval_w_e,
			phase2_ret.main_ret.kzg_all_com_ch, phase2_ret.main_ret.eval_w_e,
				phase2_ret.hashchain_b];
		let limbs = phase2_ret.main_ret.u_i1_0_cmE.x.0.len();
		let coms = vec![phase2_ret.main_ret.u_i1_0_cmE,
			phase2_ret.main_ret.u_i1_0_cmW, phase2_ret.main_ret.u_i1_0_cmF];
		let mut part2 = coms.into_iter().map(|pt| {
			vec![pt.x, pt.y].into_iter().map(|ui| 
				ui.0.iter().map(|x| 
					x.v.clone()).collect::<Vec<FpVar::<CF1::<C1>>>>()
			).flatten().collect::<Vec<FpVar::<CF1::<C1>>>>()
		}).flatten().collect::<Vec<FpVar::<CF1::<C1>>>>();
		assert!(part2.len() == 6 * limbs); //5 limbs each
		vec_ret.append(&mut part2);
		assert!(vec_ret.len()==vec_inp.len());
		for i in 0..vec_ret.len(){
			if b_debug{
				use ark_r1cs_std::R1CSVar;
				if vec_inp[0].value().is_ok(){
				assert!(vec_inp[i].value()?==vec_ret[i].value()?,
					"ERROR on idx i: {} for {}", i,
					if i<_s_dbg.len() {_s_dbg[i]} 
						else {_s_dbg[(i-_s_dbg.len())/limbs]}) ;
				}
			}
			vec_ret[i].enforce_equal(&vec_inp[i])?;
		}
		let c3 = cs.num_constraints();
		log_perf(log_level, &format!("TwoPhaseCirc connect 2 circs: {} cs.",
			c3-c2), &mut gt2);

		if b_debug{
			let cs_ok = cs.is_satisfied();
			if cs_ok.is_ok(){ assert!(cs_ok.unwrap()); }
		}

		log_perf(log_level-1, &format!("*** Groth16 TwoPhaseCirc TOTAL constraints: {} ***. circ1: {}, circ2: {} constraints.", cs.num_constraints(), c1, c2-c1), &mut gt1);
		Ok( () )

	}
}


#[cfg(test)]
pub mod tests_decider_eth_circuit_super {
	use ark_ff::{BigInteger};
	use crate::utils::vec::poly_from_vec;
	use ark_poly::{Polynomial};
	use ark_std::{UniformRand,One};
    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_r1cs_std::bits::uint8::UInt8;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_bn254::{Fr, G1Projective as Projective};

    use super::*;
    use crate::arith::{
        r1cs::{
            tests::{get_test_r1cs, get_test_z},
            {extract_r1cs, extract_w_x},
        },
        Arith,
    };
    use crate::frontend::tests::{CubicFCircuit, CustomFCircuit, WrapperCircuit};

	#[test]
	fn test_phase2_input(){
		//1. generate random
        let mut rng = ark_std::test_rng();
		let inp= TwoPhaseCircInput::<Fr, Projective>{
			ch1: Fr::rand(&mut rng),
			rc1: Fr::rand(&mut rng),
			kzg_sum1: Fr::rand(&mut rng),
			kzg_all_com_ch1: Fr::rand(&mut rng),
			eval_w_e1: Fr::rand(&mut rng),

			kzg_all_com_ch2: Fr::rand(&mut rng),
			eval_w_e2: Fr::rand(&mut rng),

			qa_nizk_vkey_hash: Fr::rand(&mut rng),
			comE2: Projective::rand(&mut rng),
			comW2: Projective::rand(&mut rng),
			comF2: Projective::rand(&mut rng),
		};

		let vec = inp.to_vec().unwrap();
		let inp2 = TwoPhaseCircInput::<Fr,Projective>::from_vec(&vec);
		let vec2 = inp2.to_vec().unwrap();
		assert!(vec==vec2);
		assert!(inp==inp2);
	}

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let r1cs: R1CS<Fr> = get_test_r1cs();
        let rel_r1cs = r1cs.clone().relax();
        let z = get_test_z(3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(rel_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(rel_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        let r1cs = extract_r1cs::<Fr>(&cs);
        let (w, x) = extract_w_x::<Fr>(&cs);
        let z = [vec![Fr::one()], x, w].concat();
        r1cs.check_relation(&z).unwrap();

        let relaxed_r1cs = r1cs.clone().relax();
        relaxed_r1cs.check_relation(&z).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let z_i = vec![Fr::from(3_u32)];
        let cubic_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: cubic_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_circuit.step_native(0, z_i, vec![]).unwrap()),
        };

        test_relaxed_r1cs_gadget(circuit);
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs.clone(), || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y = <Sha256 as CRHScheme>::evaluate(&(), x.clone()).unwrap();

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_custom_circuit() {
        let n_constraints = 10_000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints).unwrap();
        let z_i = vec![Fr::from(5_u32)];
        let circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i, vec![]).unwrap()),
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() {
    	use ark_pallas::{Fq, Fr};
        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let custom_circuit = CustomFCircuit::<Fq>::new(10).unwrap();
        let z_i = vec![Fq::from(5_u32)];
        let circuit = WrapperCircuit::<Fq, CustomFCircuit<Fq>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i, vec![]).unwrap()),
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fq>(&cs);
        let (w, x) = extract_w_x::<Fq>(&cs);
        let z = [vec![Fq::one()], x, w].concat();

        let relaxed_r1cs = r1cs.clone().relax();

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let zVar = Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(z.clone())).unwrap();
        let EVar =
            Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.clone().E)).unwrap();
        let uVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fq, FpVar<Fq>>::new_witness(cs.clone(), || Ok(r1cs.clone())).unwrap();
        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let zVar = Vec::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fr, NonNativeUintVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();
        RelaxedR1CSGadget::check_nonnative(r1csVar, EVar, uVar, zVar).unwrap();
    }


    // The test test_polynomial_interpolation is temporary disabled due
    // https://github.com/privacy-scaling-explorations/sonobe/issues/80
    // for n<=11 it will work, but for n>11 it will fail with stack overflow.
	// NOTE that the issue is addressed in evaluate_gadget by chunking
	// heavy linear combinations (every 1024 items).
    #[test]
    fn test_polynomial_interpolation() {
        let mut rng = ark_std::test_rng();
        let n = 12;
        let l = 1 << n;

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(l)
            .collect();
        let challenge = Fr::rand(&mut rng);

        let polynomial = poly_from_vec(v.to_vec()).unwrap();
        let eval = polynomial.evaluate(&challenge);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let vVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(v)).unwrap();
        let challengeVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(challenge)).unwrap();
		let one= FpVar::<Fr>::new_witness(cs.clone(),  ||
			Ok(Fr::from(1u32)) ).unwrap();
        let evalVar = evaluate_gadget::<Fr>(vVar, challengeVar, one)
			.unwrap();

        use ark_r1cs_std::R1CSVar;
        assert_eq!(evalVar.value().unwrap(), eval);
		//the above will lead to OVERFLOW due to a bug in arkworks
		//instead, we verify evalVar is equal to eval in circuit
		let evalVar2 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(eval)).unwrap();
		evalVar2.enforce_equal(&evalVar).expect("evalVar err");
        assert!(cs.is_satisfied().unwrap());
    }

}

