/* Created 09/15/2024. Adaptation for super_nova 
   Changed 01/09/2025. Add TwoPhaseDeciderCircuit to accomodate to
   	the two phase cyclepair strategy.
*/

/// This file implements the onchain (Ethereum's EVM) decider circuit. 
/// For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group, pairing::Pairing};
use ark_ff::{BigInteger, PrimeField, Field, ToConstraintField};
use ark_poly::{Polynomial,univariate::DensePolynomial,DenseUVPolynomial};
use ark_r1cs_std::{
	R1CSVar as OtherR1CSVar,
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar,FieldVar},
    prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	//prelude::*,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{log2, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::foldpot::from_field::{AffineFromField,curve_from_field_elements};
use crate::folding::{
	nova::{
		nifs::NIFS, 
	},
	foldpot::{
		FoldPot, CommittedInstanceFoldPot, WitnessFoldPot, 
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,LookupTableTwoCol_Inst,SigmaIR1CS_Inst,ZiPartTwoInst,ZiPartTwoInstVar},
		nifs::{NIFSFoldPot},
		circuits::{ChallengeGadgetFoldPot,CommittedInstanceVarFoldPot},
		//decider_eth_circuit::{RelaxedR1CSGadget, R1CSVar,WitnessVarFoldPot,CycleFoldWitnessVar},
		mod_super::{WitnessFoldPotSuper,CommittedInstanceFoldPotSuper, FoldPotSuper},
		circuits_super::{ChallengeGadgetFoldPotSuper,AugmentedFCircuitFoldPotSuper, field_to_usize,CommittedInstanceVarFoldPotSuper},
		sigma_cyclepair::{compute_hc_var, hash_var},
	},
};
use crate::arith::r1cs::R1CS;
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::{
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,CF3,
};
use crate::folding::{
	nova::{circuits::CommittedInstanceVar, CommittedInstance, Nova, Witness},
};
use crate::frontend::FCircuit;
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::{
    gadgets::{MatrixGadget, SparseMatrixVar, VectorGadget},
    vec::poly_from_vec,
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

/// Packs the wires returned by Phase1Circuit
pub struct Phase1CircuitRet<F:PrimeField, C: CurveGroup<ScalarField=F>>{
	/// challenge for kzg_all_com
	pub kzg_all_com_ch: FpVar<F>,
	/// the evaluation result 
	pub kzg_all_com_eval: FpVar<F>,
	/// kzg of the word problem (kzg_lk + kzg_wd + kzg_others
	pub kzg_batchword_eval:  FpVar<F>,
	/// the challenge used for kzg_batchword
	pub kzg_batchword_ch: FpVar<F>,
	/// the random combination factor used for kzg_batchword
	pub kzg_batchword_rc: FpVar<F>,
	/// rows of (comE, comW, comF)
	pub vec_coms: Vec<Vec<NonNativeAffineVar<C>>>,
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
pub struct Phase1Circuit<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool = false>
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

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
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
    /// R1CS of the Augmented Function circuit (each)
    pub r1cs: Vec<Arc<R1CS<C1::ScalarField>>>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: Arc<R1CS<C2::ScalarField>>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
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

    /// used for computing KZG challenges (advice) - will be checked
	pub com_all_w: Option<C1>,

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
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool> Phase1Circuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, H>
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

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. (noe: com_all_w is used
	/// to compute kzg_all_com_ch in circuit)
    pub fn from_nova<FC: FCircuit<C1::ScalarField> 
		+ SigmaIR1CS<C1::ScalarField, LK>> 
		(nova: FoldPotSuper<E,P,C2G2,C1,GC1,C2,GC2,FC,CS1,CS2,CS1E,LK, H>, 
			com_all_w: C1) -> Result<Self, Error> {
        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(&nova.poseidon_config);

        //1. compute the U_{i+1}, W_{i+1}
		let (U_i1, W_i1, r_Fr, cmT)= nova.gen_next_folded()?;
		/*
		let j = field_to_usize(&nova.pc_i1);
		let pci_val = field_to_usize(&nova.pc_i);
        let (T, cmT) = NIFSFoldPot::<C1, CS1, H>::compute_cmT(
            &nova.cs_pp[j],
            &nova.r1cs[j],
            &nova.w_i.clone(),
            &nova.u_i.clone(),
            &nova.W_i.vec_wit[j],
            &nova.U_i.vec_inst[j],
        )?;

        let r_bits = ChallengeGadgetFoldPotSuper::<C1>::get_challenge_native(
            &mut transcript,
            nova.pp_hash,
            nova.U_i.clone(),
            nova.u_i.clone(),
            cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(
			&r_bits)).ok_or(Error::OutOfBounds)?;

        let (W_i1_pci, U_i1_pci) = NIFSFoldPot::<C1, CS1, H>::fold_instances(
            r_Fr, &nova.W_i.vec_wit[pci_val], 
				&nova.U_i.vec_inst[pci_val], 
				&nova.w_i, &nova.u_i, &T, cmT,
        )?;
		let mut W_i1 = nova.W_i.clone();
		let mut U_i1 = nova.U_i.clone();
		W_i1.vec_wit[pci_val] = W_i1_pci;
		U_i1.vec_inst[pci_val] = U_i1_pci;
		*/

        //2.compute the KZG challenges used as inputs in the circuit
        let (kzg_challenge_W, kzg_challenge_E, kzg_challenge_F) =
            KZGChallengesGadgetSuper::<C1>::get_challenges_native(&mut transcript, U_i1.clone());

        //3. get KZG evals (here W is the combined vector of all witnesses)
        let mut W = W_i1.vec_wit.iter().map(|v| v.W.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
		let sum_len = W_i1.vec_wit.iter().map(|v| v.W.len()).sum::<usize>();
		assert!(sum_len==W.len());
        W.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W.len().next_power_of_two() - W.len()),
        );
        let mut E = W_i1.vec_wit.iter().map(|v| v.E.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
        E.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(E.len().next_power_of_two() - E.len()),
        );
		let size_F = W_i1.vec_wit.iter().map(|v| v.size_F)
			.collect::<Vec<usize>>();
		let start_F = W_i1.vec_wit.iter().map(|v| v.start_F)
			.collect::<Vec<usize>>();

		//	3.2 ADDED for comF
        let mut F = W_i1.vec_wit.iter().map(|v|{
			(&v.W[v.start_F..v.start_F+v.size_F]).to_vec()
		}).into_iter().flatten().collect::<Vec<C1::ScalarField>>();
        F.extend( std::iter::repeat(C1::ScalarField::zero()) 
			.take(F.len().next_power_of_two() - F.len()));
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&kzg_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&kzg_challenge_E);
        let p_F = poly_from_vec(F.to_vec())?;
        let eval_F = p_F.evaluate(&kzg_challenge_F);

		//4. ADDED for lookup
		let kzg_challenge_lkup = nova.z0_part2_inst.ch;
		let (col1_raw, col2_raw) = nova.lk_tbl.expect("lookup table null!")
			.as_ref().borrow().get_cols();
		let (lkup_col1_rev,lkup_col2_rev)
			: (Vec<C1::ScalarField>, Vec<C1::ScalarField>) 
			= (col1_raw.iter().rev().map(|x| *x).collect(), 
				col2_raw.iter().rev().map(|x| *x).collect());
		let (eval_col1, eval_col2) = {//in block to save mem 
			let p_col1 = poly_from_vec(lkup_col1_rev.clone())?;
			let p_col2 = poly_from_vec(lkup_col2_rev.clone())?;
			let eval_col1 = p_col1.evaluate(&kzg_challenge_lkup); 
			let eval_col2 = p_col2.evaluate(&kzg_challenge_lkup); 
			(eval_col1, eval_col2)
		};

        Ok(Self {
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
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
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

			n_circ: nova.n_circ,
			pc_0: nova.pc_0,
			pc_i: nova.pc_i,
			pc_i1: nova.pc_i1,

			zi_part2_inst: Some(nova.zi_part2_inst.clone()),

			com_all_w: Some(com_all_w),

        })
    }

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return the final_result = hash_a_b
    pub fn generate_constraints_adv(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(Option<Vec<Vec<FpVar<C1::ScalarField>>>>, Option<FpVar<C1::ScalarField>>), SynthesisError> {
		unimplemented!()
	}
}

/// Circuit that implements the in-circuit checks 
/// needed for the onchain (Ethereum's EVM) verification.
/// SuperNova version: needs to check the satisfication of each circuit.
#[derive(Clone, Debug)]
pub struct DeciderEthCircuitSuper<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool = false>
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
{
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
    /// R1CS of the Augmented Function circuit (each)
    pub r1cs: Vec<Arc<R1CS<C1::ScalarField>>>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: Arc<R1CS<C2::ScalarField>>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
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

    /// KZG challenges
    pub kzg_c_W: Option<C1::ScalarField>,
    pub kzg_c_E: Option<C1::ScalarField>,

    pub eval_W: Option<C1::ScalarField>,
    pub eval_E: Option<C1::ScalarField>,

	// Added for super nova
	/// the number of circuits
	pub n_circ: C1::ScalarField, 
	/// the initial pc
	pub pc_0: C1::ScalarField,
	/// the current pc (must be less than the number of circuits)
	pub pc_i: C1::ScalarField,
	/// the circuit ID to perform the next step computation
	pub pc_i1: C1::ScalarField,
	/// whether it supports cyclepair
	pub b_full_mode: bool,

	// Added for c_F and lookup
    pub kzg_c_F: Option<C1::ScalarField>,
	pub kzg_c_lkup: Option<C1::ScalarField>,
    pub eval_F: Option<C1::ScalarField>,
	pub eval_lkup_col1: Option<C1::ScalarField>,
	pub eval_lkup_col2: Option<C1::ScalarField>,
	/// the reversed lookup table col1, saved here to avoid duplicate
	/// work in decier_eth.rs
	pub lkup_col1_rev: Option<Vec<C1::ScalarField>>,
	/// reversed col2 of lookup table
	pub lkup_col2_rev: Option<Vec<C1::ScalarField>>,
	/// a copy of the zi_part2 from the FoldPot instance for witness
	/// generation
	pub zi_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>,

	/// will double check if in phase 1 circuit,
	/// will be set by the TwoPhaseDeciderCircuit before calling gen_constraints
	pub cyclepair_inputs_var: Option<Vec<Vec<FpVar<C1::ScalarField>>>>,
	/// the final_result of phase 2 circuit, will be set by
	/// TwoPhaseDeciderCircuit before calling gen_constraints
	pub final_result_var: Option<FpVar<C1::ScalarField>>,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool> DeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, H>
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

	// to allow call nova gen_next_folded in Phase1 circuit
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members.
    pub fn from_nova<
		FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
		> (
        nova: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, H>,
    ) -> Result<Self, Error> {
        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(&nova.poseidon_config);

        //1. compute the U_{i+1}, W_{i+1}
		let j = field_to_usize(&nova.pc_i1);
		let pci_val = field_to_usize(&nova.pc_i);
        let (T, cmT) = NIFSFoldPot::<C1, CS1, H>::compute_cmT(
            &nova.cs_pp[j],
            &nova.r1cs[j],
            &nova.w_i.clone(),
            &nova.u_i.clone(),
            &nova.W_i.vec_wit[j],
            &nova.U_i.vec_inst[j],
        )?;

        let r_bits = ChallengeGadgetFoldPotSuper::<C1>::get_challenge_native(
            &mut transcript,
            nova.pp_hash,
            nova.U_i.clone(),
            nova.u_i.clone(),
            cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(
			&r_bits)).ok_or(Error::OutOfBounds)?;

        let (W_i1_pci, U_i1_pci) = NIFSFoldPot::<C1, CS1, H>::fold_instances(
            r_Fr, &nova.W_i.vec_wit[pci_val], 
				&nova.U_i.vec_inst[pci_val], 
				&nova.w_i, &nova.u_i, &T, cmT,
        )?;
		let mut W_i1 = nova.W_i.clone();
		let mut U_i1 = nova.U_i.clone();
		W_i1.vec_wit[pci_val] = W_i1_pci;
		U_i1.vec_inst[pci_val] = U_i1_pci;

        //2.compute the KZG challenges used as inputs in the circuit
        let (kzg_challenge_W, kzg_challenge_E, kzg_challenge_F) =
            KZGChallengesGadgetSuper::<C1>::get_challenges_native(&mut transcript, U_i1.clone());

        //3. get KZG evals (here W is the combined vector of all witnesses)
        let mut W = W_i1.vec_wit.iter().map(|v| v.W.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
		let sum_len = W_i1.vec_wit.iter().map(|v| v.W.len()).sum::<usize>();
		assert!(sum_len==W.len());
        W.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W.len().next_power_of_two() - W.len()),
        );
        let mut E = W_i1.vec_wit.iter().map(|v| v.E.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
        E.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(E.len().next_power_of_two() - E.len()),
        );
		let size_F = W_i1.vec_wit.iter().map(|v| v.size_F)
			.collect::<Vec<usize>>();
		let start_F = W_i1.vec_wit.iter().map(|v| v.start_F)
			.collect::<Vec<usize>>();

		//	3.2 ADDED for comF
        let mut F = W_i1.vec_wit.iter().map(|v|{
			(&v.W[v.start_F..v.start_F+v.size_F]).to_vec()
		}).into_iter().flatten().collect::<Vec<C1::ScalarField>>();
        F.extend( std::iter::repeat(C1::ScalarField::zero()) 
			.take(F.len().next_power_of_two() - F.len()));
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&kzg_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&kzg_challenge_E);
        let p_F = poly_from_vec(F.to_vec())?;
        let eval_F = p_F.evaluate(&kzg_challenge_F);

		//4. ADDED for lookup
		let kzg_challenge_lkup = nova.z0_part2_inst.ch;
		let (col1_raw, col2_raw) = nova.lk_tbl.expect("lookup table null!")
			.as_ref().borrow().get_cols();
		let (lkup_col1_rev,lkup_col2_rev)
			: (Vec<C1::ScalarField>, Vec<C1::ScalarField>) 
			= (col1_raw.iter().rev().map(|x| *x).collect(), 
				col2_raw.iter().rev().map(|x| *x).collect());
		let (eval_col1, eval_col2) = {//in block to save mem 
			let p_col1 = poly_from_vec(lkup_col1_rev.clone())?;
			let p_col2 = poly_from_vec(lkup_col2_rev.clone())?;
			let eval_col1 = p_col1.evaluate(&kzg_challenge_lkup); 
			let eval_col2 = p_col2.evaluate(&kzg_challenge_lkup); 
			(eval_col1, eval_col2)
		};

        Ok(Self {
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
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
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
            kzg_c_W: Some(kzg_challenge_W),
            kzg_c_E: Some(kzg_challenge_E),
            kzg_c_F: Some(kzg_challenge_F),
            eval_W: Some(eval_W),
            eval_E: Some(eval_E),
            eval_F: Some(eval_F),

			n_circ: nova.n_circ,
			pc_0: nova.pc_0,
			pc_i: nova.pc_i,
			pc_i1: nova.pc_i1,

			kzg_c_lkup: Some(kzg_challenge_lkup),
			eval_lkup_col1: Some(eval_col1),
			eval_lkup_col2: Some(eval_col2),
			lkup_col1_rev: Some(lkup_col1_rev),
			lkup_col2_rev: Some(lkup_col2_rev),

			zi_part2_inst: Some(nova.zi_part2_inst.clone()),

			b_full_mode: nova.b_full_mode,

			cyclepair_inputs_var: None,
			final_result_var: None
        })
    }

	/// Returns the absolute index of the W_i, E_i, F_i 
	/// in the groth16 witness. The length of vec should
	/// match the number of circuits (note the last one is cycle fold
	/// circuit)
	pub fn get_idx_WEF_in_circuit()->Vec<((usize,usize), (usize,usize), (usize,usize))>{
		unimplemented!()
	}

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return the final_result = hash_a_b
    pub fn generate_constraints_adv(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(Option<Vec<Vec<FpVar<C1::ScalarField>>>>, Option<FpVar<C1::ScalarField>>), SynthesisError> {
		unimplemented!()
	}
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E, CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK> ConstraintSynthesizer<CF1<C1>>
    for DeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK >
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS1: CommitmentScheme<C1>,
    CS1E: CommitmentScheme<C1>, //must be kzg
    CS2: CommitmentScheme<C2>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    //C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
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
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		//1. generate Vector the R1CS var (one for each circuit)
		let pc_i_val = field_to_usize(&self.pc_i); //for fold
		let pc_i1_val = field_to_usize(&self.pc_i1); //for compute next (j)
		let pc_i_var = FpVar::new_witness(cs.clone(),  || Ok(self.pc_i))?;
        let vec_r1cs = self.r1cs.iter().map(|r1cs|
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>
			::new_witness(cs.clone(), || {
                Ok(r1cs.clone())
            }).unwrap()).collect::<Vec<
				R1CSVar::<C1::ScalarField,CF1<C1>,FpVar<CF1<C1>>>
			>>();

		//2. generate Var version of pp_hash, z_0, z_i
		// U_i, u_i, U_i1, given the advice from nova instance
		// NOTE: the following whenver new_input it matches the
		//the structure of the public input built in decier_eth::prove()
        let pp_hash = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i = FpVar::<CF1<C1>>::new_input(cs.clone(), || 
			Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;

        let u_dummy_native = CommittedInstanceFoldPot::<C1>::dummy(2);
        let w_dummy_native = WitnessFoldPot::<C1>::dummy(
            self.r1cs[pc_i_val].A.n_cols - 3, /* (3=2+1, since u_i.x.len=2) */
            self.E_len[pc_i_val],
        );

        let u_i = CommittedInstanceVarFoldPot::<C1>::new_witness(cs.clone(), 
			|| { Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap())
        })?;

        // here (U_i1, W_i1) = NIFS.P( (U_i,W_i), (u_i,w_i))
        let U_i1 = CommittedInstanceVarFoldPotSuper::<C1>::new_input(
		cs.clone(), || { Ok(self.U_i1.unwrap())
        })?;
        let W_i1 = WitnessVarFoldPotSuper::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i1.unwrap())
        })?;

        let kzg_c_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let kzg_c_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_E.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let kzg_c_F = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_F.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let kzg_c_lkup = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_lkup.unwrap_or_else(CF1::<C1>::zero))
        })?;


        let _eval_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_E.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let _eval_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let _eval_F = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_F.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let eval_lkup_col1 = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_lkup_col1.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let eval_lkup_col2 = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_lkup_col2.unwrap_or_else(CF1::<C1>::zero))
        })?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        //3. check RelaxedR1CS of U_{i+1} for each circuit
		for i in 0..field_to_usize(&self.n_circ){
        	let z_U1: Vec<FpVar<CF1<C1>>> =
            [vec![U_i1.vec_inst[i].u.clone()],
				U_i1.vec_inst[i].x.to_vec(), 
				W_i1.vec_wit[i].W.to_vec()].concat();
        	RelaxedR1CSGadget::check_native((&vec_r1cs)[i].clone(), 
				W_i1.vec_wit[i].E.clone(), 
				U_i1.vec_inst[i].u.clone(), 
				z_U1)?;
		}

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
        let (u_i_x, U_i_vec) = U_i.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone(),
			pc_i_var,
            z_0.clone(),
            z_i.clone(),
        )?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        #[cfg(feature = "light-test")]
        println!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        #[cfg(not(feature = "light-test"))]
        {
            use super::FOLDPOT_CF_N_POINTS;
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::circuits::cyclefold::{cf_io_len, CycleFoldCommittedInstanceVar};
            use ark_r1cs_std::ToBitsGadget;

			//7. compute cyclefold instance (they are standard - single inst)
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

            //8. u_i.x[1] == H(cf_U_i) - same as standard cyclefold
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            //9. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H = GC2::new_constant(cs.clone(), self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), self.cf_pedersen_params.generators)?;
            let cf_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
            let cf_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();

            let computed_cmE = PedersenGadget::<C2, GC2>::commit(
                H.clone(),
                G.clone(),
                cf_W_i_E_bits?,
                cf_W_i.rE.to_bits_le()?,
            )?;
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
            let computed_cmW =
                PedersenGadget::<C2, GC2>::commit(H, G, cf_W_i_W_bits?, cf_W_i.rW.to_bits_le()?)?;
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;

            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness(
                    cs.clone(),
                    || Ok(self.cf_r1cs.clone()),
                )?;

			//10. check cyclefold witness satisfy its r1cs
            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), 
				cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs, 
				cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;
        }

        // 11. (8.a, 6.a) compute NIFS.V and KZG challenges.
        // We need to ensure the order of challenge generation is the same as
        // the native counterpart, so we first compute the challenges here and
        // do the actual checks later.
        let cmT =
            NonNativeAffineVar::new_input(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        let r_bits = ChallengeGadgetFoldPot::<C1>::get_challenge_gadget(
            &mut transcript,
            pp_hash,
            U_i_vec,
            u_i.clone(),
            cmT.clone(),
        )?;
        let (incircuit_c_W, incircuit_c_E, incircuit_c_F) =
            KZGChallengesGadgetSuper::<C1>::get_challenges_gadget(&mut transcript, U_i1.clone())?;

        // 12. (6.b) check KZG challenges
        incircuit_c_W.enforce_equal(&kzg_c_W)?;
        incircuit_c_E.enforce_equal(&kzg_c_E)?;
        incircuit_c_F.enforce_equal(&kzg_c_F)?;

        // 13. (Check 7) is temporary disabled due
        // https://github.com/privacy-scaling-explorations/sonobe/issues/80
        //
        // 7. check eval_W==p_W(c_W) and eval_E==p_E(c_E)
        // let incircuit_eval_W = evaluate_gadget::<CF1<C1>>(W_i1.W, incircuit_c_W)?;
        // let incircuit_eval_E = evaluate_gadget::<CF1<C1>>(W_i1.E, incircuit_c_E)?;
        // incircuit_eval_W.enforce_equal(&eval_W)?;
        // incircuit_eval_E.enforce_equal(&eval_E)?;

        // 14. (8.b) check the NIFS.V challenge matches the 
		// one from the public input (so we
        // avoid the verifier computing it)
        let r_Fr = Boolean::le_bits_to_fp_var(&r_bits)?;
        // check that the in-circuit computed r is equal to the inputted r
        let r =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || 
				Ok(self.r.unwrap_or_else(CF1::<C1>::zero)))?;
        r_Fr.enforce_equal(&r)?;

		println!("DEBUG USE 9101.2: public_input: {}", cs.num_instance_variables());

		//15. Added check z_i is well-formed (and in-particular) its
		//r matches kzg_c_lkup, and its sum_lk_col1, sum_lk_col2 matches
		//the value of eval_lkup_col1, eval_lkup_col2 retrieved from
		//the public input
		let vec_zi:Vec<C1::ScalarField> = 
			self.zi_part2_inst.expect("zi_part2_inst null!").to_vec();
		let vec_zi_var = vec_zi.iter().map(|f| 
			FpVar::<C1::ScalarField>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<C1::ScalarField>>>();
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_part2_inst_var = ZiPartTwoInstVar::from_vec(&vec_zi_var, fq_bits);
		let zi_p2 = zi_part2_inst_var.hash(&self.poseidon_config, cs.clone());
		//println!("DEBUG USE 702: generated zi_part2: {}, zi_part2 in input: {}", zi_p2.value()?, z_i[1].value()?); 

		panic!("STOP AND FIX HERE 3191");
		zi_part2_inst_var.ch.enforce_equal(&kzg_c_lkup);
		//zi_part2_inst_var.sum_kzg_eval.enforce_equal(&eval_lkup_col1);
		//zi_part2_inst_var.total_word_len.enforce_equal(&eval_lkup_col2);
		//zi_part2_inst_var.accumulated_word_len.enforce_equal(&eval_lkup_col2);


        Ok(())
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
    if !v.len().is_power_of_two() {
        return Err(SynthesisError::Unsatisfiable);
    }
	let mut eval = FpVar::<F>::zero();
	let mut prod = FpVar::<F>::one();
	for i in 0..v.len(){
		let item = &v[i] * &prod;
		eval = &eval + &item;
		prod = &prod * &point;
		if i%1024==0{
			eval = &eval * &one;
		}
	}
	Ok(eval)
}

/// Gadget that computes the KZG challenges, also offers the rust native implementation compatible
/// with the gadget.
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
    pub fn get_challenges_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        U_i: CommittedInstanceFoldPotSuper<C>,
    ) -> (C::ScalarField, C::ScalarField, C::ScalarField) {
        // compute the KZG challenges, which are computed in-circuit and checked that it matches
        // the inputted one
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmW);
		}
        let challenge_W = transcript.get_challenge();
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmE);
		}
        let challenge_E = transcript.get_challenge();
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb_nonnative(&U_i.vec_inst[i].cmF);
		}
        let challenge_F = transcript.get_challenge();

        (challenge_W, challenge_E, challenge_F)
    }

    // compatible with the native get_challenges_native
    pub fn get_challenges_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        U_i: CommittedInstanceVarFoldPotSuper<C>,
    ) -> Result<(FpVar<C::ScalarField>, FpVar<C::ScalarField>, FpVar<C::ScalarField>), SynthesisError> {
		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmW.to_constraint_field()?)?;
		}
        let challenge_W = transcript.get_challenge()?;

		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmE.to_constraint_field()?)?;
		}
        let challenge_E = transcript.get_challenge()?;

		for i in 0..U_i.vec_inst.len(){
        	transcript.absorb(&U_i.vec_inst[i].cmF.to_constraint_field()?)?;
		}
        let challenge_F = transcript.get_challenge()?;

        Ok((challenge_W, challenge_E, challenge_F))
    }
}

/// Circuit that implements the in-circuit checks for the two phase
/// Scheme. In fact, it employs two instances of DeciderEthCircuitSuper,
/// and pass the cyclepair_input in between to make sure that
/// they are consistent.
#[derive(Clone, Debug)]
pub struct TwoPhaseDeciderEthCircuitSuper<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool = false>
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

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
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

	poseidon_config: PoseidonConfig<C1::ScalarField>, 

	/// circuit 1 for nova1
	circ1:  Phase1Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,H>,
	/// circuit 2 for nova2
	circ2:  DeciderEthCircuitSuper<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,H>,
	/// cyclepair_inputs (consistency needs to be checked about it between
	/// nova1 and nova2
	cyclepair_inputs: Vec<Vec<C1::ScalarField>>,
	/// hash of the qa_nizk_vkey
	qa_nizk_vkey_hash: C1::ScalarField,

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool> TwoPhaseDeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, H>
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

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. Basically,
	/// it builds two decider circuits, one for each nova,
	/// and builds up the checks to verify the consistency among the
	/// non-deterministic advice.
    pub fn from_nova<
	FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
		>
		(
        nova1: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, H>,
        nova2: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, SigmaIR1CS_Inst<C1::ScalarField, C1, CS1,LK, false>, CS1, CS2, CS1E, LK, H>,

		cyclepair_inputs: Vec<Vec<C1::ScalarField>>,
		qa_nizk_vkey_hash: C1::ScalarField,
		poseidon_config: PoseidonConfig<C1::ScalarField>,
		com_all_w: C1
    ) -> Result<Self, Error> {
		unimplemented!()
	/*
		let circ1 = Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,H>::from_nova::<FC>(nova1, com_all_w)?;
		let circ2 = DeciderEthCircuitSuper::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,H>::from_nova::<SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, false>>(nova2)?;
		Ok( Self{ 
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
			circ1, circ2, cyclepair_inputs, qa_nizk_vkey_hash, poseidon_config
			} )
			*/
    }

	/// generate FpVar version of cyclepair_inputs and the final result
	fn gen_shared_input(&self, cs: ConstraintSystemRef<CF1<C1>>)->(Vec<Vec<FpVar<C1::ScalarField>>>, FpVar<C1::ScalarField>){
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
		for row in cyclepair_inputs_var{
			//each row has 164 elements (gt1, a, b, gt2)
			//a has 3 elements and starts at idx 12
			let a = row[12*5..12*5+3*5].to_vec();
			let b = row[15*5..20*5].to_vec();
			hc_a = compute_hc_var(&self.poseidon_config, &hc_a, &a, cs.clone());
			hc_b = compute_hc_var(&self.poseidon_config, &hc_b, &b, cs.clone());
		}
		let final_result = hash_var(&self.poseidon_config, &vec![hc_a, hc_b], 
			cs.clone()); 
		unimplemented!()
	}

    pub fn generate_constraints_adv(&mut self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		//1. generate the shared input so that the two subcircuits
		// will be consistent (regarding cyclepair_input)
		let (cyclepair_inputs_var, final_result_var) = self.gen_shared_input(cs.clone());

		unimplemented!()
	}

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, const H: bool> ConstraintSynthesizer<CF1<C1>> for TwoPhaseDeciderEthCircuitSuper<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, H>
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

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		//1. generate the shared input so that the two subcircuits
		// will be consistent (regarding cyclepair_input)
		let (cyclepair_inputs_var, final_result_var) = self.gen_shared_input(cs.clone());
		let (v2d_coms, _) = self.circ1.generate_constraints_adv(cs.clone()).unwrap();
		let (_, final_result) = self.circ2.generate_constraints_adv(cs.clone()).unwrap();

		//2. enforce the consistency of cyclepair_inputs_var and final_results_var
		unimplemented!()
	}
}


#[cfg(test)]
pub mod tests_decider_eth_circuit_super {
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
	use ark_groth16::Groth16;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective,
		G2Projective as ProjectiveG2, constraints::PairingVar as PairingVar};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::arith::{
        r1cs::{
            tests::{get_test_r1cs, get_test_z},
            {extract_r1cs, extract_w_x},
        },
        Arith,
    };
    use crate::commitment::{pedersen::Pedersen, kzg::KZG};
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::tests::{CubicFCircuit, CustomFCircuit, WrapperCircuit};
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;
    use crate::folding::foldpot::{
		PreprocessorParamFoldPot,
		sigma_ir1cs::{SigmaIR1CS_Inst,StatementInst,ZiPartTwoInst},
		sigma_cyclepair::{create_sigma_fold_pair},
		sigma_ir1cs::tests::{SixRootMapper, gen_six_root},
		//decider_eth::{DeciderFoldPot},
		driver::{
			Driver,
			tests_driver::SumMapper
		},
		decider_eth_circuit_super::{KZGChallengesGadgetSuper},
	};
	use std::{rc::Rc, cell::RefCell};

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
    	use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
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
		evalVar2.enforce_equal(&evalVar);
        assert!(cs.is_satisfied().unwrap());
    }

}

