use std::sync::Arc;
/* Created 09/15/2024. Adaptation for super_nova 
   Changed 01/09/2025. Add TwoPhaseDeciderCircuit to accomodate to
   	the two phase cyclepair strategy.
   Changed 02/17/2026. Add MainCircuit as a wrapper of Phase1Circuit
   	and rename TwoPhaseDeciderCircuit as CyclePairCircuit
*/

/// This file implements the onchain (Ethereum's EVM) decider circuit. 
/// For non-ethereum use cases,
/// other more efficient approaches can be used.
use utils::{logger::{log_perf, emit_stdout, LOG2, LOG3}, timer::Timer as GTimer};
use std::fmt::{Debug};
use itertools::Itertools;
//use ark_ec::AffineRepr;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group, pairing::Pairing, short_weierstrass::SWCurveConfig};
use ark_ff::{PrimeField, Field, ToConstraintField, BigInteger};
use ark_crypto_primitives::sponge::constraints::AbsorbGadget;
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
use ark_std::{Zero,UniformRand};
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::foldpot::from_field::{AffineFromField};
use crate::transcript::AbsorbNonNativeGadget;
use crate::folding::{
	foldpot::{
		CommittedInstanceFoldPot, WitnessFoldPot, 
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,ZiPartTwoInstVar,GadgetMapper,cp_g0},
		circuits::{CommittedInstanceVarFoldPot},
		//decider_eth_circuit::{RelaxedR1CSGadget, R1CSVar,WitnessVarFoldPot,CycleFoldWitnessVar},
		mod_super::{WitnessFoldPotSuper,CommittedInstanceFoldPotSuper, FoldPotSuper},
		circuits_super::{field_to_usize,CommittedInstanceVarFoldPotSuper},
		sigma_cyclepair::{compute_hc_var},
		utils::{get_mem_usage,f1_limbs_to_f2, B_DEBUG, B_DEBUG2, B_DEBUG3, new_var, check_cs,
			LOG_MAX_STEPS,
			gadget_sat_check, gadget_sat_on}, //DEBUG USE 69801: +gadget_sat_check +.11 gate
		container_config::ColEle,
	},
};
use crate::arith::r1cs::R1CS;
use crate::utils::vec::SparseMatrix; //ALL_T1014
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::{
    nonnative::{affine::NonNativeAffineVar, uint::{LimbVar, NonNativeUintVar}}, //ALL_T1016: +LimbVar
    CF1, CF2,CF3,
};
use num_bigint::BigUint; //ALL_T1016
use std::cmp::max; //ALL_T1016
use crate::folding::{
	nova::{CommittedInstance, Witness},
};
use crate::frontend::FCircuit;
use crate::transcript::Transcript;
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
        //ALL_T1010: same relation, one constraint per row (was product + equality).
        if Az.len() != Bz.len() || Az.len() != uCzE.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for ((a, b), c) in Az.iter().zip(Bz.iter()).zip(uCzE.iter()) {
            a.mul_equals(b, c)?;
        }
        Ok(())
    }

    /// performs the RelaxedR1CS check for non-native variables (Az∘Bz==uCz+E)
    //ALL_T1016 (P8): same relation, cheaper congruence, via a signed split.
    //Idea. The values are BN254 base-field (q) integers held in 55-bit limbs,
    //and a row check proves L - R = k q over the integers. Its cost grows with
    //the bit bounds of L and R. A coefficient -c is stored as q - c, a 254-bit
    //value whose constant limbs get full-width bounds (about 256 bits). About
    //half of the cp coefficients are such small negatives, so today the row
    //bounds reach 1,033 bits. Split each constant matrix
    //M = M+ - M- (mod q) with small nonnegative M+, M- and move the minus terms
    //to the other side:
    //  (A+z)(B+z) + (A-z)(B-z) + u(C-z) == (A+z)(B-z) + (A-z)(B+z) + u(C+z) + E.
    //Left minus right is (A+ - A-)z (B+ - B-)z - u(C+ - C-)z - E, which is
    //Az o Bz - u Cz - E mod q, so the check is the same relation.
    //Example: the row A = [1, q - 1] (that is [1, -1]) becomes A+ = [1, 0] and
    //A- = [0, 1], 1-bit coefficients instead of 254-bit ones.
    //Effect on the cp R1CS: max bound 1,033 -> 777 bits, 3,453 -> 540
    //constraints per row (Step 10 52.4M -> 8.2M).
    //Bounds are COMPUTED FROM KNOWN CONSTANTS, never from witness values: the
    //matrix coefficients are circuit constants fixed at setup, and the witness
    //limbs only enter through their range-check widths.
    //Bounds. Every limb carries a static upper bound ub (LimbVar::ub). Witness
    //limbs of z, E, u are range checked at allocation (ub = 2^55 - 1, or 2^36 - 1
    //for the top limb). Constants get their exact value (constant_exact). add and
    //mul propagate ub1 + ub2 and sum ub1 ub2 and refuse any limb bound at or above
    //(r - 1)/2, r the native field order, so no limb wraps around r. The bounds
    //depend only on the circuit structure and the constant matrices, never on the
    //witness: they hold for every prover and are the same in setup and prove. For
    //any A, B, C the circuit is either built with true bounds (sound) or synthesis
    //stops at an assert. Only the cost depends on how small the coefficients are.
    pub fn check_nonnative<F: PrimeField, CF: PrimeField>(
        r1cs: R1CSVar<F, CF, NonNativeUintVar<CF>>,
        E: Vec<NonNativeUintVar<CF>>,
        u: NonNativeUintVar<CF>,
        z: Vec<NonNativeUintVar<CF>>,
    ) -> Result<(), SynthesisError> {
        //Shape check. The old code got this from mul_vector and hadamard. The
        //row loop below indexes E, ap, bp, ... by row, so a mismatch must stop
        //synthesis instead of silently checking fewer rows.
        let R1CSVar { A, B, C, .. } = r1cs;
        if [A.n_rows, B.n_rows, C.n_rows] != [E.len(); 3] || [A.n_cols, B.n_cols, C.n_cols] != [z.len(); 3] {
            return Err(SynthesisError::Unsatisfiable);
        }
        let [ap, an] = signed_mul_vector(A, &z)?;
        let [bp, bn] = signed_mul_vector(B, &z)?;
        let [cp, cn] = signed_mul_vector(C, &z)?;
        //One congruence per row i. Both sides are sums of nonnegative terms, so
        //their integer bounds are the sums of the term bounds and no side can
        //go negative. l holds the terms that carry a plus sign in
        //Az o Bz - u Cz, r holds the minus terms and E. Then l - r equals
        //Az o Bz - u Cz - E mod q, and enforce_congruent proves l - r = k q over
        //the integers, so the row holds mod q. The cost of that proof grows with
        //max(bits(ub(l)), bits(ub(r))), which is what the split shrinks.
        for (i, e) in E.iter().enumerate() {
            let l = sum_of_products(&[(&ap[i], &bp[i]), (&an[i], &bn[i]), (&u, &cn[i])])?;
            let r = sum_of_products(&[(&ap[i], &bn[i]), (&an[i], &bp[i]), (&u, &cp[i])])?.add_no_align(e);
            enforce_congruent_same_len::<F, CF>(r, l)?;
        }
        Ok(())
    }
}

/// ALL_T1016: a sparse matrix of non-native constants.
type NNMatrix<F, CF> = SparseMatrixVar<F, CF, NonNativeUintVar<CF>>;

/// ALL_T1016: (M+ z, M- z) for the signed split of the constant matrix M.
/// Each product is computed over the integers, without reduction mod q. Its
/// limb bounds are sum over the row of (exact coefficient) x (range-check
/// bound of z_j), so they depend only on the matrix constants and on the
/// widths z was range checked to, not on the value of z.
fn signed_mul_vector<F: PrimeField, CF: PrimeField>(
    m: NNMatrix<F, CF>, z: &[NonNativeUintVar<CF>],
) -> Result<[Vec<NonNativeUintVar<CF>>; 2], SynthesisError> {
    let [p, n] = split_signed(m);
    Ok([p.mul_vector(z)?, n.mul_vector(z)?])
}

/// ALL_T1016: split a constant matrix into exact-bound parts [M+, M-] with
/// M+ - M- == M (mod |F|) entrywise. Each entry lands on exactly one side (the
/// other side gets 0), so the identity holds for every entry whatever its value.
/// The parts are built with constant_exact, so their bounds are the true values.
fn split_signed<F: PrimeField, CF: PrimeField>(mut m: NNMatrix<F, CF>) -> [NNMatrix<F, CF>; 2] {
    let rows = std::mem::take(&mut m.coeffs); // drops the full-width constants row by row
    let mut parts = [m.clone(), m];
    for row in rows {
        let mut halves = [vec![], vec![]];
        for (c, j) in row {
            let (side, v) = signed_part::<F, CF>(&c);
            halves[side].push((NonNativeUintVar::constant_exact(&v), j));
        }
        for (p, h) in parts.iter_mut().zip(halves) {
            p.coeffs.push(h);
        }
    }
    parts
}

/// ALL_T1016: side (0 = plus with c, 1 = minus with |F| - c) of an R1CS
/// constant c, whichever value is shorter. For c = q - 1 (that is -1) this
/// gives (1, 1): a 1-bit coefficient on the minus side instead of a 254-bit one.
/// min(c, q - c) is never larger than the full width, so no bound gets worse.
fn signed_part<F: PrimeField, CF: PrimeField>(c: &NonNativeUintVar<CF>) -> (usize, BigUint) {
    use ark_r1cs_std::R1CSVar as _; // is_constant and value (this file has its own R1CSVar)
    assert!(c.is_constant(), "ALL_T1016: R1CS coefficients must be constants");
    let (q, c): (BigUint, BigUint) = (F::MODULUS.into(), c.value().unwrap());
    let neg = &q - &c;
    if neg.bits() < c.bits() { (1, neg) } else { (0, c) }
}

/// ALL_T1016: sum of x_k * y_k over the integers (no reduction).
/// The bound of the result is the sum of the products of the operand bounds
/// (mul_no_align and add_no_align propagate ub). No reduction is done here,
/// since the single congruence check at the end of the row covers it.
fn sum_of_products<CF: PrimeField>(
    pairs: &[(&NonNativeUintVar<CF>, &NonNativeUintVar<CF>)],
) -> Result<NonNativeUintVar<CF>, SynthesisError> {
    pairs.iter().try_fold(NonNativeUintVar(vec![]), |s, (x, y)| Ok(s.add_no_align(&x.mul_no_align(y)?)))
}

/// ALL_T1016: x == y (mod |M|), both padded with zero limbs to one length, so
/// enforce_equal_unaligned never takes its self-longer branch. x must hold a witness.
/// Zero limbs are constants with bound 0, so padding adds no constraint and
/// changes no bound.
fn enforce_congruent_same_len<M: PrimeField, CF: PrimeField>(
    mut x: NonNativeUintVar<CF>, mut y: NonNativeUintVar<CF>,
) -> Result<(), SynthesisError> {
    let n = max(x.0.len(), y.0.len());
    x.0.resize(n, LimbVar::zero());
    y.0.resize(n, LimbVar::zero());
    x.enforce_congruent::<M>(&y)
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

impl<C> CycleFoldWitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    //ALL_T1011 P2(a): same allocation (order E, rE, W, rW, same constraints)
    //as new_witness, also returning the range-check bits of E and W for the
    //Pedersen checks, instead of a second bit decomposition.
    pub fn new_witness_with_bits(
        cs: impl Into<Namespace<CF2<C>>>,
        w: &Witness<C>,
    ) -> Result<(Self, Vec<Vec<Boolean<CF2<C>>>>, Vec<Vec<Boolean<CF2<C>>>>), SynthesisError> {
        let cs = cs.into().cs();
        let many = |v: &[C::ScalarField]| -> Result<(Vec<_>, Vec<_>), SynthesisError> {
            Ok(v.iter()
                .map(|x| NonNativeUintVar::new_variable_with_bits(cs.clone(), || Ok(*x), AllocationMode::Witness))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .unzip())
        };
        let (E, E_bits) = many(&w.E)?;
        let rE = NonNativeUintVar::new_witness(cs.clone(), || Ok(w.rE))?;
        let (W, W_bits) = many(&w.W)?;
        let rW = NonNativeUintVar::new_witness(cs.clone(), || Ok(w.rW))?;
        Ok((Self { E, rE, W, rW }, E_bits, W_bits))
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

/// This corresponds to Phase1CircuitRet 
#[derive(Clone, Debug, PartialEq)]
pub struct Phase1CircuitRetVal<F: PrimeField,C: CurveGroup<ScalarField=F>>{
	/// the ch (challenge)
	pub ch: F,
	/// the rc (combination)
	pub rc: F,
	/// the final cmF hash-chain value z_n[0] (S107 FS-seed pin)
	pub hash_cmF: F,
	/// kzg_sum: sum_kzg_eval_lk + sum_kzg_eval_word + sum_kzg_eval_others
	pub kzg_sum: F,
	/// rows of [com_all_w, (comW, comE, comF)] for all vec_inst of U_{i+1}
	pub vec_coms: Vec<C>,
	/// the final result of the last zi_part2_inst
	pub final_result: F,
	/// the u_i instance (last)
	pub u_i: CommittedInstanceFoldPot<C>,

	/// the challene used for evaluating all_W, all_E of circuit 1
	/// NOTE that this kzg is for the decider circuit, as 
	/// W and E are NOT available after the Fiat-Shamir randoms are put in
	/// So it's different from the kzg_sum in the above section for
	/// fixed memory.
	pub kzg_all_com_ch: F,
	/// the evaluation result of com_all_w_e
	pub eval_w_e: F,

	/// the cmE of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmE: C,
	/// the cmW of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmW: C,
	/// the cmF of U_i1[0] (only used for phase 2 circuit
	pub u_i1_0_cmF: C,

	/// a randf which allows generate a random hash for the same
	/// data
	pub randf: F,
}

/// Packs the wires returned by Phase1Circuit (most info
/// retrieved from the ZiPartTwo of the last running instance),
/// the vec_coms retrieved from U_i1's all instances.
/// NOTE that the ret (even though) has a lot of data members,
/// does not increase the total number of constraints
#[derive(Clone, Debug)]
pub struct Phase1CircuitRet<F:PrimeField, C: CurveGroup<ScalarField=F>>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig,
	 <C as Group>::ScalarField: Absorb,
	 C::Affine: AffineFromField<C::BaseField>,
{
	/// the ch (challenge)
	pub ch: FpVar<F>,
	/// the rc (combination)
	pub rc: FpVar<F>,
	/// the final cmF hash-chain value z_n[0] (S107 FS-seed pin)
	pub hash_cmF: FpVar<F>,
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

	/// a randf which allows generate a random hash for the same
	/// data
	pub randf: FpVar<F>,

	/// T931 P2: (z_n.hc_a_out, z_n.hc_b_out), full mode only. Not in
	/// Phase1CircuitRetVal or to_vec, so mainres_hash is unchanged.
	pub cp_hc_out: Option<(FpVar<F>, FpVar<F>)>,
	/// T933 K2-min: z_n.total_words, the main decider's public input 2.
	pub total_words: Option<FpVar<F>>,
}

impl <F:PrimeField, C: CurveGroup<ScalarField=F>> Phase1CircuitRet<F,C>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig,
	 <C as Group>::ScalarField: Absorb,
	 C::Affine: AffineFromField<C::BaseField>,
{
	pub fn dummy(cs: ConstraintSystemRef<F>)->Self{
		let zvar = FpVar::<F>::new_witness(cs.clone(), 
			|| Ok(F::zero())).expect("create fpvar error");
		let avar = NonNativeAffineVar::<C>::zero_var(cs.clone());
		let ci = CommittedInstanceFoldPot::<C>::dummy(2);
		let randf = FpVar::<F>::new_witness(cs.clone(), 
			|| Ok(F::zero())).expect("create fpvar error");
		Self{
			ch: zvar.clone(),
			rc: zvar.clone(),
			hash_cmF: zvar.clone(),
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

			randf,
			cp_hc_out: None,
			total_words: None,
		}
	}

	pub fn from(val: &Phase1CircuitRetVal<F,C>, cs: &ConstraintSystemRef<F>)
	->Self{
		let b_debug = B_DEBUG;
		let res = Self{
			ch: new_var(cs, val.ch),
			rc: new_var(cs, val.rc),
			hash_cmF: new_var(cs, val.hash_cmF),
			kzg_sum: new_var(cs, val.kzg_sum),
			vec_coms: val.vec_coms.iter().map(|c|{
				NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(c),
					AllocationMode::Witness).unwrap()	
			}).collect::<Vec<NonNativeAffineVar<C>>>(),
			final_result: new_var(cs, val.final_result),
			u_i: CommittedInstanceVarFoldPot::<C>::new_variable(cs.clone(),
				|| Ok(val.u_i.clone()), AllocationMode::Witness).unwrap(),
			kzg_all_com_ch: new_var(cs, val.kzg_all_com_ch),
			eval_w_e: new_var(cs, val.eval_w_e),
			u_i1_0_cmE: NonNativeAffineVar::<C>::new_variable(cs.clone(), ||
				Ok(val.u_i1_0_cmE), AllocationMode::Witness).unwrap(),
			u_i1_0_cmW: NonNativeAffineVar::<C>::new_variable(cs.clone(), ||
				Ok(val.u_i1_0_cmW), AllocationMode::Witness).unwrap(),
			u_i1_0_cmF: NonNativeAffineVar::<C>::new_variable(cs.clone(), ||
				Ok(val.u_i1_0_cmF), AllocationMode::Witness).unwrap(),
			randf: new_var(cs, val.randf),
			cp_hc_out: None,
			total_words: None,
		};
		if b_debug{
			use ark_r1cs_std::R1CSVar;
			if res.ch.value().is_ok(){
				let res2 = res.val();
				assert!(*val==res2);
			}
		}

		res
	}

	pub fn val(&self)->Phase1CircuitRetVal<F,C>{
		use ark_r1cs_std::R1CSVar;
		Phase1CircuitRetVal{
			ch: self.ch.value().unwrap(),
			rc: self.rc.value().unwrap(),
			hash_cmF: self.hash_cmF.value().unwrap(),
			kzg_sum: self.kzg_sum.value().unwrap(),
			vec_coms: self.vec_coms.iter().map(|c|{
				let x: C::BaseField = c.x.value().unwrap().into();
				let y: C::BaseField  = c.y.value().unwrap().into();
				let pt = C::Affine::from_fields(x,y);
				pt.into()
		    }).collect::<Vec<C>>(),
			final_result: self.final_result.value().unwrap(),
			u_i: self.u_i.value(),
			kzg_all_com_ch: self.kzg_all_com_ch.value().unwrap(),
			eval_w_e: self.eval_w_e.value().unwrap(),
			u_i1_0_cmE: self.u_i1_0_cmE.value(),	
			u_i1_0_cmW: self.u_i1_0_cmW.value(),	
			u_i1_0_cmF: self.u_i1_0_cmF.value(),	
			randf: self.randf.value().unwrap(),	
		}
	}

	/// serialize to a vec of FpVar
	pub fn to_vec(&self)->Vec<FpVar<F>>{
		let res = vec![
			vec![self.ch.clone(), self.rc.clone(),
				self.hash_cmF.clone(), self.kzg_sum.clone()],
			self.vec_coms.iter().map(|c|{
				c.to_native_sponge_field_elements().unwrap()
			}).flatten().collect::<Vec<_>>(),
			vec![self.final_result.clone()],
			self.u_i.to_sponge_field_elements().unwrap(),
			vec![self.kzg_all_com_ch.clone(), self.eval_w_e.clone()],
			// NO need to hash u_i1_0_cmE, cmW, and cmF as we 
			// don't really use the hash() function for Phase2Circ
			// We only use the Main circ where these 3 elements are not used
			vec![self.randf.clone()]	
				
		].concat();
		res
	}

	/// hash the Phase1Ret structure
	pub fn hash(&self, ps_cfg: &PoseidonConfig<F>, cs: ConstraintSystemRef<F>)->FpVar<F>{
        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), ps_cfg);
		let vec = self.to_vec();
		sponge.absorb(&vec).expect("absort err");
		let res=sponge.squeeze_field_elements(1).expect("hash err")[0].clone();
		res
	}
}

/// Packs the wires returned by Phase2Circuit 
pub struct Phase2CircuitRet<F:PrimeField, C: CurveGroup<ScalarField=F>>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig,
	 <C as Group>::ScalarField: Absorb,
	 C::Affine: AffineFromField<C::BaseField>{
	pub hashchain_b: FpVar<F>,
	pub main_ret: Phase1CircuitRet<F, C>,
}

impl <F:PrimeField, C: CurveGroup<ScalarField=F>> Phase2CircuitRet<F,C>
where C::BaseField: PrimeField,
	C::Config: SWCurveConfig,
	 C::Affine: AffineFromField<C::BaseField>,
	 <C as Group>::ScalarField: Absorb{
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
/// (2) kzg_ch = H(tag, com_all_W, D), a witness here (T934: D binds W || E)
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
    pub r1cs: Vec<Arc<R1CS<C1::ScalarField>>>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: Arc<R1CS<C2::ScalarField>>,
	/// R1CS of the CyclePair circuit
	pub cp_r1cs: Arc<R1CS<C2::ScalarField>>,
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
	/// the r_all_w used in generating com_all_w. T933 s9 B3: the
	/// pair (o_1, o_2).
	pub r_all_w: Option<(C1::ScalarField, C1::ScalarField)>,
	/// T934 D2: r_2 (or r'), set once D is known (finalize / set_kzg_ch).
	pub kzg_ch: Option<C1::ScalarField>,

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

	pub job_id: usize,
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
		 r_all_w: (C1::ScalarField, C1::ScalarField)) -> Result<Self, Error> {
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
            cf_pedersen_params: (*nova.cf_cs_pp).clone(),
            cp_pedersen_params: (*nova.cp_cs_pp).clone(),
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
			kzg_ch: None,

			b_full_mode: nova.b_full_mode,
			job_id: nova.job_id,

        })
    }

	/// T934: the KZG vector [W_1..W_k, E_1..E_k, o_1, o_2] (s9 order).
	/// ALL_T1014: Groth16 commits cp_w() instead.
	pub fn all_w(&self) -> Vec<C1::ScalarField> {
		let w = &self.W_i1.as_ref().expect("W_i1 null").vec_wit;
		let (o1, o2) = self.r_all_w.expect("r_all_w null");
		w.iter().flat_map(|x| x.W.iter()).chain(w.iter().flat_map(|x| x.E.iter()))
			.copied().chain([o1, o2]).collect()
	}

	/// ALL_T1014: the Groth16 committed range D, every slot rescaled to u = 1.
	pub fn committed_range(&self) -> CommittedRange<C1::ScalarField> {
		let us = &self.U_i1.as_ref().expect("U_i1 null").vec_inst;
		let ws = &self.W_i1.as_ref().expect("W_i1 null").vec_wit;
		let (o1, o2) = self.r_all_w.expect("r_all_w null");
		assert!(us.len() == ws.len() && ws.len() == self.r1cs.len(), "ALL_T1014: slot count");
		let (x, w, e) = self.r1cs.iter().zip(us).zip(ws)
			.map(|((r, i), w)| scaled_slot(r, i.u, &i.x, &w.W, &w.E)).multiunzip();
		CommittedRange{ w, e, o: vec![o1, o2], u: us.iter().map(|i| i.u).collect(), x }
	}

	/// ALL_T1014: D flattened, the cp_commit vector of Stage 1 and Stage 2.
	pub fn cp_w(&self) -> Vec<C1::ScalarField> { self.committed_range().parts().flatten().collect() }

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// also z_n's (hc_a_out, hc_b_out) via cp_hc_out (T931 P2)
    pub fn generate_constraints_adv(&self, _dump_level: usize, cs: ConstraintSystemRef<CF1<C1>>, randf_in: CF1<C1>) -> Result<Phase1CircuitRet<CF1<C1>,C1>, Error> {
    	//1. generate Vector the R1CS var (one for each circuit)
    	let log_level = LOG3;
    	let mut t1 = GTimer::new();
		let mut c1 = cs.num_constraints();
		let c0 = cs.num_constraints();
		let _pc_i_val = field_to_usize(&self.pc_i); //for fold
		let _pc_i1_val = field_to_usize(&self.pc_i1); //for compute next (j)
		// DEBUG USE 69801.11: decider-side matrix dims -- compare with
		// the fold-side .11 line to rule matrix drift in or out.
		// Remove by tag 69801.
		if gadget_sat_on() {
			for (ii, r1) in self.r1cs.iter().enumerate() {
				let nnz = |m: &crate::utils::vec::SparseMatrix<
					C1::ScalarField>| m.coeffs.iter()
					.map(|r| r.len()).sum::<usize>();
				emit_stdout(format!("DEBUG USE 69801.11: decider-side \
					r1cs[{}]: rows={} cols={} l={} nnz_abc={}/{}/{}",
					ii, r1.A.n_rows, r1.A.n_cols, r1.l, nnz(&r1.A),
					nnz(&r1.B), nnz(&r1.C)));
			}
		}
		let pc_i_var = FpVar::new_witness(cs.clone(),  || Ok(self.pc_i))?;
        let vec_r1cs = self.r1cs.iter().map(|r1cs|
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>
			::new_witness(cs.clone(), || {
                Ok(r1cs.clone())
            }).unwrap()).collect::<Vec<
				R1CSVar::<C1::ScalarField,CF1<C1>,FpVar<CF1<C1>>>
			>>();
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 1: generae r1cs_var. INCREASSED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s1"); //DEBUG USE 69801
		if B_DEBUG3 {check_cs(&cs, "phase1 step 1.0");}

		//2. generate Var version of pp_hash, z_0, z_i
		// U_i, u_i, U_i1, given the advice from nova instance
		// NOTE: they are private witness (some vars will be
		// returned to TwoPhaseCircuit for verification), except
		// pp_hash: a constant (T934 K4), so the key fixes it
        let pp_hash = FpVar::<CF1<C1>>::new_constant(cs.clone(),
            self.pp_hash.expect("T934 K4: pp_hash null"))?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || 
			Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self.z_0.clone().unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self.z_i.clone().unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
		let _x_len = if self.b_full_mode {3} else {2};
        let u_dummy_native = CommittedInstanceFoldPot::<C1>::dummy(2);
        let u_i = CommittedInstanceVarFoldPot::<C1>::new_witness(cs.clone(), 
			|| { Ok(self.u_i.clone().unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(cs.clone(), || { Ok(self.U_i.clone().unwrap()) })?;
        let U_i1 = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(
			cs.clone(), || { Ok(self.U_i1.clone().unwrap())
        })?;
		//T934 D1 + ALL_T1014: D is ONE contiguous committed range,
		//tied to U_i1 here, above the !b_light_test gate.
		let d = CommittedRange::alloc(&cs, self.committed_range())?;
		d.bind(&U_i1.vec_inst)?;
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 2: igen Ui, Wi, Ui1, Wi1 witness: INCREASED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s2"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 2.0");}

		//3. compute the KZG challenge in circuit
		let com_all_w = NonNativeAffineVar::<C1>::new_witness(cs.clone(),
			|| Ok(self.com_all_w.expect("com_all null")))?;
		let com_all_w_clone = com_all_w.clone();
		//T934 D2: r_2 = H(tag, C_WE, D) is computed outside, after D.
		let kzg_all_com_ch = FpVar::<CF1<C1>>::new_witness(cs.clone(),
			|| Ok(self.kzg_ch.expect("kzg_ch not set")))?;
		let kzg_all_com_ch_clone= kzg_all_com_ch.clone();
		let len_all_w_e = d.unscaled_len();
		//DEBUG USE 69801.8: all_w_e layout so a step-4 UNSAT row maps
		//to a W (witness) vs E (error) region of a specific circuit.
		if std::env::var("ZKR_MAIN_SNARK_PROBE").is_ok(){
			let lens: Vec<(usize,usize)> = d.w.iter().zip(&d.e)
				.map(|(w, e)| (w.len(), e.len())).collect();
			println!("DEBUG USE 69801.8: all_w_e layout: per-circ \
(W,E) lens {:?}, total {}", lens, len_all_w_e);
		}
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 3: collect all_w_e. len: {}, : INCREASED: {} constraints.", 
			len_all_w_e, cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s3"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 2");}

		let one= FpVar::<C1::ScalarField>::new_witness(cs.clone(),  || 
			Ok(C1::ScalarField::from(1u32)) ).unwrap();
		one.enforce_equal(&FpVar::one())?; //T934 D3 (F1c)
		let eval_w_e = d.eval_unscaled(&kzg_all_com_ch, &one)?; //ALL_T1014
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 4: eval all_w_e. INCREASED {} constrains.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s4"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 3");}

        //4. u_i.cmE==cm(0), u_i.u==1
        // Here zero is the x & y coordinates of the 
		// zero point affine representation.
        let zero = NonNativeUintVar::new_constant(cs.clone(), 
			C1::BaseField::zero())?;
        u_i.cmE.x.enforce_equal_unaligned(&zero)?;
        u_i.cmE.y.enforce_equal_unaligned(&zero)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;
		if B_DEBUG3{check_cs(&cs, "phase1 step 4");}


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
		let mut c_ui1_base = CommittedInstanceVarFoldPotSuper::
				new_constant(cs.clone(), u_dummy)?;
		//hash() absorbs the instance's OWN pc_i (mod_super.rs Absorb), and
		//dummy() leaves it 0. Both other sides patch it to pc_i1 -- the
		//prover at mod_super.rs u_dummy1.pc_i, and the augmented circuit at
		//circuits_super.rs c_ui1_base.pc_i -- so the decider must too.
		//Without this the base-case hash differs whenever pc_i != 0, which
		//is unreachable at n_circ == 1 and always hit at n_circ > 1.
		c_ui1_base.pc_i = pc_i_var.clone();
        let (u_i1_x_base, _) = c_ui1_base.hash(
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
		// T971: SYSTEM-WIDE depth cap 1 <= i <= MAX_STEPS, i.e. i - 1 in
		// LOG_MAX_STEPS bits (18 cs). i stays a private witness.
		let im1 = (self.i.unwrap_or_else(CF1::<C1>::zero)
			- CF1::<C1>::from(1u32)).into_bigint();
		let im1_bits = (0..LOG_MAX_STEPS).map(|k| Boolean::new_witness(
			cs.clone(), || Ok(im1.get_bit(k))))
			.collect::<Result<Vec<_>, _>>()?;
		Boolean::le_bits_to_fp_var(&im1_bits)?.enforce_equal(&i_minus_one)?;
		// REASON: when i (from nova) is 1, we are talking about verifying
		// u_1.x = hash(U_1, ...) where U_1 is really from the dummy case.
        let is_basecase = i_minus_one.is_zero()?;
        (u_i.x[0]).enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i_x)?)?;
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 5: Enforce u_i standard and hash. INCREASED r1cs: {}.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s5"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 5");}

		//6. Added check z_i is well-formed (and in-particular) its
		//r matches kzg_c_lkup, and its sum_lk_col1, sum_lk_col2 matches
		//the value of eval_lkup_col1, eval_lkup_col2 retrieved from
		//the public input
		let zi_part2_inst_var = ZiPartTwoInstVar::from::<C1>(
			&self.zi_part2_inst.clone().expect("zi_part null"), cs.clone());
		let zi_p2 = zi_part2_inst_var.hash(&self.poseidon_config, cs.clone());
		if B_DEBUG2{
			use ark_r1cs_std::R1CSVar;
			if zi_p2.value().is_ok(){//incase circ setup no value
			assert!(zi_p2.value().unwrap()==z_i[1].value().unwrap());
		}}
		zi_p2.enforce_equal(&z_i[1])?;

		//S106 TERMINALITY PIN. The final state must BE terminal:
		//  word_id == total_words, word_id != 0, subseg_id ==
		//  total_word_segs.
		//With the step circuit's b_last now reading the carried
		//total_words (sigma_ir1cs.rs, "S106: b_last compares"), these
		//three clauses are exactly b_last's two conjuncts plus the
		//word_id != 0 that used to sit in final_step -- so pin =>
		//final_step is a syntactic identity at the last step, and the
		//three real checks (I/O, Hab'22, failed-sigs) can no longer be
		//declared away.
		//PLACEMENT IS LOAD-BEARING: this must stay ABOVE the
		//`if !b_light_test` gate below, or every light-mode run skips
		//it and the regression suite reports green while covering
		//nothing.
		zi_part2_inst_var.word_id
			.enforce_equal(&zi_part2_inst_var.total_words)?;
		zi_part2_inst_var.subseg_id
			.enforce_equal(&zi_part2_inst_var.total_word_segs)?;
		zi_part2_inst_var.word_id.is_zero()?
			.enforce_equal(&Boolean::FALSE)?;
		//T932-F2W r1 (G1). The step circuit checks a word's length
		//only at the NEXT word's first step (sigma_ir1cs.rs
		//b_last_full), so the LAST word is unchecked. Pin it on the
		//final state. total_word_len is the copy S106b ties to the
		//first subseg (bound to kzg_length, Horner start of v_n), and
		//accumulated_word_len counts the symbols the circuit
		//processed. Each step's act is at most word_subseg_size
		//(T932 B-R7), so the sum cannot wrap. Read the digest-bound
		//zi_part2_inst_var above,
		//never a second ZiPartTwoInstVar::from, whose fresh witnesses
		//no digest binds. Stage 1 only, since Stage-2 words are
		//cyclepair rows, and so the cp decider stays unchanged. Same
		//placement rule as the S106 pin, above the !b_light_test gate.
		if !self.b_full_mode {
			let zp = &zi_part2_inst_var;
			zp.accumulated_word_len
				.enforce_equal(&zp.total_word_len)?;
		} else {
			//T931 P3: the last row's gt2 is [0]_T, z_n.g == g0 (15 eq).
			//Same placement rule as S106.
			let link = zi_part2_inst_var.cp_link.as_ref().expect("T931: no cp_link");
			let g0 = cp_g0::<E, CF1<C1>, CF2<C1>>();
			assert_eq!(link.g.len(), g0.len(), "T931 P3: z_n.g len != g0 len");
			for (g, g0) in link.g.iter().zip(g0){
				g.enforce_equal(&FpVar::constant(g0))?;
			}
		}

		//S105b: pin z_0[1] to the CANONICAL initial state. Without it
		//the chain S104 builds has no root -- z_0 is a decider witness
		//(:763), so a prover picks the starting accumulators freely and
		//can seed away any deficit. Rebuilding the state here also
		//subsumes S101: alpha = H(rc) and beta = H(rc, alpha) are
		//recomputed in-circuit instead of read from an unbound witness.
		//SCOPE: pins accumulators to zero and alpha/beta to rc.
		//total_words is pinned to the verifier's n_words by the main
		//decider's public input 2 (T933 K2-min).
		{
			let zero_v = FpVar::<CF1<C1>>::zero();
			let mut sp = PoseidonSpongeVar::<CF1<C1>>::new(
				cs.clone(), &self.poseidon_config);
			sp.absorb(&zi_part2_inst_var.rc)?;
			let alpha0 = sp.squeeze_field_elements(1)?[0].clone();
			sp.absorb(&alpha0)?;
			let beta0 = sp.squeeze_field_elements(1)?[0].clone();
			//21 fields, in ZiPartTwoInst::to_vec order. Note indices
			//14,15,16 (word_id, subseg_id, total_word_segs) are THREE
			//zeros before total_words -- an off-by-one here yields a
			//wrong digest and breaks every honest proof.
			//S102/F4: indices 19,20 are batch_r and batch_v, both zero
			//in z_0 (see ZiPartTwoInst::new).
			let v_fixed = vec![
				zi_part2_inst_var.ch.clone(),
				zi_part2_inst_var.rc.clone(),
				zero_v.clone(), zero_v.clone(),
				alpha0, beta0,
				zero_v.clone(), zero_v.clone(),
				zero_v.clone(), zero_v.clone(),
				zero_v.clone(), zero_v.clone(),
				zero_v.clone(), zero_v.clone(),
				zero_v.clone(), zero_v.clone(), zero_v.clone(),
				zi_part2_inst_var.total_words.clone(),
				zero_v.clone(),
				//S102/F4: batch_r, batch_v -- zero in z_0.
				zero_v.clone(), zero_v.clone(),
			];
			//T931 H6: full mode appends z_0's CpLink (hc_out = 0 and g0,
			//see ZiPartTwoInst::new), one plain hash like ZiPartTwoInst::
			//hash. Branch on the mode, never on the native length.
			let mut v_z0 = v_fixed;
			if self.b_full_mode {
				assert_eq!(self.zi_part2_inst.as_ref().expect("zi_part null")
					.to_vec().len(), 38, "T931: full-mode state is not 38 fields");
				v_z0.extend([zero_v.clone(), zero_v.clone()]);
				v_z0.extend(cp_g0::<E, CF1<C1>, CF2<C1>>().into_iter()
					.map(FpVar::constant));
			}
			let z0_hash = ZiPartTwoInstVar::<CF1<C1>>::hash_slice(
				&self.poseidon_config, cs.clone(), &v_z0);
			z0_hash.enforce_equal(&z_0[1])?;
			//T934 K3: the rest of z_0 (chain seed z_0[0], cmF limbs
			//z_0[2..]) is honest 0. z_0[0] is not in zi_part2, so the
			//digest above cannot cover it.
			z_0[0].enforce_equal(&zero_v)?;
			for k in 2..z_0.len(){ z_0[k].enforce_equal(&zero_v)?; }
		}
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 6: verify zi_part2. INCREASED r1cs: {}, memory usage: {}.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s6"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 6");}


        //7. check RelaxedR1CS of U_{i+1} for each circuit
		let n_circ = field_to_usize(&self.n_circ);
		for i in 0..n_circ{
			d.check_slot(i, vec_r1cs[i].clone())?; //ALL_T1014: rescaled, 1 cs per row
		}
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 7: check {} circs. INCREASED r1cs: {}", self.n_circ, cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		gadget_sat_check(&cs, "decider::p1s7"); //DEBUG USE 69801
		if B_DEBUG3{check_cs(&cs, "phase1 step 7");}

		//T935 C3: pc_i in [0, n_circ), every n_circ. One selector per
		//slot over a CONSTANT index (see S103b), shared by 7b and step 8.
		//Stays ABOVE the !b_light_test gate, like 7b.
		let b_sel_vec = (0..n_circ).map(|j| FpVar::<CF1<C1>>::new_constant(cs.clone(),
			C1::ScalarField::from(j as u32))?.is_eq(&pc_i_var))
			.collect::<Result<Vec<_>, _>>()?;
		let mut sel_sum = FpVar::<CF1<C1>>::zero();
		for b in &b_sel_vec { sel_sum += FpVar::from(b.clone()); }
		sel_sum.enforce_equal(&FpVar::one())?;

		//7b. S103: bind the INACTIVE accumulator slots. Step 7 above
		//proves each U_i1[j] is INDIVIDUALLY valid; step 8 below proves
		//only U_i1[pc_i] = NIFS.V(U_i[pc_i], u_i, cmT). Neither ties
		//U_i1[j] to U_i[j] for j != pc_i, so without this a prover swaps
		//a valid-but-unrelated instance into an inactive slot and
		//discards everything ever folded into that rung. Second half of
		//the paper's Step 13(v). The native IVC verifier checks the
		//right vector already -- it checks U_i, which u_i.x[0] binds
		//(mod_super.rs verify step 6).
		//PLACEMENT IS LOAD-BEARING: this stays ABOVE the !b_light_test
		//gate below, or light-mode runs skip it and the suite reports
		//green over nothing. It needs nothing that gate computes.
		//CONSTANTS, not witnesses, for the index: as a witness the
		//prover picks fp_j != pc_i freely, forcing b_inact FALSE at
		//every j, and conditional_enforce_equal then emits rows that are
		//all VACUOUS. circuits_super.rs:734,787 uses constants for the
		//same reason.
		//FIELD BY FIELD, not CommittedInstanceVarFoldPot::enforce_equal
		//(circuits.rs:212): that helper pins only u and x -- its
		//cmE/cmW/cmF compare is a native assert under B_DEBUG=false.
		//cmW is what carries the accumulated witness, so it must be
		//compared here explicitly.
		//SCOPE: this closes n_circ-1 slots. The ACTIVE slot keeps the
		//same hole, because step 8 drops the commitment fold for the
		//very same reason (circuits.rs:223-224) and pc_i is a free
		//witness, so the prover names the victim rung. That is S126,
		//tracked separately -- do not read this block as closing it.
		//Honest satisfiability is STRUCTURAL, not incidental: the
		//prover builds U_i1 as U_i.clone() with only slot pc_i replaced
		//(mod_super.rs gen_next_folded), and from_nova ships that same
		//pair, so inactive slots are limb-identical clones.
		if n_circ > 1 {
			for j in 0..n_circ{
				let b_inact = b_sel_vec[j].not();
				let (a, b) = (&U_i1.vec_inst[j], &U_i.vec_inst[j]);
				assert_eq!(a.x.len(), b.x.len(),
					"S103: U_i1[{}].x len {} != U_i[{}].x len {}",
					j, a.x.len(), j, b.x.len());
				a.u.conditional_enforce_equal(&b.u, &b_inact)?;
				for k in 0..a.x.len(){
					a.x[k].conditional_enforce_equal(&b.x[k], &b_inact)?;
				}
				a.cmE.conditional_enforce_equal(&b.cmE, &b_inact)?;
				a.cmW.conditional_enforce_equal(&b.cmW, &b_inact)?;
				a.cmF.conditional_enforce_equal(&b.cmF, &b_inact)?;
			}
			//count says n_circ, not n_circ-1: the loop is uniform over
			//every slot so the R1CS cannot depend on pc_i's VALUE, and
			//the active slot's rows are the vacuous ones.
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 7b: S103 bind inactive slots, {} slots swept. INCREASED r1cs: {}", n_circ, cs.num_constraints()-c1), &mut t1);
			c1 = cs.num_constraints();
			gadget_sat_check(&cs, "decider::p1s7b"); //DEBUG USE 69801
		}

		//S107: bind the LAST step's absorbed cmF limbs (z_i[2..6])
		//to the folded commitment u_i.cmF. i >= 1 always holds for
		//a completed fold, so no basecase gate.
		//PLACEMENT IS LOAD-BEARING: stays ABOVE the !b_light_test
		//gate, like the S105b/S106 pins.
		let u_cmf_limbs = u_i.cmF.to_native_sponge_field_elements()?;
		for k in 0..4{
			u_cmf_limbs[k].enforce_equal(&z_i[2+k])?;
		}
		gadget_sat_check(&cs, "decider::p1s7c_s107_cmF"); //DEBUG USE 69801

        //#[cfg(feature = "light-test")]
        //println!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        //#[cfg(not(feature = "light-test"))]
		let b_light_test = utils::consts::read_global_config().b_light_test;
		if !b_light_test
        {
            use super::FOLDPOT_CF_N_POINTS;
            use crate::commitment::pedersen::FixedBasePedersenGadget;
            use crate::folding::circuits::{
				cyclefold::{cf_io_len, CycleFoldCommittedInstanceVar}
			};
			use crate::folding::foldpot::{
				circuits::{ChallengeGadgetFoldPot, NIFSGadgetFoldPot},
			};
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
			gadget_sat_check(&cs, "decider::p1s8a_challenge"); //DEBUG USE 69801
			let mut Ui_pci = U_i.vec_inst[0].clone(); 
			let mut expected_Ui1_pci = U_i1.vec_inst[0].clone();
			for i in 0..n_circ{//this generate FIXED constraints
				//S103b: the selector index must be a CONSTANT. As a
				//witness the prover sets var_i == pc_i at an index of
				//their choosing (or at none, leaving the :1024-1025
				//initializers = slot 0), which redirects this whole
				//NIFS check to a slot decoupled from pc_i. The
				//augmented circuit already does it right
				//(circuits_super.rs:734, :787, :859). b_sel_vec (T935
				//C3) is built over constant indices.
				let b_sel = b_sel_vec[i].clone();
				Ui_pci = b_sel.select(&U_i.vec_inst[i], &Ui_pci)?;
				expected_Ui1_pci = b_sel.select(&U_i1.vec_inst[i], &expected_Ui1_pci)?;
			}
			gadget_sat_check(&cs, "decider::p1s8b_slot_sel"); //DEBUG USE 69801
			// the expensive one: 6MB R1CS
			let Ui1_pci = NIFSGadgetFoldPot::<C1>
				::fold_committed_instance_full(
				r_Fr, 
				Ui_pci,
				u_i.clone(), 
				cmT
			)?;
			Ui1_pci.enforce_equal(&expected_Ui1_pci)?;
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 8: Verify U_i1 is folded U_i and u_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();
			gadget_sat_check(&cs, "decider::p1s8"); //DEBUG USE 69801

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
                Ok(self.cf_U_i.clone().unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            //ALL_T1011 P2(a): keep the range-check bits of E and W.
            let (cf_W_i, cf_E_bits, cf_W_bits) = CycleFoldWitnessVar::<C2>::new_witness_with_bits(
                cs.clone(), self.cf_W_i.as_ref().unwrap_or(&w_dummy_native))?;
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;
			gadget_sat_check(&cs, "decider::p1s9a_cf_hash"); //DEBUG USE 69801

            //9. check Pedersen commitments of cf_U_i.{cmE, cmW}
            //ALL_T1011 P2(b): constant bases, 2-bit windows (no blinding, H = false).
            assert!(!H, "FixedBasePedersenGadget has no blinding term");
            let (computed_cmE, computed_cmW) = FixedBasePedersenGadget::<C2, GC2>::commit_pair(
                cs.clone(), &self.cf_pedersen_params.generators, &cf_E_bits, &cf_W_bits)?;
            drop((cf_E_bits, cf_W_bits));
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
			gadget_sat_check(&cs, "decider::p1s9b_cmE"); //DEBUG USE 69801
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 9: check cf_W_i commits to cf_U_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();
			gadget_sat_check(&cs, "decider::p1s9"); //DEBUG USE 69801


			//10. check cyclefold witness satisfy its r1cs
            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness( cs.clone(), || Ok(self.cf_r1cs.clone()),)?;

            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(),
				cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs,
				cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;

			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 10: check cp_W_i satisfies cyclefold instance. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			gadget_sat_check(&cs, "decider::p1s10"); //DEBUG USE 69801
        }

		if B_DEBUG3{check_cs(&cs, "phase1 step 10");}

		let mut vec_coms_part2 = U_i1.vec_inst.iter().map(|inst|
			vec![inst.cmW.clone(), inst.cmE.clone(), inst.cmF.clone()]
		).flatten().collect::<Vec<NonNativeAffineVar<C1>>>();
		let mut vec_coms = vec![com_all_w_clone];
		vec_coms.append(&mut vec_coms_part2);
		//T941: salt mainres_hash with the caller's randf (driver
		//draws it from OsRng), not a fixed-seed rng.
		let randf_val = randf_in;
		let randf = FpVar::<CF1<C1>>::new_witness(cs.clone(), ||{
			Ok(randf_val)
		})?;
		let cp_hc_out = if self.b_full_mode {
			let link = zi_part2_inst_var.cp_link.as_ref().expect("T931: no cp_link");
			Some((link.hc_a_out.clone(), link.hc_b_out.clone()))
		} else {None};
		let res = Phase1CircuitRet::<C1::ScalarField, C1>{
			ch: zi_part2_inst_var.ch,
			rc: zi_part2_inst_var.rc,
			hash_cmF: z_i[0].clone(),
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

			randf,
			cp_hc_out,
			total_words: Some(zi_part2_inst_var.total_words),
		};

		if B_DEBUG3{check_cs(&cs, "phase1 step 10");}
		let _last_c1 = c1; //just to disable the warning on c1.
		gadget_sat_check(&cs, "decider::p1done"); //DEBUG USE 69801
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: COMPLETED. TOTAL all_w_e: {}, r1cs: {}, RAM: {} GB.", len_all_w_e, cs.num_constraints()-c0, get_mem_usage()), &mut t1);
			Ok( res )
	}
}

/// Phase 2 Circuit that implements the in-circuit checks 
/// It basically proves the same as Phase1 circuit (using its main_circ),
/// and some additional features:
/// THIS CIRCUIT in driver is SPECIFICALLY to compute (as its main function)
///   the *** hashchain *** 
///   of cyclepair_input (and also folding cyclepair checks).
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
///         the ones returned in Phase1 circuit (NOTE not its main circ,
///              which computes the hashchain of cyclepair inp,
///              it's the MAIN zkregplus circ).
/// (3) compute the hashchain(G_1): [com_All_w, (comW, com_E, com_F)_i=1^k, prf]
///             hashchain(G_2): the qa-nizk key series
///     and verify that they are z_n's (hc_a_out, hc_b_out), which the
///     cyclepair circuits chained row by row (T931 P2)
/// (4) verify that hashchain(G_2) is the same as the QA-NIZK verifier key
///     hash
/// --> the above essentially finishes the proof of circ1's (MainDeciderCircuit
///       for ZkregPlus relation)'s com_all_w
///   matches the (W_i || E_i)_i=1^k for the comW, comE, comF of each subcirc
///   of circ1.
/// As this is a "sub-circuit", it does NOT have public I/O, instead,
/// It returns to the caller a Return Package of Wires 
///  In addition to the Phase1CircRet of its main circuit,
///  It returns hashchain(b). Stage 2's z_n (hc_a_out, hc_b_out) reach
/// it via cp_hc_out and are checked against both chains (T931 P2)
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
	pub main_circ:  Phase1Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM, H>,
	/// its own cyclepair_inputs, need to be consistent with the
	/// phase1circ (by the MainDeciderCircuit) return later in gen_constraints
    cyclepair_inputs: Vec<Vec<CF1<C1>>>,
	pub job_id: usize,
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
		 r_all_w_2: (C1::ScalarField, C1::ScalarField),
		 cyclepair_inputs: Vec<Vec<CF1<C1>>>,
	 	) -> Result<Self, Error> {
			let job_id = nova.job_id;
			let main_circ= Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM, H>::from_nova::<FC>(nova, com_all_w_2, r_all_w_2)?;
			Ok(Self {
				_gm: PhantomData,
				main_circ,
				cyclepair_inputs: cyclepair_inputs,
				job_id,
        	})
    }

	/// generate FpVar version of cyclepair_inputs and compute
	/// hash_chain(a), hash_chain(b), which must match z_n's
	/// (hc_a_out, hc_b_out) (T931 P2).
	/// return (cyclapair_inputs_var, hashchain(a), hashchain(b))
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
		(cyclepair_inputs_var, hc_a, hc_b)
	}

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return hashchain(b) (T931 P2 checks both chains in-circuit)
    pub fn generate_constraints_adv(self, circ1_res: &Phase1CircuitRet<CF1<C1>,C1>, cs: ConstraintSystemRef<CF1<C1>>) -> Result<Phase2CircuitRet<CF1<C1>,C1>, Error> {
		//1. generate the cyclepair input and its hash chains
		// hashchain(a), hashchain(b), checked against z_n in step 4
		let c0 = cs.num_constraints();
		let mut c1 = cs.num_constraints();
		let mut t1 = GTimer::new();
		let log_level = LOG3;
		let (cyclepair_inputs_var, hashchain_a, hashchain_b) = 
			self.process_cyclepair_inp(cs.clone());
		log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 1: gen_expected_final_result. r1cs: {}", cs.num_constraints()-c1), &mut t1);
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
				if B_DEBUG2{
					use ark_r1cs_std::R1CSVar;
					if vres[j-12*5].value().is_ok(){
					assert!(vres[j-12*5].value()?==
						cyclepair_inputs_var[i][j].value()?);
				} }
				vres[j-12*5].enforce_equal(&cyclepair_inputs_var[i][j])?;
			}
		}
		log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 2: check cyclepair consistency. r1cs: {}", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//3. perform the main circuit to check its own validity
		assert!(self.main_circ.cp_U_i.is_some());  //2nd phase require it
		let my_phase1_ret={
			let main_circ2 = self.main_circ.clone();
			//T941: 0 is fine. This main_ret is never hashed (CyclePair
			//hashes the Stage-1 mainres), so its salt is unused.
			let randf = CF1::<C1>::zero();
			main_circ2.generate_constraints_adv(3,cs.clone(),randf).unwrap()
		};
		log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 3: Main circ construction. r1cs: {}", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();

		//4. T931 P2: the rows' hash chains are z_n's (hc_a_out,
		//hc_b_out), which the step circuit chained row by row from
		//z_0's zeros. Replaces the compare against the free f_result.
		if self.main_circ.b_full_mode {
			let (ha, hb) = my_phase1_ret.cp_hc_out.clone().expect("T931: no cp_hc_out");
			hashchain_a.enforce_equal(&ha)?;
			hashchain_b.enforce_equal(&hb)?;
		}

		//5. perform an extra cyclepair check!
        //#[cfg(feature = "light-test")]
        //println!("[WARNING]: Running with the 'light-test' feature, skipping the cyclepair part of the DeciderEthCircuit.\n Only for testing purposes.");
        //#[cfg(not(feature = "light-test"))]
		let b_light_test = utils::consts::read_global_config().b_light_test;
		//let part1_enable = false;
		//let part2_enable = false;
		if !b_light_test
        {
            use crate::commitment::pedersen::FixedBasePedersenGadget;
            use crate::folding::circuits::cyclefold::{CycleFoldCommittedInstanceVar};
			//5. Verify cyclepair instance
			//(1) u_i.x[2] = cp_U_i.hash()
			//(2) cp_W_i satisfies the cyclepair R1CS
			//(3) cp_U_i is the commitment of cp_W_i
			//-- cost: 14M for commitment keys 
        	let pp_hash = FpVar::<CF1<C1>>::new_constant(cs.clone(),
            	self.main_circ.pp_hash.expect("T934 K4: pp_hash null"))?;
        	let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(
				cs.clone(), &self.main_circ.poseidon_config);
			assert!(self.main_circ.cp_U_i.is_some());
            let cp_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>
			::new_witness(cs.clone(), || { 
				Ok(self.main_circ.cp_U_i.unwrap())
            })?;
            //ALL_T1011 P2(a): keep the range-check bits of E and W.
            let (cp_W_i, cp_E_bits, cp_W_bits) = CycleFoldWitnessVar::<C2>::new_witness_with_bits(
                cs.clone(), self.main_circ.cp_W_i.as_ref().expect("cp_W_i"))?;
            let (cp_u_i_x, _) = cp_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (my_phase1_ret.u_i.x[2]).enforce_equal(&cp_u_i_x)?;
			if B_DEBUG2{
				use ark_r1cs_std::R1CSVar;
				if my_phase1_ret.u_i.x[2].value().is_ok(){
				assert!(my_phase1_ret.u_i.x[2].value()?==cp_u_i_x.value()?);
			} }
			log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 5: check u_i.x[2]=cp_U_i.hash(). r1cs: {}", cs.num_constraints()-c1), &mut t1);
			c1 = cs.num_constraints();

            //9. check Pedersen commitments of cp_U_i.{cmE, cmW}
			//48M (50G RAM) for cmW and 35M (40G) for cmW
			//check R1CS relation: 90MB (100GB) -> 241GB NOW. 
			//TOTAL: 217M constraints now!!!!. (about 1hr to this point)
			//*** set the debug_disable to true on real server

            //ALL_T1011 P2(b): constant bases, 2-bit windows (no blinding, H = false).
            //Steps 6.1 and 6.2 run together, sharing each generator's table.
            assert!(!H, "FixedBasePedersenGadget has no blinding term");
            let (computed_cmE, computed_cmW) = FixedBasePedersenGadget::<C2, GC2>::commit_pair(
                cs.clone(), &self.main_circ.cp_pedersen_params.generators, &cp_E_bits, &cp_W_bits)?;
            drop((cp_E_bits, cp_W_bits)); // free before Step 10
            cp_U_i.cmE.enforce_equal(&computed_cmE)?;
            cp_U_i.cmW.enforce_equal(&computed_cmW)?;
			if B_DEBUG2{
				if cp_U_i.cmE.value().is_ok(){
				assert!(cp_U_i.cmE.value()?== computed_cmE.value()?);
				assert!(cp_U_i.cmW.value()?== computed_cmW.value()?);
			} }
			log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 6: check cp_W_i commits to cp_U_i (cmE and cmW). r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			//10. check cyclepair witness satisfy its r1cs
            let cp_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness( cs.clone(), || Ok(self.main_circ.cp_r1cs.clone()),)?;
            let cp_z_U = [vec![cp_U_i.u.clone()], cp_U_i.x.to_vec(), 
				cp_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cp_r1cs, 
				cp_W_i.E, cp_U_i.u.clone(), cp_z_U)?;
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 10: check cp_W_i satisfies cyclefold instance. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();
		}

		let res = Phase2CircuitRet::<C1::ScalarField, C1>{
			hashchain_b: hashchain_b,
			main_ret: my_phase1_ret.clone()
		};

		let _c1 = c1; //to disable warning
		log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: COMPLETE. TOTAL r1cs: {}, RAM: {} GB", cs.num_constraints()-c0, get_mem_usage()), &mut t1);

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

/// Horner evaluation sum_i v_i point^i. `one` is a witness wire pinned to 1
/// (one == FpVar::one() is enforced by the caller). Every 1024 steps
/// eval * one adds one real constraint and a fresh variable with the same
/// value, which cuts the growing chain of symbolic linear combinations.
/// Without the cut, inlining that chain over about 10^8 entries overflows
/// the stack (sonobe issue 80). The constant 1 would be free and would not cut.
fn evaluate_gadget<F: PrimeField>(v: &[FpVar<F>], point: &FpVar<F>, one: &FpVar<F>)
	-> Result<FpVar<F>, SynthesisError> {
	let mut eval = FpVar::<F>::zero();
	for (i, x) in v.iter().rev().enumerate() {
		eval = &eval * point + x;
		if i % 1024 == 0 { eval = &eval * one; }
	}
	Ok(eval)
}

/// ALL_T1014: sum_s w_s r^{off_s} H_s(r), H_s = evaluate_gadget of segment s,
/// off_s = total length of the segments before s.
fn weighted_horner<F: PrimeField>(segs: &[(&[FpVar<F>], FpVar<F>)], r: &FpVar<F>, one: &FpVar<F>)
	-> Result<FpVar<F>, SynthesisError> {
	segs.iter().rev().try_fold(FpVar::zero(), |acc, (v, w)|
		Ok(acc * r.pow_by_constant([v.len() as u64])? + w * evaluate_gadget(v, r, one)?))
}

/// ALL_T1014: one slot (u, x, W, E) rescaled to u = 1, i.e. (x/u, W/u, E/u^2).
/// A u = 0 slot must be a never-folded dummy (x = W = E = 0) and keeps
/// x' = W' = 0 with E' = dummy_residual.
pub fn scaled_slot<F: PrimeField>(r1cs: &R1CS<F>, u: F, x: &[F], w: &[F], e: &[F])
	-> (Vec<F>, Vec<F>, Vec<F>) {
	let scale = |v: &[F], s: F| v.iter().map(|a| *a * s).collect::<Vec<F>>();
	match u.inverse() {
		Some(i) => (scale(x, i), scale(w, i), scale(e, i.square())),
		None => {
			assert!(x.iter().chain(w).chain(e).all(F::is_zero), "ALL_T1014: u = 0 slot is not a dummy");
			(x.to_vec(), w.to_vec(), dummy_residual(r1cs))
		}
	}
}

/// ALL_T1014: E' of a u = 0 dummy slot at z' = (1, 0..0), i.e. A0 o B0 - C0
/// with M0 the column 0 of M.
pub fn dummy_residual<F: PrimeField>(r1cs: &R1CS<F>) -> Vec<F> {
	let col0 = |m: &SparseMatrix<F>| m.coeffs.iter().map(|row| row.iter()
		.filter(|(_, c)| *c == 0).map(|(a, _)| *a).sum::<F>()).collect::<Vec<F>>();
	let (a, b, c) = (col0(&r1cs.A), col0(&r1cs.B), col0(&r1cs.C));
	a.iter().zip(&b).zip(&c).map(|((a, b), c)| *a * b - c).collect()
}

/// ALL_T1014: the Groth16 committed range D in D order: W'_1..W'_k,
/// E'_1..E'_k, (o_1, o_2), (u_1..u_k), x'_1..x'_k. W', E', x' are the
/// slots rescaled to u = 1. The first 2k + 1 parts unscale to all_w().
#[derive(Clone, Debug)]
pub struct CommittedRange<T> {
	pub w: Vec<Vec<T>>,
	pub e: Vec<Vec<T>>,
	pub o: Vec<T>,
	pub u: Vec<T>,
	pub x: Vec<Vec<T>>,
}

impl<T> CommittedRange<T> {
	/// The parts in D order.
	pub fn parts(self) -> impl Iterator<Item = Vec<T>> {
		self.w.into_iter().chain(self.e).chain([self.o, self.u]).chain(self.x)
	}

	/// Maps every part by f, calling f in D order.
	pub fn try_map<S, Er>(self, mut f: impl FnMut(Vec<T>) -> Result<Vec<S>, Er>)
		-> Result<CommittedRange<S>, Er> {
		let w = self.w.into_iter().map(&mut f).collect::<Result<_, _>>()?;
		let e = self.e.into_iter().map(&mut f).collect::<Result<_, _>>()?;
		let (o, u) = (f(self.o)?, f(self.u)?);
		let x = self.x.into_iter().map(&mut f).collect::<Result<_, _>>()?;
		Ok(CommittedRange{ w, e, o, u, x })
	}

	/// Length of the unscaled all_w() (the W, E and o parts).
	pub fn unscaled_len(&self) -> usize {
		self.o.len() + self.w.iter().chain(&self.e).map(Vec::len).sum::<usize>()
	}
}

impl<F: PrimeField> CommittedRange<FpVar<F>> {
	/// ALL_T1014: allocates D as ONE contiguous committed witness range.
	pub fn alloc(cs: &ConstraintSystemRef<F>, d: CommittedRange<F>) -> Result<Self, SynthesisError> {
		let s0 = cs.num_witness_variables();
		let v = d.try_map(|p| Vec::<FpVar<F>>::new_witness(cs.clone(), || Ok(p)))?;
		cs.set_committed(s0, cs.num_witness_variables() - s0);
		Ok(v)
	}

	/// ALL_T1014: ties D to the instance on every slot: u_j = U_j.u and
	/// U_j.x = u_j x'_j.
	pub fn bind<C: CurveGroup<ScalarField = F>>(&self, inst: &[CommittedInstanceVarFoldPot<C>])
		-> Result<(), SynthesisError> where C::BaseField: PrimeField {
		assert_eq!(inst.len(), self.u.len(), "ALL_T1014: slot count");
		for ((i, u), xp) in inst.iter().zip(&self.u).zip(&self.x) {
			assert_eq!(i.x.len(), xp.len(), "ALL_T1014: |x|");
			u.enforce_equal(&i.u)?;
			for (x, q) in i.x.iter().zip(xp) { q.mul_equals(u, x)?; }
		}
		Ok(())
	}

	/// ALL_T1014: P(r) of the unscaled all_w(), with W_j = u_j W'_j and
	/// E_j = u_j^2 E'_j, then (o_1, o_2). `one` is the pinned witness 1 that
	/// evaluate_gadget uses to cut its linear-combination chain.
	pub fn eval_unscaled(&self, r: &FpVar<F>, one: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
		let u2 = self.u.iter().map(FieldVar::square).collect::<Result<Vec<_>, _>>()?;
		let segs = self.w.iter().zip(self.u.iter().cloned()).chain(self.e.iter().zip(u2))
			.map(|(v, s)| (v.as_slice(), s))
			.chain([(self.o.as_slice(), FpVar::one())]).collect::<Vec<_>>();
		weighted_horner(&segs, r, one)
	}

	/// ALL_T1014: Step 7 on slot j, (A z')(B z') = C z' + E' with
	/// z' = (1, x'_j, W'_j). One constraint per row. Here 1 is the R1CS
	/// constant (FpVar::one()), never a witness, and u = 1 makes u Cz free.
	pub fn check_slot(&self, j: usize, r1cs: R1CSVar<F, F, FpVar<F>>) -> Result<(), SynthesisError> {
		let z = [vec![FpVar::one()], self.x[j].clone(), self.w[j].clone()].concat();
		RelaxedR1CSGadget::check_native(r1cs, self.e[j].clone(), FpVar::one(), z)
	}
}

/// T934 D2 / ruling D: Fiat-Shamir tags of r_2 (Stage 1) and r' (Stage 2).
pub const KZG_CH_TAG_S1: &[u8] = b"bora/kzg_ch/s1";
pub const KZG_CH_TAG_S2: &[u8] = b"bora/kzg_ch/s2";

/// T934 D2: r = H(tag, com, D), both points absorbed nonnative.
pub fn kzg_ch<C: CurveGroup>(poseidon_config: &PoseidonConfig<C::ScalarField>,
	tag: &[u8], com: C, d: C) -> C::ScalarField
where C::ScalarField: Absorb, C::BaseField: PrimeField {
	let mut t = PoseidonSponge::<C::ScalarField>::new(poseidon_config);
	t.absorb(&tag);
	t.absorb_nonnative(&com);
	t.absorb_nonnative(&d);
	t.get_challenge()
}

/// T934: native evaluate_gadget, sum_i v_i r^i.
pub fn eval_all_w<F: PrimeField>(v: &[F], r: F) -> F {
	v.iter().rev().fold(F::zero(), |acc, x| acc * r + x)
}

/// Represents the public i/o of the CyclePairCircInput,
/// most elements can be retrieved from nova
#[derive(Clone, Debug, PartialEq)]
pub struct CircPubInput<F: PrimeField+ColEle,C: CurveGroup<ScalarField=F>>{
	/// the ch of circ1
	pub ch1: F,
	/// the rc of circ1
	pub rc1: F,
	/// the disclosed z_n[0] chain value of circ1 (S107)
	pub hash_cmF1: F,
	/// the kzg sum of circ1
	pub kzg_sum1: F,
	/// the the challenge of kzg_all_com_e
	pub kzg_all_com_ch1: F,
	/// the evaluation of kzg_all_com at kzg_all_com_ch
	pub eval_w_e1: F,
	/// the hash of the Circ1Ret of the main circ
	pub mainres_hash: F,

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


	/// the comE of U_{i+1} of circ2 (they will go to the
	/// QA-NIZK proof). Circ 2 handles the MANY comE,W,F for each
	/// sub circuit (so these of Circ1 don't have to get disclosed)
	pub comE2: C,
	/// the comW of U_{i+1} of circ2
	pub comW2: C,
	/// the comF of U_{i+1} of circ2
	pub comF2: C,
	/// T934 D4: C_WE of circ1, pinned to the circuit's com_all_w
	pub kzg_all_com1: C,
}

impl <F: PrimeField+ColEle, C: CurveGroup<ScalarField=F>> CircPubInput<F,C>
where
C::Affine: AffineFromField<CF2<C>>,
CF2<C>: PrimeField
{
	pub fn to_vec(&self)->Result<Vec<F>,Error>{
		let mut res = vec![
			self.ch1.clone(),
			self.rc1.clone(),
			self.hash_cmF1.clone(),
			self.kzg_sum1.clone(),
			self.kzg_all_com_ch1.clone(),
			self.eval_w_e1.clone(),
			self.mainres_hash.clone(),

			self.kzg_all_com_ch2.clone(),
			self.eval_w_e2.clone(),

			self.qa_nizk_vkey_hash.clone(),
		];
		let (comEx, comEy) = 	NonNativeAffineVar::inputize(self.comE2)?;
		let (comWx, comWy) = 	NonNativeAffineVar::inputize(self.comW2)?;
		let (comFx, comFy) = 	NonNativeAffineVar::inputize(self.comF2)?;
		let (cwex, cwey) = NonNativeAffineVar::inputize(self.kzg_all_com1)?;
		let mut part2 = vec![comEx, comEy, comWx, comWy, comFx, comFy, cwex, cwey].concat();
		res.append(&mut part2);
		Ok(res)
	}

	/// parse from vector
	pub fn from_vec(v: &Vec<F>)->Self{
		let (ch1, rc1, hash_cmF1, kzg_sum1, kzg_all_com_ch1,
			  eval_w_e1, mainres_hash, kzg_all_com_ch2, eval_w_e2) =
			v[0..9].to_vec().into_iter().collect_tuple().unwrap();
		let qa_nizk_vkey_hash = v[9];
		let vec_rest = &v[10..v.len()];
		assert!(vec_rest.len()==5*8);
		let vec_fq = vec_rest.chunks(5).map(|chunk| {
			f1_limbs_to_f2::<F, CF2<C>>(&chunk.to_vec())
		}).collect::<Vec<CF2<C>>>();
		assert!(vec_fq.len()==8);
		let v_pt = vec_fq.chunks(2).map(|chunk|{
			C::Affine::from_fields(chunk[0], chunk[1])
		}
		).collect::<Vec<C::Affine>>();
		let (comE2, comW2, comF2, kzg_all_com1): (C,C,C,C) = (v_pt[0].into(),
			v_pt[1].into(), v_pt[2].into(), v_pt[3].into());
		Self{
			ch1, rc1, hash_cmF1, kzg_sum1, kzg_all_com_ch1, eval_w_e1,
			kzg_all_com_ch2, eval_w_e2,
			qa_nizk_vkey_hash,
			mainres_hash,
			comE2, comW2, comF2, kzg_all_com1
		}
	}
}

/// Main Circuit (which asserts that there exists a 
/// FoldSuper instance (both predicate and witness)
/// that evaluates at a given random point to a certain kzg_sum value
/// and satisfies the circuit relation (the ZkregReg relation circs).
/// It is basically a wrapper of Phase1 circ, except that
/// it GENERATES 1 field element: the hash of the Phase1Ret.
#[derive(Clone, Debug)]
pub struct MainDeciderCircuit<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool = false>
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
	/// circuit 1 for nova1
	pub circ1:  Phase1Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM,H>,
	/// the result
	pub res: Phase1CircuitRetVal<C1::ScalarField,C1>,
	/// the randf
	pub randf: C1::ScalarField,
	/// the hash of the main result
	pub res_hash: C1::ScalarField,
	pub job_id: usize,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool> MainDeciderCircuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, H>
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
		com_all_w_1: C1,
		r_all_w_1: (C1::ScalarField, C1::ScalarField),
		randf: C1::ScalarField,
    ) -> Result<Self, Error> {
		use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
		use ark_r1cs_std::R1CSVar;
		let job_id = nova1.job_id;
		let mut circ1 = Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM,H>::from_nova::<FC>(nova1, com_all_w_1, r_all_w_1)?;
		circ1.kzg_ch = Some(C1::ScalarField::zero()); //T934: placeholder until finalize

        let cs = ConstraintSystem::<CF1<C1>>::new_ref();
		cs.set_mode(SynthesisMode::Eager); //T940: values only
		let res = circ1.generate_constraints_adv(0, cs.clone(), randf).unwrap();
		let res_val = res.val();
		let res_hash_var = res.hash(&circ1.poseidon_config,
			cs.clone());
		let res_hash = res_hash_var.value()?;
		if std::env::var("ZKR_MAIN_SNARK_PROBE").is_ok(){
			println!("DEBUG USE 69801.0: from_nova res_hash={}",
				res_hash);
		}
		Ok(Self{circ1, res: res_val, randf, res_hash, job_id})
    }

	/// T934 ruling C: set r_2 and patch res natively (eval_w_e, hash).
	pub fn finalize(&mut self, r_2: C1::ScalarField, all_w: &[C1::ScalarField]) {
		use ark_r1cs_std::R1CSVar;
		self.circ1.kzg_ch = Some(r_2);
		self.res.kzg_all_com_ch = r_2;
		self.res.eval_w_e = eval_all_w(all_w, r_2);
		let cs = ark_relations::r1cs::ConstraintSystem::<CF1<C1>>::new_ref();
		cs.set_mode(ark_relations::r1cs::SynthesisMode::Eager); //T940: values only
		self.res_hash = Phase1CircuitRet::from(&self.res, &cs)
			.hash(&self.circ1.poseidon_config, cs).value().expect("res hash");
	}

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, const H: bool> ConstraintSynthesizer<CF1<C1>> for MainDeciderCircuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM, H>
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
		let b_debug = B_DEBUG;
		let log_level = LOG2;

		//1. let the two circuits generate constraints first
		let c0 = cs.num_constraints();
		let phase1_ret=self.circ1
			.generate_constraints_adv(2,cs.clone(),self.randf).unwrap();
		let mainres_hash = phase1_ret.hash(&self.circ1.poseidon_config,
			cs.clone());

		//2. set up the hash of ret as the PUBLIC i/o of circ
		use ark_r1cs_std::R1CSVar;
		let mainres_hash_val = if mainres_hash.value().is_ok(){
			mainres_hash.value()?
		}else{C1::ScalarField::zero()};
		let mainres_pub = FpVar::<C1::ScalarField>::new_input(cs.clone(),
			|| Ok(mainres_hash_val) )?; //public input 1 of 2
		mainres_hash.enforce_equal(&mainres_pub)?;
		//T933 K2-min: public input 2 = the fold's word count.
		let tw = phase1_ret.total_words.as_ref().expect("T933: no total_words");
		FpVar::new_input(cs.clone(), || tw.value())?.enforce_equal(tw)?;
		if B_DEBUG2{
			if phase1_ret.ch.value().is_ok(){
				let phase1_ret_val = phase1_ret.val();
				assert!(phase1_ret_val == self.res);
			}
		}
		//DEBUG probe 69801: prove-pass vs from_nova cross-check. The
		//verifier checks against from_nova's res_hash while the proof
		//instance is seeded HERE -- a mismatch names the exact field.
		if std::env::var("ZKR_MAIN_SNARK_PROBE").is_ok()
			&& mainres_hash.value().is_ok(){
			let pv = phase1_ret.val();
			println!("DEBUG USE 69801.1: pass res_hash={} \
				from_nova={} eq={}", mainres_hash_val,
				self.res_hash, mainres_hash_val==self.res_hash);
			if pv == self.res {
				println!("DEBUG USE 69801.2: phase1_ret == \
					from_nova res (all fields)");
			}else{
				if pv.ch != self.res.ch {println!(
					"DEBUG USE 69801.3: ch {} vs {}",
					pv.ch, self.res.ch);}
				if pv.rc != self.res.rc {println!(
					"DEBUG USE 69801.3: rc {} vs {}",
					pv.rc, self.res.rc);}
				if pv.hash_cmF != self.res.hash_cmF {println!(
					"DEBUG USE 69801.3: hash_cmF {} vs {}",
					pv.hash_cmF, self.res.hash_cmF);}
				if pv.kzg_sum != self.res.kzg_sum {println!(
					"DEBUG USE 69801.3: kzg_sum {} vs {}",
					pv.kzg_sum, self.res.kzg_sum);}
				if pv.final_result != self.res.final_result {println!(
					"DEBUG USE 69801.3: final_result {} vs {}",
					pv.final_result, self.res.final_result);}
				if pv.kzg_all_com_ch != self.res.kzg_all_com_ch {
					println!("DEBUG USE 69801.3: kzg_all_com_ch \
						{} vs {}", pv.kzg_all_com_ch,
						self.res.kzg_all_com_ch);}
				if pv.eval_w_e != self.res.eval_w_e {println!(
					"DEBUG USE 69801.3: eval_w_e {} vs {}",
					pv.eval_w_e, self.res.eval_w_e);}
				if pv.randf != self.res.randf {println!(
					"DEBUG USE 69801.3: randf {} vs {}",
					pv.randf, self.res.randf);}
				if pv.vec_coms != self.res.vec_coms {println!(
					"DEBUG USE 69801.3: vec_coms first diff at \
						{:?}", pv.vec_coms.iter()
						.zip(self.res.vec_coms.iter())
						.position(|(a,b)| a!=b));}
				if pv.u_i != self.res.u_i {println!(
					"DEBUG USE 69801.3: u_i differs: {:?} vs {:?}",
					pv.u_i, self.res.u_i);}
				if pv.u_i1_0_cmE != self.res.u_i1_0_cmE {println!(
					"DEBUG USE 69801.3: u_i1_0_cmE differs");}
				if pv.u_i1_0_cmW != self.res.u_i1_0_cmW {println!(
					"DEBUG USE 69801.3: u_i1_0_cmW differs");}
				if pv.u_i1_0_cmF != self.res.u_i1_0_cmF {println!(
					"DEBUG USE 69801.3: u_i1_0_cmF differs");}
			}
		}
		log_perf(self.job_id, log_level, &format!("TwoPhaseCirc build circ1: {} cs.",
			cs.num_constraints()-c0), &mut gt2);

		if B_DEBUG2{check_cs(&cs, "TwoPhaseCirc build circ1");}

		log_perf(self.job_id, log_level-1, &format!("*** MainDeciderCirtuit TOTAL constraints: {} ***. ", cs.num_constraints()), &mut gt1);

		Ok( () )

	}
}


/// Circuit that implements the in-circuit checks for the two phase
/// Scheme. In fact, it employs two instances of DeciderEthCircuitSuper,
/// and pass the cyclepair_input in between to make sure that
/// they are consistent.
#[derive(Clone, Debug)]
pub struct CyclePairCircuit<E:Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM2, const H: bool = false>
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
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
	<C2G2 as ark_ec::Group>::ScalarField: ColEle
{
	/// circuit 2 for nova2
	pub circ2:  Phase2Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>,
	/// public input for the circuit
	inp:  CircPubInput<CF1<C1>,C1>,
	/// Maincirc res
	mainres: Phase1CircuitRetVal<CF1<C1>,C1>,
	pub job_id: usize,
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM2, const H: bool> CyclePairCircuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM2, H>
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
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
	<C2G2 as ark_ec::Group>::ScalarField: ColEle
{
	/// Retrieve the non-deterministic advice from the nova instance
	/// and save in its own data members. Basically,
	/// it builds  a phase2 decider circuit, which
	/// processes the return (commitments) from MainDeciderCircuit
	/// and links up the information between two circs.
    pub fn from_nova
		(
        nova2: FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, SigmaIR1CS_Inst<C1::ScalarField, C1, CS1,LK,GM2, H>, CS1, CS2, CS1E, LK, GM2, H>,
		cyclepair_inputs: Vec<Vec<C1::ScalarField>>,
		_qa_nizk_vkey_hash: C1::ScalarField,
		_poseidon_config: PoseidonConfig<C1::ScalarField>,
		_com_all_w_1: C1,
		_r_all_w_1: (C1::ScalarField, C1::ScalarField),
		com_all_w_2: C1,
		r_all_w_2: (C1::ScalarField, C1::ScalarField),
		mainres: Phase1CircuitRetVal<CF1<C1>, C1>, //will generate cyclepair inp
		inp: CircPubInput<CF1<C1>,C1>, //will be verified against mainres
    ) -> Result<Self, Error> 
	where <C2G2 as ark_ec::Group>::ScalarField: ColEle
	{
		let job_id = nova2.job_id;
		let circ2 = Phase2Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>::from_nova::<SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, GM2, H>>(nova2, com_all_w_2, r_all_w_2, cyclepair_inputs)?;
		Ok( Self{ circ2, inp, mainres, job_id } )
    }

	/// T934 ruling C: set r' after D_2; also patches inp's ch2 / eval_w_e2.
	pub fn set_kzg_ch(&mut self, r: C1::ScalarField, all_w: &[C1::ScalarField]) {
		self.circ2.main_circ.kzg_ch = Some(r);
		self.inp.kzg_all_com_ch2 = r;
		self.inp.eval_w_e2 = eval_all_w(all_w, r);
	}

}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + Debug, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM2, const H: bool> ConstraintSynthesizer<CF1<C1>> for CyclePairCircuit<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK, GM2, H>
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
	//GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	GM2: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,

	// to call nova function
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
	C1::Config: SWCurveConfig,
	P: Clone,
	<C2G2 as ark_ec::Group>::ScalarField: ColEle
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		let mut gt1 = GTimer::new();
		let mut gt2 = GTimer::new();
		let log_level = LOG2;
		let b_debug = B_DEBUG;
		let c0 = cs.num_constraints();

		//1. create circ2 (cyclepair circ generate constraints)
		// circ2 takes the phase1_ret, encodes its vector of
		// commitments as cyclepair_input, and compute the
		// hashchain of these commitments, and its cyclepair
		// component verifies the correctness of the pairing equations
		// that involves these commitments.
		let phase1_ret = Phase1CircuitRet::from(&self.mainres, &cs);
		let mainres_hash = phase1_ret.hash(&self.circ2.main_circ
			.poseidon_config, cs.clone());
		let phase2_ret = self.circ2.generate_constraints_adv(
			&phase1_ret, 
			cs.clone()).unwrap();
		let c2 = cs.num_constraints();
		log_perf(self.job_id, log_level, &format!("CyclePairCirc step 1. build circ: {} cs.",
			c2-c0), &mut gt2);

		//2. establish the public inputs and check the consistency
		// with the phase1 and phase2 returns.
		// this includes the check:
		// (1) the public input mainres_hash MATCHES the hash
		//    of the Circ1Ret from MainCirc. (thus connecting the two circs)
		// (2) the phase2 circ ret cmE, cmF, cmW match that of the public inp
		// (3) the cyclepair input generates hashchain_b and it
		//       matches the one in pub_input.
		let _s_dbg = vec![
			"ch1", "rc1", "hash_cmF1", "kzg_sum1", "kzg_all_com_ch1",
			"eval_w_e1", "mainres_hash",
			"kzg_all_com_ch2", "eval_w_2", "qa_nizk_vkey_hash", 
		];
		let vec_inp = self.inp.to_vec().expect("Inp to Vec error")
			.into_iter().map(|x: C1::ScalarField|
				FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(x) )
					.expect("FpVar new input fails"))
			.collect::<Vec<FpVar<CF1<C1>>>>();


		let mut vec_ret = vec![
			phase1_ret.ch, phase1_ret.rc, phase1_ret.hash_cmF,
				phase1_ret.kzg_sum,
				phase1_ret.kzg_all_com_ch, phase1_ret.eval_w_e,
				mainres_hash,
			phase2_ret.main_ret.kzg_all_com_ch, phase2_ret.main_ret.eval_w_e,
				phase2_ret.hashchain_b ];


		let limbs = phase2_ret.main_ret.u_i1_0_cmE.x.0.len();
		let coms = vec![phase2_ret.main_ret.u_i1_0_cmE,
			phase2_ret.main_ret.u_i1_0_cmW, phase2_ret.main_ret.u_i1_0_cmF,
			phase1_ret.vec_coms[0].clone()]; //T934 D4: C_WE
		let mut part2 = coms.into_iter().map(|pt| {
			vec![pt.x, pt.y].into_iter().map(|ui| 
				ui.0.iter().map(|x| 
					x.v.clone()).collect::<Vec<FpVar::<CF1::<C1>>>>()
			).flatten().collect::<Vec<FpVar::<CF1::<C1>>>>()
		}).flatten().collect::<Vec<FpVar::<CF1::<C1>>>>();
		assert!(part2.len() == 8 * limbs); //5 limbs each
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
		log_perf(self.job_id, log_level, &format!("CyclePairCirc Step 2: validate all other data: {} cs.", c3-c2), &mut gt2);

		if B_DEBUG2{check_cs(&cs, "CyclcePairCirc Step 2");}

		log_perf(self.job_id, log_level-1, &format!("*** CyclePairCirc TOTAL constraints: {} ***.", cs.num_constraints()), &mut gt1);
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
		let inp= CircPubInput::<Fr, Projective>{
			ch1: Fr::rand(&mut rng),
			rc1: Fr::rand(&mut rng),
			hash_cmF1: Fr::rand(&mut rng),
			kzg_sum1: Fr::rand(&mut rng),
			kzg_all_com_ch1: Fr::rand(&mut rng),
			eval_w_e1: Fr::rand(&mut rng),
			mainres_hash: Fr::rand(&mut rng),

			kzg_all_com_ch2: Fr::rand(&mut rng),
			eval_w_e2: Fr::rand(&mut rng),

			qa_nizk_vkey_hash: Fr::rand(&mut rng),
			comE2: Projective::rand(&mut rng),
			comW2: Projective::rand(&mut rng),
			comF2: Projective::rand(&mut rng),
			kzg_all_com1: Projective::rand(&mut rng),
		};

		let vec = inp.to_vec().unwrap();
		let inp2 = CircPubInput::<Fr,Projective>::from_vec(&vec);
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
        let evalVar = evaluate_gadget::<Fr>(&vVar, &challengeVar, &one)
			.unwrap();

        use ark_r1cs_std::R1CSVar;
        assert_eq!(evalVar.value().unwrap(), eval);
		//the above will lead to OVERFLOW due to a bug in arkworks
		//instead, we verify evalVar is equal to eval in circuit
		let evalVar2 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(eval)).unwrap();
		evalVar2.enforce_equal(&evalVar).expect("evalVar err");
        assert!(cs.is_satisfied().unwrap());
    }

	// ---------------------------------------------------------------
	// S119: the two shipped decider-side pins CONSTRAIN, not merely
	// EXECUTE. Both sit ABOVE the `if !b_light_test` gate in gen_cs,
	// so light mode (the default) covers them while NIFS.V stays gated
	// out -- no proving, no Phase 2, no CyclePairCircuit.
	//
	// Emission order inside generate_constraints_adv:
	//   step 5   u_i.x[0] == H(.., z_0, z_i, ..)  <- reads z_0 AND z_i
	//   step 6   zi_p2 == z_i[1]                  <- the digest carry
	//            S106 terminality pin
	//            S105b z_0 pin
	// Every arm below edits WITNESS VALUES only, so all four systems
	// are shape-identical and the first-unsatisfied INDEX names the
	// same constraint across them. That index is what LOCALISES a
	// rejection: an arm that merely goes UNSAT proves nothing, because
	// a naive edit breaks step 5 or the digest carry first, upstream
	// of the pin it means to test.
	// ---------------------------------------------------------------
	use crate::commitment::{kzg::KZG, pedersen::Pedersen};
	use crate::transcript::poseidon::poseidon_canonical_config;
	use crate::FoldingScheme; //preprocess() / prove_step() live here
	use crate::folding::foldpot::{
		mod_super::PreprocessorParamFoldPotSuper,
		sigma_ir1cs::{
			LookupTableTwoCol_Inst,
			tests_sigma_ir1cs::{gen_six_root_adv, SixRootMapper},
		},
	};
	use ark_bn254::{Bn254, G2Projective as ProjectiveG2,
		constraints::{GVar, PairingVar as Bn254PairingVar}};
	use ark_grumpkin::{constraints::GVar as GVar2,
		Projective as Projective2};

	type S119Lk = LookupTableTwoCol_Inst<Fr>;
	type S119Cm = KZG<'static, Bn254>;
	type S119Cm2 = Pedersen<Projective2>;
	type S119Gm = SixRootMapper<Fr, S119Lk>;
	type S119Fc = SigmaIR1CS_Inst<Fr, Projective, S119Cm, S119Lk,
		S119Gm, false>;
	type S119Nova = FoldPotSuper<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Fc, S119Cm, S119Cm2,
		S119Cm, S119Lk, S119Gm, false>;
	type S119Circ = Phase1Circuit<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Cm, S119Cm2,
		S119Cm, S119Lk, S119Gm, false>;

	/// Fold the six_root toy n_steps and return the Phase 1 decider
	/// circuit built from it, mirroring driver.rs foldpot_main step 5.
	fn s119_fold(n_steps: usize) -> S119Circ{ s119_fold_probe(n_steps, None) }

	/// T933 s9 probe at step 5: (folded witness, com_all_w, opening of
	/// com_all_w, its challenge, the cs1e key).
	type S119Probe<'p> = &'p mut dyn FnMut(&WitnessFoldPotSuper<Projective>,
		Projective, &crate::commitment::kzg::Proof<Projective>, Fr,
		&crate::commitment::kzg::ProverKey<'static, Projective>);

	/// s119_fold with an optional probe on the step-5 values.
	fn s119_fold_probe(n_steps: usize, probe: Option<S119Probe>) -> S119Circ{
		s119_fold_rows(n_steps, probe).0
	}

	/// T931: s119_fold_probe plus the Stage-2 rows of its QA-NIZK (the
	/// driver.rs:3547 encoder), the vkey hash and b_0 = vkey.c[0].
	fn s119_fold_rows(n_steps: usize, probe: Option<S119Probe>)
		-> (S119Circ, Vec<Vec<Fr>>, Fr, ProjectiveG2){ s119_fold_pp(n_steps, probe, None) }

	/// T934 K4: s119_fold_rows with the IVC folded under pp_hash `pp`.
	fn s119_fold_pp(n_steps: usize, probe: Option<S119Probe>, pp: Option<Fr>)
		-> (S119Circ, Vec<Vec<Fr>>, Fr, ProjectiveG2){
		let mut rng = ark_std::test_rng();
		let cfg = poseidon_canonical_config::<Fr>();
		let b_full = false;
		//b_check_lkup=false -- see the S118 note on s103_fold. The
		//toy's Hab'22 sums cannot balance at a TERMINAL step, and
		//this fold ends terminal on purpose.
		let (lk, f_circ, mut vec_stmt) =
			gen_six_root_adv::<Fr, Projective, S119Cm, S119Lk, false>(
				n_steps, false);
		//the toy's counter is inconsistent with what CounterIOGadget
		//can read (see build_statement's NOTE): for n = 64 the
		//statement claims oup = inp + 1 while the gadget adds 0, so
		//assert_msg3 kills any fold of >= 2 steps. Zero the counter
		//to make the two agree. This is local to S119 -- the shared
		//fixture is untouched, so the S106 tests keep their exact
		//statements -- and it costs nothing here: S119 exercises the
		//DECIDER pins, not the toy's I/O increment. The carry itself
		//(inp == previous oup) is still exercised, at 0.
		for st in vec_stmt.iter_mut(){
			st.inp_buf[0] = Fr::zero();
			st.oup_buf[0] = Fr::zero();
		}
		let prep = PreprocessorParamFoldPotSuper::<Projective,
			Projective2, S119Fc, S119Cm, S119Cm2, S119Lk, S119Gm,
			false>::new(cfg.clone(), vec![f_circ.clone()], lk,
				vec![f_circ.get_size_f()], b_full);
		let params = S119Nova::preprocess(&mut rng, &prep, 0)
			.expect("preprocess err");
		let fq_bits = <<Projective as CurveGroup>::BaseField
			as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;

		//PASS 1: the cmF hash chain. n_words MUST be the value also
		//passed to init_adv -- init_adv rebuilds z_0 canonically and
		//asserts the two agree (mod_super.rs init_adv step 1).
		//n_words = n_steps is the faithful seed here: total_words is a
		//PURE CARRY from z_0 (sigma_ir1cs.rs "S106: total_words is now
		//a PURE CARRY") and the toy's statements run word_id
		//1..n_steps, so any smaller seed leaves the last step
		//non-terminal.
		let zero = Fr::zero();
		let z0_p2 = ZiPartTwoInst::<Fr>::new(zero, zero, &cfg, b_full,
			fq_bits, n_steps);
		let z_0 = [vec![zero, z0_p2.hash(&cfg)],
			vec![zero; 4]].concat();
		let nova0 = S119Nova::init_adv(&params, vec![f_circ.clone()],
			z_0, 1, 0, b_full, zero, zero, n_steps, None, 0)
			.expect("init_adv pass1 err");
		let mut hash_cmf = zero;
		for i in 0..n_steps{
			(hash_cmf, _) = nova0.compute_step_hc_cmF(hash_cmf,
				&vec_stmt[i]).expect("hc_cmF err");
		}
		drop(nova0);

		//PASS 2: the real IVC, seeded with ch = hash_cmf.
		//S107: z_0[0] is ZERO, not hash_cmf -- the in-circuit chain
		//re-runs from zero so z_n[0] lands back on hash_cmf, which
		//is what the decider discloses. ch keeps carrying hash_cmf
		//through init_adv's own argument (driver.rs pass_all).
		let z0_p2 = ZiPartTwoInst::<Fr>::new(hash_cmf, zero, &cfg,
			b_full, fq_bits, n_steps);
		let z_0 = [vec![zero, z0_p2.hash(&cfg)],
			vec![zero; 4]].concat();
		let mut nova = S119Nova::init_adv(&params,
			vec![f_circ.clone()], z_0, 1, 0, b_full, hash_cmf, zero,
			n_steps, None, 0).expect("init_adv pass2 err");
		if let Some(h) = pp { nova.pp_hash = h; }
		for j in 0..n_steps{
			nova.prove_step(&mut rng, vec_stmt[j].to_vec(), None)
				.expect("prove_step err");
		}
		assert_eq!(Fr::from(n_steps as u32), nova.i);

		//driver.rs step 5: com_all_w / r_all_w over the folded witness.
		let (u_i1, w_i1, _r, _cmt) = nova.gen_next_folded()
			.expect("gen_next_folded err");
		let (com_all_w, qa, r_all_w) = w_i1
			.gen_com_all_w_and_qa_nizk_prf::<Bn254, S119Cm, false>(
				params.0.qa_pp.as_ref().expect("qa_pp null"),
				&params.0.cs1e_pp,
				params.1.qa_vp.as_ref().expect("qa_vp null"),
				&u_i1);
		let vp = params.1.qa_vp.as_ref().expect("qa_vp null");
		let rows = u_i1.generate_cyclepair_inputs::<Bn254>(
			params.0.qa_pp.as_ref().expect("qa_pp null"), vp, &com_all_w, &qa, &cfg);
		let mut circ = S119Circ::from_nova::<S119Fc>(nova, com_all_w, r_all_w)
			.expect("from_nova err");
		//T934: r_2 = H(tag, C_WE, D) needs a Groth16 pk; a fresh draw
		//stands in for it here (the pins below do not read it).
		let ch = Fr::rand(&mut rng);
		circ.kzg_ch = Some(ch);
		if let Some(p) = probe {
			let prf = <S119Cm as CommitmentScheme<Projective, false>>::prove_with_challenge(
				&params.0.cs1e_pp, ch, &circ.all_w(), &Fr::zero(), None).expect("kzg prf err");
			p(&w_i1, com_all_w, &prf, ch, &params.0.cs1e_pp);
		}
		(circ, rows, vp.hash(&cfg), vp.c[0])
	}

	/// T933-B1 on (C_WE, e_2), T933 s9. com_all_w commits W || E ||
	/// blinds in coefficient order, so the blinds sit on top, from X^L
	/// with L = |W||E|. With one blind o at X^L,
	/// C - [g(s)]_1 == ((e_2 - g(ch)) / ch^L) [s^L]_1 confirms a guess g
	/// of W || E with one MSM. A second blind at X^(L+1) hides it.
	#[test]
	fn test_t933_b1_cwe_guess(){
		use ark_ff::Field;
		use std::ops::Mul;
		let mut hits: Vec<(bool, bool)> = vec![];
		let mut probe = |w: &WitnessFoldPotSuper<Projective>, com: Projective,
			prf: &crate::commitment::kzg::Proof<Projective>, ch: Fr,
			pk: &crate::commitment::kzg::ProverKey<'static, Projective>|{
			let mut we: Vec<Fr> = w.vec_wit.iter()
				.flat_map(|x| x.W.clone()).collect();
			we.extend(w.vec_wit.iter().flat_map(|x| x.E.clone()));
			let l = we.len();
			let s_l = pk.powers_of_g[l];
			let test = |g: &Vec<Fr>| {
				let cg = <S119Cm as CommitmentScheme<Projective, false>>
					::commit(pk, g, &Fr::zero()).unwrap();
				let eg = poly_from_vec(g.clone()).unwrap().evaluate(&ch);
				let o = (prf.eval - eg) * ch.pow([l as u64]).inverse()
					.unwrap();
				com - cg == s_l.mul(o)
			};
			let mut wrong = we.clone();
			wrong[0] += Fr::from(1u32);
			hits.push((test(&we), test(&wrong)));
		};
		let _ = s119_fold_probe(5, Some(&mut probe));
		assert!(hits.len() == 1);
		assert!(!hits[0].0, "T933-B1: C_WE guess test confirms the true W||E");
		assert!(!hits[0].1, "T933-B1: C_WE guess test confirms a wrong guess");
	}

	/// Synthesize one arm on a fresh CS. Returns (num_constraints,
	/// index of the FIRST unsatisfied constraint, None when SAT).
	fn s119_synth(circ: &S119Circ) -> (usize, Option<usize>){
		let cs = ConstraintSystem::<Fr>::new_ref();
		circ.generate_constraints_adv(0, cs.clone(), Fr::zero())
			.expect("gen_cs err");
		//no ConstraintLayer is installed here, so which_is_unsatisfied
		//hands back the bare constraint index as a string (see the
		//map_or_else default in ark-relations constraint_system.rs).
		let idx = cs.which_is_unsatisfied().expect("unsat query err")
			.map(|s| s.parse::<usize>().expect("want a bare index"));
		(cs.num_constraints(), idx)
	}

	/// T941: the decider salt is the passed randf, not a fixed seed.
	/// Two randf values give two mainres_hash values. The salt moves no
	/// constraint: the toy's own known UNSAT row (see S119 ARM 0) is the
	/// same for every randf.
	#[test]
	fn test_t941_randf_salt(){
		use ark_r1cs_std::R1CSVar;
		let circ = s119_fold(5);
		let run = |r: Fr| {
			let cs = ConstraintSystem::<Fr>::new_ref();
			let ret = circ.generate_constraints_adv(0, cs.clone(), r)
				.expect("gen_cs err");
			let salt = ret.val().randf;
			let h = ret.hash(&circ.poseidon_config, cs.clone()).value()
				.expect("hash val");
			let bad = cs.which_is_unsatisfied().expect("unsat query");
			(salt, h, bad)
		};
		let (_, _, bad0) = run(Fr::zero());
		let (f1, h1, bad1) = run(Fr::from(7u32));
		let (f2, h2, bad2) = run(Fr::from(11u32));
		assert!(bad1 == bad0 && bad2 == bad0,
			"T941: randf moves satisfiability: {:?} {:?} {:?}", bad0, bad1, bad2);
		assert_eq!(f1, Fr::from(7u32), "T941: salt is not the passed randf");
		assert_eq!(f2, Fr::from(11u32), "T941: salt is not the passed randf");
		assert_ne!(h1, h2, "T941: mainres_hash ignores randf");
	}

	/// T932W-G G1-prov. True when every witness column of constraint
	/// `row` also occurs in some constraint before `before`.
	fn s932w_pin_reads_digest(circ: &S119Circ, row: usize,
		before: usize) -> bool{
		let cs = ConstraintSystem::<Fr>::new_ref();
		circ.generate_constraints_adv(0, cs.clone(), Fr::zero())
			.expect("gen_cs err");
		cs.finalize();
		let m = cs.to_matrices().expect("matrices null");
		let n_inst = m.num_instance_variables;
		let cols = |r: usize| [&m.a[r], &m.b[r], &m.c[r]].into_iter()
			.flat_map(|lc| lc.iter().map(|(_, i)| *i))
			.filter(|&i| i >= n_inst).collect::<Vec<usize>>();
		let mut seen = std::collections::HashSet::new();
		for r in 0..before { seen.extend(cols(r)); }
		let pin = cols(row);
		!pin.is_empty() && pin.iter().all(|c| seen.contains(c))
	}

	/// Repoint u_i.x[0] at the circuit's CURRENT z_0/z_i so a state
	/// edit does not die at step 5's hash before reaching the pins.
	/// u_i is a decider witness, so a prover can make this same move.
	fn s119_rehash_u_i<GM: GadgetMapper<Fr, S119Lk> + Clone + Debug>(circ: &mut Phase1Circuit<
		Bn254, Bn254PairingVar, ProjectiveG2, Projective, GVar, Projective2, GVar2,
		S119Cm, S119Cm2, S119Cm, S119Lk, GM, false>){
		let sponge = PoseidonSponge::<Fr>::new(&circ.poseidon_config);
		let x0 = circ.U_i.as_ref().expect("U_i null").hash(
			&sponge,
			circ.pp_hash.expect("pp_hash null"),
			circ.i.expect("i null"),
			circ.pc_i,
			circ.z_0.clone().expect("z_0 null"),
			circ.z_i.clone().expect("z_i null"));
		let mut u_i = circ.u_i.clone().expect("u_i null");
		u_i.x[0] = x0;
		circ.u_i = Some(u_i);
	}

	/// S119: the honest Phase 1 statement is SAT, and each shipped pin
	/// rejects its own witness-consistent corruption at its own index.
	#[test]
	fn test_s119_decider_pins_constrain(){
		let n_steps = 5;
		let mut circ = s119_fold(n_steps);
		let cfg = circ.poseidon_config.clone();
		let zi_ok = circ.zi_part2_inst.clone().expect("zi null");
		let z_i_ok = circ.z_i.clone().expect("z_i null");
		let z_0_ok = circ.z_0.clone().expect("z_0 null");
		let u_i_ok = circ.u_i.clone().expect("u_i null");

		//ARM 0 -- the honest fold. If this is not SAT then every UNSAT
		//below is uninterpretable, so it is asserted first.
		//ARM 0 -- the honest fold. Everything up to and including
		//both pins (gen_cs steps 1-6) must be clean. The toy's folded
		//relation still has ONE unsatisfied row of its own, surfacing
		//in step 7's RelaxedR1CS check: circuits_super.rs step 9's
		//base-case `x` public input. That defect predates this test
		//and is independent of the pins -- arming or disarming b_last
		//does not move it. So the control is stated as "the honest
		//failure lies DOWNSTREAM of every pin rejection below", and
		//is checked in the bracket at the end. No magic index.
		assert!(zi_ok.word_id == zi_ok.total_words,
			"toy did not end terminal: word_id {} total_words {}",
			zi_ok.word_id, zi_ok.total_words);
		let (n0, i0) = s119_synth(&circ);
		let i_honest = i0.expect("honest arm is now fully SAT -- the \
			pre-existing step-7 defect is gone, so tighten this \
			control back to asserting None");

		//ARM 1 -- control for the false positive this test exists to
		//rule out: word_id edited alone, z_i[1] left stale. This MUST
		//die at the digest carry, upstream of the terminality pin.
		let mut zi_bad = zi_ok.clone();
		zi_bad.word_id = zi_ok.word_id - Fr::one();
		circ.zi_part2_inst = Some(zi_bad.clone());
		let (n1, i1) = s119_synth(&circ);
		let i_digest = i1.expect("a stale z_i[1] was ACCEPTED");

		//ARM 2 -- the same non-terminal final state, now carried
		//consistently: z_i[1] rehashed and u_i.x[0] repointed. All
		//three are decider witnesses (gen_cs step 2), so this is what
		//a prover can actually present. Only the S106 pin is left to
		//reject it.
		let mut z_i_bad = z_i_ok.clone();
		z_i_bad[1] = zi_bad.hash(&cfg);
		circ.z_i = Some(z_i_bad);
		s119_rehash_u_i(&mut circ);
		let (n2, i2) = s119_synth(&circ);
		let i_term = i2.expect(
			"NON-TERMINAL final state ACCEPTED -- S106 pin is inert");

		//ARM 3 -- honest state restored, z_0[1] moved off the
		//canonical initial state, u_i.x[0] repointed to match. Only
		//the S105b pin reads z_0[1] past step 5.
		circ.zi_part2_inst = Some(zi_ok.clone());
		circ.z_i = Some(z_i_ok.clone());
		circ.u_i = Some(u_i_ok.clone());
		let mut z_0_bad = z_0_ok.clone();
		z_0_bad[1] += Fr::one();
		circ.z_0 = Some(z_0_bad);
		s119_rehash_u_i(&mut circ);
		let (n3, i3) = s119_synth(&circ);
		let i_z0 = i3.expect(
			"MIS-SEEDED z_0 ACCEPTED -- S105b pin is inert");

		//shape identity: the arms differ in witness VALUES only, so
		//the indices above name constraints of one and the same
		//system and are comparable.
		assert!(n0==n1 && n1==n2 && n2==n3,
			"arms are not shape-identical: {} {} {} {}",
			n0, n1, n2, n3);
		//the bracket. Between the digest carry and the z_0 pin the
		//only constraints gen_cs emits are the three terminality
		//equalities, so i_term lands on one of those and nowhere
		//else. i_z0 < i_honest is the ARM 0 control: every pin
		//rejection above fires strictly upstream of the toy's own
		//pre-existing failure, so the pin block is clean when honest.
		assert!(i_digest < i_term && i_term < i_z0
			&& i_z0 < i_honest,
			"rejection not localised: digest {} term {} z0 {} \
			 honest {}", i_digest, i_term, i_z0, i_honest);

		//ARM 4 (T932W-G). The G1 forgery shape on the final state.
		//Word n declares length 0 and acc stays 1. Carried
		//consistently, so only the C5.1 length pin can reject it.
		circ.u_i = Some(u_i_ok.clone());
		circ.z_0 = Some(z_0_ok.clone());
		let mut zi_len = zi_ok.clone();
		zi_len.total_word_len = Fr::zero();
		circ.zi_part2_inst = Some(zi_len.clone());
		let mut z_i_len = z_i_ok.clone();
		z_i_len[1] = zi_len.hash(&cfg);
		circ.z_i = Some(z_i_len);
		s119_rehash_u_i(&mut circ);
		let (n4, i4) = s119_synth(&circ);
		let i_len = i4.expect("last word's length unbound, no C5.1");
		//Localisation first, so a pre-C5.1 tree reports the missing
		//pin and not the G1-prov message.
		assert!(i_term < i_len && i_len < i_z0,
			"length pin not localised, term {} len {} z0 {}",
			i_term, i_len, i_z0);
		//G1-prov. The pin must read the digest-bound witnesses. Each
		//witness column of its row occurs in some row before the
		//digest carry (the Poseidon rows of zi_p2). A pin on a second
		//ZiPartTwoInstVar::from reads fresh columns that no earlier
		//row can contain.
		assert!(s932w_pin_reads_digest(&circ, i_len, i_digest),
			"C5.1 reads witnesses that the digest does not bind");
		//ARM 4b. acc == total == 2, while total_word_segs and
		//subseg_id stay 1. A correct pin accepts it, so the first
		//failure is the honest one. A pin of total_word_len against
		//total_word_segs or subseg_id rejects it.
		circ.u_i = Some(u_i_ok.clone());
		let mut zi_4b = zi_ok.clone();
		zi_4b.total_word_len = Fr::from(2u32);
		zi_4b.accumulated_word_len = Fr::from(2u32);
		circ.zi_part2_inst = Some(zi_4b.clone());
		let mut z_i_4b = z_i_ok.clone();
		z_i_4b[1] = zi_4b.hash(&cfg);
		circ.z_i = Some(z_i_4b);
		s119_rehash_u_i(&mut circ);
		let (n4b, i4b) = s119_synth(&circ);
		assert!(n4 == n0 && n4b == n0,
			"T932W-G arms are not shape-identical");
		assert!(i4b == i0,
			"length pin rejects acc == total == 2, {:?} vs {:?}",
			i4b, i0);
		//ARM 5 (T934 K3). Honest state, z_0[0] or one of z_0[2..] moved off zero,
		//u_i.x[0] repointed. Only K3, right after S105b, reads them past
		//step 5, so the first failure sits between S105b and step 7.
		for k in [0usize, 2, 3, 4, 5]{
			circ.zi_part2_inst = Some(zi_ok.clone());
			circ.z_i = Some(z_i_ok.clone());
			let mut z_0_k3 = z_0_ok.clone();
			z_0_k3[k] += Fr::one();
			circ.z_0 = Some(z_0_k3);
			s119_rehash_u_i(&mut circ);
			let (n5, i5) = s119_synth(&circ);
			assert!(n5 == n0 && i5.map_or(false, |i| i_z0 < i && i < i_honest),
				"K3: z_0[{}] = 1 not rejected after S105b: {:?} (z0 {} honest {})",
				k, i5, i_z0, i_honest);
		}
	}

	// ---------------------------------------------------------------
	// S103 -- the decider must bind the INACTIVE accumulator slots.
	//
	// Vehicle: the same six_root toy as S119, folded with n_circ = 2 and
	// an ALTERNATING pc schedule so both slots hold real folded work.
	// The toy's fixture is n_circ = 1 with pc_i = pc_i1 = 0 hard-coded
	// (sigma_ir1cs.rs gen_six_root_adv, SixRootMapper::build_statement),
	// so the schedule is patched into the statements here -- BEFORE
	// pass 1, because the statement vector is what cmF commits to.
	//
	// WHY NOT THE S119 INDEX BRACKET. S106/S105b sit UPSTREAM of the
	// toy's own pre-existing step-7 unsatisfied row, so a first-index
	// comparison localises them. The S103 block is emitted AFTER step 7
	// -- DOWNSTREAM -- and which_is_unsatisfied() reports only the FIRST
	// unsatisfied row, so that pre-existing row MASKS every S103
	// rejection and honest/corrupt arms report the same index. A test in
	// the S119 style would be green over nothing. This one diffs the
	// FULL unsatisfied-row SET instead.
	// ---------------------------------------------------------------

	/// Fold the six_root toy over `n_circ` slots. `sched[i]` is step i's
	/// pc_i1; step i's pc_i is sched[i-1], with 0 before the first --
	/// the same convention as driver.rs pass_all.
	fn s103_fold(n_steps: usize, n_circ: usize, sched: &[usize])
		-> S119Circ{
		assert_eq!(sched.len(), n_steps, "sched len != n_steps");
		let mut rng = ark_std::test_rng();
		let cfg = poseidon_canonical_config::<Fr>();
		let b_full = false;
		//b_check_lkup=false. The six_root toy's Hab'22 sums CANNOT
		//balance at a terminal step: the circuit counts a dynamic
		//subtable_id=0 query at (0,val) (case 3 of the left sum)
		//while fill_lkup_mvec counts it at (0,0), so every
		//multiplicity stays 0 -- right sum 0, left sum not (S118;
		//see test_s109_hab22_zero_waiver). Folding to a TERMINAL
		//step therefore trips the native assert now that S109 has
		//removed the sum_hab22_right.is_zero() waiver that used to
		//hide it. These tests exercise the DECIDER pins and the
		//slot binding, not the lookup argument, and
		//b_check_lkup=false is what legacy production ships (see
		//the gen_six_root_adv doc comment, S108).
		let (lk, f_circ, mut vec_stmt) =
			gen_six_root_adv::<Fr, Projective, S119Cm, S119Lk, false>(
				n_steps, false);
		//same counter repair as s119_fold, and for the same reason
		//(build_statement's NOTE): without it assert_msg3 kills any
		//fold of >= 2 steps. Local to this test.
		for st in vec_stmt.iter_mut(){
			st.inp_buf[0] = Fr::zero();
			st.oup_buf[0] = Fr::zero();
		}
		//the pc schedule. n_circ_minus_pc follows the fixture's own
		//rule (n_circ - pc_i); it is carried in the statement but no
		//constraint reads it.
		let pc_of = |i: usize| if i==0 {0usize} else {sched[i-1]};
		for i in 0..n_steps{
			vec_stmt[i].pc_i = Fr::from(pc_of(i) as u32);
			vec_stmt[i].pc_i1 = Fr::from(sched[i] as u32);
			vec_stmt[i].n_circ = Fr::from(n_circ as u32);
			vec_stmt[i].n_circ_minus_pc =
				Fr::from(n_circ as u32) - Fr::from(pc_of(i) as u32);
		}
		let vec_f = vec![f_circ.clone(); n_circ];
		let vec_size = vec![f_circ.get_size_f(); n_circ];
		let prep = PreprocessorParamFoldPotSuper::<Projective,
			Projective2, S119Fc, S119Cm, S119Cm2, S119Lk, S119Gm,
			false>::new(cfg.clone(), vec_f.clone(), lk, vec_size,
				b_full);
		let params = S119Nova::preprocess(&mut rng, &prep, 0)
			.expect("preprocess err");
		let fq_bits = <<Projective as CurveGroup>::BaseField
			as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;

		//PASS 1: the cmF hash chain, over the PATCHED statements.
		let zero = Fr::zero();
		let z0_p2 = ZiPartTwoInst::<Fr>::new(zero, zero, &cfg, b_full,
			fq_bits, n_steps);
		let z_0 = [vec![zero, z0_p2.hash(&cfg)],
			vec![zero; 4]].concat();
		let nova0 = S119Nova::init_adv(&params, vec_f.clone(), z_0,
			n_circ, 0, b_full, zero, zero, n_steps, None, 0)
			.expect("init_adv pass1 err");
		let mut hash_cmf = zero;
		for i in 0..n_steps{
			(hash_cmf, _) = nova0.compute_step_hc_cmF(hash_cmf,
				&vec_stmt[i]).expect("hc_cmF err");
		}
		drop(nova0);

		//PASS 2: the real IVC. pc_i / pc_i1 are set per step exactly as
		//driver.rs pass_all does it (driver.rs "nova.pc_i =
		//vea[idx].pc_i").
		//S107 zero seed, same as s119_fold.
		let z0_p2 = ZiPartTwoInst::<Fr>::new(hash_cmf, zero, &cfg,
			b_full, fq_bits, n_steps);
		let z_0 = [vec![zero, z0_p2.hash(&cfg)],
			vec![zero; 4]].concat();
		let mut nova = S119Nova::init_adv(&params, vec_f.clone(), z_0,
			n_circ, 0, b_full, hash_cmf, zero, n_steps, None, 0)
			.expect("init_adv pass2 err");
		for j in 0..n_steps{
			nova.pc_i = Fr::from(pc_of(j) as u32);
			nova.pc_i1 = Fr::from(sched[j] as u32);
			nova.prove_step(&mut rng, vec_stmt[j].to_vec(), None)
				.expect("prove_step err");
		}
		assert_eq!(Fr::from(n_steps as u32), nova.i);

		let (u_i1, w_i1, _r, _cmt) = nova.gen_next_folded()
			.expect("gen_next_folded err");
		let (com_all_w, _qa, r_all_w) = w_i1
			.gen_com_all_w_and_qa_nizk_prf::<Bn254, S119Cm, false>(
				params.0.qa_pp.as_ref().expect("qa_pp null"),
				&params.0.cs1e_pp,
				params.1.qa_vp.as_ref().expect("qa_vp null"),
				&u_i1);
		let mut circ = S119Circ::from_nova::<S119Fc>(nova, com_all_w, r_all_w)
			.expect("from_nova err");
		circ.kzg_ch = Some(Fr::rand(&mut rng)); //T934, as in s119_fold_probe
		circ
	}

	/// EVERY unsatisfied row, not just the first: (num_constraints, set).
	/// which_is_unsatisfied() stops at the first row, which is useless
	/// here (see the note above), so the rows are evaluated directly off
	/// to_matrices() and the assignments.
	fn s103_unsat_rows(circ: &S119Circ) -> (usize, Vec<usize>){
		let (m, z, _) = synth_mats(|cs| { circ.generate_constraints_adv(0, cs,
			Fr::zero()).expect("gen_cs err"); });
		(m.num_constraints, unsat(&m, &z))
	}

	/// Synthesize on a fresh CS: (matrices, z, committed range).
	fn synth_mats(f: impl FnOnce(ConstraintSystemRef<Fr>))
		-> (ark_relations::r1cs::ConstraintMatrices<Fr>, Vec<Fr>, (usize, usize)){
		let cs = ConstraintSystem::<Fr>::new_ref();
		f(cs.clone());
		//REQUIRED before to_matrices(): make_row calls
		//get_index_unchecked, which panics on a SymbolicLc, and the LCs
		//are symbolic until finalize() inlines them. It changes neither
		//num_constraints nor the assignments.
		cs.finalize();
		let m = cs.to_matrices().expect("matrices null");
		//make_row indexes instance variables first (column 0 is the ONE
		//variable) and then witness variables, so z is exactly the two
		//assignment vectors concatenated in that order.
		let g = cs.borrow().expect("cs borrow null");
		let z = [g.instance_assignment.clone(), g.witness_assignment.clone()].concat();
		(m, z, g.committed.unwrap_or((0, 0)))
	}

	/// The rows of `m` that `z` leaves unsatisfied.
	fn unsat(m: &ark_relations::r1cs::ConstraintMatrices<Fr>, z: &[Fr]) -> Vec<usize>{
		let dot = |row: &Vec<(Fr, usize)>| row.iter()
			.map(|(c, i)| *c * z[*i]).sum::<Fr>();
		(0..m.num_constraints)
			.filter(|&r| dot(&m.a[r]) * dot(&m.b[r]) != dot(&m.c[r]))
			.collect::<Vec<usize>>()
	}

	/// S103: at n_circ=2 the decider rejects a swapped INACTIVE-slot
	/// commitment; the same swap on the ACTIVE slot is still accepted,
	/// which measures S126 rather than assuming it.
	#[test]
	fn test_s103_inactive_slot_bound(){
		let n_steps = 5;
		//alternating, so folds land in slots 0,1,0,1,0 and BOTH hold
		//real work. A schedule that never leaves slot 0 would compare
		//dummy against dummy and prove nothing.
		let sched = vec![1usize, 0, 1, 0, 1];
		let circ0 = s103_fold(n_steps, 2, &sched);
		let pci = field_to_usize(&circ0.pc_i);
		assert!(pci < 2, "pc_i {} out of range", pci);
		let inact = 1 - pci;

		//ARM A -- honest control. The toy carries its own pre-existing
		//step-7 unsatisfied row (S120), so this set is NOT empty; it is
		//the baseline every other arm is diffed against.
		let (n_a, bad_a) = s103_unsat_rows(&circ0);
		emit_stdout(format!("S103 arm A honest: {} rows, {} unsat",
			n_a, bad_a.len()));

		//ARM B -- swap cmW on the INACTIVE slot, change nothing else.
		//In light mode cmW is read by no other row (step 7 uses only
		//u, x, W, E; the KZG challenge absorbs it but is recomputed
		//in-circuit from the same value), so any NEW unsatisfied row is
		//attributable to the S103 block alone.
		let mut circ_b = circ0.clone();
		{
			let mut u = circ_b.U_i1.clone().expect("U_i1 null");
			u.vec_inst[inact].cmW = u.vec_inst[inact].cmW
				+ Projective::generator();
			circ_b.U_i1 = Some(u);
		}
		let (n_b, bad_b) = s103_unsat_rows(&circ_b);

		//ARM D -- the SAME swap on the ACTIVE slot. Step 8 is gated out
		//in light mode, and even in full mode it drops cm*
		//(circuits.rs enforce_equal pins only u and x), so this arm
		//must add NOTHING. Two jobs: it is the selector control -- a
		//b_inact inversion would swap B and D -- and it MEASURES the
		//residual S126 hole instead of asserting it.
		let mut circ_d = circ0.clone();
		{
			let mut u = circ_d.U_i1.clone().expect("U_i1 null");
			u.vec_inst[pci].cmW = u.vec_inst[pci].cmW
				+ Projective::generator();
			circ_d.U_i1 = Some(u);
		}
		let (n_d, bad_d) = s103_unsat_rows(&circ_d);

		//shape identity: the arms differ in witness VALUES only, so the
		//row indices name constraints of one and the same system.
		assert!(n_a == n_b && n_b == n_d,
			"arms not shape-identical: {} {} {}", n_a, n_b, n_d);
		let new_b = bad_b.iter().filter(|r| !bad_a.contains(r))
			.collect::<Vec<_>>();
		let new_d = bad_d.iter().filter(|r| !bad_a.contains(r))
			.collect::<Vec<_>>();
		emit_stdout(format!("S103 arm B inactive slot {}: {} NEW unsat \
			rows {:?}; arm D active slot {}: {} NEW", inact,
			new_b.len(), new_b, pci, new_d.len()));
		assert!(bad_a.iter().all(|r| bad_b.contains(r)),
			"arm B lost a baseline unsatisfied row -- the arms are not \
			 comparable");
		assert!(new_b.len() > 0,
			"INACTIVE slot cmW swap ACCEPTED -- the S103 block is inert");
		//ATTRIBUTION: in light mode gen_cs emits, at its very end,
		//the T935 C3 selectors and the S103 block (3n+1 + 75 per slot
		//= 157 at n_circ = 2, reported in the "Step 7b" log line)
		//followed by the S107 cmF-limb pin
		//(4 nonnative limb equalities, measured 473 rows). Steps 8-10
		//are gated out. So every new row must fall in the final
		//`width` indices -- otherwise the rejection came from
		//somewhere else and this test is measuring the wrong thing.
		//157 + 473 = 630 today; asserted loosely as <= 1024 so a
		//gadget-level cost change does not turn this into a tripwire.
		let width = 1024;
		assert!(new_b.iter().all(|&&r| r + width >= n_a),
			"new unsatisfied rows {:?} are NOT inside the last {} rows \
			 of {} -- rejection is not attributable to the S103 block",
			new_b, width, n_a);
		assert_eq!(new_d.len(), 0,
			"ACTIVE slot cmW swap was REJECTED ({} new rows). Step 8 is \
			 light-gated and drops cm*, so this was the S126 control -- \
			 re-derive S126 before trusting it", new_d.len());
	}

	/// S126: the step-8 commitment fold now CONSTRAINS -- an ACTIVE-slot
	/// cmW swap is rejected in full mode, and accepted in light mode.
		#[test]
	fn test_s126_active_slot_bound(){
		//b_light_test is a PROCESS-WIDE RwLock and step 8 lives under
		//`if !b_light_test`, so this test owns the flag for its whole
		//body (hence --test-threads=1) and restores it even on a panic
		//-- otherwise every later test in this binary silently runs in
		//full mode.
		struct LightGuard(bool);
		impl Drop for LightGuard{
			fn drop(&mut self){
				utils::consts::get_global_config().b_light_test = self.0;
			}
		}
		let _guard = LightGuard(
			utils::consts::read_global_config().b_light_test);

		let n_steps = 5;
		let sched = vec![1usize, 0, 1, 0, 1];
		let circ0 = s103_fold(n_steps, 2, &sched);
		let pci = field_to_usize(&circ0.pc_i);
		assert!(pci < 2, "pc_i {} out of range", pci);

		//the SAME one-field corruption as the S103 test's arm D: cmW on
		//the ACTIVE slot. Step 8 is the only block that reads it.
		let mut circ_d = circ0.clone();
		{
			let mut u = circ_d.U_i1.clone().expect("U_i1 null");
			u.vec_inst[pci].cmW = u.vec_inst[pci].cmW
				+ Projective::generator();
			circ_d.U_i1 = Some(u);
		}

		//LIGHT arms -- the control that makes the full-mode delta
		//attributable to the gated block rather than to step 7.
		utils::consts::get_global_config().b_light_test = true;
		let (n_la, bad_la) = s103_unsat_rows(&circ0);
		let (n_ld, bad_ld) = s103_unsat_rows(&circ_d);
		assert_eq!(n_la, n_ld, "light arms not shape-identical");
		let new_ld = bad_ld.iter().filter(|r| !bad_la.contains(r))
			.count();
		assert_eq!(new_ld, 0,
			"light mode REJECTED the ACTIVE-slot swap -- step 8 is then \
			 not the only reader of cmW and the full-mode arm below is \
			 not attributable");

		//FULL arms -- step 8 is built, and the S126 rows in
		//circuits.rs enforce_equal bind the folded commitments.
		utils::consts::get_global_config().b_light_test = false;
		let (n_fa, bad_fa) = s103_unsat_rows(&circ0);
		let (n_fd, bad_fd) = s103_unsat_rows(&circ_d);
		emit_stdout(format!("S126 light: {} rows / {} unsat; full: {} \
			rows / {} unsat", n_la, bad_la.len(), n_fa, bad_fa.len()));
		assert_eq!(n_fa, n_fd, "full arms not shape-identical");
		assert!(n_fa > n_la,
			"full mode built no extra rows -- the gate did not flip");

		//HONEST SATISFIABILITY. The fix adds rows to EVERY point add,
		//and the zero-point cases (u_i.cmE is pinned to zero at :820)
		//are exactly where it could have broken honest proofs. Full
		//mode must not gain unsatisfied rows over the light baseline.
		assert!(bad_fa.len() <= bad_la.len(),
			"HONEST full-mode synthesis has {} unsatisfied rows vs {} \
			 in light -- the S126 enforcements are NOT honestly \
			 satisfiable", bad_fa.len(), bad_la.len());

		let new_fd = bad_fd.iter().filter(|r| !bad_fa.contains(r))
			.collect::<Vec<_>>();
		emit_stdout(format!("S126 full-mode active-slot swap: {} NEW \
			unsat rows {:?}", new_fd.len(), new_fd));
		assert!(new_fd.len() > 0,
			"ACTIVE-slot cmW swap ACCEPTED in full mode -- S126 is NOT \
			 closed");
	}

	// ---------------------------------------------------------------
	// T934 (commit-and-prove decider). Groth16 runs at S119 scale on the
	// Main wrapper of the S119 Phase 1 circuit. Stage 2 runs on an
	// S119-scale CyclePairCircuit whose cyclepair rows are zeros: it is
	// UNSAT elsewhere, so its pins are read off the unsatisfied-row SET.
	// ---------------------------------------------------------------
	type S119Main = MainDeciderCircuit<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Cm, S119Cm2, S119Cm, S119Lk, S119Gm, false>;
	type S119Cp = CyclePairCircuit<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Cm, S119Cm2, S119Cm, S119Lk, S119Gm, false>;
	type G16 = ark_groth16::Groth16<Bn254>;
	use crate::folding::foldpot::batch_proc::CpSnark;

	/// As MainDeciderCircuit::from_nova + finalize(r): res from a
	/// synthesis at the placeholder r = 0, then the native patch.
	fn t934_main(mut c: S119Circ, r: Fr) -> S119Main{
		c.kzg_ch = Some(Fr::zero());
		let res = c.generate_constraints_adv(0, ConstraintSystem::<Fr>::new_ref(),
			Fr::zero()).unwrap().val();
		let all_w = c.all_w();
		let mut m = S119Main{ circ1: c, res, randf: Fr::zero(), res_hash: Fr::zero(), job_id: 0 };
		m.finalize(r, &all_w);
		m
	}

	/// W_1[0] += dw and E_j := Az_j o Bz_j - u_j Cz_j on every slot (dw = 0
	/// repairs the toy's own step-7 row, see S119 ARM 0, and keeps a u = 0
	/// dummy at E = 0). With Some((r, e2)), o_2 is solved so that all_w
	/// still evaluates to e2 at r (T934-2 F1).
	fn t934_forge(circ: &S119Circ, dw: Fr, re: Option<(Fr, Fr)>) -> S119Circ{
		let mut f = circ.clone();
		let ws = &mut f.W_i1.as_mut().unwrap().vec_wit;
		ws[0].W[0] += dw;
		for ((inst, w), r) in f.U_i1.as_ref().unwrap().vec_inst.iter().zip(ws).zip(&f.r1cs) {
			w.E = t1014_residual(r, inst.u, &inst.x, &w.W, &vec![Fr::zero(); w.E.len()]);
		}
		if let Some((r, e2)) = re { t934_resolve_o2(&mut f, r, e2); }
		f
	}

	/// o_2 solved so that all_w() evaluates to e2 at r, and kzg_ch = r (T934-2 F1).
	fn t934_resolve_o2(f: &mut S119Circ, r: Fr, e2: Fr){
		let v = f.all_w();
		let (o1, o2) = f.r_all_w.unwrap();
		f.r_all_w = Some((o1, o2 + (e2 - eval_all_w(&v, r)) / r.pow([v.len() as u64 - 1])));
		f.kzg_ch = Some(r);
	}

	/// ALL_T1014: D = cp_commit(c.cp_w()) and r = H(tag, com_all, D) of c.
	fn t1014_d_r(pk: &ark_groth16::ProvingKey<Bn254>, c: &S119Circ, kappa: Fr) -> (Projective, Fr){
		let d = G16::cp_commit(pk, &c.cp_w(), kappa);
		(d, kzg_ch(&c.poseidon_config, KZG_CH_TAG_S1, c.com_all_w.unwrap(), d))
	}

	/// ALL_T1014: Groth16 proof of c finalized at r under the precommitted D.
	/// Returns (it verifies on [res_hash, total_words], res_hash).
	fn t1014_g16_ok(pk: &ark_groth16::ProvingKey<Bn254>, c: &S119Circ, (d, r): (Projective, Fr),
		kappa: Fr, rng: &mut impl ark_std::rand::RngCore) -> (bool, Fr){
		let m = t934_main(c.clone(), r);
		let (h, n) = (m.res_hash, c.zi_part2_inst.as_ref().unwrap().total_words);
		let p = <G16 as CpSnark<Bn254>>::prove_cp(pk, m, kappa, Some(d), rng).unwrap();
		(G16::verify_proof(&ark_groth16::prepare_verifying_key(&pk.vk), &p, &[h, n]).unwrap(), h)
	}

	/// ALL_T1014 arm (c) on slot j of c, honest (D, r): E_j[0] += 1 with o_2
	/// re-solved. The weighted Horner still gives e2 and the statement is
	/// unchanged, yet Step 7 rejects, Groth16 rejects under the honest D, and
	/// a D over the forged cp_w() moves r.
	fn t1014_forged_e_arm(pk: &ark_groth16::ProvingKey<Bn254>, c: &S119Circ, j: usize,
		(d, r): (Projective, Fr), kappa: Fr, rng: &mut impl ark_std::rand::RngCore){
		let e2 = eval_all_w(&c.all_w(), r);
		let mut f = c.clone();
		f.W_i1.as_mut().unwrap().vec_wit[j].E[0] += Fr::one();
		t934_resolve_o2(&mut f, r, e2);
		let cs = ConstraintSystem::<Fr>::new_ref();
		let eval = f.generate_constraints_adv(0, cs.clone(), Fr::zero()).unwrap().val().eval_w_e;
		assert!(eval == e2 && !cs.is_satisfied().unwrap(),
			"ALL_T1014 (c) slot {}: forged E SAT or weighted Horner != e2", j);
		let (ok, h) = t1014_g16_ok(pk, &f, (d, r), kappa, rng);
		assert!(h == t934_main(c.clone(), r).res_hash && !ok,
			"ALL_T1014 (c) slot {}: statement changed or forged E accepted under the honest D", j);
		assert!(t1014_d_r(pk, &f, kappa).1 != r, "ALL_T1014 (c) slot {}: r does not follow D", j);
	}

	/// T934-2 (+ ruling C check, T934-7 Stage 1). Pre-T934 the same
	/// forgery verifies (baseline red run): r_2 ignored W||E.
	#[test]
	fn test_t934_f1_forgery(){
		use ark_r1cs_std::R1CSVar;
		let circ = t934_forge(&s119_fold(5), Fr::zero(), None);
		assert_eq!(s119_synth(&circ).1, None, "T934-2: repaired honest witness not SAT");
		let (cfg, com, all_w) = (circ.poseidon_config.clone(), circ.com_all_w.unwrap(), circ.all_w());
		let mut rng = ark_std::test_rng();
		let pk = G16::generate_random_parameters_with_reduction(t934_main(circ.clone(), Fr::zero()),
			&mut rng).unwrap();
		let pvk = ark_groth16::prepare_verifying_key(&pk.vk);
		let n = circ.zi_part2_inst.as_ref().unwrap().total_words;
		let v = |p: &ark_groth16::Proof<Bn254>, h: Fr| G16::verify_proof(&pvk, p, &[h, n]).unwrap();
		let kappa = Fr::rand(&mut rng);
		let (d, r2) = t1014_d_r(&pk, &circ, kappa); //ALL_T1014
		assert!(kzg_ch(&cfg, KZG_CH_TAG_S1, d, d) != r2 && kzg_ch(&cfg, KZG_CH_TAG_S2, com, d) != r2,
			"T934: r_2 ignores C_WE/tag");
		let main = t934_main(circ.clone(), r2);
		let cs = ConstraintSystem::<Fr>::new_ref();
		let ret = main.circ1.generate_constraints_adv(0, cs.clone(), Fr::zero()).unwrap();
		assert!(ret.val() == main.res && ret.hash(&cfg, cs.clone()).value().unwrap() == main.res_hash,
			"T934 ruling C: finalize != re-synthesis at r_2");
		let (s0, m) = cs.borrow().unwrap().committed.unwrap();
		let (o1, o2) = circ.r_all_w.unwrap();
		//ALL_T1014: D = cp_w(), with (o_1, o_2) at N - 2 and the u tail at N.
		let (cp, n_aw) = (circ.cp_w(), all_w.len());
		let us = circ.U_i1.as_ref().unwrap().vec_inst.iter().map(|i| i.u).collect::<Vec<_>>();
		assert!(cs.borrow().unwrap().witness_assignment[s0..s0 + m] == cp[..]
			&& cp[n_aw - 2..n_aw] == [o1, o2] && cp[n_aw..n_aw + us.len()] == us[..],
			"T934-7: Stage-1 committed range != cp_w()");
		let h = main.res_hash;
		let p = <G16 as CpSnark<Bn254>>::prove_cp(&pk, main, kappa, Some(d), &mut rng).unwrap();
		assert!(v(&p, h), "T934-2: honest proof rejected");
		assert!(!G16::verify_proof(&pvk, &p, &[h, n + Fr::one()]).unwrap(),
			"T933 K2-min: honest proof verifies at word count n + 1");
		//(a) forged W||E, same statement, honest D_1
		let forged = t934_forge(&circ, Fr::one(), Some((r2, eval_all_w(&all_w, r2))));
		let (fa, fcp) = (forged.all_w(), forged.cp_w());
		assert_eq!(s119_synth(&forged).1, None, "T934-2: forged witness not SAT");
		let mf = t934_main(forged, r2);
		assert_eq!(mf.res_hash, h, "T934-2: forgery changed the statement");
		let pf = <G16 as CpSnark<Bn254>>::prove_cp(&pk, mf, kappa, Some(d), &mut rng).unwrap();
		assert!(!v(&pf, h), "T934-2(a): forged W||E accepted under the honest D_1");
		//(b) D_1 recomputed over the forged W||E moves r_2 off e2
		let r2f = kzg_ch(&cfg, KZG_CH_TAG_S1, com, G16::cp_commit(&pk, &fcp, kappa));
		assert!(r2f != r2 && eval_all_w(&fa, r2f) != eval_all_w(&all_w, r2f),
			"T934-2(b): r_2 does not follow D_1");
		//(c) ALL_T1014: forged E[0], o_2 re-solved
		t1014_forged_e_arm(&pk, &circ, 0, (d, r2), kappa, &mut rng);
	}

	/// ALL_T1014: one Groth16 key from setup on s103 [1,0,1,0,1] (k = 2).
	/// Honest proofs of both s103 fixtures verify under it ([0; 5] has a
	/// u = 0 slot), and arm (c) rejects on slot 0 and slot 1 (slot 1 checks
	/// the weighted Horner offset after the first slot).
	#[test]
	fn test_t1014_g16_s103(){
		let fx = [s103_fold(5, 2, &[1, 0, 1, 0, 1]), s103_fold(5, 2, &[0; 5])]
			.map(|c| t934_forge(&c, Fr::zero(), None));
		let mut rng = ark_std::test_rng();
		let pk = G16::generate_random_parameters_with_reduction(t934_main(fx[0].clone(), Fr::zero()),
			&mut rng).unwrap();
		let kappa = Fr::rand(&mut rng);
		for (f, c) in fx.iter().enumerate() {
			assert!(t1014_g16_ok(&pk, c, t1014_d_r(&pk, c, kappa), kappa, &mut rng).0,
				"ALL_T1014: honest s103 fixture {} rejected", f);
		}
		let dr = t1014_d_r(&pk, &fx[0], kappa);
		(0..2).for_each(|j| t1014_forged_e_arm(&pk, &fx[0], j, dr, kappa, &mut rng));
	}

	/// T933 K2-min: main decider public input 2 is the fold's word count
	/// total_words. Honest SAT; the instance at n - 1 or n + 1 is UNSAT.
	#[test]
	fn test_t933_k2_count_public(){
		let circ = t934_forge(&s119_fold(5), Fr::zero(), None);
		let n = circ.zi_part2_inst.as_ref().unwrap().total_words;
		let cs = ConstraintSystem::<Fr>::new_ref();
		t934_main(circ.clone(), Fr::zero()).generate_constraints(cs.clone()).unwrap();
		assert!(cs.is_satisfied().unwrap(), "T933 K2-min: honest main decider not SAT");
		assert_eq!(cs.borrow().unwrap().instance_assignment.get(2), Some(&n),
			"T933 K2-min: public input 2 != total_words");
		for k in [n - Fr::one(), n + Fr::one()] {
			cs.borrow_mut().unwrap().instance_assignment[2] = k;
			assert!(!cs.is_satisfied().unwrap(), "T933 K2-min: count {} != total_words SAT", k);
		}
		//T3: the equality row is (inst_2 - w) * 1 = 0, and w must be the digest-bound
		//total_words. Moving inst_2 and w together to n + 1 must break a pin.
		let (m, mut z, _) = synth_mats(|cs| t934_main(circ, Fr::zero()).generate_constraints(cs).unwrap());
		let w = (0..m.num_constraints).find_map(|r| match m.a[r].as_slice() {
			[(o, 2), (k, w)] if *o == Fr::one() && *k == -Fr::one() => Some(*w), _ => None })
			.expect("T933 K2-min: no row inst_2 - w");
		z[2] = n + Fr::one();
		z[w] = z[2];
		assert!(!unsat(&m, &z).is_empty(), "T933 K2-min: input 2 is tied to an unbound witness");
	}

	/// T934-5 F1c: the Horner multiplier `one` (value 1, sole B entry of
	/// rows over committed wires) is pinned by a row over {1, one} alone.
	#[test]
	fn test_t934_one_pinned(){
		let (m, z, (s0, k)) = synth_mats(|cs| { s119_fold(5)
			.generate_constraints_adv(0, cs, Fr::zero()).unwrap(); });
		let n_in = m.num_instance_variables;
		let com = n_in + s0..n_in + s0 + k;
		let one = (0..m.num_constraints).filter_map(|r| match m.b[r].as_slice() {
			[(c, i)] if *c == Fr::one() && z[*i] == Fr::one() && *i >= n_in && !com.contains(i)
				&& m.a[r].iter().any(|(_, j)| com.contains(j)) => Some(*i),
			_ => None }).collect::<std::collections::HashSet<usize>>();
		assert_eq!(one.len(), 1, "T934-5: Horner multiplier not unique: {:?}", one);
		let c = *one.iter().next().unwrap();
		let mut z2 = z.clone();
		z2[c] = Fr::from(2u64);
		assert!(unsat(&m, &z2).iter().any(|&r| [&m.a[r], &m.b[r], &m.c[r]].iter()
			.all(|l| l.iter().all(|(_, i)| *i == 0 || *i == c))),
			"T934-5 F1c: witness one = 2 is not rejected by a pin");
	}

	/// Stage-2 fixture: the S119 circuit is both the main decider (res)
	/// and main_circ2; dummy cp_U_i / cp_W_i keep full mode synthesizable.
	fn t934_cp(circ: &S119Circ, res: &Phase1CircuitRetVal<Fr, Projective>) -> S119Cp{
		let (mut c2, z) = (circ.clone(), Fr::zero());
		let l = c2.cp_r1cs.l;
		c2.cp_U_i = Some(CommittedInstance::<Projective2>::dummy(l));
		c2.cp_W_i = Some(Witness::<Projective2>::dummy(c2.cp_r1cs.A.n_cols - 1 - l, c2.cp_r1cs.A.n_rows));
		let inp = CircPubInput{ ch1: res.ch, rc1: res.rc, hash_cmF1: res.hash_cmF,
			kzg_sum1: res.kzg_sum, kzg_all_com_ch1: res.kzg_all_com_ch, eval_w_e1: res.eval_w_e,
			mainres_hash: z, kzg_all_com_ch2: z, eval_w_e2: z, qa_nizk_vkey_hash: z,
			comE2: res.u_i1_0_cmE, comW2: res.u_i1_0_cmW, comF2: res.u_i1_0_cmF,
			kzg_all_com1: res.vec_coms[0] };
		S119Cp{ circ2: Phase2Circuit{ _gm: PhantomData, main_circ: c2,
			cyclepair_inputs: vec![vec![z; 164]; res.vec_coms.len() + 1], job_id: 0 },
			inp, mainres: res.clone(), job_id: 0 }
	}

	/// T934-4 (D4 pin), T934-3 (r_2 mismatch, c5 arm) and T934-7 Stage 2.
	#[test]
	fn test_t934_cp_pins(){
		let circ = s119_fold(5);
		let res = t934_main(circ.clone(), Fr::from(7u64)).res;
		let run = |cp: S119Cp| { let (m, z, r) = synth_mats(|cs| cp.generate_constraints(cs).unwrap());
			(unsat(&m, &z), z, r, m.num_instance_variables) };
		let (base, z, (s0, k), n_in) = run(t934_cp(&circ, &res));
		assert!(z[n_in + s0..n_in + s0 + k] == circ.cp_w()[..],
			"T934-7: Stage-2 committed range != main_circ2 cp_w"); //ALL_T1014
		let grows = |cp: S119Cp| { let b = run(cp).0;
			b.len() > base.len() && base.iter().all(|r| b.contains(r)) };
		let mut cp = t934_cp(&circ, &res);
		cp.inp.kzg_all_com1 = res.vec_coms[1];
		assert!(grows(cp), "T934-4: verifier C_WE != circuit com_all_w accepted");
		let mut bad = res.clone();
		bad.kzg_all_com_ch += Fr::one();
		let mut cp = t934_cp(&circ, &bad);
		cp.inp.kzg_all_com_ch1 = res.kzg_all_com_ch;
		assert!(grows(cp), "T934-3: decider r_2 != verifier r_2 accepted");
	}

	/// B1: every committed E column is read by its Horner row and by the
	/// relaxed-R1CS check (>= 2 rows). ALL_T1014: so is every u and x' column.
	#[test]
	fn test_t934_committed_read(){
		let circ = s119_fold(5);
		let w = &circ.W_i1.as_ref().unwrap().vec_wit;
		let nw = w.iter().map(|x| x.W.len()).sum::<usize>();
		let ne = w.iter().map(|x| x.E.len()).sum::<usize>();
		let (m, _, (s0, k)) = synth_mats(|cs| { circ.generate_constraints_adv(0, cs, Fr::zero()).unwrap(); });
		let c0 = m.num_instance_variables + s0;
		let mut cnt = vec![0usize; k];
		for r in 0..m.num_constraints {
			let cols = [&m.a[r], &m.b[r], &m.c[r]].iter().flat_map(|l| l.iter().map(|(_, i)| *i))
				.filter(|i| (c0..c0 + k).contains(i)).collect::<std::collections::HashSet<usize>>();
			cols.into_iter().for_each(|i| cnt[i - c0] += 1);
		}
		assert!(cnt[nw..nw + ne].iter().all(|&c| c >= 2), "T934 B1: a committed E column is read by its Horner row only");
		assert!(cnt[nw + ne + 2..].iter().all(|&c| c >= 2), "ALL_T1014: a committed u or x' column is read by < 2 rows");
	}

	// ---------------------------------------------------------------
	// T935. C1, Decision 1 and C2 on the step-0 augmented circuit (x and
	// cf_x default to the in-circuit values, so the honest arm is SAT);
	// C3 on the Phase 1 decider. Arms differ in witness values (and in
	// the constant j for C1).
	// ---------------------------------------------------------------
	type T935Aug = crate::folding::foldpot::circuits_super::AugmentedFCircuitFoldPotSuper<
		Projective, Projective2, GVar2, S119Lk, S119Fc, S119Gm, false>;
	/// witness index of stmt[1]: 14 preamble vars + cmF (4) + extra (2) + 1.
	const T935_STMT1: usize = 21;

	/// (matrices, z) of the step-0 augmented circuit of slot j over n_circ
	/// slots, one per arm (j, pc_i): stmt[0] = pc_i, stmt[1] = j.
	fn t935_aug(n_circ: usize, arms: &[(usize, usize)])
		-> Vec<(ark_relations::r1cs::ConstraintMatrices<Fr>, Vec<Fr>)>{
		let mut rng = ark_std::test_rng();
		let (cfg, zero, n_steps) = (poseidon_canonical_config::<Fr>(), Fr::zero(), 5);
		let (lk, f_circ, vec_stmt) =
			gen_six_root_adv::<Fr, Projective, S119Cm, S119Lk, false>(n_steps, false);
		let vec_f = vec![f_circ.clone(); n_circ];
		let prep = PreprocessorParamFoldPotSuper::<Projective, Projective2, S119Fc,
			S119Cm, S119Cm2, S119Lk, S119Gm, false>::new(cfg.clone(), vec_f.clone(),
			lk, vec![f_circ.get_size_f(); n_circ], false);
		let params = S119Nova::preprocess(&mut rng, &prep, 0).expect("preprocess err");
		let fq_bits = <<Projective as CurveGroup>::BaseField
			as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_p2 = ZiPartTwoInst::<Fr>::new(zero, zero, &cfg, false, fq_bits, n_steps);
		let z_0 = [vec![zero, z0_p2.hash(&cfg)], vec![zero; 4]].concat();
		let nova = S119Nova::init_adv(&params, vec_f, z_0, n_circ, 0, false,
			zero, zero, n_steps, None, 0).expect("init_adv err");
		arms.iter().map(|&(j, pc)| {
			let mut st = vec_stmt[0].clone(); //counter repair as in s103_fold
			(st.inp_buf[0], st.oup_buf[0]) = (zero, zero);
			(st.pc_i, st.pc_i1, st.n_circ) = (Fr::from(pc as u32), Fr::from(j as u32), Fr::from(n_circ as u32));
			st.n_circ_minus_pc = st.n_circ - st.pc_i;
			let mut c = T935Aug::empty(&cfg, nova.F[j].clone(), n_circ, j, 0);
			c.F.set_keygen_synth(false);
			(c.pp_hash, c.i, c.i_usize) = (Some(nova.pp_hash), Some(zero), Some(0));
			(c.z_0, c.z_i) = (Some(nova.z_0.clone()), Some(nova.z_i.clone()));
			(c.z0_part2_inst, c.zi_part2_inst) = (Some(nova.z0_part2_inst.clone()), Some(nova.zi_part2_inst.clone()));
			c.external_inputs = Some(st.to_vec());
			let (m, z, _) = synth_mats(|cs| c.generate_constraints(cs).expect("gen_cs err"));
			(m, z)
		}).collect()
	}

	/// T935-1 (C1): circuit 1 rejects the honest witness of a stmt with
	/// stmt[1] = 0, built as circuit 0 (passes the native assert, so it is
	/// consistent everywhere). Pre-T935 j enters no row: SAT.
	#[test]
	fn test_t935_c1_stmt1_is_j(){
		let a = t935_aug(2, &[(1, 0), (0, 0)]);
		let ((m1, z1), (m0, z0)) = (&a[0], &a[1]);
		let col = m1.num_instance_variables + T935_STMT1;
		assert!(unsat(m1, z1).is_empty() && unsat(m0, z0).is_empty(), "T935-1: honest arms not SAT");
		assert!(z1[col] == Fr::one() && z0[col] == Fr::zero(), "T935-1: stmt[1] is not witness {}", T935_STMT1);
		let rows_j = (0..m1.num_constraints).filter(|&r| m1.a[r] != m0.a[r] || m1.b[r] != m0.b[r]
			|| m1.c[r] != m0.c[r]).collect::<Vec<_>>();
		let bad = unsat(m1, z0);
		assert!(m1.num_constraints == m0.num_constraints && rows_j.len() == 1 && bad == rows_j,
			"T935-1: circuit 1 vs stmt[1] = 0: unsat {:?}, rows naming j {:?}", bad, rows_j);
	}

	/// T935-1b (Decision 1): the u_{i+1}.x hashes read the committed
	/// stmt[1]. Circuit 0's witness with stmt[1] reset to 1 meets C1 of
	/// circuit 1 but hashes pc_i1 = 0. Pre-T935 the hashes read a fresh
	/// witness, so this is SAT: the hashed pc_i1 is free.
	#[test]
	fn test_t935_d1_hashed_pc_i1(){
		let a = t935_aug(2, &[(1, 0), (0, 0)]);
		let ((m1, _), (_, z0)) = (&a[0], &a[1]);
		let mut zh = z0.clone();
		zh[m1.num_instance_variables + T935_STMT1] = Fr::one();
		let bad = unsat(m1, &zh);
		emit_stdout(format!("T935-1b: committed 1, hashed 0: unsat {:?}", bad));
		assert!(!bad.is_empty(), "T935-1b: hashed pc_i1 = 0 accepted with committed stmt[1] = 1");
	}

	/// T935-1c (Decision 4): the committed stmt[0] is read in-circuit
	/// (u_i.x hash and pc_i selects; M6 restores both fresh witnesses).
	#[test]
	fn test_t935_d4_hashed_pc_i(){
		let a = t935_aug(2, &[(0, 1)]);
		let (m, z) = &a[0];
		let col = m.num_instance_variables + T935_STMT1 - 1;
		assert!(unsat(m, z).is_empty(), "T935-1c: honest arm not SAT");
		assert!(z[col] == Fr::one() && z[col + 1] == Fr::zero(), "T935-1c: stmt[0] is not witness {}", T935_STMT1 - 1);
		let mut zt = z.clone();
		zt[col] = Fr::zero();
		let bad = unsat(m, &zt);
		emit_stdout(format!("T935-1c: committed 0, hashed 1: unsat {:?}", bad));
		assert!(!bad.is_empty(), "T935-1c: committed stmt[0] = 0 accepted with hashed pc_i = 1");
	}

	/// T935-2 (C2): pc_i = n_circ and n_circ + 5 select no slot and fail
	/// exactly one row, the sel_sum row. n_circ = 1 is the Stage-2 shape.
	#[test]
	fn test_t935_c2_pc_i_range(){
		for n in [1usize, 2]{
			let a = t935_aug(n, &[(0, 0), (0, n), (0, n + 5)]);
			let m = &a[0].0;
			assert!(a.iter().all(|x| x.0.num_constraints == m.num_constraints), "T935-2: arms not shape-identical");
			assert!(unsat(m, &a[0].1).is_empty(), "T935-2: honest arm not SAT");
			let (b1, b2) = (unsat(m, &a[1].1), unsat(m, &a[2].1));
			assert!(b1.len() == 1 && b1 == b2,
				"T935-2: n_circ {}: pc_i = n_circ unsat {:?}, pc_i = n_circ + 5 unsat {:?}", n, b1, b2);
		}
	}

	/// b_light_test guard, as in test_s126: restored on drop.
	struct T935Light(bool);
	impl Drop for T935Light{
		fn drop(&mut self){ utils::consts::get_global_config().b_light_test = self.0; }
	}

	/// T935-3 (C3, TASK s7.3 test 1) arm: n_circ = 1, pc_N = 1, u_i.x[0]
	/// rehashed. Returns the number of NEW unsatisfied rows.
	fn t935_c3_n1_new() -> usize{
		let c0 = s119_fold(5);
		let mut c1 = c0.clone();
		c1.pc_i = Fr::one();
		s119_rehash_u_i(&mut c1);
		let ((n0, b0), (n1, b1)) = (s103_unsat_rows(&c0), s103_unsat_rows(&c1));
		assert_eq!(n0, n1, "T935-3: arms not shape-identical");
		let new = b1.iter().filter(|r| !b0.contains(r)).count();
		emit_stdout(format!("T935-3 light={}: {} rows, {} honest unsat, {} new",
			utils::consts::read_global_config().b_light_test, n0, b0.len(), new));
		new
	}

	/// T935-3, light (the default): no row past step 5 reads pc_i, so
	/// only C3 can reject pc_N = 1 at n_circ = 1.
	#[test]
	fn test_t935_c3_pc_n_n1(){
		assert!(utils::consts::read_global_config().b_light_test, "T935-3: needs light mode");
		assert!(t935_c3_n1_new() > 0, "T935-3: pc_N = 1 at n_circ = 1 accepted (light)");
	}

	/// T935-3, full: step 8 rejects it too (its challenge absorbs u_i),
	/// so more rows fail than the one light-mode C3 row.
	/// 17M rows: next to test_s126 in the parallel lib run it OOMs at
	/// 90 GB, so run it alone with --ignored.
	#[test]
	#[ignore]
	fn test_t935_c3_pc_n_n1_full(){
		let _g = T935Light(utils::consts::read_global_config().b_light_test);
		utils::consts::get_global_config().b_light_test = false;
		assert!(t935_c3_n1_new() >= 2, "T935-3: step 8 does not reject pc_N = 1 (full)");
	}

	/// T935-4 (TASK s7.3 test 2): n_circ = 2, pc_N = 2, light. UNSAT before
	/// T935 (S103: every slot reads inactive). Now it also fails the C3
	/// row, the one row an in-range wrong pc_N leaves intact.
	#[test]
	fn test_t935_c3_pc_n_n2(){
		assert!(utils::consts::read_global_config().b_light_test, "T935-4: needs light mode");
		let c0 = s103_fold(5, 2, &[1, 0, 1, 0, 1]);
		let pci = field_to_usize(&c0.pc_i);
		let (n0, b0) = s103_unsat_rows(&c0);
		let new = |pc: usize| {
			let mut c = c0.clone();
			c.pc_i = Fr::from(pc as u32);
			s119_rehash_u_i(&mut c);
			let (n, b) = s103_unsat_rows(&c);
			assert_eq!(n, n0, "T935-4: arms not shape-identical");
			b.into_iter().filter(|r| !b0.contains(r)).collect::<Vec<_>>()
		};
		let (out, wrong) = (new(2), new(1 - pci));
		let c3 = out.iter().filter(|r| !wrong.contains(r)).collect::<Vec<_>>();
		emit_stdout(format!("T935-4: pc_N = 2: {} new rows, {} not shared with pc_N = {}: {:?}",
			out.len(), c3.len(), 1 - pci, c3));
		assert!(!out.is_empty(), "T935-4: pc_N = 2 accepted");
		assert_eq!(c3.len(), 1, "T935-4: pc_N = 2 does not fail one C3 row");
	}

	// ---------------------------------------------------------------
	// T931 (TASK_T931 s7). Stage 2 = FoldPairMapper in full mode. Rows
	// come from the S119 Stage-1 fold through the driver.rs:3547 encoder.
	// Arms differ in witness values only (shape asserted), so rows compare.
	// ---------------------------------------------------------------
	use crate::folding::nova::traits::NovaR1CS;
	use crate::folding::foldpot::{
		cyclepair::cp_io_len,
		sigma_cyclepair::{create_sigma_fold_pair, FoldPairMapper,
			tests_sigma_cyclepair::{Fq12, t931_enc, t931_pack4, t931_rechain,
				t931_row, t931_stmt}},
	};
	use ark_bn254::Fq;
	type T931Gm = FoldPairMapper<Fr, S119Lk>;
	type T931Fc = SigmaIR1CS_Inst<Fr, Projective, S119Cm, S119Lk, T931Gm, false>;
	type T931Nova = FoldPotSuper<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, T931Fc, S119Cm, S119Cm2,
		S119Cm, S119Lk, T931Gm, false>;
	type T931Circ = Phase1Circuit<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Cm, S119Cm2, S119Cm, S119Lk, T931Gm, false>;
	type T931Cp = CyclePairCircuit<Bn254, Bn254PairingVar, ProjectiveG2,
		Projective, GVar, Projective2, GVar2, S119Cm, S119Cm2, S119Cm, S119Lk, T931Gm, false>;
	type T931Aug = crate::folding::foldpot::circuits_super::AugmentedFCircuitFoldPotSuper<
		Projective, Projective2, GVar2, S119Lk, T931Fc, T931Gm, false>;
	const T931_FQ: usize = 254;

	/// T931: Stage-2 params and the step-0 nova over n rows (driver.rs
	/// driver2: one FoldPair circuit, empty table, z_0 canonical, ch = rc = 0).
	macro_rules! t931_nova { ($rng: expr, $n: expr) => {{
		let (cfg, zero) = (poseidon_canonical_config::<Fr>(), Fr::zero());
		let f = create_sigma_fold_pair::<Fr, Projective, S119Cm, S119Lk, false>(1, cfg.clone());
		let prep = PreprocessorParamFoldPotSuper::<Projective, Projective2, T931Fc,
			S119Cm, S119Cm2, S119Lk, T931Gm, false>::new(cfg.clone(), vec![f.clone()],
			Arc::new(S119Lk::new(vec![])), vec![f.get_size_f()], true);
		let params = T931Nova::preprocess($rng, &prep, 0).expect("preprocess err");
		let z0 = ZiPartTwoInst::<Fr>::new(zero, zero, &cfg, true, T931_FQ, $n);
		let nova = T931Nova::init_adv(&params, vec![f], [vec![zero, z0.hash(&cfg)],
			vec![zero; 4]].concat(), 1, 0, true, zero, zero, $n, None, 0)
			.expect("init_adv err");
		(params, nova)
	}}}

	/// T931: Stage-2 fold over rows (one row per step), then its Phase 1
	/// circuit (driver.rs from_nova path).
	fn t931_fold2(rows: &[Vec<Fr>]) -> T931Circ{
		let mut rng = ark_std::test_rng();
		let (params, mut nova) = t931_nova!(&mut rng, rows.len());
		for (j, r) in rows.iter().enumerate(){
			nova.prove_step(&mut rng, t931_stmt(r, j + 1, rows.len()), None)
				.expect("prove_step err");
		}
		let (u, w, _, _) = nova.gen_next_folded().expect("gen_next_folded err");
		let (com, _, r) = w.gen_com_all_w_and_qa_nizk_prf::<Bn254, S119Cm, false>(
			params.0.qa_pp.as_ref().expect("qa_pp null"), &params.0.cs1e_pp,
			params.1.qa_vp.as_ref().expect("qa_vp null"), &u);
		T931Circ::from_nova::<T931Fc>(nova, com, r).expect("from_nova err")
	}

	/// T931: the cp decider over (Stage-1 main, Stage-2 circuit, rows), with
	/// every public input honest (driver.rs CircPubInput + set_kzg_ch).
	fn t931_cp(main: &S119Main, c2: &T931Circ, rows: &[Vec<Fr>], vk: Fr) -> T931Cp{
		let (res, r) = (&main.res, Fr::from(11u64));
		let mut c2 = c2.clone();
		c2.kzg_ch = Some(r);
		let u0 = c2.U_i1.as_ref().unwrap().vec_inst[0].clone();
		let inp = CircPubInput{ ch1: res.ch, rc1: res.rc, hash_cmF1: res.hash_cmF,
			kzg_sum1: res.kzg_sum, kzg_all_com_ch1: res.kzg_all_com_ch, eval_w_e1: res.eval_w_e,
			mainres_hash: main.res_hash, kzg_all_com_ch2: r, eval_w_e2: eval_all_w(&c2.all_w(), r),
			qa_nizk_vkey_hash: vk, comE2: u0.cmE, comW2: u0.cmW, comF2: u0.cmF,
			kzg_all_com1: res.vec_coms[0] };
		T931Cp{ circ2: Phase2Circuit{ _gm: PhantomData, main_circ: c2,
			cyclepair_inputs: rows.to_vec(), job_id: 0 }, inp, mainres: res.clone(), job_id: 0 }
	}

	/// T931: (num_constraints, unsat rows) of the cp decider.
	fn t931_cp_unsat(main: &S119Main, c2: &T931Circ, rows: &[Vec<Fr>], vk: Fr)
		-> (usize, Vec<usize>){
		let (m, z, _) = synth_mats(|cs| t931_cp(main, c2, rows, vk)
			.generate_constraints(cs).expect("gen_cs err"));
		(m.num_constraints, unsat(&m, &z))
	}

	/// T931 T-8 / T-9 forgery: fake C_WE (a_0 += G). m = 0 keeps every gt,
	/// so row 0 is invalid (T-8, gt2_0 = (prod_(j>=1) e(a_j,b_j))^-1);
	/// m = 1 re-chains row 0 (valid) so row 1 is the invalid one (T-9).
	/// The Stage-1 main res carries a_0', so every light pin holds.
	fn t931_forged(m: usize) -> (S119Main, T931Circ, Vec<Vec<Fr>>, Fr){
		use ark_r1cs_std::R1CSVar;
		let (circ, mut rows, vk, b0) = s119_fold_rows(5, None);
		let a0 = circ.com_all_w.unwrap() + Projective::generator();
		rows[0][60..75].copy_from_slice(&t931_enc(&a0));
		if m == 1 {
			let g = t931_enc(&Bn254::pairing(a0, b0).0);
			rows[0][100..160].copy_from_slice(&g);
			rows[1][..60].copy_from_slice(&g);
		}
		t931_rechain(&mut rows, (Fr::zero(), Fr::zero()));
		let mut main = t934_main(circ, Fr::from(7u64));
		main.res.vec_coms[0] = a0;
		let cs = ConstraintSystem::<Fr>::new_ref();
		main.res_hash = Phase1CircuitRet::from(&main.res, &cs)
			.hash(&main.circ1.poseidon_config, cs).value().unwrap();
		let c2 = t931_fold2(&rows);
		(main, c2, rows, vk)
	}

	/// T931 P2, P3 (+ T-12b) and S105b-full on the cp decider, light. The
	/// honest Stage-2 fixture is SAT. Each arm moves one state field and
	/// carries it consistently (digest rehashed, u_i.x[0] repointed), so
	/// only its pin can reject. Baseline: the P2, P3, T-12b arms are SAT.
	#[test]
	fn test_t931_cp_pins(){
		let (circ, rows, vk, _) = s119_fold_rows(5, None);
		let main = t934_main(circ, Fr::from(7u64));
		let c2 = t931_fold2(&rows);
		let cfg = c2.poseidon_config.clone();
		let (n0, b0) = t931_cp_unsat(&main, &c2, &rows, vk);
		emit_stdout(format!("T931 T-13 cp decider (light, 5 rows): {} cs", n0));
		assert!(b0.is_empty(), "T931: honest cp decider not SAT, {} rows {:?}",
			b0.len(), &b0[..b0.len().min(8)]);
		assert!(c2.cp_r1cs.check_relaxed_instance_relation(c2.cp_W_i.as_ref().unwrap(),
			c2.cp_U_i.as_ref().unwrap()).is_ok(), "T931: honest cp_U_n not satisfying");
		let run = |c: &T931Circ| { let (n, b) = t931_cp_unsat(&main, c, &rows, vk);
			assert_eq!(n, n0, "T931: arms not shape-identical"); b.len() };
		//z_n arms: f edits z_n.to_vec(), the rest is carried
		let zn = |f: &dyn Fn(&mut Vec<Fr>)| {
			let mut c = c2.clone();
			let mut v = c.zi_part2_inst.as_ref().unwrap().to_vec();
			f(&mut v);
			let zi = ZiPartTwoInst::<Fr>::from_vec(&v, T931_FQ);
			let mut z_i = c.z_i.clone().unwrap();
			z_i[1] = zi.hash(&cfg);
			(c.zi_part2_inst, c.z_i) = (Some(zi), Some(z_i));
			s119_rehash_u_i(&mut c);
			run(&c)
		};
		let bump = |k: usize| move |v: &mut Vec<Fr>| { let j = v.len() - k; v[j] += Fr::one(); };
		let (p2a, p2b, p3) = (zn(&bump(17)), zn(&bump(16)), zn(&bump(15)));
		//T-12b: last gt2 = [0]_T with coordinate 0 encoded as 1 + q. Every
		//limb < 2^55 and the limbs reduce to the same Fq, so the chain stays
		//consistent; only the endpoint pin sees the other encoding.
		let x = num_bigint::BigUint::from(Fq::MODULUS) + 1u32;
		let mask = (num_bigint::BigUint::from(1u32) << 55) - 1u32;
		let mut nc = t931_enc(&Fq12::one());
		for t in 0..5 { nc[t] = Fr::from((&x >> (55 * t)) & &mask); }
		assert!(f1_limbs_to_f2::<Fr, Fq>(&nc[..5].to_vec()) == Fq::one()
			&& nc[..5] != t931_enc(&Fq12::one())[..5], "T931 T-12b: bad encoding");
		let g_nc = t931_pack4(&nc);
		let p3nc = zn(&|v: &mut Vec<Fr>| { let j = v.len() - 15; v[j..].copy_from_slice(&g_nc); });
		//S105b-full: z_0's g[0] moved, z_0[1] rehashed
		let s105 = {
			let mut c = c2.clone();
			let mut v = ZiPartTwoInst::<Fr>::new(Fr::zero(), Fr::zero(), &cfg, true,
				T931_FQ, rows.len()).to_vec();
			let j = v.len() - 15;
			v[j] += Fr::one();
			let mut z_0 = c.z_0.clone().unwrap();
			z_0[1] = ZiPartTwoInst::<Fr>::from_vec(&v, T931_FQ).hash(&cfg);
			c.z_0 = Some(z_0);
			s119_rehash_u_i(&mut c);
			run(&c)
		};
		emit_stdout(format!("T931 cp pins, new unsat rows: P2 hc_a {} hc_b {} | P3 g {} \
			T-12b {} | S105b z_0.g {}", p2a, p2b, p3, p3nc, s105));
		assert_eq!((p2a, p2b, p3, p3nc, s105), (1, 1, 1, 2, 1),
			"T931 (P2 hc_a, P2 hc_b, P3, T-12b, S105b) rows off");
	}

	/// T931: step-0 Stage-2 augmented circuit, one synthesis per arm
	/// (row, cp_U_0, cp_u_0.cmW, unfold). x, cf_x, cp_x default to the
	/// in-circuit values; unfold sets cp_x = H(dummy cp_U_0), the value the
	/// baseline prover sends at i = 0 (row 0 left out of cp_U_1).
	fn t931_aug(arms: &[(Vec<Fr>, Option<CommittedInstance<Projective2>>, Option<Projective2>, bool)])
		-> Vec<(ark_relations::r1cs::ConstraintMatrices<Fr>, Vec<Fr>)>{
		let mut rng = ark_std::test_rng();
		let (cfg, zero) = (poseidon_canonical_config::<Fr>(), Fr::zero());
		let (_, nova) = t931_nova!(&mut rng, 1);
		let cp_x0 = CommittedInstance::<Projective2>::dummy(cp_io_len())
			.hash_cyclefold(&PoseidonSponge::<Fr>::new(&cfg), nova.pp_hash);
		arms.iter().map(|(row, cp_u, cm_w, unfold)| {
			let mut c = T931Aug::empty(&cfg, nova.F[0].clone(), 1, 0, 0);
			c.F.set_keygen_synth(false);
			(c.pp_hash, c.i, c.i_usize) = (Some(nova.pp_hash), Some(zero), Some(0));
			(c.z_0, c.z_i) = (Some(nova.z_0.clone()), Some(nova.z_i.clone()));
			(c.z0_part2_inst, c.zi_part2_inst) = (Some(nova.z0_part2_inst.clone()),
				Some(nova.zi_part2_inst.clone()));
			(c.external_inputs, c.cp_U_i, c.cp_u_i_cmW) = (Some(t931_stmt(row, 1, 1)),
				cp_u.clone(), *cm_w);
			if *unfold { c.cp_x = Some(cp_x0); }
			let (m, z, _) = synth_mats(|cs| c.generate_constraints(cs).expect("gen_cs err"));
			(m, z)
		}).collect()
	}

	/// T931 T-8 local and T-11 (O1), T-9 local (O2) and T-12a (pack4 range)
	/// on the step-0 Stage-2 augmented circuit. k0 = column of cp_u_0.cmW. A hybrid
	/// takes one arm's prefix and another's suffix from k0 - 160 (on the
	/// baseline the 160 fresh cp_u_i.x copies, now cyclefold columns that
	/// no row of the step reads) plus its cp_x. Baseline: T-11 and every
	/// hybrid are SAT, and no CyclePair row reads a statement column.
	#[test]
	fn test_t931_wrapper_cp(){
		let mut rng = ark_std::test_rng();
		let zero = Fr::zero();
		let (a, b) = (Projective::rand(&mut rng), ProjectiveG2::rand(&mut rng));
		let row = t931_row(Fq12::one(), a, b, (zero, zero));
		//T-9 tuple (gt1, O, b, gt1): a valid CyclePair, not this row
		let row_o = t931_row(Fq12::one(), Projective::zero(), b, (zero, zero));
		//T-12a: one gt2 group re-split, a limb >= 2^55, same pack4 value
		let mut row_p = row.clone();
		let k = (0..15).find(|&k| row[100 + 4 * k + 1] != zero).unwrap();
		row_p[100 + 4 * k] += Fr::from(1u64 << 55);
		row_p[100 + 4 * k + 1] -= Fr::one();
		assert_eq!(t931_pack4(&row_p[100..160]), t931_pack4(&row[100..160]));
		let mut cp_bad = CommittedInstance::<Projective2>::dummy(cp_io_len());
		cp_bad.u = Fq::one();
		let arms = t931_aug(&[(row.clone(), None, None, false),
			(row.clone(), None, Some(Projective2::generator()), false),
			(row.clone(), Some(cp_bad), None, false), (row_o, None, None, false),
			(row_p, None, None, false), (row.clone(), None, None, true)]);
		let (m, za) = (&arms[0].0, &arms[0].1);
		let n_in = m.num_instance_variables;
		emit_stdout(format!("T931 T-13 Stage-2 augmented step: cs {}, witness {}",
			m.num_constraints, m.num_witness_variables));
		assert!(arms.iter().all(|x| x.0.num_constraints == m.num_constraints) && n_in == 4,
			"T931: arms not shape-identical");
		assert!(unsat(m, za).is_empty(), "T931: honest Stage-2 step 0 not SAT");
		let k0 = (n_in..za.len()).find(|&i| za[i] != arms[1].1[i]).unwrap();
		let cols = |r: usize| [&m.a[r], &m.b[r], &m.c[r]].into_iter()
			.flat_map(|l| l.iter().map(|(_, i)| *i)).collect::<Vec<usize>>();
		let in_cp = |r: usize| cols(r).iter().any(|&c| c >= k0);
		let hyb = |p: &Vec<Fr>, s: &Vec<Fr>| {
			let mut h = [&p[..k0 - 160], &s[k0 - 160..]].concat();
			h[n_in - 1] = s[n_in - 1];
			unsat(m, &h)
		};
		//T-11: cp_U_0 != dummy, everything else honest
		let n11 = unsat(m, &arms[2].1).len();
		//T-8 local: u_1.x[2] = H(cp_U_0), so row 0 never enters cp_U_1
		let n8 = unsat(m, &arms[5].1).len();
		//T-9 by variable index: a CyclePair row reads every statement cp column
		let stmt = t931_stmt(&row, 1, 1);
		let map = FoldPairMapper::<Fr, S119Lk>{ _f: PhantomData, _lk: PhantomData,
			poseidon_config: poseidon_canonical_config::<Fr>(), job_id: 0 }
			.gen_statement_structure(0).4;
		let mut read = vec![false; za.len()];
		for r in (0..m.num_constraints).filter(|&r| in_cp(r)){
			for c in cols(r){ read[c] = true; }
		}
		assert!(map[..160].iter().all(|&j| za[n_in + 20 + j] == stmt[j]),
			"T931: statement columns not at 20 + idx");
		let n_unread = map[..160].iter().filter(|&&j| !read[n_in + 20 + j]).count();
		//hybrids: control (same row, other cmW), T-9 row, T-12a statement
		let ctl = hyb(za, &arms[1].1);
		let h9 = hyb(za, &arms[3].1);
		let d12 = unsat(m, &arms[4].1);
		let h12 = hyb(&arms[4].1, za);
		emit_stdout(format!("T931 wrapper: k0 {} | T-8 {} | T-11 {} | T-9 unread stmt cols {} \
			hybrid {} (control {}) | T-12a direct {} hybrid {}", k0, n8, n11, n_unread,
			h9.len(), ctl.len(), d12.len(), h12.len()));
		assert!(ctl.is_empty(), "T931: hybrid control not SAT {:?}", ctl);
		assert_eq!(n8, 1, "T931 T-8: step 0 accepted u_1.x[2] = H(cp_U_0), row 0 unfolded");
		assert_eq!(n11, 1, "T931 T-11: cp_U_0 != dummy not rejected by one pin row");
		assert_eq!(n_unread, 0, "T931 T-9: folded cp_u_i.x is not the statement vars");
		assert!(!h9.is_empty() && h9.iter().all(|&r| in_cp(r)),
			"T931 T-9: folded tuple != statement row accepted {:?}", h9);
		assert!(!d12.is_empty() && d12.iter().all(|&r| in_cp(r)),
			"T931 T-12a: statement limb >= 2^55 not rejected by the cp absorb {:?}", d12);
		assert!(!h12.is_empty() && h12.iter().all(|&r| in_cp(r)),
			"T931 T-12a: limb >= 2^55 accepted with an in-range folded copy {:?}", h12);
	}

	/// T931 T-8 (O1) / T-9 (O2), native (TASK s7.8 (b)): the folded
	/// (cp_W_n, cp_U_n) fails the CyclePair relaxed R1CS, while the light
	/// cp decider (every pin) accepts the forgery. Baseline: row 0 is not
	/// folded, so T-8 passes the relaxed check.
	#[test]
	fn test_t931_t8_t9_native(){
		let mut res = vec![];
		for m in [0usize, 1]{
			let (main, c2, rows, vk) = t931_forged(m);
			let ok = c2.cp_r1cs.check_relaxed_instance_relation(
				c2.cp_W_i.as_ref().unwrap(), c2.cp_U_i.as_ref().unwrap()).is_ok();
			let light = t931_cp_unsat(&main, &c2, &rows, vk).1;
			emit_stdout(format!("T931 T-{}: relaxed R1CS ok {} | light unsat {}",
				8 + m, ok, light.len()));
			res.push((ok, light.len()));
		}
		//informational: the light pins accept both forgeries (0 rows expected)
		emit_stdout(format!("T931 T-8/T-9 light unsat rows: {:?}", res));
		assert!(!res[0].0, "T931 T-8: row 0 not folded, (cp_W_n, cp_U_n) satisfied");
		assert!(!res[1].0, "T931 T-9: (cp_W_n, cp_U_n) satisfied");
	}

	/// T931 T-8 / T-9 in-circuit (TASK s7.8 (b)), b_light_test = false:
	/// the gated cp_U_n checks reject the forgery. Full decider: run alone
	/// with --ignored (jet1tb, T935-3 full pattern).
	fn t931_full(m: usize){
		let _g = T935Light(utils::consts::read_global_config().b_light_test);
		utils::consts::get_global_config().b_light_test = false;
		let (circ, rows, vk, _) = s119_fold_rows(5, None);
		let main = t934_main(circ, Fr::from(7u64));
		let (n_h, hon) = t931_cp_unsat(&main, &t931_fold2(&rows), &rows, vk);
		let (main, c2, rows, vk) = t931_forged(m);
		let (n, bad) = t931_cp_unsat(&main, &c2, &rows, vk);
		emit_stdout(format!("T931 T-{} full: honest {} rows, {} unsat; forged {} rows, {} unsat",
			8 + m, n_h, hon.len(), n, bad.len()));
		assert!(bad.iter().any(|x| !hon.contains(x)),
			"T931 T-{}: forged Stage 2 accepted (full)", 8 + m);
	}
	#[test]
	#[ignore]
	fn test_t931_t8_full(){ t931_full(0) }
	#[test]
	#[ignore]
	fn test_t931_t9_full(){ t931_full(1) }

	// ---------------------------------------------------------------
	// T934 K4 (pp_hash a decider constant) and F71 (Stage-2 pp_hash
	// covers the CyclePair R1CS dims and key).
	// ---------------------------------------------------------------
	/// ALL_T1014: (hits inside W', hits outside W') of v in the witness
	/// vector w, with W' the first |W| entries of the committed range at s0.
	/// A step-circuit wire that is v in every instance is u v in W, so
	/// W' = W/u holds v. No other witness may.
	fn t1014_pp_hits(w: &[Fr], s0: usize, wit: &WitnessFoldPotSuper<Projective>, v: Fr) -> (usize, usize){
		let wp = s0..s0 + wit.vec_wit.iter().map(|x| x.W.len()).sum::<usize>();
		let (a, b): (Vec<usize>, Vec<usize>) = (0..w.len()).filter(|&i| w[i] == v).partition(|i| wp.contains(i));
		(a.len(), b.len())
	}

	/// T934 K4, light: the matrices follow pp_hash and no witness outside
	/// W' holds it (ALL_T1014). The cp decider's own copy (Step 5) is gated
	/// out in light mode (R8b covers it).
	#[test]
	fn test_t934_k4_pp_hash_const(){
		let circ = s119_fold(5);
		let res = t934_main(circ.clone(), Fr::from(7u64)).res;
		let x = circ.pp_hash.unwrap();
		let with = |h: Fr| { let mut c = circ.clone(); c.pp_hash = Some(h); c };
		let main = |h: Fr| synth_mats(|cs| { with(h).generate_constraints_adv(0, cs, Fr::zero()).unwrap(); });
		let cp = |h: Fr| synth_mats(|cs| t934_cp(&with(h), &res).generate_constraints(cs).unwrap());
		for (name, (mx, z, (s0, _)), my) in [("main", main(x), main(x + Fr::one()).0),
			("cp", cp(x), cp(x + Fr::one()).0)] {
			emit_stdout(format!("T934 K4 {}: cs {}, witness {}", name, mx.num_constraints, mx.num_witness_variables));
			assert!(mx != my, "T934 K4 {}: pp_hash X and X + 1 give the same matrices", name);
			let (inw, out) = t1014_pp_hits(&z[mx.num_instance_variables..], s0, circ.W_i1.as_ref().unwrap(), x);
			emit_stdout(format!("T934 K4 {}: pp_hash in {} W' wires, {} other witnesses", name, inw, out));
			assert_eq!(out, 0, "T934 K4 {}: a witness outside W' holds pp_hash", name);
		}
	}

	/// T934 K4 (R8, jet1tb, run alone with --ignored): full-mode main
	/// decider, Groth16 key at pp_hash X. A proof of an IVC folded under
	/// X + 1 fails; the X/X control verifies. Baseline: both verify.
	#[test]
	#[ignore]
	fn test_t934_k4_g16_full(){
		let _g = T935Light(utils::consts::read_global_config().b_light_test);
		utils::consts::get_global_config().b_light_test = false;
		let fold = |pp: Option<Fr>| t934_forge(&s119_fold_pp(5, None, pp).0, Fr::zero(), None);
		let circ = fold(None);
		let circ_y = fold(Some(circ.pp_hash.unwrap() + Fr::one()));
		let sat = |c: &S119Circ| { let cs = ConstraintSystem::<Fr>::new_ref();
			t934_main(c.clone(), Fr::zero()).generate_constraints(cs.clone()).unwrap();
			cs.is_satisfied().unwrap() };
		assert!(sat(&circ) && sat(&circ_y), "T934 K4: honest full main decider (X or X + 1) not SAT");
		let mut rng = ark_std::test_rng();
		let pk = G16::generate_random_parameters_with_reduction(t934_main(circ.clone(), Fr::zero()),
			&mut rng).unwrap();
		let kappa = Fr::rand(&mut rng);
		let mut run = |c: S119Circ| t1014_g16_ok(&pk, &c, t1014_d_r(&pk, &c, kappa), kappa, &mut rng).0; //ALL_T1014
		assert!(run(circ), "T934 K4: X/X control rejected");
		assert!(!run(circ_y), "T934 K4: key for pp_hash X accepts an X + 1 proof");
	}

	/// T934 K4 (R8b, jet1tb, run alone with --ignored): one full-mode cp
	/// decider synthesis over the T931 fixture. It is SAT and no witness
	/// outside W' holds pp_hash (ALL_T1014). This covers Step 5's copy
	/// (:1575), which only full mode synthesizes.
	#[test]
	#[ignore]
	fn test_t934_k4_cp_full_scan(){
		let _g = T935Light(utils::consts::read_global_config().b_light_test);
		utils::consts::get_global_config().b_light_test = false;
		let (circ, rows, vk, _) = s119_fold_rows(5, None);
		let c2 = t931_fold2(&rows);
		let cs = ConstraintSystem::<Fr>::new_ref();
		t931_cp(&t934_main(circ, Fr::from(7u64)), &c2, &rows, vk).generate_constraints(cs.clone()).unwrap();
		assert!(cs.is_satisfied().unwrap(), "T934 K4: honest full cp decider not SAT");
		let g = cs.borrow().unwrap();
		let (inw, out) = t1014_pp_hits(&g.witness_assignment, g.committed.unwrap().0,
			c2.W_i1.as_ref().unwrap(), c2.pp_hash.unwrap());
		emit_stdout(format!("T934 K4 cp full: pp_hash in {} W' wires, {} other witnesses", inw, out));
		assert_eq!(out, 0, "T934 K4: a cp decider witness outside W' holds pp_hash");
	}

	/// T934 F71: Stage 1 keeps the pre-F71 pp_hash. Stage 2 also hashes
	/// the CyclePair R1CS dims and key (the R1CS the decider checks).
	#[test]
	fn test_t934_f71_pp_hash(){
		use crate::arith::Arith;
		use sha3::{Digest, Sha3_256};
		use ark_serialize::CanonicalSerialize;
		type Vp = crate::folding::foldpot::mod_super::VerifierParamsFoldPotSuper<Bn254, Projective,
			Projective2, S119Cm, S119Cm2, S119Cm, false>;
		let ser = |x: &dyn Fn(&mut Vec<u8>)| { let mut b = vec![]; x(&mut b); b };
		//pre-F71 formula: SHA3 over the per-circuit hashes
		let old = |vp: &Vp| { let mut h = Sha3_256::new();
			for v in &vp.vec_vp { h.update(ser(&|b| v.pp_hash().unwrap().serialize_uncompressed(b).unwrap())); }
			h };
		let fr = |h: Sha3_256| Fr::from_le_bytes_mod_order(&h.finalize());
		let mut rng = ark_std::test_rng();
		let cfg = poseidon_canonical_config::<Fr>();
		let (lk, f, _) = gen_six_root_adv::<Fr, Projective, S119Cm, S119Lk, false>(5, false);
		let prep = PreprocessorParamFoldPotSuper::<Projective, Projective2, S119Fc, S119Cm, S119Cm2,
			S119Lk, S119Gm, false>::new(cfg, vec![f.clone()], lk, vec![f.get_size_f()], false);
		let vp1 = S119Nova::preprocess(&mut rng, &prep, 0).expect("preprocess err").1;
		assert!(vp1.cp_r1cs.is_none() && vp1.pp_hash().unwrap() == fr(old(&vp1)),
			"T934 F71: Stage-1 pp_hash changed");
		let (params, nova) = t931_nova!(&mut rng, 1);
		let vp2 = &params.1;
		let cp = vp2.cp_r1cs.as_ref().expect("T934 F71: Stage 2 without cp_r1cs");
		assert!(cp.params_to_le_bytes() == nova.cp_r1cs.params_to_le_bytes(),
			"T934 F71: hashed cp R1CS != the decider's");
		let mut h = old(vp2);
		h.update(cp.params_to_le_bytes());
		h.update(ser(&|b| vp2.vec_vp[0].cp_cs_vp.serialize_uncompressed(b).unwrap()));
		let p2 = vp2.pp_hash().unwrap();
		assert!(p2 != fr(old(vp2)) && p2 == fr(h) && nova.pp_hash == p2,
			"T934 F71: Stage-2 pp_hash misses the CyclePair R1CS / key");
	}

	const FIXED_T971: bool = true;

	/// T971 red test: the decider caps the step counter i at MAX_STEPS.
	/// Arms differ only in i (no rehash), so only rows reading i move.
	/// H: honest i = 5. A: i = MAX_STEPS adds only the u_i.x[0] row.
	/// B: i = MAX_STEPS + 1 adds exactly one more row (the T971 row).
	/// Z: i = 0 also hits that row (lower bound).
	#[test]
	fn test_t971_step_cap(){
		use crate::folding::foldpot::utils::MAX_STEPS;
		let h = s119_fold(5);
		let arm = |i: usize| { let mut c = h.clone();
			c.i = Some(Fr::from(i as u64)); s103_unsat_rows(&c) };
		let new = |x: &Vec<usize>, y: &Vec<usize>| x.iter()
			.filter(|r| !y.contains(r)).cloned().collect::<Vec<usize>>();
		let ((nh, bh), (na, ba), (nb, bb), (nz, bz)) = (s103_unsat_rows(&h),
			arm(MAX_STEPS), arm(MAX_STEPS + 1), arm(0));
		assert!(nh == na && na == nb && nb == nz, "T971: arms not shape-identical");
		assert!(new(&bh, &ba).is_empty() && new(&ba, &bh).len() == 1,
			"T971: i = MAX_STEPS: new unsat {:?}, want only the u_i.x[0] row",
			new(&ba, &bh));
		assert!(new(&ba, &bb).is_empty(), "T971: B lost rows of A");
		let nb_rows = new(&bb, &ba);
		assert_eq!(nb_rows.is_empty(), !FIXED_T971,
			"T971: i = MAX_STEPS + 1 sat={} with FIXED_T971={}",
			nb_rows.is_empty(), FIXED_T971);
		if FIXED_T971 {
			assert!(nb_rows.len() == 1 && bz.contains(&nb_rows[0]),
				"T971: B new rows {:?}, i = 0 unsat {:?}", nb_rows, bz);
		}
	}

	// ---------------------------------------------------------------
	// ALL_T1014 (sonobe#22 part 2): Step 7 runs on the slots rescaled to
	// u = 1. Unit arms on a random R1CS, then decider arms on s119 (k = 1),
	// s103 [1,0,1,0,1] (k = 2, distinct u) and s103 [0; 5] (slot 1 is a
	// u = 0 dummy).
	// ---------------------------------------------------------------
	use ark_r1cs_std::R1CSVar as _;

	fn t1014_rv<R: ark_std::rand::Rng>(rng: &mut R, n: usize) -> Vec<Fr>{
		(0..n).map(|_| Fr::rand(rng)).collect()
	}

	/// Az o Bz - u Cz - E of the slot (u, x, W, E) of r.
	fn t1014_residual(r: &R1CS<Fr>, u: Fr, x: &[Fr], w: &[Fr], e: &[Fr]) -> Vec<Fr>{
		use crate::utils::vec::mat_vec_mul;
		let z = [vec![u], x.to_vec(), w.to_vec()].concat();
		let m = |a| mat_vec_mul(a, &z).unwrap();
		let (a, b, c) = (m(&r.A), m(&r.B), m(&r.C));
		(0..a.len()).map(|t| a[t] * b[t] - u * c[t] - e[t]).collect()
	}

	/// Indices of the nonzero entries of v.
	fn t1014_nz(v: &[Fr]) -> Vec<usize>{ (0..v.len()).filter(|&t| !v[t].is_zero()).collect() }

	/// Unsat rows of check_native alone. u = None is the rescaled check (u the constant 1).
	fn t1014_check(r: &R1CS<Fr>, u: Option<Fr>, x: &[Fr], w: &[Fr], e: &[Fr]) -> Vec<usize>{
		let (m, z, _) = synth_mats(|cs| {
			let rv = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r.clone())).unwrap();
			let v = |a: &[Fr]| Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(a.to_vec())).unwrap();
			let uv = u.map_or(FpVar::one(), |u| FpVar::new_witness(cs.clone(), || Ok(u)).unwrap());
			RelaxedR1CSGadget::check_native(rv, v(e), uv.clone(), [vec![uv], v(x), v(w)].concat()).unwrap();
		});
		unsat(&m, &z)
	}

	/// A random D over slots of (|W|, |E|), |x| = 2 and u != 0, with its
	/// unscaled all_w() and the instance (u_j, x_j).
	fn t1014_range<R: ark_std::rand::Rng>(rng: &mut R, lens: &[(usize, usize)])
		-> (CommittedRange<Fr>, Vec<Fr>, Vec<(Fr, Vec<Fr>)>){
		let r1cs = R1CS::<Fr>::rand(rng, 1, 1); //read only when u = 0
		let slots = lens.iter().map(|&(nw, ne)| (Fr::rand(rng), t1014_rv(rng, 2),
			t1014_rv(rng, nw), t1014_rv(rng, ne))).collect::<Vec<_>>();
		let o = t1014_rv(rng, 2);
		let (x, w, e) = slots.iter().map(|(u, x, w, e)| scaled_slot(&r1cs, *u, x, w, e)).multiunzip();
		let d = CommittedRange{ w, e, o: o.clone(), u: slots.iter().map(|s| s.0).collect(), x };
		let aw = slots.iter().flat_map(|s| s.2.clone()).chain(slots.iter().flat_map(|s| s.3.clone()))
			.chain(o).collect();
		(d, aw, slots.into_iter().map(|(u, x, _, _)| (u, x)).collect())
	}

	/// ALL_T1014 tests 1-3 and 7. scaled_slot round trip. The rescaled
	/// check accepts exactly when the relaxed one does, and rejects the same
	/// rows. A u = 0 dummy needs E' = dummy_residual. Rescaled Step 7 costs
	/// exactly 1 constraint and 0 variables per row.
	#[test]
	fn test_t1014_scaled_slot(){
		let mut rng = ark_std::test_rng();
		let r = R1CS::<Fr>::rand(&mut rng, 24, 12);
		let (nx, nw, nr) = (r.l, r.A.n_cols - 1 - r.l, r.A.n_rows);
		let mul = |a: &[Fr], s: Fr| a.iter().map(|v| *v * s).collect::<Vec<Fr>>();
		for k in 0..20 {
			let (u, x, w) = (Fr::rand(&mut rng), t1014_rv(&mut rng, nx), t1014_rv(&mut rng, nw));
			let e = t1014_residual(&r, u, &x, &w, &vec![Fr::zero(); nr]);
			let (xp, wp, ep) = scaled_slot(&r, u, &x, &w, &e);
			assert!(mul(&xp, u) == x && mul(&wp, u) == w && mul(&ep, u * u) == e, "test 1: round trip");
			assert!(t1014_check(&r, Some(u), &x, &w, &e).is_empty()
				&& t1014_check(&r, None, &xp, &wp, &ep).is_empty(), "test 2: honest slot UNSAT");
			let (mut x2, mut w2, mut e2) = (x.clone(), w.clone(), e.clone());
			match k % 3 { 0 => w2[k % nw] += Fr::one(), 1 => e2[k % nr] += Fr::one(), _ => x2[0] += Fr::one() }
			let want = t1014_nz(&t1014_residual(&r, u, &x2, &w2, &e2));
			let (xq, wq, eq) = scaled_slot(&r, u, &x2, &w2, &e2);
			assert_eq!(t1014_check(&r, None, &xq, &wq, &eq), want, "test 2: rescaled unsat rows");
			assert_eq!(t1014_check(&r, Some(u), &x2, &w2, &e2).len(), want.len(), "test 2: relaxed unsat rows");
		}
		let (zx, zw, ze) = (vec![Fr::zero(); nx], vec![Fr::zero(); nw], vec![Fr::zero(); nr]);
		let (xp, wp, ep) = scaled_slot(&r, Fr::zero(), &zx, &zw, &ze);
		assert!(xp == zx && wp == zw && ep == dummy_residual(&r) && ep.iter().any(|a| !a.is_zero()),
			"test 3: dummy slot is not (0, 0, nonzero dummy_residual)");
		assert!(t1014_check(&r, None, &xp, &wp, &ep).is_empty(), "test 3: dummy slot UNSAT");
		assert!(!t1014_check(&r, None, &xp, &wp, &ze).is_empty(), "test 3: dummy slot with E' = 0 SAT");
		let cost = |u: Option<Fr>| { let cs = ConstraintSystem::<Fr>::new_ref();
			let rv = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r.clone())).unwrap();
			let v = |a: &[Fr]| Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(a.to_vec())).unwrap();
			let uv = u.map_or(FpVar::one(), |u| FpVar::new_witness(cs.clone(), || Ok(u)).unwrap());
			let z = [vec![uv.clone()], v(&zx), v(&zw)].concat();
			let ev = v(&ze);
			let (c0, w0) = (cs.num_constraints(), cs.num_witness_variables());
			RelaxedR1CSGadget::check_native(rv, ev, uv, z).unwrap();
			(cs.num_constraints() - c0, cs.num_witness_variables() - w0) };
		let c_rows = r.C.coeffs.iter().filter(|row| !row.is_empty()).count();
		assert_eq!(cost(None), (nr, 0), "test 7: rescaled Step 7 cost");
		assert_eq!(cost(Some(Fr::one())), (nr + c_rows, c_rows), "test 7: relaxed Step 7 cost");
	}

	/// ALL_T1014 test 4: a u = 0 slot that is not a dummy panics.
	#[test]
	#[should_panic(expected = "u = 0 slot is not a dummy")]
	fn test_t1014_scaled_slot_u0_live(){
		let r = R1CS::<Fr>::rand(&mut ark_std::test_rng(), 4, 4);
		let x = [vec![Fr::one()], vec![Fr::zero(); r.l - 1]].concat();
		scaled_slot(&r, Fr::zero(), &x, &[Fr::zero(); 2], &[Fr::zero(); 4]);
	}

	/// ALL_T1014 test 5: weighted_horner with weights 1 is evaluate_gadget of
	/// the concatenation, with random weights the native sum, and
	/// eval_unscaled of a random D is P(r) of its unscaled all_w().
	#[test]
	fn test_t1014_weighted_horner(){
		let mut rng = ark_std::test_rng();
		let cs = ConstraintSystem::<Fr>::new_ref();
		let wit = |v: Fr| FpVar::new_witness(cs.clone(), || Ok(v)).unwrap();
		let rn = Fr::rand(&mut rng);
		let (r, one) = (wit(rn), wit(Fr::one()));
		let vals = [5usize, 1, 1100, 3].iter().map(|&n| t1014_rv(&mut rng, n)).collect::<Vec<_>>();
		let vars = vals.iter().map(|v| Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(v.clone())).unwrap())
			.collect::<Vec<_>>();
		let ws = t1014_rv(&mut rng, vals.len());
		let horner = |w: &dyn Fn(usize) -> FpVar<Fr>| { let segs = vars.iter().enumerate()
			.map(|(s, v)| (v.as_slice(), w(s))).collect::<Vec<_>>();
			weighted_horner(&segs, &r, &one).unwrap().value().unwrap() };
		let cat = evaluate_gadget(&vars.concat(), &r, &one).unwrap().value().unwrap();
		assert!(horner(&|_| FpVar::one()) == cat && cat == eval_all_w(&vals.concat(), rn), "test 5: weights 1");
		let mut off = 0u64;
		let want = vals.iter().zip(&ws).map(|(v, w)| { let t = *w * rn.pow([off]) * eval_all_w(v, rn);
			off += v.len() as u64; t }).sum::<Fr>();
		assert_eq!(horner(&|s| wit(ws[s])), want, "test 5: random weights");
		let (d, aw, _) = t1014_range(&mut rng, &[(3, 5), (4, 7)]);
		let dv = CommittedRange::alloc(&cs, d).unwrap();
		assert_eq!(dv.eval_unscaled(&r, &one).unwrap().value().unwrap(), eval_all_w(&aw, rn), "test 5: eval_unscaled");
		assert!(cs.is_satisfied().unwrap(), "test 5: honest Horner UNSAT");
	}

	/// ALL_T1014 test 6: bind rejects D.u != U.u (either side moved),
	/// x != u x', and u = 0 with x != 0 for any x'.
	#[test]
	fn test_t1014_bind_arms(){
		let (d0, _, inst0) = t1014_range(&mut ark_std::test_rng(), &[(2, 3), (2, 3)]);
		let sat = |d: &CommittedRange<Fr>, inst: &[(Fr, Vec<Fr>)]| {
			let cs = ConstraintSystem::<Fr>::new_ref();
			let iv = inst.iter().map(|(u, x)| { let mut c = CommittedInstanceFoldPot::<Projective>::dummy(2);
				(c.u, c.x) = (*u, x.clone());
				CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(c)).unwrap() })
				.collect::<Vec<_>>();
			CommittedRange::alloc(&cs, d.clone()).unwrap().bind(&iv).unwrap();
			cs.is_satisfied().unwrap() };
		assert!(sat(&d0, &inst0), "test 6: honest bind UNSAT");
		let mut d = d0.clone();
		d.u[1] += Fr::one();
		assert!(!sat(&d, &inst0), "test 6: D.u != U.u accepted");
		let mut i = inst0.clone();
		i[0].0 += Fr::one();
		assert!(!sat(&d0, &i), "test 6: moved U.u accepted");
		let mut i = inst0.clone();
		i[1].1[1] += Fr::one();
		assert!(!sat(&d0, &i), "test 6: x != u x' accepted");
		let (mut d, mut i) = (d0.clone(), inst0.clone());
		(d.u[0], i[0].0) = (Fr::zero(), Fr::zero());
		assert!(!sat(&d, &i), "test 6: u = 0 with x != 0 accepted");
	}

	/// ALL_T1014 test 8: alloc commits parts() in D order, as one range of
	/// exactly the part lengths, starting at the first new witness.
	#[test]
	fn test_t1014_alloc_order(){
		let mut n = 0u64;
		let mut seq = |k: usize| (0..k).map(|_| { n += 1; Fr::from(n) }).collect::<Vec<Fr>>();
		let d = CommittedRange{ w: vec![seq(3), seq(2)], e: vec![seq(4), seq(1)], o: seq(2), u: seq(2),
			x: vec![seq(2), seq(2)] };
		let (m, z, (s0, k)) = synth_mats(|cs| { let _ = FpVar::new_witness(cs.clone(), || Ok(Fr::zero())).unwrap();
			CommittedRange::alloc(&cs, d.clone()).unwrap(); });
		let c0 = m.num_instance_variables + s0;
		assert!(s0 == 1 && k == 18 && z[c0..c0 + k] == d.parts().flatten().collect::<Vec<_>>()[..]
			&& (0..k).all(|t| z[c0 + t] == Fr::from(t as u64 + 1)), "test 8: committed range out of D order");
	}

	/// The three decider fixtures. s119 is repaired (t934_forge) so it is SAT.
	fn t1014_fixtures() -> [S119Circ; 3]{
		[t934_forge(&s119_fold(5), Fr::zero(), None), s103_fold(5, 2, &[1, 0, 1, 0, 1]), s103_fold(5, 2, &[0; 5])]
	}

	/// (N = |all_w()|, k, |x|) of a fixture.
	fn t1014_dims(c: &S119Circ) -> (usize, usize, usize){
		let inst = &c.U_i1.as_ref().unwrap().vec_inst;
		(c.all_w().len(), inst.len(), inst[0].x.len())
	}

	/// The bind rows of slot j: (u pin row, x-binding rows), with D at column d0.
	fn t1014_bind_rows(m: &ark_relations::r1cs::ConstraintMatrices<Fr>, d0: usize,
		(n, k, nx): (usize, usize, usize), j: usize) -> (usize, Vec<usize>){
		let (cu, one) = (d0 + n + j, Fr::one());
		let pin = (0..m.num_constraints).filter(|&r| m.b[r] == [(one, 0)] && m.c[r].is_empty()
			&& m.a[r].len() == 2 && m.a[r].iter().any(|&(c, i)| i == cu && (c == one || c == -one)))
			.collect::<Vec<_>>();
		assert_eq!(pin.len(), 1, "ALL_T1014: u pin row of slot {} not unique", j);
		let xr = (0..nx).map(|t| (0..m.num_constraints).find(|&r| m.a[r] == [(one, d0 + n + k + j * nx + t)]
			&& m.b[r] == [(one, cu)]).expect("ALL_T1014: no x-binding row")).collect();
		(pin[0], xr)
	}

	/// ALL_T1014 tests 9-12 and 14 on the three fixtures. 9: eval_w_e is
	/// P(r) of all_w(). 10: the unsat rows are exactly the Step 7 rows whose
	/// native relaxed residual is nonzero, none in a u = 0 slot. 11: the
	/// committed range is cp_w() with the o and u tails in place. 12: moving
	/// D.u_j, U_j.u or D.x'_j breaks a bind row. 14: setup-mode and
	/// prove-mode synthesis, and the two s103 fixtures, share one shape.
	#[test]
	fn test_t1014_decider_rescale(){
		let fx = t1014_fixtures();
		let mut shapes = vec![];
		for (f, c) in fx.iter().enumerate() {
			let (aw, cp, dims) = (c.all_w(), c.cp_w(), t1014_dims(c));
			let (n, k, nx) = dims;
			let inst = &c.U_i1.as_ref().unwrap().vec_inst;
			let wit = &c.W_i1.as_ref().unwrap().vec_wit;
			let cs = ConstraintSystem::<Fr>::new_ref();
			let ret = c.generate_constraints_adv(0, cs.clone(), Fr::zero()).unwrap().val();
			assert_eq!(ret.eval_w_e, eval_all_w(&aw, c.kzg_ch.unwrap()), "test 9: fixture {}", f);
			let (m, z, (s0, len)) = synth_mats(|cs| { c.generate_constraints_adv(0, cs, Fr::zero()).unwrap(); });
			let d0 = m.num_instance_variables + s0;
			let us = inst.iter().map(|i| i.u).collect::<Vec<_>>();
			assert!(len == n + k * (1 + nx) && z[d0..d0 + len] == cp[..] && cp[n - 2..n] == aw[n - 2..]
				&& cp[n..n + k] == us[..], "test 11: fixture {} committed range != cp_w()", f);
			//An unsat honest row is a Step 7 row. Row (j, t) reads E'_j[t] in C,
			//or in A when it is an enforce_equal (Az' or Bz' constant).
			let mut e_col = std::collections::HashMap::new();
			let mut col = d0 + wit.iter().map(|w| w.W.len()).sum::<usize>();
			for (j, w) in wit.iter().enumerate() { for t in 0..w.E.len() { e_col.insert(col, (j, t)); col += 1; } }
			let got = unsat(&m, &z).iter().map(|&r| m.c[r].iter().chain(&m.a[r]).find_map(|(_, i)| e_col.get(i).copied())
				.expect("test 10: an unsat row outside Step 7")).collect::<std::collections::BTreeSet<_>>();
			let want = (0..k).flat_map(|j| t1014_nz(&t1014_residual(&c.r1cs[j], inst[j].u, &inst[j].x,
				&wit[j].W, &wit[j].E)).into_iter().map(move |t| (j, t))).collect::<std::collections::BTreeSet<_>>();
			assert_eq!(got, want, "test 10: fixture {} unsat Step 7 rows", f);
			assert!(got.iter().all(|&(j, _)| !us[j].is_zero()), "test 10: unsat row in a u = 0 slot");
			assert_eq!(f == 2, us.iter().any(|u| u.is_zero()), "fixture {}: u = 0 slot expected only in [0; 5]", f);
			for j in 0..k {
				let (pin, xr) = t1014_bind_rows(&m, d0, dims, j);
				let cu_inst = m.a[pin].iter().map(|&(_, i)| i).find(|&i| i != d0 + n + j).unwrap();
				//x' is free when u_j = 0 (x = u x' = 0 for every x').
				let x_arm = (!us[j].is_zero()).then(|| (d0 + n + k + j * nx, xr[0]));
				for (cl, row) in [(d0 + n + j, pin), (cu_inst, pin)].into_iter().chain(x_arm) {
					let mut z2 = z.clone();
					z2[cl] += Fr::one();
					assert!(unsat(&m, &z2).contains(&row), "test 12: fixture {} slot {}: column {} moved, row {} SAT", f, j, cl, row);
				}
			}
			let (ms, _, rs) = synth_mats(|cs| { cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
				c.generate_constraints_adv(0, cs, Fr::zero()).unwrap(); });
			let shape = |m: &ark_relations::r1cs::ConstraintMatrices<Fr>, r| (m.a.clone(), m.b.clone(), m.c.clone(),
				m.num_instance_variables, m.num_witness_variables, r);
			assert!(shape(&ms, rs) == shape(&m, (s0, len)), "test 14: fixture {} setup shape != prove shape", f);
			shapes.push(shape(&m, (s0, len)));
		}
		assert!(shapes[1] == shapes[2], "test 14: s103 [1,0,1,0,1] and [0; 5] differ in shape");
	}

	/// ALL_T1014 test 15: through the CyclePair synthesis, the Stage-2
	/// committed range is the main circuit's cp_w() and a moved D.u breaks its pin.
	#[test]
	fn test_t1014_cp_bind(){
		let circ = s119_fold(5);
		let res = t934_main(circ.clone(), Fr::from(7u64)).res;
		let (m, z, (s0, len)) = synth_mats(|cs| t934_cp(&circ, &res).generate_constraints(cs).unwrap());
		let d0 = m.num_instance_variables + s0;
		assert!(z[d0..d0 + len] == circ.cp_w()[..], "test 15: Stage-2 committed range != cp_w()");
		let dims = t1014_dims(&circ);
		let (pin, _) = t1014_bind_rows(&m, d0, dims, 0);
		let mut z2 = z.clone();
		z2[d0 + dims.0] += Fr::one();
		assert!(!unsat(&m, &z).contains(&pin) && unsat(&m, &z2).contains(&pin),
			"test 15: Stage-2 u pin does not reject a moved D.u");
	}

	// ---------------------------------------------------------------
	// ALL_T1016 (P8): the signed-split non-native RelaxedR1CS check (Step 10)
	// on the CyclePair and CycleFold R1CS the decider checks. The tests
	// run without prints.
	// ---------------------------------------------------------------
	mod t1016 {
		use super::*;
		use std::{cmp::min, collections::HashMap, iter::successors, ops::Range};
		use rayon::prelude::*;
		use ark_bn254::{Bn254, Fq, constraints::{GVar, PairingVar}, G1Projective as G1, G2Projective as G2};
		use ark_relations::r1cs::SynthesisMode;
		use ark_std::rand::{rngs::StdRng, SeedableRng};
		use crate::folding::circuits::{cyclefold::CycleFoldCircuit, nonnative::uint::BoundedBigUint};
		use crate::folding::foldpot::{cyclepair::CyclePairCircuit, FOLDPOT_CF_N_POINTS};
		use crate::utils::vec::mat_vec_mul;

		type NV = NonNativeUintVar<Fr>;
		type Gadget = fn(R1CSVar<Fq, Fr, NV>, Vec<NV>, NV, Vec<NV>) -> Result<(), SynthesisError>;
		const NEW: Gadget = RelaxedR1CSGadget::check_nonnative::<Fq, Fr>;
		const CHUNK: usize = 2000;

		/// A relaxed instance as integers: z = [u, x, W] and E.
		#[derive(Clone)]
		struct Inst { z: Vec<BigUint>, e: Vec<BigUint> }

		fn q() -> BigUint { Fq::MODULUS.into() }

		fn r1cs_of(c: impl ConstraintSynthesizer<Fq>) -> R1CS<Fq> {
			let cs = ConstraintSystem::<Fq>::new_ref();
			c.generate_constraints(cs.clone()).unwrap();
			cs.finalize();
			extract_r1cs::<Fq>(&cs.into_inner().unwrap())
		}
		fn cp_r1cs() -> R1CS<Fq> { r1cs_of(CyclePairCircuit::<Bn254, PairingVar, G1, G2>::empty()) }
		fn cf_r1cs() -> R1CS<Fq> { r1cs_of(CycleFoldCircuit::<G1, GVar>::empty(FOLDPOT_CF_N_POINTS)) }

		/// Honest instance: random z (z[0] = u), E = Az o Bz - u Cz in Fq.
		fn honest(r: &R1CS<Fq>, seed: u64) -> Inst {
			let rng = &mut StdRng::seed_from_u64(seed);
			let z: Vec<Fq> = (0..r.A.n_cols).map(|_| Fq::rand(rng)).collect();
			let m = |a: &SparseMatrix<Fq>| mat_vec_mul(a, &z).unwrap();
			let (a, b, c) = (m(&r.A), m(&r.B), m(&r.C));
			let e = (0..r.A.n_rows).map(|i| (a[i] * b[i] - z[0] * c[i]).into()).collect();
			Inst { z: z.into_iter().map(Into::into).collect(), e }
		}

		/// Rows `rows` of (r, inst), keeping only the columns they use (and u).
		fn restrict(r: &R1CS<Fq>, inst: &Inst, rows: Range<usize>) -> (R1CS<Fq>, Inst) {
			let mut cols: Vec<usize> = [&r.A, &r.B, &r.C].iter()
				.flat_map(|m| m.coeffs[rows.clone()].iter().flatten().map(|&(_, j)| j)).chain([0]).collect();
			cols.sort_unstable();
			cols.dedup();
			let pos: HashMap<usize, usize> = cols.iter().enumerate().map(|(k, &j)| (j, k)).collect();
			let sub = |m: &SparseMatrix<Fq>| SparseMatrix { n_rows: rows.len(), n_cols: cols.len(),
				coeffs: m.coeffs[rows.clone()].iter().map(|row| row.iter().map(|&(c, j)| (c, pos[&j])).collect()).collect() };
			(R1CS { l: 0, A: sub(&r.A), B: sub(&r.B), C: sub(&r.C) },
				Inst { z: cols.iter().map(|&j| inst.z[j].clone()).collect(), e: inst.e[rows.clone()].to_vec() })
		}

		/// Allocate z, u = z[0] and E as Step 10's callers do (witness limbs of 55, 55,
		/// 55, 55 and 36 bits, as new_witness of an Fq element) and run gadget.
		/// Returns its result and its constraint count.
		fn synth(cs: ConstraintSystemRef<Fr>, r: &R1CS<Fq>, inst: &Inst, gadget: Gadget)
			-> (Result<(), SynthesisError>, usize) {
			let alloc = |v: &[BigUint]| v.iter()
				.map(|x| NV::new_witness(cs.clone(), || Ok(BoundedBigUint(x.clone(), 256))).unwrap()).collect::<Vec<_>>();
			let (z, e) = (alloc(&inst.z), alloc(&inst.e));
			let r1cs = R1CSVar::<Fq, Fr, NV>::new_witness(cs.clone(), || Ok(r.clone())).unwrap();
			let c0 = cs.num_constraints();
			let res = gadget(r1cs, e, z[0].clone(), z);
			(res, cs.num_constraints() - c0)
		}

		/// (SAT, constraint count) of gadget on (r, inst) in a fresh cs.
		fn sat(r: &R1CS<Fq>, inst: &Inst, gadget: Gadget) -> (bool, usize) {
			let cs = ConstraintSystem::<Fr>::new_ref();
			let (res, n) = synth(cs.clone(), r, inst, gadget);
			res.unwrap();
			(cs.is_satisfied().unwrap(), n)
		}

		/// [A, B, C] of r as constants, each split into [M+, M-].
		fn splits(r: &R1CS<Fq>) -> [[NNMatrix<Fq, Fr>; 2]; 3] {
			let R1CSVar { A, B, C, .. } = R1CSVar::<Fq, Fr, NV>::new_constant(ConstraintSystemRef::None, r.clone()).unwrap();
			[A, B, C].map(split_signed::<Fq, Fr>)
		}

		/// T1: each entry c lands on exactly one side, plus == c or q - minus == c,
		/// the side value has min(bits(c), bits(q - c)) bits, and every limb bound
		/// equals its limb value.
		fn check_split(r: &R1CS<Fq>) {
			let q = q();
			for (m, parts) in [&r.A, &r.B, &r.C].into_iter().zip(splits(r)) {
				for p in &parts { assert!(p.n_rows == m.n_rows && p.n_cols == m.n_cols && p.coeffs.len() == m.coeffs.len()); }
				for (i, row) in m.coeffs.iter().enumerate() {
					let mut left: HashMap<usize, BigUint> = row.iter().map(|&(c, j)| (j, c.into())).collect();
					assert_eq!(left.len(), row.len(), "T1016 T1: repeated column in row {}", i);
					for (side, part) in parts.iter().enumerate() {
						for (v, j) in &part.coeffs[i] {
							let c = left.remove(j).expect("T1016 T1: entry on both sides");
							let val = v.value().unwrap();
							assert_eq!(if side == 0 { val.clone() } else { &q - &val }, c, "T1016 T1: row {} col {}", i, j);
							assert_eq!(val.bits(), min(c.bits(), (&q - &c).bits()), "T1016 T1: not the shorter side");
							assert!(v.0.iter().all(|l| l.ub == BigUint::from(l.value().unwrap())), "T1016 T1: bound != value");
						}
					}
					assert!(left.is_empty(), "T1016 T1: entry lost in row {}", i);
				}
			}
		}

		/// T5: rows whose two sides differ in limb count before padding. Lengths do
		/// not depend on values, so z, u and E are constant zeros (free products).
		fn unequal_rows(r: &R1CS<Fq>) -> usize {
			let zero = || NV::new_constant(ConstraintSystemRef::None, Fq::zero()).unwrap();
			let (u, z) = (zero(), vec![zero(); r.A.n_cols]);
			let [[ap, an], [bp, bn], [cp, cn]] = splits(r).map(|s| s.map(|m| m.mul_vector(&z).unwrap()));
			(0..r.A.n_rows).filter(|&i| {
				let lhs = sum_of_products(&[(&ap[i], &bp[i]), (&an[i], &bn[i]), (&u, &cn[i])]).unwrap();
				let rhs = sum_of_products(&[(&ap[i], &bn[i]), (&an[i], &bp[i]), (&u, &cp[i])]).unwrap().add_no_align(&zero());
				lhs.0.len() != rhs.0.len()
			}).count()
		}

		/// T3: each arm alone is UNSAT on the rows window(i) around its target row i.
		fn red_arms(r: &R1CS<Fq>, window: impl Fn(usize) -> Range<usize>) {
			let (inst, n) = (honest(r, 1), r.A.n_rows);
			let [[_, an], [_, bn], _] = splits(r);
			let width = |i: usize| [&r.A, &r.B, &r.C].iter().flat_map(|m| m.coeffs[i].iter())
				.map(|&(c, _)| { let c: BigUint = c.into(); min(c.bits(), (q() - c).bits()) }).max().unwrap_or(0);
			let big = (0..n).max_by_key(|&i| width(i)).unwrap();
			let no_minus = (0..n).find(|&i| an.coeffs[i].is_empty() && bn.coeffs[i].is_empty()).expect("no row without A- and B-");
			let (w_row, w_col) = (0..n).find_map(|i| r.A.coeffs[i].iter().find(|e| e.1 > r.l).map(|e| (i, e.1))).unwrap();
			let u_row = (0..n).find(|&i| !r.C.coeffs[i].is_empty()).unwrap();
			let s_row = (0..n).find(|&i| !an.coeffs[i].is_empty()).unwrap();
			let s_k = r.A.coeffs[s_row].iter().position(|e| e.1 == an.coeffs[s_row][0].1).unwrap();
			type Arm = Box<dyn Fn(&mut R1CS<Fq>, &mut Inst)>;
			let e_plus = |i: usize| -> Arm { Box::new(move |_: &mut R1CS<Fq>, s: &mut Inst| s.e[i] += 1u32) };
			let arms: Vec<(&str, usize, Arm)> = vec![
				("E_0 + 1", 0, e_plus(0)),
				("E_7 + 1", 7, e_plus(7)),
				("E_last + 1", n - 1, e_plus(n - 1)),
				("E + 1 at the largest coefficient", big, e_plus(big)),
				("E + 1 where A- and B- are empty", no_minus, e_plus(no_minus)),
				("W entry + 1", w_row, Box::new(move |_: &mut R1CS<Fq>, s: &mut Inst| s.z[w_col] += 1u32)),
				("u + 1, E unchanged", u_row, Box::new(|_: &mut R1CS<Fq>, s: &mut Inst| s.z[0] += 1u32)),
				("A- coefficient changed by 1", s_row,
					Box::new(move |m: &mut R1CS<Fq>, _: &mut Inst| m.A.coeffs[s_row][s_k].0 += Fq::one())),
			];
			for (name, i, arm) in arms {
				let (mut r2, mut s) = (r.clone(), inst.clone());
				arm(&mut r2, &mut s);
				let (rr, ss) = restrict(&r2, &s, window(i));
				assert!(!sat(&rr, &ss, NEW).0, "T1016 T3 {} (row {}): SAT", name, i);
			}
		}

		/// T4: z_j + q and E_0 + q (non-canonical, below 2^256) stay SAT.
		fn noncanonical(r: &R1CS<Fq>, rows: Range<usize>) {
			let (rr, mut s) = restrict(r, &honest(r, 1), rows);
			let j = s.z.len() - 1;
			s.z[j] += q();
			s.e[0] += q();
			assert!(s.z[j].bits() <= 256 && s.e[0].bits() <= 256);
			assert!(sat(&rr, &s, NEW).0, "T1016 T4: non-canonical limbs rejected");
		}

		/// T6: Setup mode and two prove-mode instances build identical matrices.
		fn setup_vs_prove(r: &R1CS<Fq>, rows: Range<usize>) {
			let (rr, i1) = restrict(r, &honest(r, 1), rows.clone());
			let (_, i2) = restrict(r, &honest(r, 2), rows);
			let mats = |inst: &Inst, setup: bool| synth_mats(|cs| {
				if setup { cs.set_mode(SynthesisMode::Setup); }
				synth(cs, &rr, inst, NEW).0.unwrap();
			}).0;
			let m = mats(&i1, true);
			assert!(m == mats(&i1, false) && m == mats(&i2, false), "T1016 T6: setup and prove shapes differ");
		}

		/// T8 (break B2), each row alone: E_i + r or E_i - r (mod q, r = |Fr|), and
		/// each lift of it by q below 2^256. The honest quotient then leaves exactly
		/// +r or -r for enforce_equal_unaligned. Its field carries take the small
		/// wrong solution where a group bound has 253 bits and its low part fits.
		/// Returns the rows where some forged E_i is SAT.
		fn b2_sat_rows(r: &R1CS<Fq>, gadget: Gadget) -> Vec<usize> {
			let (inst, q, rm) = (honest(r, 1), q(), BigUint::from(Fr::MODULUS));
			(0..r.A.n_rows).into_par_iter().filter(|&i| {
				let (sub, s) = restrict(r, &inst, i..i + 1);
				[&s.e[0] + &rm, &s.e[0] + &q - &rm].into_iter()
					.flat_map(|e| successors(Some(e % &q), |e| Some(e + &q)).take_while(|e| e.bits() <= 256))
					.any(|e| sat(&sub, &Inst { e: vec![e], ..s.clone() }, gadget).0)
			}).collect()
		}

		#[test]
		fn test_t1016_split(){
			check_split(&cf_r1cs());
			check_split(&cp_r1cs());
		}

		#[test]
		fn test_t1016_cf_red(){
			let r = cf_r1cs();
			let n = r.A.n_rows;
			red_arms(&r, |_| 0..n);
			noncanonical(&r, 0..n);
		}

		#[test]
		fn test_t1016_cp_red(){
			let r = cp_r1cs();
			red_arms(&r, |i| i..i + 1);
			noncanonical(&r, 0..CHUNK);
		}

		#[test]
		fn test_t1016_b2_red(){
			for r in [cf_r1cs(), cp_r1cs()] {
				let bad = b2_sat_rows(&r, NEW);
				assert!(bad.is_empty(), "T1016 T8: B2 forgery SAT on {} rows, such as {:?}", bad.len(), &bad[..min(bad.len(), 5)]);
			}
		}

		#[test]
		fn test_t1016_shapes(){
			let r = cf_r1cs();
			let inst = honest(&r, 1);
			let short = |cut: fn(&mut Inst)| { let mut s = inst.clone(); cut(&mut s); synth(ConstraintSystem::<Fr>::new_ref(), &r, &s, NEW).0 };
			assert!(matches!(short(|s| { s.e.pop(); }), Err(SynthesisError::Unsatisfiable)), "T1016 T5: short E accepted");
			assert!(matches!(short(|s| { s.z.pop(); }), Err(SynthesisError::Unsatisfiable)), "T1016 T5: short z accepted");
			// one row, A = B = (q - 1) / 2 (plus side, 5 limbs), C = 1: L has 17 limbs, R 9
			let row = |c: Fq, j: usize| SparseMatrix { n_rows: 1, n_cols: 3, coeffs: vec![vec![(c, j)]] };
			let half = Fq::from(q() / 2u32);
			let h = R1CS { l: 0, A: row(half, 1), B: row(half, 2), C: row(Fq::one(), 0) };
			assert_eq!(unequal_rows(&h), 1);
			let mut s = honest(&h, 1);
			assert!(sat(&h, &s, NEW).0, "T1016 T5: honest one-row instance not SAT");
			s.e[0] += 1u32;
			assert!(!sat(&h, &s, NEW).0, "T1016 T5: one-row E + 1 SAT");
			// the test allocation has the caller's limb bounds
			let cs = ConstraintSystem::<Fr>::new_ref();
			let bounds = |x: NV| x.0.iter().map(|l| l.ub.clone()).collect::<Vec<_>>();
			let v = Fq::from(5u32);
			assert_eq!(bounds(NV::new_witness(cs.clone(), || Ok(v)).unwrap()),
				bounds(NV::new_witness(cs, || Ok(BoundedBigUint(v.into(), 256))).unwrap()));
		}

		#[test]
		fn test_t1016_setup_vs_prove(){
			let r = cf_r1cs();
			setup_vs_prove(&r, 0..r.A.n_rows);
			let cp = cp_r1cs();
			for s in (0..cp.A.n_rows).step_by(CHUNK) {
				setup_vs_prove(&cp, s..min(s + CHUNK, cp.A.n_rows));
			}
		}
	}
}
