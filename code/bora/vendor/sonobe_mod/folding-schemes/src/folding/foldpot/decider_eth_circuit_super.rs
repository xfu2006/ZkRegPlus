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
use ark_ff::{PrimeField, Field, ToConstraintField};
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
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,SigmaIR1CS_Inst,ZiPartTwoInst,ZiPartTwoInstVar,GadgetMapper},
		circuits::{CommittedInstanceVarFoldPot},
		//decider_eth_circuit::{RelaxedR1CSGadget, R1CSVar,WitnessVarFoldPot,CycleFoldWitnessVar},
		mod_super::{WitnessFoldPotSuper,CommittedInstanceFoldPotSuper, FoldPotSuper},
		circuits_super::{field_to_usize,CommittedInstanceVarFoldPotSuper},
		sigma_cyclepair::{compute_hc_var, hash_var},
		utils::{get_mem_usage,f1_limbs_to_f2, B_DEBUG, B_DEBUG2, B_DEBUG3, new_var, check_cs},
		container_config::ColEle,
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

			randf
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

			b_full_mode: nova.b_full_mode,
			job_id: nova.job_id,

        })
    }

	/// In addition to generate constraints, for stage 1 circuit
	/// return the <<com_E, com_W, com_F>>; for stage 2 circuit
	/// return the final_result = hash_a_b
    pub fn generate_constraints_adv(&self, _dump_level: usize, cs: ConstraintSystemRef<CF1<C1>>, _randf: CF1<C1>) -> Result<Phase1CircuitRet<CF1<C1>,C1>, Error> {
    	//1. generate Vector the R1CS var (one for each circuit)
    	let log_level = LOG3;
    	let mut t1 = GTimer::new();
		let mut c1 = cs.num_constraints();
		let c0 = cs.num_constraints();
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
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 1: generae r1cs_var. INCREASSED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		if B_DEBUG3 {check_cs(&cs, "phase1 step 1.0");}

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
        let W_i1 = WitnessVarFoldPotSuper::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i1.clone().unwrap())
        })?;
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 2: igen Ui, Wi, Ui1, Wi1 witness: INCREASED {} constraints", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		if B_DEBUG3{check_cs(&cs, "phase1 step 2.0");}

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
		let len_all_w_e = all_w.len();
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 3: collect all_w_e. len: {}, : INCREASED: {} constraints.", 
			all_w.len(), cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		if B_DEBUG3{check_cs(&cs, "phase1 step 2");}

		let one= FpVar::<C1::ScalarField>::new_witness(cs.clone(),  || 
			Ok(C1::ScalarField::from(1u32)) ).unwrap();
        let eval_w_e= evaluate_gadget::<CF1<C1>>(all_w, kzg_all_com_ch, one)?;
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 4: eval all_w_e. INCREASED {} constrains.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
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
		// REASON: when i (from nova) is 1, we are talking about verifying
		// u_1.x = hash(U_1, ...) where U_1 is really from the dummy case.
        let is_basecase = i_minus_one.is_zero()?;
        (u_i.x[0]).enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i_x)?)?;
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 5: Enforce u_i standard and hash. INCREASED r1cs: {}.", cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
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

		//S105b: pin z_0[1] to the CANONICAL initial state. Without it
		//the chain S104 builds has no root -- z_0 is a decider witness
		//(:763), so a prover picks the starting accumulators freely and
		//can seed away any deficit. Rebuilding the state here also
		//subsumes S101: alpha = H(rc) and beta = H(rc, alpha) are
		//recomputed in-circuit instead of read from an unbound witness.
		//SCOPE: this pins the accumulators to zero and alpha/beta to
		//rc. It does NOT pin total_words to a verifier-known count --
		//it only ties z_0's copy to the final state's. Anchoring the
		//count needs total_words as a real public input (BatchClaim +
		//Phase1CircuitRet + mainres_hash), which is NOT done here.
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
			let h_fixed = ZiPartTwoInstVar::<CF1<C1>>::hash_slice(
				&self.poseidon_config, cs.clone(), &v_fixed);
			//full mode: z_0's cyclepair limbs are all zero, so their
			//half of the split digest is a compile-time constant --
			//computed natively, injected as a constant, 0 R1CS.
			let zp_native = self.zi_part2_inst.clone()
				.expect("zi_part null");
			let n_limbs = zp_native.to_vec().len().saturating_sub(21);
			let z0_hash = if n_limbs==0 { h_fixed } else {
				let h_cp0 = {
					let mut sp2 = PoseidonSponge::<CF1<C1>>::new(
						&self.poseidon_config);
					sp2.absorb(&vec![CF1::<C1>::zero(); n_limbs]);
					sp2.squeeze_field_elements::<CF1<C1>>(1)[0]
				};
				let h_cp0_var = FpVar::<CF1<C1>>::new_constant(
					cs.clone(), h_cp0)?;
				ZiPartTwoInstVar::<CF1<C1>>::hash_slice(
					&self.poseidon_config, cs.clone(), &[h_fixed, h_cp0_var])
			};
			z0_hash.enforce_equal(&z_0[1])?;
		}
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 6: verify zi_part2. INCREASED r1cs: {}, memory usage: {}.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
		c1 = cs.num_constraints();
		if B_DEBUG3{check_cs(&cs, "phase1 step 6");}


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
		log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 7: check {} circs. INCREASED r1cs: {}", self.n_circ, cs.num_constraints()-c1), &mut t1);
		c1 = cs.num_constraints();
		if B_DEBUG3{check_cs(&cs, "phase1 step 7");}

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
				let fp_j = FpVar::<CF1<C1>>::new_constant(cs.clone(),
					C1::ScalarField::from(j as u32))?;
				let b_inact = fp_j.is_eq(&pc_i_var)?.not();
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
				//S103b: the selector index must be a CONSTANT. As a
				//witness the prover sets var_i == pc_i at an index of
				//their choosing (or at none, leaving the :1024-1025
				//initializers = slot 0), which redirects this whole
				//NIFS check to a slot decoupled from pc_i. The
				//augmented circuit already does it right
				//(circuits_super.rs:734, :787, :859).
				let var_i = FpVar::<CF1<C1>>::new_constant(cs.clone(),
					C1::ScalarField::from(i as u32))?;
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
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 8: Verify U_i1 is folded U_i and u_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
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
                Ok(self.cf_U_i.clone().unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.clone().unwrap_or(w_dummy_native.clone()))
            })?;
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            //9. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H2 = GC2::new_constant(cs.clone(), 
				self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), 
				self.cf_pedersen_params.generators.clone())?;
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
			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 9: check cf_W_i commits to cf_U_i. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();


			//10. check cyclefold witness satisfy its r1cs
            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness( cs.clone(), || Ok(self.cf_r1cs.clone()),)?;

            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(),
				cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs,
				cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;

			log_perf(self.job_id, log_level, &format!("Phase1 Circ gen_cs: Step 10: check cp_W_i satisfies cyclefold instance. INCREASED r1cs: {}, RAM: {} GB.", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
        }

		if B_DEBUG3{check_cs(&cs, "phase1 step 10");}

		let mut vec_coms_part2 = U_i1.vec_inst.iter().map(|inst|
			vec![inst.cmW.clone(), inst.cmE.clone(), inst.cmF.clone()]
		).flatten().collect::<Vec<NonNativeAffineVar<C1>>>();
		let mut vec_coms = vec![com_all_w_clone];
		vec_coms.append(&mut vec_coms_part2);
        let mut rng = ark_std::test_rng();
		let randf_val = C1::ScalarField::rand(&mut rng);
		//let randf_val = C1::ScalarField::from(100u32);
		let randf = FpVar::<CF1<C1>>::new_witness(cs.clone(), ||{
			Ok(randf_val)
		})?;
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

			randf
		};

		if B_DEBUG3{check_cs(&cs, "phase1 step 10");}
		let _last_c1 = c1; //just to disable the warning on c1.
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
///     and verify that hash(hashchain(G_1), hashchain(G_2)) is the same
///     as computed by the cyclepair circuits's final result (in ZiPart2)
/// (4) verify that hashchain(G_2) is the same as the QA-NIZK verifier key
///     hash
/// --> the above essentially finishes the proof of circ1's (MainDeciderCircuit
///       for ZkregPlus relation)'s com_all_w
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
		 r_all_w_2: C1::ScalarField,
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
			let randf = CF1::<C1>::zero();
			main_circ2.generate_constraints_adv(3,cs.clone(),randf).unwrap()
		};
		log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 3: Main circ construction. r1cs: {}", cs.num_constraints()-c1), &mut t1);
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
		let b_light_test = utils::consts::read_global_config().b_light_test;
		//let part1_enable = false;
		//let part2_enable = false;
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

            let H2 = GC2::new_constant(cs.clone(), 
				self.main_circ.cp_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), 
				self.main_circ.cp_pedersen_params.generators)?;
			//if part1_enable{
				let cp_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cp_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
				let computed_cmE = PedersenGadget::<C2, GC2>::commit(
					H2.clone(),
					G.clone(),
					cp_W_i_E_bits?,
					cp_W_i.rE.to_bits_le()?,
				)?;
				cp_U_i.cmE.enforce_equal(&computed_cmE)?;
				if B_DEBUG2{
					if cp_U_i.cmE.value().is_ok(){
					assert!(cp_U_i.cmE.value()?== computed_cmE.value()?);
				} }
			//}
			log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 6.1: check cp_W_i commits to cp_U_i. r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
			c1 = cs.num_constraints();

			//if part2_enable{
				let cp_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> = cp_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();
				let computed_cmW =
					PedersenGadget::<C2, GC2>::commit(H2, G, cp_W_i_W_bits?, cp_W_i.rW.to_bits_le()?)?;
				cp_U_i.cmW.enforce_equal(&computed_cmW)?;
				if B_DEBUG2{
					if cp_U_i.cmW.value().is_ok(){
					assert!(cp_U_i.cmW.value()?== computed_cmW.value()?);
				} }
			//}
			log_perf(self.job_id, log_level, &format!("Phase2 Circ gen_cs: Step 6.2: check cp_E_i commits to cp_U_i. r1cs: {}, RAM: {} GB", cs.num_constraints()-c1, get_mem_usage()), &mut t1);
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
		let mut part2 = vec![comEx, comEy, comWx, comWy, comFx, comFy].concat();
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
			ch1, rc1, hash_cmF1, kzg_sum1, kzg_all_com_ch1, eval_w_e1,
			kzg_all_com_ch2, eval_w_e2,
			qa_nizk_vkey_hash,
			mainres_hash,
			comE2, comW2, comF2
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
		r_all_w_1: C1::ScalarField,
		randf: C1::ScalarField,
    ) -> Result<Self, Error> {
		use ark_relations::r1cs::ConstraintSystem;
		use ark_r1cs_std::R1CSVar;
		let job_id = nova1.job_id;
		let circ1 = Phase1Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM,H>::from_nova::<FC>(nova1, com_all_w_1, r_all_w_1)?;

        let cs = ConstraintSystem::<CF1<C1>>::new_ref();
		let res = circ1.generate_constraints_adv(0, cs.clone(), randf).unwrap();
		let res_val = res.val();
		let res_hash_var = res.hash(&circ1.poseidon_config,
			cs.clone());
		let res_hash = res_hash_var.value()?;
		Ok(Self{circ1, res: res_val, randf, res_hash, job_id})
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
			|| Ok(mainres_hash_val) )?; //it is the ONLY PUBLIC VAR of circ!!! 
		mainres_hash.enforce_equal(&mainres_pub)?;
		if B_DEBUG2{
			if phase1_ret.ch.value().is_ok(){
				let phase1_ret_val = phase1_ret.val();
				assert!(phase1_ret_val == self.res);
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
	circ2:  Phase2Circuit<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>,
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
		_r_all_w_1: C1::ScalarField,
		com_all_w_2: C1,
		r_all_w_2: C1::ScalarField,
		mainres: Phase1CircuitRetVal<CF1<C1>, C1>, //will generate cyclepair inp
		inp: CircPubInput<CF1<C1>,C1>, //will be verified against mainres
    ) -> Result<Self, Error> 
	where <C2G2 as ark_ec::Group>::ScalarField: ColEle
	{
		let job_id = nova2.job_id;
		let circ2 = Phase2Circuit::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,LK,GM2,H>::from_nova::<SigmaIR1CS_Inst<C1::ScalarField, C1, CS1, LK, GM2, H>>(nova2, com_all_w_2, r_all_w_2, cyclepair_inputs)?;
		Ok( Self{ circ2, inp, mainres, job_id } )
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
	fn s119_fold(n_steps: usize) -> S119Circ{
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
		for j in 0..n_steps{
			nova.prove_step(&mut rng, vec_stmt[j].to_vec(), None)
				.expect("prove_step err");
		}
		assert_eq!(Fr::from(n_steps as u32), nova.i);

		//driver.rs step 5: com_all_w / r_all_w over the folded witness.
		let (u_i1, w_i1, _r, _cmt) = nova.gen_next_folded()
			.expect("gen_next_folded err");
		let (com_all_w, _qa, r_all_w, _kzg, _ch) = w_i1
			.gen_com_all_w_and_qa_nizk_prf::<Bn254, S119Cm, false>(
				params.0.qa_pp.as_ref().expect("qa_pp null"),
				&params.0.cs1e_pp,
				params.1.qa_vp.as_ref().expect("qa_vp null"),
				&u_i1, &cfg);
		S119Circ::from_nova::<S119Fc>(nova, com_all_w, r_all_w)
			.expect("from_nova err")
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

	/// Repoint u_i.x[0] at the circuit's CURRENT z_0/z_i so a state
	/// edit does not die at step 5's hash before reaching the pins.
	/// u_i is a decider witness, so a prover can make this same move.
	fn s119_rehash_u_i(circ: &mut S119Circ){
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
		circ.zi_part2_inst = Some(zi_ok);
		circ.z_i = Some(z_i_ok);
		circ.u_i = Some(u_i_ok);
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
		let (com_all_w, _qa, r_all_w, _kzg, _ch) = w_i1
			.gen_com_all_w_and_qa_nizk_prf::<Bn254, S119Cm, false>(
				params.0.qa_pp.as_ref().expect("qa_pp null"),
				&params.0.cs1e_pp,
				params.1.qa_vp.as_ref().expect("qa_vp null"),
				&u_i1, &cfg);
		S119Circ::from_nova::<S119Fc>(nova, com_all_w, r_all_w)
			.expect("from_nova err")
	}

	/// EVERY unsatisfied row, not just the first: (num_constraints, set).
	/// which_is_unsatisfied() stops at the first row, which is useless
	/// here (see the note above), so the rows are evaluated directly off
	/// to_matrices() and the assignments.
	fn s103_unsat_rows(circ: &S119Circ) -> (usize, Vec<usize>){
		let cs = ConstraintSystem::<Fr>::new_ref();
		circ.generate_constraints_adv(0, cs.clone(), Fr::zero())
			.expect("gen_cs err");
		//REQUIRED before to_matrices(): make_row calls
		//get_index_unchecked, which panics on a SymbolicLc, and the LCs
		//are symbolic until finalize() inlines them. It changes neither
		//num_constraints nor the assignments.
		cs.finalize();
		let m = cs.to_matrices().expect("matrices null");
		//make_row indexes instance variables first (column 0 is the ONE
		//variable) and then witness variables, so z is exactly the two
		//assignment vectors concatenated in that order.
		let z = {
			let g = cs.borrow().expect("cs borrow null");
			[g.instance_assignment.clone(),
				g.witness_assignment.clone()].concat()
		};
		let dot = |row: &Vec<(Fr, usize)>| row.iter()
			.map(|(c, i)| *c * z[*i]).sum::<Fr>();
		let bad = (0..m.num_constraints)
			.filter(|&r| dot(&m.a[r]) * dot(&m.b[r]) != dot(&m.c[r]))
			.collect::<Vec<usize>>();
		(m.num_constraints, bad)
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
		//the S103 block (78 rows per slot x n_circ = 156, reported in
		//the "Step 7b" log line) followed by the S107 cmF-limb pin
		//(4 nonnative limb equalities, measured 473 rows). Steps 8-10
		//are gated out. So every new row must fall in the final
		//`width` indices -- otherwise the rejection came from
		//somewhere else and this test is measuring the wrong thing.
		//156 + 473 = 629 today; asserted loosely as <= 1024 so a
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

}

