/* Created 08/09/2024.
   Contains Minor updates on syntax changes that use
   CommittedInstanceFoldPot (which contains one more commitment 
    on fixed memory
   Revised: 01/17/2025: added support for fully folding instances (
   	including nonnative group ops)
*/

/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group, short_weierstrass::SWCurveConfig};
use ark_ff::{Field,PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    uint8::UInt8,
    select::CondSelectGadget,
    R1CSVar, ToConstraintFieldGadget,
	ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use crate::Error;
use ark_std::{fmt::Debug, One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::foldpot::{CommittedInstance, sigma_ir1cs::{SigmaIR1CS,ZiPartTwoInst, LookupTableTwoCol,GadgetMapper}};
use super::{CommittedInstanceFoldPot, FOLDPOT_CF_N_POINTS};
use crate::constants::N_BITS_RO;
use crate::folding::circuits::{
    cyclefold::{
        cf_io_len, CycleFoldChallengeGadget, CycleFoldCommittedInstanceVar, NIFSFullGadget,
    },
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNativeGadget, Transcript, TranscriptVar};

/// CommittedInstanceVar contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr, where E1 is the main curve). The peculiarity is that cmE and cmW are
/// represented non-natively over the constraint field.
#[derive(Debug, Clone)]
pub struct CommittedInstanceVarFoldPot<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub u: FpVar<C::ScalarField>,
    pub x: Vec<FpVar<C::ScalarField>>,
    pub cmE: NonNativeAffineVar<C>,
    pub cmW: NonNativeAffineVar<C>,
	/// Commitment to the Fixed Memory 
    pub cmF: NonNativeAffineVar<C>,
}

impl<C> AllocVar<CommittedInstanceFoldPot<C>, CF1<C>> for 
CommittedInstanceVarFoldPot<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CommittedInstanceFoldPot<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            let cmE =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;
            let cmF =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmF), mode)?;

            Ok(Self { u, x, cmE, cmW, cmF })
        })
    }
}

impl<C> CondSelectGadget<C::ScalarField> for NonNativeAffineVar<C> 
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn conditionally_select(
        cond: &Boolean<C::ScalarField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
			x: cond.select(&true_value.x, &false_value.x)?,
			y: cond.select(&true_value.y, &false_value.y)?,
        })
    }
}

impl<C> CondSelectGadget<C::ScalarField> for CommittedInstanceVarFoldPot<C> 
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn conditionally_select(
        cond: &Boolean<C::ScalarField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
		assert!(true_value.x.len()==false_value.x.len());
		let mut x = vec![];
		for i in 0..true_value.x.len(){
			let xi = cond.select(&true_value.x[i], &false_value.x[i])?;
			x.push(xi);
		}
		assert!(x.len()==2 || x.len()==3); //3 for fullmode
        Ok(Self {
			u: cond.select(&true_value.u, &false_value.u)?,
			x: x,
			cmE: cond.select(&true_value.cmE, &false_value.cmE)?,
			cmW: cond.select(&true_value.cmW, &false_value.cmW)?,
			cmF: cond.select(&true_value.cmF, &false_value.cmF)?,
        })
    }
}

impl<C> AbsorbGadget<C::ScalarField> for CommittedInstanceVarFoldPot<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        unimplemented!()
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            vec![self.u.clone()],
            self.x.clone(),
            self.cmE.to_constraint_field()?,
            self.cmW.to_constraint_field()?,
            self.cmF.to_constraint_field()?,
        ]
        .concat())
    }
}

impl<C> CommittedInstanceVarFoldPot<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    /// Additionally it returns the vector of the field elements from the self parameters, so they
    /// can be reused in other gadgets avoiding recalculating (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        self,
        sponge: &T,
        pp_hash: FpVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_sponge_field_elements()?;
        sponge.absorb(&pp_hash)?;
        sponge.absorb(&i)?;
        sponge.absorb(&z_0)?;
        sponge.absorb(&z_i)?;
        sponge.absorb(&U_vec)?;
        let res =  
			Ok((sponge.squeeze_field_elements(1)?.pop().unwrap(), U_vec));
		res
    }

	/// enforce equal to the other
	pub fn enforce_equal(&self, other: &Self)->Result<(),SynthesisError>{
		#[cfg(test)]{
			assert!(self.u.value().unwrap_or_default()==other.u.value().unwrap_or_default());
			assert!(self.x.value().unwrap_or_default()==other.x.value().unwrap_or_default());
			assert!(self.cmE.x.value().unwrap_or_default()==other.cmE.x.value().unwrap_or_default());
			assert!(self.cmE.y.value().unwrap_or_default()==other.cmE.y.value().unwrap_or_default());
			assert!(self.cmW.x.value().unwrap_or_default()==other.cmW.x.value().unwrap_or_default());
			assert!(self.cmW.y.value().unwrap_or_default()==other.cmW.y.value().unwrap_or_default());
			assert!(self.cmF.x.value().unwrap_or_default()==other.cmF.x.value().unwrap_or_default());
			assert!(self.cmF.y.value().unwrap_or_default()==other.cmF.y.value().unwrap_or_default());
			println!("DEBUG USE 601: passing enforce_equal internally");
		}
		self.u.enforce_equal(&other.u)?;
		self.x.enforce_equal(&other.x)?;
		Ok( () )
	}
}

/// Implements the circuit that does the checks of the Non-Interactive Folding Scheme Verifier
/// described in section 4 of [Nova](https://eprint.iacr.org/2021/370.pdf), where the cmE & cmW checks are
/// delegated to the NIFSCycleFoldGadget.
/// NOTE: added handling of cmF.
pub struct NIFSGadgetFoldPot<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> NIFSGadgetFoldPot<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
	C::Config: SWCurveConfig,
{
    pub fn fold_committed_instance(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVarFoldPot<C>, // U_i
        ci2: CommittedInstanceVarFoldPot<C>, // u_i
    ) -> Result<CommittedInstanceVarFoldPot<C>, SynthesisError> {
		// the reason: the folding part of cmE, cmW, and cmF
		// is actually done by cycle fold circuit.
        Ok(CommittedInstanceVarFoldPot {
            cmE: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            cmW: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            cmF: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            // ci3.u = ci1.u + r * ci2.u
            u: ci1.u + &r * ci2.u,
            // ci3.x = ci1.x + r * ci2.x
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| a + &r * &b)
                .collect::<Vec<FpVar<CF1<C>>>>(),
        })
    }

	/// Fold the committed instance in Full.
	/// There are THREE point folding, which is costly (1.6M each x3) = 5M
    pub fn fold_committed_instance_full(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVarFoldPot<C>, // U_i
        ci2: CommittedInstanceVarFoldPot<C>, // u_i
		cmT: NonNativeAffineVar<C>
    ) -> Result<CommittedInstanceVarFoldPot<C>, Error> {
		let cs = ci1.cmE.x.cs();
		println!("DEBUG USE 101: before cs: {}", cs.num_constraints());
		let r_bits = r.to_bits_le()?;
		let cmE = ci1.cmE.add(
			&ci2.cmE.scalar_mul(&r_bits)?)?
			.add( &cmT.scalar_mul(&r_bits)?)?;
		let cmW = ci1.cmW.add(
			&ci2.cmW.scalar_mul(&r_bits)?)?;
		let cmF = ci1.cmF.add(
			&ci2.cmF.scalar_mul(&r_bits)?)?;
		println!("DEBUG USE 102: AFTER cs: {}", cs.num_constraints());


        Ok(CommittedInstanceVarFoldPot {
            cmE: cmE,
            cmW: cmW,
            cmF: cmF,
            // ci3.u = ci1.u + r * ci2.u
            u: ci1.u + &r * ci2.u,
            // ci3.x = ci1.x + r * ci2.x
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| a + &r * &b)
                .collect::<Vec<FpVar<CF1<C>>>>(),
        })
    }


    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    pub fn verify(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVarFoldPot<C>, // U_i
        ci2: CommittedInstanceVarFoldPot<C>, // u_i
        ci3: CommittedInstanceVarFoldPot<C>, // U_{i+1}
    ) -> Result<(), SynthesisError> {
        let ci = Self::fold_committed_instance(r, ci1, ci2)?;

        ci.u.enforce_equal(&ci3.u)?;
        ci.x.enforce_equal(&ci3.x)?;

        Ok(())
    }
}

/// ChallengeGadget computes the RO challenge used for the Nova instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
/// NOTE: only very syntax change for taking CommitedInstanceFoldPot (one
/// more cmF element)
pub struct ChallengeGadgetFoldPot<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> ChallengeGadgetFoldPot<C>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: CommittedInstanceFoldPot<C>,
        u_i: CommittedInstanceFoldPot<C>,
        cmT: C,
    ) -> Vec<bool> {
        transcript.absorb(&pp_hash);
        transcript.absorb(&U_i);
        transcript.absorb(&u_i);
        transcript.absorb_nonnative(&cmT);
        transcript.squeeze_bits(N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        pp_hash: FpVar<CF1<C>>,      // public params hash
        U_i_vec: Vec<FpVar<CF1<C>>>, // apready processed input, so we don't have to recompute these values
        u_i: CommittedInstanceVarFoldPot<C>,
        cmT: NonNativeAffineVar<C>,
    ) -> Result<Vec<Boolean<C::ScalarField>>, SynthesisError> {
        transcript.absorb(&pp_hash)?;
        transcript.absorb(&U_i_vec)?;
        transcript.absorb(&u_i)?;
        transcript.absorb_nonnative(&cmT)?;
        transcript.squeeze_bits(N_BITS_RO)
    }
}

/// AugmentedFCircuit implements the F' circuit (augmented F) defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf) together with the extra constraints defined in
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
#[derive(Debug, Clone)]
pub struct AugmentedFCircuitFoldPot<
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    FC: FCircuit<CF1<C1>> + SigmaIR1CS<H,CF1<C1>,LK, GM>,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
	const H: bool,
> where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
	pub _gm: PhantomData<GM>,
	pub _lk: PhantomData<LK>,
    pub _gc2: PhantomData<GC2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub pp_hash: Option<CF1<C1>>,
    pub i: Option<CF1<C1>>,
    pub i_usize: Option<usize>,
    pub z_0: Option<Vec<C1::ScalarField>>,
	pub z0_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>, //Added
    pub z_i: Option<Vec<C1::ScalarField>>,
	pub zi_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>, //Added
    pub external_inputs: Option<Vec<C1::ScalarField>>,
    pub u_i_cmW: Option<C1>,
    pub u_i_cmF: Option<C1>, //new element compared with Nova
    pub U_i: Option<CommittedInstanceFoldPot<C1>>,
    pub U_i1_cmE: Option<C1>,
    pub U_i1_cmW: Option<C1>,
    pub U_i1_cmF: Option<C1>, //new elemeent compared with Nova
    pub cmT: Option<C1>,
    pub F: FC,              // F circuit
    pub x: Option<CF1<C1>>, // public input (u_{i+1}.x[0])

    // cyclefold verifier on C1
    // Here 'cf1, cf2, cf3' are for each of the CycleFold circuits, corresponding to the fold of cmW,cmE, cmF respectively
    pub cf1_u_i_cmW: Option<C2>,               // input
    pub cf2_u_i_cmW: Option<C2>,               // input
    pub cf3_u_i_cmW: Option<C2>,               // input, ADDED
    pub cf_U_i: Option<CommittedInstance<C2>>, // input, normal NOVA ins
    pub cf1_cmT: Option<C2>,
    pub cf2_cmT: Option<C2>,
    pub cf3_cmT: Option<C2>, //ADDED
    pub cf_x: Option<CF1<C1>>, // public input (u_{i+1}.x[1])
}

impl<C1: CurveGroup, C2: CurveGroup, GC2: CurveVar<C2, CF2<C2>>, LK: LookupTableTwoCol<CF1<C1>>, FC: FCircuit<CF1<C1>> + SigmaIR1CS<H, CF1<C1>,LK, GM>, GM, const H: bool>
    AugmentedFCircuitFoldPot<C1, C2, GC2, LK, FC, GM, H>
where
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	<C1 as Group>::ScalarField: Absorb,
{
    pub fn empty(poseidon_config: &PoseidonConfig<CF1<C1>>, F_circuit: FC, full_mode: bool) -> Self {
		assert!(full_mode==false, "full_mode not supported. Only SuperNova version supports it");
		let dummy_external_inputs = F_circuit.gen_dummy_stmt();
		let zero = C1::ScalarField::zero();
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_dummy= ZiPartTwoInst::new(zero, zero, poseidon_config, full_mode, fq_bits, 0);
        Self {
			_gm: PhantomData,
            _lk: PhantomData,
            _gc2: PhantomData,
            poseidon_config: poseidon_config.clone(),
            pp_hash: None,
            i: None,
            i_usize: None,
            z_0: None,
			z0_part2_inst: Some(zi_dummy.clone()),
            z_i: None,
			zi_part2_inst: Some(zi_dummy),
            external_inputs: Some(dummy_external_inputs),
            u_i_cmW: None,
            u_i_cmF: None, //new element
            U_i: None,
            U_i1_cmE: None,
            U_i1_cmW: None,
            U_i1_cmF: None, //new element
            cmT: None,
            F: F_circuit,
            x: None,
            // cyclefold values
            cf1_u_i_cmW: None,
            cf2_u_i_cmW: None,
            cf3_u_i_cmW: None, //Added for FoldPot
            cf_U_i: None,
            cf1_cmT: None,
            cf2_cmT: None,
            cf3_cmT: None, //Added for FoldPot
            cf_x: None,
        }
    }
}

impl<C1, C2, GC2, LK, FC, GM, const H: bool> ConstraintSynthesizer<CF1<C1>> 
for AugmentedFCircuitFoldPot<C1, C2, GC2, LK, FC,GM,H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    FC: FCircuit<CF1<C1>> + SigmaIR1CS<H, CF1<C1>,LK, GM>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<CF1<C1>,LK> + std::clone::Clone + Debug,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		assert!(self.F.is_full_mode()==false, "only AugmentedF SuperNova supports full mode");
		let stmt = self.external_inputs.clone().expect("external null!");

        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
		//println!(">> step 1");

        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;

        let _external_inputs = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .external_inputs
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.external_inputs_len()]))
        })?;

		// MOVED up here
        // get z_{i+1} from the F circuit
        let i_usize = self.i_usize.unwrap_or(0);
		//TODO: set pre_cmF
		let pre_cmF = None;
		let (witness, wit_cfg, _z_i1_part2) = 
			self.F.gen_witness(&stmt, &self.zi_part2_inst.clone().unwrap(),
				pre_cmF, &self.F.params);
		let wtns_vec = witness.to_vec_fp_var(cs.clone(), &wit_cfg);
        let z_i1 =
            self.F
                .generate_step_constraints(cs.clone(), i_usize, z_i.clone(), wtns_vec)?;
		#[cfg(test)]{
			let zi1_part2_hash = _z_i1_part2.hash(&self.poseidon_config);
			assert!(z_i1[1].value()? == zi1_part2_hash);
		}
        let is_basecase = i.is_zero()?;


        let u_dummy = CommittedInstanceFoldPot::dummy(2);
        let U_i = CommittedInstanceVarFoldPot::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy.clone()))
        })?;
        let U_i1_cmE = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmE.unwrap_or_else(C1::zero))
        })?;
        let U_i1_cmW = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmW.unwrap_or_else(C1::zero))
        })?;
		// added cmF logic here for foldpot
        let U_i1_cmF = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmF.unwrap_or_else(C1::zero))
        })?;
		//println!(">> step 3");

        let cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;

        let cf_u_dummy = CommittedInstance::dummy(cf_io_len(FOLDPOT_CF_N_POINTS));
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or(cf_u_dummy.clone()))
        })?;
		//println!(">> step 4");

        let cf1_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf1_cmT.unwrap_or_else(C2::zero)))?;
        let cf2_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf2_cmT.unwrap_or_else(C2::zero)))?;
        let cf3_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf3_cmT.unwrap_or_else(C2::zero)))?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

		// ORIGINAL position of generating wtns_vec! 
		// TODO: move these constraints to the VERY TOP.


        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) = U_i.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone(),
            z_0.clone(),
            z_i.clone(),
        )?;
        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, cf_U_i_vec) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;

		//println!(">> step 5");
        // P.2. Construct u_i
        let u_i = CommittedInstanceVarFoldPot {
            // u_i.cmE = cm(0)
            cmE: NonNativeAffineVar::new_constant(cs.clone(), C1::zero())?,
            // u_i.u = 1
            u: FpVar::one(),
            // u_i.cmW is provided by the prover as witness
            cmW: NonNativeAffineVar::new_witness(cs.clone(), || {
                Ok(self.u_i_cmW.unwrap_or(C1::zero()))
            })?,
            // u_i.x is computed in step 1
            x: vec![u_i_x, cf_u_i_x],
            cmF: NonNativeAffineVar::new_witness(cs.clone(), || {
                Ok(self.u_i_cmF.unwrap_or(C1::zero()))
            })?,
        };

        // P.3. nifs.verify, obtains U_{i+1} by folding u_i & U_i .
        // compute r = H(u_i, U_i, cmT)
        let r_bits = ChallengeGadgetFoldPot::<C1>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            U_i_vec,
            u_i.clone(),
            cmT.clone(),
        )?;
        let r = Boolean::le_bits_to_fp_var(&r_bits)?;
		//println!(">> step 6");

        // Also convert r_bits to a `NonNativeFieldVar`
        let r_nonnat = {
            let mut bits = r_bits;
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };

        // Notice that NIFSGadget::fold_committed_instance does not fold cmE & cmW.
        // We set `U_i1.cmE` and `U_i1.cmW` to unconstrained witnesses `U_i1_cmE` and `U_i1_cmW`  respectively. (ADDED: similarly for cmF)
        // The correctness of them will be checked on the other curv
        let mut U_i1 = NIFSGadgetFoldPot::<C1>::fold_committed_instance(r, U_i.clone(), u_i.clone())?;
        U_i1.cmE = U_i1_cmE;
        U_i1.cmW = U_i1_cmW;
        U_i1.cmF = U_i1_cmF;
		//println!(">> step 7");

        // P.4.a compute and check the first output of F'
        // Base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{\bot})
        // Non-base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{i+1})
        let (u_i1_x, _) = U_i1.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone() + FpVar::<CF1<C1>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;
        let (u_i1_x_base, _) = CommittedInstanceVarFoldPot::
				new_constant(cs.clone(), u_dummy)?.hash(
            &sponge,
            pp_hash.clone(),
            FpVar::<CF1<C1>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;
        let x = FpVar::new_input(cs.clone(), || Ok(self.x.unwrap_or(u_i1_x_base.value()?)))?;
		

        x.enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i1_x)?)?;
		//println!(">> step 8!!!");

        // CycleFold part
        // C.1. Compute cf1_u_i.x and cf2_u_i.x
        let cfW_x = vec![
            r_nonnat.clone(),
            U_i.cmW.x,
            U_i.cmW.y,
            u_i.cmW.x,
            u_i.cmW.y,
            U_i1.cmW.x,
            U_i1.cmW.y,
        ];
        let cfF_x = vec![
            r_nonnat.clone(),
            U_i.cmF.x,
            U_i.cmF.y,
            u_i.cmF.x,
            u_i.cmF.y,
            U_i1.cmF.x,
            U_i1.cmF.y,
        ];
        let cfE_x = vec![
            r_nonnat, U_i.cmE.x, U_i.cmE.y, cmT.x, cmT.y, U_i1.cmE.x, U_i1.cmE.y,
        ];

        // ensure that cf1_u & cf2_u have as public inputs the cmW & cmE from main instances U_i,
        // u_i, U_i+1 coordinates of the commitments
        // C.2. Construct `cf1_u_i` and `cf2_u_i`
        let cf1_u_i = CycleFoldCommittedInstanceVar {
            // cf1_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf1_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf1_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf1_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf1_u_i.x is computed in step 1
            x: cfW_x,
        };
        let cf2_u_i = CycleFoldCommittedInstanceVar {
            // cf2_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf2_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf2_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf2_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf2_u_i.x is computed in step 1
            x: cfE_x,
        };
		// cf3 is the ADDED cyclefold component for folding cmF
        let cf3_u_i = CycleFoldCommittedInstanceVar {
            // cf3_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf3_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf3_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf3_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf3_u_i.x is computed in step 1
            x: cfF_x,
        };

        // C.3. nifs.verify, 
		// obtains cf1_U_{i+1} by folding cf1_u_i & cf_U_i, 
		// and then cf2_U_{i+1} by folding cf2_u_i & cf1_U_{i+1}. - original
		// and then cf3_U{i+1} again by folding cf3_u_i & cf2_U_{i+1}. (added)

        // compute cf1_r = H(cf1_u_i, cf_U_i, cf1_cmT)
        // cf_r_bits is denoted by rho* in the paper.
        let cf1_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf_U_i_vec,
            cf1_u_i.clone(),
            cf1_cmT.clone(),
        )?;
        // Convert cf1_r_bits to a `NonNativeFieldVar`
        let cf1_r_nonnat = {
            let mut bits = cf1_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        // Fold cf1_u_i & cf_U_i into cf1_U_{i+1}
        let cf1_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf1_r_bits,
            cf1_r_nonnat,
            cf1_cmT,
            cf_U_i,
            cf1_u_i,
        )?;


        // same for cf2_r:
        let cf2_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf1_U_i1.to_native_sponge_field_elements()?,
            cf2_u_i.clone(),
            cf2_cmT.clone(),
        )?;
        let cf2_r_nonnat = {
            let mut bits = cf2_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        let cf2_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf2_r_bits,
            cf2_r_nonnat,
            cf2_cmT,
            cf1_U_i1, // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf2_u_i,
        )?;

		//ADDED -----
        // same for cf3_r:
        let cf3_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf2_U_i1.to_native_sponge_field_elements()?,
            cf3_u_i.clone(),
            cf3_cmT.clone(),
        )?;
        let cf3_r_nonnat = {
            let mut bits = cf3_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        let cf3_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf3_r_bits,
            cf3_r_nonnat,
            cf3_cmT,
            cf2_U_i1.clone(), // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf3_u_i.clone(),
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf3_U_i1.clone().hash(&sponge, pp_hash.clone())?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&sponge, pp_hash)?;
        let cf_x = FpVar::new_input(cs.clone(), || {
            Ok(self.cf_x.unwrap_or(cf_u_i1_x_base.value()?))
        })?;
        cf_x.enforce_equal(&is_basecase.select(&cf_u_i1_x_base, &cf_u_i1_x)?)?;

        Ok(())
    }
}
#[cfg(test)]
pub mod tests_circuits {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_ff::BigInteger;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::foldpot::nifs::tests::prepare_simple_fold_inputs;
    use crate::folding::foldpot::nifs::NIFSFoldPot;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_committed_instance_var() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstanceFoldPot::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            cmF: Projective::rand(&mut rng), //not even need to ensure a part
											 //W, because the circuit only 
											 //checks random combination
            x: vec![Fr::rand(&mut rng); 1],
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        let ciVar =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
        assert_eq!(ciVar.u.value().unwrap(), ci.u);
        assert_eq!(ciVar.x.value().unwrap(), ci.x);
        // the values cmE and cmW are checked in the CycleFold's circuit
        // CommittedInstanceInCycleFoldVar in
        // nova::cyclefold::tests::test_committed_instance_cyclefold_var
    }

    #[test]
    fn test_nifs_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, _, r_Fr) = prepare_simple_fold_inputs();

        let ci3_verifier = NIFSFoldPot::<Projective, Pedersen<Projective>>::verify(r_Fr, &ci1, &ci2, &cmT);
        assert_eq!(ci3_verifier, ci3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let rVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let ci1Var =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci1.clone()))
                .unwrap();
        let ci2Var =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci2.clone()))
                .unwrap();
        let ci3Var =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci3.clone()))
                .unwrap();

        NIFSGadgetFoldPot::<Projective>::verify(
            rVar.clone(),
            ci1Var.clone(),
            ci2Var.clone(),
            ci3Var.clone(),
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_committed_instance_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let sponge = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::from(42u32); // only for test

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let ci = CommittedInstanceFoldPot::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
			cmF: Projective::rand(&mut rng),
        };

        // compute the CommittedInstance hash natively
        let h = ci.hash(&sponge, pp_hash, i, z_0.clone(), z_i.clone());

        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone())).unwrap();
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();
        let ciVar =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();

        let sponge = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        // compute the CommittedInstance hash in-circuit
        let (hVar, _) = ciVar
            .hash(&sponge, pp_hashVar, iVar, z_0Var, z_iVar)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);

        let u_i = CommittedInstanceFoldPot::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
            cmF: Projective::rand(&mut rng),
        };
        let U_i = CommittedInstanceFoldPot::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
            cmF: Projective::rand(&mut rng),
        };
        let cmT = Projective::rand(&mut rng);

        let pp_hash = Fr::from(42u32); // only for testing

        // compute the challenge natively
        let r_bits = ChallengeGadgetFoldPot::<Projective>::get_challenge_native(
            &mut transcript,
            pp_hash,
            U_i.clone(),
            u_i.clone(),
            cmT,
        );
        let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let u_iVar =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(u_i.clone()))
                .unwrap();
        let U_iVar =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();
        let cmTVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(cmT)).unwrap();
        let mut transcriptVar = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        // compute the challenge in-circuit
		let U_iVar_vec = U_iVar.to_sponge_field_elements().unwrap();
        let r_bitsVar = ChallengeGadgetFoldPot::<Projective>::get_challenge_gadget(
            &mut transcriptVar,
            pp_hashVar,
            U_iVar_vec,
            u_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }
}
