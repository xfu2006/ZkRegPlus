/* Created 09/24/2024, 
   Revised 10/01/2024
   Revised 10/18/2024 -> added support from/to gt/g1/g2 vars
*/
/// This circuit computes the following equation:
/// gt1 + e(a,b) = gt2 using non-native arithmetics.
/// here a in G1 and b in G2 and gt1 and gt2 are two points
/// in Gt.
///
/// It simulates the CycleFold circuit, replacing the
/// logic of CycleFold 
/// to 2 pairing and addition in Gt. The idea is pretty similar
/// to the original CycleFold circuit, which performs arithmetic
/// over Basefield of C1. Here, the difference is that we need
/// to encode Pairing operations using basefield, and it involves
/// the G2 of BN254 (not the curvegroup of Grumpkin).
/// So the generic parameter of the declartion of all structs
/// have to include Pair and PairingVar. All related structs
/// are changed correspondingly, but the main change is
/// in generate_constraints() step which performs the
/// pairing operations.
/// NTOE that the public x[] length is 32 (2 gt points, 1 g1 and 1 g2)

use crate::folding::foldpot::utils::B_DEBUG;
use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ec::{Group, CurveGroup,
	pairing::{Pairing},
	short_weierstrass::{SWCurveConfig,Projective},
};
use ark_ff::{BigInteger, PrimeField,Field,ToConstraintField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar},
    //prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	prelude::*,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::circuits::{nonnative::uint::NonNativeUintVar, CF2, CF3};
use crate::folding::foldpot::from_field::{AffineFromField,curve_from_field_elements};
use crate::arith::r1cs::{extract_w_x, R1CS};
use crate::commitment::CommitmentScheme;
use crate::constants::N_BITS_RO;
use crate::folding::nova::{nifs::NIFS, CommittedInstance, Witness};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNativeGadget, Transcript, TranscriptVar};
use crate::Error;

/// Public inputs length for the CyclePairCircuit:
/// It takes four points (a,b,c,d) where
/// (a,b) in G1 and (c,d) in G2.
/// returns the size in CF2 (base elements)
pub fn cp_io_len() -> usize {
	let g2_num = 3;  //for G1 point in projective
	let g1_num = 5;  //for G2 point in projective
	let gt_num = 12; //for Gt point

	g1_num + g2_num + 2*gt_num
}

/// CyclePairCommittedInstanceVar. 
/// It's the same as CycleFoldCommitted Instance (treat it as
/// a standard NOVA folded instance on CF2<C>.
#[derive(Debug, Clone)]
pub struct CyclePairCommittedInstanceVar<C: CurveGroup, 
	GC: CurveVar<C, CF2<C>>>
	where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
	C::BaseField: PrimeField,
{
    pub cmE: GC,
    pub u: NonNativeUintVar<CF2<C>>,
    pub cmW: GC,
    pub x: Vec<NonNativeUintVar<CF2<C>>>,
}

impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CyclePairCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>, //note curve point on base field
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();
            let cmE = GC::new_variable(cs.clone(), 
				|| Ok(val.borrow().cmE), mode)?;
            let cmW = GC::new_variable(cs.clone(), 
				|| Ok(val.borrow().cmW), mode)?;
            let u = NonNativeUintVar::new_variable(cs.clone(), 
				|| Ok(val.borrow().u), mode)?;
            let x = Vec::new_variable(cs.clone(), 
				|| Ok(val.borrow().x.clone()), mode)?;

            Ok(Self { cmE, u, cmW, x })
        })
    }
}

impl<C, GC> AbsorbNonNativeGadget<C::BaseField> for CyclePairCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// Extracts the underlying field elements from `CyclePairCommittedInstanceVar`, in the order
    /// of `u`, `x`, `cmE.x`, `cmE.y`, `cmW.x`, `cmW.y`, `cmE.is_inf || cmW.is_inf` (|| is for
    /// concat).
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<CF2<C>>>, SynthesisError> {
        let mut cmE_elems = self.cmE.to_constraint_field()?;
        let mut cmW_elems = self.cmW.to_constraint_field()?;

        // See `transcript/poseidon.rs: TranscriptVar::absorb_point` for details
        // why the last element is unnecessary.
        cmE_elems.pop();
        cmW_elems.pop();

        Ok([
            self.u.to_native_sponge_field_elements()?,
            self.x
                .iter()
                .map(|i| i.to_native_sponge_field_elements())
                .collect::<Result<Vec<_>, _>>()?
                .concat(),
            cmE_elems,
            cmW_elems,
        ]
        .concat())
    }
}

impl<C, GC> CyclePairCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash_cyclefold. Returns `H(U_i)`, where `U` is the `CommittedInstance`
    /// for CyclePair. Additionally it returns the vector of the field elements from the self
    /// parameters, so they can be reused in other gadgets avoiding recalculating (reconstraining)
    /// them.
    #[allow(clippy::type_complexity)]
    pub fn hash<S: CryptographicSponge, T: TranscriptVar<CF2<C>, S>>(
        self,
        sponge: &T,
        pp_hash: FpVar<CF2<C>>, // public params hash
    ) -> Result<(FpVar<CF2<C>>, Vec<FpVar<CF2<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_native_sponge_field_elements()?;
        sponge.absorb(&pp_hash)?;
        sponge.absorb(&U_vec)?;
        Ok((sponge.squeeze_field_elements(1)?.pop().unwrap(), U_vec))
    }
}

/// This is the gadget used in the AugmentedFCircuit to verify the CyclePair 
/// instances folding,
/// which checks the correct RLC of u,x,cmE,cmW (hence the name containing 'Full', since it checks
/// all the RLC values, not only the native ones). It assumes that ci2.cmE=0, ci2.u=1.
pub struct NIFSFullGadgetCyclePair<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> NIFSFullGadgetCyclePair<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn fold_committed_instance(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeUintVar<CF2<C>>,
        cmT: GC,
        ci1: CyclePairCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CyclePairCommittedInstanceVar<C, GC>,
    ) -> Result<CyclePairCommittedInstanceVar<C, GC>, SynthesisError> {
        Ok(CyclePairCommittedInstanceVar {
            cmE: cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE,
            cmW: ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?,
            u: ci1.u.add_no_align(&r_nonnat).modulo::<C::ScalarField>()?,
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| {
                    a.add_no_align(&r_nonnat.mul_no_align(&b)?)
                        .modulo::<C::ScalarField>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub fn verify(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeUintVar<CF2<C>>,
        cmT: GC,
        ci1: CyclePairCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CyclePairCommittedInstanceVar<C, GC>,
        ci3: CyclePairCommittedInstanceVar<C, GC>,
    ) -> Result<(), SynthesisError> {
        let ci = Self::fold_committed_instance(r_bits, r_nonnat, cmT, ci1, ci2)?;

        ci.cmE.enforce_equal(&ci3.cmE)?;
        ci.u.enforce_equal_unaligned(&ci3.u)?;
        ci.cmW.enforce_equal(&ci3.cmW)?;
        for (x, y) in ci.x.iter().zip(ci3.x.iter()) {
            x.enforce_equal_unaligned(y)?;
        }

        Ok(())
    }
}

/// CyclePairChallengeGadget computes the RO challenge used for the CyclePair instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct CyclePairChallengeGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>, // Nova's Curve2, the one used for the CyclePair circuit
    _gc: PhantomData<GC>,
}
impl<C, GC> CyclePairChallengeGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as CurveGroup>::BaseField: Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn get_challenge_native<T: Transcript<C::BaseField>>(
        transcript: &mut T,
        pp_hash: C::BaseField, // public params hash
        U_i: CommittedInstance<C>,
        u_i: CommittedInstance<C>,
        cmT: C,
    ) -> Vec<bool> {
        transcript.absorb(&pp_hash);
        transcript.absorb_nonnative(&U_i);
        transcript.absorb_nonnative(&u_i);
        transcript.absorb_point(&cmT);
        transcript.squeeze_bits(N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<C::BaseField, S>>(
        transcript: &mut T,
        pp_hash: FpVar<C::BaseField>, // public params hash
        U_i_vec: Vec<FpVar<C::BaseField>>,
        u_i: CyclePairCommittedInstanceVar<C, GC>,
        cmT: GC,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        transcript.absorb(&pp_hash)?;
        transcript.absorb(&U_i_vec)?;
        transcript.absorb_nonnative(&u_i)?;
        transcript.absorb_point(&cmT)?;
        transcript.squeeze_bits(N_BITS_RO)
    }
}

/// CyclePairCircuit contains the constraints that check 
/// pairing function gt1 + e(a,b) = gt_2
/// Here: C1 and C2G2 are are the two G1 and G2 groups of 
/// the SAME pairing engine
/// (like Projective1Var and Project2Var of BN254 - instead of cycles of
/// BN254 and Grumpkin!). Note that CF2 is redefined in circuits.mod,
/// CF3 is the original sonobe CF2. 
#[derive(Debug, Clone)]
pub struct CyclePairCircuit<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>>, C1, C2G2>
	where
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	CF3<E::G2>: PrimeField,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
{
	pub _p: PhantomData<P>,
    /// points to be checked in CyclePairCircuit
	/// gt1 + e(a,b) = gt2 (note in code. + is represented as *)
	pub gt1: E::TargetField,
	pub a: E::G1,
	pub b: E::G2,
	pub gt2: E::TargetField,

	/// public inputs (encodes the points)
    pub x: Vec<CF2<E::G1>>, // should be the 32 Fq elements
}

pub fn projective_from_field_elements<F:PrimeField, 
	F2: Field<BasePrimeField=F>, 
	Cfg: SWCurveConfig<BaseField=F2> >(v: &Vec<F>) ->  Projective<Cfg>{
		let n = v.len();
		println!("--- DUMP v: ---");
		for x in v{
			println!("-- {} --", x);
		}
		assert!(n%3==0);
		let (c0, c1, c2) = (v[0..n/3].to_vec(), v[n/3..2*n/3].to_vec(),
			v[2*n/3..n].to_vec());
		let (x,y,_z) = (F2::from_base_prime_field_elems(&c0).unwrap(), F2::from_base_prime_field_elems(&c1).unwrap(), F2::from_base_prime_field_elems(&c2).unwrap());
		let (zero, one) = (F2::zero(), F2::one());
		let (x,y,z) = if x==zero && y==zero{ (zero, zero, zero)	}else{
			(x,y,one)
		};

		Projective::<Cfg>{x,y,z}
}


impl <E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>>, C1, C2G2>
CyclePairCircuit<E,P, C1, C2G2> 
	where
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	CF3<E::G2>: PrimeField,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
    pub fn empty() -> Self {
		let g1_zero = E::G1::zero();
		let g2_zero = E::G2::zero();
		let gt_zero = E::TargetField::zero();
		let _zero = <E::G1 as CurveGroup>::BaseField::zero();
		let x = [
			gt_zero.to_field_elements().unwrap(),
			g1_zero.to_field_elements().unwrap(),
			g2_zero.to_field_elements().unwrap(),
			gt_zero.to_field_elements().unwrap()].concat();
		assert!(x.len()==cp_io_len());
		if B_DEBUG {
			let gt3 = E::pairing(&g1_zero, &g2_zero).0;
			let gt4 = gt_zero * gt3;
			assert!(gt4==gt_zero);
		}
        Self {
            _p: PhantomData,
			gt1: gt_zero,
			a: g1_zero,
			b: g2_zero,
			gt2: gt_zero,
			x: x
        }
    }

	/// from (gt1, a, b, gt2) generate (12 + 3 + 5 + 12) = 32 Fq elements
	pub fn real_inst_to_fq(gt1: &E::TargetField, a: &E::G1, b: &E::G2, gt2: &E::TargetField) -> Vec<CF2<E::G1>>{
		let vec_a = a.to_field_elements().unwrap(); //3 compared with get_cm in utils, wasted one element.
		let vec_b = b.to_field_elements().unwrap(); //5.
		let vec_gt1 = gt1.to_field_elements().unwrap();
		let vec_gt2 = gt2.to_field_elements().unwrap();
        let vec: Vec<CF2<E::G1>> = [
			vec_gt1, vec_a, vec_b, vec_gt2,
        ].concat();
	
		vec
	}

	/// generate from the x input
	pub fn from_vec_fq(v: &Vec<CF3<E::G1>>) -> Self{
		assert!(v.len()==32);
		let vec_gt1: Vec<<E::TargetField as Field>::BasePrimeField> = v[0..12].to_vec();
		let vec_a = v[12..15].to_vec();
		let mut vec_b = v[15..20].to_vec();
		vec_b.push( CF3::<E::G1>::zero() );
		let vec_gt2 = v[20..32].to_vec();
		let gt1: E::TargetField = <E::TargetField as Field>::from_base_prime_field_elems(&vec_gt1[..]).unwrap();
		let a: C1 = curve_from_field_elements::<C1>(&vec_a);
		let b: E::G2 = curve_from_field_elements::<E::G2>(&vec_b);
		let gt2 = E::TargetField::from_base_prime_field_elems(&vec_gt2[..]).unwrap();

		if B_DEBUG {
			let gt3 = E::pairing(&a, &b).0;
			let gt4 = gt1 * gt3;
			assert!(gt4==gt2);
		}
		Self{
			_p: PhantomData,
			gt1, a, b, gt2, 
			x: v.clone()
		}
	}
}

/// if true return FpVar of 1; otherwise zero
#[allow(dead_code)]
fn is_slice_zero<F:PrimeField>(vec: &[FpVar<F>])->FpVar<F>{
	let cs = vec[0].cs();
	for x in vec{
		if !x.value().unwrap().is_zero() {
			return FpVar::<F>::new_constant(cs,  F::one()).unwrap();
		}
	}
	return FpVar::<F>::new_constant(cs.clone(),  F::zero()).unwrap();
}

impl <E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>>, C1, C2G2>
ConstraintSynthesizer<CF2<C1>> for CyclePairCircuit<E,P, C1, C2G2> 
	where
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField>,
	C2G2: CurveGroup,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF2<E::G1>>) -> Result<(), SynthesisError> {
		//1. get the points in var
		let a_var = P::G1Var::new_witness(cs.clone(), || Ok(self.a.clone()))?;
		let b_var = P::G2Var::new_witness(cs.clone(), || Ok(self.b.clone()))?;
		let gt1_var = P::GTVar::new_witness(cs.clone(),||Ok(self.gt1.clone()))?;
		let gt2_var = P::GTVar::new_witness(cs.clone(),||Ok(self.gt2.clone()))?;
		let a_p = P::prepare_g1(&a_var)?;
		let b_p = P::prepare_g2(&b_var)?; 


		let _n1 = cs.num_constraints();
		let m1 = P::miller_loop(&[a_p], &[b_p.clone()])?;
		let gt3 = P::final_exponentiation(&m1)?;
		let lhs = &gt1_var * &gt3;
		let rhs = gt2_var.clone();
		if B_DEBUG {
			assert!(lhs.value()?==rhs.value()?, "gt1 * e(a+b) != gt2");
		}
		lhs.enforce_equal(&rhs)?;

		//2. construct and verify x
        let x = Vec::<FpVar<CF2<E::G1>>>::new_input(cs.clone(), || {
            Ok(self.x)
        })?;
        if B_DEBUG { assert_eq!(x.len(), cp_io_len()); } // non-constrained sanity check
        
		//3. Check that the points coordinates are placed as the public 
		// input x:  [gt1, a, b, gt2]
		let va: Vec<FpVar<CF2<E::G1>>> = a_var.to_constraint_field().unwrap();
		let vb: Vec<FpVar<CF3<E::G2>>> = b_var.to_constraint_field().unwrap();
		let v_gt1:Vec<FpVar<CF2<E::G1>>>=gt1_var.to_constraint_field().unwrap();
		let v_gt2:Vec<FpVar<CF2<E::G1>>>=gt2_var.to_constraint_field().unwrap();
		//3.5 fix va and vb is they zero, clear the 3rd coordinate to zero 
		//as well (infinitey)
		let _one_var = FpVar::<CF2<E::G1>>::one();
		//va[2] = is_slice_zero(&va[0..2]).is_zero()?.select(&one_var, &va[2])?;
		//vb[4] = is_slice_zero(&vb[0..4]).is_zero()?.select(&one_var, &vb[4])?;


        let computed_x: Vec<FpVar<CF2<E::G1>>> = [
			v_gt1, va, vb, v_gt2,
        ]
        .concat();
		assert!(computed_x.len()==x.len());

		if B_DEBUG {
			assert!(computed_x.value()?==x.value()?);
			//println!("DEBUG USE 9301.3 verify computed_x = x");
		}
		computed_x.enforce_equal(&x)?;


		Ok( () )
	}
}

/// Folds the given cyclepair circuit and its instances. 
/// The only different from fold_cyclefold_circuit is that
/// it takes a new template parameter C2G2: like the G2 of BN254,
/// and the C2 is the curve group of Grumpkin.
/// Basically it computes the advice of cf_U and cf_W instances
/// for folded and incoming instance.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn fold_cyclepair_circuit<E:Pairing<G1=C1,G2=C2G2>, 
	P: PairingVar<E,CF3<C2G2>>,
	C1, GC1, C2G2, C2, GC2, FC, CS1, CS2, const H: bool>(
    transcript: &mut impl Transcript<C1::ScalarField>,
    cf_r1cs: &R1CS<C2::ScalarField>, //C1::BaseField
    cf_cs_params: CS2::ProverParams,
    pp_hash: C1::ScalarField,      // public params hash
    cf_W_i: Witness<C2>,           // witness of the running instance
    cf_U_i: CommittedInstance<C2>, // running instance
    cf_u_i_x: Vec<C2::ScalarField>,
    cf_circuit: CyclePairCircuit<E, P, C1, C2G2>,
    rng: &mut impl RngCore,
) -> Result<
    (
        Witness<C2>,
        CommittedInstance<C2>, // u_i
        Witness<C2>,           // W_i1
        CommittedInstance<C2>, // U_i1
        C2,                    // cmT
        C2::ScalarField,       // r_Fq
    ),
    Error,
>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	//Newly added 
	C2G2: CurveGroup,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2: CurveGroup<BaseField=C1::ScalarField, ScalarField=C1::BaseField>,
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	CF3<E::G2>: PrimeField,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
{
	//1. build R1CS and extract witness and statement (cf_w_i and cf_x_i)
    let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
    cf_circuit.generate_constraints(cs2.clone())?;
	cs2.finalize();
    let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let (cf_w_i, cf_x_i) = extract_w_x::<C1::BaseField>(&cs2);
    if cf_x_i != cf_u_i_x {
        return Err(Error::NotEqual);
    }
    if B_DEBUG { assert_eq!(cf_x_i.len(), cp_io_len()); }

	//println!("DEBUG USE 911.2 BEFORE checking");
    //2. compute the committed instance 
    let cf_w_i = Witness::<C2>::new::<H>(cf_w_i.clone(), 
		cf_r1cs.A.n_rows, rng);
    let cf_u_i: CommittedInstance<C2> = 
		cf_w_i.commit::<CS2, H>(&cf_cs_params, cf_x_i.clone())?;


    //3. compute T* and cmT* for CyclePairCircuit
    let (cf_T, cf_cmT) = NIFS::<C2, CS2, H>::compute_cyclefold_cmT(
        &cf_cs_params,
        &cf_r1cs,
        &cf_w_i,
        &cf_u_i,
        &cf_W_i,
        &cf_U_i,
    )?;

	//4. compute the random challenge
    let cf_r_bits = CyclePairChallengeGadget::<C2, GC2>::get_challenge_native(
        transcript,
        pp_hash,
        cf_U_i.clone(),
        cf_u_i.clone(),
        cf_cmT,
    );
    let cf_r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&cf_r_bits)) .expect("cf_r_bits out of bounds");


    let (cf_W_i1, cf_U_i1) = NIFS::<C2, CS2, H>::fold_instances(
        cf_r_Fq, &cf_W_i, &cf_U_i, &cf_w_i, &cf_u_i, &cf_T, cf_cmT,
    )?;
    Ok((cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, cf_r_Fq))
}

#[cfg(test)]
pub mod tests_cyclepair {
    use ark_bn254::{Bn254,constraints::GVar, constraints::PairingVar, Fq, Fr, G1Projective as Bn254G1, G2Projective as Bn254G2};
    use ark_crypto_primitives::sponge::{
        constraints::CryptographicSpongeVar,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    };
	use ark_ec::{pairing::{Pairing}};
    use ark_r1cs_std::R1CSVar;
    use ark_std::{UniformRand,test_rng};
	use ark_ff::ToConstraintField;

    use super::*;
    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::transcript::poseidon::poseidon_canonical_config;

	type TargetField = <Bn254 as Pairing>::TargetField;
	fn rand_real_inst() -> (TargetField, Bn254G1, Bn254G2, TargetField, Vec<Fq>){
		let mut rng = test_rng();
		let a =  Bn254G1::rand(&mut rng);
		let b =  Bn254G2::rand(&mut rng);

		let t1 =  Bn254G1::rand(&mut rng);
		let t2 =  Bn254G2::rand(&mut rng);
		let gt1 = Bn254::pairing(t1, t2).0;
		let gt2 = gt1 * Bn254::pairing(a,b).0;

		let vec_a = a.to_field_elements().unwrap(); //3 compared with get_cm in utils, wasted one element.
		let vec_b = b.to_field_elements().unwrap(); //5.
		let vec_gt1 = gt1.to_field_elements().unwrap();
		let vec_gt2 = gt2.to_field_elements().unwrap();
        let cfW_u_i_x: Vec<Fq> = [
			vec_gt1, vec_a, vec_b, vec_gt2,
        ].concat();

		(gt1, a, b, gt2, cfW_u_i_x)
	}

    #[test]
    fn test_CyclePairCircuit_constraints() {
		let (gt1, a, b, gt2, cfW_u_i_x) = rand_real_inst();
        let cs = ConstraintSystem::<Fq>::new_ref();
        let cfW_circuit = CyclePairCircuit::<Bn254, PairingVar, Bn254G1, Bn254G2> {
			_p: PhantomData,
			gt1: gt1,
			a: a,
			b: b,
			gt2: gt2,
            x: cfW_u_i_x.clone(),
        };
        cfW_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

		let circ2 = CyclePairCircuit::<Bn254, PairingVar, Bn254G1, Bn254G2>::empty();
        let cs2 = ConstraintSystem::<Fq>::new_ref();
		circ2.generate_constraints(cs2.clone()).unwrap();
    }

	#[test]
	fn test_cyclepair_from_to(){
		let (gt1, a, b, gt2, cfW_u_i_x) = rand_real_inst();
		let vec_fq = CyclePairCircuit::<Bn254, PairingVar, 
			Bn254G1, Bn254G2>::real_inst_to_fq(&gt1, &a, &b, &gt2);
		assert!(vec_fq==cfW_u_i_x);
        let c = CyclePairCircuit::<Bn254, PairingVar, 
			Bn254G1, Bn254G2>::from_vec_fq(&vec_fq);
		assert!(c.gt1 ==gt1 && c.gt2==gt2 && c.a ==a && c.b==b);

	}

    #[test]
    fn test_nifs_full_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, r_Fr) = prepare_simple_fold_inputs();

        let cs = ConstraintSystem::<Fq>::new_ref();

        let r_nonnatVar = NonNativeUintVar::<Fq>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();

        let ci1Var =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(ci1.clone())
            })
            .unwrap();
        let ci2Var =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(ci2.clone())
            })
            .unwrap();
        let ci3Var =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(ci3.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        NIFSFullGadgetCyclePair::<Bn254G1, GVar>::verify(
            r_bitsVar,
            r_nonnatVar,
            cmTVar,
            ci1Var,
            ci2Var,
            ci3Var,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_cyclepair_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();
        let mut transcript = PoseidonSponge::<Fq>::new(&poseidon_config);

        let u_i = CommittedInstance::<Bn254G1> {
            cmE: Bn254G1::zero(), // zero on purpose, so we test also the zero point case
            u: Fr::zero(),
            cmW: Bn254G1::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(7) // 7 = cp_io_len
                .collect(),
        };
        let U_i = CommittedInstance::<Bn254G1> {
            cmE: Bn254G1::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Bn254G1::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(16) // 16 = cp_io_len
                .collect(),
        };
        let cmT = Bn254G1::rand(&mut rng);

        // compute the challenge natively
        let pp_hash = Fq::from(42u32); // only for test
        let r_bits = CyclePairChallengeGadget::<Bn254G1, GVar>::get_challenge_native(
            &mut transcript,
            pp_hash,
            U_i.clone(),
            u_i.clone(),
            cmT,
        );

        let cs = ConstraintSystem::<Fq>::new_ref();
        let u_iVar =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(u_i.clone())
            })
            .unwrap();
        let U_iVar =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();
        let mut transcript_var =
            PoseidonSpongeVar::<Fq>::new(ConstraintSystem::<Fq>::new_ref(), &poseidon_config);

        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let r_bitsVar = CyclePairChallengeGadget::<Bn254G1, GVar>::get_challenge_gadget(
            &mut transcript_var,
            pp_hashVar,
            U_iVar.to_native_sponge_field_elements().unwrap(),
            u_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        let r = Fq::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }

    #[test]
    fn test_cyclepair_hash_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();
        let sponge = PoseidonSponge::<Fq>::new(&poseidon_config);

        let U_i = CommittedInstance::<Bn254G1> {
            cmE: Bn254G1::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Bn254G1::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(7) // 7 = cp_io_len in Nova
                .collect(),
        };
        let pp_hash = Fq::from(42u32); // only for test
        let h = U_i.hash_cyclefold(&sponge, pp_hash);

        let cs = ConstraintSystem::<Fq>::new_ref();
        let U_iVar =
            CyclePairCommittedInstanceVar::<Bn254G1, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let (hVar, _) = U_iVar
            .hash(
                &PoseidonSpongeVar::new(cs.clone(), &poseidon_config),
                pp_hashVar,
            )
            .unwrap();
        hVar.enforce_equal(&FpVar::new_witness(cs.clone(), || Ok(h)).unwrap())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
