#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused)]

extern crate std;

use ark_relations::r1cs::SynthesisError;
use super::PairingVar as PG;
use crate::pairing::{CurveVar,AllocVar};
use std::fmt;

use crate::{
    fields::{fp::FpVar, fp12::Fp12Var, fp2::Fp2Var, FieldVar},
    groups::bn::{G1AffineVar, G1PreparedVar, G1Var, G2PreparedVar, G2Var},
};
use ark_ec::bn::{Bn, BnConfig, TwistType};
use ark_ff::BitIteratorBE;
use ark_std::marker::PhantomData;


/// Specifies the constraints for computing a pairing in a BLS12 bilinear group.
pub struct PairingVar<P: BnConfig>(PhantomData<P>);

type Fp2V<P> = Fp2Var<<P as BnConfig>::Fp2Config>;

impl <P:BnConfig> Clone for PairingVar<P>{
    fn clone(&self) -> Self{
		panic!("this function should not be called. Just for syntax compatibility in FoldPotSuper")
    }
}    
impl <P:BnConfig> std::fmt::Debug for PairingVar<P>{
	 fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //write!(f, "Hi: {}", self.id)
		panic!("this function should not be called. Just for syntax compatibility in FoldPot")
    }
}    

impl<P: BnConfig> PairingVar<P> {
    #[tracing::instrument(target = "r1cs")]
    fn ell(
        f: &mut Fp12Var<P::Fp12Config>,
        coeffs: &(Fp2V<P>, Fp2V<P>),
        p: &G1AffineVar<P>,
    ) -> Result<(), SynthesisError> {
		// the same as bls (note because ElfCoeff has 2 elements
		// it's eseentially unpacking to 3 elements
        let zero = FpVar::<P::Fp>::zero();

        match P::TWIST_TYPE {
            TwistType::M => {
                let c0 = coeffs.0.clone();
                let mut c1 = coeffs.1.clone();
                let c2 = Fp2V::<P>::new(p.y.clone(), zero);

                c1.c0 *= &p.x;
                c1.c1 *= &p.x;
                *f = f.mul_by_014(&c0, &c1, &c2)?;
                Ok(())
            },
            TwistType::D => {
                let c0 = Fp2V::<P>::new(p.y.clone(), zero);
                let mut c1 = coeffs.0.clone();
                let c2 = coeffs.1.clone();

                c1.c0 *= &p.x;
                c1.c1 *= &p.x;
                *f = f.mul_by_034(&c0, &c1, &c2)?;
                Ok(())
            },
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn exp_by_neg_x(f: &Fp12Var<P::Fp12Config>) -> Result<Fp12Var<P::Fp12Config>, SynthesisError> {
        let mut result = f.optimized_cyclotomic_exp(P::X)?;
        if P::X_IS_NEGATIVE {
            result = result.unitary_inverse()?;
        }
        Ok(result)
    }
}

impl<P: BnConfig> PG<Bn<P>> for PairingVar<P> {
	type G1Var = G1Var<P>;
    type G2Var = G2Var<P>;
    type G1PreparedVar = G1PreparedVar<P>;
    type G2PreparedVar = G2PreparedVar<P>;
    type GTVar = Fp12Var<P::Fp12Config>;

    #[tracing::instrument(target = "r1cs")]
    fn miller_loop(
        ps: &[Self::G1PreparedVar],
        qs: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError> {
		// here compared with the "raw" version in algebra
		// skipped the check of zero cases (negligible probability)
        let mut pairs = vec![];
        for (p, q) in ps.iter().zip(qs.iter()) {
            pairs.push((p, q.ell_coeffs.iter()));
        }
        let mut f = Self::GTVar::one();

		// here: also simplification: no chunks by 4
		for i in (1..P::ATE_LOOP_COUNT.len()).rev() {
			if i!=P::ATE_LOOP_COUNT.len()-1{
            	f.square_in_place()?;
			}

            for &mut (p, ref mut coeffs) in pairs.iter_mut() {
                Self::ell(&mut f, coeffs.next().unwrap(), &p.0)?;
            }

			let bit = P::ATE_LOOP_COUNT[i-1];
			if bit==1 || bit==-1{
                for &mut (p, ref mut coeffs) in pairs.iter_mut() {
                    Self::ell(&mut f, &coeffs.next().unwrap(), &p.0)?; 
                }
			}
        }

        if P::X_IS_NEGATIVE {
            f = f.unitary_inverse()?;
        }

		for &mut (p, ref mut coeffs) in pairs.iter_mut() {
			Self::ell(&mut f, &coeffs.next().unwrap(), &p.0)?; 
		}

		for &mut (p, ref mut coeffs) in pairs.iter_mut() {
			Self::ell(&mut f, &coeffs.next().unwrap(), &p.0)?; 
		}

        Ok(f)
    }

    #[tracing::instrument(target = "r1cs")]
    fn final_exponentiation(f: &Self::GTVar) -> Result<Self::GTVar, SynthesisError> {
		/* The following is for bls12
        // Computing the final exponentation following
        // https://eprint.iacr.org/2016/130.pdf.
        // We don't use their "faster" formula because it is difficult to make
        // it work for curves with odd `P::X`.
        // Hence we implement the slower algorithm from Table 1 below.
        let f1 = f.unitary_inverse()?;
        f.inverse().and_then(|mut f2| {
            // f2 = f^(-1);
            // r = f^(p^6 - 1)
            let mut r = f1;
            r *= &f2;

            // f2 = f^(p^6 - 1)
            f2 = r.clone();
            // r = f^((p^6 - 1)(p^2))
            r.frobenius_map_in_place(2)?; //r<- r^{p^2}

            // r = f^((p^6 - 1)(p^2) + (p^6 - 1))
            // r = f^((p^6 - 1)(p^2 + 1))
            r *= &f2;

            // Hard part of the final exponentation is below:
            // From https://eprint.iacr.org/2016/130.pdf, Table 1
            let mut y0 = r.cyclotomic_square()?;
            y0 = y0.unitary_inverse()?;
            let mut y5 = Self::exp_by_x(&r)?; //r is f?
            let mut y1 = y5.cyclotomic_square()?;
            let mut y3 = y0 * &y5;

            y0 = Self::exp_by_x(&y3)?;

            let y2 = Self::exp_by_x(&y0)?;

            let mut y4 = Self::exp_by_x(&y2)?;

            y4 *= &y1; 
            y1 = Self::exp_by_x(&y4)?;
            y3 = y3.unitary_inverse()?;
            y1 *= &y3;
            y1 *= &r;

            y3 = r.clone();
            y3 = y3.unitary_inverse()?;
            y0 *= &r;
            y0.frobenius_map_in_place(3)?; //t0 <- t0^{p^3}

            y4 *= &y3;
            y4.frobenius_map_in_place(1)?; //t4 <- t5^{p}

            y5 *= &y2;
            y5.frobenius_map_in_place(2)?;

            y5 *= &y0;
            y5 *= &y4;
            y5 *= &y1;
            Ok(y5)
        })
		*/
		// algoirthm 10 from : <https://eprint.iacr.org/2015/192.pdf>
		// also: <https://github.com/onurinanc/noir-bn254/blob/main/src/bn254/pairing.nr>
		// NOTE that even the (p^4 - p^2 + 1)/r is formula is the same
		// as BLS12, but the extract linear equation (e.g., on top of
		// page 4 of 192.pdf is DIFFERENT from BLS12, thus the computation
		// map is different.
        let f1 = f.unitary_inverse()?;
        f.inverse().and_then(|mut f2| {
            // f2 = f^(-1);
            // r = f^(p^6 - 1)
            let mut r = f1;
            r *= &f2;

            // f2 = f^(p^6 - 1)
            f2 = r.clone();
            // r = f^((p^6 - 1)(p^2))
            r.frobenius_map_in_place(2)?;

            // r = f^((p^6 - 1)(p^2) + (p^6 - 1))
            // r = f^((p^6 - 1)(p^2 + 1))
            r *= &f2;

			// r = f^((p^6-1)(p^2+1)) is needed (see page 2) of
			// <https://eprint.iacr.org/2015/192.pdf>
			// this part is the same as bls12
            // Hard part of the final exponentation is below:
			// https://eprint.iacr.org/2015/192.pdf
			// Algorithm 10. Here y0 corresponds to t0, and y1 for t1, etc.
            let mut y0 = r.clone();
            y0 = Self::exp_by_neg_x(&y0)?;
            y0 = y0.unitary_inverse()?; //t0 = f^{-u}
            y0 = y0.cyclotomic_square()?; //t0 = t0^2
			let mut y2 = y0.clone();
			y2 = Self::exp_by_neg_x(&y2)?;
			y2 = y2.unitary_inverse()?; //t2 = t0^{-u}
			let mut y1 = y2.cyclotomic_square()?; //t1 = t2^2
			y2 *= &y1; // t2 = t2*t1
			y2 *= &r;  // t2 = t2*f

			y1 = y2.clone();
			y1 = Self::exp_by_neg_x(&y1)?;
			y1 = y1.cyclotomic_square()?;
			y1 *= &y2;
			y1 = y1.unitary_inverse()?; //t1 = t2^{-2u-1}
			let mut y3 = y1.unitary_inverse()?; //t3 = t1^{-1}
			y1 = y0.cyclotomic_square()?; //t1 = t0^2
			y1 *= &r; //t1 = t1 * f
			y1 = y1.unitary_inverse()?; //t1 = t1^{-1}
			y1 *= &y3; //t1 = t1 * t3

			y0 *= &y1; //t0 = t0 * t1
			y2 *= &y1; //t2 = t2 * t1
			y3 = y1.clone();
            y3.frobenius_map_in_place(2)?; //t3 =t1^{p^2}
			y2 *= &y3; //t2 = t2 * t3

			y3 = r.unitary_inverse()?; //t3 = f^{-1}
			y3 *= &y0; //t3 = t0 * t3
			y1 = y3.clone();
			y1.frobenius_map_in_place(3)?; //t1 = t3^{p^3}

			y2 *= &y1; //t2 * t1
			y1 = y0.clone();
			y1.frobenius_map_in_place(1)?; //t1 = t0^{p}

			y1 *= &y2; //t1 = t1 * t2
            Ok(y1)
        })
    }

    #[tracing::instrument(target = "r1cs")]
    fn prepare_g1(p: &Self::G1Var) -> Result<Self::G1PreparedVar, SynthesisError> {
        Self::G1PreparedVar::from_group_var(p)
    }

    #[tracing::instrument(target = "r1cs")]
    fn prepare_g2(q: &Self::G2Var) -> Result<Self::G2PreparedVar, SynthesisError> {
        Self::G2PreparedVar::from_group_var(q)
    }
}

