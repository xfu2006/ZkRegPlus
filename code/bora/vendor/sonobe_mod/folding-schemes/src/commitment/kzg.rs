/// Adaptation of the prover methods and structs from arkworks/poly-commit's KZG10 implementation
/// into the CommitmentScheme trait.
///
/// The motivation to do so, is that we want to be able to use KZG / Pedersen for committing to
/// vectors indistinctly, and the arkworks KZG10 implementation contains all the methods under the
/// same trait, which requires the Pairing trait, where the prover does not need access to the
/// Pairing but only to G1.
use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, Polynomial,
};
use ark_poly_commit::kzg10::{
    Commitment as KZG10Commitment, Proof as KZG10Proof, VerifierKey, KZG10,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::rand::RngCore;
use ark_std::{borrow::Cow, fmt::Debug};
use ark_std::{One, Zero};
use core::marker::PhantomData;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use super::CommitmentScheme;
use crate::transcript::Transcript;
use crate::utils::vec::poly_from_vec;
use crate::Error;

/// ProverKey defines a similar struct as in ark_poly_commit::kzg10::Powers, but instead of
/// depending on the Pairing trait it depends on the CurveGroup trait.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ProverKey<'a, C: CurveGroup> {
    /// Group elements of the form `β^i G`, for different values of `i`.
    pub powers_of_g: Cow<'a, [C::Affine]>,
}

impl<'a, C: CurveGroup> CanonicalSerialize for ProverKey<'a, C> {
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.powers_of_g.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.powers_of_g.serialized_size(compress)
    }
}

impl<'a, C: CurveGroup> CanonicalDeserialize for ProverKey<'a, C> {
    fn deserialize_with_mode<R: std::io::prelude::Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let powers_of_g_vec = Vec::deserialize_with_mode(reader, compress, validate)?;
        Ok(ProverKey {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g_vec),
        })
    }
}

impl<'a, C: CurveGroup> Valid for ProverKey<'a, C> {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        match self.powers_of_g.clone() {
            Cow::Borrowed(powers) => powers.to_vec().check(),
            Cow::Owned(powers) => powers.check(),
        }
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Proof<C: CurveGroup> {
    pub eval: C::ScalarField,
    pub proof: C,
}

/// KZG implements the CommitmentScheme trait for the KZG commitment scheme.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct KZG<'a, E: Pairing, const H: bool = false> {
    _a: PhantomData<&'a ()>,
    _e: PhantomData<E>,
}

impl<'a, E, const H: bool> KZG<'a, E, H> where E: Pairing{

	/// batch prove a collection of polynomials and provide
	/// the aggregated poly evaluates to a certain challenge point
	/// and yiled a value.
    pub fn batch_prove_with_challenge(
        params: &ProverKey<'a,E::G1>,
        challenge: E::ScalarField,
        v: &Vec<Vec<E::ScalarField>>,
		rand_comb: E::ScalarField
    ) -> Result<Proof<E::G1>, Error> {
		let k = v.len();
		let mut factor = E::ScalarField::one();
		let mut polynomial = poly_from_vec(vec![E::ScalarField::zero()])?;
		for i in 0..k{
			let new_vec = v[i].par_iter().map(|x| *x*factor).
				collect::<Vec<E::ScalarField>>();
			let poly = poly_from_vec(new_vec.to_vec())?;
			polynomial = polynomial + poly;
			factor = factor * rand_comb;
		}
		check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;
        let divisor = DensePolynomial::<E::ScalarField>
			::from_coefficients_vec(vec![
            	-challenge, E::ScalarField::one(),
        ]);
        let (witness_poly, remainder_poly) = DenseOrSparsePolynomial
			::from(&polynomial)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&divisor))
            .unwrap();
        let eval = if remainder_poly.is_zero() {
            E::ScalarField::zero()
        } else {
            remainder_poly[0]
        };
        check_degree_is_too_large(witness_poly.degree(), 
			params.powers_of_g.len())?;
        let (num_leading_zeros, witness_coeffs) =
            skip_first_zero_coeffs_and_convert_to_bigints(&witness_poly);
        let proof = <E::G1 as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &witness_coeffs,
        );

        Ok(Proof { eval, proof })
	}
}

impl<'a, E, const H: bool> CommitmentScheme<E::G1, H> for KZG<'a, E, H>
where
    E: Pairing,
{
    type ProverParams = ProverKey<'a, E::G1>;
    type VerifierParams = VerifierKey<E>;
    type Proof = Proof<E::G1>;
    type ProverChallenge = E::ScalarField;
    type Challenge = E::ScalarField;

    fn is_hiding() -> bool {
        if H {
            return true;
        }
        false
    }

    /// setup returns the tuple (ProverKey, VerifierKey). For real world deployments the setup must
    /// be computed in the most trustless way possible, usually through a MPC ceremony.
    fn setup(
        mut rng: impl RngCore,
        len: usize,
    ) -> Result<(Self::ProverParams, Self::VerifierParams), Error> {
		/* COMMENTED OUT by BORA paper author
		 as kzg10 costing 3x times of RAM than what is needed.
        let len = len.next_power_of_two();
        let universal_params =
            KZG10::<E, DensePolynomial<E::ScalarField>>::setup(len, false, &mut rng)
                .expect("Setup failed");
        let powers_of_g = universal_params.powers_of_g[..=len].to_vec();
        let powers = ProverKey::<E::G1> {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
        };
        let vk = VerifierKey {
            g: universal_params.powers_of_g[0],
            gamma_g: universal_params.powers_of_gamma_g[&0],
            h: universal_params.h,
            beta_h: universal_params.beta_h,
            prepared_h: universal_params.prepared_h.clone(),
            prepared_beta_h: universal_params.prepared_beta_h.clone(),
        };
        Ok((powers, vk))
		*/
		//THE following code is mainly adapted from kzg10 of arkworks/poly-commit/kzg10
		//we simply skipped the construction of neg_powers_of_h and
		//powers_of_gamma_g
		use ark_std::UniformRand;
		use ark_ec::scalar_mul::fixed_base::FixedBase;
		use std::ops::Mul;

        let len = len.next_power_of_two();
		let beta = E::ScalarField::rand(&mut rng);
        let g = E::G1::rand(&mut rng);
		let gamma_g = E::G1::rand(&mut rng);
		let h = E::G2::rand(&mut rng);
		let max_degree = len;

		let mut powers_of_beta = vec![E::ScalarField::one(); max_degree+2];
        let mut cur = beta;
        for i in 0..=max_degree {
            //powers_of_beta.push(cur);
			powers_of_beta[i+1] = cur;
            cur *= &beta;
        }

		let window_size = FixedBase::get_mul_window_size(max_degree + 1);
		let scalar_bits = E::ScalarField::MODULUS_BIT_SIZE as usize;
        let g_table = FixedBase::get_window_table(scalar_bits, 
			window_size, g);
        let powers_of_g = FixedBase::msm::<E::G1>(
			scalar_bits, window_size, &g_table, &powers_of_beta);

		let aff_powers_of_g = <E::G1 as CurveGroup>::normalize_batch(
			&powers_of_g);
		// to save RAM: we use the following
		//THIS IS VERY SLOW THOUGH, par_into_iter()?
		//let aff_powers_of_g = powers_of_g.into_iter().map(|g|
		//	g.into_affine()).collect::<Vec<_>>();
		//use rayon::iter::IntoParallelIterator;
		//let aff_powers_of_g = powers_of_g.into_par_iter().map(|g|
		//	g.into_affine()).collect::<Vec<_>>();
        let powers = ProverKey::<E::G1> {
            powers_of_g: ark_std::borrow::Cow::Owned(aff_powers_of_g),
        };

		let h = h.into_affine();
        let beta_h = h.mul(beta).into_affine();
        let prepared_h = h.into();
        let prepared_beta_h = beta_h.into();

        let vk = VerifierKey {
            g: g.into(),
            gamma_g: gamma_g.into(),
            h: h,
            beta_h: beta_h,
            prepared_h: prepared_h,
            prepared_beta_h: prepared_beta_h,
        };
        Ok((powers, vk))

    }

    /// commit implements the CommitmentScheme commit interface, adapting the implementation from
    /// <https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L178>
    /// with the main difference being the removal of the blinding factors and the no-dependency to
    /// the Pairing trait.
    fn commit(
        params: &Self::ProverParams,
        v: &[E::ScalarField],
        _blind: &E::ScalarField,
    ) -> Result<E::G1, Error> {
        if !_blind.is_zero() || H {
            return Err(Error::NotSupportedYet("hiding".to_string()));
        }

        let polynomial = poly_from_vec(v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        let (num_leading_zeros, plain_coeffs) =
            skip_first_zero_coeffs_and_convert_to_bigints(&polynomial);
        let commitment = <E::G1 as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &plain_coeffs,
        );
        Ok(commitment)
    }

	// added for retrieving the key for qa-nizk
	fn pkey_in_affine(pkey: &Self::ProverParams, size: usize) -> Vec<E::G1Affine>{
		pkey.powers_of_g[0..size].to_vec()
	}


    /// prove implements the CommitmentScheme prove interface, adapting the implementation from
    /// <https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L307>
    /// with the main difference being the removal of the blinding factors and the no-dependency to
    /// the Pairing trait.
    fn prove(
        params: &Self::ProverParams,
        transcript: &mut impl Transcript<E::ScalarField>,
        cm: &E::G1,
        v: &[E::ScalarField],
        _blind: &E::ScalarField,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        transcript.absorb_nonnative(cm);
        let challenge = transcript.get_challenge();
        Self::prove_with_challenge(params, challenge, v, _blind, _rng)
    }

    fn prove_with_challenge(
        params: &Self::ProverParams,
        challenge: Self::ProverChallenge,
        v: &[E::ScalarField],
        _blind: &E::ScalarField,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        if !_blind.is_zero() || H {
            return Err(Error::NotSupportedYet("hiding".to_string()));
        }

        let polynomial = poly_from_vec(v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        // Compute q(x) = (p(x) - p(z)) / (x-z). Observe that this quotient does not change with z
        // because p(z) is the remainder term. We can therefore omit p(z) when computing the
        // quotient.
		// comment out the following divide_with_q_and_r for better performance
		// by BORA paper author
        //let divisor = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![ -challenge, E::ScalarField::one(), ]);
    //    let (witness_poly, remainder_poly) = DenseOrSparsePolynomial::from(&polynomial)
     //       .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&divisor))
            // the panic inside `divide_with_q_and_r` should never be reached, since the divisor
            // polynomial is constructed right before and is set to not be zero. And the `.unwrap`
            // should not give an error.
      //      .unwrap();
	    let (witness_poly, remainder_poly) = deg1_div(&polynomial.coeffs, 
			&challenge).unwrap();

        let eval = if remainder_poly.is_zero() {
            E::ScalarField::zero()
        } else {
            remainder_poly[0]
        };

        check_degree_is_too_large(witness_poly.degree(), params.powers_of_g.len())?;
        let (num_leading_zeros, witness_coeffs) =
            skip_first_zero_coeffs_and_convert_to_bigints(&witness_poly);
        let proof = <E::G1 as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &witness_coeffs,
        );

        Ok(Proof { eval, proof })
    }

    fn verify(
        params: &Self::VerifierParams,
        transcript: &mut impl Transcript<E::ScalarField>,
        cm: &E::G1,
        proof: &Self::Proof,
    ) -> Result<(), Error> {
        transcript.absorb_nonnative(cm);
        let challenge = transcript.get_challenge();
        Self::verify_with_challenge(params, challenge, cm, proof)
    }

    fn verify_with_challenge(
        params: &Self::VerifierParams,
        challenge: Self::Challenge,
        cm: &E::G1,
        proof: &Self::Proof,
    ) -> Result<(), Error> {
        if H {
            return Err(Error::NotSupportedYet("hiding".to_string()));
        }

        // verify the KZG proof using arkworks method
        let v = KZG10::<E, DensePolynomial<E::ScalarField>>::check(
            params, // vk
            &KZG10Commitment(cm.into_affine()),
            challenge,
            proof.eval,
            &KZG10Proof::<E> {
                w: proof.proof.into_affine(),
                random_v: None,
            },
        )?;
        if !v {
            return Err(Error::CommitmentVerificationFail);
        }
        Ok(())
    }
}

fn check_degree_is_too_large(
    degree: usize,
    num_powers: usize,
) -> Result<(), ark_poly_commit::error::Error> {
    let num_coefficients = degree + 1;
    if num_coefficients > num_powers {
        Err(ark_poly_commit::error::Error::TooManyCoefficients {
            num_coefficients,
            num_powers,
        })
    } else {
        Ok(())
    }
}

fn skip_first_zero_coeffs_and_convert_to_bigints<F: PrimeField, P: DenseUVPolynomial<F>>(
    p: &P,
) -> (usize, Vec<F::BigInt>) {
    let mut num_leading_zeros = 0;
    while num_leading_zeros < p.coeffs().len() && p.coeffs()[num_leading_zeros].is_zero() {
        num_leading_zeros += 1;
    }
    let coeffs = convert_to_bigints(&p.coeffs()[num_leading_zeros..]);
    (num_leading_zeros, coeffs)
}

fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    ark_std::cfg_iter!(p)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>()
}

/// perform a division (added by BORA paper author to improve division performance
/// Assumtpion: the poly represented by coef can be perfectly
/// divided by (x-d). We just do school boook division.
fn deg1_div<F:PrimeField>(coefs: &Vec<F>, d: &F)->Result<(DensePolynomial<F>,DensePolynomial<F>),Error>{
	let n = coefs.len();
	let d:F = *d;
	let mut vec_coef = coefs.clone();
	let mut quot = vec![F::zero(); n-1];
	for j in 0..n-1{
		let idx = n -1 - j;
		let q = vec_coef[idx];
		quot[idx-1] = q;
		vec_coef[idx-1] += d * q;
	}
	let quot_poly = DensePolynomial::<F>::from_coefficients_vec(quot);
	let remain_poly = DensePolynomial::<F>::from_coefficients_vec(
		vec![vec_coef[0]]);

	Ok( (quot_poly, remain_poly) )
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_std::{test_rng, UniformRand};
	use std::ops::Mul;

    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_kzg_commitment_scheme() {
        let mut rng = &mut test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let transcript_p = &mut PoseidonSponge::<Fr>::new(&poseidon_config);
        let transcript_v = &mut PoseidonSponge::<Fr>::new(&poseidon_config);

        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, n).unwrap();

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZG::<Bn254>::commit(&pk, &v, &Fr::zero()).unwrap();

        let proof = KZG::<Bn254>::prove(&pk, transcript_p, &cm, &v, &Fr::zero(), None).unwrap();

        // verify the proof:
        KZG::<Bn254>::verify(&vk, transcript_v, &cm, &proof).unwrap();
    }

    #[test]
    fn test_kzg_batch() {
		// create 3 polynomials and batch prove them at a given point.
        let mut rng = &mut test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let _transcript_p = &mut PoseidonSponge::<Fr>::new(&poseidon_config);
        let _transcript_v = &mut PoseidonSponge::<Fr>::new(&poseidon_config);

        let n = 10;
		let k = 3;
		let ch = Fr::rand(&mut rng);
		let rc = Fr::rand(&mut rng);
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, n).unwrap();
		let mut v2d = vec![];
		let mut cm2d = vec![];
		let mut cm_all = G1::zero();
		let mut factor = Fr::one();
		let mut eval_all = Fr::zero();
		let zero = Fr::zero();
		for _i in 0..k{
        	let v: Vec<Fr>=std::iter::repeat_with(||Fr::rand(rng)).take(n)
				.collect();
        	let cm = KZG::<Bn254>::commit(&pk, &v, &Fr::zero()).unwrap();
			cm_all = cm_all + cm.mul(factor);
			let prf = KZG::<Bn254>::prove_with_challenge(&pk, ch, &v, &zero, 
				None);
			eval_all = eval_all + prf.unwrap().eval * factor;

			v2d.push(v);
			cm2d.push(cm);


			factor = factor * rc;
		}

		//1. batch proof
        let proof=KZG::<Bn254>::batch_prove_with_challenge(&pk, ch,  &v2d, rc)
			.expect("prf generation error");
        let b_res = KZG::<Bn254>::verify_with_challenge(&vk, ch, &cm_all, &proof);
		assert!(b_res.is_ok(), "batch verify failure");

		//2. verify the eval
		assert!(proof.eval == eval_all, "eval_all not match");
    }
}
