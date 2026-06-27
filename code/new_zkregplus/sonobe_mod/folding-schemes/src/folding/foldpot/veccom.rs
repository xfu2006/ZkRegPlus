/* Created 08/26/2024
   Modified 12/03/2024
*/
/// Adaptaion of KZG commitment in ../../commitment. (Note that in this
/// mod the ../../commit/kzg.rs is changed to drop interpolation).
/// This one is essentially the original Sonobe KZG commitment with 
/// interpolation.
/// This vector commitment commits to a vector v, which is first
/// interpolated to a polynomial p, which at `omega^i` evaluates to
/// `v_i`. Note: when test `v_i`, the integer i is changed to
/// `omega^i` instead.

use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM, 
	scalar_mul::{fixed_base::FixedBase}};
use std::ops::Mul;
use ark_ff::{PrimeField};
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, Polynomial,EvaluationDomain, Evaluations,
	GeneralEvaluationDomain
};
use ark_poly_commit::kzg10::{
    Commitment as KZG10Commitment, Proof as KZG10Proof, VerifierKey, KZG10,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::{rand::RngCore,UniformRand};
use ark_std::{borrow::Cow, fmt::Debug};
use ark_std::{One, Zero};
use core::marker::PhantomData;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rayon::prelude::*; 

use super::CommitmentScheme;
use crate::transcript::Transcript;
use crate::utils::vec::poly_from_vec;
use crate::Error;

pub fn interpret_poly_from_vec<F: PrimeField>(v: &Vec<F>) -> Result<DensePolynomial<F>, Error> {
    let D = GeneralEvaluationDomain::<F>::new(v.len()).ok_or(Error::NewDomainFail)?;
	let poly = Evaluations::from_vec_and_domain(v.to_vec(), D).interpolate();
	Ok(poly)
}

pub fn compute_powers_and_mul_by_const_serial<F: PrimeField>( size: usize, root: F, c: F) -> Vec<F> {
    let mut value = c;
    (0..size)
        .map(|_| {
            let old_value = value;
            value *= root;
            old_value
        })
        .collect()
}

pub fn compute_powers_serial<F: PrimeField>(size: usize, root: F) -> Vec<F> {
    compute_powers_and_mul_by_const_serial(size, root, F::one())
}

const MIN_PARALLEL_CHUNK_SIZE: usize = 1 << 7;
pub fn compute_powers<F: PrimeField>(size: usize, g: F) -> Vec<F> {
	assert!(size.is_power_of_two(), "size: {} is not power of 2", size);
    if size < MIN_PARALLEL_CHUNK_SIZE {
        return compute_powers_serial(size, g);
    }
    // compute the number of threads we will be using.
    use ark_std::cmp::{max, min};
    let num_cpus_available = rayon::current_num_threads();
    let num_elem_per_thread = max(size / num_cpus_available, MIN_PARALLEL_CHUNK_SIZE);
    // ceil-divide so the final partial chunk (size not divisible by
    // num_elem_per_thread, e.g. non-power-of-2 core counts) is included;
    // the per-chunk min() already truncates it to the exact remainder.
    let num_cpus_used = (size + num_elem_per_thread - 1) / num_elem_per_thread;

    // Split up the powers to compute across each thread evenly.
    let res: Vec<F> = (0..num_cpus_used)
        .into_par_iter()
        .flat_map(|i| {
            let offset = g.pow(&[(i * num_elem_per_thread) as u64]);
            // Compute the size that this chunks' output should be
            // (num_elem_per_thread, unless there are less than num_elem_per_thread elements remaining)
            let num_elements_to_compute = min(size - i * num_elem_per_thread, num_elem_per_thread);
           let res = compute_powers_and_mul_by_const_serial(num_elements_to_compute, g, offset);
            res
        })
        .collect();
    res
}

/// compute z_n(omega^i) for each i in [0, n)
pub fn compute_derive_vanish<F:PrimeField>(n: usize) ->Vec<F>{
	let omega = F::get_root_of_unity(n as u64).unwrap();
	let arr_omega = compute_powers::<F>(n, omega);
	let fe_n = F::from(n as u64);
	let z_n_prime = arr_omega.into_par_iter().map(|x|
		fe_n*x.inverse().unwrap()).collect::<Vec<F>>();

	z_n_prime
}

/// compute all L_i(s) for each i. 
pub fn precompute_lags<F:PrimeField>(
	n: usize, 
	s: F)->Vec<F>{
	assert!(n.is_power_of_two(), "n is not pow of 2");
	//1. compute Z_n(s)
	let one = F::one();
	let z_n_s = s.pow(&[n as u64]) - one;
	let omega = F::get_root_of_unity(n as u64).unwrap();
	let arr_omega = compute_powers::<F>(n, omega);

	//2. compute Z_n'(omega_i)
	// n*(omega^i)^{n-1} = n/omega^i
	let z_n_prime = compute_derive_vanish::<F>(n);

	//3. L_i(s) = Z_n(s)/((s-omega^i) Z_n'(omega^i))
	let arr_l_i = z_n_prime.into_par_iter().zip(arr_omega.into_par_iter()).
		map(|(x, y)|
		z_n_s*((s-y) * x).inverse().unwrap()).collect::<Vec<F>>();

	arr_l_i	
}

/// Added to implement the Defalut triat
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WrapperEvalDomain<F:PrimeField>{
	pub domain: GeneralEvaluationDomain<F>,
}

impl <F:PrimeField> Default for WrapperEvalDomain<F>{
	fn default() -> Self{
    	let D = GeneralEvaluationDomain::<F>::new(1024)
			.expect("Gen domain err");
		Self{ domain: D }
	}
}

impl <F:PrimeField> WrapperEvalDomain<F>{
	fn new(n: usize) -> Self{
		assert!(n.is_power_of_two());
    	let D = GeneralEvaluationDomain::<F>::new(n).expect("Gen domain err");
		Self{ domain: D }
	}
}

/// ProverKey defines a similar struct as in ark_poly_commit::kzg10::Powers, but instead of
/// depending on the Pairing trait it depends on the CurveGroup trait.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ProverKey<'a, C: CurveGroup> {
    /// Group elements of the form `Lambda_i(beta) G`, 
	/// for different values of `i`.
    pub lagkeys: Cow<'a, [C::Affine]>,
	/// the evaluation domain for convenience
	pub domain: WrapperEvalDomain<C::ScalarField>,
	/// real powers of g. for i: [beta^i]_1
    pub powers_of_g: Cow<'a, [C::Affine]>,
}

impl <'a, C:CurveGroup> ProverKey<'a,C>{
	/// return omega^i where omega is the root of unity
	pub fn get_idx(&self, i: usize)->C::ScalarField{
		assert!(i<self.lagkeys.len());
		self.domain.domain.element(i)
	}
}

impl<'a, C: CurveGroup> CanonicalSerialize for ProverKey<'a, C> {
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.lagkeys.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.lagkeys.serialized_size(compress)
    }
}

impl<'a, C: CurveGroup> CanonicalDeserialize for ProverKey<'a, C> {
    fn deserialize_with_mode<R: std::io::prelude::Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let lagkeys_vec = Vec::deserialize_with_mode(reader, compress, validate)?;
		let n_len = lagkeys_vec.len();
        Ok(ProverKey {
			//REMOVE the clone() later
            lagkeys: ark_std::borrow::Cow::Owned(lagkeys_vec.clone()),
			domain: WrapperEvalDomain::new(n_len),
            powers_of_g: ark_std::borrow::Cow::Owned(lagkeys_vec),
        })
    }
}

impl<'a, C: CurveGroup> Valid for ProverKey<'a, C> {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        match self.lagkeys.clone() {
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
pub struct VecCom<'a, E: Pairing, const H: bool = false> {
    _a: PhantomData<&'a ()>,
    _e: PhantomData<E>,
}

impl<'a, E, const H: bool> CommitmentScheme<E::G1, H> for VecCom<'a, E, H>
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
        let len = len.next_power_of_two();
		//the following is adapted from KZG10 (from arkworks)
		//difference is that we performed evaluation domain interpretation
		//on the power series


		//1. compute lagkeys as L_i(beta) where beta
		// is the trapdoor secret. 
		assert!(len>=1);
        let g = E::G1::rand(&mut rng);
        let beta = E::ScalarField::rand(&mut rng);
        let mut powers_of_beta = vec![E::ScalarField::one()];
        let mut cur = beta;
        for _ in 0..=len{
            powers_of_beta.push(cur);
            cur *= &beta;
        }
		let old_powers_of_beta = powers_of_beta.clone();
    	let D = GeneralEvaluationDomain::<E::ScalarField>::new(len)
			.ok_or(Error::NewDomainFail)?;
		let powers_of_beta = precompute_lags(len, beta);

		let window_size = FixedBase::get_mul_window_size(len + 1);
		let scalar_bits = E::ScalarField::MODULUS_BIT_SIZE as usize;
        let g_table = FixedBase::get_window_table(
			scalar_bits, window_size, g);
        let lagkeys = FixedBase::msm::<E::G1>(scalar_bits, 
			window_size, &g_table, &powers_of_beta);
		let lagkeys = E::G1::normalize_batch(&lagkeys);
        let powers_of_g = FixedBase::msm::<E::G1>(scalar_bits, 
			window_size, &g_table, &old_powers_of_beta);
		let powers_of_g = E::G1::normalize_batch(&powers_of_g);

		//2. compute other attriubtes such as scaled h
		let h = E::G2::rand(&mut rng);
		let h = h.into_affine();
		let beta_h = h.mul(beta).into_affine();
		let prepared_h = h.into();
		let prepared_beta_h = beta_h.into();
		let gamma_g = E::G1::rand(&mut rng).into_affine();

        let powers = ProverKey::<E::G1> {
            lagkeys: ark_std::borrow::Cow::Owned(lagkeys),
			domain: WrapperEvalDomain{domain:D} ,
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
        };

		let g = g.into_affine();
        let vk = VerifierKey {
            g: g,
            gamma_g: gamma_g,
            h: h,
            beta_h: beta_h,
            prepared_h: prepared_h,
            prepared_beta_h: prepared_beta_h
        };
        Ok((powers, vk))
    }

	/// essentially the kzg10 commitment.
	/// it computes p(X) = sum_i^n v_i lamda_i(X)
	/// for X = beta
    fn commit(
        params: &Self::ProverParams,
        v: &[E::ScalarField],
        _blind: &E::ScalarField,
    ) -> Result<E::G1, Error> {
        if !_blind.is_zero() || H {
            return Err(Error::NotSupportedYet("hiding".to_string()));
        }

        let polynomial = poly_from_vec(v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.lagkeys.len())?;

        let (num_leading_zeros, plain_coeffs) =
            skip_first_zero_coeffs_and_convert_to_bigints(&polynomial);
        let commitment = <E::G1 as VariableBaseMSM>::msm_bigint(
            &params.lagkeys[num_leading_zeros..],
            &plain_coeffs,
        );


        Ok(commitment)
    }

	/// added for retrieving the key for qa-nizk
	fn pkey_in_affine(pkey: &Self::ProverParams, size: usize) 
	-> Vec<E::G1Affine>{
        pkey.lagkeys[0..size].to_vec()
	}

	/// proves that the interpolated poly evaluates to the
	/// corresponding value at the challenge
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

	/// the poly is p(X) = \sum_i^n v_i lamda(X)
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

        let polynomial = interpret_poly_from_vec(&v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.lagkeys.len())?;

        // Compute q(x) = (p(x) - p(z)) / (x-z). 
		// Observe that this quotient does not change with z
        // because p(z) is the remainder term. 
		// We can therefore omit p(z) when computing the
        // quotient.
        let divisor = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![ -challenge, E::ScalarField::one(), ]);
        let (witness_poly, remainder_poly) = DenseOrSparsePolynomial
			::from(&polynomial)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&divisor))
            .unwrap();

        let eval = if remainder_poly.is_zero() {
            E::ScalarField::zero()
        } else {
            remainder_poly[0]
        };
        check_degree_is_too_large(witness_poly.degree(), params.lagkeys.len())?;
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

#[cfg(test)]
mod tests_veccom {
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_std::{test_rng, UniformRand};

    use super::*;
	#[test]
	fn test_interpolate(){
        let mut rng = &mut test_rng();
		let n = 5;
        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let (pk, _vk): (ProverKey<G1>, VerifierKey<Bn254>) =
            VecCom::<Bn254>::setup(&mut rng, n).unwrap();
		let poly = interpret_poly_from_vec(&v).unwrap(); 
		for i in 0..n{
			let idx = pk.get_idx(i); //omega^i
			let res = poly.evaluate(&idx);
			assert!(res == v[i]);
		}
	}

    #[test]
    fn test_veccom_commitment_scheme() {
        let mut rng = &mut test_rng();

        let n = 16;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) =
            VecCom::<Bn254>::setup(&mut rng, n).unwrap();

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = VecCom::<Bn254>::commit(&pk, &v, &Fr::zero()).unwrap();
		for i in 0..n{
			let idx = pk.get_idx(i);
			let proof = VecCom::<Bn254>::prove_with_challenge(&pk, idx, &v, &Fr::zero(), None).unwrap();
			VecCom::<Bn254>::verify_with_challenge(&vk, idx, &cm, &proof).unwrap();
		}

    }
}
