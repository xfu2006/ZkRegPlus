use rayon::prelude::*;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_r1cs_std::{boolean::Boolean, groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::Zero;
use ark_std::{rand::RngCore, UniformRand};
use ark_std::rand::SeedableRng;
use ark_ec::AffineRepr;
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use core::marker::PhantomData;

use super::CommitmentScheme;
use crate::transcript::Transcript;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C: CurveGroup> {
    pub R: C,
    pub u: Vec<C::ScalarField>,
    pub r_u: C::ScalarField, // blind
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Params<C: CurveGroup> {
    pub h: C,
    pub generators: Vec<C::Affine>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: CurveGroup, const H: bool = false> {
    _c: PhantomData<C>,
}

/// T939: domain tag of the public-seed (NUMS) Pedersen keys. Changing
/// it changes every key (and the K4 pp_hash constant).
const PED_DOMAIN: &[u8] = b"BORA-Pedersen-NUMS-v1";
const PED_CHUNK: usize = 1 << 14;

/// SHA-256 over length-prefixed parts (injective encoding).
fn derive_seed(parts: &[&[u8]]) -> [u8; 32] {
	let mut h = Sha256::new();
	for p in parts { h.update((p.len() as u64).to_le_bytes()); h.update(p); }
	h.finalize().into()
}

impl<C: CurveGroup, const H: bool> Pedersen<C, H> {
	/// Independent generators (try-and-increment on x). No discrete-log
	/// relation among them is known to anyone.
	fn params_from_seed(seed: [u8; 32], len: usize) -> Params<C> {
		let n = len.next_power_of_two();
		let mut generators = vec![C::Affine::zero(); n];
		generators.par_chunks_mut(PED_CHUNK).enumerate().for_each(|(i, out)| {
			let mut r = ChaCha20Rng::from_seed(
				derive_seed(&[&seed, &(i as u64).to_le_bytes()]));
			for g in out.iter_mut() { *g = C::Affine::rand(&mut r); }
		});
		assert!(generators.par_iter().all(|g| !g.is_zero()),
			"Pedersen key holds the identity");
		let mut rh = ChaCha20Rng::from_seed(derive_seed(&[&seed, b"h"]));
		Params::<C> { h: C::rand(&mut rh), generators }
	}
}

/// Implements the CommitmentScheme trait for Pedersen commitments
impl<C: CurveGroup, const H: bool> CommitmentScheme<C, H> for Pedersen<C, H> {
    type ProverParams = Params<C>;
    type VerifierParams = Params<C>;
    type Proof = Proof<C>;
    type ProverChallenge = (C::ScalarField, Vec<C::ScalarField>, C, C::ScalarField);
    type Challenge = C::ScalarField;

    fn is_hiding() -> bool {
        if H {
            return true;
        }
        false
    }

    fn trim_pp(pp: &Self::ProverParams, len: usize)
    -> Self::ProverParams {
        let n = len.min(pp.generators.len());
        Params::<C>{
            h: pp.h,
            generators: pp.generators[0..n].to_vec(),
        }
    }

    fn setup(
        mut rng: impl RngCore,
        len: usize,
    ) -> Result<(Self::ProverParams, Self::VerifierParams), Error> {
		//T939: the old b_fast branch (every generator a known multiple
		//i*2^k of one point) is removed. Seed drawn from the caller rng.
		let mut seed = [0u8; 32];
		rng.fill_bytes(&mut seed);
		let p = Self::params_from_seed(seed, len);
        Ok((p.clone(), p))
    }

	//T939: public-seed (NUMS) keys, identical on every run.
    fn setup_tagged(
        _rng: impl RngCore,
        len: usize,
        tag: &[u8],
    ) -> Result<(Self::ProverParams, Self::VerifierParams), Error> {
		let p = Self::params_from_seed(derive_seed(&[PED_DOMAIN, tag]), len);
        Ok((p.clone(), p))
    }

    fn commit(
        params: &Self::ProverParams,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
    ) -> Result<C, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }

        // h⋅r + <g, v>
        // use msm_unchecked because we already ensured at the if that lengths match
        if !H {
            return Ok(C::msm_unchecked(&params.generators[..v.len()], v));
        }
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..v.len()], v))
    }

	// added for retrieving the key for qa-nizk
	fn pkey_in_affine(pkey: &Self::ProverParams, size: usize) -> Vec<C::Affine>{
        pkey.generators[0..size].to_vec()
	}

    fn prove(
        params: &Self::ProverParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        transcript.absorb_nonnative(cm);
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenges(v.len());

        // R = h⋅r_1 + <g, d>
        // use msm_unchecked because we already ensured at the if that lengths match
        let mut R: C = C::msm_unchecked(&params.generators[..d.len()], &d);
        if H {
            R += params.h.mul(r1);
        }

        transcript.absorb_nonnative(&R);
        let e = transcript.get_challenge();

        let challenge = (r1, d, R, e);
        Self::prove_with_challenge(params, challenge, v, r, _rng)
    }

    fn prove_with_challenge(
        params: &Self::ProverParams,
        challenge: Self::ProverChallenge,
        v: &[C::ScalarField], // vector
        r: &C::ScalarField,   // blinding factor
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }
        let (r1, d, R, e): (C::ScalarField, Vec<C::ScalarField>, C, C::ScalarField) = challenge;

        // u = d + v⋅e
        let u = vec_add(&vec_scalar_mul(v, &e), &d)?;
        // r_u = e⋅r + r_1
        let mut r_u = C::ScalarField::zero();
        if H {
            r_u = e * r + r1;
        }

        Ok(Self::Proof { R, u, r_u })
    }

    fn verify(
        params: &Self::VerifierParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        proof: &Proof<C>,
    ) -> Result<(), Error> {
        transcript.absorb_nonnative(cm);
        transcript.get_challenge(); // r_1
        transcript.get_challenges(proof.u.len()); // d
        transcript.absorb_nonnative(&proof.R);
        let e = transcript.get_challenge();
        Self::verify_with_challenge(params, e, cm, proof)
    }

    fn verify_with_challenge(
        params: &Self::VerifierParams,
        challenge: Self::Challenge,
        cm: &C,
        proof: &Proof<C>,
    ) -> Result<(), Error> {
        if params.generators.len() < proof.u.len() {
            return Err(Error::PedersenParamsLen(
                params.generators.len(),
                proof.u.len(),
            ));
        }
        if !H && (!proof.r_u.is_zero()) {
            return Err(Error::BlindingNotZero);
        }

        let e = challenge;

        // check that: R + cm⋅e == h⋅r_u + <g, u>
        let lhs = proof.R + cm.mul(e);
        // use msm_unchecked because we already ensured at the if that lengths match
        let mut rhs = C::msm_unchecked(&params.generators[..proof.u.len()], &proof.u);
        if H {
            rhs += params.h.mul(proof.r_u);
        }
        if lhs != rhs {
            return Err(Error::CommitmentVerificationFail);
        }
        Ok(())
    }
}

pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

pub struct PedersenGadget<C, GC, const H: bool = false>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
{
    _cf: PhantomData<CF<C>>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

use ark_r1cs_std::ToBitsGadget;
impl<C, GC, const H: bool> PedersenGadget<C, GC, H>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,

    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn commit(
        h: GC,
        g: Vec<GC>,
        v: Vec<Vec<Boolean<CF<C>>>>,
        r: Vec<Boolean<CF<C>>>,
    ) -> Result<GC, SynthesisError> {
        let mut res = GC::zero();
        if H {
            res += h.scalar_mul_le(r.iter())?;
        }
        for (i, v_i) in v.iter().enumerate() {
            res += g[i].scalar_mul_le(v_i.to_bits_le()?.iter())?;
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;

    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;

    /// trim_pp(key, |v|) commits identically to the full key, its
    /// generators length is exactly the requested prefix, and an
    /// under-trimmed key fails LOUD (PedersenParamsLen).
    #[test]
    fn test_pedersen_trim_pp() {
        let mut rng = ark_std::test_rng();
        let (pp, _vp) =
            Pedersen::<Projective>::setup(&mut rng, 1000).unwrap();
        let v: Vec<Fr> = (0..100).map(|_| Fr::rand(&mut rng))
            .collect();
        let zero = Fr::from(0u64);
        let full = Pedersen::<Projective>::commit(&pp, &v, &zero)
            .unwrap();
        let trimmed = Pedersen::<Projective>::trim_pp(&pp, 100);
        assert_eq!(trimmed.generators.len(), 100);
        let cut = Pedersen::<Projective>::commit(&trimmed, &v, &zero)
            .unwrap();
        assert_eq!(full, cut, "trimmed key changed the commitment");
        let short = Pedersen::<Projective>::trim_pp(&pp, 50);
        let res = Pedersen::<Projective>::commit(&short, &v, &zero);
        assert!(matches!(res, Err(Error::PedersenParamsLen(50, 100))),
            "under-trim must fail loud");
    }

    #[test]
    fn test_pedersen() {
        test_pedersen_opt::<false>();
        test_pedersen_opt::<true>();
    }
    fn test_pedersen_opt<const hiding: bool>() {
        let mut rng = ark_std::test_rng();

        let n: usize = 10;
        // setup params
        let (params, _) = Pedersen::<Projective>::setup(&mut rng, n).unwrap();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        // blinding factor
        let r: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = Pedersen::<Projective, hiding>::commit(&params, &v, &r).unwrap();
        let proof =
            Pedersen::<Projective, hiding>::prove(&params, &mut transcript_p, &cm, &v, &r, None)
                .unwrap();
        Pedersen::<Projective, hiding>::verify(&params, &mut transcript_v, &cm, &proof).unwrap();
    }

    #[test]
    fn test_pedersen_circuit() {
        test_pedersen_circuit_opt::<false>();
        test_pedersen_circuit_opt::<true>();
    }
    fn test_pedersen_circuit_opt<const hiding: bool>() {
        let mut rng = ark_std::test_rng();

        let n: usize = 8;
        // setup params
        let (params, _) = Pedersen::<Projective, hiding>::setup(&mut rng, n).unwrap();

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        // blinding factor
        let r: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = Pedersen::<Projective, hiding>::commit(&params, &v, &r).unwrap();

        let v_bits: Vec<Vec<bool>> = v.iter().map(|val| val.into_bigint().to_bits_le()).collect();
        let r_bits: Vec<bool> = r.into_bigint().to_bits_le();

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        // prepare inputs
        let vVar: Vec<Vec<Boolean<Fq>>> = v_bits
            .iter()
            .map(|val_bits| {
                Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(val_bits.clone())).unwrap()
            })
            .collect();
        let rVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();
        let gVar = Vec::<GVar>::new_witness(cs.clone(), || Ok(params.generators)).unwrap();
        let hVar = GVar::new_witness(cs.clone(), || Ok(params.h)).unwrap();
        let expected_cmVar = GVar::new_witness(cs.clone(), || Ok(cm)).unwrap();

        // use the gadget
        let cmVar =
            PedersenGadget::<Projective, GVar, hiding>::commit(hVar, gVar, vVar, rVar).unwrap();
        cmVar.enforce_equal(&expected_cmVar).unwrap();
    }

    /// T939 T-1 predicate: no identity, pairwise distinct, and no
    /// doubling chain g[k+1] = 2 g[k] (the old b_fast layout).
    fn check_key_independent<C: CurveGroup>(g: &[C::Affine]) {
        use std::collections::HashSet;
        assert!(g.iter().all(|x| !x.is_zero()), "identity generator");
        let set: HashSet<C::Affine> = g.iter().cloned().collect();
        assert_eq!(set.len(), g.len(), "repeated generator");
        for k in 0..g.len() - 1 {
            assert_ne!(g[k + 1], (g[k] + g[k]).into_affine(),
                "doubling chain at {}", k);
        }
    }

    /// T939 T-1: keys from `setup` are independent on both curves.
    #[test]
    fn test_t939_key_independent() {
        let mut rng = ark_std::test_rng();
        let (pp, _) = Pedersen::<ark_bn254::G1Projective>::setup(
            &mut rng, 3000).unwrap();
        assert_eq!(pp.generators.len(), 4096);
        check_key_independent::<ark_bn254::G1Projective>(&pp.generators);
        let (pp, _) = Pedersen::<ark_grumpkin::Projective>::setup(
            &mut rng, 100).unwrap();
        check_key_independent::<ark_grumpkin::Projective>(&pp.generators);
    }

    /// T939 T-2: the b_fast collisions are gone: e_0 commits to a
    /// non-identity point and v, v + 2e_k - e_{k+1} commit differently.
    #[test]
    fn test_t939_no_collision() {
        type G = ark_bn254::G1Projective;
        type F = ark_bn254::Fr;
        let mut rng = ark_std::test_rng();
        let (pp, _) = Pedersen::<G>::setup(&mut rng, 512).unwrap();
        let zero = F::from(0u64);
        let mut e0 = vec![zero; 512];
        e0[0] = F::from(1u64);
        let cm = Pedersen::<G>::commit(&pp, &e0, &zero).unwrap();
        assert!(!cm.is_zero(), "segment-0 generator is the identity");
        let v: Vec<F> = (0..512).map(|_| F::rand(&mut rng)).collect();
        let mut w = v.clone();
        w[200] += F::from(2u64);
        w[201] -= F::from(1u64);
        assert_ne!(Pedersen::<G>::commit(&pp, &v, &zero).unwrap(),
            Pedersen::<G>::commit(&pp, &w, &zero).unwrap(),
            "v and v + 2e_k - e_(k+1) collide");
    }
    fn hex<T: CanonicalSerialize>(x: &T) -> String {
        let mut b = Vec::new();
        x.serialize_compressed(&mut b).unwrap();
        b.iter().map(|y| format!("{:02x}", y)).collect()
    }

    /// T939 known-answer test. K4 bakes pp_hash (which hashes these keys)
    /// into the decider, so any change of the NUMS derivation (domain,
    /// chunking, rand_chacha stream, ark sampling) must fail here first.
    /// Probes cover chunk 0, the chunk boundary and h on both curves.
    #[test]
    fn test_t939_nums_kat() {
        const IDX: [usize; 5] = [0, 1, (1 << 14) - 1, 1 << 14, (1 << 14) + 1];
        let len = (1 << 14) + 2;
        let (a, _) = Pedersen::<ark_bn254::G1Projective>::setup_tagged(
            ark_std::test_rng(), len, b"s1/c0/cs1").unwrap();
        let bn = [
            "ca7b5a2e8f63ba58a4bb77dcf9b7a182ee0f63f0123a3d707749521e1534efaf",
            "b74494d1d00af526ffff397357819645bd686eb8d9ab066453ed223210bdf917",
            "47ff904a8110096cde8a529c09819c22718a7e742b6cbb682dac9fa7af38b4a3",
            "8fcb1204607f81138b288fa11cc71d8293e87ecad041044a1b3041c34981a78d",
            "8d08d620fc999dc313df12c4bf8c1eff59d8f76c699623cfbb073592dddf898a",
        ];
        for (k, want) in IDX.iter().zip(bn.iter()) {
            assert_eq!(hex(&a.generators[*k]), *want, "bn254 g[{}]", k);
        }
        assert_eq!(hex(&a.h.into_affine()),
            "a1c455c2f73c89b35c683bfd96ab8046200698fab1d207c62c0b598e6dba5bac");
        let (b, _) = Pedersen::<ark_grumpkin::Projective>::setup_tagged(
            ark_std::test_rng(), len, b"s1/cf").unwrap();
        let gk = [
            "d523277069b2bd25aceca6a82e2929ef4ef4c01216025b059b0cd9aca19d092c",
            "5b202a87923bea53f4c39958a402676ef09c048e2af1fa026e04174077a7fb0b",
            "7d7571a4ebd36c5e9367a66f4a456a0f53dbba759c9927ccb9e84250263a7297",
            "7b856d7e6f97fb7cfc29f0291137895856477471f01d80cbb6b96dc0ed055096",
            "194adaa78ac816979f0aa9a836ab6b6e913c11356da3e550153daff7abc40b04",
        ];
        for (k, want) in IDX.iter().zip(gk.iter()) {
            assert_eq!(hex(&b.generators[*k]), *want, "grumpkin g[{}]", k);
        }
        assert_eq!(hex(&b.h.into_affine()),
            "86f34bc85f894d78a9a066139532a2e078f935efbf6590473ea4c9339a0ea98a");
    }

    /// T939 T-3 (key level): setup_tagged ignores the rng, is stable
    /// under length change (prefix), separates tags, and its keys pass
    /// the T-1 predicate.
    #[test]
    fn test_t939_tagged_keys() {
        type G = ark_bn254::G1Projective;
        let mut r1 = ark_std::test_rng();
        let mut r2 = rand::rngs::OsRng;
        let (a, _) = Pedersen::<G>::setup_tagged(&mut r1, 40000, b"s1/cf").unwrap();
        let (b, _) = Pedersen::<G>::setup_tagged(&mut r2, 40000, b"s1/cf").unwrap();
        assert_eq!(a, b, "tagged key depends on the rng");
        let (c, _) = Pedersen::<G>::setup_tagged(&mut r1, 100, b"s1/cf").unwrap();
        assert_eq!(c.generators[..], a.generators[..128], "not prefix-stable");
        assert_eq!(c.h, a.h);
        let (d, _) = Pedersen::<G>::setup_tagged(&mut r1, 40000, b"s2/cf").unwrap();
        assert!(a.generators.iter().zip(d.generators.iter()).all(|(x, y)| x != y),
            "s1/cf and s2/cf share a generator");
        let (e, _) = Pedersen::<G>::setup_tagged(&mut r1, 40000, b"s1/cp").unwrap();
        assert_ne!(a.generators[0], e.generators[0], "cf and cp keys equal");
        check_key_independent::<G>(&a.generators);
    }
}
