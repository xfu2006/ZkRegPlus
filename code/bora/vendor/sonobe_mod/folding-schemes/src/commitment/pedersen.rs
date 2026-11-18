use rayon::prelude::*;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_r1cs_std::{boolean::Boolean, groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use ark_ff::PrimeField; //ALL_T1011
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::{fp::FpVar, FieldVar}, R1CSVar, ToConstraintFieldGadget};
use ark_relations::{lc, r1cs::{ConstraintSystemRef, LinearCombination, Variable}};
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

//ALL_T1011 P2(b): FixedBasePedersenGadget checks a Pedersen commitment
//sum_i v_i G_i whose bases G_i are CONSTANTS (the public Pedersen key). It
//gives the same point as PedersenGadget::commit with H = false (no blinding)
//at about 545 constraints per 256-bit scalar instead of 1,574.
//
//Idea. Read each scalar v two bits at a time (a digit d in 0..3) and add one
//precomputed constant point per digit, chosen by a 2-bit table lookup. A
//constant table costs 1 constraint per lookup (the product b0 b1) and one
//cheap affine addition costs 3, so 4 constraints per 2 bits. The old gadget
//spends 5 constraints per single bit.
//
//The cheap addition A + T is wrong when A = T or A = -T, and cannot add the
//point at infinity. To rule both out for ANY bits, window w adds
//(d + 2) 4^w G instead of d 4^w G. Then every added point is nonzero, and the
//running sum s G is always smaller than the next term t G as an integer:
//s <= (5/3) 4^w < 2 4^w <= t, and s + t < q. So A = +-T never happens. The
//extra 2 4^w G per window is a known constant c G, subtracted once at the end.
//
//Concrete example, v = 45 = 0b10_11_01, 3 windows, digits d = 1, 3, 2
//(45 = 1 + 3*4 + 2*16):
//  window 0: table {2,3,4,5} G,     d = 1 -> acc = 3G
//  window 1: table {8,12,16,20} G,  d = 3 -> acc = 3G + 20G = 23G  (3 < 20)
//  window 2: table {32,48,64,80} G, d = 2 -> acc = 23G + 64G = 87G (23 < 64)
//  offset c = 2 (1 + 4 + 16) = 42, and 87G - 42G = 45G.
//
//Ranges for the real 256-bit scalars:
//  bits 0..251:   126 windows in the cheap chain (the bound s + t < q holds
//                 up to window 125 for a 254-bit group order q)
//  bits 252, 253: choose one of the constants {0, 1, 2, 3} 2^252 G and add it
//                 with the complete (always correct) addition
//  bits 254, 255: forced to 0, since inputs are canonical (v < q < 2^254)
pub struct FixedBasePedersenGadget<C, GC>(PhantomData<(C, GC)>);

const FB_LOW: usize = 252; // bits in the incomplete chain
const FB_WIN: usize = FB_LOW / 2; // 2-bit windows
const FB_TOP: usize = FB_LOW + 2; // = order bits, asserted in commit_pair

impl<C, GC> FixedBasePedersenGadget<C, GC>
where
    C: CurveGroup,
    C::BaseField: PrimeField,
    GC: CurveVar<C, C::BaseField> + ToConstraintFieldGadget<C::BaseField>,
{
    /// Returns (sum_i v1_i G_i, sum_i v2_i G_i) for the bits of two vectors
    /// that share the generators G_i (cmE and cmW of one CycleFold witness).
    /// For each G_i it builds the constant table once and runs scalar_mul for
    /// v1_i and v2_i. Every scalar adds its point to r1 or r2 and returns its
    /// constant offset c G_i. The offsets are summed natively (o1, o2) and
    /// subtracted once at the end, which costs one addition per vector.
    /// Panics if there are fewer generators than values (no value may go
    /// unchecked) or if the group order does not have 254 bits.
    pub fn commit_pair(
        cs: ConstraintSystemRef<C::BaseField>,
        g: &[C::Affine],
        v1: &[Vec<Boolean<C::BaseField>>],
        v2: &[Vec<Boolean<C::BaseField>>],
    ) -> Result<(GC, GC), SynthesisError> {
        assert!(g.len() >= v1.len() && g.len() >= v2.len(), "fewer generators than values");
        assert_eq!(<C::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize, FB_TOP, "group order bits");
        let (mut r1, mut r2) = (GC::zero(), GC::zero());
        let (mut o1, mut o2) = (C::zero(), C::zero());
        for (i, gi) in g.iter().enumerate().take(v1.len().max(v2.len())) {
            let tab = FixedBaseTable::<C, GC>::new(gi.into_group());
            if let Some(bits) = v1.get(i) { o1 += Self::scalar_mul(cs.clone(), &tab, bits, &mut r1)?; }
            if let Some(bits) = v2.get(i) { o2 += Self::scalar_mul(cs.clone(), &tab, bits, &mut r2)?; }
        }
        Ok((r1 - o1, r2 - o2))
    }

    /// Adds (v + c) G to res for one scalar v given by its little-endian bits,
    /// and returns the constant c G. Steps:
    /// 1. Force bits 254 and up to 0 (2 constraints).
    /// 2. Cheap chain over bits 0..251: acc = T_0[d_0], then
    ///    acc = acc + T_w[d_w] for w = 1..125 (4 constraints per window).
    ///    acc ends as (L + c) G, L = bits 0..251 of v, c = sum 2 4^w.
    /// 3. Turn acc (raw x, y) into a GC point p: allocate p as a witness and
    ///    require its encoding [x, y, infinity] to equal [acc.x, acc.y, 0]
    ///    (15 constraints), then res += p (complete addition, 12).
    /// 4. Bits 252, 253: select d 2^252 G among 4 constants (3 constraints)
    ///    and res += it (complete addition, 12, correct also for d = 0).
    fn scalar_mul(
        cs: ConstraintSystemRef<C::BaseField>,
        tab: &FixedBaseTable<C, GC>,
        bits: &[Boolean<C::BaseField>],
        res: &mut GC,
    ) -> Result<C, SynthesisError> {
        for b in bits.iter().skip(FB_TOP) {
            b.enforce_equal(&Boolean::FALSE)?;
        }
        let nw = (bits.len().min(FB_LOW) + 1) / 2;
        if nw == 0 {
            return Ok(C::zero());
        }
        let bit = |i: usize| if i < FB_LOW { bits.get(i).cloned().unwrap_or(Boolean::FALSE) } else { Boolean::FALSE };
        let digits = (0..nw).map(|w| (bit(2 * w), bit(2 * w + 1))).collect::<Vec<_>>();
        let mut acc = fixed_base_lookup::<C>(&tab.low[0], &digits[0].0, &digits[0].1)?;
        for w in 1..nw {
            let t = fixed_base_lookup::<C>(&tab.low[w], &digits[w].0, &digits[w].1)?;
            acc = add_incomplete(&cs, &acc, &t)?;
        }
        // bind acc to a GC point through its encoding [x, y, inf] = [x, y, 0]
        let p = GC::new_witness(cs.clone(), || {
            let mut s = C::zero();
            for (w, (b0, b1)) in digits.iter().enumerate() {
                s += tab.low[w][b0.value()? as usize + 2 * b1.value()? as usize];
            }
            Ok(s)
        })?;
        let enc = p.to_constraint_field()?;
        assert_eq!(enc.len(), 3, "short Weierstrass encoding [x, y, inf] expected");
        cs.enforce_constraint(fp_lc(&enc[0]) - &acc.0, lc!() + Variable::One, lc!())?;
        cs.enforce_constraint(fp_lc(&enc[1]) - &acc.1, lc!() + Variable::One, lc!())?;
        enc[2].enforce_equal(&FpVar::zero())?;
        *res += p;
        if bits.len() > FB_LOW {
            let q = &tab.high;
            let lo = bit_at(bits, FB_LOW).select(&q[1], &q[0])?; // constants: free
            let hi = bit_at(bits, FB_LOW).select(&q[3], &q[2])?;
            *res += bit_at(bits, FB_LOW + 1).select(&hi, &lo)?;
        }
        Ok(tab.offs[nw - 1])
    }
}

fn bit_at<F: PrimeField>(bits: &[Boolean<F>], i: usize) -> Boolean<F> {
    bits.get(i).cloned().unwrap_or(Boolean::FALSE)
}

/// Native constant tables of one base G, computed outside the circuit.
/// low[w][d] = (d + 2) 4^w G for the 126 windows, in affine form (the lookup
/// needs x and y). offs[w] = sum_{i <= w} 2 4^i G is the offset after w + 1
/// windows. high[d] = d 2^252 G for bits 252, 253, as circuit constants.
/// new() walks p = 4^w G with two doublings per window and converts all 504
/// points to affine with one batch inversion, so it does no per-point
/// inversion and no subgroup check.
struct FixedBaseTable<C: CurveGroup, GC> {
    low: Vec<[C::Affine; 4]>, // low[w][d] = (d + 2) 4^w G
    offs: Vec<C>,             // offs[w] = sum_{i <= w} 2 4^i G
    high: [GC; 4],            // d 2^252 G as circuit constants
}

impl<C: CurveGroup, GC: CurveVar<C, C::BaseField>> FixedBaseTable<C, GC>
where
    C::BaseField: PrimeField,
{
    fn new(base: C) -> Self {
        let mut pts = Vec::with_capacity(4 * FB_WIN);
        let mut offs = Vec::with_capacity(FB_WIN);
        let (mut p, mut off) = (base, C::zero()); // p = 4^w G
        for _ in 0..FB_WIN {
            let two = p.double();
            let four = two.double();
            pts.extend([two, two + p, four, four + p]);
            off += two;
            offs.push(off);
            p = four;
        }
        let aff = C::normalize_batch(&pts); // one inversion per base
        let low = aff.chunks(4).map(|c| [c[0], c[1], c[2], c[3]]).collect();
        let h = p; // 4^126 G = 2^252 G
        let high = [C::zero(), h, h.double(), h.double() + h].map(GC::constant);
        Self { low, offs, high }
    }
}

/// A point (x, y) whose coordinates are linear combinations of circuit
/// variables, plus their values (None in setup mode). Using linear
/// combinations directly, instead of FpVar arithmetic, creates no symbolic
/// variables, which keeps the prover memory small.
type LcPoint<F> = (LinearCombination<F>, LinearCombination<F>, Option<(F, F)>);

/// The linear combination of an FpVar (a constant or one variable).
fn fp_lc<F: PrimeField>(v: &FpVar<F>) -> LinearCombination<F> {
    match v {
        FpVar::Constant(c) => lc!() + (*c, Variable::One),
        FpVar::Var(a) => lc!() + a.variable,
    }
}

/// Table lookup of the point t[d], d = b0 + 2 b1, for 4 constant points.
/// Each coordinate is the unique polynomial in the bits that hits the 4
/// table values:
///   x = x0 + (x1 - x0) b0 + (x2 - x0) b1 + (x3 - x2 - x1 + x0) b0 b1
/// (same for y). Example: b0 = 1, b1 = 1 gives x0 + x1 - x0 + x2 - x0
/// + x3 - x2 - x1 + x0 = x3. Only b0 b1 needs a constraint (1 total,
/// shared by x and y). The rest is a linear combination with constant
/// coefficients.
fn fixed_base_lookup<C: CurveGroup>(
    t: &[C::Affine; 4],
    b0: &Boolean<C::BaseField>,
    b1: &Boolean<C::BaseField>,
) -> Result<LcPoint<C::BaseField>, SynthesisError>
where
    C::BaseField: PrimeField,
{
    let p = b0.and(b1)?;
    let c = |k: usize| {
        let (x, y) = t[k].xy().expect("nonzero table point");
        [*x, *y]
    };
    let (t0, t1, t2, t3) = (c(0), c(1), c(2), c(3));
    let coord = |j: usize| {
        b0.lc() * (t1[j] - t0[j]) + &(b1.lc() * (t2[j] - t0[j]))
            + &(p.lc() * (t3[j] - t2[j] - t1[j] + t0[j])) + (t0[j], Variable::One)
    };
    let val = b0.value().and_then(|a| Ok(c(a as usize + 2 * b1.value()? as usize))).ok();
    Ok((coord(0), coord(1), val.map(|v| (v[0], v[1]))))
}

/// Cheap affine addition c = a + b, valid only when a != +-b and neither
/// is the point at infinity (the window offsets guarantee this). With the
/// slope lam = (y2 - y1) / (x2 - x1) it enforces 3 constraints:
///   lam (x2 - x1) = y2 - y1
///   lam lam       = x1 + x2 + x3       (x3 = lam^2 - x1 - x2)
///   lam (x1 - x3) = y1 + y3            (y3 = lam (x1 - x3) - y1)
/// Each constraint fixes one new variable uniquely because x2 - x1 != 0.
/// x3 and y3 are new variables, so the chain of 125 additions keeps every
/// linear combination short.
fn add_incomplete<F: PrimeField>(
    cs: &ConstraintSystemRef<F>,
    a: &LcPoint<F>,
    b: &LcPoint<F>,
) -> Result<LcPoint<F>, SynthesisError> {
    let (x1, y1, va) = a;
    let (x2, y2, vb) = b;
    let v = match (va, vb) {
        (Some((x1, y1)), Some((x2, y2))) => {
            let lam = (*y2 - y1) * (*x2 - x1).inverse().ok_or(SynthesisError::Unsatisfiable)?;
            let x3 = lam.square() - x1 - x2;
            Some((lam, x3, lam * (*x1 - x3) - y1))
        }
        _ => None,
    };
    let get = |k: usize| move || v.map(|t| [t.0, t.1, t.2][k]).ok_or(SynthesisError::AssignmentMissing);
    let lam = cs.new_witness_variable(get(0))?;
    let x3 = cs.new_witness_variable(get(1))?;
    let y3 = cs.new_witness_variable(get(2))?;
    cs.enforce_constraint(lc!() + lam, x2.clone() - x1, y2.clone() - y1)?;
    cs.enforce_constraint(lc!() + lam, lc!() + lam, x1.clone() + x2 + x3)?;
    cs.enforce_constraint(lc!() + lam, x1.clone() - x3, y1.clone() + y3)?;
    Ok((lc!() + x3, lc!() + y3, v.map(|t| (t.1, t.2))))
}

#[cfg(test)]
mod tests {

    //ALL_T1011: FixedBasePedersenGadget equals the native MSM (edge and random
    //scalars, unequal lengths), setup and prove give the same constraint
    //count, and a set bit 254 (non-canonical input) is rejected.
    #[test]
    fn test_fixed_base_pedersen() {
        use super::FixedBasePedersenGadget;
        use crate::folding::circuits::nonnative::uint::NonNativeUintVar;
        use ark_bn254::{Fq, Fr};
        use ark_ec::{CurveGroup, VariableBaseMSM};
        use ark_ff::Field;
        use ark_grumpkin::{constraints::GVar, Affine, Projective};
        use ark_r1cs_std::{alloc::{AllocVar, AllocationMode}, boolean::Boolean, R1CSVar};
        use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef, SynthesisMode};
        use ark_std::{One, UniformRand, Zero};

        let mut rng = ark_std::test_rng();
        let p252 = Fq::from(2u64).pow([252u64]);
        let mut v1 = vec![Fq::zero(), Fq::one(), -Fq::one(), p252 - Fq::one(), p252, p252 * Fq::from(3u64)];
        v1.extend((0..10).map(|_| Fq::rand(&mut rng)));
        let v2 = v1[..3].to_vec();
        let g: Vec<Affine> = (0..v1.len()).map(|_| Projective::rand(&mut rng).into_affine()).collect();
        let build = |mode: Option<SynthesisMode>, bit254: bool| {
            let cs: ConstraintSystemRef<Fr> = ConstraintSystem::new_ref();
            if let Some(m) = mode { cs.set_mode(m); }
            let bits = |v: &[Fq]| v.iter().map(|x| NonNativeUintVar::<Fr>::new_variable_with_bits(
                cs.clone(), || Ok(*x), AllocationMode::Witness).unwrap().1).collect::<Vec<_>>();
            let (mut b1, b2) = (bits(&v1), bits(&v2));
            if bit254 { b1[1][254] = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap(); }
            let (r1, r2) = FixedBasePedersenGadget::<Projective, GVar>::commit_pair(cs.clone(), &g, &b1, &b2).unwrap();
            let vals = r1.value().ok().zip(r2.value().ok());
            (cs, vals)
        };
        let (cs, vals) = build(None, false);
        assert!(cs.is_satisfied().unwrap());
        let (r1, r2) = vals.unwrap();
        assert_eq!(r1, Projective::msm(&g, &v1).unwrap());
        assert_eq!(r2, Projective::msm(&g[..3], &v2).unwrap());
        let (cs_setup, _) = build(Some(SynthesisMode::Setup), false);
        assert_eq!(cs_setup.num_constraints(), cs.num_constraints());
        let (cs_bad, _) = build(None, true);
        assert!(!cs_bad.is_satisfied().unwrap());
    }
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

    /// T939 T-7 (R7): wall time of the production key path
    /// (setup_tagged, BN254 G1) at 2^k for each k in PED_BENCH_LOGS
    /// (comma list, default "25,26" = one Stage-1 job).
    #[test]
    #[ignore]
    fn test_t939_setup_timing() {
        type G = ark_bn254::G1Projective;
        let logs = std::env::var("PED_BENCH_LOGS").unwrap_or("25,26".into());
        let mut total = 0f64;
        for k in logs.split(',').map(|s| s.trim().parse::<u32>().unwrap()) {
            let t = std::time::Instant::now();
            let (p, _) = Pedersen::<G>::setup_tagged(
                ark_std::test_rng(), 1usize << k, b"t7").unwrap();
            let s = t.elapsed().as_secs_f64();
            total += s;
            println!("T939 T-7: setup 2^{} = {} pts, {:.2} s, threads {}",
                k, p.generators.len(), s, rayon::current_num_threads());
        }
        println!("T939 T-7: total {:.2} s", total);
    }
}
