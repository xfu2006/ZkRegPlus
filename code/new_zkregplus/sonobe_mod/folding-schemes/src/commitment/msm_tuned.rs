// Tuned MSM kernels — copies of arkworks `msm_bigint` and
// `msm_bigint_wnaf` from ark-ec 0.4.1 (Apache-2.0/MIT, arkworks-rs)
// with the window size `c` exposed as an explicit parameter so callers
// can override the default heuristic.
//
// Why this exists: `arkworks::VariableBaseMSM::msm_bigint` picks
// `c = ⌊log2(M) * 0.69⌋ + 2`, which for M ≈ 1.89 M gives c=16 → 16
// windows over `bases` per MSM. When several MSMs run concurrently the
// DRAM bus saturates near 41 GB/s, so reducing the number of bases
// passes is a direct DRAM-traffic win. WNAF additionally cuts ~half
// the curve adds via signed digits, which helps the compute side.

use ark_ec::{ScalarMul, VariableBaseMSM};
use ark_ff::prelude::*;
use ark_ff::PrimeField;
use ark_std::{cfg_into_iter, vec, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Mirrors arkworks `msm_bigint` with explicit window size `c`.
pub fn msm_bigint_with_c<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    bigints: &[<V::ScalarField as PrimeField>::BigInt],
    c: usize,
) -> V {
    let size = ark_std::cmp::min(bases.len(), bigints.len());
    let scalars = &bigints[..size];
    let bases = &bases[..size];
    let scalars_and_bases_iter =
        scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
    let one = V::ScalarField::one().into_bigint();
    let zero = V::zero();
    let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

    let window_sums: Vec<_> = cfg_into_iter!(window_starts)
        .map(|w_start| {
            let mut res = zero;
            let mut buckets = vec![zero; (1 << c) - 1];
            scalars_and_bases_iter
                .clone()
                .for_each(|(&scalar, base)| {
                    if scalar == one {
                        if w_start == 0 {
                            res += base;
                        }
                    } else {
                        let mut scalar = scalar;
                        scalar.divn(w_start as u32);
                        let scalar = scalar.as_ref()[0] % (1 << c);
                        if scalar != 0 {
                            buckets[(scalar - 1) as usize] += base;
                        }
                    }
                });

            let mut running_sum = V::zero();
            buckets.into_iter().rev().for_each(|b| {
                running_sum += &b;
                res += &running_sum;
            });
            res
        })
        .collect();

    let lowest = *window_sums.first().unwrap();
    lowest
        + &window_sums[1..]
            .iter()
            .rev()
            .fold(zero, |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

/// Mirrors arkworks private `msm_bigint_wnaf` with explicit window
/// size. WNAF uses signed digits so ~half the digits are zero, cutting
/// the per-window add count.
pub fn msm_bigint_wnaf_with_c<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    bigints: &[<V::ScalarField as PrimeField>::BigInt],
    c: usize,
) -> V {
    let size = ark_std::cmp::min(bases.len(), bigints.len());
    let scalars = &bigints[..size];
    let bases = &bases[..size];

    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
    let digits_count = (num_bits + c - 1) / c;
    let scalar_digits = scalars
        .iter()
        .flat_map(|s| make_digits(s, c, num_bits))
        .collect::<Vec<_>>();
    let zero = V::zero();
    let window_sums: Vec<_> = cfg_into_iter!(0..digits_count)
        .map(|i| {
            let mut buckets = vec![zero; 1 << c];
            for (digits, base) in
                scalar_digits.chunks(digits_count).zip(bases)
            {
                use ark_std::cmp::Ordering;
                let scalar = digits[i];
                match 0.cmp(&scalar) {
                    Ordering::Less => {
                        buckets[(scalar - 1) as usize] += base
                    }
                    Ordering::Greater => {
                        buckets[(-scalar - 1) as usize] -= base
                    }
                    Ordering::Equal => (),
                }
            }
            let mut running_sum = V::zero();
            let mut res = V::zero();
            buckets.into_iter().rev().for_each(|b| {
                running_sum += &b;
                res += &running_sum;
            });
            res
        })
        .collect();

    let lowest = *window_sums.first().unwrap();
    lowest
        + &window_sums[1..]
            .iter()
            .rev()
            .fold(zero, |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

fn make_digits(
    a: &impl BigInteger,
    w: usize,
    num_bits: usize,
) -> Vec<i64> {
    let scalar = a.as_ref();
    let radix: u64 = 1 << w;
    let window_mask: u64 = radix - 1;
    let mut carry = 0u64;
    let num_bits = if num_bits == 0 {
        a.num_bits() as usize
    } else {
        num_bits
    };
    let digits_count = (num_bits + w - 1) / w;
    let mut digits = vec![0i64; digits_count];
    for (i, digit) in digits.iter_mut().enumerate() {
        let bit_offset = i * w;
        let u64_idx = bit_offset / 64;
        let bit_idx = bit_offset % 64;
        let bit_buf =
            if bit_idx < 64 - w || u64_idx == scalar.len() - 1 {
                scalar[u64_idx] >> bit_idx
            } else {
                (scalar[u64_idx] >> bit_idx)
                    | (scalar[1 + u64_idx] << (64 - bit_idx))
            };
        let coef = carry + (bit_buf & window_mask);
        carry = (coef + radix / 2) >> w;
        *digit = (coef as i64) - (carry << w) as i64;
    }
    digits[digits_count - 1] += (carry << w) as i64;
    digits
}

/// Public entry point: pick the implementation + `c`. Currently uses
/// the WNAF variant with c bumped one window above the arkworks
/// default. For M = 1.89 M this gives c = 17 (vs default 16) → 15
/// passes over `bases` instead of 16, plus ~half the per-window adds
/// from signed digits.
pub fn msm_bigint_tuned<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    bigints: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = ark_std::cmp::min(bases.len(), bigints.len());
    let c = if size < 32 {
        3
    } else {
        // Match arkworks' formula: `log2(size) * 69 / 100 + 2`, then
        // bump by +1 to get one fewer window pass over `bases`. For
        // M = 1.89 M this is c = 17, M = 16 M → c = 19.
        ln_without_floats(size) + 2 + 1
    };
    msm_bigint_wnaf_with_c::<V>(bases, bigints, c)
}

fn ln_without_floats(a: usize) -> usize {
    (ark_std::log2(a) * 69 / 100) as usize
}

// Small wrapper used by callers that have `&[ScalarField]` rather
// than `&[BigInt]` already.
pub fn msm_tuned<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[V::ScalarField],
) -> V {
    let bigints =
        cfg_into_iter!(scalars).map(|s| s.into_bigint()).collect::<Vec<_>>();
    msm_bigint_tuned::<V>(bases, &bigints)
}

// Re-export for convenience.
pub use msm_bigint_tuned as msm_bigint;

// Silence "unused" if parallel feature not on.
#[allow(unused_imports)]
use ark_ec::CurveGroup;

// ScalarMul brings `double_in_place`. Pull in just to make trait
// resolution explicit.
const _: fn() = || {
    fn _check<V: ScalarMul>() {}
};
