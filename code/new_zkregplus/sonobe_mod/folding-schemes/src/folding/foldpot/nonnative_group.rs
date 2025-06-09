/* Created 01/14/2025
  Non-native group operations based on nonnative field arkswork
  Here we hance the existing NonNativeAffineVar in the circuits::nonnative
	fn test_value(){
  module. We provide add(), double(), scalar_mul() functions.
  NOTE: it is expensive - scalar_mul costs 2 million R1CS constraints.
  But since it's used in decider (only 3 times), we leave it for future work.
*/

use std::{cmp::{max,min}};
use std::ops::{Mul};
use ark_std::{Zero,One};
use ark_ff::{BigInteger,fields::{PrimeField},Field};
use ark_relations::{r1cs::{ConstraintSystemRef, SynthesisError}};
use crate::folding::circuits::nonnative::{
	affine::NonNativeAffineVar,
	uint::{NonNativeUintVar,BoundedBigUint,LimbVar},
};
use ark_ec::{
	 CurveGroup,AffineRepr, 
	short_weierstrass::{SWCurveConfig},
};
use num_bigint::{BigUint};
use ark_r1cs_std::{
	R1CSVar,
	prelude::{AllocationMode},
	alloc::AllocVar,
	boolean::Boolean,
	fields::{fp::FpVar,FieldVar},
	eq::EqGadget
};
use crate::{
	folding::{
		foldpot::{ utils::{f1_limbs_to_f2, biguint_to_f, bits_le_to_biguint} },
		circuits::{CF1,CF2,CF3},
	},
	Error,
};

impl <F:PrimeField> EqGadget<F> for NonNativeUintVar<F>
{
	fn enforce_equal(&self, other: &Self)->Result<(), SynthesisError>{
		let bres = self.is_eq(other)?;
		#[cfg(test)]{ if bres.value().is_ok(){assert!(bres.value().unwrap());} }
		Ok( bres.enforce_equal(&Boolean::<F>::TRUE)? )
	}

	/// Adapted from enforce_eq_unaligned of circuits/nonnative/uint.rs
	/// enforce_equal_unaligned.
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let len = min(self.0.len(), other.0.len());

        // Group the limbs of `self` and `other` so that each group nearly
        // reaches the capacity `F::MODULUS_MINUS_ONE_DIV_TWO`.
        // By saying group, we mean the operation `Σ x_i 2^{i * W}`, where `W`
        // is the initial number of bits in a limb, just as what we do in grade
        // school arithmetic, e.g.,
        //         5   9
        // x       7   3
        // -------------
        //        15  27
        //    35  63
        // -------------  <- When grouping 35, 15 + 63, and 27, we are computing
        // 4   3   0   7     35 * 100 + (15 + 63) * 10 + 27 = 4307
        // Note that this is different from the concatenation `x_0 || x_1 ...`,
        // since the bit-length of each limb is not necessarily the initial size
        // `W`.
        let (steps, x, y, rest) = {
            // `steps` stores the size of each grouped limb.
            let mut steps = vec![];
            // `x_grouped` stores the grouped limbs of `self`.
            let mut x_grouped = vec![];
            // `y_grouped` stores the grouped limbs of `other`.
            let mut y_grouped = vec![];
            let mut i = 0;
            while i < len {
                let mut j = i;
                // The current grouped limbs of `self` and `other`.
                let mut xx = LimbVar::zero();
                let mut yy = LimbVar::zero();
                while j < len {
                    let shift = BigUint::one() << (Self::bits_per_limb() * (j - i));
                    assert!(shift < F::MODULUS_MINUS_ONE_DIV_TWO.into());
                    let shift = LimbVar::constant(shift.into());
                    match (
                        // Try to group `x` and `y` into `xx` and `yy`.
                        self.0[j].mul(&shift).and_then(|x| xx.add(&x)),
                        other.0[j].mul(&shift).and_then(|y| yy.add(&y)),
                    ) {
                        // Update the result if successful.
                        (Some(x), Some(y)) => (xx, yy) = (x, y),
                        // Break the loop if the upper bound of the result exceeds
                        // the maximum capacity.
                        _ => break,
                    }
                    j += 1;
                }
                // Store the grouped limbs and their size.
                steps.push((j - i) * Self::bits_per_limb());
                x_grouped.push(xx);
                y_grouped.push(yy);
                // Start the next group
                i = j;
            }
            let remaining_limbs = &(if i < self.0.len() { self } else { other }).0[i..];


            let rest = if remaining_limbs.is_empty() {
                FpVar::zero()
            } else {
                // If there is any remaining limb, the first one should be the
                // final carry (which will be checked later), and the following
                // ones should be zero.

                // Enforce the remaining limbs to be zero.
                // Instead of doing that one by one, we check if their sum is
                // zero using a single constraint.
                // This is sound, as the upper bounds of the limbs and their sum
                // are guaranteed to be less than `F::MODULUS_MINUS_ONE_DIV_TWO`
                // (i.e., all of them are "non-negative"), implying that all
                // limbs should be zero to make the sum zero.
                let sum_remain = LimbVar::add_many(&remaining_limbs[1..])
                    .unwrap()
                    .v;
				sum_remain.enforce_equal(&FpVar::zero())?;
				#[cfg(test)]{if sum_remain.value().is_ok(){
						assert!(sum_remain.value()?.is_zero());
				} }
                remaining_limbs[0].v.clone()
            };
            (steps, x_grouped, y_grouped, rest)
        };

        let n = steps.len();
        // `c` stores the current carry of `x_i - y_i`
        let mut c = FpVar::<F>::zero();
        // For each group, check the last `step_i` bits of `x_i` and `y_i` are
        // equal.
        // The intuition is to check `diff = x_i - y_i = 0 (mod 2^step_i)`.
        // However, this is only true for `i = 0`, and we need to consider carry
        // values `diff >> step_i` for `i > 0`.
        // Therefore, we actually check `diff = x_i - y_i + c = 0 (mod 2^step_i)`
        // and derive the next `c` by computing `diff >> step_i`.
        // To enforce `diff = 0 (mod 2^step_i)`, we compute `diff / 2^step_i`
        // and enforce it to be small (soundness holds because for `a` that does
        // not divide `b`, `b / a` in the field will be very large.
		let mut res = Boolean::<F>::TRUE;
        for i in 0..n {
            let step = steps[i];
            c = (&x[i].v - &y[i].v + &c)
                .mul_by_inverse_unchecked(&FpVar::constant(F::from(BigUint::one() << step)))?;
            if i != n - 1 {
                // Unlike the code mentioned above which add some offset to the
                // diff `x_i - y_i + c` to make it always positive, we directly
                // check if the absolute value of the diff is small.
                let part_res = Self::is_abs_bit_length(
                    &c,
                    (max(&x[i].ub, &y[i].ub).bits() as usize)
                        .checked_sub(step)
                        .unwrap_or_default(),
                )?;
				res = res.and(&part_res)?;
            } else {
                // For the final carry, we need to ensure that it equals the
                // remaining limb `rest`.
                let part_res = c.is_eq(&rest)?;
				res = res.and(&part_res)?;
           }
        }

        Ok(res)
    }

}

impl <F:PrimeField> NonNativeUintVar<F>{
	/// return its value in target F
	/// assuming the converted value is less than F2's modulus.
	/// NOTE that we do not make the check
	pub fn value_target_f<F2:PrimeField>(&self)->Result<F2, Error>{
		let val = if self.0[0].value().is_ok(){
			let limb_vals = self.0.iter().map(|x| 
				x.value().unwrap()).collect::<Vec<F>>();
			let val: F2 = f1_limbs_to_f2(&limb_vals);
			val
		}else{ F2::zero()};
		Ok( val )
	}

	/// assert that self is congruent to other regarding F2's MODULUS 
	#[allow(dead_code)]
	fn assert_congruent<F2: PrimeField>(&self, other: &Self){
		//only test when value exists
		//the if ensures it does not crash in g16 setup 
		//which has no assignment
		if self.0.value().is_ok(){
			let v1 = self.value_target_f::<F2>().unwrap();
			let v2 = other.value_target_f::<F2>().unwrap();
			assert!(v1==v2, "assert congruent failed");
		}
	}
    /// Return Boolean if they two are congruent
	/// Adapt from enforce_congruent from uint in circuits/nonnative/uint.rs
    pub fn is_congruent<M: PrimeField>(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let cs = self.0.cs().clone();
		assert!(!cs.is_none());
        let mode = AllocationMode::Witness;
        let m: BigUint = M::MODULUS.into();
        let bits = (max(self.ubound(), other.ubound()) / &m).bits() as usize;
        // Provide the quotient `|x - y| / m` and a boolean indicating if `x > y`

        // as hints.
        let (q, is_ge) = {
            let x = self.value().unwrap_or_default();
            let y = other.value().unwrap_or_default();
            let (d, b) = if x > y {
                ((x - y) / &m, true)
            } else {
                ((y - x) / &m, false)
            };
            (
                Self::new_variable(cs.clone(), || Ok(BoundedBigUint(d, bits)), mode)?,
                Boolean::new_variable(cs.clone(), || Ok(b), mode)?,
            )
        };

        let zero = Self::new_constant(cs.clone(), BoundedBigUint(BigUint::zero(), bits))?;
        let m = Self::new_constant(cs.clone(), BoundedBigUint(m, M::MODULUS_BIT_SIZE as usize))?;
        let l = self.add_no_align(&is_ge.select(&zero, &q)?.mul_no_align(&m)?);
        let r = other.add_no_align(&is_ge.select(&q, &zero)?.mul_no_align(&m)?);


        // If `self >= other`, enforce `self = other + q * m`
        // Otherwise, enforce `self + q * m = other`
        // Soundness holds because if `self` and `other` are not congruent, then
        // one can never find a `q` satisfying either equation above.
		let res =  l.is_eq(&r)?;

		Ok( res )
    }

	/// Adapted from the enforce_abs_bit_length of 
	/// circuits/nonnative/uint.rs:: enforce_abs-bit_length.
	/// Tell if x's absolute value's bit length does not exceed the given length
    pub fn is_abs_bit_length(
        x: &FpVar<F>,
        length: usize,
    ) -> Result<Boolean<F>, SynthesisError> {
        let cs = x.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };

        let is_neg = Boolean::new_variable(
            cs.clone(),
            || Ok(x.value().unwrap_or_default().into_bigint() > F::MODULUS_MINUS_ONE_DIV_TWO),
            mode,
        )?;
        let bits = Vec::new_variable(
            cs.clone(),
            || {
                Ok({
                    let x = x.value().unwrap_or_default();
                    let mut bits = if is_neg.value().unwrap_or_default() {
                        -x
                    } else {
                        x
                    }
                    .into_bigint()
                    .to_bits_le();
                    bits.resize(length, false);
                    bits
                })
            },
            mode,
        )?;

        // Below is equivalent to but more efficient than
        // `Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&is_neg.select(&x.negate()?, &x)?)?`
        // Note that this enforces:
        // 1. The claimed absolute value `is_neg.select(&x.negate()?, &x)?` has
        //    exactly `length` bits.
        // 2. `is_neg` is indeed the sign of `x`, i.e., `is_neg = false` when
        //    `0 <= x < (|F| - 1) / 2`, and `is_neg = true` when
        //    `(|F| - 1) / 2 <= x < F`, thus the claimed absolute value is
        //    correct.
        //    If `is_neg` is incorrect, then:
        //        a. `0 <= x < (|F| - 1) / 2`, but `is_neg = true`, then
        //           `is_neg.select(&x.negate()?, &x)?` returns `|F| - x`,
        //           which is greater than `(|F| - 1) / 2` and cannot fit in
        //           `length` bits (given that `length` is small).
        //        b. `(|F| - 1) / 2 <= x < F`, but `is_neg = false`, then
        //           `is_neg.select(&x.negate()?, &x)?` returns `x`, which is
        //           greater than `(|F| - 1) / 2` and cannot fit in `length`
        //           bits.
		let fp_double = FpVar::from(is_neg).mul(&x.double()?);
		let res = fp_double.is_eq(&(x - Boolean::le_bits_to_fp_var(&bits)?))?;

        Ok(res)
    }

	/// Note: it's expensive. It calls congruent.
	pub fn sub_target_f<F2:PrimeField>(&self, other: &Self)->Result<Self,Error>{
		//1. decide which value to produce
		let (my_val, o_val) = (self.value().unwrap_or_default(), 
			other.value().unwrap_or_default());
		let mod_val_bits= F2::MODULUS.to_bits_le();
		let mod_val = bits_le_to_biguint(&mod_val_bits);
		let res_val = if my_val < o_val{ my_val + mod_val - o_val}
			else {my_val - o_val}; //guaranteed in range

		//2. enforce the result is right
		let cs = self.0.cs();
		let res_f = biguint_to_f::<F2>(&res_val); 
		let res = Self::new_witness(cs.clone(), ||  Ok(res_f))?;

		let sum1 = res.add_no_align(&other);
		sum1.enforce_congruent::<F2>(&self)?;
		#[cfg(test)]{sum1.assert_congruent::<F2>(&&self);}

		Ok(res)
	}

	/// ensure two are "exactly" the same 
	pub fn enforce_eq_limb_by_limb(&self, other: &Self)->Result<(), Error>{
		assert!(self.0.len()==other.0.len());
		for i in 0..self.0.len(){
			self.0[i].v.enforce_equal(&other.0[i].v)?;
			#[cfg(test)]{
				assert!(self.0[i].v.value().unwrap_or_default()==other.0[i].value().unwrap_or_default());
			}
		}
		Ok(())
	}

	/// Return true if the very first limb is one
	/// It only checks the VERY WELL fromed representation (not all one's
	/// possible representation)
	pub fn is_standard_zero(&self) -> Result<Boolean<F>, Error>{
		let mut res = Boolean::<F>::TRUE;
		for i in 0..self.0.len(){ res = res.and(&self.0[i].v.is_zero()?)?; }
		Ok(res)
	}
}

#[allow(dead_code)]
/// Given non_zero point (x,y) return its double
fn non_zero_double<C: CurveGroup>(x: CF2<C>, y: CF2<C>) ->Result<(CF2<C>, CF2<C>), Error> 
where CF2<C>: PrimeField,
	C::Config: SWCurveConfig,
{
	assert!(!x.is_zero() && !y.is_zero());
	let x1_sqr = x * x;
	let num = x1_sqr + x1_sqr + x1_sqr + C::Config::COEFF_A;
	let denom = y + y;
	let lambda = num / denom;
	let x3 = lambda * lambda - x - x;
	let y3 = lambda * (x - x3) - y;
	Ok( (x3, y3) )
}


impl <C: CurveGroup> EqGadget<C::ScalarField> for NonNativeAffineVar<C>{
	fn enforce_equal(&self, other: &Self)->Result<(), SynthesisError>{
		let bres = self.is_eq(other)?;
		#[cfg(test)]{ assert!(bres.value().unwrap_or_default()); }
		Ok( bres.enforce_equal(&Boolean::<>::TRUE)? )
	}

	fn is_eq(&self, other: &Self)->Result<Boolean<C::ScalarField>, 
		SynthesisError>{
		let res = self.x.is_eq(&other.x)?.and(&self.y.is_eq(&other.y)?)?;
		Ok( res )
	}
}

//Note: for simplicity, we assume NonNativeAffineVar are NON-ZERO
//And we do not handle zero vars for add and double.
//When zero vars are involved, we throw "unhandled error".
impl<C: CurveGroup> NonNativeAffineVar<C>
where CF2<C>: PrimeField,
	C::Config: SWCurveConfig
{

	/// return the zero_var
	pub fn zero_var(cs: ConstraintSystemRef<C::ScalarField>)->Self{
		let zero = C::zero();
		NonNativeAffineVar::<C>::new_witness(cs.clone(), 
			|| Ok(zero)).unwrap()
	}

	/// Returns true if x and y are both "standard" one.
	/// It does not handle all forms of zero, but the "standard" form.
	pub fn is_standard_zero(&self)->Result<Boolean<CF1<C>>,Error>{
		Ok( self.x.is_standard_zero()?.and(&self.y.is_standard_zero()?)? )
	}

	/// Return its value (x,y) as Fq.
	pub fn affine_value(&self)->Result<(CF2<C>, CF2<C>), Error>
	{
		let x = self.x.value_target_f::<CF2<C>>()?;
		let y = self.y.value_target_f::<CF2<C>>()?;
		Ok( (x,y) )
	}

	/// generate [zero, g1, g1+1]
	pub fn dummy_vars(&self)->Vec<NonNativeUintVar<C::ScalarField>>{
		let cs = self.x.0.cs();
		let x0 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(CF2::<C>::zero())).unwrap();
		let y0 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(CF2::<C>::zero())).unwrap();
	
		let g1 = C::generator().into_affine();
		let xy = g1.xy().unwrap();
		let x1 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(xy.0.clone())).unwrap();
		let y1 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(xy.1.clone())).unwrap();

		let g2 = (g1 + g1).into_affine();
		let xy = g2.xy().unwrap();
		let x2 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(xy.0.clone())).unwrap();
		let y2 = NonNativeUintVar::<C::ScalarField>::new_witness(cs.clone(),
			|| Ok(xy.1.clone())).unwrap();

		vec![x0, y0, x1, y1, x2, y2]
	}

	/// This is essentially add_no_check (see non_zero_affine.rs
	/// in r1cs-std/src/groups/curves/short_weierstrass.
	/// Performs: (self + other)
	/// If self is zero, return other
	/// if other is zero, return self
	/// If both zero, return zero
	/// CANNOT HANDLE self==other case (should call DOUBLE)!
	/// dummy_vars is for saving memory.
	pub fn add(&self, other: &Self)
		-> Result<Self, Error>{
		//1. get the values in Fq first
		let cs = self.x.cs().clone();
		let (x1, y1) = self.affine_value()?;
		let (x2, y2) = other.affine_value()?;
		let b_self_zero_var = self.is_standard_zero()?;
		let b_other_zero_var = other.is_standard_zero()?;
		let b_same = x1==x2 && y1==y2;
		// if self==other and not the 0+0 case, fail!
		assert!( !b_same || (x1.is_zero() && y1.is_zero()), "CAN'T handle x+x case, need to call double()!"); 

		let b_same_var = self.is_eq(&other)?;
		let (fq_zero, _fq_one) =(C::BaseField::zero(), C::BaseField::one());
		let numerator = y2 - y1;
		let denominator = if b_same {fq_zero} else {x2 - x1};
		let lambda = if b_same {fq_zero} else {numerator/denominator};
		let x3 = lambda*lambda - x1 - x2;
		let y3 = lambda * (x1 - x3) - y1;


		//2. create the var version
		let (x1_var, y1_var) = (self.x.clone(), self.y.clone());
		let (x2_var, y2_var) = (other.x.clone(), other.y.clone());

		//2.1 verified numerator = y2 - y1 regarding Fq
		// sub_target_f itself including cfg(test)
		let numerator_var = y2_var.sub_target_f::<CF3<C>>(&y1_var)?;

		//2.2 verified denom = x2 - x1 regarding Fq
		let denom_var = x2_var.sub_target_f::<CF3<C>>(&x1_var)?;

		//2.3 just build values and then later verify their relation
		let one_var= NonNativeUintVar::<C::ScalarField>::new_constant(
			cs.clone(),  CF3::<C>::one() )?;
		let _zero_var= NonNativeUintVar::<C::ScalarField>::new_constant(
			cs.clone(),  CF3::<C>::zero() )?;
		let numerator_inv = if b_same {fq_zero} 
			else {numerator.inverse().expect("failed on num.inv()")};
		let _num_inv_var = NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(numerator_inv) )?; //compared with denom_inv saves
		let lambda_inv = if b_same {fq_zero} 
			else {lambda.inverse().expect("falied on lambda.inv()")};
		let lambda_inv_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(lambda_inv) )?; 
		let lambda_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(lambda) )?; 
		let x3_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(x3) )?; 
		let y3_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(y3) )?; 

		//2.4 encode lambda = numerator * denom_inv
		// as 1/lambda * numerator = denom
		let tmp1 = lambda_inv_var.mul_no_align(&numerator_var)?;
		denom_var.enforce_congruent::<CF3<C>>(&tmp1)?;
		#[cfg(test)]{denom_var.assert_congruent::<CF3<C>>(&tmp1);}

		//2.5 verify lambda * lamda_inv = 1
		let tmp2 = lambda_inv_var.mul_no_align(&lambda_var)?;
		let b1 = tmp2.is_congruent::<CF3<C>>(&one_var)?;
		let b2 = b1.or(&b_same_var)?; //if b same var skip the test
		b2.enforce_equal(&Boolean::<CF1<C>>::TRUE)?; 
		#[cfg(test)]{ if b2.value().is_ok(){assert!(b2.value().unwrap());}}

		//2.6 enfoce x3 = lambda * lambda - x1 - x2 
		// as x3 * 1/lambda + x1 * 1/lambda + x2 * 1/lambda
		let sum1 = x3_var.add_no_align(&x1_var).add_no_align(&x2_var)
			.mul_no_align(&lambda_inv_var)?;
		let b1 = sum1.is_congruent::<CF3<C>>(&lambda_var)?;
		let _b2 = b1.or(&b_same_var)?; //if b same var skip the test
		#[cfg(test)]{if _b2.value().is_ok(){assert!(b2.value().unwrap());}}

		//2.7 enforce y3 = lambda * (x1- x3) - y1
		// as (y3 + y1) * 1/lbamda + x3 = x1
		let sum2 = y3_var.add_no_align(&y1_var).mul_no_align(&lambda_inv_var)?
			.add_no_align(&x3_var);
		let b1 = sum2.is_congruent::<CF3<C>>(&x1_var)?;
		let _b2 = b1.or(&b_same_var)?; //if b same var skip the test
		#[cfg(test)]{ if _b2.value().is_ok(){assert!(b2.value().unwrap());}}

		let reg_var= Self{x: x3_var, y: y3_var};
		let mut res = b_self_zero_var.select(other, &reg_var)?;
		res = b_other_zero_var.select(self, &res)?;
		Ok( res )
	}

	/// This is essentially double() in non_zero_affine.rs
	/// in r1cs-std/src/groups/curves/short_weierstrass.
	/// Performs: (self + self)
	/// If self is zero, return zero.
	pub fn double(&self) -> Result<Self, Error>{
		//1. get the values in Fq first
		let cs = self.x.cs().clone();
		let fq_zero = C::BaseField::zero();
		let fq_zero_var = NonNativeUintVar::<C::ScalarField>::new_constant(
			cs.clone(), fq_zero)?;
		let (x1, y1) = self.affine_value()?;
		let b_zero = x1.is_zero() && y1.is_zero();
		let b_zero_var = self.is_standard_zero()?;

		let x1_sqr = x1 * x1;
		let numerator = if b_zero {fq_zero} 
			else {x1_sqr + x1_sqr + x1_sqr + C::Config::COEFF_A};
		let denominator = if b_zero {fq_zero} else {y1 + y1};
		let lambda = if b_zero {fq_zero} else {numerator/denominator};
		let x3 = lambda*lambda - x1 - x1;
		let y3 = lambda * (x1 - x3) - y1;


		//2. create the var version
		let (x1_var, y1_var) = (self.x.clone(), self.y.clone());


		let x1_sqr_var = x1_var.mul_no_align(&x1_var)?;
		let a_var = NonNativeUintVar::<C::ScalarField>::new_constant(cs.clone(),
			C::Config::COEFF_A.clone())?;
		let a_var = b_zero_var.select(&fq_zero_var, &a_var)?;


		let right_num_var = x1_sqr_var.add_no_align(&x1_sqr_var)
			.add_no_align(&x1_sqr_var)
			.add_no_align(&a_var);


		let numerator_var = NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok( numerator ))?;
		//2.1 verified numerator
		numerator_var.enforce_congruent::<CF2<C>>(&right_num_var)?;
		#[cfg(test)]{numerator_var.assert_congruent::<CF2<C>>(&right_num_var);}


		//2.2 verified denom = y1 + y1 regarding Fq
		let denom_var = NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok( denominator))?;
		let denom_var = b_zero_var.select(&fq_zero_var, &denom_var)?;
		let tmp1 = y1_var.add_no_align(&y1_var);
		denom_var.enforce_congruent::<CF2<C>>(&tmp1)?;
		#[cfg(test)]{denom_var.assert_congruent::<CF2<C>>(&tmp1);}


		//2.3 just build values and then later verify their relation
		let lambda_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(lambda) )?; 
		let tmp2 = lambda_var.mul_no_align(&denom_var)?;
		numerator_var.enforce_congruent::<CF2<C>>(&tmp2)?;
		#[cfg(test)]{numerator_var.assert_congruent::<CF2<C>>(&tmp2);}


		//2.4 verify x3 and v3
		let x3_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(x3) )?; 
		let tmp3 = x3_var.add_no_align(&x1_var).add_no_align(&x1_var);
		let tmp4 = lambda_var.mul_no_align(&lambda_var)?;
		tmp3.enforce_congruent::<CF2<C>>(&tmp4)?;
		#[cfg(test)]{tmp3.assert_congruent::<CF2<C>>(&tmp4);}

		let y3_var= NonNativeUintVar::<C::ScalarField>::new_witness(
			cs.clone(), || Ok(y3) )?; 
		let tmp6 = y3_var.add_no_align(&y1_var).add_no_align(
			&(lambda_var.mul_no_align(&x3_var))?);
		let tmp7 = lambda_var.mul_no_align(&x1_var)?;
		tmp6.enforce_congruent::<CF2<C>>(&tmp7)?;
		#[cfg(test)]{tmp6.assert_congruent::<CF2<C>>(&tmp7);}

		let res = Self{x: x3_var, y: y3_var};
		Ok( res )
	}


	/// The standard textbook double_and_add approach without
	/// further optimization (needs lookup table to greatly cut
	/// cost, but since this is only used in decider 3 times, 
	/// improve it later), 
	pub fn scalar_mul(&self, bits_le: &Vec<Boolean<C::ScalarField>>)
	->Result<Self, Error>{
		let cs = self.x.0.cs();
		let mut bits = bits_le.clone();
		bits.reverse();
		let mut q_var = NonNativeAffineVar::<C>::zero_var(cs.clone());
		for i in 0..bits.len(){
			q_var = q_var.double()?;
			let sum = q_var.add(self)?;
			q_var = bits[i].select(&sum, &q_var)?;
		}
		Ok(q_var)
	}
}

#[cfg(test)]
mod tests_nonnative_group{
    use ark_bn254::{Fr, G1Projective as G1, Fq};
	use ark_relations::{r1cs::ConstraintSystem};
	use ark_std::{UniformRand};
	use crate::folding::foldpot::{
		nonnative_group::{NonNativeAffineVar,NonNativeUintVar,non_zero_double}
	};
	use ark_r1cs_std::{
		R1CSVar,
		alloc::AllocVar,
		fields::fp::FpVar,
		ToBitsGadget,
	};
	use ark_ec::{CurveGroup,AffineRepr};
	use std::ops::Mul;
	use ark_std::{Zero};

	#[test]
	fn test_nonnative_uint(){//new functions of nonnative uint
		//1. test value_target_f
		let f1 = Fq::from(2u32);
		let f2 = Fq::from(1u32);
        let cs = ConstraintSystem::<Fr>::new_ref();
		let var1 = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(f1)).unwrap();
		let var2 = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(f2)).unwrap();
		let f1_2 = var1.value_target_f::<Fq>().unwrap();
		assert!(f1==f1_2);

		//2. test sub_target_f
		let var3 = var1.sub_target_f::<Fq>(&var2).unwrap();
		let f3 = var3.value_target_f::<Fq>().unwrap();
		assert!(f1==f3+f2);

		//3. test is_standard_one
		let v4 = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(Fq::from(0))).unwrap();
		let v5 = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(Fq::from(101))).unwrap();
		let b1 = v4.is_standard_zero().unwrap();
		let b2 = v5.is_standard_zero().unwrap();
		assert!(b1.value().unwrap() && !b2.value().unwrap());
		assert!(cs.is_satisfied().unwrap());


	}

	#[test]
	fn test_nonnative_affine(){
		//1. test get value
        let mut rng = rand::rngs::OsRng;
		let g2 = G1::rand(&mut rng);
        let cs = ConstraintSystem::<Fr>::new_ref();
		let g2_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(), 
			|| Ok(g2)).unwrap();
		let g1_var = NonNativeAffineVar::<G1>::zero_var(cs.clone());
		let (x,y)= g2_var.affine_value().unwrap();
		let g2_affine = g2.into_affine();
		let (x2,y2) = g2_affine.xy().unwrap();
		assert!(x==*x2 && y==*y2);

		//2. test is_zero
		let b1 = g1_var.is_standard_zero().unwrap();
		let b2 = g2_var.is_standard_zero().unwrap();
		assert!(b1.value().unwrap() && !b2.value().unwrap());

		//3. test non_zero_double
		let g1 = G1::rand(&mut rng);
		let g1_d = g1 + g1;
		let g1_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(),
			|| Ok(g1)).unwrap();
		let g1_d_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(),
			|| Ok(g1_d)).unwrap();
		let (x,y) = g1_var.affine_value().unwrap();
		let (x2,y2) = g1_d_var.affine_value().unwrap();
		let (x3,y3) = non_zero_double::<G1>(x, y).unwrap();
		assert!(x2==x3 && y2==y3);
		assert!(cs.is_satisfied().unwrap());
	}

	fn test_add_worker(g1: G1, g2: G1){
        let cs = ConstraintSystem::<Fr>::new_ref();
		let g3 = (g1 + g2).into_affine();
		let g1_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(), 
			|| Ok(g1)).unwrap();
		let g2_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(), 
			|| Ok(g2)).unwrap();
		let g3_var = g1_var.add(&g2_var).unwrap();
		let (x,y) = g3_var.affine_value().unwrap();
		let (x2,y2)= if g3.is_zero() {(Fq::zero(), Fq::zero())} 
			else {
				let (x,y) = g3.xy().unwrap();
				(*x, *y)
			};
		assert!(x==x2 && y==y2);
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_add(){
        let mut rng = rand::rngs::OsRng;
		let g1 = G1::rand(&mut rng);
		let g2 = G1::rand(&mut rng);
		let zero = G1::zero();

		test_add_worker(g1, g2);
		// test_add_worker(g1, g1); -> will trigger err, call double instead
		test_add_worker(g1, zero);
		test_add_worker(zero, g1);
		test_add_worker(zero, zero);
	}

	fn test_double_worker(g1: G1){
        let cs = ConstraintSystem::<Fr>::new_ref();
		let g3 = (g1 + g1).into_affine();
		let g1_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(), 
			|| Ok(g1)).unwrap();
		let g3_var = g1_var.double().unwrap();
		let (x,y) = g3_var.affine_value().unwrap();
		let (x2,y2)= if g1.is_zero() {(Fq::zero(), Fq::zero())} else {
			let (x,y) = g3.xy().unwrap();
			(*x, *y)
		};
		assert!(x==x2 && y==y2);
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_double(){
        let mut rng = rand::rngs::OsRng;
		let g1 = G1::rand(&mut rng);
		let g0 = G1::zero();
		test_double_worker(g1);
		test_double_worker(g0);
	}

	#[test]
	fn test_scalar_mul(){
        let mut rng = rand::rngs::OsRng;
        let cs = ConstraintSystem::<Fr>::new_ref();
		let g1 = G1::rand(&mut rng);
		let g1_var = NonNativeAffineVar::<G1>::new_witness(cs.clone(),
			|| Ok(g1)).unwrap();
		let r = Fr::rand(&mut rng);
		let r_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(r)).unwrap();
		let bits = r_var.to_bits_le().unwrap();
		let res_f = g1.mul(&r).into_affine();
		let (x,y) = res_f.xy().unwrap();
		assert!(cs.is_satisfied().unwrap(), "before mul");

		let res_var = g1_var.scalar_mul(&bits).unwrap();
		let (x2, y2) = res_var.affine_value().unwrap();
		assert!(*x==x2 && *y==y2);
		assert!(cs.is_satisfied().unwrap(), "after mul");
	}

}
