/* Created 01/07/2025
Utility classes/functions
*/
use rayon::iter::{ParallelIterator,IntoParallelIterator};
use std::time::{Instant};
use ark_ff::{PrimeField,BigInteger};
use ark_std::{Zero};
use num_bigint::{BigUint};
use std::ops::{Rem};
use crate::folding::circuits::nonnative::uint::NonNativeUintVar;
use memory_stats::memory_stats;
use libc::{pthread_getattr_np, pthread_attr_getstack, pthread_self};
use std::mem::MaybeUninit;
use std::ptr;
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::{
	boolean::{Boolean},
	fields::{
		//FieldVar,
		fp::FpVar
	},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};


pub const LOG_LEVEL:usize = 2;

/// get the RAM usage in GB
pub fn get_mem_usage()->usize{
	let usage = memory_stats().expect("call mem usage fails");
	usage.virtual_mem/(1024*1024*1024)
}

/// get the stack available in bytes
pub fn get_stack_space()->usize{
	unsafe {
		//1. get pthread attr
        let mut attr = MaybeUninit::uninit();
        if pthread_getattr_np(pthread_self(), attr.as_mut_ptr()) != 0 {
			panic!("ERROR in getting pthread attr");
        }
        let attr = attr.assume_init();

		//2. get stack attributes (base and size)
		let mut stack_size: usize = 0;
        let mut stack_base: *mut libc::c_void = ptr::null_mut();
        if pthread_attr_getstack(&attr, &mut stack_base as *mut _, 
			&mut stack_size as *mut _) != 0 {
			panic!("ERROR reading stack attr");
        }

		//3. declare a new var to get top of stack (top means go to 
		// LOWER addr)
        let current_sp: usize = {
            let local: u8 = 0;
            &local as *const u8 as usize
        };
        let base = stack_base as usize;
		let res = current_sp - base;

		res
    }
}

/// expand into vec of tuples
pub fn expand2(v: &Vec<usize>)->Vec<(usize,usize)>{
	v.into_iter().map(|x| (*x,*x)).collect::<Vec<(usize,usize)>>()
}

pub struct Timer{
	/// instance it is started
	inst: Instant,	
	/// name of the timer
	name: String,	
	/// indentation lvel
	level: usize
}

impl Timer{
	/// level means indentation level
	pub fn new(s: &str, level: usize)->Self{
		Self{
			inst: Instant::now(),
			name: s.to_string(),
			level
		}
	}

	pub fn prt(&mut self, msg: &str){
		if LOG_LEVEL<self.level {return;}

		print!("");
		for _i in 0..self.level{print!("-");}
		print!(" {}: {}: {:?}", self.name, msg, self.inst.elapsed());
		println!("");

		self.inst = Instant::now();	
	}
}

/// convert a field to big uint
pub fn f_to_biguint<F:PrimeField>(f: &F)->BigUint{
	let bits = f.into_bigint().to_bits_le();
	bits_le_to_biguint(&bits)
}

/// Biguint to F (do the mod op if it's over the limit)
pub fn biguint_to_f<F:PrimeField>(u: &BigUint)->F{
	let m_bits = F::MODULUS.to_bits_le();
	let u_mod = bits_le_to_biguint(&m_bits);
	let u_rem = u.rem(&u_mod);
	let bits = biguint_to_bits_le(&u_rem);
	let f = F::from_bigint(F::BigInt::from_bits_le(&bits))
		.expect("conv f fails");
	f
}

/// convert from bits
pub fn bits_le_to_biguint(bits: &Vec<bool>)->BigUint{
	//1. extend bits if its length %8!=0
	let bits = if bits.len()%8==0 {bits.clone()} else{
		let target_len = (bits.len()/8 + 1) * 8;
		let n_more = target_len - bits.len();
		let mut bits2 = bits.clone();
		let mut rem_part = vec![false; n_more];
		bits2.append(&mut rem_part);
		bits2
	};

	let bytes = bits.chunks(8).map(|chunk| bits_to_u8(&chunk.to_vec()))
		.collect::<Vec<u8>>();
	BigUint::from_bytes_le(&bytes)
}

/// convert to bits
pub fn biguint_to_bits_le(u: &BigUint)->Vec<bool>{
	let bytes = u.to_bytes_le();
	bytes.into_iter().flat_map(|x|  u8_to_bits(x)).collect()
}

/// u8 to bits (le)
pub fn u8_to_bits(n: u8) -> Vec<bool>{
	let mut res = vec![false; 8];
	for i in 0..8{ res[i] = (n>>i) & 1  == 1; }
	res
}

// bits to u8
pub fn bits_to_u8(bits: &Vec<bool>)->u8{
	assert!(bits.len()==8);
	let mut res = 0;
	for (i, &bit) in bits.iter().enumerate(){
		if bit{ res |= 1<<i;}
	}
	res
}

/// if F1 is encoded using F2, how many limbs are there
pub fn get_limb_size<F1:PrimeField, F2:PrimeField>()->usize{
	let f1 = F1::zero();
	let temp_limbs = f1_to_f2_limbs::<F1,F2>(&f1);
	temp_limbs.len()
}

/// convert one field element to segments of limbs in F2.
/// This simulates the NonNativeUintVar::inputize function.
/// Both should be base prime field elements (extension degree 1).
pub fn f1_to_f2_limbs<F1: PrimeField, F2: PrimeField>(v: &F1)->Vec<F2>{
	let bits_per_limb = NonNativeUintVar::<F2>::bits_per_limb();
	#[cfg(test)]{
		assert_eq!(F1::extension_degree(), 1); //both should be base prime field
		assert_eq!(F2::extension_degree(), 1); 
		assert_eq!(NonNativeUintVar::<F1>::bits_per_limb(),bits_per_limb);
	}

	let res = v.into_bigint().to_bits_le()
		.chunks(bits_per_limb)
		.map(|chunk| F2::from_bigint(F2::BigInt::from_bits_le(chunk)).unwrap())
		.collect();
	res
}

/// convert f1_limbs to bigUint first (could handle the case that
/// bituint exceeds F2::MODULUS - takes mod operation), and then
/// convert to F2. Note that sometimes limbs are exceeding the
/// bits_per_limt (as long as not exceeding MODULUS/2), in this case
/// assemble using the algorithm of NonInteractiveUint
pub fn f1_limbs_to_f2<F1:PrimeField, F2:PrimeField>(v: &Vec<F1>)->F2{
	let limb_size = NonNativeUintVar::<F1>::bits_per_limb() as usize;
	let mut r = BigUint::zero();
	//simulating the value() function of NonNativeUintVar
	for limb in v.into_iter().rev() {
		r <<= limb_size;
		let limb_val = f_to_biguint(limb);
		r += limb_val;
	}
	let f2 = biguint_to_f::<F2>(&r);
	
	f2
}

// this function is copied verbatim from gadgets/common.rs to avoid
// too much module inter/recursive dependence
/// verify v2 is an inverse of v1. elen is the expected length of both
/// array. Beta is the random challenge
pub fn verify_inverse<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], 
	beta: &FpVar<F>, elen: usize)->Result<(), SynthesisError>{
	assert!(v1.len()==v2.len());
	assert!(v1.len()==elen);
	let one_var= FpVar::<F>::new_constant(cs.clone(), F::one())?;
	for i in 0..elen{
		let prod = &v2[i] * &(&v1[i] + beta);
		prod.enforce_equal(&one_var)?;
		#[cfg(test)]{
			if prod.value().is_ok(){ assert!(prod.value()?==F::one()); }
		}
	}
	Ok( () )
}

// this function is adapted from zkreg/gadgets/utils.rs: verify_log_inverse
/// verify the log-up relation. check if all elements of (inverse of) v1 belong
/// to v2. Here v1 and v2 should be the
/// INVERSE of the query table and lkup table.  Call verify_inverse()
/// first on the inversed table and the original table before calling this
/// function.
/// Return Boolean to indicate if the check is pass or not
pub fn is_logup_inverse_correct<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], m_tbl: &[FpVar<F>])
	->Result<Boolean<F>, SynthesisError>{
	assert!(v2.len()==m_tbl.len());
	let mut sum_left = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v1.len(){ sum_left += &v1[i]; }

	let mut sum_right = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v2.len(){ 
		sum_right+= &(&v2[i] * &m_tbl[i]);
		if i%128==0{//this is to prevent the cfg(test) code calling value
			//for chain too long, which overflows stack when it's doing 
			//recursion.
			let value= sum_right.value();
			assert!(value.is_ok());
		}
	}

	let res = sum_left.is_eq(&sum_right)?;
	Ok( res )
}

// this function is adapted from zkreg/gadgets/db.rs assert_logup
// the only difference is that it returns Boolean to indicate logup relation
// is true
/// assert that each element of qry belongs to lkup.
/// Note that both qry and lkup may contain multiple duplicates.
/// We use the Logup algorithm ([Hab22] `https://eprint.iacr.org/2022/1530`).
/// 
/// NOTE that there are two parts: using the Fiat-shamir challenge r,
/// generate the inverse table for qry and lkup, and then, check the m_tbl
/// relation: sum_{i=1}^{n} 1/(qry[i]+r) = sum_{j=1}^N m_tb[j]/(lkup[j]+r)
/// COST: 2*qry_size + 3*lkup_size 
pub fn check_logup<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	qry: &Vec<FpVar<F>>, 
	lkup: &Vec<FpVar<F>>,
	m_tbl: &Vec<FpVar<F>>, 
	r: &FpVar<F>)
->Result<Boolean<F>, SynthesisError>{
	//1. generte the inverse table (as part of msg3)
	let r_val = r.value().expect("error get val of r");
	let qry_val = qry.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>();
	let lkup_val = lkup.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>();
	let qry_inv_val = qry_val.into_par_iter().map(|x| 
		(r_val+x).inverse().expect("inv err")
	).collect::<Vec<F>>();
	let lkup_inv_val = lkup_val.into_par_iter().map(|x| 
		(r_val+x).inverse().expect("inv err")
	).collect::<Vec<F>>();
	// unfortunately ConstraintSystemRef can't be sent to Rayon threads safely
	// because it uses Rc<RefCell<ConstraintSystem>>. We have to use
	// iter() here. Cost is about 500ms for 2^20 variables in testing mode
	// probably in release mode for 50ms.
	let qry_inv = qry_inv_val.iter().map(|x| FpVar::new_witness(
		cs.clone(), || Ok(x)).unwrap()).collect::<Vec<FpVar<F>>>();
	let lkup_inv = lkup_inv_val.iter().map(|x| FpVar::new_witness(
		cs.clone(), || Ok(x)).unwrap()).collect::<Vec<FpVar<F>>>();

	//2. verify inverse
	verify_inverse(cs.clone(), &qry, &qry_inv, &r, qry.len())?;
	verify_inverse(cs.clone(), &lkup, &lkup_inv, &r, lkup.len())?;

	//3. verify logup relation (m_table)
	let res = is_logup_inverse_correct(cs.clone(), 
		&qry_inv, &lkup_inv, m_tbl)?; 

	Ok( res )
}


#[cfg(test)]
pub mod tests_utils{
    use ark_bn254::{Fr, Fq};
	use ark_std::{UniformRand};
	use crate::folding::foldpot::utils::{f_to_biguint, biguint_to_f, f1_to_f2_limbs, f1_limbs_to_f2};

	#[test]
	fn test_bituint(){
		//1. simple test
        let mut rng = ark_std::test_rng();
		let f1 = Fq::rand(&mut rng);
		let u1 = f_to_biguint(&f1);
		let f2 = biguint_to_f::<Fq>(&u1);
		assert!(f1==f2);
		let f1 = Fr::rand(&mut rng);
		let u1 = f_to_biguint(&f1);
		let f2 = biguint_to_f::<Fr>(&u1);
		assert!(f1==f2);

		//2. test modular part
		let f3 = f1 + f1 + f1 + f1 + f1 + f1;
		let u3 = &u1 + &u1 + &u1 + &u1 + &u1 + &u1;
		let f3_2 = biguint_to_f::<Fr>(&u3); //mod applied
		assert!(f3==f3_2);
	}

	#[test]
	fn test_f1_to_f2_limbs(){
        let mut rng = ark_std::test_rng();
		let f1 = Fr::rand(&mut rng);
		let limbs = f1_to_f2_limbs::<Fr,Fq>(&f1);
		let f1_2 = f1_limbs_to_f2::<Fq,Fr>(&limbs);
		assert!(f1==f1_2);

		let f1 = Fq::rand(&mut rng);
		let limbs = f1_to_f2_limbs::<Fq,Fr>(&f1);
		let f1_2 = f1_limbs_to_f2::<Fr,Fq>(&limbs);
		assert!(f1==f1_2);
	}
}
