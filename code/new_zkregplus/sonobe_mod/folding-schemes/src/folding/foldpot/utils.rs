/* Created 01/07/2025
Utility classes/functions
*/
use utils::{consts::ADD_CHAIN_SIZE};
use rayon::iter::{ParallelIterator,IntoParallelIterator,IntoParallelRefIterator};
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
use ark_r1cs_std::fields::fp::AllocatedFp;
use ark_relations::{lc,
	r1cs::{SynthesisError,ConstraintSystemRef,
//	LinearCombination,Variable
	}
};

use ark_r1cs_std::{
	boolean::{Boolean},
	fields::{
		//FieldVar,
		fp::FpVar,
		fp::FpVar::Constant,
		fp::FpVar::Var,
	},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};
use ark_relations::r1cs::{Variable,LinearCombination};


// determines if timer prints (but will not block recording)
pub const LOG_LEVEL:usize = 2;
pub const LOG3:usize = 0;
pub const LOG2:usize = 1;
pub const LOG1:usize = 0;
pub const B_DEBUG:bool = false; //category 1
pub const B_DEBUG2:bool = true; //cateogry 2
pub const B_DEBUG3:bool = true; //category 3 (higher ID the higher cost)

/// NOTE it has an internal bug, manually turn it on 
/// if you need it.
pub fn check_cs<F:PrimeField>(cs: &ConstraintSystemRef<F>, info: &str){
	let b_debug = true;
	println!("-- DEBUG USE 1001: entering CHECK: {}", info);
	if b_debug && cs.should_construct_matrices(){
		let csat = cs.is_satisfied();
		if csat.is_ok(){ 
			let res = csat.unwrap();
			if res{
				println!("-- DEBUG USE 1001.2: CHECK cs passing: {}", info);
			}else{
				assert!(csat.unwrap(), "ERROR: not satisfiable: {}", info);
			}
		}
	}
}

pub fn format_bytes(bytes: usize) -> String {
    const KB: f64 = 1024.0;
    const MB: f64 = 1024.0 * 1024.0;
    const GB: f64 = 1024.0 * 1024.0 * 1024.0;

    let b = bytes as f64;
    if b < KB {
        format!("{} bytes", bytes)
    } else if b < MB {
        format!("{:.2} KB", b / KB)
    } else if b < GB {
        format!("{:.2} MB", b / MB)
    } else {
        format!("{:.2} GB", b / GB)
    }
}

/// generate the inverse for vec[i] if vec[i]!=0; otherwise
/// return 0, using parallelism
pub fn gen_vec_inverse<F:PrimeField>(vec: &Vec<F>)->Vec<F>{
	vec.par_iter().map(|v|{
		if v.is_zero(){F::zero()} else{
			v.inverse().unwrap()
		}
	}).collect::<Vec<F>>()
}

/// it is cheapter than standard arkworks is_zero(), which costs 3 constraints.
/// it returns 1 when v is zero and 0 when v is not zero.
/// It's guaranteed to be boolean. COST: (2 constraints).
/// the reason is that we skipped z*(1-z) = 0 check when arkworks converted
/// to boolean. It's already guaranteed by the two constraints in the body.
/// We output a FpVar (1/0) to avoid extra BoolVar constraint.
pub fn is_zero_better<F:PrimeField>(x: &FpVar<F>, cs: &ConstraintSystemRef<F>)
->Result<FpVar<F>, SynthesisError>{
	let lb_zero= lc!();
	let lb_one = lc!() + (F::one(), Variable::One);
	let z = FpVar::new_witness(cs.clone(), || {
        let xv = x.value()?;
        if xv.is_zero() { Ok(F::one()) } else { Ok(F::zero()) }
    })?;
	let inv = FpVar::new_witness(cs.clone(), || {
        let xv = x.value()?;
        if xv.is_zero() { Ok(F::zero()) } else { Ok(xv.inverse().unwrap()) }
    })?;
    // Constraint 1: x * inv = 1 - z
	let lb_x = var_to_lb(x, F::one());
	let lb_z = var_to_lb(&z, F::one());
	let lb_inv = var_to_lb(&inv, F::one());
	let z_variable = fpvar_to_var(&z);
	let lb_res = lb_one + (-F::one(), z_variable);
	cs.enforce_constraint(
		lb_x.clone(),
		lb_inv,
		lb_res
	)?;

    // Constraint 2: x * z = 0
	cs.enforce_constraint(
		lb_x,
		lb_z,
		lb_zero
	)?;

	Ok(z)
}


/// convert a FP var to LinearCombination
pub fn var_to_lb<F:PrimeField>(v: &FpVar<F>, coef: F)->LinearCombination<F>{
	let res = match v{
		Var(v) => LinearCombination::from( (coef, v.variable) ),
		Constant(val) => LinearCombination::from(
			(*val*coef, Variable::One)
		)
	};

	res
}

/// assumption v1 and v2 both have to be AllocatedFp
/// This will be faser than &v1 * &v1 (avg: 271ns)
/// Cost: 231 ns (improved 40ns) 
#[inline(always)]
pub fn alloc_fpvar_mul<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>)->FpVar<F>{
	if let Var(rv1) = v1{
		if let Var(rv2) = v2{
			return FpVar::<F>::Var(AllocatedFp::<F>::mul(&rv1, &rv2));
		}
	}
	panic!("v1 or v2 is not AllocatedFpVar")
}

/// sum up 3 FpVar (allow constants)
#[inline(always)]
pub fn sum3<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>, v3: &FpVar<F>)
->FpVar<F>{
	 let value = v1.value().unwrap() + v2.value().unwrap() + 
	 		v3.value().unwrap();

	let tp1 = var_to_tuple(v1);
	let tp2 = var_to_tuple(v2);
	let tp3 = var_to_tuple(v3);
	let lb = LinearCombination::<F>(
		vec![tp1, tp2, tp3]
	);
	let variable = v1.cs().new_lc(lb).unwrap();
	let res = AllocatedFp::new(Some(value), variable, v1.cs().clone());

	FpVar::Var(res)
}

/// subtraction (faster than trait dispatch),  allow constants
/// Can improve about 30 ns for &v1 - &v2 (196ns -> 160ns)
#[inline(always)]
pub fn sub2<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>)
->FpVar<F>{
	 let value = v1.value().unwrap() - v2.value().unwrap();

	let tp1 = var_to_tuple(v1);
	let tp2 = var_to_tuple_adv(v2, F::zero()-F::one());
	let lb = LinearCombination::<F>(
		vec![tp1, tp2]
	);
	let variable = v1.cs().new_lc(lb).unwrap();
	let res = AllocatedFp::new(Some(value), variable, v1.cs().clone());

	FpVar::Var(res)
}

/// FpVar to a tuple (can handle consants
#[inline(always)]
pub fn var_to_tuple<F:PrimeField>(v: &FpVar<F>)->(F,Variable){
	let res = match v{
		Var(v) => (F::one(), v.variable) ,
		Constant(val) => (*val, Variable::One)
	};

	res
}

/// FpVar to a tuple (can handle consants
#[inline(always)]
pub fn var_to_tuple_adv<F:PrimeField>(v: &FpVar<F>, c: F)->(F,Variable){
	let res = match v{
		Var(v) => (c, v.variable) ,
		Constant(val) => (*val*c, Variable::One)
	};

	res
}


/// convert a FP var tovar  
pub fn fpvar_to_var<F:PrimeField>(v: &FpVar<F>)->Variable{
	let res = match v{
		Var(v) => v.variable,
		Constant(_) => panic!("expecting var!")
	};

	res
}

/// print a vector
pub fn print_vec_var<F:PrimeField>(msg: &str, v: &Vec<FpVar<F>>){
	println!("=== {} ===", msg);
	for i in 0..v.len(){
		println!("  i: {} => {}", i, v[i].value().unwrap());
	}
}

/// get the RAM usage in GB
pub fn get_mem_usage()->usize{
	let usage = memory_stats().expect("call mem usage fails");
	usage.virtual_mem/(1024*1024*1024)
}

/// get the RAM in MB
pub fn get_mem_usage_mb()->usize{
	let usage = memory_stats().expect("call mem usage fails");
	usage.virtual_mem/(1024*1024)
}

/// number of MB to string
pub fn mb2s(mb: usize)->String{
	if mb<1024{ 
		format!("{} MB", mb)	
	} else{ 
		format!("{} GB", mb/1024)
	}
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

/// We use timer as a Timer but also as a data recorder.
/// It can keeps track of all time pieces in microseconds
/// and it keeps a customized 2-d column for every time piece
#[allow(dead_code)]
pub struct Timer{
	/// instance it is started
	inst: Instant,	
	/// name of the timer
	name: String,	
	/// indentation lvel
	level: usize,

	/// number of extra data cols
	num_extra_cols: usize,
	/// description of extra cols
	desc_extra_cols: Vec<String>,
	/// extra data cols (will have data if num_extra_cols>0)
	extra_data: Vec<Vec<usize>>,
	/// time pieces in microseconds
	time_pieces: Vec<usize>,
	/// if the clock is running
	b_running: bool,
}

pub fn new_var<F:PrimeField>(cs: &ConstraintSystemRef<F>, v: F)
->FpVar<F>{
	FpVar::<F>::new_witness(cs.clone(), ||
		Ok(v)).expect("new var err")
}
impl Timer{
	/// level means indentation level
	pub fn new(s: &str, level: usize)->Self{
		Self{
			inst: Instant::now(),
			name: s.to_string(),
			level,
			num_extra_cols: 0,
			desc_extra_cols: vec![],
			extra_data: vec![],
			time_pieces: vec![],
			b_running: true, //after creation it's started
		}
	}

	pub fn new_adv(s: &str, level: usize, desc: &Vec<&str>)->Self{
		Self{
			inst: Instant::now(),
			name: s.to_string(),
			level,
			num_extra_cols: 0,
			desc_extra_cols: desc.iter().map(|s| s.to_string())
				.collect::<Vec<String>>(),
			extra_data: vec![],
			time_pieces: vec![],
			b_running: false, //needs manual start
		}
	}

	/// can only be used in default mode where there is
	/// no extra data (if has extra data, has to call prv_adv)
	pub fn prt(&mut self, msg: &str){
		self.stop(vec![]);
		if LOG_LEVEL>=self.level {
			print!("");
			for _i in 0..self.level{print!("-");}
			print!(" {}: {}: {:?}", self.name, msg, self.inst.elapsed());
			println!("");
		}
		self.start();
	}

	/// expecting nonw-empty data_row. b_start indicate whether
	/// to start the clock immediately
	pub fn prt_adv(&mut self, msg: &str, data_row: Vec<usize>, b_start: bool){
		self.stop(data_row);
		if LOG_LEVEL>=self.level {
			print!("");
			for _i in 0..self.level{print!("-");}
			print!(" {}: {}: {:?}", self.name, msg, self.inst.elapsed());
			println!("");
		}
		if b_start{ self.start();}
	}

	/// start ticking
	pub fn start(&mut self){
		assert!(!self.b_running);
		self.inst = Instant::now();
		self.b_running = true;
	}

	/// stop ticking and feed the data
	pub fn stop(&mut self, extra_data_row: Vec<usize>){
		assert!(self.b_running);
		let micro_sec = self.inst.elapsed().as_micros();
		self.time_pieces.push(micro_sec as usize);
		assert!(extra_data_row.len()==self.num_extra_cols);
		if extra_data_row.len()>0{
			self.extra_data.push(extra_data_row);
		}
		self.b_running = false;
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
		//at this moment, we don't need to following because
		//we break the build up of long linear combinations by
		//inserting prod with one_witness_var every 100 items in
		//sonobe code.
		//COMMENT OUT LATER if does not help
		//if i%128==0{//break too long chain of eval_f() to avoid stack overflow
			//if prod.value().is_ok(){ 
			//	assert!(prod.value()?==F::one()); 
			//}
		//}
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
	let one_var= FpVar::<F>::new_constant(cs.clone(), F::one())?;
	let one_wit_var = FpVar::<F>::new_witness(cs.clone(), ||Ok(F::one())).unwrap();
	one_wit_var.enforce_equal(&one_var)?; 

	let mut sum_left= FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v1.len(){
		sum_left = &sum_left + &v1[i];
		if i%ADD_CHAIN_SIZE==0{ //to break the long linear combination chain
			sum_left = &sum_left * &one_wit_var; 
			let _val = sum_left.value()?; //to avoid long eval chain
		}
	}
	sum_left = &sum_left * &one_wit_var;

	let mut sum_right = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v2.len(){ 
		sum_right+= &(&v2[i] * &m_tbl[i]);
		//COMMENT OUT LATER IF DOES NOT HELP
		//if i%128==0{//this is to prevent the cfg(test) code calling value
			//for chain too long, which overflows stack when it's doing 
			//recursion.
			 //let value= sum_right.value();
			 //assert!(value.is_ok());
		//}
	}
	assert!(sum_left.value()? == sum_right.value()?);
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
	// because it uses Arc<Mutex<ConstraintSystem>>. We have to use
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
