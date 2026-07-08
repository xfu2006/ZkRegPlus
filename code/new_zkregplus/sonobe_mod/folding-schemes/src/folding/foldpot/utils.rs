/* Created 01/07/2025
Utility classes/functions
*/
use utils::{consts::{ADD_CHAIN_SIZE, read_global_config, current_bit_parts}, logger::{log, log_perf, emit_stdout, ERR, LOG2 as LOGL2}, timer::Timer as GTimer};
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
pub const B_DEBUG2:bool = false; //cateogry 2
pub const B_DEBUG3:bool = false; //category 3 (higher ID the higher cost)

/// NOTE it has an internal bug, manually turn it on
/// if you need it.
pub fn check_cs<F:PrimeField>(cs: &ConstraintSystemRef<F>, info: &str){
	let b_debug = B_DEBUG;
	if b_debug{ emit_stdout(format!(
		"-- DEBUG USE 1001: entering CHECK: {}", info));}
	if b_debug && cs.should_construct_matrices(){
		let csat = cs.is_satisfied();
		if csat.is_ok(){
			let res = csat.unwrap();
			if res{
				emit_stdout(format!(
					"-- DEBUG USE 1001.2: CHECK cs passing: {}",
					info));
			}else{
				assert!(csat.unwrap(), "ERROR: not satisfiable: {}", info);
			}
		}
	}
}

/// Runtime-gated, NON-panicking satisfiability probe. When env
/// ZKR_CS_CHECK is set and cs is in prove mode (matrices built, not
/// setup), report whether the constraints built SO FAR are satisfied and,
/// if not, the index of the FIRST bad constraint -- tagged with job_id and
/// a block label so a concurrent N-way batch (bisect_job3.py) localizes the
/// failing gadget WITHOUT aborting the run. Constraint traces stay disabled
/// so which_is_unsatisfied returns the bare index. Zero cost when unset.
pub fn check_cs_probe<F:PrimeField>(cs: &ConstraintSystemRef<F>,
	info: &str, job_id: usize){
	if std::env::var("ZKR_CS_CHECK").is_err() { return; }
	if cs.is_in_setup_mode() || !cs.should_construct_matrices() { return; }
	let n = cs.num_constraints();
	match cs.which_is_unsatisfied() {
		Ok(None) => log(job_id, ERR, &format!(
			"DEBUG USE 62001.1: CS OK    @{} ({} cons)", info, n)),
		Ok(Some(idx)) => log(job_id, ERR, &format!(
			"DEBUG USE 62001.2: CS UNSAT @{} first-bad={} of {} cons",
			info, idx, n)),
		Err(e) => log(job_id, ERR, &format!(
			"DEBUG USE 62001.3: CS probe err @{}: {:?}", info, e)),
	}
}

// ===== DEBUG USE 62730 BEGIN (REMOVE LATER): per-gadget SAT checkpoints =====
// A process-global flag armed either by the single-step repro (test) or by
// mod_super at the target fold step. When on, gadget_sat_check() runs an
// is_satisfied() on the constraints built SO FAR and, at the FIRST unsatisfied
// checkpoint, names the gadget label + first-bad row and PANICS -- so a single
// faithful synthesis of the culprit step aborts AT the offending sub-gadget
// (finer than the whole-step first_bad_row from 62727.1). Zero cost when off.
pub static GADGET_SAT: std::sync::atomic::AtomicBool =
	std::sync::atomic::AtomicBool::new(false);
pub fn set_gadget_sat(b: bool){
	GADGET_SAT.store(b, std::sync::atomic::Ordering::Relaxed);
}
pub fn gadget_sat_on() -> bool {
	GADGET_SAT.load(std::sync::atomic::Ordering::Relaxed)
}
/// Labeled satisfiability checkpoint. No-op unless GADGET_SAT is armed and cs
/// is in prove mode with matrices. On UNSAT: prints 62730.2 + panics (naming
/// the sub-gadget). which_is_unsatisfied returns the bare index (traces off).
pub fn gadget_sat_check<F:PrimeField>(cs: &ConstraintSystemRef<F>, label: &str){
	if !gadget_sat_on() { return; }
	if cs.is_in_setup_mode() || !cs.should_construct_matrices() { return; }
	let n = cs.num_constraints();
	match cs.which_is_unsatisfied() {
		Ok(None) => emit_stdout(format!(
			"DEBUG USE 62730.1: GADGET-SAT OK    @{} ({} cons)", label, n)),
		Ok(Some(idx)) => {
			emit_stdout(format!(
				"DEBUG USE 62730.2: GADGET-UNSAT @{} first-bad={} of {} cons",
				label, idx, n));
			panic!("DEBUG USE 62730.2: GADGET-UNSAT @{} first-bad={} of {} cons",
				label, idx, n);
		}
		Err(e) => emit_stdout(format!(
			"DEBUG USE 62730.3: GADGET-SAT err   @{}: {:?}", label, e)),
	}
}
// ===== DEBUG USE 62730 END =====

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

/// Bit-width assumed for runtime exponents in `alloc_le_bits` /
/// `pow_le`-style usage in this crate.  Any FpVar value fed into
/// `alloc_le_bits` MUST fit in this many bits or the recomposition
/// equality fails (and the proof is rejected).
pub const POW_LE_BITS: usize = 32;

/// Allocate `POW_LE_BITS` little-endian Boolean witnesses for `v`
/// and enforce  Σ b_i · 2^i  ==  v.  Implicitly bounds  v < 2^32.
///
/// Cost: POW_LE_BITS r1cs (booleanity) + 1 r1cs (the recomposition
/// equality).  Designed to be paired with `FieldVar::pow_le` for
/// runtime-exponent powers where the exponent is known to fit in
/// 32 bits.
pub fn alloc_le_bits<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	v: &FpVar<F>,
) -> Result<Vec<Boolean<F>>, SynthesisError> {
	let val_bits: Vec<bool> = match v.value() {
		Ok(f) => {
			let full = f.into_bigint().to_bits_le();
			// sanity: high bits should all be zero in production
			debug_assert!(
				full.iter().skip(POW_LE_BITS).all(|b| !b),
				"alloc_le_bits: value exceeds 2^{} bound",
				POW_LE_BITS
			);
			let mut bs = full;
			bs.resize(POW_LE_BITS, false);
			bs
		}
		Err(_) => vec![false; POW_LE_BITS], //synthesis-mode
	};

	let bits: Vec<Boolean<F>> = (0..POW_LE_BITS)
		.map(|i| Boolean::new_witness(cs.clone(), || Ok(val_bits[i])))
		.collect::<Result<Vec<_>,_>>()?;

	// recompose: Σ bits[i]·2^i  ==  v
	let mut acc = FpVar::<F>::Constant(F::zero());
	let mut pow = F::one();
	let two = F::from(2u64);
	for b in &bits {
		let b_fp: FpVar<F> = FpVar::from(b.clone());
		acc = acc + b_fp * FpVar::<F>::Constant(pow);
		pow *= two;
	}
	acc.enforce_equal(v)?;

	Ok(bits)
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
	emit_stdout(format!("=== {} ===", msg));
	for i in 0..v.len(){
		emit_stdout(format!(
			"  i: {} => {}", i, v[i].value().unwrap()));
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
			// Build the whole line as a single String so the
			// drainer emits it atomically (one line per send).
			let dashes = "-".repeat(self.level);
			emit_stdout(format!(
				"{} {}: {}: {:?}",
				dashes, self.name, msg, self.inst.elapsed()));
		}
		self.start();
	}

	/// expecting nonw-empty data_row. b_start indicate whether
	/// to start the clock immediately
	pub fn prt_adv(&mut self, msg: &str, data_row: Vec<usize>, b_start: bool){
		self.stop(data_row);
		if LOG_LEVEL>=self.level {
			let dashes = "-".repeat(self.level);
			emit_stdout(format!(
				"{} {}: {}: {:?}",
				dashes, self.name, msg, self.inst.elapsed()));
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
	if B_DEBUG {
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

// --- Added for raw affine serialization ---
use ark_ec::{AffineRepr, short_weierstrass::{Affine, SWCurveConfig}};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use rayon::prelude::*;
use std::fs::{File, metadata};
use std::io::{BufWriter, BufReader};
use std::path::Path;
//use ark_groth16::{ProvingKey, VerifyingKey};
use ark_bn254::Bn254;

use std::io::{Read, Write};
use ark_serialize::Compress;

pub fn serialize_affines_compressed_raw<P: SWCurveConfig>(v: &[Affine<P>], path_prefix: &str) {
    let path = format!("{}_compressed.data", path_prefix);
    if v.is_empty() {
        File::create(&path).expect("create file err");
        return;
    }
    let dummy = Affine::<P>::zero();
    let point_size = dummy.serialized_size(Compress::Yes);
    let total_size = point_size * v.len();
    let mut buffer = vec![0u8; total_size];
    buffer.par_chunks_mut(point_size).zip(v.par_iter()).for_each(|(chunk, pt)| {
        let mut slice: &mut [u8] = chunk;
        pt.serialize_compressed(&mut slice).expect("serialize pt err");
    });
    let file = File::create(&path).expect("create file err");
    let mut writer = BufWriter::new(file);
    writer.write_all(&buffer).expect("write buffer err");
    std::io::Write::flush(&mut writer).expect("flush err");
}

pub fn deserialize_affines_compressed_raw<P: SWCurveConfig>(path_prefix: &str) -> Vec<Affine<P>> {
    let path = format!("{}_compressed.data", path_prefix);
    let file = File::open(&path).expect("open file err");
    let file_size = file.metadata().expect("metadata err").len() as usize;
    if file_size == 0 { return vec![]; }
    let mut reader = BufReader::new(file);
    let mut buffer = vec![0u8; file_size];
    reader.read_exact(&mut buffer).expect("read file err");
    let dummy = Affine::<P>::zero();
    let point_size = dummy.serialized_size(Compress::Yes);
    assert_eq!(file_size % point_size, 0);
    let n = file_size / point_size;
    let mut v = vec![Affine::<P>::zero(); n];
    v.par_iter_mut().zip(buffer.par_chunks(point_size)).for_each(|(pt, chunk)| {
        let mut slice: &[u8] = chunk;
        *pt = Affine::<P>::deserialize_compressed_unchecked(&mut slice).expect("deserialize pt err");
    });
    v
}

pub fn serialize_affines_raw<P: SWCurveConfig>(v: &[Affine<P>], path_prefix: &str) {
    let zero = P::BaseField::zero();
    let n = v.len();
    let mut vx = vec![zero; n];
    let mut vy = vec![zero; n];
    let mut vb = vec![false; n];
    
    // Convert to uncompressed coordinates
    vx.par_iter_mut().zip(vy.par_iter_mut()).zip(vb.par_iter_mut()).zip(v.par_iter()).for_each(|(((vx_i, vy_i), vb_i), pt)| {
        if pt.is_zero() {
            *vx_i = zero;
            *vy_i = zero;
            *vb_i = true;
        } else {
            *vx_i = *pt.x().unwrap();
            *vy_i = *pt.y().unwrap();
            *vb_i = false;
        }
    });
    let path_vx = format!("{}_vx.data", path_prefix);
    let path_vy = format!("{}_vy.data", path_prefix);
    let path_vb = format!("{}_vb.data", path_prefix);

    let file = File::create(&path_vx).expect("create v_x err");
    let mut writer = BufWriter::new(file);
    vx.serialize_uncompressed(&mut writer).expect("serialize v_x err");

    let file = File::create(&path_vy).expect("create v_y err");
    let mut writer = BufWriter::new(file);
    vy.serialize_uncompressed(&mut writer).expect("serialize v_y err");
    
    let file = File::create(&path_vb).expect("create v_b err");
    let mut writer = BufWriter::new(file);
    vb.serialize_uncompressed(&mut writer).expect("serialize v_b err");
}

pub fn deserialize_affines_raw<P: SWCurveConfig>(path_prefix: &str) -> Vec<Affine<P>> {
    let path_vx = format!("{}_vx.data", path_prefix);
    let path_vy = format!("{}_vy.data", path_prefix);
    let path_vb = format!("{}_vb.data", path_prefix);

    let file_vx = File::open(&path_vx).expect("open v_x err");
    let mut reader_vx = BufReader::new(file_vx);
    let vx = Vec::<P::BaseField>::deserialize_uncompressed(&mut reader_vx).expect("deserialize v_x err");

    let file_vy = File::open(&path_vy).expect("open v_y err");
    let mut reader_vy = BufReader::new(file_vy);
    let vy = Vec::<P::BaseField>::deserialize_uncompressed(&mut reader_vy).expect("deserialize v_y err");

    let file_vb = File::open(&path_vb).expect("open v_b err");
    let mut reader_vb = BufReader::new(file_vb);
    let vb = Vec::<bool>::deserialize_uncompressed(&mut reader_vb).expect("deserialize v_b err");

    assert_eq!(vx.len(), vy.len());
    assert_eq!(vx.len(), vb.len());

    let mut v = vec![Affine::<P>::zero(); vx.len()];
    v.par_iter_mut().enumerate().for_each(|(i, pt)| {
        if vb[i] {
            *pt = Affine::<P>::zero();
        } else {
            *pt = Affine::<P>::new_unchecked(vx[i], vy[i]);
        }
    });

    v
}

pub fn write_g16_optimized_bn254(path: &Path, pk: &ark_groth16::ProvingKey<Bn254>, vk: &ark_groth16::VerifyingKey<Bn254>) {
	let mut gt1 = GTimer::new();
    let b_debug = B_DEBUG;
    let path_str = path.to_str().unwrap();

    let meta_path = format!("{}.meta", path_str);
    let file = File::create(&meta_path).expect("create meta err");
    let mut writer = BufWriter::new(file);
    vk.alpha_g1.serialize_compressed(&mut writer).expect("ser vk.alpha_g1");
    vk.beta_g2.serialize_compressed(&mut writer).expect("ser vk.beta_g2");
    vk.gamma_g2.serialize_compressed(&mut writer).expect("ser vk.gamma_g2");
    vk.delta_g2.serialize_compressed(&mut writer).expect("ser vk.delta_g2");
    
    pk.vk.alpha_g1.serialize_compressed(&mut writer).expect("ser pk.vk.alpha_g1");
    pk.beta_g1.serialize_compressed(&mut writer).expect("ser pk.beta_g1");
    pk.delta_g1.serialize_compressed(&mut writer).expect("ser pk.delta_g1");
    std::io::Write::flush(&mut writer).expect("flush err");

    drop(writer);
    serialize_affines_compressed_raw(&vk.gamma_abc_g1, &format!("{}_vk_gamma_abc_g1", path_str));
    serialize_affines_compressed_raw(&pk.a_query, &format!("{}_pk_a_query", path_str));
    serialize_affines_compressed_raw(&pk.b_g1_query, &format!("{}_pk_b_g1_query", path_str));
    serialize_affines_compressed_raw(&pk.b_g2_query, &format!("{}_pk_b_g2_query", path_str));
    serialize_affines_compressed_raw(&pk.h_query, &format!("{}_pk_h_query", path_str));
    serialize_affines_compressed_raw(&pk.l_query, &format!("{}_pk_l_query", path_str));

    // Calculate total size
    let mut total_size = metadata(&meta_path).map(|m| m.len()).unwrap_or(0);
    let prefixes = vec![
        format!("{}_vk_gamma_abc_g1", path_str),
        format!("{}_pk_a_query", path_str),
        format!("{}_pk_b_g1_query", path_str),
        format!("{}_pk_b_g2_query", path_str),
        format!("{}_pk_h_query", path_str),
        format!("{}_pk_l_query", path_str),
    ];
    for prefix in prefixes {
        total_size += metadata(&format!("{}_compressed.data", prefix)).map(|m| m.len()).unwrap_or(0);
    }
	let job_id = 0;
    log_perf(job_id, LOGL2, &format!("PERF 1003: [write_g16_optimized_bn254] path: {:?}, elements: {}, size: {} bytes", path, pk.a_query.len(), total_size),&mut gt1);

    if b_debug {
        let (pk_read, vk_read) = read_g16_optimized_bn254(path);
        assert_eq!(*pk, pk_read, "ProvingKey mismatch!");
        assert_eq!(*vk, vk_read, "VerifyingKey mismatch!");
        println!("Debug verification passed!");
    }
}

pub fn read_g16_optimized_bn254(path: &Path) -> (ark_groth16::ProvingKey<Bn254>, ark_groth16::VerifyingKey<Bn254>) {
	let mut gt1 = GTimer::new();
    let path_str = path.to_str().unwrap();

    let meta_path = format!("{}.meta", path_str);
    let file = File::open(&meta_path).expect("open meta err");
    let mut reader = BufReader::new(file);
    
    let vk_alpha_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser vk.alpha_g1");
    let vk_beta_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.beta_g2");
    let vk_gamma_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.gamma_g2");
    let vk_delta_g2 = <ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config>>::deserialize_compressed(&mut reader).expect("deser vk.delta_g2");
    
    let _pk_vk_alpha_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.vk.alpha_g1");
    let pk_beta_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.beta_g1");
    let pk_delta_g1 = <ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config>>::deserialize_compressed(&mut reader).expect("deser pk.delta_g1");

    let vk_gamma_abc_g1 = deserialize_affines_compressed_raw(&format!("{}_vk_gamma_abc_g1", path_str));
    let pk_a_query = deserialize_affines_compressed_raw(&format!("{}_pk_a_query", path_str));
    let pk_b_g1_query = deserialize_affines_compressed_raw(&format!("{}_pk_b_g1_query", path_str));
    let pk_b_g2_query = deserialize_affines_compressed_raw(&format!("{}_pk_b_g2_query", path_str));
    let pk_h_query = deserialize_affines_compressed_raw(&format!("{}_pk_h_query", path_str));
    let pk_l_query = deserialize_affines_compressed_raw(&format!("{}_pk_l_query", path_str));

    let vk = ark_groth16::VerifyingKey {
        alpha_g1: vk_alpha_g1,
        beta_g2: vk_beta_g2,
        gamma_g2: vk_gamma_g2,
        delta_g2: vk_delta_g2,
        gamma_abc_g1: vk_gamma_abc_g1,
    };

    let pk = ark_groth16::ProvingKey {
        vk: vk.clone(),
        beta_g1: pk_beta_g1,
        delta_g1: pk_delta_g1,
        a_query: pk_a_query,
        b_g1_query: pk_b_g1_query,
        b_g2_query: pk_b_g2_query,
        h_query: pk_h_query,
        l_query: pk_l_query,
    };

    // Calculate total size
    let mut total_size = metadata(&meta_path).map(|m| m.len()).unwrap_or(0);
    let prefixes = vec![
        format!("{}_vk_gamma_abc_g1", path_str),
        format!("{}_pk_a_query", path_str),
        format!("{}_pk_b_g1_query", path_str),
        format!("{}_pk_b_g2_query", path_str),
        format!("{}_pk_h_query", path_str),
        format!("{}_pk_l_query", path_str),
    ];
    for prefix in prefixes {
        total_size += metadata(&format!("{}_compressed.data", prefix)).map(|m| m.len()).unwrap_or(0);
    }
	let job_id = 0;
    log_perf(job_id, LOGL2, &format!("PERF 1003: [read_g16_optimized_bn254] path: {:?}, elements: {}, size: {} bytes", path, pk.a_query.len(), total_size, 
	), &mut gt1);

    (pk, vk)
}

// --- Added for R1CS serialization and diagnostics ---
use crate::arith::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

pub fn save_r1cs<F: PrimeField>(r1cs: &R1CS<F>, filepath: &str) -> Result<(), std::io::Error> {
	let path = Path::new(filepath);
	if let Some(parent) = path.parent() {
		std::fs::create_dir_all(parent)?;
	}
    let mut file = File::create(path)?;
    r1cs.serialize_uncompressed(&mut file)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    Ok(())
}

/// Deserializes an R1CS instance from a binary file
pub fn load_r1cs<F: PrimeField>(filepath: &str) -> Result<R1CS<F>, std::io::Error> {
    let mut file = File::open(Path::new(filepath))?;
    let r1cs = R1CS::<F>::deserialize_uncompressed(&mut file)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    Ok(r1cs)
}

/// Compares two R1CS instances and prints the differences
pub fn compare_r1cs<F: PrimeField>(name: &str, current: &R1CS<F>, loaded: &R1CS<F>) -> bool {
    if current == loaded {
        println!("[SUCCESS] {} R1CS instances are EXACTLY identical!", name);
        return true;
    }
    
    println!("[WARNING] {} R1CS instances DIFFER. Finding mismatch...", name);
    
    if current.l != loaded.l {
        println!("  -> 'l' (io len) differs: current={} vs loaded={}", current.l, loaded.l);
    }
    
    let mut diff_found = false;
    diff_found |= !compare_sparse_matrices(format!("{}-A", name), &current.A, &loaded.A);
    diff_found |= !compare_sparse_matrices(format!("{}-B", name), &current.B, &loaded.B);
    diff_found |= !compare_sparse_matrices(format!("{}-C", name), &current.C, &loaded.C);
	
	!diff_found
}

fn compare_sparse_matrices<F: PrimeField>(mat_name: String, m1: &SparseMatrix<F>, m2: &SparseMatrix<F>) -> bool {
    if m1.n_rows != m2.n_rows || m1.n_cols != m2.n_cols {
        println!("  -> Matrix {} dimensions differ: current({}x{}) vs loaded({}x{})", 
                 mat_name, m1.n_rows, m1.n_cols, m2.n_rows, m2.n_cols);
		return false;
    }
    
	let mut diff_count = 0;
    for row_idx in 0..m1.n_rows {
        let row1 = &m1.coeffs[row_idx];
        let row2 = &m2.coeffs[row_idx];
        
        if row1 != row2 {
			diff_count += 1;
			if diff_count > 10 {
				println!("  -> Matrix {}: ... more than 10 rows differ, stopping report.", mat_name);
				return false;
			}

            if row1.len() != row2.len() {
                println!("  -> Matrix {} Row {} length differs: current({}) vs loaded({})", 
                         mat_name, row_idx, row1.len(), row2.len());
            } else {
                println!("  -> Matrix {} Row {} contents differ!", mat_name, row_idx);
                
                // Check if it's just an ordering issue
                let mut row1_sorted = row1.clone();
                let mut row2_sorted = row2.clone();
                row1_sorted.sort_by(|a, b| a.1.cmp(&b.1)); // Sort by column index
                row2_sorted.sort_by(|a, b| a.1.cmp(&b.1));
                
                if row1_sorted == row2_sorted {
                    println!("     Note: Row {} elements are mathematically SAME, but physical ORDER shifted.", row_idx);
                } else {
					println!("     Note: Row {} is mathematically DIFFERENT.", row_idx);
					println!("     Current (first 5): {:?}", &row1[..std::cmp::min(5, row1.len())]);
					println!("     Loaded  (first 5): {:?}", &row2[..std::cmp::min(5, row2.len())]);
				}
            }
        }
    }
    diff_count == 0
}

// --- Added: sidecar save/load for circuit-constant data
// (Pedersen params + R1CS topology hash) ---
use ark_ec::CurveGroup;
use crate::commitment::pedersen::Params as PedersenParams;

/// SHA-256 of the canonical-uncompressed R1CS serialization.
/// Used to verify that a freshly-built R1CS matches the one that
/// produced a saved Groth16 key.
pub fn hash_r1cs<F: PrimeField>(r1cs: &R1CS<F>) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut bytes = Vec::new();
    r1cs.serialize_uncompressed(&mut bytes)
        .expect("ser r1cs for hash");
    let digest = Sha256::digest(&bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Write a PedersenParams<C> to disk at `prefix`:
///   <prefix>_h.meta             — single affine (compressed CanonicalSerialize)
///   <prefix>_generators_compressed.data — via serialize_affines_compressed_raw
pub fn write_pedersen_params<C>(prefix: &Path, pp: &PedersenParams<C>)
where
    C: CurveGroup<Affine = Affine<<C as CurveGroup>::Config>>,
    C::Config: SWCurveConfig,
{
    let prefix_str = prefix.to_str().expect("prefix str");
    let h_path = format!("{}_h.meta", prefix_str);
    let file = File::create(&h_path).expect("create h meta err");
    let mut writer = BufWriter::new(file);
    let h_aff: Affine<C::Config> = pp.h.into_affine();
    h_aff.serialize_compressed(&mut writer).expect("ser h err");
    std::io::Write::flush(&mut writer).expect("flush h err");
    drop(writer);

    serialize_affines_compressed_raw::<C::Config>(
        &pp.generators,
        &format!("{}_generators", prefix_str),
    );
}

/// Inverse of write_pedersen_params.
pub fn read_pedersen_params<C>(prefix: &Path) -> PedersenParams<C>
where
    C: CurveGroup<Affine = Affine<<C as CurveGroup>::Config>>,
    C::Config: SWCurveConfig,
{
    let prefix_str = prefix.to_str().expect("prefix str");
    let h_path = format!("{}_h.meta", prefix_str);
    let file = File::open(&h_path).expect("open h meta err");
    let mut reader = BufReader::new(file);
    let h_aff = Affine::<C::Config>::deserialize_compressed(&mut reader)
        .expect("deser h err");
    let h: C = h_aff.into();

    let generators = deserialize_affines_compressed_raw::<C::Config>(
        &format!("{}_generators", prefix_str),
    );
    PedersenParams { h, generators }
}
