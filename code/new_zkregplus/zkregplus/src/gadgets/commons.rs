/* Created 03/07/2025 */
// common utility functions
use utils::{consts::ADD_CHAIN_SIZE,logger::{log_perf,LOG2}, timer::Timer};
use rayon::{
	iter::{ParallelIterator,IntoParallelIterator, 
		IntoParallelRefIterator,IndexedParallelIterator, IntoParallelRefMutIterator},
	//prelude::{ParallelSliceMut}
};
use folding_schemes::{Error};
use crate::gadgets::traits::{Container,Col,IDX_DATA,IDX_SI_DATA};
use std::{collections::{HashMap,HashSet}, rc::{Rc}, cell::{RefCell}};
use ark_ff::{PrimeField,BigInteger};
use ark_relations::{
	lc, 
	r1cs::{ SynthesisError,ConstraintSystemRef,LinearCombination,Variable }
};
use ark_r1cs_std::{
	boolean::{Boolean},
	fields::{
		FieldVar,
		fp::FpVar,
		fp::AllocatedFp,
	 	fp::FpVar::Var,
	 	fp::FpVar::Constant,
	},
	alloc::AllocVar,
	eq::EqGadget,
	R1CSVar,
};
use data_processor::clam_db::{RANGE2_BIT,RANGE2};

pub fn print_vec<F:PrimeField>(msg: &str, v: &Vec<F>){
	println!("=== {} ====", msg);
	for i in 0..v.len(){ println!("  {} => {}", i, v[i]); }
}

/// quickly generate repeating of vec for n times.
pub fn repeat_vec<F:PrimeField>(v: &[FpVar<F>], n: usize)->Vec<FpVar<F>>{
	let (_vlen,total) = (v.len(), v.len()*n);
	let zero = FpVar::<F>::zero();
    let mut result = vec![zero; total];
	let v_len = v.len();
	for i in 0..n{//unfortunately FpVar does not support send,
		//so cannot do parallel assignmen here.
		for j in 0..v_len{
			result[i*v_len+j] = v[j].clone();
		}
	}

    result
}

/// takeing a vector of slices of the same size and interleaving
/// these into one vec, e.g., [[1,2], [3,4]] ==> [1,3,2,4]
pub fn mix_vec<F:PrimeField>(v2d: &Vec<&[F]>)->Vec<F>{
	let m = v2d.len();
	let n = v2d[0].len();
	for v in v2d {assert!(v.len()==n);}
	let zero = F::zero();
	let mut result = vec![zero; m*n];
	result.par_iter_mut().enumerate().for_each(|(i,ele)|{
		let (col_id, loc) = (i%m, i/m);
		*ele = v2d[col_id][loc]
	});

	result
}

pub fn is_sorted<F:PrimeField>(vec: &Vec<F>)->bool{
	if vec.len()==0 {return true;}
	for i in 0..vec.len()-1{ if vec[i]>vec[i+1] {return false;} }
	true
}

pub fn is_incrementing_by_one<F:PrimeField>(vec: &Vec<F>)->bool{
	if vec.len()<1 {return true;}
	for i in 0..vec.len()-1{ if vec[i+1] != vec[i] + F::one() {return false;} }
	true
}

/// create a vec of var
pub fn vec_to_var<F:PrimeField>(cs: &ConstraintSystemRef<F>, v: &Vec<F>)
->Vec<FpVar<F>>{
	v.iter().map(|x| FpVar::new_witness(cs.clone(), 
		|| Ok(x.clone())).unwrap() ).collect()
}

/// if sid[i] is rg2 check data[i] is in range2
#[allow(dead_code)]
pub fn check_rg2<F:PrimeField>(data: &Vec<F>,sid: &Vec<F>){
	let frg = F::from(RANGE2);
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u64);
	assert!(data.len()==sid.len());
	for i in 0..data.len(){
		if sid[i]==frg {assert!(data[i]<max);}
	}
}

/// create  a new var
pub fn new_var<F:PrimeField>(cs: &ConstraintSystemRef<F>, v: F)->FpVar<F>{
	FpVar::new_witness(cs.clone(), || Ok(v)).expect("err new var")
}

/// create  a new constant var
pub fn new_const_var<F:PrimeField>(cs: &ConstraintSystemRef<F>, v: F)
->FpVar<F>{
	FpVar::new_constant(cs.clone(), v).expect("err new var")
}

/// assuming each val is within RANGE2. basically concat as bits.
pub fn encode_2col_var<F:PrimeField>(c1: &[FpVar<F>], c2: &[FpVar<F>]
)->Vec<FpVar<F>>{
	let cs = c1[0].cs();
	let factor = new_const_var(&cs, F::from(1u32<<RANGE2_BIT));	
	assert!(c1.len()==c2.len());
	let res = c1.iter().zip(c2.iter()).map(|(x,y)|
		x + (y*&factor)).collect::<Vec<FpVar<F>>>();

	res
}

/// use random r to combine.
pub fn encode_2col_var_adv<F:PrimeField>(c1: &[FpVar<F>], c2: &[FpVar<F>], r: &FpVar<F>)->Vec<FpVar<F>>{
	let factor = r.clone();
	assert!(c1.len()==c2.len());
	let res = c1.iter().zip(c2.iter()).map(|(x,y)|
		x + (y*&factor)).collect::<Vec<FpVar<F>>>();

	res
}

/// encode 2 column into one encoded column
pub fn encode_2col<F:PrimeField>(c1: &[F], c2: &[F]
)->Vec<F>{
	let factor = F::from(1u32<<RANGE2_BIT);	
	assert!(c1.len()==c2.len());
	let res = c1.par_iter().zip(c2.par_iter()).map(|(x,y)|
		*x + (*y*factor)).collect::<Vec<F>>();

	res
}
/// encode multiple columns, this can be regarded as an
/// extension of encode_2col. Assume each column field is within RANGE2
/// better version take slces
pub fn encode_cols_better<F:PrimeField>(cols: Vec<&[F]>, col_ids: Vec<usize>)
	->Vec<F>{
	//1. prepare data
	let (num_cols, n) = (col_ids.len(), cols[col_ids[0]].len());
	let factor = F::from(1u32<<RANGE2_BIT);	
	let mut coefs = vec![F::one(); num_cols];
	for i in 1..coefs.len() {coefs[i] = coefs[i-1] * factor;}
	coefs.reverse();

	//2. generate the data
	#[cfg(test)] { for i in 0..num_cols {assert!(cols[col_ids[i]].len()==n);} }
	let zero = F::zero();
	let res = (0..n).into_par_iter().map(|i|{
		let mut res = zero;
		for col in 0..num_cols{
			res += cols[col_ids[col]][i] * coefs[col];
		}
		res
	}).collect::<Vec<F>>();
	assert!(res.len()==n);

	res
}

/// encode multiple columns, this can be regarded as an
/// extension of encode_2col. Assume each column field is within RANGE2
pub fn encode_cols<F:PrimeField>(cols: &Vec<Vec<F>>, col_ids: &Vec<usize>)
	->Vec<F>{
	//1. prepare data
	let (num_cols, n) = (col_ids.len(), cols[col_ids[0]].len());
	let factor = F::from(1u32<<RANGE2_BIT);	
	let mut coefs = vec![F::one(); num_cols];
	for i in 1..coefs.len() {coefs[i] = coefs[i-1] * factor;}
	coefs.reverse();

	//2. generate the data
	#[cfg(test)] { for i in 0..num_cols {assert!(cols[col_ids[i]].len()==n);} }
	let zero = F::zero();
	let res = (0..n).into_par_iter().map(|i|{
		let mut res = zero;
		for col in 0..num_cols{
			res += cols[col_ids[col]][i] * coefs[col];
		}
		res
	}).collect::<Vec<F>>();
	assert!(res.len()==n);

	res
}

/// reverse of encode_cols
pub fn decode_cols<F:PrimeField>(vec: &Vec<F>, n: usize)->Vec<Vec<F>>{
	let tuples = vec.par_iter().map(|v| {
		let bits:Vec<bool> = v.into_bigint().to_bits_le();
		let chunks = bits.chunks(RANGE2_BIT).map(|v|{
			let bi: F::BigInt= BigInteger::from_bits_le(v);
			F::from(bi)
		}).collect::<Vec<F>>();
		let res = chunks[0..n].to_vec();
		res
	}).collect::<Vec<Vec<F>>>();

	let res = (0..n).collect::<Vec<_>>().into_par_iter().map(|i|{
		tuples.par_iter().map(|t| t[n-1-i]).collect::<Vec<F>>()
	}).collect::<Vec<Vec<F>>>();

	#[cfg(test)]{
		let ids = (0..n).collect::<Vec<usize>>();
		let encoded = encode_cols(&res, &ids);
		assert!(encoded == *vec);
	}

	res
}

/// encode multiple columns, this can be regarded as an
/// extension of encode_2col. Assume each column field is within RANGE2
pub fn encode_cols_var<F:PrimeField>(cols: &Vec<Vec<FpVar<F>>>, 
	col_ids: &Vec<usize>) ->Vec<FpVar<F>>{
	let cs = cols[0][0].cs();
	let factor =new_const_var(&cs,F::from(1u32<<RANGE2_BIT));	
	encode_cols_var_adv(cols, col_ids, &factor)
}

/// verify the target_col isthe reslt of encoding cols using
/// RANGE2 powers as factor. Here we assume that
/// all col cells are in RANGE2 (which is usually verified
/// by corresponding column in IDX_SI_DATA segement).
///
/// COST: n where n is the target_col_len
pub fn verify_encode_cols_in_range<F:PrimeField>(target_col: &[FpVar<F>],
	cols: &[&[FpVar<F>]]) -> Result<(),SynthesisError>{
	//1. build the factor array for use
	let b_perf = false;
	let b_debug = false;
	let mut gt = Timer::new();
	assert!(target_col.len()>0);
	let cs = target_col[0].cs();
	let nc = cs.num_constraints();
	let factor = F::from(1u32<<RANGE2_BIT);	
	let logl = LOG2;
	let num_cols = cols.len();
	let mut coefs = vec![F::one(); num_cols];
	for i in 1..coefs.len() {coefs[i] = coefs[i-1] * factor;}
	coefs.reverse();

	//2. encode the check
	let n = target_col.len();
	for col in cols{assert!(col.len()==n);}
	let lb_one = LinearCombination::from((F::one(),Variable::One));
	let mut vec2 = vec![(F::one(), Variable::One); num_cols];
	for i in 0..n{
		//2.1 assert that target[i] = weighted sum of cols[j][i]
		let lb_target = var_to_lb(&target_col[i], F::one());
		let mut sum = F::zero();
		for j in 0..num_cols{
			vec2[j] = var_to_tuple_adv(&cols[j][i], coefs[j]);
			sum += coefs[j] * cols[j][i].value()?;

		}
		let lb_res = LinearCombination::<F>(vec2.clone());
		cs.enforce_constraint(
			lb_target,
			lb_one.clone(),
			lb_res
		)?;
	}
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	if b_perf {
		log_perf(logl, &format!("assert_encode_cols_in_range. n: {}, cs: {}",
			n, cs.num_constraints()-nc), &mut gt);
	}

	Ok( () )
}
/// advanced vesion using the given r as combining factor, better
///version that allows slice
pub fn encode_cols_var_adv_better<F:PrimeField>(cols: &Vec<&[FpVar<F>]>, 
	col_ids: &Vec<usize>, r: &FpVar<F>) ->Vec<FpVar<F>>{
	//1. prepare data
	let cs = cols[0][0].cs();
	let (num_cols, n) = (col_ids.len(), cols[col_ids[0]].len());
	let factor = r.clone();
	let one = new_const_var(&cs, F::one());
	let mut coefs = vec![one; num_cols];
	for i in 1..coefs.len() {coefs[i] = &coefs[i-1] * &factor;}
	coefs.reverse();

	//2. generate the data
	#[cfg(test)] { for i in 0..num_cols {assert!(cols[col_ids[i]].len()==n);} }
	let zero = new_var(&cs, F::zero());
	let res = (0..n).into_iter().map(|i|{
		let mut res = zero.clone();
		for col in 0..num_cols{
			let item = if col<num_cols-1 {&cols[col_ids[col]][i] * &coefs[col]}
				else {cols[col_ids[col]][i].clone()};
			res = &res + &item;
		}
		res
	}).collect::<Vec<FpVar<F>>>();
	assert!(res.len()==n);

	res
}

/// advanced vesion using the given r as combining factor
pub fn encode_cols_var_adv<F:PrimeField>(cols: &Vec<Vec<FpVar<F>>>, 
	col_ids: &Vec<usize>, r: &FpVar<F>) ->Vec<FpVar<F>>{
	//1. prepare data
	let cs = cols[0][0].cs();
	let (num_cols, n) = (col_ids.len(), cols[col_ids[0]].len());
	let factor = r.clone();
	let one = new_const_var(&cs, F::one());
	let mut coefs = vec![one; num_cols];
	for i in 1..coefs.len() {coefs[i] = &coefs[i-1] * &factor;}
	coefs.reverse();

	//2. generate the data
	#[cfg(test)] { for i in 0..num_cols {assert!(cols[col_ids[i]].len()==n);} }
	let zero = new_var(&cs, F::zero());
	let res = (0..n).into_iter().map(|i|{
		let mut res = zero.clone();
		for col in 0..num_cols{
			let item = if col<num_cols-1 {&cols[col_ids[col]][i] * &coefs[col]}
				else {cols[col_ids[col]][i].clone()};
			res = &res + &item;
		}
		res
	}).collect::<Vec<FpVar<F>>>();
	assert!(res.len()==n);

	res
}

/// given n length F generating the difference col (length n-1)
/// the diff value is the ABSOLUTE value
pub fn gen_abs_diff_col<F:PrimeField>(col: &Vec<F>)->Vec<F>{
	let zero = F::zero();
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	//let f_rg= F::from(RANGE2);
	let col = (1..col.len()).collect::<Vec<usize>>().into_par_iter().map(|i|{
		let diff = col[i] - col[i-1];
		let diff = if diff<=max {diff} else {zero-diff};
		diff	
	}).collect::<Vec<F>>();

	col
}

/// Generate a SID column for a diff col, so that it can be used
/// in assert_wellformedness. Note that we could actually generate
/// a boolean vec, but to be compatible with the legacy code of
/// assert_well_formed_ness, we are generating
/// 0 - key[i]>key[i+1]
/// frg2 - key[i]<=key[i+1
/// the resulting length is n-1. Note that it reflects the "sid"
/// for (key[i+1]-key[i])_{i=0}^{n-1}
/// this function also asserts that it is consistent with the
/// value of abs_diff column (that is when it's value is
/// 0 - key[i] = key[i+1] + abs_diff[i].
/// otherwise key[i+1] = key[i] + abs_diff[i]
/// Here abs_diff[i] EARLIER has been proved to be all in RANGE2.
///
/// COST: 2n
pub fn gen_assert_sidcol_for_diff<F:PrimeField>(key: &Vec<FpVar<F>>,
	diff: &Vec<FpVar<F>>)
-> Vec<FpVar<F>>{
	//1. generate the return
	let b_perf = false;
	let cs = diff[0].cs();
	let nc = cs.num_constraints();
	let (zero, frg) = (F::zero(), F::from(RANGE2 as u32));
	let vals = (0..key.len()-1).collect::<Vec<_>>().iter().map(|&i|{
		if key[i].value().unwrap() >key[i+1].value().unwrap()
			{zero} else {frg}
	}).collect::<Vec<F>>();
	let res = vals.iter().map(|&x|
		new_var(&cs, x)
	).collect::<Vec<FpVar<F>>>();

	//2. (a) res is "boolean" i.e. res * (res - rg2) = 0
	//(b) assert res is valid
	//when res = 0, key[i+1] + diff[i] = key[i]
	// when res * inv_rg2 = 1, key[i] + diff[i] = key[i+1]
	// so we have:
	// res * (key[i+1] - diff[i] - key[i]) + 
	// (1-res * inv_rg2)* (key[i] - diff[i] - key[i+1]) = 0
	// i.e.,
	// res * ((key[i+1](1+inv_rg2)+diff[i](inv_rg2-1) -key[i](inv_rg2+1)))
	// = key[i+1] + diff[i] - key[i] 
	let n = res.len();
	let lb_zero= lc!();
	let const_rg2 = new_const_var(&cs, F::from(RANGE2));
	let rg2 = F::from(RANGE2);
	let val_rg_plus_1 = rg2.inverse().unwrap() + F::one();
	let val_rg_minus_1 = rg2.inverse().unwrap() - F::one();

	let minus_rg2 = var_to_lb(&const_rg2, -F::one());
	for i in 0..n{
		let lb_res = var_to_lb(&res[i], F::one());
		cs.enforce_constraint(
			lb_res.clone(),
			lb_res.clone() + minus_rg2.clone(),
			lb_zero.clone()
		).unwrap();

		let minus_key = var_to_lb(&key[i], -F::one());
		let key_1 = var_to_lb(&key[i+1], F::one());
		let lb_diff = var_to_lb(&diff[i], F::one());
		cs.enforce_constraint(
			lb_res,
			key_1.clone()*val_rg_plus_1 + 
				lb_diff.clone() * val_rg_minus_1 + 
				minus_key.clone()*val_rg_plus_1,
			key_1 + lb_diff + minus_key
		).unwrap();
	}

	if b_perf{
		println!(" ### gen_assert_sidcol_for_diff: n: {}, cs: {}",
			n, cs.num_constraints() - nc);
	}

	res
}


/* REMOVE LATER
/// given n length F generating the difference col (length n-1)
/// and its SID
pub fn gen_diff_col<F:PrimeField>(col: &Vec<F>)->(Vec<F>,Vec<F>){
	let zero = F::zero();
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let f_rg= F::from(RANGE2);
	let tuples = (1..col.len()).collect::<Vec<usize>>().into_par_iter().map(|i|{
		let diff = col[i] - col[i-1];
		let sid = if diff<=max {f_rg} else {zero};

		(diff, sid)
	}).collect::<Vec<(F,F)>>();

	let col_diff = tuples.par_iter().map(|t| t.0).collect::<Vec<F>>();
	let col_sid = tuples.par_iter().map(|t| t.1).collect::<Vec<F>>();
	assert!(col_diff.len()==col.len()-1 && col_diff.len()==col_sid.len());

	(col_diff, col_sid)
}
*/

/// given two cols of the same size, construct and map key to a collection
/// of values.
/// NOTE: we ignore 0 and max entries in vec1
/// e.g.,
/// given vec1 = [100, 200, 100, 300, 0, max], vec2 = [1,2,3,4, 200, 300];
/// we return [100->[1,3], 200->[2], 300->[4]] where 0 and max do not
/// show up in key col
pub fn two_col_to_hashmap<F:PrimeField>(
	col1: &Vec<F>, col2: &Vec<F>
)->HashMap<F,Vec<F>>{
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	assert!(col1.len()==col2.len());
	let hs:HashMap<F, Vec<F>> = col1.par_iter().zip(col2.par_iter())
	.filter(|(a,b)| !a.is_zero() && !b.is_zero() && **a!=max && **b!=max)
	.fold( || HashMap::<F, Vec<F>>::new(),
		|mut acc, (k,v)|{
			acc.entry(*k).or_insert(vec![]).append(&mut vec![*v]);
			acc
	}).reduce(|| HashMap::<F,Vec<F>>::new(),
		|mut acc1, acc2| {
			for (k, mut vec) in acc2{
				let mut vec1 = if acc1.contains_key(&k) 
					{acc1.get(&k).unwrap().clone()} else {vec![]};
				vec1.append(&mut vec);
				let hs1=vec1.into_iter().map(|x| x).collect::<HashSet<_>>();
				let mut v2= hs1.into_iter().map(|x| x).collect::<Vec<_>>(); 
				v2.sort();
				acc1.insert(k, v2);
			}
			acc1
		}
	);

	hs
}

/// Convert two col table to first compress all entries (no duplicates),
/// and then to well formed and sorted on both keys and vals
/// of tbl structure (key, id, val). Note that 0/max entries 
/// (any cell value zero)
/// are removed.
/// Return the key, id, val column.
///
/// might throw CapErr("target_size");
pub fn two_col_tbl_to_sorted<F: PrimeField>(col1: &Vec<F>, col2: &Vec<F>, target_size: usize)-> Result<(Vec<F>,Vec<F>,Vec<F>), Error>{
	//1. collect a hash map which maps from key to a vector of vals sorted.
	let hs = two_col_to_hashmap(col1, col2);

	//2. call hashmap_to_sorted_2col_table 
	hashmap_to_sorted_2col_tbl(&hs, target_size)
}

///Construct a wide-wellformed table, which has the structure
///   column key-val-id-count
///where id starts from 0 and count is the real count -1
///NOTE that it's light weighted. We do not gurantee
///that key or val is sorted. The table is padded
///by a real (1-row) key-0 entries which are also well formed.
///.e.g,
/// key - val - id - count
/// 0     0     0      0   (1-record entry)
/// 0     0     0      0   (there can be multile entries)
/// 1    10     0      3
/// 1      5     1     3  (note not necessarily val is osrted
/// 1     20     2     3  (last entry) 
/// HERE the well-formed means that the id for a key starts
/// from 0 and ends at count-1. This is useful when we
/// deal with table join. Compared with the "deep" well-formed
/// table using 0-max to wrap value columns, it is
/// SHORTER with the cost of more columns.
/// NOTE: the table ITSELF does NOT forbid a key (with a different block)
/// When we use it to construt state-pat, the "unique" key-block
/// relation is guaranteed by the external lookup table. but here we
/// do construct unique keys except padding 0-entries.
pub fn two_col_to_wide_wellformed<F:PrimeField>(
	col1: &Vec<F>, col2: &Vec<F>, target_size: usize, name: &str
)->Result<Rc<RefCell<Container<F>>>,Error>{
	//1. collect a hash map which maps from key to a vector of vals sorted.
	let hs = two_col_to_hashmap(col1, col2);

	//2. call hashmap_to_sorted_2col_table 
	hashmap_to_wide_wellformed(&hs, target_size, name)
}


/// assuming tbl1 and tbl2 are both well formed two column table with
/// structure (key, id, val). Produce the table needed of structure
/// (k1, id1, k2, id2, val) where val of tbl1 serves as the forieng key.
///
/// Might throw CapErr("target_size")
pub fn two_col_tbl_left_join<F:PrimeField>(
	tbl1: &Vec<Vec<F>>, 
	tbl2: &Vec<Vec<F>>, 
	target_size: usize
) -> Result<Vec<Vec<F>>,Error>{
	//1. data check
	#[cfg(test)]{
		assert_wellformed_sorted_two_col_tbl(tbl1);
		assert_wellformed_sorted_two_col_tbl(tbl2);
	}
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let (zero, one, max) = (F::zero(), F::one(), F::from(max_val as u32));

	//2. build a hashmap of tbl2. map from real key to (begin,end) included
	// on both ends. keys are never zero.
	let n = tbl2[0].len();
	let mut hs = HashMap::<F, (usize,usize)>::new();
	let mut key = F::zero();
	let mut start = 0usize;
	let mut found_one = false;
	for i in 0..n{
		if (i>0 && tbl2[0][i]!=tbl2[0][i-1]) ||  //new key starts
			(tbl2[0][i]!=zero && i==0) ||  //real key starts from row 0
			i==n-1 //last row
		{
			//found new entry or need to update last
			//2.1 insert for the last entry
			if found_one{
				assert!(!hs.contains_key(&key));
				//the assumption is that at the very last idx,
				//there couldn't be two MAX entries.
				let end = if i==n-1 {i} else {i-1}; 
				assert!(key!=zero);
				hs.insert(key, (start, end));
			}
			found_one = true;
			key = tbl2[0][i];
			start = i;
		}
	}

	//3. expand each entry of tbl1.
	let n1 = tbl1[0].len();
	let tuples = (0..n1).collect::<Vec<usize>>().into_par_iter()
	.filter(|i| tbl1[0][*i]!=zero && tbl1[0][*i]!=max)
	.map(|i|{
		//3.1 get the result
		let (key, id, key2) = (tbl1[0][i], tbl1[1][i], tbl1[2][i]);
		let t1 = hs.get(&key2);
		let to_rep = if t1.is_some() {
			let t1 = *t1.unwrap();
			(t1.0..(t1.1+1)).collect::<Vec<usize>>()
				.into_iter().map(|j| tbl2[2][j])
				.collect::<Vec<F>>()
		}else{vec![]};

		//3.2 build table
		let mut res = vec![];
		let tn = to_rep.len();
		let b_empty = to_rep.len()==0;
		if b_empty{
			res.push( vec![key, id, key2, zero, zero]);
			res.push( vec![key,id,key2, one, max]); 
		}else{
			for id2 in 0..tn{
				res.push(vec![key,id,key2,F::from(id2 as u32), to_rep[id2]]);
			}
		}

		res
	}).flatten().collect::<Vec<Vec<F>>>();


	//4. pad at the beginning
	let tn = tuples.len();
	if tn>target_size{
		return Err(
			Error::CapErr(vec![(format!("target_size::2col_left_join"), 
			tn
		)]));
	}
	assert!(tn<=target_size, "tn: {}, target_size: {}. Consider adjust related capacity parameter", tn, target_size);
	let to_pad = vec![zero; target_size - tuples.len()];
	let res = (0..5).collect::<Vec<usize>>().into_iter().map(|i|{
		let col = (0..tn).into_par_iter().map(|j| 
			tuples[j][i]
		).collect::<Vec<F>>();
		vec![to_pad.clone(), col].concat()
	}).collect::<Vec<Vec<F>>>();
	assert!(res.len()==5);

	Ok( res )
}

/// build vec of 8 elements [2^31, ... 2^248]
pub fn build_pows_31<F:PrimeField>(cs: ConstraintSystemRef<F>)
-> Vec<FpVar<F>>{
	let f16 = new_const_var(&cs, F::from(1u32<<16));
	let f15 = new_const_var(&cs, F::from(1u32<<15));
	let f31 = &f16 * &f15;
	let mut vec = vec![];
	let mut item = f31.clone();
	for _i in 0..8{
		vec.push(item.clone());
		item = &item * &f31;
	}

	vec
}

/// build vec of 8 elements [2^31, ... 2^248]
pub fn build_pows_31_val<F:PrimeField>() -> Vec<F>{
	let f16 = F::from(1u32<<16);
	let f15 = F::from(1u32<<15);
	let f31 = f16 * f15;
	let mut vec = vec![];
	let mut item = f31.clone();
	for _i in 0..8{
		vec.push(item.clone());
		item = item * f31;
	}

	vec
}

/// build vec of 4 elements [2^56, ... 2^(56*4)]
pub fn build_pows_56<F:PrimeField>(cs: ConstraintSystemRef<F>)
-> Vec<FpVar<F>>{
	let f16 = new_const_var(&cs, F::from(1u32<<16));
	let f6= new_const_var(&cs, F::from(1u32<<6));
	let f56 = &f16 * &f16 * &f16 * &f16 * &f6;
	let mut vec = vec![];
	let mut item = f56.clone();
	for _i in 0..4{
		vec.push(item.clone());
		item = &item * &f56;
	}

	vec
}

/// build vec of 4 elements [2^56, ... 2^(56*4)]
pub fn build_pows_56_val<F:PrimeField>() -> Vec<F>{
	let f16 = F::from(1u32<<16);
	let f6= F::from(1u32<<6);
	let f56 = f16 * f16 * f16 * f16 * f6;
	let mut vec = vec![];
	let mut item = f56.clone();
	for _i in 0..4{
		vec.push(item);
		item = item * f56;
	}

	vec
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

#[inline(always)]
pub fn var_to_variable<F:PrimeField>(v: &FpVar<F>)->Variable{
	let res = match v{
		Var(v) => v.variable,
		Constant(_) => panic!("var is contsntat")
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


///compute sum (v[i] * weights[i]) where weights as consants
/// we assume that v and weights are small
/// so do not use parallelism here
#[inline(always)]
pub fn sum_vec_vars_weighted<F:PrimeField>(v: &[FpVar<F>], weights: &[F])
->FpVar<F>{
	assert!(v.len()==weights.len());
	let vec_tuples = v.iter().zip(weights.iter()).map(|(x,&w)|
		var_to_tuple_adv(x, w)
	).collect::<Vec<(F,Variable)>>();
	let v_sum= v.iter().zip(weights.iter()).map(|(x,&w)|
		x.value().unwrap() * w
	).sum::<F>();
	let lb = LinearCombination::<F>(vec_tuples);
	let cs = v[0].cs();
	let var = cs.new_lc(lb).unwrap();
	let alloc_var = AllocatedFp::new(Some(v_sum), var, cs.clone());
	FpVar::Var(alloc_var)
}


/// pack the check of 8 values into one check
/// assuming that each element of vec is ALREADY IN RANGE 31-BIT
/// COST is vec.len()/8
/// ASSUMING vec_pows_31 has 8 elements [2^31, 2^62, 2^93 ..., 2^248]
pub fn packcheck_vec<F:PrimeField>(vec: &Vec<FpVar<F>>, exp_val: &FpVar<F>,
	pows_31: &Vec<F>)
->Result<(),SynthesisError>{
	assert!(pows_31.len()==8);
	//let cs = vec[0].cs();
	//let c1 = new_const_var(&cs, F::one());
	assert!(pows_31.len()==8);
	//for i in 0..8{ total_exp = &total_exp + &(exp_val * &pows_31[i]); }
	let vec_exp_val = vec![exp_val.clone(); 8];
	let total_exp = sum_vec_vars_weighted(&vec_exp_val[..], &pows_31);

	for i in 0..vec.len()/8{//note mul with const does not cost
		//let mut total_var = c1.clone();
		//for j in 0..8{ total_var = &total_var + &(&vec[i*8 + j]*&pows_31[j]); }
		let total_var = sum_vec_vars_weighted(&vec[i*8..(i+1)*8], &pows_31); 
		check_eq(&total_var, &total_exp, "failed vec check")?;
	}
	//check the remaining
	let start = vec.len()/8 * 8;
	for i in start..vec.len(){
		check_eq(&vec[i], exp_val, "failed vec check part 2")?;
	}
	Ok( () )
}



/// assert that the table is sorted in keys and values (per key)
pub fn assert_wellformed_sorted_two_col_tbl<F:PrimeField>(tbl: &Vec<Vec<F>>){
	assert_wellformed_sorted_two_col_tbl_adv(tbl, false);
}

/// print a two dimension table
pub fn print_tbl<F:PrimeField>(name: &str, tbl: &Vec<Vec<F>>){
	println!("===== {} ====", name);
	let n = tbl[0].len();
	for i in 0..n{
		for j in 0..tbl.len(){
			print!(" {} ", tbl[j][i]);
		}
		println!("");
	}
}
/// assert that the table is sorted in keys and values (per key)
/// (key, id, col) padded with zero and max entries. Relaxed mean that
/// id not required to be strictly increasing
pub fn assert_wellformed_sorted_two_col_tbl_adv<F:PrimeField>(tbl: &Vec<Vec<F>>,
	b_relax: bool){
	//1. quick check
	let n = tbl[0].len();
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let (zero, max, one) = (F::zero(), F::from(max_val as u32), F::one());
	assert!(tbl[1].len()==n && tbl[2].len()==n);

	//2. check key is sorted
	for i in 1..n{ assert!(tbl[0][i-1] <= tbl[0][i]); }

	//3. assert id is well formed
	for i in 1..n{
		if tbl[0][i] != tbl[0][i-1]{//new key 
			assert!(tbl[2][i]==zero);
			assert!(tbl[2][i-1]==max || (tbl[0][i-1]==zero && tbl[2][i-1]==zero));
		}else{//same key
			assert!(tbl[0][i]==zero || tbl[1][i] == tbl[1][i-1] + one || (b_relax && tbl[1][i]==tbl[1][i-1]));
			assert!(tbl[0][i]==zero || tbl[2][i] > tbl[2][i-1], "tbl[0][i]: {}, tbl[2][i]: {}, tbl2[i][i-1]: {}. Not satisfy tbl[0][i]==zero or tbl[2][i]>tbl[2][i-1]. FAILURE usual cause: RANGE2_BIT not sufficient", tbl[0][i], tbl[2][i], tbl[2][i-1]);
		}
		if i==n-1{ assert!(tbl[2][i]==max || tbl[0][i]==zero); }
	}
}

/// given the hashmap generate a wide wellformed table of structure
///  key - val - id - count
/// where id starts from 0 and count is the real count -1.
/// it is padded with (0-0-0-0) entries.
pub fn hashmap_to_wide_wellformed<F:PrimeField>(
	map: &HashMap<F, Vec<F>>, n: usize, name: &str) 
-> Result<Rc<RefCell<Container<F>>>, Error>{
	//1. collect the sorted keys first
	let res = Container::<F>::new(name);
	let mut sorted_keys = map.keys().map(|x| x.clone())
		.collect::<Vec<F>>();
	sorted_keys.sort();

	//2. construct tuples
	let tuples = sorted_keys.par_iter().map(|k|{
		let v = map.get(k).unwrap();
		let f_count = F::from( (v.len()-1) as u32); //actual count - 1
		let mut res = vec![];
		let mut id = 0;
		for val in v{
			res.push(vec![*k, *val, F::from(id as u32), f_count]);
			id += 1;
		}

		res
	}).flatten().collect::<Vec<Vec<F>>>(); 

	if n<tuples.len(){
		return Err(Error::CapErr(vec![(format!("target_size::hashmap_2col_wide"), tuples.len())]));
	}
	assert!(n>=tuples.len(),"n:{} lower than tuples.len(): {}",n,tuples.len());

	//3. pad and construct
	let zero = F::zero();
	let part1 = vec![vec![zero, zero, zero,zero]; n - tuples.len()];
	let all_tuples = vec![part1, tuples].concat();
	assert!(all_tuples.len()==n);
	
	let c1 = all_tuples.par_iter().map(|t| t[0]).collect::<Vec<F>>();
	let c2 = all_tuples.par_iter().map(|t| t[1]).collect::<Vec<F>>();
	let c3 = all_tuples.par_iter().map(|t| t[2]).collect::<Vec<F>>();
	let c4 = all_tuples.par_iter().map(|t| t[3]).collect::<Vec<F>>();
	let f_rg= F::from(RANGE2);
	let s = vec![f_rg; n];
	res.borrow_mut().add_col(Col::new(c1, "key", IDX_DATA));
	res.borrow_mut().add_col(Col::new(s.clone(), "si_key", IDX_SI_DATA));
	res.borrow_mut().add_col(Col::new(c2, "val", IDX_DATA));
	res.borrow_mut().add_col(Col::new(s.clone(), "si_val", IDX_SI_DATA));
	res.borrow_mut().add_col(Col::new(c3, "id", IDX_DATA));
	res.borrow_mut().add_col(Col::new(s.clone(), "si_id", IDX_SI_DATA));
	res.borrow_mut().add_col(Col::new(c4, "count", IDX_DATA));
	res.borrow_mut().add_col(Col::new(s, "si_count", IDX_SI_DATA));

	Ok( res )
}

/// given the hashmap generate padded 2 column table where
/// entries are padded with pure 0 entries, and it's well formed
/// and sorted. Form: (key, id, val). It's actually 3 columns
/// with an additonal id col.
/// e.g.
/// key id val
/// 0   0  0    # pad
/// 0   0  0    # pad
/// 100 0  0    
/// 100 1  2   
/// 100 2  50  
/// 100 3  max # max = 2^RANGE2_BIT - 1
///
/// might throw CapErr("target_size");
pub fn hashmap_to_sorted_2col_tbl<F:PrimeField>(
	map: &HashMap<F, Vec<F>>, n: usize) 
-> Result<(Vec<F>,Vec<F>,Vec<F>),Error>{
	//1. collect the sorted keys first
	let mut sorted_keys = map.keys().map(|x| x.clone())
		.collect::<Vec<F>>();
	sorted_keys.sort();

	//2. construct tuples
	let zero = F::zero();
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let tuples = sorted_keys.par_iter().map(|k|{
		let v = map.get(k).unwrap();
		let mut res = vec![];
		let mut id = 1;
		res.push(vec![*k, zero, zero]);
		for val in v{
			res.push(vec![*k, F::from(id as u32), *val]);
			id += 1;
		}
		res.push(vec![*k, F::from(id as u32), max]);

		res
	}).flatten().collect::<Vec<Vec<F>>>(); 

	if n<=tuples.len(){
		return Err(Error::CapErr(vec![(format!("target_size::hashmap_2col"), 
			tuples.len()+1)]));
	}
	assert!(n>tuples.len(),"n:{} lower than tuples.len(): {}",n,tuples.len());
	let part1 = vec![vec![zero, zero, zero]; n - tuples.len()];
	let all_tuples = vec![part1, tuples].concat();
	let key:Vec<F>= all_tuples.par_iter().map(|t| t[0]).collect::<Vec<_>>();

	let id= all_tuples.par_iter().map(|t| t[1]).collect::<Vec<_>>();
	let val= all_tuples.par_iter().map(|t| t[2]).collect::<Vec<_>>();
	assert!(key.len()==n);

	Ok( (key, id, val) )
}



/// verify v2 is an inverse of v1. elen is the expected length of both
/// array. Beta is the random challenge.
/// COST: n constraints (n = elen)
pub fn verify_inverse<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], 
	beta: &FpVar<F>, elen: usize)->Result<(), SynthesisError>{
	let b_new = true;
	let b_perf = false;
	let nc = cs.num_constraints();
	assert!(v1.len()==v2.len());
	assert!(v1.len()==elen);
	let res = if b_new{
		verify_inverse_new(cs.clone(), v1, v2, beta, elen)
	}else{
		verify_inverse_old(cs.clone(), v1, v2, beta, elen)
	};

	if b_perf{ 
		println!("--- verify_inverse: len: {}, cs: {}", elen,
			cs.num_constraints() - nc)
	};
	res
}

/// old version: cost: 2N
pub fn verify_inverse_old<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], 
	beta: &FpVar<F>, elen: usize)->Result<(), SynthesisError>{
	let b_debug = false;

	let one_var= FpVar::<F>::new_constant(cs.clone(), F::one())?;
	for i in 0..elen{
		if b_debug{
			assert!((v2[i].value()?*(v1[i].value()? + beta.value()?)).is_one());
		}
		let prod = &v2[i] * &(&v1[i] + beta);
		prod.enforce_equal(&one_var)?;
	}
	Ok( () )
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

/// convert a FP var tovar  
pub fn fpvar_to_var<F:PrimeField>(v: &FpVar<F>)->Variable{
	let res = match v{
		Var(v) => v.variable,
		Constant(_) => panic!("expecting var!")
	};

	res
}


/// verify v2: cost N.
pub fn verify_inverse_new<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], 
	beta: &FpVar<F>, elen: usize)->Result<(), SynthesisError>{
	let b_debug = false;

	let beta_tuple= var_to_tuple(&beta);
	let lb_one = LinearCombination::from((F::one(),Variable::One));
	for i in 0..elen{
		if b_debug{
			assert!((v2[i].value()?*(v1[i].value()? + beta.value()?)).is_one());
		}

		let lb_v2_i = var_to_lb(&v2[i], F::one());
		let lb_v1_i = LinearCombination::<F>(vec![
			var_to_tuple(&v1[i]),
			beta_tuple.clone(),
		]);

		cs.enforce_constraint(
			lb_v2_i,
			lb_v1_i,
			lb_one.clone(),
		)?;
	}
	Ok( () )
}

///  assert that v2 is the inverse of the combined values from v1.
/// assuming v1 all column's cell already in RANGE2.
/// COST: n
pub fn verify_inverse_mul_col<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	v1: &Vec<&[FpVar<F>]>, 
	v2: &[FpVar<F>], 
	beta: &FpVar<F>
)->Result<(), SynthesisError>{
	//1. preprare the factors
	let b_debug = false;
	let num_cols = v1.len();
	let n = v1[0].len();
	for c in v1 {assert!(c.len()==n);}
	let factor = F::from(1u32<<RANGE2_BIT);	
	let mut coefs = vec![F::one(); num_cols];
	for i in 1..coefs.len() {coefs[i] = coefs[i-1] * factor;}
	coefs.reverse();
	let lb_one = LinearCombination::from((F::one(),Variable::One));
	let mut lb_v1_template = coefs.iter().map(|coef|{
		(*coef, Variable::One)
	}).collect::<Vec<(F, Variable)>>();
	lb_v1_template.push( var_to_tuple(beta) );
	let beta_val = beta.value()?;

	//2. enforce the inverse relation
	for i in 0..n{
		let mut vec_lb_v1 = lb_v1_template.clone();
		for j in 0..num_cols {vec_lb_v1[j].1 = var_to_variable(&v1[j][i]) };
		let lb_v1 = LinearCombination(vec_lb_v1);
		if b_debug{
			let mut v1_val = F::zero();
			for j in 0..num_cols{ v1_val += v1[j][i].value()? * coefs[j]; }
			v1_val += beta_val;
			assert!(v2[i].value()? * v1_val == F::one());
		}

		let lb_v2_i = var_to_lb(&v2[i], F::one());

		cs.enforce_constraint(
			lb_v2_i,
			lb_v1,
			lb_one.clone(),
		)?;
	}
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	Ok( () )
}

/// verify the log-up relation. check if all elements of (inverse of) v1 belong
/// to v2. Here v1 and v2 should be the
/// INVERSE of the query table and lkup table.  Call verify_inverse()
/// first on the inversed table and the original table before calling this
/// function.
///
/// COST: n2 + 6
pub fn verify_logup_inverse<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], m_tbl: &[FpVar<F>])
	->Result<(), SynthesisError>{
	let b_new = true;
	let b_perf = false;
	let nc = cs.num_constraints();
	let res = if b_new{
		verify_logup_inverse_new(cs.clone(), v1, v2, m_tbl)
	}else{
		verify_logup_inverse_old(cs.clone(), v1, v2, m_tbl)
	};
	if b_perf{ 
		println!("--- verify_logup_inverse: len1: {}, len2: {}, cs: {}", 
			v1.len(), v2.len(), cs.num_constraints() - nc)
	};
	res

}

/// COST: 2*n2  (n1 almost cost nothing)
/// v1 is the query table, v2 is the lookup table.
pub fn verify_logup_inverse_old<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], m_tbl: &[FpVar<F>])
	->Result<(), SynthesisError>{
	assert!(v2.len()==m_tbl.len());
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?; 
	let one_wit_var = FpVar::<F>::new_witness(cs.clone(), 
		||Ok(F::one())).unwrap();
	one_wit_var.enforce_equal(&one_var)?; 


	let mut sum_left = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v1.len(){ 
		sum_left += &v1[i]; 
		if i%ADD_CHAIN_SIZE==0{ //this is to prevent code calling assigned_value() chain
			//too long which can cause stack overflow in recursion
			//COMMENT OUT LATER IF DOES NOT HELP
			let value = sum_left.value();
			assert!(value.is_ok());
			sum_left = &sum_left * &one_wit_var; //to break the long chain of
							//linear combination
		}
	}

	let mut sum_right = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v2.len(){ 
		sum_right+= &(&v2[i] * &m_tbl[i]);
		if i%ADD_CHAIN_SIZE==0{//this is to prevent the cfg(test) code calling value
			//for chain too long, which overflows stack when it's doing 
			//recursion.
			//COMMENT OUT LATER IF DOES NOT HELP
			//let value= sum_right.value();
			//assert!(value.is_ok());
			sum_right = &sum_right * &one_wit_var; //to break long chain
				//of lc chain. ... Note: this may not be needed.
		}
	}
	sum_right = &sum_right * &one_wit_var; //prevents which assert
		//sum_left == sum_right, the two contains concat and generates
		//2x long linear combination chain.

	sum_left.enforce_equal(&sum_right)?;
		
	#[cfg(test)]{
		if sum_left.value().is_ok(){ 
			assert!(sum_left.value().unwrap()==sum_right.value().unwrap()); 
		}
	}

	Ok( () )
}

/// COST: n2 + 6 (n1 almost cost nothing)
pub fn verify_logup_inverse_old1<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], m_tbl: &[FpVar<F>])
	->Result<(), SynthesisError>{
	assert!(v2.len()==m_tbl.len());
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?; 
	let one_wit_var = FpVar::<F>::new_witness(cs.clone(), 
		||Ok(F::one())).unwrap();
	one_wit_var.enforce_equal(&one_var)?; 


	let mut sum_left = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	for i in 0..v1.len(){ 
		sum_left += &v1[i]; 
		if i%ADD_CHAIN_SIZE==0{ //this is to prevent code calling assigned_value() chain
			//too long which can cause stack overflow in recursion
			//COMMENT OUT LATER IF DOES NOT HELP
			let value = sum_left.value();
			assert!(value.is_ok());
			sum_left = &sum_left * &one_wit_var; //to break the long chain of
							//linear combination
		}
	}

	let mut sum_right = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))
		.unwrap();
	sum_right.enforce_equal(&FpVar::zero())?; //as we need sum_right as var
	let mut vec_sum_right = vec![sum_right.clone()];

	for i in 0..v2.len(){ 
		//we try to simulate the following with one constraint
		//sum_right+= &(&v2[i] * &m_tbl[i]);
		let new_sum_right = FpVar::new_witness(cs.clone(),
			|| Ok(vec_sum_right[i].value()? + 
				m_tbl[i].value()?*v2[i].value()?)).unwrap(); 
		vec_sum_right.push(new_sum_right.clone());

		let lb_v2_i =  var_to_lb(&v2[i], F::one());
		let lb_m_i=  var_to_lb(&m_tbl[i], F::one());
		//let lb_neg_sum_right =  var_to_lb(&vec_sum_right[i], -F::one());
		//let lb_new_sum_right =  var_to_lb(&new_sum_right, F::one());
		//let lb_diff = lb_new_sum_right + lb_neg_sum_right;
		let lb_diff = LinearCombination::<F>(vec![
			var_to_tuple_adv(&vec_sum_right[i], -F::one()),
			var_to_tuple(&new_sum_right),
		]);
		
		cs.enforce_constraint(
			lb_v2_i,
			lb_m_i,
			lb_diff,
		)?;
		

		if i%ADD_CHAIN_SIZE==0{//this is to prevent the cfg(test) code calling value
			//for chain too long, which overflows stack when it's doing 
			//recursion.
			//COMMENT OUT LATER IF DOES NOT HELP
			//let value= sum_right.value();
			//assert!(value.is_ok());
			sum_right = vec_sum_right[i].clone();
			sum_right = &sum_right * &one_wit_var; //to break long chain
				//of lc chain. ... Note: this may not be needed.
			vec_sum_right[i] = sum_right;
		}
	}
	sum_right = vec_sum_right[vec_sum_right.len()-1].clone();
	sum_right = &sum_right * &one_wit_var; //prevents which assert
		//sum_left == sum_right, the two contains concat and generates
		//2x long linear combination chain.

	sum_left.enforce_equal(&sum_right)?;
		
	#[cfg(test)]{
		if sum_left.value().is_ok(){ 
			assert!(sum_left.value().unwrap()==sum_right.value().unwrap()); 
		}
	}

	Ok( () )
}

/// IDEA: every lblcok of ADD_CHAIN, build a huge LinearCombination 
/// and sum it up
/// COST: vlen/ADD_CHAIN_SIZE (64)
pub fn sum_vec_vars<F:PrimeField>(v: &[FpVar<F>])->FpVar<F>{
	let cs = v[0].cs();
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one()).unwrap(); 
	let one_wit_var = FpVar::<F>::new_witness(cs.clone(), 
		||Ok(F::one())).unwrap();
	one_wit_var.enforce_equal(&one_var).unwrap(); 
	let mut sum = FpVar::<F>::new_constant(cs.clone(), F::zero()).unwrap();
	let lb_one = LinearCombination::<F>(vec![(F::one(), Variable::One)]);

	let blocks = v.len() / ADD_CHAIN_SIZE;
	for i in 0..blocks{
		//1. build up the big linear combination
		let start = i * ADD_CHAIN_SIZE;
		let mut vec_sum_tuples = vec![(F::one(), Variable::One); 
			ADD_CHAIN_SIZE];
		let mut f_sum = F::zero();
		for j in 0..ADD_CHAIN_SIZE{
			f_sum += v[start+j].value().unwrap();
			vec_sum_tuples[j]  = var_to_tuple(&v[start+j]);
		}

		//2. sum it up
		let lb = LinearCombination::<F>(vec_sum_tuples);
		let x = FpVar::<F>::new_witness(cs.clone(), || Ok(f_sum)).unwrap();
		cs.enforce_constraint(
			lb, 
			lb_one.clone(),
			var_to_lb(&x, F::one())
		).unwrap();
		sum = sum + &x * &one_wit_var; 
	}
	for i in blocks * ADD_CHAIN_SIZE .. v.len(){
		sum  = &sum + &v[i];
	}

	sum
}

/// COST: n2 + 6 (n1 almost cost nothing)
pub fn verify_logup_inverse_new<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>], m_tbl: &[FpVar<F>])
	->Result<(), SynthesisError>{
	assert!(v2.len()==m_tbl.len());
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?; 
	let one_wit_var = FpVar::<F>::new_witness(cs.clone(), 
		||Ok(F::one())).unwrap();
	one_wit_var.enforce_equal(&one_var)?; 

	let sum_left = sum_vec_vars(&v1);

	assert!(v2.len()==m_tbl.len());
	let v3 = v2.iter().zip(m_tbl.iter()).map(|(v,m)|
		v * m).collect::<Vec<FpVar<F>>>();
	let sum_right = sum_vec_vars(&v3);

	sum_left.enforce_equal(&sum_right)?;
		
	#[cfg(test)]{
		if sum_left.value().is_ok(){ 
			assert!(sum_left.value().unwrap()==sum_right.value().unwrap()); 
		}
	}

	Ok( () )
}

/// verify v1 is the encoded form of v2 regarding states and sig counts
/// (the state corresponds to how many signatures)
/// see clam_db for how it's encoded
/// We assume v2 is structured as states concat with counts.
pub fn verify_encoded_states_sig_count<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>])
	->Result<(), SynthesisError>{
	let n = v1.len();
	assert!(v2.len()==2*n);
	let sigbit_factor = FpVar::<F>::new_constant(cs.clone(),
		F::from(1u32 << RANGE2_BIT))?;
	for i in 0..n{
		let (s, v) = (&v2[i], &v2[n+i]); //assume s is already +1
		let encoded = s*&sigbit_factor + v; 
		encoded.enforce_equal(&v1[i])?;
		#[cfg(test)]{
			if encoded.value().is_ok(){ 
				assert!(encoded.value()?==v1[i].value()?); 
			}
		}
	}

	Ok( () )
}
/// verify v1 is the encoded form of v2 regarding states and sigs.
/// (the state corresponds to one signature)
/// see clam_db for how it's encoded
/// We assume v2 is structured as states || ids || counts
/// NOTE: all states and ids start from 1
pub fn verify_encoded_states_sig<F:PrimeField>(cs: ConstraintSystemRef<F>,
	v1: &[FpVar<F>], v2: &[FpVar<F>])
	->Result<(), SynthesisError>{
	let n = v1.len();
	assert!(v2.len()==3*n);
	let sigbit_factor = FpVar::<F>::new_constant(cs.clone(),
		F::from(1u32 << RANGE2_BIT))?;
	let sigbit_fac2 = &sigbit_factor * &sigbit_factor;
	for i in 0..n{
		let (s, id, v) = (&v2[i], &v2[n+i], &v2[2*n+i]); 
		let encoded = s*&sigbit_fac2 + id*&sigbit_factor + v; 
		encoded.enforce_equal(&v1[i])?;
		#[cfg(test)]{
			if encoded.value().is_ok(){ 
				assert!(encoded.value()?==v1[i].value()?); 
			}
		}
	}

	Ok( () )
}

/// check if array is increasing
pub fn check_increase<F:PrimeField>(vec: &Vec<FpVar<F>>)
->Result<(),SynthesisError>{
	let cs = vec[0].cs();
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?; 
	for i in 1..vec.len(){
		let diff = &vec[i] - &vec[i-1];
		check_eq(&diff, &one_var, "check location")?;
	}
	Ok( () )
}

/// pack the check of 8 values into one check
/// assuming that each element of vec is ALREADY IN RANGE 31-BIT
/// COST is vec.len()/4
/// ASSUMING vec_pows_31 has 8 elements [2^31, 2^62, 2^93 ..., 2^248]
pub fn packcheck_increase<F:PrimeField>(vec: &Vec<FpVar<F>>, 
	pows_31: &Vec<FpVar<F>>)
->Result<(),SynthesisError>{
	assert!(pows_31.len()==8);
	let cs = vec[0].cs();
	let c1 = new_const_var(&cs, F::one());
	let c0 = new_const_var(&cs, F::zero());
	let vec_inc = (0..8).into_iter().map(|i|
		new_const_var(&cs, F::from( i as u32))
	).collect::<Vec<FpVar<F>>>();

	for i in 0..vec.len()/8{//note mul with const does not cost
		let mut total_exp = c0.clone();
		for j in 0..8{ total_exp = &total_exp + 
			&( &(&vec[i*8] +&vec_inc[j]) * &pows_31[j]); }
		let mut total_var = c0.clone();
		for j in 0..8{ total_var = &total_var + &(&vec[i*8 + j]*&pows_31[j]); }
		check_eq(&total_var, &total_exp, "failed vec check inc")?;
		if i>0{
			check_eq(&(&vec[i*8]-&vec[i*8-1]), &c1, "failed conn check inc")?;
		}
	}
	//check the remaining
	let start = vec.len()/8 * 8;
	for i in start..vec.len()-1{
		if i>0{
			check_eq(&(&vec[i+1]-&vec[i]), &c1, "failed inc check part 2")?;
		}
	}
	Ok( () )
}


/// Check two fp_var equal. Cost 1 gate.
pub fn check_eq<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	v1.enforce_equal(&v2)?;

	#[cfg(test)]{
		if v1.value().is_ok(){ 
			assert!(v1.value()?==v2.value()?, "ERROR on {}. v1: {}, v2: {}", _msg, v1.value()?, v2.value()?);
		}
	}
	Ok( () )
}

/// Check two fp_var NOT equal. Cost 4 gate.
pub fn check_neq<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	#[cfg(test)]{
		if v1.value().is_ok(){ 
			assert!(v1.value()?!=v2.value()?, "ERROR on check_neq: {}. v1: {}, v2: {}", _msg, v1.value()?, v2.value()?);
		}
	}
	let cs = v1.cs();
	let nc = cs.num_constraints();
	let beq = is_zero_better(&(v1-v2), &cs)?;
	let zero_var = FpVar::<F>::constant(F::zero());
	check_eq(&beq, &zero_var, "ERR in check_neq")?;
	println!("STOP HERE 3333: {}", cs.num_constraints()-nc);

	Ok( () )
	
}


/// Check two fp_var equal or v1[i] is zero
pub fn check_eq_nz<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>, z_const: &FpVar<F>,_msg: &str)
->Result<(),SynthesisError>{
	let diff = v1 - v2;
	let res = &diff * v1;
	res.enforce_equal(z_const)?;

	#[cfg(test)]{
		if v1.value().is_ok(){ 
			assert!(v1.value()?==v2.value()? || v1.value()?.is_zero(), "ERROR on check eq_nz: {}.", _msg);
		}
	}
	Ok( () )
}

/// Check array eq value. Cost: n gates
pub fn check_arr_eq<F:PrimeField>(vec: &[FpVar<F>], z: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	for i in 0..vec.len(){
		check_eq(&vec[i], &z, &format!("check eq {} fails: {}", i, _msg))?;
	}
	Ok( () )
}

/// Check array eq value. Cost: n gates
pub fn check_arr_eq_arr<F:PrimeField>(vec: &[FpVar<F>], vec2: &[FpVar<F>], _msg: &str)
->Result<(),SynthesisError>{
	assert!(vec.len()==vec2.len());
	for i in 0..vec.len(){
		check_eq(&vec[i], &vec2[i], &format!("check eq {} fails: {}", i, _msg))?;
	}
	Ok( () )
}


/// Check array eq value (takes advantage of random r so we actually
/// do a random combination). This function should ONLY be called
/// on vec when it is part of fixed witness (in stmt or msg1)
/// It actually costs the same number of gates of check_arr_eq (n+1)
#[allow(dead_code)]
pub fn check_arr_eq_fast<F:PrimeField>(vec: &[FpVar<F>], 
	z: &FpVar<F>, r: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	let cs = r.cs();
	let zero = FpVar::new_constant(cs.clone(), F::zero())?;
	let mut res = FpVar::new_constant(cs.clone(), F::zero())?;
	for i in 0..vec.len(){
		res = &res + r * &(&vec[i] - z);
	}
	res.enforce_equal(&zero)?;
	Ok( () )
}

/// Check array eq given value or the entro is zero
pub fn check_arr_eq_nz<F:PrimeField>(vec: &[FpVar<F>], z: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	let fp_zero = FpVar::<F>::new_constant(z.cs().clone(), F::zero())?;
	for i in 0..vec.len(){
		check_eq_nz(&vec[i], &z, &fp_zero, &format!("check eq {} fails: {}", i, _msg))?;
	}
	Ok( () )
}

/// Check array eq or the value if rg2
///COST: n
pub fn check_arr_eq_or_rg2<F:PrimeField>(vec: &[FpVar<F>], z: &FpVar<F>, _msg: &str)
->Result<(),SynthesisError>{
	let fp_zero = FpVar::<F>::new_constant(z.cs().clone(), F::zero())?;
	let rg2 = F::from(RANGE2 as u32);
	let fp_rg2= FpVar::<F>::new_constant(z.cs().clone(), rg2)?;
	let lb_minus_v2 = var_to_lb(z, -F::one());
	let lb_minus_rg2 = var_to_lb(&fp_rg2, -F::one());
	let lb_zero = var_to_lb(&fp_zero, F::one());
	let cs = vec[0].cs();
	for i in 0..vec.len(){
		let lb_v1 = var_to_lb(&vec[i], F::one());
		//check_eq_nz(&vec[i], &z, &fp_zero, &format!("check eq {} fails: {}", i, _msg))?;
		#[cfg(test)]{
			let z_val = z.value().unwrap(); 
			let v1 = vec[i].value().unwrap();
			assert!(v1==z_val || v1==rg2);
		}
		cs.enforce_constraint(
			lb_v1.clone() + lb_minus_rg2.clone(),
			lb_v1 + lb_minus_v2.clone(),
			lb_zero.clone(),
		)?;

	}
	Ok( () )
}




/// check two boolean var equal
pub fn check_beq<F:PrimeField>(v1: &Boolean<F>, v2: &Boolean<F>, _msg: &str)
->Result<(),SynthesisError>{
	v1.enforce_equal(&v2)?;
	#[cfg(test)]{
		if v1.value().is_ok(){ 
			assert!(v1.value()?==v2.value()?, "ERROR on {}.", _msg);
		}
	}
	Ok( () )
}

/// check b1 implies b2, i.e., not b1 or b2 is true
pub fn check_imply<F:PrimeField>(b1: &Boolean<F>, b2: &Boolean<F>, _msg: &str)
-> Result<(), SynthesisError>{
	let res = b1.not().or(b2)?;
	check_beq(&res, &Boolean::TRUE, &format!("ERR on imply: {}", _msg))?;
	Ok( () )
}

/// expand a vec to a given size (if the vec is greater
/// than the vec size, panic)
pub fn expand_vec<F:PrimeField>(vec: &mut Vec<F>, size: usize){
	assert!(vec.len()<=size);
	let mut rem = vec![F::zero(); size-vec.len()];
	vec.append(&mut rem);
}

/// generate the correpsonding m_table for cols with selectors.
/// Count the WEIGHTED number of appearance of lkup (using selector)
/// We ALLOW lkup has duplicate non-zero elements (that is:
/// the first entry will have non-zero m-table value and the other
/// duplicates will have m-tbl value 0).
pub fn gen_m_table<F:PrimeField>(qry: &Vec<F>, lkup: &Vec<F>)->Vec<F>{
	let b_debug = false;
	if b_debug{
		for x in qry{ assert!(lkup.contains(x), "cannot find {}", x); } 
	}
	//1. establish a hashmap and go over the query table
	let map:HashMap<F,usize> = qry.into_par_iter()
	.fold(|| HashMap::new(),
		|mut acc, state| {
			*acc.entry(*state).or_insert(0) += 1;
			acc
		})
	.reduce(//merge accumulator of threads
		|| HashMap::new(),
		|mut acc1, acc2| {
			for (key, val) in acc2{ *acc1.entry(key).or_insert(0) += val; }
			acc1
		}
	);

	//2. raw dump
	let mut m_tbl = lkup.par_iter().map(|x|{
			let occ = map.get(x).unwrap_or(&0usize);
			F::from(*occ as u32)
	}).collect::<Vec<F>>();

	//3. mark up in the m_tbl duplicate entries to 0
	let mut set2 = HashSet::<F>::new();
	let zero = F::zero();
	for i in 0..m_tbl.len(){
		m_tbl[i] = if set2.contains(&lkup[i]){zero} else { 
			set2.insert(lkup[i]);
			m_tbl[i]
		};
	}

	m_tbl
}

/// Generate 2 direction lookup proof.
/// Here we have a collection of query columns, where we assume
/// all values in RANGE2. Similarly, same number of lkup_cols with
/// all values in RANGE2 (so that we can simply concat values as bit-paterns).
/// We prove that all values of query_cols (combines) can be found in
/// lkup_cols, and all combined values of lkup_cols can be found in 
/// qury columns (2-direciton lookup).
/// NOTE: we require: the lookup table (except for 0 entry)
/// has *** NO duplicate values ***! [in this case, query size
/// is usually larger, e.g., lookup table is the pat-loc table
/// and the query table is the pat-loc column in pat-state-loc joined table,
/// and it is larger)].
///
/// Idea: we only need to construct the m_tbl for proving all elements
/// in query table are in lookup table. Then we just need to justify that
/// each element of lookup table has a POSITIVE m_tbl value (counts in query).
/// Then we simply send the vector: m_tbl - vec![1; mtbl.len()], which
/// we use the SID table to justify that it's in range. Note that
/// this scheme works if we assume: *** lookup table have NO DUPLICATES ***
///
/// Now, the only complication is that both lookup table and 
/// query table have MULTIPLE 0 elements. This can be easily
/// addressed by sendng over the COUNT_OF_0_IN_QUERY and COUNT_OF_0_IN_LKUP
/// and for m_tbl value for 0 elements in LOOKUP (simply assign 1).
/// This easily balances the equation check.
/// Eg.g.,
/// qry-tbl (2col)              lkup-tbl(2col)   m-tbl (counts of occ in qry)
/// 0  0                        0    0           1
/// 0  0                        1    2           3 
/// 1  2                        2    3           1
/// 2  3
/// 1  2
/// 1  2
/// We write bit-concat of two column values as 0-0, let r be random
/// 1/(0-0 + r)  + 1/(0-0+r) + 1/(1-2 + r) +... 1/(1-2 + r)
/// = 
/// 1 * 1/(0-0 + r) + 3 * 1/(1-2 + r) + 1 * 1/(2-3+r)
///   + COUNT_DIFF * 1(0-0 + r)
/// The count difference is 1 qry table has one more (0,0) entry.
/// The verification cost will be just one Logup check cost,
/// because the "range check" for mtbl-vec![1; mtbl.len()] is free.
pub fn gen_2d_lkup_prf<F:PrimeField>(
	qry_cols: Vec<&[F]>, 
	lkup_cols: Vec<&[F]>, 
	name: &str)->Rc<RefCell<Container<F>>>{
	//1. compute the combined cell values
	let res = Container::<F>::new(name);
	assert!(qry_cols.len()==lkup_cols.len());
	let n1 = qry_cols[0].len();
	let n2 = lkup_cols[0].len();
	for c in &qry_cols {assert!(c.len()==n1);}
	for c in &lkup_cols {assert!(c.len()==n2);}
	let ids = (0..qry_cols.len()).collect::<Vec<usize>>();
	let qry = encode_cols_better(qry_cols.clone(), ids.clone()); 
	let lkup = encode_cols_better(lkup_cols.clone(), ids); 
	assert!(qry.len()==n1 && lkup.len()==n2);

	//2. data-check (no duplicate elements)
	let count0_qry = qry.par_iter().filter(|x| x.is_zero()).count();
	let count0_lkup= lkup.par_iter().filter(|x| x.is_zero()).count();
	let nz_lkup = lkup.par_iter().filter(|x| !x.is_zero()).map(|x| *x)
		.collect::<HashSet<F>>();
	assert!(nz_lkup.len()+count0_lkup==lkup.len(), "lkup should have no-duplicates of NON-zero values!");

	//3. compute the m_tbl (offset by 1)
	//modify the m_tbl such that each 0 entry is lkup is mandatoriy
	//assign a value "1" (which will be compensated by the zero_diff
	//calcuation later). This avoids to assign "0" to 0 entries i lkup
	//if there are multiple of them.
	//then perform "-1" to each m_tbl entry.
	let mut m_tbl = gen_m_table(&qry, &lkup);
	for i in 0..lkup.len(){if lkup[i].is_zero() {m_tbl[i] = F::one();}}
	let mz = m_tbl.par_iter().find_any(|x| x.is_zero());
	assert!(mz.is_none(), "m_tbl has zero entries");
	let m_tbl_1 = m_tbl.par_iter().map(|&x| x - F::one())
		.collect::<Vec<F>>();
	let f_rg= F::from(RANGE2);
	let sid_m_tbl_1 = vec![f_rg; m_tbl_1.len()];
	res.borrow_mut().add_col(Col::new(m_tbl_1, "m_tbl_1", IDX_DATA));
	res.borrow_mut().add_col(
		Col::new_const(sid_m_tbl_1, "sid_m_tbl_1", IDX_SI_DATA));

	//4. compute the difference in 0 entries
	let f_zero_diff = F::from(count0_qry as u32) - F::from(count0_lkup as u32);
	res.borrow_mut().add_col(
		Col::new(vec![f_zero_diff], "zero_diff", IDX_DATA));
	res.borrow_mut().add_col(Col::new_const(
		vec![F::zero()], "sid_zero_diff", IDX_SI_DATA));

	res
}

// this is essentially the gen_m_tbl
// the only difference is that we handle multiple columns
// NOTE that unlike the gen_2d_lkup we have NO restriction
// on that no non-zero duplicate elemnets in lookup. This is
// actually pretty standard 1-way lookup (Logup relation [Hab'22])
pub fn gen_1d_lkup_prf<F:PrimeField>(
	qry_cols: Vec<&[F]>, 
	lkup_cols: Vec<&[F]>, 
	name: &str)->Rc<RefCell<Container<F>>>{
	//1. compute the combined cell values
	let res = Container::<F>::new(name);
	assert!(qry_cols.len()==lkup_cols.len());
	let n1 = qry_cols[0].len();
	let n2 = lkup_cols[0].len();
	for c in &qry_cols {assert!(c.len()==n1);}
	for c in &lkup_cols {assert!(c.len()==n2);}
	let ids = (0..qry_cols.len()).collect::<Vec<usize>>();
	let qry = encode_cols_better(qry_cols.clone(), ids.clone()); 
	let lkup = encode_cols_better(lkup_cols.clone(), ids); 
	assert!(qry.len()==n1 && lkup.len()==n2);

	//2. generate the proof
	let f_rg= F::from(RANGE2);
	let m_tbl = gen_m_table(&qry, &lkup);
	let sid_m_tbl_1 = vec![f_rg; m_tbl.len()];
	res.borrow_mut().add_col(Col::new(m_tbl, "m_tbl", IDX_DATA));
	res.borrow_mut().add_col(Col::new_const(sid_m_tbl_1, "sid_m_tbl", 
		IDX_SI_DATA));

	res
}

/// verify the 2-way lookup between qry_cols and lkup_cols
/// where we assume all values in RANGE2, and no DUPLICATED non-zero
/// combined alues in lkup_cols. 
/// Idea: we just run one lookup between qry_cols and lkup_cols
/// and reason about that all entries in lkup table are COVERED
/// (basically proving that all m_table entries are positive, with
/// the only exception to handle 0-entries). 
///
/// COST: let n_q and n_l be the length of qry and lkup table
/// nq + 2*n_l + 6
pub fn verify_2d_lkup_prf<F:PrimeField>(
	r: FpVar<F>,
	qry_cols: &Vec<&[FpVar<F>]>, 
	lkup_cols: &Vec<&[FpVar<F>]>, 
	prf: &Rc<RefCell<Container<FpVar<F>>>>	
)-> Result<(), SynthesisError>{
	//1. retrieve data
	let b_perf = false;
	let b_debug = false;
	let cs = r.cs();
	let logl = LOG2;
	let mut gt = Timer::new();
	let mut nc = cs.num_constraints();
	let nc0 = nc;
	let m_tbl_1 = prf.borrow().get_container("m_tbl_1").unwrap()
		.borrow().to_vec();
	let zero_diff = prf.borrow().get_container("zero_diff").unwrap()
		.borrow().to_vec()[0].clone();
	let r_val = r.value().expect("error get val of r");
	let n_cols = qry_cols.len();
	assert!(lkup_cols.len() == n_cols);
	let n_q = qry_cols[0].len();
	let n_l = lkup_cols[0].len();
	for c in qry_cols{assert!(c.len()==n_q);}
	for c in lkup_cols{assert!(c.len()==n_l);}
	let qry_cols_vals = qry_cols.iter().map(|c|
		c.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>()
	).collect::<Vec<Vec<F>>>();
	let lkup_cols_vals = lkup_cols.iter().map(|c|
		c.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>()
	).collect::<Vec<Vec<F>>>();
	let qry_cols_vals = qry_cols_vals.iter().map(|c| &c[..])
		.collect::<Vec<&[F]>>();
	let lkup_cols_vals = lkup_cols_vals.iter().map(|c| &c[..])
		.collect::<Vec<&[F]>>();
	let ids = (0..qry_cols.len()).collect::<Vec<usize>>();
	let qry_val = encode_cols_better(qry_cols_vals, ids.clone()); 
	let lkup_val = encode_cols_better(lkup_cols_vals, ids); 
	let inv_qry_val = gen_vec_inverse(&qry_val.par_iter().map(|x|
		*x + r_val).collect::<Vec<F>>());
	let inv_lkup_val = gen_vec_inverse(&lkup_val.par_iter().map(|x|
		*x + r_val).collect::<Vec<F>>());
	let inv_qry = inv_qry_val.iter().map(|&v| new_var(&cs, v))
		.collect::<Vec<FpVar<F>>>();
	let inv_lkup = inv_lkup_val.iter().map(|&v| new_var(&cs, v))
		.collect::<Vec<FpVar<F>>>();
	if b_perf {
		log_perf(logl, &format!("verif_2dlkup step 0. build witness. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
		nc = cs.num_constraints();
	}

	//2. verify the inverse relations are fine
	//COST: n_q + n_l 
	verify_inverse_mul_col(cs.clone(),&qry_cols, &inv_qry, &r)?;
	verify_inverse_mul_col(cs.clone(),&lkup_cols, &inv_lkup, &r)?;
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	if b_perf {
		log_perf(logl, &format!("verif_2dlkup step 1. build witness. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
		nc = cs.num_constraints();
	}


	//3. do a customized assert_logup with the corresponding
	//m_tbl_1 (here, we import and slightly modify the logic of
	//verify_logup_inverse_new. Slight differences are:
	//(1) m_tbl_1 needs to plus one for each item
	//(2) needs to add zero_diff entry
	//multiple columns involved and m_tbl_1 is m_tbl shifted by one
	//we need to lastly handle the zero_diff entries.
	//Given ADD_CHAIN_SIZE is 64.
	//COST: n_l*1.02 + nq*0.02 + 4
	//3.1 sum up the Logup equation on the left (the query table)
	let zero_inv_val = r_val.inverse().unwrap();
	let zero_inv = new_var(&cs, zero_inv_val);
	let mut sum_left = sum_vec_vars(&inv_qry);
	let one_var = FpVar::<F>::new_constant(cs.clone(), F::one())?; 
	check_eq(&(&zero_inv * &r), &one_var, "fails zero_inv check")?;
	let adj = &zero_inv * &zero_diff;
	sum_left -= adj;
	if b_perf {
		log_perf(logl, &format!("verif_2dlkup step 3.1 logup_check. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
		nc = cs.num_constraints();
	}

	//3.2 build up the values first (to speed up mtbl + vec[1]
	assert!(inv_lkup.len()==m_tbl_1.len());
	let m_tbl_1_val = m_tbl_1.iter().map(|x| x.value().unwrap())
		.collect::<Vec<F>>();
	assert!(m_tbl_1_val.len()==inv_lkup_val.len());
	let prod_val = m_tbl_1_val.par_iter().zip(inv_lkup_val.par_iter())
		.map(|(&x,&y)| (x + F::one()) * y).collect::<Vec<F>>();
	let prods = prod_val.into_iter().map(|x| new_var(&cs, x))
		.collect::<Vec<FpVar<F>>>();
	for i in 0..m_tbl_1.len(){
		let lb_m_tbl = LinearCombination(vec![ //m_tbl_1[i] + 1
			var_to_tuple(&m_tbl_1[i]),
			(F::one(), Variable::One),
		]);
		let lb_inv = var_to_lb(&inv_lkup[i], F::one());
		let lb_res = var_to_lb(&prods[i], F::one());
		cs.enforce_constraint( lb_m_tbl, lb_inv, lb_res)?;
	}
	let sum_right = sum_vec_vars(&prods);
	check_eq(&sum_left, &sum_right, "logup check fails")?;
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	if b_perf {
		log_perf(logl, &format!("verif_2dlkup step 3.2 logup_check. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
	}
	if b_perf {
		log_perf(logl, &format!("verif_2dlkup TOTAL . n_q: {}, n_l: {}, cs: {}",
			n_q, n_l, cs.num_constraints()-nc0), &mut gt);
	}

	Ok( () )
}

// verify the standard [Hab'22] Logup relation
// Here we assume all cell values are in RANGE2
// COST: nq + 2*lkup 
// (there is a small factor of
//  extra 0.02*nq + 0.02*lkup because ADDCHAIN_SIZE is 64, it incurs
//  0.02 factor in long chain of add constraints).
pub fn verify_1d_lkup_prf<F:PrimeField>(
	r: FpVar<F>,
	qry_cols: &Vec<&[FpVar<F>]>, 
	lkup_cols: &Vec<&[FpVar<F>]>, 
	prf: &Rc<RefCell<Container<FpVar<F>>>>	
)-> Result<(), SynthesisError>{
	//1. retrieve data
	let b_perf = false;
	let b_debug = false;
	let cs = r.cs();
	let logl = LOG2;
	let mut gt = Timer::new();
	let mut nc = cs.num_constraints();
	let nc0 = nc;
	let m_tbl = prf.borrow().get_container("m_tbl").unwrap()
		.borrow().to_vec();
	let r_val = r.value().expect("error get val of r");
	let n_cols = qry_cols.len();
	assert!(lkup_cols.len() == n_cols);
	let n_q = qry_cols[0].len();
	let n_l = lkup_cols[0].len();
	for c in qry_cols{assert!(c.len()==n_q);}
	for c in lkup_cols{assert!(c.len()==n_l);}
	let qry_cols_vals = qry_cols.iter().map(|c|
		c.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>()
	).collect::<Vec<Vec<F>>>();
	let lkup_cols_vals = lkup_cols.iter().map(|c|
		c.iter().map(|x| x.value().unwrap()).collect::<Vec<F>>()
	).collect::<Vec<Vec<F>>>();
	let qry_cols_vals = qry_cols_vals.iter().map(|c| &c[..])
		.collect::<Vec<&[F]>>();
	let lkup_cols_vals = lkup_cols_vals.iter().map(|c| &c[..])
		.collect::<Vec<&[F]>>();
	let ids = (0..qry_cols.len()).collect::<Vec<usize>>();
	let qry_val = encode_cols_better(qry_cols_vals, ids.clone()); 
	let lkup_val = encode_cols_better(lkup_cols_vals, ids); 
	let inv_qry_val = gen_vec_inverse(&qry_val.par_iter().map(|x|
		*x + r_val).collect::<Vec<F>>());
	let inv_lkup_val = gen_vec_inverse(&lkup_val.par_iter().map(|x|
		*x + r_val).collect::<Vec<F>>());
	let inv_qry = inv_qry_val.iter().map(|&v| new_var(&cs, v))
		.collect::<Vec<FpVar<F>>>();
	let inv_lkup = inv_lkup_val.iter().map(|&v| new_var(&cs, v))
		.collect::<Vec<FpVar<F>>>();
	if b_perf {
		log_perf(logl, &format!("verif_1dlkup step 0. build witness. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
		nc = cs.num_constraints();
	}

	//2. verify the inverse relations are fine
	//COST: n_q + n_l 
	verify_inverse_mul_col(cs.clone(),&qry_cols, &inv_qry, &r)?;
	verify_inverse_mul_col(cs.clone(),&lkup_cols, &inv_lkup, &r)?;
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	if b_perf {
		log_perf(logl, &format!("verif_1dlkup step 1. build witness. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
		nc = cs.num_constraints();
	}

	//3. do a customized assert_logup for multi-columns
	//COST: n_l*1.02 + nq*0.02 + 4
	//3.1  the sum of inverse of query table
	let sum_left = sum_vec_vars(&inv_qry);

	//3.2 the sum of inverse of lookup table
	assert!(inv_lkup.len()==m_tbl.len());
	let m_tbl_val = m_tbl.iter().map(|x| x.value().unwrap())
		.collect::<Vec<F>>();
	let prod_val = m_tbl_val.par_iter().zip(inv_lkup_val.par_iter())
		.map(|(&x,&y)| x * y).collect::<Vec<F>>();
	let prods = prod_val.into_iter().map(|x| new_var(&cs, x))
		.collect::<Vec<FpVar<F>>>();
	for i in 0..m_tbl.len(){
		let lb_m_tbl = var_to_lb(&m_tbl[i], F::one());
		let lb_inv = var_to_lb(&inv_lkup[i], F::one());
		let lb_res = var_to_lb(&prods[i], F::one());
		cs.enforce_constraint( lb_m_tbl, lb_inv, lb_res)?;
	}
	let sum_right = sum_vec_vars(&prods);
	check_eq(&sum_left, &sum_right, "logup check fails")?;
	if b_debug{ assert!(cs.is_satisfied().unwrap()); }
	if b_perf {
		log_perf(logl, &format!("verif_1dlkup step 3.2 logup_check. n_q: {}, n_l: {}, cs: {}", n_q, n_l, cs.num_constraints()-nc), &mut gt);
	}
	if b_perf {
		log_perf(logl, &format!("verif_1dlkup TOTAL . n_q: {}, n_l: {}, cs: {}",
			n_q, n_l, cs.num_constraints()-nc0), &mut gt);
	}

	Ok( () )
}

/// generate the correpsonding m_table, its size will be
/// equal to lkup for CONDITIONAL LOOKUP where
/// only when selector value is NON-ZERO, the entry will be
/// considered. Also note that when selected, any non-zero
/// value serves as `1`. 0 indicates not-selected. We thus,
/// compute values different.
pub fn gen_m_table_cond<F:PrimeField>(qry: &Vec<F>, sel_qry: &Vec<F>,
	lkup: &Vec<F>, sel_lkup: &Vec<F>)->Vec<F>{
	#[cfg(test)]{ 
		for i in 0..qry.len(){ 
			if !sel_qry[i].is_zero() { 
				assert!(lkup.contains(&qry[i]), 
					"cannot find qry[{}]: {}", i, qry[i]); 
			}; 
		} 
	}
	assert!(qry.len()==sel_qry.len());
	assert!(lkup.len()==sel_lkup.len());

	//1. establish a hashmap and go over the query table
	let zero = F::zero();
	let map:HashMap<F,F> = qry.into_par_iter().zip(sel_qry.into_par_iter())
	.fold(|| HashMap::new(),
		|mut acc, (a,b)| {
			*acc.entry(*a).or_insert(zero) += b; 
			acc
		})
	.reduce(//merge accumulator of threads
		|| HashMap::new(),
		|mut acc1, acc2| {
			for (key, val) in acc2{ *acc1.entry(key).or_insert(zero) += val; }
			acc1
		}
	);

	//2. raw dump
	let mut m_tbl = lkup.par_iter().zip(sel_lkup.par_iter()).map(|(x,y)|{
			let occ = map.get(x).unwrap_or(&zero);
			let res = if occ.is_zero() || y.is_zero() {zero} 
				else {*occ * (y.inverse().unwrap())};
			res
	}).collect::<Vec<F>>();

	//3. mark up in the m_tbl duplicate entries to 0
	let mut set2 = HashSet::<F>::new();
	let zero = F::zero();
	for i in 0..m_tbl.len(){
		m_tbl[i] = if set2.contains(&lkup[i]){zero} else { 
			set2.insert(lkup[i]);
			m_tbl[i]
		};
	}

	m_tbl
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
	let lb_res = LinearCombination::<F>(vec![
		(F::one(), Variable::One),
		(-F::one(), z_variable)
	]);
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

pub fn is_eq_adv<F:PrimeField>(x: &FpVar<F>, y: &FpVar<F>, inverse: &F, cs: &ConstraintSystemRef<F>)->FpVar<F>{
	let lb_zero: LinearCombination<F> = lc!();
	//let lb_one = LinearCombination::<F>(vec![(F::one(), Variable::One)]);
	let lb_x_y = LinearCombination::<F>(vec![
		var_to_tuple_adv(x, F::one()),
		var_to_tuple_adv(y, -F::one()),
	]);
	let inv = FpVar::new_witness(cs.clone(), || { Ok(inverse) }).unwrap();
	let lb_inv = var_to_lb(&inv, F::one());
	let z = FpVar::new_witness(cs.clone(), || {
        let xv = x.value().unwrap()-y.value().unwrap();
        if xv.is_zero() { Ok(F::one()) } else { Ok(F::zero()) }
    }).unwrap();
	let lb_z = var_to_lb(&z, F::one());
	let z_variable = fpvar_to_var(&z);

	//Constraint 1: (x-y)*inv = 1-z
	let lb_res = LinearCombination::<F>(vec![
		(F::one(), Variable::One),
		(-F::one(), z_variable)
	]);

	cs.enforce_constraint(
		lb_x_y.clone(),
		lb_inv,
		lb_res
	).unwrap();

    //Constraint 2: (x-y) * z = 0
	cs.enforce_constraint(
		lb_x_y,
		lb_z,
		lb_zero
	).unwrap();

	z
}

/// compared with is_zero_better, it provides a precomputed inverse value
pub fn is_zero_better_adv<F:PrimeField>(x: &FpVar<F>, inverse: &F, cs: &ConstraintSystemRef<F>)
->Result<FpVar<F>, SynthesisError>{
	let lb_zero= lc!();
	let z = FpVar::new_witness(cs.clone(), || {
        let xv = x.value()?;
        if xv.is_zero() { Ok(F::one()) } else { Ok(F::zero()) }
    })?;
	let inv = FpVar::new_witness(cs.clone(), || { Ok(inverse) })?;
    // Constraint 1: x * inv = 1 - z
	let lb_x = var_to_lb(x, F::one());
	let lb_z = var_to_lb(&z, F::one());
	let lb_inv = var_to_lb(&inv, F::one());
	let z_variable = fpvar_to_var(&z);
	//let lb_res = lb_one + (-F::one(), z_variable);
	let lb_res = LinearCombination::<F>(vec![
		(F::one(), Variable::One),
		(-F::one(), z_variable)
	]);
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


/// construct a variable if bvar=1, return v1 
/// otherwise return v2. Assumption: bvar is an int var either 1 or 0.
/// COST:  1
pub fn better_select<F:PrimeField>(bvar: &FpVar<F>, v1: &FpVar<F>, v2: &FpVar<F>)->FpVar<F>{
	let bval = bvar.value().unwrap();
	assert!(bval.is_zero() || bval.is_one());
	let val = if bval.is_one(){ v1.value().unwrap()} else {v2.value().unwrap()};
	let cs = bvar.cs();
	let var = new_var(&cs, val);
	//enforce bvar*(v1-v2) = v-v2;
	let lb_bvar = var_to_lb(bvar, F::one());
	let lb_v1 = var_to_lb(v1, F::one());
	let lb_neg_v2 = var_to_lb(v2, -F::one());
	let lb_var = var_to_lb(&var, F::one());
	cs.enforce_constraint(
		lb_bvar,
		lb_v1 + lb_neg_v2.clone(),
		lb_var + lb_neg_v2
	).unwrap();

	var
}
/// construct a variable if bvar=1, return v1 
/// otherwise return v2. Assumption: bvar is an int var either 1 or 0.
/// check that vres is the result
/// COST:  1
pub fn better_select_check<F:PrimeField>(bvar: &FpVar<F>, v1: &FpVar<F>, v2: &FpVar<F>, vres: &FpVar<F>)->Result<(),SynthesisError>{
	let bval = bvar.value().unwrap();
	assert!(bval.is_zero() || bval.is_one());
	let _val = if bval.is_one(){v1.value().unwrap()} else {v2.value().unwrap()};
	#[cfg(test)]{ assert!(_val==vres.value()?, "failed better select check"); }
	let cs = bvar.cs();
	//enforce bvar*(v1-v2) = v-v2;
	let lb_bvar = var_to_lb(bvar, F::one());
	let lb_v1 = var_to_lb(v1, F::one());
	let lb_neg_v2 = var_to_lb(v2, -F::one());
	let lb_var = var_to_lb(&vres, F::one());
	cs.enforce_constraint(
		lb_bvar,
		lb_v1 + lb_neg_v2.clone(),
		lb_var + lb_neg_v2
	).unwrap();

	Ok( () )
}

/// check the product of v1 and v2 is zero
/// cost is 1
pub fn check_prod_zero<F:PrimeField>(v1: &FpVar<F>, v2: &FpVar<F>, lb_zero: LinearCombination<F>, _msg: &str)
-> Result<(),SynthesisError>
{
	let cs = v1.cs();
	let lb_v1 = var_to_lb(v1, F::one());
	let lb_v2 = var_to_lb(v2, F::one());
	#[cfg(test)]{
		assert!(v1.value()? * v2.value()? == F::zero(), "ERR on check prod zero: {}", _msg); 
	}
	cs.enforce_constraint(
		lb_v1,
		lb_v2,
		lb_zero
	)?;
	Ok( () )
}


/// compute multiset_prod only counts sel[i] is 1.
/// sel is a "boolean" array.
/// COST: 3n
/// if unit var is a constant -> it's 2n
#[allow(dead_code)]
pub fn multiset_prod_2col<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	col1: &[FpVar<F>],
	col2: &[FpVar<F>],
	sel: &[FpVar<F>],
	r1: &FpVar<F>,
	unit_var: &FpVar<F>
)->FpVar<F>{
	let n = col1.len();
	let f_one = F::one();
	let lb_one = LinearCombination::from((F::one(),Variable::One));
	assert!(col2.len()==n && sel.len()==n);
	let mut prod = new_const_var(&cs, f_one);
	for i in 0..n{
		let v1 = r1 + &col1[i] + &(&col2[i] * unit_var);
		let v1_val = v1.value().unwrap();
		let sel_val = sel[i].value().unwrap();
		let item_val = if sel_val.is_zero() {f_one} else {v1_val};
		let item = new_var(&cs, item_val);

		prod = &prod * &item;

		//enforce that when 
		//	sel[i] is 0: item is 1 
		//  sel[i] is 1: item is  v1
		//  we have: 
		// sel*(item-val) + (1-sel)*(item-1)
		// sel*(1-val) + item-1 = 0;
		let lb_minus_val = var_to_lb(&v1, -F::one());
		let lb_minus_item = var_to_lb(&item, -F::one()); 
		let lb_sel = var_to_lb(&sel[i], F::one());
		cs.enforce_constraint(
			lb_sel,
			lb_one.clone() + lb_minus_val,
			lb_one.clone() + lb_minus_item
		).unwrap();

	}

	prod
}


/// compute Prod_{i=1}^n (vec[i] + r) ignore the entries that
/// has vec[i] = 0.
/// This is used to prove permutation.
///
/// COST 4*n
#[allow(dead_code)]
pub fn multiset_prod_ignore_zero<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	vec: &[FpVar<F>],
	r: &FpVar<F>
)->FpVar<F>{
	let bi_zero = vec.iter().map(|x| 
		is_zero_better(x, &cs).unwrap()
	).collect::<Vec<FpVar<F>>>();
	let r_val = r.value().unwrap();

	let mut prod = new_const_var(&cs, F::one());
	let lb_minus_one = LinearCombination::from((-F::one(),Variable::One));
	let lb_r= var_to_lb(r, F::one());
	for i in 0..vec.len(){
		//1. compute the value as non-deterministic witness var
		let vec_i_val = vec[i].value().expect("error val at i");
		let val = if vec_i_val.is_zero(){ F::one() }else{
			r_val + vec_i_val	
		};
		let item = new_var(&cs, val);

		//2. enforce the constraint on item (just need one constraint) 
		//enforce: bi_zero is 0, then item=1; bi_zero is 1, then item=r + vec[i]
		//this is:
		// bi_zero * (item-1) + (1-bi_zero)*(item - r - vec[i])
		// i.e., -bi_zero + item -r - vec[i] bi_zero * (r + vec[i]) = 0
		// i.e., bi_zero*(r + vec[i] -1) = r + vec[i] - item
		// this is just one constraint
		let lb_bi_zero = var_to_lb(&bi_zero[i], F::one()); 
		let lb_vec_i = var_to_lb(&vec[i], F::one());
		let lb_minus_item = var_to_lb(&item, -F::one());
		cs.enforce_constraint(
			lb_bi_zero,
			lb_r.clone() + lb_vec_i.clone() + lb_minus_one.clone(),
			lb_r.clone() + lb_vec_i + lb_minus_item
		).expect("enforce cs err");

		//3. update product
		prod = &prod * &item;
	}

	prod
}

/// compute Prod_{i=1}^n (vec[i] + r), (including those 0 entries)
///
/// COST 4*n
pub fn multiset_prod<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	vec: &[FpVar<F>],
	r: &FpVar<F>
)->FpVar<F>{
	let mut prod = new_const_var(&cs, F::one());
	for i in 0..vec.len(){
		prod = prod * (r + &vec[i]);
	}
	prod
}

/// compute the inverse
pub fn gen_vec_inverse<F:PrimeField>(vec: &Vec<F>)->Vec<F>{
	if vec.len()<16{
		vec.iter().map(|v| 
			if v.is_zero() {F::zero()} else {v.inverse().unwrap()}
		).collect::<Vec<F>>()
	}else{
		vec.par_iter().map(|v| 
			if v.is_zero() {F::zero()} else {v.inverse().unwrap()}
		).collect::<Vec<F>>()
	}
}

/// assert that vec is a sorted table and for non-zero elements
/// they are unique (distinct). We assume that vec_diff and vec
/// already have their SID columns in RANGE2. vec_diff[i] = vec[i+1]-vec[i].
/// vec_diff.len()==vec.len()=1. We assert that for each non zero
/// element vec[i], the vec_diff[i]!=0.
///
/// COST: 3*n
pub fn verify_unique_sorted_set<F:PrimeField>(vec: &[FpVar<F>],
	vec_diff: &[FpVar<F>])->Result<(),SynthesisError>{
	let n = vec.len();
	assert!(vec_diff.len()==n-1);
	let cs = vec[0].cs();
	let zero = new_const_var(&cs, F::zero());
	let lb_zero = var_to_lb(&zero, F::one());
	let vec_diff_val = vec_diff.iter().map(|x| x.value().unwrap())
		.collect::<Vec<F>>();
	let vec_inv = gen_vec_inverse(&vec_diff_val);
	for i in 0..n-1{
		let b_diff_zero = is_zero_better_adv(&vec_diff[i], &vec_inv[i], &cs)?;
		//let val = &union_key[i] * &b_diff_zero.into(); 
		//val.enforce_equal(&zero)?;
		//the following saves one constraint
		let lb_diff_zero = var_to_lb(&b_diff_zero.into(),F::one());
		let lb_vec_i= var_to_lb(&vec[i],F::one());
		cs.enforce_constraint(
			lb_diff_zero,
			lb_vec_i,
			lb_zero.clone()
		)?; //if union_key[i] is NOT zero, then union_key_diff[i] is NOT zero
	}
	Ok( () )
}


#[cfg(test)]
pub mod tests_commons{
	use ark_bn254::{Fr};
	use crate::gadgets::commons::{gen_m_table,encode_cols, decode_cols};

	#[test]
	fn test_gen_m_tbl(){
		let qry = vec![0, 3, 2, 5, 3].iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let lkup = vec![0, 0, 3, 5, 2, 2].iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		let m = gen_m_table(&qry, &lkup);
		let exp_m = vec![1, 0, 2, 1, 1, 0].iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		assert!(m==exp_m);
	}

	fn mysum(slice: &[Fr])->Fr{
		let mut res = Fr::from(0u32);
		for i in 0..slice.len(){
			res = res + slice[i];
		}
		res
	}

	#[test]
	fn test_temp(){//this is a simple test which checks if
		//conerting a vector to slice will blow up the stack
		let n = 1024 * 1024 * 16;
		let vec = vec![Fr::from(321); n];
		let _vec2 = vec[1..n].to_vec();
		let res = mysum(&vec);
		println!("ok: res: {}", res);
	}

	#[test]
	fn test_encode(){
		let vec1 = vec![Fr::from(15), Fr::from(16), Fr::from(17), Fr::from(18)];
		let vec2 = vec![Fr::from(25), Fr::from(26), Fr::from(27), Fr::from(27)];
		let vec3 = vec![Fr::from(35), Fr::from(36), Fr::from(37), Fr::from(38)];
		let vec = vec![vec1,vec2,vec3];
		let encoded = encode_cols(&vec, &vec![0,1,2]);
		let decoded = decode_cols(&encoded,3);
		assert!(decoded==vec);

		let vecs2 = vec![vec![Fr::from(9)], vec![Fr::from(0)], vec![Fr::from(0)], vec![Fr::from(0)], vec![Fr::from(0)]]; 
		let enc2 = encode_cols(&vecs2, &vec![0,1,2,3,4]);
		let dec2= decode_cols(&enc2, 5);
		assert!(dec2==vecs2);

	}
}
