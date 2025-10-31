/* Created 04/10/2025 */

/*! The module provides a number of structs and functions
related to relational database (mostly join, projection operations).
We have two cateogries of functions:
(1) create_prf(claim)->Container. Which generates proof for some claim.
    the proof is in the form of Container and attributes can be
	referenced by names. Note that the container is BUILT INTO
	part of the statement instance (i.e., fixed PART of witness)
	where a first pass of commit is run to allow msg2.
(2) verify_prf(claim, prf), and assert_claim(claim).
    These functions are to be called in assert_msg3().
	Note that they MIGHT generate R1CS variables as a part of msg3.
	Here: we are `lazy' here in the sense that we do NOT explicitly
	place these newly generated R1CS vars into gen_msg3(), as we did
	for CP related gadgets (when they are simple). So these functions
	should be regarded as two parts: (i) generate msg3 variables, e.g.,
	the inverse table for LOGUP, (ii) verify these `dynamically` generated
	values given msg2.
*/

use std::{rc::{Rc}, cell::{RefCell},collections::{HashSet}};
use ark_ff::{PrimeField};
use crate::gadgets::{traits::{Container,Col,IDX_DATA, IDX_SI_DATA}};
use ark_r1cs_std::{R1CSVar,alloc::AllocVar, eq::EqGadget,fields::FieldVar};
use ark_relations::r1cs::{SynthesisError,ConstraintSystemRef};
use ark_r1cs_std::fields::fp::FpVar;
use rayon::iter::{
	ParallelIterator,
	IntoParallelIterator,
	IntoParallelRefIterator,
	IndexedParallelIterator
};
use data_processor::clam_db::{RANGE2,RANGE2_BIT,check_pad_ratio};
use crate::gadgets::commons::{verify_inverse,verify_logup_inverse, check_eq, 
	check_arr_eq, check_arr_eq_arr, gen_m_table, new_const_var,
	encode_2col, encode_2col_var, gen_m_table_cond,
	new_var, two_col_tbl_to_sorted, gen_diff_col, two_col_tbl_left_join,
	encode_cols, encode_cols_var, 
	multiset_prod, verify_unique_sorted_set, is_zero_better,
	multiset_prod_2col};


// ----------------------------------------------------
//			Structs
// ----------------------------------------------------

// ----------------------------------------------------
//			Implementations and Functions	
// ----------------------------------------------------
/// assert that each element of qry belongs to lkup.
/// Note that both qry and lkup may contain multiple duplicates.
/// We use the Logup algorithm ([Hab22] `https://eprint.iacr.org/2022/1530`).
/// 
/// NOTE that there are two parts: using the Fiat-shamir challenge r,
/// generate the inverse table for qry and lkup, and then, check the m_tbl
/// relation: sum_{i=1}^{n} 1/(qry[i]+r) = sum_{j=1}^N m_tb[j]/(lkup[j]+r)
/// COST: 2*qry_size + 3*lkup_size  (if old version of
///		of verify_inverse and verify_logup_inverse used)
/// NEW COST: qry_size + 2 * lkup_size.
pub fn assert_logup<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	qry: &[FpVar<F>], 
	lkup: &[FpVar<F>],
	m_tbl: &[FpVar<F>], 
	r: &FpVar<F>)
->Result<(), SynthesisError>{
	//1. generte the inverse table (as part of msg3)
	let b_perf = false;
	let nc = cs.num_constraints();
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
	verify_logup_inverse(cs.clone(), &qry_inv, &lkup_inv, m_tbl)?; 

	if b_perf{
		println!(" --- assert_logup qry: {}, lkup: {}, cs: {}",
			qry.len(), lkup.len(), cs.num_constraints() - nc);
	}
	Ok( () )
}

/// assert_logup for the selector version.
pub fn assert_logup_cond<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	qry: &Vec<FpVar<F>>, 
	sel_qry: &Vec<FpVar<F>>, 
	lkup: &Vec<FpVar<F>>,
	sel_lkup: &Vec<FpVar<F>>,
	m_tbl: &Vec<FpVar<F>>, 
	r: &FpVar<F>)
->Result<(), SynthesisError>{
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
	let qry_inv_raw = qry_inv_val.iter().map(|x| FpVar::new_witness(
		cs.clone(), || Ok(x)).unwrap()).collect::<Vec<FpVar<F>>>();
	let qry_inv = qry_inv_raw.iter().zip(sel_qry.iter()).map(|(x,y)|
		x * y).collect::<Vec<FpVar<F>>>();
	let lkup_inv_raw = lkup_inv_val.iter().map(|x| FpVar::new_witness(
		cs.clone(), || Ok(x)).unwrap()).collect::<Vec<FpVar<F>>>();
	let lkup_inv = lkup_inv_raw.iter().zip(sel_lkup.iter()).map(|(x,y)|
		x * y).collect::<Vec<FpVar<F>>>();

	//2. verify inverse
	verify_inverse(cs.clone(), &qry, &qry_inv_raw, &r, qry.len())?;
	verify_inverse(cs.clone(), &lkup, &lkup_inv_raw, &r, lkup.len())?;

	//3. verify logup relation (m_table)
	verify_logup_inverse(cs.clone(), &qry_inv, &lkup_inv, m_tbl)?; 

	Ok( () )
}

/// verify that encoded col is the encoding of the columns in vec_src.
/// the number of bits for each field (usually, pass RANGE2_BIT) 
pub fn verify_encoded_table<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	unit_bits: usize,
	vec_src: &Vec<&Vec<FpVar<F>>>, 
	encoded: &Vec<FpVar<F>>,
) ->Result<(), SynthesisError>{
	//1. set up base data. 
	let n = vec_src[0].len();
	for i in 0..vec_src.len(){assert!(vec_src[i].len()==n);}
	assert!(encoded.len()==n);
	let f_unit = FpVar::new_constant(cs.clone(), F::from(1u32<<unit_bits))?; 

	//2. verify for each row
	for i in 0..n{
		let mut expected = FpVar::new_witness(cs.clone(), || Ok(F::zero()))?;
		for j in 0..vec_src.len(){
			expected = &(&expected * &f_unit)  + &vec_src[j][i];
		}
		check_eq(&expected, &encoded[i], "checking exp")?;
	}

	Ok( () )
}

/// Assert a table is well formed, i.e.,
/// for the same key, id increaes from 0 to count+1.
/// for 0 and count+1 (idx) entries, val1 is 0 and MAX respectively.
/// NOTICE that we only need to check val1 (even if there might be multiple
/// value columns), IF the encoded table is verified to be subsegements
/// of external lookup table (which ensures that all other value columns are
/// MAX as well due to encoded).
/// When sid_sort_diff is some, it also asserted that the val1 column
/// in each subsegement (by keys) is sorted, by checking that sid column
/// for the cell difference is contained in RANGE2 table (i.e., non-negative)
/// When sort_diff_key is Some, it verifies that key col is in the
/// asencding order. This is useful when the table is NOT a part of
/// a verified external table, this guarantees UNIQUE KEY.
/// NOTE: zero entries (key=0) are ignored (as they are dummy entry)
///
/// COST: 9n
pub fn assert_well_formed_sorted<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	key: &Vec<FpVar<F>>,
	id: &Vec<FpVar<F>>,
	val1: &Vec<FpVar<F>>,
	sort_diff: Option<&Vec<FpVar<F>>>, //the pair-wise diff of val1 (n-1)
	sid_sort_diff: Option<&Vec<FpVar<F>>>, //len n (n-1)
	sort_diff_key: Option<&Vec<FpVar<F>>>,//diff of key (n-1)
	sid_diff_key: Option<&Vec<FpVar<F>>>, //sid for the above
	r: FpVar<F>, //the random challenge
	state_part_bits: usize,
)->Result<(),SynthesisError>{
	let b_relaxed = false;

	assert_well_formed_sorted_adv(cs.clone(), key, id, val1,
		sort_diff, sid_sort_diff, sort_diff_key, sid_diff_key,
		r, state_part_bits, b_relaxed)
}

/// An advanced version of assert_well_forned_sorted.
/// When b_relaxed is set (sid_sort and sid_diff) must be off.
/// b_relaxed means that when key is the same, the id either remains or 
/// increase by 1. Still entries are wrapped with two dummy entries
pub fn assert_well_formed_sorted_adv<F:PrimeField>(
	cs: ConstraintSystemRef<F>,
	key: &Vec<FpVar<F>>,
	id: &Vec<FpVar<F>>,
	val1: &Vec<FpVar<F>>,
	sort_diff: Option<&Vec<FpVar<F>>>, //the pair-wise diff of val1 (n-1)
	sid_sort_diff: Option<&Vec<FpVar<F>>>, //len n (n-1)
	sort_diff_key: Option<&Vec<FpVar<F>>>,//diff of key (n-1)
	sid_diff_key: Option<&Vec<FpVar<F>>>, //sid for the above
	r: FpVar<F>, //the random challenge
	state_part_bits: usize,
	b_relaxed: bool
)->Result<(),SynthesisError>{
	// IDEA: basically we are enforcing two cases:
	// (1) regular case:  key[i]-key[i-1] = 0 \and id[i]-id[i-1] = 1 
	// (2) border case: key[i]\neq key[i-1]: val1[i-1] = max and id[i]=0
	// note that we do not even have to check val1[i]=0 because lookup into
	// an external container tale guarantees that when id[i]=0, all VALs are 0 (dummy
	// low value). But we do have to check val1[i-1]=max as we canont tell
	// from id[i-1] it's the max possible id for the previous key.
	//
	// Now since key, id, val1 are ALREADY located in the FIXED segment
	// before msg2. We can actually use "r" to perform fingerprinting
	// random combination of zero values to save cost.
	// compared with the naive algorithm, the fingerprint algorithm
	// costs (5  vs 12 per row), [for case sid_sort_diff is none]
	// with check sort and ignore zero entries it's 7 constraints per row.

	//0. quick check of data
	let n = key.len();
	assert!(id.len()==n && val1.len()==n);
	if b_relaxed {assert!(!sort_diff.is_some()  && !sort_diff_key.is_some())};
	let max_val:usize = (1<<state_part_bits) - 1;
	let zero = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	let one = FpVar::<F>::new_constant(cs.clone(), F::one())?;
	let max = FpVar::<F>::new_constant(cs.clone(), F::from(max_val as u32))?;
	let _rg2 = FpVar::<F>::new_constant(cs.clone(), F::from(RANGE2))?;
	check_eq(&id[0], &zero, "check id0")?;
	let b_check_sort = sid_sort_diff.is_some();
	let b_check_sort_key = sid_diff_key.is_some();
	if b_check_sort{
		let sort_diff = sort_diff.unwrap();
		assert!(sort_diff.len()==val1.len()-1);
		let exp_val1 = val1.iter().zip(sort_diff.iter()).map(|(a,b)|{
			a + b
		}).collect::<Vec<FpVar<F>>>();
		check_arr_eq_arr(&val1[1..], &exp_val1[0..n-1], "err diff")?;
	}
	if b_check_sort_key{
		let sort_diff_key = sort_diff_key.unwrap();
		assert!(sort_diff_key.len()==key.len()-1);
		let exp_key = key.iter().zip(sort_diff_key.iter()).map(|(a,b)|{
			a + b
		}).collect::<Vec<FpVar<F>>>();
		check_arr_eq_arr(&key[1..], &exp_key[0..n-1], "err diff key")?;
		//simply check here all are in ascending order
		//we do not have the value problem ascending by chunks
		//this is ascending along the entire column.
		//NOT needed as it's constant
		//check_arr_eq(&sid_diff_key.unwrap(), &rg2, "err sid_sort key")?; 
	}

	// -------------------------------------------------------
	// naive algorithm: avg 12 constraints per ROW of table
	// -------------------------------------------------------
// 	let n1 = cs.num_constraints();
// 	for i in 1..n{
// 		let b_same_key = key[i].is_eq(&key[i-1])?; //boolean var - cost: 3
// 		let id_same = (&id[i]-&id[i-1]).is_eq(&one)?; // cost: 3
// 		let val_same = val1[i].is_eq(&max)?; // cost: 3
// 		let b_case1 = b_same_key.and(&id_same)?; //cost: 1
// 		let b_case2 = b_same_key.not().and(&val_same)?; //cost: 1
// 		let b_res = b_case1.or(&b_case2)?; //cost: 2
// 		b_res.enforce_equal(&Boolean::TRUE)?; //cost: 1
// 	}
// 	let n2 = cs.num_constraints();


	// finger printing algorithm
	let mut sum = zero.clone();
	let f_rg2= F::from(RANGE2);
	let vec_sid_diff = if sid_sort_diff.is_some(){
		let sid_s2 = sid_sort_diff.unwrap();
		assert!(sid_s2.len()==key.len()-1);
		sid_s2.iter().map(|x| x.clone()-f_rg2).collect::<Vec<_>>()
	}else{vec![zero.clone(); key.len()-1]};
	for i in 1..n{
		let b_same_key = key[i].is_eq(&key[i-1])?; 
		let bk: FpVar<F> = b_same_key.into();
		let id_diff = &id[i]-&id[i-1]-&one;
		let val_diff = &val1[i-1]-&max;
		//NOTE: bk is either 0 or 1 (already asserted as boolean)
		//bk=0 implies id_diff is 0
		//bk=1 implies val[i-1]=max and val[i]=0
		//this implies res =0, we use random combination to enforce all RES are 0
		//outside of loop
		let res = if !b_check_sort{ 
			if !b_relaxed{
				//NOTE: if key[i-1]=0, we regard it as dummy entry so do NOT
				//enforce the rule that res be 0.
				// technically, when key[i-1]=0, its 
				// id and val entries for key 0 can be 
				// anything, because they are ignored. but when we generate
				// table, we make them 0.
				let part2 = &val_diff + &(&r * &val1[i]);
				&key[i-1]*(&bk * &id_diff + &(&one-&bk)*&part2)
			}else{//b_relaxed mode
				//part1 means id[i]-id[i-1] is either 1 or 0
				let part1 = &id_diff * &(&id[i]-&id[i-1]);
				let part2 = &val_diff + &(&r * &val1[i]);
				&key[i-1]*(&bk * &part1+ &(&one-&bk)*&part2)
			}
		} else {//this is only checked when b_relaxed is false
			#[cfg(test)] {assert!(!b_relaxed);}
			let sid_diff = &vec_sid_diff[i-1];
			let part1 = &id_diff + &(sid_diff* &r);
			let part2 = &val_diff + &(&r * &val1[i]);
			let res = &key[i-1] * &(&bk * &part1 + &(&one-&bk)*&part2);

			res
		};
		sum = &sum * &r + &res;
	}
	check_eq(&sum, &zero, "check sum fails")?;
	
	Ok( () )
}

/// from a column of values, generated a sorted set
/// <id, val>
/// or ascending order over value. Assuming all value in RANGE2 which
/// is proved already.
/// If target_n is larger, pad with (0,0) entries at the beginning
/// of the resulting table.
/// It also includes prf which includes the following columns
/// neighbor_diff: whose length is target_n-1.
/// We simply labor each element as in RANGE2 (for positive).
/// NOTE that zero is regarded as padding value.
pub fn col_to_sorted_set<F:PrimeField>(
	col: &Rc<RefCell<Container<F>>>,  //container to a vec
	target_n: usize, //target set size
	name: &str, //name of container
) ->Rc<RefCell<Container<F>>>{
	//0. prepare data
	let res = Container::new(name);
	res.borrow_mut().add_container(col.clone());
	let max_val:usize = (1<<RANGE2_BIT) - 1; //state_part_bit is RANGE2_BIT
	let max = F::from(max_val as u32);
	let zero = F::zero();

	//1. extract the set of non-zero values and non-max values generate
	// the sorted_src which is zero padded at the beginning
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max2 = F::from(max_val as u32);
	let src = col.borrow().to_vec();
	let mut set_src = src.par_iter().filter(|x| !x.is_zero() && **x!=max2)
		.map(|x| x.clone()).collect::<HashSet<F>>()
		.par_iter().map(|x| x.clone()).collect::<Vec<F>>();
	set_src.sort();

	let real_len = set_src.len();
	assert!(target_n>=real_len+2,
	  "col_to_sort_set: target_n: {} < set_src+2: {}",
	  	target_n, set_src.len());
	let num_zero = target_n - set_src.len() - 1; //need 0 padding and max
	let sorted_val = vec![ vec![zero; num_zero], set_src, vec![max]].concat();

	//2. generated the ID col. padded with zero and the diff
	let ids_part2 = (1..real_len+2).collect::<Vec<_>>().par_iter().map(|x|
		F::from(*x as u32)).collect::<Vec<F>>();
	let ids = vec![ vec![zero; num_zero], ids_part2].concat();
	assert!(ids.len()==sorted_val.len());

	let diffs = (1..target_n).collect::<Vec<_>>().par_iter().map(|i|
		sorted_val[*i] - sorted_val[*i-1]).collect::<Vec<F>>();

	//3. create the mtables. m_tbl1: look extended src into sorted_val
	// m_tbl2: look sorted_val into extended_src.
	let src_len = src.len();
	let extended_src = vec![src, vec![zero, max]].concat();
	let m_tbl1 = gen_m_table(&extended_src, &sorted_val);
	let m_tbl2 = gen_m_table(&sorted_val, &extended_src);

	//3. generate the cols
	let vec2d = vec![ids, sorted_val, diffs, m_tbl1, m_tbl2];
	let names = vec!["id", "sorted_val", "diff", "mtbl_1", "mtbl_2"];
	let lens = vec![target_n, target_n, target_n-1, target_n, src_len+2];
	let cols = vec2d.into_iter().zip(names.clone().into_iter()).map(|(c,n)|
		Col::new(c, n, IDX_DATA)).collect::<Vec<Rc<RefCell<Col<F>>>>>();
	let f_rg2= F::from(RANGE2);
	let vec2d_sid = vec![ 
		vec![f_rg2; target_n],  //sid
		vec![f_rg2; target_n],  //sid_sorted_val
		vec![f_rg2; target_n-1], //sid_diff
		vec![f_rg2; target_n], //sid_mtbl_1
		vec![f_rg2; src_len+2], //sid_mtbl_2
	];
	let cols_sid = vec2d_sid.into_iter().zip(names.into_iter()).map(|(c,n)|
		Col::new(c, &format!("sid_{}",n), IDX_SI_DATA))
		.collect::<Vec<Rc<RefCell<Col<F>>>>>();
	for i in 0..cols.len(){
		assert!(cols[i].borrow().data.len()==lens[i]);
		assert!(cols_sid[i].borrow().data.len()==lens[i]);
	}
	let to_add = vec![cols, cols_sid].concat();
	//adding clone of Rc does not cost much
	for i in 0..to_add.len() {res.borrow_mut().add_col(to_add[i].clone());}

	res
}

/// verify a col_to_sorted_set bundle is correct
/// we take advantage the fact in assert3(), randoms from msg2 can
/// be used given that src info (to be verified) are all locaed in stmt/msg1
/// which are fixed.
/// COST: 7m + 14n (where m is the len of larger src_col, n is the size of
///     the compressed sorted set)
pub fn verify_col_to_sorted_set<F:PrimeField>(
	r: &FpVar<F>,
	c: &Container<FpVar<F>>, 
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	//1. retrieve the src data colomn and other cols
	let src_data = c.get_container_by_idx(0); 
	let src_col = src_data.borrow().to_vec();
	let id = c.get_container("id")?.borrow().to_vec();
	let sorted_val = c.get_container("sorted_val")?.borrow().to_vec();
	let diff = c.get_container("diff")?.borrow().to_vec();
	let mtbl_1= c.get_container("mtbl_1")?.borrow().to_vec();
	let mtbl_2= c.get_container("mtbl_2")?.borrow().to_vec();
	let sid_id = c.get_container("sid_id")?.borrow().to_vec();
	let sid_sorted_val = c.get_container("sid_sorted_val")?.borrow().to_vec();
	let sid_diff = c.get_container("sid_diff")?.borrow().to_vec();
	let sid_mtbl_1= c.get_container("sid_mtbl_1")?.borrow().to_vec();
	let sid_mtbl_2= c.get_container("sid_mtbl_2")?.borrow().to_vec();

	//2. check the sid columns (all in RANGE2): cost 4m+n
	let rg2 = FpVar::new_constant(cs.clone(), F::from(RANGE2))?;
	check_arr_eq(&sid_id, &rg2, "error sid_id")?; 
	check_arr_eq(&sid_sorted_val, &rg2, "error sid_sorted_val")?; 
	check_arr_eq(&sid_diff, &rg2, "error sid_diff")?; 
	check_arr_eq(&sid_mtbl_1, &rg2, "error sid_mtbl1")?; 
	check_arr_eq(&sid_mtbl_2, &rg2, "error sid_mtbl2")?; 

	//3. check the validity diff column: cost:m 
	let n = sorted_val.len();
	assert!(diff.len()==n-1);
	let vec_sum = diff.iter().zip(sorted_val.iter()).map(|(a,b)|
		a + b).collect::<Vec<FpVar<F>>>();
	check_arr_eq_arr(&vec_sum, &sorted_val[1..n], "failed diff check")?;

	//4. lookup: cost 5(m+n): m: source data, n: target_set_size
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let zero = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
	let max = FpVar::<F>::new_constant(cs.clone(), F::from(max_val as u32))?;
	let extended_src = vec![src_col, vec![zero.clone(),max]].concat();
	assert_logup(cs.clone(), &extended_src, &sorted_val, &mtbl_1, r)?;
	assert_logup(cs.clone(), &sorted_val, &extended_src, &mtbl_2, r)?;

	//5. verify the ID column: cost: 4n
	let diff_id = (1..id.len()).collect::<Vec<_>>().iter().map(|i|
		&id[*i] - &id[*i-1]).collect::<Vec<FpVar<F>>>();
	let one = FpVar::<F>::new_constant(cs.clone(), F::one())?;
	//when val is 0 it should be 0, otherwise it is 1, do this again using
	//random combination which is cheaper.
	let mut res = zero.clone();
	for i in 0..diff_id.len(){
		//NOTE that we've already proved that val is ascending.
		//if val is 0 -> diff_id MUST be 0.
		//if val is not 0 -> diff_id MUST be 1.
		let item1 = &(&one-&sorted_val[i+1]) * &diff_id[i];
		res = &(&res * r) + &item1;
		let item2 = &sorted_val[i+1] * &(&one - &diff_id[i]);
		res = &(&res * r) + &item2;
	}

	Ok( () )
}


/// Prove that the tag is the correct tagging of each element
/// of the key array (if it is a valid element in sorted_key).
/// We assume that sorted_key is a sorted set of unique elements
/// padded with 0 at the beginning (where 0 is regarded as dummy).
/// Key can be arbitrary order and allow duplicates, the tag has 1 or 0
/// indicating that element is in sorted_key. Note that 0 is NOT regarded
/// as a part of sorted key.
///
/// Example
/// given sorted key: (0,1,2,3)
/// given key (4,0,1,1,3) the tag vec is (0,0,1,1,1)
/// where for key element 0, its tag is 0.
pub fn prove_filter_tag<F:PrimeField>(
	key: &Vec<F>, sorted_key: &Vec<F>, tags: &Vec<F>,
	unique_key_size: usize,
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	//0. check data
	let (_n, m, k) = (key.len(), unique_key_size, sorted_key.len());
	#[cfg(test)]{
		assert!(tags.len()==_n);
		for i in 0.._n{
			assert!(tags[i].is_zero() || tags[i].is_one());
		}
		for i in 0..k-1{
			assert!(sorted_key[i].is_zero() ||
				sorted_key[i] < sorted_key[i+1]);
		}
	}
	//1. generate neg set of unique_key_size
	let prf = Container::<F>::new("prf_tag");
	let no_key_set = key.par_iter().zip(tags.par_iter()).filter(|(&k,&t)|{
		k.is_zero() || t.is_zero()	
	}).map(|(&k,_)|{
		k
	}).collect::<HashSet<F>>();
	let mut no_key:Vec<F> = no_key_set.iter().cloned().collect();
	assert!(no_key.len()<m, "no_key.len: {} should < unique_set_size: {}",
		no_key.len(), m);
	no_key.sort();
	no_key = vec![vec![F::zero(); m-no_key.len()], no_key].concat();

	//2. generate union of key
	let mut union_key = [&no_key[..], &sorted_key[..]].concat();
	union_key.sort();
	assert!(union_key.len()==m+k);

	//3. prove union_key is sorted. provide the the pairwise diff
	//as the proof.
	let union_key_diff = (0..m+k-1).into_par_iter().map(|i|
		union_key[i+1]-union_key[i]
	).collect::<Vec<F>>();

	//4. prove union_key is the union of no_key and sorted_key.
	//NOW given: (1) sorted-key is sorted unique set, (2) union_key
	// is hte union or sorted_key and no_key and its size is the
	// sum of two. We can infer that: no_key is union_key - sorted_key
	// and then no_key's is DISJOINT with sorted key.

	//5. produce m_table for proving that (key,tag) belong to
	// the following concat table:
	//  [ (no_key, 0), (sorted_key, 1 except for 0 entries)]
	let qry = encode_2col(&key, &tags);
	let no_key_tag = vec![F::zero(); no_key.len()];
	let sorted_key_tag = sorted_key.iter().map(|x| 
		if x.is_zero() {F::zero()} else {F::one()}
	).collect::<Vec<F>>();
	let lkup = vec![encode_2col(&no_key, &no_key_tag),
		encode_2col(&sorted_key, &sorted_key_tag)].concat();
	let m_tbl = gen_m_table(&qry, &lkup);
	assert!(m_tbl.len()==m+k);


	//6. return
	let (zero,rg2) = (F::zero(), F::from(RANGE2));
	assert!(no_key.len()==m && union_key.len()==m+k 
		&& union_key_diff.len()==m+k-1);
	prf.borrow_mut().add_col(Col::new(no_key, "no_key", IDX_DATA));
	prf.borrow_mut().add_col(Col::new(vec![rg2;m], "si_no_key", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(union_key, "union_key", IDX_DATA));
	prf.borrow_mut().add_col(Col::new(vec![rg2;m+k], 
		"si_union_key", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(union_key_diff, 
		"union_key_diff", IDX_DATA));
	prf.borrow_mut().add_col(Col::new(vec![rg2;m+k-1], 
		"si_union_key_diff", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(m_tbl, "m_tbl", IDX_DATA));
	prf.borrow_mut().add_col(Col::new(vec![zero;m+k], 
		"si_m_tbl", IDX_SI_DATA));

	Ok(prf)
}

/// verify the given tags is the correct tagging of key
/// for its elements in sorted_key or not.
///
/// COST: 3*(m+k-1) + 2*(m+k) -1 + 2n + 2m + 5k
/// = 2n + 7m + 10k
pub fn verify_filter_tag<F:PrimeField>(
	key: &Vec<FpVar<F>>, sorted_key: &Vec<FpVar<F>>, tags: &Vec<FpVar<F>>,
	prf: &Rc<RefCell<Container<FpVar<F>>>>,
	r1: &FpVar<F>,
	r2: &FpVar<F>
)->Result<(), SynthesisError>{
	let b_perf = false;
	let cs = key[0].cs();
	let mut nc = cs.num_constraints();

	//1-2. retrieve neg_key and union key
	let cols = ["no_key", "union_key", "union_key_diff", "m_tbl"].iter().map(|n|
		prf.borrow().get_container(n).unwrap().borrow().to_vec())
		.collect::<Vec<_>>();
	let (no_key, union_key, union_key_diff, m_tbl) = (&cols[0],
		&cols[1], &cols[2], &cols[3]);
	let (n,m,k) = (key.len(), no_key.len(), sorted_key.len());
	if b_perf {
		println!("-- -- verify_filter_tag: step 1: key.len: {}, sorted_key.len: {}, no_key.len: {}, cs: {}", n, k, m, cs.num_constraints()-nc);
		nc = cs.num_constraints();
	}

	//3. veify union_key is sorted.
	// COST = 3*(m+k-1)
	verify_unique_sorted_set(&union_key, &union_key_diff)?;
	if b_perf{
		println!("-- -- verify_filter_tag: step 3: cs: {}",
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//4. VERIFY that union_key is the union of no_key and sorted_key.
	//NOW given: (1) sorted-key is sorted unique set, (2) union_key
	// is hte union or sorted_key and no_key and its size is the
	// sum of two. We can infer that: no_key is union_key - sorted_key
	// and then proved the following:
	// *** no_key's is DISJOINT with sorted key. ***

	// COST: 2*(m+k)-1
	let prod1 = multiset_prod(cs.clone(),
		&union_key, r1);
	let q1 = multiset_prod(cs.clone(),
		&sorted_key, r1);
	let q2 = multiset_prod(cs.clone(),
		&no_key, r1);
	let prod2 = q1 * q2;
	prod2.enforce_equal(&prod1)?;
	if b_perf{
		println!("-- -- verify_filter_tag: step 4: cs: {}",
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//5. verify the (key,tag) as a 2-column table can be looked up
	//in (union_key,tag) properly tagged.
	//COST: n + 3k + n + 2*(m+k)
	// = 2*n + 2*m + 5*k 
	let qry = key.iter().zip(tags.iter()).map(|(k,t)|
		k + r1 * t).collect::<Vec<FpVar<F>>>();
	// tbl_1: (no_key,0) is itself as r1 * 0 is 0
	// tbl_2: sorted_key_tag is 0 if sorted_key[i] is 0 o.t. 1
	let tbl_2 = sorted_key.iter().map(|x|{
		let b_zero = is_zero_better(x, &cs).unwrap();
		x + r1 - r1 * &b_zero 
	}).collect::<Vec<FpVar<F>>>();
	let lkup = [&no_key[..], &tbl_2[..]].concat();
	assert!(lkup.len()==m+k);
	assert_logup(cs.clone(), &qry, &lkup, &m_tbl, r2)?;
	if b_perf{
		println!("-- -- verify_filter_tag: step 5: cs: {}",
			cs.num_constraints() - nc);
	}

	Ok( () )
}

/// convert two column (unsorted) table to a sorted and well
/// formed table, the the result of projection by a sorted_set of keys.
/// The sorted_set-key is a sorted set of key values (as the
/// result of col_to_sorted_set).
/// For multiple key/value columns, this function can be re-used
/// by encoding multiple fields into ONE, assuming column(cell) values
/// in certain bound, such as RANGE2 (24-bits in default setting).
///
/// It returns a well-formed (entries padded with 0 and max dummy entries),
/// and sorted table (val in ascending order). 
///
/// It returns the bundle that includes the sorted table (key: "sorted_tbl")
/// and the corresponding proof (key: "prf")
pub fn tbl_filtered_to_sorted_tbl<F:PrimeField>(
	key: &Rc<RefCell<Container<F>>>,
	val: &Rc<RefCell<Container<F>>>,
	sorted_set_key: &Rc<RefCell<Container<F>>>, //the sorted_set bundle
		//this is used to FILTER the (key,val) pair, e.g., key has
		//states, but sorted_set_key has FINAL STATES only.
	target_size: usize,
	name: &str, //the name of the new container bundle
	unique_key_size: usize, //when pack key to unique set, what's the size
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	let b_new = true;
	if b_new{
		tbl_filtered_to_sorted_tbl_new(key,val,sorted_set_key,target_size,name,
			unique_key_size)
	}else{
		tbl_filtered_to_sorted_tbl_old(key,val,sorted_set_key,target_size,name)
	}
}

// new approach: We first provie a 
pub fn tbl_filtered_to_sorted_tbl_new<F:PrimeField>(
	key: &Rc<RefCell<Container<F>>>,
	val: &Rc<RefCell<Container<F>>>,
	sorted_set_key: &Rc<RefCell<Container<F>>>, //the sorted_set bundle
		//this is used to FILTER the (key,val) pair, e.g., key has
		//states, but sorted_set_key has FINAL STATES only.
	target_size: usize,
	name: &str, //the name of the new container bundle
	unique_key_size: usize, //when pack key to unique set, what's the size
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	let res = Container::<F>::new(name);
	let sorted_tbl = Container::new("sorted_tbl");

	//Part I. establish the tag column to indicate
	//whether the key is in sorted_key_set (filter)
	//1.1 extract the data columns
	let keys = key.borrow().to_vec(); 
	let vals = val.borrow().to_vec(); 
	let proj_keys = sorted_set_key.borrow().get_container(
		"sorted_val")?.borrow().to_vec();

	let (m,n,k) = (keys.len(), target_size, proj_keys.len());
	assert!(vals.len()==m);
	println!("DEBUG USE 6101: m: {}, n: {}, k: {}", m, n, k);

	//1.2 try to tag each key
	// in_sorted_set_key: 1
	// not_in_sorted_set_key: 0
	// don't care (for dummy entries): 0
	let (f_in, f_out, f_dummy) = (F::from(1u32), F::zero(), F::zero());
	let tags = keys.par_iter().map(|k|{
		if k.is_zero(){ f_dummy} else{
			if proj_keys.contains(k){ f_in }else { f_out }
		}
	}).collect::<Vec<F>>();
	let si_tags = vec![F::zero(); tags.len()];//boolean, will be checked 
												//so just use don't care
	//1.3 prove that the tag is correct
	let prf_tag = prove_filter_tag(&keys, &proj_keys, &tags, unique_key_size)?;

	//PART 2. constuct the filtered and sorted table and prove that
	//its correctness
	//2.1 build the sorted-table. consists of
	// packed_key, packed_id, packed_val
	// diff_key, diff_val (to prove they are sorted and well formed) 
	let fil1 = keys.par_iter().zip(tags.par_iter()).filter(|(_k,t)|{
		!t.is_zero()
	}).map(|(k,_)| k.clone()).collect::<Vec<F>>();
	let fil2 = vals.par_iter().zip(tags.par_iter()).filter(|(_v,t)|{
		!t.is_zero()
	}).map(|(v,_)| v.clone()).collect::<Vec<F>>();
	let (packed_key,packed_id,packed_val)=two_col_tbl_to_sorted(&fil1,&fil2,n);

	let f_rg = F::from(RANGE2);
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let tbl_names = vec!["packed_key", "packed_id", "packed_val"];
	let zero = F::zero();
	let packed_diff = (1..packed_val.len()).collect::<Vec<_>>()
		.into_par_iter().map(|i| packed_val[i] - packed_val[i-1])
		.collect::<Vec<_>>();
	
	let diff_key= (1..packed_key.len()).collect::<Vec<_>>()
		.into_par_iter().map(|i| packed_key[i] - packed_key[i-1])
		.collect::<Vec<_>>();
	let sid_packed_diff = (1..packed_val.len()).into_iter().map(|i|{
		let res = if packed_diff[i-1]<max {f_rg} else {zero} ;
		res
	}).collect::<Vec<_>>();

	let sid_diff_key= vec![f_rg; sid_packed_diff.len()];
	assert!(packed_diff.len()==sid_packed_diff.len());
	assert!(diff_key.len()==sid_diff_key.len());


	//4. now basically do a filtered multi-set "permutation" check.
	//no additional proof needed, just do it on the verifier side

	//5. return (make sure data col and its sid col are added in
	// the right order).
	res.borrow_mut().add_col(Col::new(tags, "tags", IDX_DATA));
	res.borrow_mut().add_col(Col::new(si_tags, "si_tags", IDX_SI_DATA));
	res.borrow_mut().add_container(prf_tag);

	sorted_tbl.borrow_mut().add_col(Col::new(packed_key,"packed_key",IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(packed_id,"packed_id",IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(packed_val,"packed_val",IDX_DATA));
	assert!(tbl_names.len()==3);
	for i in 0..tbl_names.len(){
		sorted_tbl.borrow_mut().add_col(Col::new(vec![f_rg; n],
			&format!("sid_{}", tbl_names[i]), IDX_SI_DATA));
	}


	sorted_tbl.borrow_mut().add_col(Col::new(diff_key,"diff_key",IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(sid_diff_key, "sid_diff_key", IDX_SI_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(packed_diff,"packed_diff"
		,IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(sid_packed_diff, "sid_packed_diff", IDX_SI_DATA));
	res.borrow_mut().add_container(sorted_tbl);

	Ok(res)
}


//old version more costly
pub fn tbl_filtered_to_sorted_tbl_old<F:PrimeField>(
	key: &Rc<RefCell<Container<F>>>,
	val: &Rc<RefCell<Container<F>>>,
	sorted_set_key: &Rc<RefCell<Container<F>>>, //the sorted_set bundle
		//this is used to FILTER the (key,val) pair, e.g., key has
		//states, but sorted_set_key has FINAL STATES only.
	target_size: usize,
	name: &str, //the name of the new container bundle
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	let res = Container::new(name);
	let sorted_tbl = Container::new("sorted_tbl");
	let prf = Container::new("prf");

	//1. extract the data columns
	let keys = key.borrow().to_vec(); 
	let vals = val.borrow().to_vec(); 
	let proj_ids = sorted_set_key.borrow().get_container(
		"id")?.borrow().to_vec();
	let proj_keys = sorted_set_key.borrow().get_container(
		"sorted_val")?.borrow().to_vec();

	let (m,n,k) = (keys.len(), target_size, proj_keys.len());
	assert!(vals.len()==m);

	//2. do the binary search and build up proof for filter
	let tuples = keys.par_iter().zip(vals.par_iter()).map(|(key,val)|{
		let res = proj_keys.binary_search(key);
		let (sel_key, id) = match res{
			Ok(pos) => {
				assert!(pos<k && pos>0);
				(true, pos)
			},
			Err(pos) => {
				assert!(pos<k && pos>0);
				(false, pos-1)
			}
		};
		let (val1, val2) = (proj_keys[id], proj_keys[id+1]);
		let (diff1, diff2) = (*key-val1, val2-*key);
		assert!(diff1.is_zero() == sel_key);
		//NOTE: no need to save sel_key as verifier can build it.

		let f_id = proj_ids[id];
		let tp = vec![f_id, val1, val2, diff1, diff2, *key, *val];
		//key, val located at idx 5 and 6. diff1 located at 4

		tp	
	}).collect::<Vec<_>>();

	let (f_rg, f_1) = (F::from(RANGE2), F::one());
	let mut names = vec!["id", "val1", "val2", "diff1", "diff2"];
	let mut cols_prf_src = (0..names.len()).collect::<Vec<_>>()
	.into_iter().map(|i|{
		tuples.par_iter().map(|t| t[i]).collect::<Vec<F>>()	
	}).collect::<Vec<Vec<F>>>();
	assert!(cols_prf_src[0].len()==m);
	//diff1 serves as selector, 0 means in
	let (one,zero) = (F::one(),F::zero());
	let sel_src = cols_prf_src[3].iter().map(|x|
		if x.is_zero() {one} else {zero}
	).collect::<Vec<F>>();
	let encoded_src = encode_2col(&keys, &vals);

	
	let id_1 = cols_prf_src[0].par_iter().map(|x| *x+f_1).collect::<Vec<_>>();
	let qry = vec![
		encode_2col(&cols_prf_src[0], &cols_prf_src[1]),  //(id,val1)
		encode_2col(&id_1, &cols_prf_src[2]), //(id,val2)
	].concat();
	let lkup = encode_2col(&proj_ids, &proj_keys);
	let m_tbl_sorted_set = gen_m_table(&qry, &lkup);
	assert!(m_tbl_sorted_set.len() ==k);
	names.push("m_tbl_sorted_set");
	cols_prf_src.push(m_tbl_sorted_set);
	assert!(cols_prf_src.len()==names.len());

	//3. build the filtered table padded to target_size
	// (key, id, val)
	let filtered_tuples =  tuples.par_iter().filter(|t|{
		let diff1 = t[3];
		diff1.is_zero() //means the key is in the sorted_set
	}).map(|t|
		(t[5], t[6])
	).collect::<Vec<_>>();
	let fil1= filtered_tuples.par_iter().map(|x| x.0).collect::<Vec<F>>();
	let fil2 = filtered_tuples.par_iter().map(|x| x.1).collect::<Vec<F>>();
	let (packed_key,packed_id,packed_val)=two_col_tbl_to_sorted(&fil1,&fil2,n);
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let sel_dst = packed_val.iter().map(|v|
		*v * (max-v) //when v is 0 or max, it disables selection
	).collect::<Vec<F>>();
	let encoded_dst = encode_2col(&packed_key, &packed_val);
	let tbl_names = vec!["packed_key", "packed_id", "packed_val"];
	let zero = F::zero();
	let packed_diff = (1..packed_val.len()).collect::<Vec<_>>()
		.into_par_iter().map(|i| packed_val[i] - packed_val[i-1])
		.collect::<Vec<_>>();
	
	let diff_key= (1..packed_key.len()).collect::<Vec<_>>()
		.into_par_iter().map(|i| packed_key[i] - packed_key[i-1])
		.collect::<Vec<_>>();
	let sid_packed_diff = (1..packed_val.len()).into_iter().map(|i|{
		let res = if packed_diff[i-1]<max {f_rg} else {zero} ;

		res
	}).collect::<Vec<_>>();

	let sid_diff_key= vec![f_rg; sid_packed_diff.len()];
	assert!(packed_diff.len()==sid_packed_diff.len());
	assert!(diff_key.len()==sid_diff_key.len());

	sorted_tbl.borrow_mut().add_col(Col::new(packed_key,"packed_key",IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(packed_id,"packed_id",IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(packed_val,"packed_val",IDX_DATA));
	assert!(tbl_names.len()==3);
	for i in 0..tbl_names.len(){
		prf.borrow_mut().add_col(Col::new(vec![f_rg; n],
			&format!("sid_{}", tbl_names[i]), IDX_SI_DATA));
	}
	sorted_tbl.borrow_mut().add_col(Col::new(packed_diff,"packed_diff"
		,IDX_DATA));
	sorted_tbl.borrow_mut().add_col(Col::new(diff_key,"diff_key",IDX_DATA));
	prf.borrow_mut().add_col(Col::new(sid_packed_diff, "sid_packed_diff", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(sid_diff_key, "sid_diff_key", IDX_SI_DATA));

	//4. build the prf part for filtering
	let cols = cols_prf_src.into_iter().zip(names.iter()).map(|(c,n)|{
		let (nlen, sid_name) = (c.len(), format!("sid_{}", n));
		let sid_vec = vec![f_rg; nlen];
		(Col::new(c, n, IDX_DATA), Col::new(sid_vec, &sid_name, IDX_SI_DATA))
	}).collect::<Vec<_>>();
	for i in 0..cols.len(){
		prf.borrow_mut().add_col(cols[i].0.clone()); //clone rc low cost
		prf.borrow_mut().add_col(cols[i].1.clone());
	}

	//5. build the prf part for the sorted_tabble
	let mtbl_src_dst = gen_m_table_cond(&encoded_src, &sel_src, 
		&encoded_dst, &sel_dst);
	let mtbl_dst_src = gen_m_table_cond(&encoded_dst, &sel_dst, 
		&encoded_src, &sel_src);

	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_src_dst.len()],
		"sid_mtbl_src_dst", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_dst_src.len()],
		"sid_mtbl_dst_src", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_src_dst,"mtbl_src_dst",IDX_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_dst_src, "mtbl_dst_src",IDX_DATA));

	res.borrow_mut().add_container(sorted_tbl);
	res.borrow_mut().add_container(prf);
	Ok( res )
}

pub fn verify_tbl_filtered_to_sorted_tbl<F:PrimeField>(
	r1: &FpVar<F>, //random challenges from msg2
	r2: &FpVar<F>,
	keys: &Rc<RefCell<Container<FpVar<F>>>>,
	vals: &Rc<RefCell<Container<FpVar<F>>>>,
	sorted_set_key: &Rc<RefCell<Container<FpVar<F>>>>, //the sorted_set bundle
	bundle: &Rc<RefCell<Container<FpVar<F>>>>, //result of tbl_filtered_to_sorted_tbl
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	let b_new = true;
	if b_new{
		verify_tbl_filtered_to_sorted_tbl_new(r1,r2,keys,vals,
			sorted_set_key,bundle,cs)
	}else{
		verify_tbl_filtered_to_sorted_tbl_old(r1,r2,keys,vals,
			sorted_set_key,bundle,cs)
	}
}

/// new version which is much less costly.
///
/// COST: 2N + 7m + 10k + 3n + 11n + 6n + 3N
/// = 5N + 17n + 7m + 10k
/// where N: keys, n: sorted_tbl.len, m: unique_state_size: k: sorted_set size
/// n is determined by basis_pats_per_traces, m determined by 
///  basis_unique_states
pub fn verify_tbl_filtered_to_sorted_tbl_new<F:PrimeField>(
	r1: &FpVar<F>, //random challenges from msg2
	r2: &FpVar<F>,
	keys: &Rc<RefCell<Container<FpVar<F>>>>,
	vals: &Rc<RefCell<Container<FpVar<F>>>>,
	sorted_set_key: &Rc<RefCell<Container<FpVar<F>>>>, //the sorted_set bundle
	bundle: &Rc<RefCell<Container<FpVar<F>>>>, //result of tbl_filtered_to_sorted_tbl
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	let b_perf = false;
	let mut nc = cs.num_constraints();
	let nc0 = nc;
	let sorted_tbl= bundle.borrow().get_container("sorted_tbl")?;
	if b_perf{
		println!(" --- verify_tbl_filtered_new N: {}, n: {}, m: {}, k: {}", 
			keys.borrow().to_vec().len(), 
			sorted_tbl.borrow().
				get_container("packed_key")?.borrow().to_vec().len(),
			bundle.borrow().
				get_container("prf_tag")?.borrow().
				get_container("no_key")?.borrow().to_vec().len(),
			sorted_set_key.borrow().get_container("sorted_val")?.
				borrow().to_vec().len());
	}

	//Part I. establish the tag column to indicate
	//whether the key is in sorted_key_set (filter)
	//COST: 2N + 7m + 10k
	// N = key.len
	// n = sorted_table.packed_key.len (determined by basis_pats_in_trace)
	// m = unique_key_size (detremined by basis_unique_states)
	// k = sorted_set_key.len (determined by pat_per_subsig * subsigs)
	let keys = keys.borrow().to_vec();
	let vals= vals.borrow().to_vec();
	let sorted_keys = sorted_set_key.borrow().get_container("sorted_val")?
		.borrow().to_vec(); 
	let tags = bundle.borrow().get_container("tags")?.borrow().to_vec();
	let prf_tag = bundle.borrow().get_container("prf_tag")?;
	verify_filter_tag(&keys, &sorted_keys, &tags, &prf_tag, r1, r2)?;
	if b_perf{
		println!(" --- verify_tbl_filtered_new keys step 1: {}: ",
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//PART 2. constuct the filtered and sorted table and prove that
	//its correctness
	//2.1 retrieve data and check sids 
	//COST: 3n
	let rg = new_const_var(&cs, F::from(RANGE2));
	let names = vec!["packed_key", "packed_id", "packed_val"];
	let sids1 = names.iter().map(|n| 
		sorted_tbl.borrow().get_container(&format!("sid_{}",n))
		.expect(&format!("err get {}", n))).collect::<Vec<_>>();
	for vs in &sids1{check_arr_eq(&vs.borrow().to_vec(), &rg, "err sid")?; }
	let tblcols = names.iter().map(|n|
		sorted_tbl.borrow().get_container(n).expect("err get tbl"))
		.collect::<Vec<_>>();
	let sid_sorted_diff = sorted_tbl.borrow_mut().get_container("sid_packed_diff")?
		.borrow().to_vec();
	let sid_diff_key= sorted_tbl.borrow_mut().get_container("sid_diff_key")?
		.borrow().to_vec();
	if b_perf{
		println!("  --- verify_tbl_filtered_new keys: step 2.1  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//2.2 check sorted_tbl is well_formed and sorted
	//COST: 11n
	let packed_vals = tblcols[2].borrow().to_vec();
	let packed_keys= tblcols[0].borrow().to_vec();
	let diff_val = (1..packed_vals.len()).collect::<Vec<_>>()
		.into_iter().map(|i|{
			&packed_vals[i] - &packed_vals[i-1]
		}).collect::<Vec<_>>();
	let diff_key = (1..packed_keys.len()).collect::<Vec<_>>()
		.into_iter().map(|i|{
			&packed_keys[i] - &packed_keys[i-1]
		}).collect::<Vec<_>>();

	assert_well_formed_sorted(cs.clone(),
		&tblcols[0].borrow().to_vec(), //packed_key
		&tblcols[1].borrow().to_vec(), //id
		&packed_vals, //val
		Some(&diff_val),
		Some(&sid_sorted_diff), //sid of diff col
		Some(&diff_key),
		Some(&sid_diff_key),
		r1.clone(), 
		RANGE2_BIT)?;
	if b_perf{
		println!("  --- verify_tbl_filtered_new keys: step 2.2  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}



	//2.3. to show that the sorted table is a VALID projection (filtered)
	//version of the (key,val) table.
	// Basically we do a filtered multi-set "permutation" check.
	//no additional proof needed, just do it on the verifier side
	// IDEA:
	// for (key, val, tag)  we are computing the PRODUCT of
	// each item. 
	// It is already proved that tag is 0 or 1 so the formula for
	// item is:
	// ------------------------------
	// (r1 + key + r2 * val) for tag 1
	// and 1 for tag 0
	// ------------------------------
	// this is:
	// DEFINE t1 = r1 + key + r2 * val; 
	// we have: tag * (item-t1) + (1-tag)*(item-1)
	// where tag*(1-t1) + item - 1 = 0
	// which is 2 constraints each (plus one constraint for
	// computing product) -> 3 constraints.
	//
	// for the right side. we are checking (key,val) for 
	// those items val!=0 and val!=max
	// define tag = (val-0)*(val-max) != 0 [costing two constraints]
	// then 3 more constraints for the same. But sinc ethe right table
	// is small, this is acceptable.
	// COST: 6n + 3N

	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let (vone, vmax) = (new_const_var(&cs, F::one()), new_const_var(&cs, max)); 
	let tag_sorted_tbl = packed_vals.iter().map(|v|{
		&vone - &is_zero_better(&(v * (v-&vmax)), &cs ).unwrap()
	}).collect::<Vec<FpVar<F>>>();
	if b_perf{
		println!("  --- verify_tbl_filtered_new keys: step 2.3.1  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	let v1 = multiset_prod_2col(cs.clone(), &packed_keys, &packed_vals,
		&tag_sorted_tbl, r1, r2);
	if b_perf{
		println!("  --- verify_tbl_filtered_new keys: step 2.3.2  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	let v2 = multiset_prod_2col(cs.clone(), &keys, &vals,
		&tags, r1, r2);
	if b_perf{
		println!("  --- verify_tbl_filtered_new keys: step 2.3  cs: {}", 
			cs.num_constraints() - nc);
		println!("  --- verify_tbl_filered_new TOTAL: {}", 
			cs.num_constraints()-nc0);
	}
	check_eq(&v1, &v2, "failed multiset eq check")?;
	Ok( () )
}


/// old version
/// COST around 20 * max_nibble_len
pub fn verify_tbl_filtered_to_sorted_tbl_old<F:PrimeField>(
	r1: &FpVar<F>, //random challenges from msg2
	_r2: &FpVar<F>,
	keys: &Rc<RefCell<Container<FpVar<F>>>>,
	vals: &Rc<RefCell<Container<FpVar<F>>>>,
	sorted_set_key: &Rc<RefCell<Container<FpVar<F>>>>, //the sorted_set bundle
	bundle: &Rc<RefCell<Container<FpVar<F>>>>, //result of tbl_filtered_to_sorted_tbl
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	let b_perf = false;
	let mut nc = cs.num_constraints();
	let nc0 = nc;
	if b_perf{
		println!(" --- verify_tbl_filtered_old keys: {}, sorted_keys: {}", 
			keys.borrow().to_vec().len(), 
			sorted_set_key.borrow().to_vec().len());
	}

	// ----- Part 1: verify the filtering of src (key,val) ---
	//1.1 get all data to verify
	let keys = keys.borrow().to_vec();
	let vals = vals.borrow().to_vec();
	let names = vec!["id","val1","val2","diff1","diff2","m_tbl_sorted_set"];
	let proj_ids = sorted_set_key.borrow().get_container(
		"id")?.borrow().to_vec();
	let proj_keys = sorted_set_key.borrow().get_container(
		"sorted_val")?.borrow().to_vec();
	let prf = bundle.borrow().get_container("prf")?;
	let sorted_tbl= bundle.borrow().get_container("sorted_tbl")?;
	let ct = names.iter().map(|n| 
		prf.borrow().get_container(n).expect(&format!("err get {}", n))
		.borrow().to_vec()).collect::<Vec<_>>();
	let (id,val1,val2,diff1,diff2,m_tbl_sorted_set) = (ct[0].clone(), 
		ct[1].clone(), ct[2].clone(), ct[3].clone(), ct[4].clone(),
		ct[5].clone()); //rc clone low cost
	let sids = names.iter().map(|n| 
		prf.borrow().get_container(&format!("sid_{}",n))
		.expect(&format!("err get {}", n))).collect::<Vec<_>>();

	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 1.1  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//1.2 check sids
	let rg = new_const_var(&cs, F::from(RANGE2));
	let zero= new_const_var(&cs, F::zero());
	for vs in &sids{ check_arr_eq(&vs.borrow().to_vec(), &rg, "err sid")?; }
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 1.2  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//1.3. check val1==key-diff1, val2==key+diff2
	let exp_val1 = keys.iter().zip(diff1.iter()).map(|(v,d)| v-d)
		.collect::<Vec<FpVar<F>>>();
	let exp_val2 = keys.iter().zip(diff2.iter()).map(|(v,d)| v+d)
		.collect::<Vec<FpVar<F>>>();
	check_arr_eq_arr(&exp_val1, &val1, "err checking val1")?;
	check_arr_eq_arr(&exp_val2, &val2, "err checking val2")?;
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 1.3  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//1.4 verify (id,val1) and (id+1,val2) all belong to sorted_set
	let one_var = new_const_var(&cs, F::one());
	let id_1 = id.iter().map(|x| &one_var + x).collect::<Vec<_>>(); 
	let qry = vec![
		encode_2col_var(&id, &val1), 
		encode_2col_var(&id_1, &val2)
	].concat();
	let lkup = encode_2col_var(&proj_ids, &proj_keys);
	assert_logup(cs.clone(), &qry, &lkup, &m_tbl_sorted_set, r1)?;
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 1.4  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}
		
	// ----- Part 2: verify the resulting well formed table
	//2.1 check sids 
	let names = vec!["packed_key", "packed_id", "packed_val"];
	let sids1 = names.iter().map(|n| 
		prf.borrow().get_container(&format!("sid_{}",n))
		.expect(&format!("err get {}", n))).collect::<Vec<_>>();
	let sids2 = vec!["mtbl_src_dst", "mtbl_dst_src"].iter().map(|n|
		prf.borrow().get_container(&format!("sid_{}",n))
		.expect(&format!("err get {}", n))).collect::<Vec<_>>();
	for vs in &sids1{check_arr_eq(&vs.borrow().to_vec(), &rg, "err sid")?; }
	for vs in &sids2{check_arr_eq(&vs.borrow().to_vec(), &zero, "err sid")?; }
	let tblcols = names.iter().map(|n|
		sorted_tbl.borrow().get_container(n).expect("err get tbl"))
		.collect::<Vec<_>>();
	let sid_sorted_diff = prf.borrow_mut().get_container("sid_packed_diff")?
		.borrow().to_vec();
	let sid_diff_key= prf.borrow_mut().get_container("sid_diff_key")?
		.borrow().to_vec();
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 2.1  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//2.2 check the sorted_tbl is well formed and sorted
	let packed_vals = tblcols[2].borrow().to_vec();
	let packed_keys= tblcols[0].borrow().to_vec();
	let diff_val = (1..packed_vals.len()).collect::<Vec<_>>()
		.into_iter().map(|i|{
			&packed_vals[i] - &packed_vals[i-1]
		}).collect::<Vec<_>>();
	let diff_key = (1..packed_keys.len()).collect::<Vec<_>>()
		.into_iter().map(|i|{
			&packed_keys[i] - &packed_keys[i-1]
		}).collect::<Vec<_>>();

	assert_well_formed_sorted(cs.clone(),
		&tblcols[0].borrow().to_vec(), //packed_key
		&tblcols[1].borrow().to_vec(), //id
		&packed_vals, //val
		Some(&diff_val),
		Some(&sid_sorted_diff), //sid of diff col
		Some(&diff_key),
		Some(&sid_diff_key),
		r1.clone(), 
		RANGE2_BIT)?;
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 2.2  cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}

	//2.3 do the double direction lookup to assert all (state,loc)
	//appears appropraitely in the sorted table (state, id, loc)
	//and vice versa.
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = new_var(&cs, F::from(max_val as u32));
	let encoded_src = encode_2col_var(&keys, &vals);
	let encoded_dst = encode_2col_var(&packed_keys, &packed_vals);
	let sel_src = ct[3].iter().map(|x| {
		x.is_zero().unwrap().into() }).collect::<Vec<FpVar<F>>>(); 
	let sel_dst = packed_vals.iter().map(|v|
		v * &(&max - v)).collect::<Vec<FpVar<F>>>();
	let mtbl_src_dst = prf.borrow().get_container("mtbl_src_dst")?
		.borrow().to_vec();
	let mtbl_dst_src= prf.borrow().get_container("mtbl_dst_src")?
		.borrow().to_vec();

	assert_logup_cond(cs.clone(), &encoded_src, &sel_src, &encoded_dst, &sel_dst, &mtbl_src_dst, r1)?;
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 2.3 cs: {}", 
			cs.num_constraints() - nc);
		nc = cs.num_constraints();
	}
	assert_logup_cond(cs.clone(), &encoded_dst, &sel_dst, &encoded_src, &sel_src, &mtbl_dst_src, r1)?;
	if b_perf{
		println!("  --- verify_tbl_filtered_old keys: step 2.4  cs: {}", 
			cs.num_constraints() - nc);
		println!("  --- # verify_tbl_filtered_old total: {}", 
			cs.num_constraints() - nc0);
	}

	Ok( () )
}

/// This is a simplified version of tbl_filter_to_sorted_tbl without
/// filtering step. Given 2 columns, compress all pairs to unique
/// and organize them as sorted table of form (key-id-val) which is well
/// formed and key column is sorted.
pub fn tbl_to_sorted_tbl<F:PrimeField>(
	key: &Rc<RefCell<Container<F>>>,
	val: &Rc<RefCell<Container<F>>>,
	target_size: usize,
	name: &str, //the name of the new container bundle
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	//1. generating the resulting table (data column and sid columns)
	let (zero,_one) = (F::zero(), F::one());
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let res = Container::<F>::new(name);
	let sorted_tbl = Container::<F>::new("sorted_tbl");
	let prf = Container::<F>::new("prf");
	let keys = key.borrow().to_vec();
	let vals = val.borrow().to_vec();
	let f_rg = F::from(RANGE2); 
	let (sorted_key, sorted_id, sorted_val)
		=two_col_tbl_to_sorted(&keys, &vals, target_size);
	let encoded_dst = encode_2col(&sorted_key, &sorted_val);
	let sel_dst = sorted_key.iter().zip(sorted_val.iter()).map(|(x,y)|
		*x * (max - *x) * (*y) * (max-*y)).collect::<Vec<F>>();
	let n = sorted_key.len();
	let (sid_sorted_key, sid_sorted_id, sid_sorted_val) =( 
		vec![f_rg;n], vec![f_rg; n], vec![f_rg; n]); 
	let (diff_key, sid_diff_key) = gen_diff_col(&sorted_key);
	let (diff_val, sid_diff_val) = gen_diff_col(&sorted_val);

	//2. prove that the resulting table is well formed and
	// key and val sorted
	let s_names = vec!["sorted_key", "sorted_id", "sorted_val"];
	let d_names = vec!["diff_key", "diff_val"];
	vec![sorted_key, sorted_id, sorted_val].into_iter().zip(s_names.iter())
	.for_each(|(c,n)| {
		sorted_tbl.borrow_mut() .add_col(Col::new(c, n, IDX_DATA));
	});
	vec![sid_sorted_key, sid_sorted_id, sid_sorted_val].into_iter()
	.zip(s_names.iter()).for_each(|(c,n)|{
		prf.borrow_mut().add_col(Col::new(c, &format!("sid_{}",n),IDX_SI_DATA));
	});
	vec![diff_key, diff_val].into_iter().zip(d_names.iter()).for_each(|(c,n)|{
		prf.borrow_mut().add_col(Col::new(c, &format!("{}",n),IDX_DATA));
	});
	vec![sid_diff_key, sid_diff_val].into_iter().zip(d_names.iter())
	.for_each(|(c,n)|{
		prf.borrow_mut().add_col(Col::new(c, &format!("sid_{}",n),IDX_SI_DATA));
	});

	//3. lkup in both directions (ignore 0 entries).
	let encoded_src = encode_2col(&keys, &vals);
	let sel_src = keys.iter().zip(vals.iter()).map(|(x,y)|
		*x * (max-*x) * (*y * (max-*y))
	).collect::<Vec<F>>();

	let mtbl_src_dst = gen_m_table_cond(&encoded_src, &sel_src, 
		&encoded_dst, &sel_dst);
	let mtbl_dst_src = gen_m_table_cond(&encoded_dst, &sel_dst, 
		&encoded_src, &sel_src);

	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_src_dst.len()],
		"sid_mtbl_src_dst", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_dst_src.len()],
		"sid_mtbl_dst_src", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_src_dst,"mtbl_src_dst",IDX_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_dst_src, "mtbl_dst_src",IDX_DATA));



	//4. return
	res.borrow_mut().add_container(sorted_tbl);
	res.borrow_mut().add_container(prf);

	Ok(res)
}

/// verify in assert_msg3() that  
pub fn verify_tbl_to_sorted_tbl<F:PrimeField>(
	r1: &FpVar<F>, //random challenges from msg2
	_r2: &FpVar<F>,
	keys: &Rc<RefCell<Container<FpVar<F>>>>,
	vals: &Rc<RefCell<Container<FpVar<F>>>>,
	bundle: &Rc<RefCell<Container<FpVar<F>>>>, //result of tbl_to_sorted_tbl_
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	//1. prove that the resulting table is well formed 
	let keys = keys.borrow().to_vec();
	let vals = vals.borrow().to_vec();
	let prf = bundle.borrow().get_container("prf")?;
	let sorted_tbl = bundle.borrow().get_container("sorted_tbl")?;
	let cols_prf = vec!["diff_val","sid_diff_val","diff_key","sid_diff_key"]
		.iter().map(|n| prf.borrow().get_container(n)
			.expect(&format!("can't find {}",n)).borrow().to_vec())
		.collect::<Vec<Vec<FpVar<F>>>>();

	let sel_keys=sorted_tbl.borrow().get_container_by_idx(0).borrow().to_vec();
	let sel_ids=sorted_tbl.borrow().get_container_by_idx(1).borrow().to_vec();
	let sel_vals=sorted_tbl.borrow().get_container_by_idx(2).borrow().to_vec();
	assert_well_formed_sorted(cs.clone(),
		&sel_keys,
		&sel_ids,
		&sel_vals,
		Some(&cols_prf[0]), //diff_val
		Some(&cols_prf[1]), //sid_diff_val
		Some(&cols_prf[2]), //diff_key
		Some(&cols_prf[3]), //sid_diff_key
		r1.clone(), 
		RANGE2_BIT)?;

	//2. check sid columns (f_rg) but don't have to check those zeros,
	// e.g., those m_tbl values' sid
	// ALSO Note sid_diff_key and sid_diff_val is already checked
	// in assert_well_formed_sorted. So we only need to check sid for
	// sorted_key, id, val.
	let f_rg = new_var(&cs, F::from(RANGE2)); 
	let sid_names = vec!["sorted_key", "sorted_id", "sorted_val"];
	let scols= sid_names.iter().map(|n|
			prf.borrow().get_container(&format!("sid_{}",n))
			.unwrap().borrow().to_vec()
		).collect::<Vec<Vec<FpVar<F>>>>();
	for i in 0..scols.len(){
		check_arr_eq(&scols[i], &f_rg,&format!("sid err: {}", sid_names[i]))?;
	}
	//sid_diff_val needs needs special treatment

	//3. check logups (bi-directional) - conditional means
	// to ignore zero entries
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = new_const_var(&cs, F::from(max_val as u32));
	let encoded_src = encode_2col_var(&keys, &vals);
	let encoded_dst = encode_2col_var(&sel_keys, &sel_vals);

	let mtbl_src_dst = prf.borrow().get_container("mtbl_src_dst")?
		.borrow().to_vec();
	let mtbl_dst_src= prf.borrow().get_container("mtbl_dst_src")?
		.borrow().to_vec();
	let sel_src = keys.iter().zip(vals.iter()).map(|(x,y)| {
		x * &(&max-x) * &(y * &(&max-y))
	}).collect::<Vec<FpVar<F>>>(); 
	let sel_dst = sel_keys.iter().zip(sel_vals.iter()).map(|(x,y)|
		x * &(&max-x) * &(y * &(&max-y))).collect::<Vec<FpVar<F>>>();

	assert_logup_cond(cs.clone(), &encoded_src, &sel_src, &encoded_dst, &sel_dst, &mtbl_src_dst, r1)?;
	assert_logup_cond(cs.clone(), &encoded_dst, &sel_dst, &encoded_src, &sel_src, &mtbl_dst_src, r1)?;

	Ok( () )
}

/// Left join of two sorted tables each with two columsn.
/// We assume that these two tables are already well formed and sorted (both
/// key and val). Note that it's a left join, even if one entry in tbl1
/// does not have an entry in tbl2, it will have two dummy (0, max) records.
/// Application example: tbl1: (pat-state), tble2 (state-loc). 
/// Example:
/// tbl1                 tbl2
/// k1 id1 val1          k2 id2 val2
/// 1  0    0            100 0   0
/// 1  1    100          100 1   20
/// 1  2    max          100 2   max
/// 2  0    0
/// 2  1    200
/// 2  2    max
/// It results in (using val1/k2 as join column)
/// k1  id1 k2  id2  val
/// 1   0   0    0   0
/// 1   0   0    0   max 
/// 1   1   100  0   0
/// 1   1   100  1  20
/// 1   1   100  2  max
/// 1   2   max  0   0  
/// 1   2   max  0   max  
/// 2   0   0    0   0 
/// 2   0   0    0   max  
/// 2   1   200    0   0 
/// 2   1   200    0   max  
/// 2   2   max		0   0 
/// 2   2   max		0   max  
/// NOTE: the result table is NOT necessarily sorted over key.
/// But it is WELL formed regarding last 3 columns, and
/// well formed also for first 3 columns (in some relaxed sense that
/// when key is the same, id increases by 0 or 1).
/// As usual prepadded by 0 entries.
pub fn tbl_left_join<F:PrimeField>(
	tbl1: &Rc<RefCell<Container<F>>>, //needs to be sorted_tbl
	tbl2: &Rc<RefCell<Container<F>>>, //needs to be sorted_tbl
	sorted_set_key2: &Rc<RefCell<Container<F>>>, //sorted set of key2
			//in our scenario, it's already computed in caller.
			//otherwise, it can be generated in the function
	target_size: usize,
	name: &str, //the name of the new container bundle
) -> Result<Rc<RefCell<Container<F>>>, SynthesisError>{
	//1. generate the resulting table
	let (zero, one) = (F::zero(), F::one());
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = F::from(max_val as u32);
	let res = Container::<F>::new(name);
	let f_rg = F::from(RANGE2); 
	let join_tbl= Container::<F>::new("join_tbl");
	let prf = Container::<F>::new("prf");
	let tbl1_cols = (0..3).into_iter().map(|i| tbl1.borrow()
		.get_container("sorted_tbl").expect("err get sort_tbl").borrow()
		.get_container_by_idx(i).borrow().to_vec()).collect::<Vec<Vec<F>>>();
	let tbl2_cols = (0..3).into_iter().map(|i| tbl2.borrow()
		.get_container("sorted_tbl").expect("err get sort_tbl").borrow()
		.get_container_by_idx(i).borrow().to_vec()).collect::<Vec<Vec<F>>>();


	let tbl_res = two_col_tbl_left_join(&tbl1_cols, &tbl2_cols, target_size);
	check_pad_ratio(&tbl_res[0], "FsmAdvCapaicty.basis_pats_in_trace");
	assert!(tbl_res.len()==5);

	//2. lkup tbl1 in first 3 columns (guarantees tbl1 left join covered)
	let tbl1_encoded = encode_cols(&tbl1_cols, &vec![0,1,2]);
	let tbl1_sel = tbl1_cols[0].par_iter().map(|x| 
		if x.is_zero() {zero} else {one}).collect::<Vec<F>>();

	let res_firsthalf_encoded = encode_cols(&tbl_res, &vec![0,1,2]); 
	let res_firsthalf_sel = tbl_res[0].par_iter().map(|x|
		if x.is_zero() {zero} else {one}).collect::<Vec<F>>();
	let mtbl_tbl1_res = gen_m_table_cond(&tbl1_encoded, &tbl1_sel,
		&res_firsthalf_encoded, &res_firsthalf_sel);
	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_tbl1_res.len()],
		"sid_mtbl_tbl1_res", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_tbl1_res,"mtbl_tbl1_res",IDX_DATA));

	//3. lkup first 3 column in tbl1 (guarnatee no extra) 
	let mtbl_res_tbl1= gen_m_table_cond( 
		&res_firsthalf_encoded, &res_firsthalf_sel, &tbl1_encoded, &tbl1_sel);
	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_res_tbl1.len()],
		"sid_mtbl_res_tbl1", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_res_tbl1,"mtbl_res_tbl1",IDX_DATA));

	//4. relaxed well formed check of first 3 column (combining with 2)
	// needed for making sure expanding value column is correct
	// otherwise entries could be for different (k1,k2) pairs.
	// we do NOT have to check if key is sorted and no need to check
	// val is sorted as the first 3 column is already proved to be
	// contained in tbl1, as the relaxed well-formedness already guarantees
	// that for a key, an adversary prover cannot insert or delete
	// entries for a key (as all first 3 column entries must be in tbl1),
	// the well-formnedness guaranees that dummy (0-max entries wrapped 
	// around). Since we do not enforce key sorted, therefore full mapping
	// of tbl1 are preserved, but adversary prover can insert DUPLICATED
	// entries (expanded with join), but this only comes at the cost of
	// proving, but does not affect soundness of the proof.
	// * as there is no additional diff col needed for sorting, no
	// * additional proof data needs to be generated

	//5. lkup last 3 columns in tbl2 (one direction only)
	//NOTE: tbl2 need to be PADDED with sorted_set_key2 dummy entries
	//for left-join of those who do not appear in tbl2.
	let sorted_set_key2 = sorted_set_key2.borrow().get_container_by_idx(2)
		.borrow().to_vec();//note col #2 is the val of sorted set
	let sn = sorted_set_key2.len();
	let tbl2_pad = vec![
		sorted_set_key2.par_iter().map(
			|x| vec![*x,*x])
			.collect::<Vec<Vec<F>>>().concat(),
		vec![vec![zero,one]; sn].concat(),
		vec![vec![zero,max]; sn].concat()
	];
	assert!(tbl2_cols.len()==3);
	let tbl2_cols = tbl2_cols.into_iter().zip(tbl2_pad.into_iter())
		.map(|(v1,v2)|{
			vec![v1, v2].concat()
		}).collect::<Vec<Vec<F>>>();
	let tbl2_encoded = encode_cols(&tbl2_cols, &vec![0,1,2]);
	let tbl2_sel = tbl2_cols[0].par_iter().map(|x| 
		if x.is_zero() {zero} else {one}).collect::<Vec<F>>();
	assert!(tbl2_encoded.len()==tbl2_sel.len());
	let res_sechalf_encoded = encode_cols(&tbl_res, &vec![2,3,4]); 
	let res_sechalf_sel = tbl_res[2].par_iter().map(|x|
		if x.is_zero() {zero} else {one}).collect::<Vec<F>>();
	let mtbl_sechalf_tbl2= gen_m_table_cond(
		&res_sechalf_encoded, &res_sechalf_sel, &tbl2_encoded, &tbl2_sel);

	prf.borrow_mut().add_col(Col::new(vec![zero; mtbl_sechalf_tbl2.len()],
		"sid_mtbl_sechalf_tbl2", IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(mtbl_sechalf_tbl2,"mtbl_sechalf_tbl2"
		,IDX_DATA));

	//6. check last3 column is of res_tbl well formed (
	// combined with 5 makes sure
	// that the expansion of (k1,k2) is complete. because the two dummy
	// entries are verified to be in tbl2. Note: no need on key
	let (diff_val, sid_diff_val) = gen_diff_col(&tbl_res[4]);
	prf.borrow_mut().add_col(Col::new(sid_diff_val,"sid_diff_val",IDX_SI_DATA));
	prf.borrow_mut().add_col(Col::new(diff_val,"diff_val",IDX_DATA));


	//7. build the join_tbl and its sids
	let join_tbl_names = vec!["key", "id1", "key2", "id2", "val"];
	let vec_c_len = tbl_res.iter().map(|c| c.len()).collect::<Vec<usize>>();
	tbl_res.into_iter().zip(join_tbl_names.iter()).for_each(|(c,n)|{
		join_tbl.borrow_mut().add_col(Col::new(c, n, IDX_DATA));
	});
	vec_c_len.iter().zip(join_tbl_names.iter()).for_each(|(l,n)|{
		join_tbl.borrow_mut().add_col(Col::new(vec![f_rg;*l],
			&format!("sid_{}",n), IDX_SI_DATA));
	});


	res.borrow_mut().add_container(join_tbl);
	res.borrow_mut().add_container(prf);
	Ok(res)
}

/// verify in assert_msg3() that  
pub fn verify_tbl_left_join<F:PrimeField>(
	r1: &FpVar<F>, //random challenges from msg2
	r2: &FpVar<F>,
	tbl1: &Rc<RefCell<Container<FpVar<F>>>>,
	tbl2: &Rc<RefCell<Container<FpVar<F>>>>,
	sorted_set_key2: &Rc<RefCell<Container<FpVar<F>>>>, //sorted set of key2
	output: &Rc<RefCell<Container<FpVar<F>>>>,  //the output table
	cs: ConstraintSystemRef<F>
) -> Result<(), SynthesisError>{
	//1. retrieve data
	let max_val:usize = (1<<RANGE2_BIT) - 1;
	let max = new_const_var(&cs, F::from(max_val as u32));
	let (zero,one)=(new_const_var(&cs,F::zero()),new_const_var(&cs,F::one()));
	let join_tbl= output.borrow().get_container("join_tbl")?;
	let prf = output.borrow().get_container("prf")?;
	let tbl1_cols = (0..3).into_iter().map(|i| tbl1.borrow()
		.get_container("sorted_tbl").expect("err get sort_tbl").borrow()
		.get_container_by_idx(i).borrow().to_vec())
		.collect::<Vec<Vec<FpVar<F>>>>();
	let tbl2_cols = (0..3).into_iter().map(|i| tbl2.borrow()
		.get_container("sorted_tbl").expect("err get sort_tbl").borrow()
		.get_container_by_idx(i).borrow().to_vec())
		.collect::<Vec<Vec<FpVar<F>>>>();
	let names = vec!["key", "id1", "key2", "id2", "val"];
	let tbl_res = names.iter().map(|n|
		join_tbl.borrow().get_container(n).unwrap()
		.borrow().to_vec()).collect::<Vec<Vec<FpVar<F>>>>();

	//2. verify tbl1 in first 3 columns 
	let tbl1_encoded = encode_cols_var(&tbl1_cols, &vec![0,1,2]);
	let tbl1_sel = tbl1_cols[0].iter().map(|x| 
		x.is_zero().unwrap().not().into()).collect::<Vec<FpVar<F>>>();
	let res_firsthalf_encoded = encode_cols_var(&tbl_res, &vec![0,1,2]); 
	let res_firsthalf_sel = tbl_res[0].iter().map(|x|
		x.is_zero().unwrap().not().into() ).collect::<Vec<FpVar<F>>>();
	let mtbl_tbl1_res= prf.borrow().get_container("mtbl_tbl1_res")?
		.borrow().to_vec();
	assert_logup_cond(cs.clone(), &tbl1_encoded, &tbl1_sel, 
		&res_firsthalf_encoded, &res_firsthalf_sel, &mtbl_tbl1_res, r1)?;

	//3. verify lkup first 3 column in tbl1 (guarnatee no extra) 
	let mtbl_res_tbl1= prf.borrow().get_container("mtbl_res_tbl1")?
		.borrow().to_vec();
	assert_logup_cond(cs.clone(), &res_firsthalf_encoded, &res_firsthalf_sel, 
		&tbl1_encoded, &tbl1_sel, &mtbl_res_tbl1, r2)?;

	//4. relaxed well formed check of first 3 column (combining with 2)
	// needed for making sure expanding value column is correct
	// otherwise entries could be for different (k1,k2) pairs.
	// we do NOT have to check if key is sorted and no need to check
	// val is sorted as the first 3 column is already proved to be
	// contained in tbl1, as the relaxed well-formedness already guarantees
	// that for a key, an adversary prover cannot insert or delete
	// entries for a key (as all first 3 column entries must be in tbl1),
	// the well-formnedness guaranees that dummy (0-max entries wrapped 
	// around). Since we do not enforce key sorted, therefore full mapping
	// of tbl1 are preserved, but adversary prover can insert DUPLICATED
	// entries (expanded with join), but this only comes at the cost of
	// proving, but does not affect soundness of the proof.

	assert_well_formed_sorted_adv(cs.clone(),
		&tbl_res[0], //key1
		&tbl_res[1], //id
		&tbl_res[2], //key2
		None, //no need for checking sort val (tbl1 already proved)
		None,
		None, //no need for checking sort key
		None, 
		r1.clone(), 
		RANGE2_BIT,
		true, //relaxed
		)?;
	
	//5. lkup last 3 columns in tbl2 (one direction only)
	// NOTE that tbl2 is padded with dummy entries for all keys to deal with
	// left-join semantics (for those non-appearing foreign keys)
	let sorted_set_key2 = sorted_set_key2.borrow().get_container_by_idx(2)
		.borrow().to_vec();//note col #2 is the val of sorted set
	let sn = sorted_set_key2.len();
	let tbl2_pad = vec![
		sorted_set_key2.iter().map(
			|x| vec![x.clone(),x.clone()])
			.collect::<Vec<Vec<FpVar<F>>>>().concat(),
		vec![vec![zero.clone(),one.clone()]; sn].concat(),
		vec![vec![zero.clone(),max.clone()]; sn].concat()
	];
	assert!(tbl2_cols.len()==3);
	let tbl2_cols = tbl2_cols.into_iter().zip(tbl2_pad.into_iter())
		.map(|(v1,v2)|{
			vec![v1, v2].concat()
		}).collect::<Vec<Vec<FpVar<F>>>>();
	let tbl2_encoded = encode_cols_var(&tbl2_cols, &vec![0,1,2]);
	let tbl2_sel = tbl2_cols[0].iter().map(|x| 
		x.is_zero().unwrap().not().into()).collect::<Vec<FpVar<F>>>();
	let res_sechalf_encoded = encode_cols_var(&tbl_res, &vec![2,3,4]); 
	let res_sechalf_sel = tbl_res[2].iter().map(|x|
		x.is_zero().unwrap().not().into() ).collect::<Vec<FpVar<F>>>();
	let mtbl_sechalf_tbl2= prf.borrow().get_container("mtbl_sechalf_tbl2")?
		.borrow().to_vec();
	assert_logup_cond(cs.clone(), &res_sechalf_encoded, &res_sechalf_sel, 
		&tbl2_encoded, &tbl2_sel, &mtbl_sechalf_tbl2, r2)?;
	
	//6. check last3 column is of res_tbl well formed (
	// combined with 5 makes sure
	// that the expansion of (k1,k2) is complete. because the two dummy
	// entries are verified to be in tbl2. Note: no need on key
	let diff_val = prf.borrow().get_container("diff_val")?.borrow().to_vec();
	let sid_diff_val = prf.borrow().get_container("sid_diff_val")?
		.borrow().to_vec();
	assert_well_formed_sorted(cs.clone(),
		&tbl_res[2], //key2
		&tbl_res[3], //id
		&tbl_res[4], //val
		Some(&diff_val), //diff_val
		Some(&sid_diff_val), //sid_diff_val
		None, //diff_key (no need to check sort)
		None, //sid_diff_key
		r1.clone(), 
		RANGE2_BIT)?;

	Ok( () )
}

#[cfg(test)]
pub mod tests_db{
	use ark_relations::r1cs::{ConstraintSystem,ConstraintSystemRef};
	use ark_r1cs_std::{fields::fp::FpVar, alloc::AllocVar};
	use ark_bn254::{Fr};
	use crate::gadgets::{
		db::{assert_logup, assert_well_formed_sorted,col_to_sorted_set,verify_col_to_sorted_set,Container,verify_tbl_filtered_to_sorted_tbl, tbl_filtered_to_sorted_tbl,assert_logup_cond, tbl_to_sorted_tbl, verify_tbl_to_sorted_tbl, tbl_left_join, verify_tbl_left_join},
		traits::{Col, IDX_DATA},
		commons::{gen_m_table_cond,new_var},
	};
	use data_processor::clam_db::{RANGE2,RANGE2_BIT};
	use ark_ff::UniformRand;
	use ark_std::{test_rng};

	fn vec_to_var(cs: ConstraintSystemRef<Fr>, v: Vec<usize>)->Vec<FpVar<Fr>>{
		v.iter().map(|x| FpVar::new_witness(cs.clone(), 
			|| Ok(Fr::from(*x as u32))).unwrap() ).collect()
	}

	fn fr_to_var(cs: ConstraintSystemRef<Fr>, v: Fr)->FpVar<Fr>{
		FpVar::new_witness(cs, || Ok(v)).unwrap()
	}

	#[test]
	fn test_assert_logup_standard(){
        let cs = ConstraintSystem::<Fr>::new_ref();
		let qry = vec_to_var(cs.clone(), 
			vec![1, 3, 2, 5, 3, 0, 0, 0, 0, 3]); // 10 elements
		let lkup = vec_to_var(cs.clone(), vec![
			0, 1, 3, 5, 2, 2,
			500, 600, 700, 800, 900, 950, 
			1001, 1002, 1003, 1004, 1005, 1006,
			5001, 5002, 5003, 5004, 5005, 5006,
			6001, 6002, 6003, 6004, 6005, 6006,
			7001, 7002, 7003, 7004, 7005, 7006,
			8001, 8002, 8003, 8004, 8005, 8006,
			9001, 9002, 9003, 9004, 9005, 9006,
		]); //48 elements
		let r = fr_to_var(cs.clone(), Fr::from(123123123u32));
		let m_tbl = vec_to_var(cs.clone(), vec![
			4, 1, 3, 1, 1, 0, 
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0,
		]); //48 elements
		assert!(assert_logup(cs.clone(), &qry, &lkup, &m_tbl, &r).is_ok());
		assert!(cs.is_satisfied().unwrap());
	}

	fn vec_to_f(v: &Vec<usize>)->Vec<Fr>{
		v.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>()
	}

	#[test]
	fn test_assert_logup_cond(){
        let cs = ConstraintSystem::<Fr>::new_ref();
		let u_qry = vec![1, 3, 2, 5, 3, 0, 0, 0, 0];
		let u_sel_qry= vec![0, 13, 0, 0, 19, 0, 0, 0, 0];
		let u_lkup = vec![0, 1, 3, 5, 2, 2];
		let u_sel_lkup= vec![0, 0, 200, 0, 0, 0];

		let qry = vec_to_var(cs.clone(), u_qry.clone());
		let sel_qry = vec_to_var(cs.clone(), u_sel_qry.clone());
		let lkup = vec_to_var(cs.clone(), u_lkup.clone());
		let sel_lkup= vec_to_var(cs.clone(), u_sel_lkup.clone());

		let r = fr_to_var(cs.clone(), Fr::from(123123123u32));
		let f_m_tbl = gen_m_table_cond(
			&vec_to_f(&u_qry),
			&vec_to_f(&u_sel_qry),
			&vec_to_f(&u_lkup),
			&vec_to_f(&u_sel_lkup)
		);
		let m_tbl = f_m_tbl.iter().map(|x| new_var(&cs, *x)).collect::<Vec<FpVar::<Fr>>>();
		assert!(assert_logup_cond(cs.clone(), &qry, &sel_qry, &lkup, &sel_lkup, &m_tbl, &r).is_ok());
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_assert_wellformed_sorted(){
		let bits = RANGE2_BIT;
		let max:usize = (1<<bits) - 1;
		let rg2 = RANGE2 as usize;
        let cs = ConstraintSystem::<Fr>::new_ref();
		let key = vec_to_var(cs.clone(), vec![2, 2, 2, 3,3,3]);
		let id = vec_to_var(cs.clone(), vec![0, 1, 2, 0, 1, 2]);
		let val = vec_to_var(cs.clone(), vec![0, 100, max, 0, 22, max]);
		let diff_val = (1..val.len()).collect::<Vec<_>>()
			.into_iter().map(|i| &val[i] - &val[i-1]).collect::<Vec<_>>();
		//[100, 156, -max, 22, max-22]
		let diff_key= (1..key.len()).collect::<Vec<_>>()
			.into_iter().map(|i| &key[i] - &key[i-1]).collect::<Vec<_>>();
		let sid_diff_val= vec_to_var(cs.clone(), 
			vec![rg2, rg2, 0, rg2, rg2]);
		let sid_diff_key = vec_to_var(cs.clone(), 
			vec![rg2, rg2, rg2, rg2, rg2, rg2]);
		let mut rng = test_rng();
		let r = fr_to_var(cs.clone(), Fr::rand(&mut rng));
		assert!(assert_well_formed_sorted(cs.clone(), 
			&key, &id, &val, Some(&diff_val), Some(&sid_diff_val), Some(&diff_key), Some(&sid_diff_key), r, bits).is_ok());
		assert!(cs.is_satisfied().unwrap());

	}

	#[test]
	fn test_sorted_set(){
		let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
		let data = vec![2, 3, 100, 5, 7, 0, 2, 3].iter().map(|x|
			Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let data2 = vec![5,9].iter().map(|x|
			Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let col_1 = Col::new(data, "data", IDX_DATA);
		let col_2 = Col::new(data2, "data2", IDX_DATA);
		let col_ctn = Container::new("data");
		col_ctn.borrow_mut().add_col(col_1);
		col_ctn.borrow_mut().add_col(col_2);
		let n = 16;
		let f_ctn = col_to_sorted_set(&col_ctn, n, "sorted_set");
		let r = FpVar::new_witness(cs.clone(), 
			|| Ok(Fr::rand(&mut rng))).unwrap();
		let var_ctn= Container::<FpVar<Fr>>::from(&f_ctn.borrow(),cs.clone()); 
		assert!(verify_col_to_sorted_set(&r,&var_ctn,cs.clone()).is_ok());
		assert!(cs.is_satisfied().unwrap());

	}

	#[test]
	fn test_filter_tbl(){
		let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
		let r1 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();
		let r2 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();

		//1. build up the sorted_tbl for final states
		let n = 4;
		let final_states= Container::new_single(Col::new(
			vec![100, 200].iter().map(|x| Fr::from(*x as u32)).collect(), 
			"final_states", IDX_DATA));
		let sorted_set= col_to_sorted_set::<Fr>(&final_states, 
			n, "sorted_set");

		//2. build the table to project
		let states= Container::new_single(Col::new(
			vec![
				100, 200, 100, 53, 204, 205, 206, 207, 208,
				901, 901, 901, 901, 901, 901, 901, 901, 901, //dummy data
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
				901, 901, 901, 901, 901, 901, 901, 901, 901, 
			]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"states", IDX_DATA));
		let locs =  Container::new_single(Col::new(
			vec![
				1, 2, 3, 4, 5, 6, 7, 8, 9,
				11, 12, 13, 14, 15, 16, 17, 18, 19, //dummy data
				101, 102, 103, 104, 105, 106, 107, 108, 109,
				201, 202, 203, 204, 205, 206, 207, 208, 209,
				211, 212, 213, 214, 215, 216, 217, 218, 219,
				221, 222, 223, 224, 225, 226, 227, 228, 229,
				231, 232, 233, 234, 235, 236, 237, 238, 239,
				241, 242, 243, 244, 245, 246, 247, 248, 249,
			]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"locs", IDX_DATA));
		let n2 = 16;
		let unique_key_size = 8;
		let sorted_tbl = tbl_filtered_to_sorted_tbl(&states, 
			&locs, &sorted_set, n2, "sorted tbl", unique_key_size).unwrap();

		//3. construct claim/proof bundle and verify
		let states = Container::rc_from(&states.borrow(), cs.clone());
		let locs = Container::rc_from(&locs.borrow(), cs.clone());
		let sorted_tbl = Container::rc_from(&sorted_tbl.borrow(), cs.clone());
		let sorted_set = Container::rc_from(&sorted_set.borrow(), cs.clone());
		assert!( 
			verify_tbl_filtered_to_sorted_tbl(
				&r1, &r2, &states, &locs, &sorted_set, &sorted_tbl, 
				cs.clone()).is_ok()
		);
		assert!(cs.is_satisfied().unwrap());

	}

	#[test]
	fn test_tbl_to_sorted_tbl(){
		let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
		let r1 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();
		let r2 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();

		let states= Container::new_single(Col::new(
			vec![0, 100]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"states", IDX_DATA));
		let locs =  Container::new_single(Col::new(
			vec![0, 7]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"locs", IDX_DATA));
		let n2 = 4;

		let sorted_tbl = tbl_to_sorted_tbl(&states, 
			&locs, n2, "sorted tbl").unwrap();

		//3. construct claim/proof bundle and verify
		let states = Container::rc_from(&states.borrow(), cs.clone());
		let locs = Container::rc_from(&locs.borrow(), cs.clone());
		let sorted_tbl = Container::rc_from(&sorted_tbl.borrow(), cs.clone());
		assert!( 
			verify_tbl_to_sorted_tbl(
				&r1, &r2, &states, &locs, &sorted_tbl, cs.clone()).is_ok());
		assert!(cs.is_satisfied().unwrap());
	}


	#[test]
	fn test_tbl_left_join(){
		let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
		let r1 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();
		let r2 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();

		let n2 = 8;
		let states= Container::new_single(Col::new(
			vec![0, 100]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"states", IDX_DATA));
		let locs =  Container::new_single(Col::new(
			vec![0, 7]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"locs", IDX_DATA));
		let state_loc_tbl= tbl_to_sorted_tbl(&states, 
			&locs, n2, "state_loc_tbl").unwrap();

		let pat =  Container::new_single(Col::new(
			vec![0, 9, 9, 9, 9]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"pats", IDX_DATA));
		let states= Container::new_single(Col::new(
			vec![0, 0, 100, 127, 255]
			.iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>(),
			"states", IDX_DATA));
		let sorted_set_states= col_to_sorted_set::<Fr>(&states, 
			n2, "sorted_set_states");
		let pat_state_tbl = tbl_to_sorted_tbl(&pat, &states, 
			n2, "pat_state_tbl").unwrap();

		//3. construct claim/proof bundle and verify
		let n = 16;
		let pat_state_loc_tbl= tbl_left_join(&pat_state_tbl,
			&state_loc_tbl, 
			&sorted_set_states,
			n, "pat_state_loc_tbl").unwrap();

		let pat_state_tbl= Container::rc_from(
			&pat_state_tbl.borrow(), cs.clone());
		let state_loc_tbl= Container::rc_from(
			&state_loc_tbl.borrow(), cs.clone());
		let pat_state_loc_tbl= Container::rc_from(
			&pat_state_loc_tbl.borrow(), cs.clone());
		let sorted_set_states= Container::rc_from(
			&sorted_set_states.borrow(), cs.clone());

		assert!( 
			verify_tbl_left_join(
				&r1, &r2, 
				&pat_state_tbl, 
				&state_loc_tbl, 
				&sorted_set_states, 
				&pat_state_loc_tbl, 
				cs.clone()).is_ok());
		assert!(cs.is_satisfied().unwrap());
	}

	#[test]
	fn test_prove_tag(){
		use crate::gadgets::db::{prove_filter_tag, verify_filter_tag};

		let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
		let r1 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();
		let r2 = FpVar::new_witness(cs.clone(),|| 
			Ok(Fr::rand(&mut rng))).unwrap();

		let key = vec![//32 elements
				100, 0, 200, 300, 10, 20, 30, 0, 
				1000, 2000, 1000, 2000, 3000, 2000, 3000, 2000,
				1000, 2000, 1000, 2000, 3000, 2000, 3000, 2000,
				1000, 2000, 1000, 2000, 3000, 2000, 3000, 2000,
			].iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let sorted_key= vec![0, 10, 20, 30].
			iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let tag= vec![//16 elements
				0, 0, 0, 0, 1, 1, 1, 0, 
				0, 0, 0, 0, 0, 0, 0, 0,
				0, 0, 0, 0, 0, 0, 0, 0,
				0, 0, 0, 0, 0, 0, 0, 0,
			].iter().map(|x| Fr::from(*x as u32)).collect::<Vec<Fr>>();
		let unique_key_size = 10;
		let prf_tag = prove_filter_tag(&key, &sorted_key, &tag, 
			unique_key_size).unwrap();

		let var_key = key.iter().map(|x| new_var(&cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		let var_sorted_key = sorted_key.iter().map(|x| new_var(&cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		let var_tag= tag.iter().map(|x| new_var(&cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		let var_prf_tag = Container::rc_from(&prf_tag.borrow(), cs.clone());
		assert!(
			verify_filter_tag(&var_key, &var_sorted_key, &var_tag,
				&var_prf_tag, &r1, &r2).is_ok()
		);
		assert!(cs.is_satisfied().unwrap());


	}


}
