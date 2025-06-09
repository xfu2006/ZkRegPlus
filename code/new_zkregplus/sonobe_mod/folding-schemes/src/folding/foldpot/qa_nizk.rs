/* Created 09/28/2024 
	Implemented 10/29/2024
	quasi-linear space NIZK: legosnark apdx D. <https://eprint.iacr.org/2019/142.pdf>. We made the optimization here to allow matrix to be sparse.
	Modified 11/03/2024: add one kzg row
	Modified 11/10/2024: addressing the E vector
	Modified 01/12/2025: adding random blinding factor 
*/
use std::time::Instant;
use std::ops::Mul;
use rayon::prelude::*;
use crate::folding::foldpot::{
	utils::{f1_to_f2_limbs,get_limb_size},
	CF2,
};

use ark_ec::{Group, CurveGroup,
	pairing::{Pairing},
	VariableBaseMSM
};
use ark_ff::{PrimeField,ToConstraintField};
use crate::folding::{
	foldpot::{ 
		sigma_cyclepair::{compute_hc},
	}
};
use ark_std::{Zero,UniformRand};
use ark_crypto_primitives::sponge::{
	poseidon::{PoseidonConfig},
    Absorb
};

/// prover key
#[derive(Clone,Debug)]
pub struct QaNizkProverParams<E:Pairing>{
	/// the qa-nizk prover key (check LegoSnark 
	/// <https://eprint.iacr.org/2019/142> apdx D.2)
	pub p: Vec<E::G1Affine>,
	/// optional for debugging
	pub smatrix: Option<SparseMatrix<E::G1>>,
	/// optional for debugging (regular standard matrix)
	pub matrix: Option<Matrix<E::G1>>
}

/// verifier key
#[derive(Clone,Debug)]
pub struct QaNizkVerifierParams<E:Pairing>{
	pub c: Vec<E::G2>,
	pub a: E::G2,
}

impl <E:Pairing<G1=C,ScalarField=C::ScalarField>, C: CurveGroup> QaNizkVerifierParams<E> 
where
C: ToConstraintField<CF2<C>>, 
<C as Group>::ScalarField: PrimeField + Absorb,
<C as CurveGroup>::BaseField: PrimeField,
<E as Pairing>::TargetField: ToConstraintField<CF2<C>>,
<E as Pairing>::G2: ToConstraintField<CF2<C>>,
<E as Pairing>::ScalarField: PrimeField + Absorb,
{
	pub fn hash(&self, config: &PoseidonConfig<E::ScalarField>)->E::ScalarField{
		//1. init
		let v_data = vec![self.c.clone(), vec![self.a.clone()]].concat();
		let limb_size = get_limb_size::<C::BaseField,C::ScalarField>();
		let vec_b_raw:Vec<C::BaseField> = self.a.to_field_elements().unwrap(); 
		let _vec_b_raw_len = vec_b_raw.len();
		let zero = C::ScalarField::zero();
		let mut hb_out = zero;

		for b in v_data{
			let vec_b_raw:Vec<C::BaseField> = b.to_field_elements().unwrap(); 
			let vec_b_raw_len = vec_b_raw.len();
			let vec_b = vec_b_raw.into_iter().map(|a|
				f1_to_f2_limbs::<C::BaseField,C::ScalarField>(&a) )
				.collect::<Vec<Vec<C::ScalarField>>>()
				.concat();
			assert!(vec_b.len()==vec_b_raw_len*limb_size);
			hb_out = compute_hc(&config, &hb_out, &vec_b);
		}
		hb_out
	}
}

/// proof
#[derive(Clone,Debug)]
pub struct QaNizkProof<E:Pairing>{
	/// just one element
	pub prf: E::G1,
}

/// represent a sparse matrix (only pertaining to this 
/// special app in decider circuit). every row
/// is a chunk of the special data
/// This is a SPECIAL matrix designed specifically for our problem.
/// row1: kzg_keys (size: |W| + |E| + 1) -> produce KZG commitment to W + E.
///    the last element is a random blinding factor
/// row2: W1: which is a fragment of Pedersen key
/// row3: E1: which is a part of Pedersen key.
/// row4: F1: which is a part of the Pedersen key
/// for row2-4 their indiex never exceeds the cols (which is
/// essentially half of row1
#[derive(Debug,Clone)]
pub struct SparseMatrix<C: CurveGroup>{
	/// number of rows
	pub rows: usize,
	/// number of columns (sum of length of |W| + |E| + 1), where |W| = |E|
	pub cols: usize,
	/// used for Pedersen key generation |W| + |E| + 1 (last element treat
	/// it as zero)
	pub ped_row: Vec<C::Affine>,
	/// the kzg keys (actual 1st row). Width is |W| + |E| + 1 (last element
	/// put a zero)
	pub kzg_row: Vec<C::Affine>,
	/// represents the (w_start_idx, k_start_idx_to_take_from_ped_row, size)
	/// e.g., (200, 100, 50) represents a sparse row which starts at
	/// position 200 and length 50, its contents is taken from position 100
	/// of ped_row
	pub vec_rows: Vec<(usize, usize, usize)>,
}

impl <C:CurveGroup> SparseMatrix<C>{
	/// return group element at location i, j.
	/// distinguish the handling of 0'th row and the rest
	pub fn get(&self, i: usize, j: usize) -> C::Affine{
		assert!(j<self.cols && i<self.rows);
		let (w_idx, k_idx, len) = self.vec_rows[i];
		if j<w_idx || j>=w_idx + len{
			return C::zero().into_affine();
		}else if i==0{
			self.kzg_row[j]
		}else{
			self.ped_row[j-w_idx+k_idx]
		}
	}

	/// get the column i. Since usually column is short, we do not
	/// use parallel processing here
	pub fn get_col(&self, i: usize) -> Vec<C::Affine>{
		let mut res = vec![];
		for j in 0..self.rows{ res.push( self.get(j, i) ); }
		res
	}

	/// generate a random matrix
	pub fn rand(rows: usize, cols: usize)->Self{
		assert!(cols>rows, "cols must be greater than rows");
		assert!((rows-1)%3==0); //must b3 3k+1
		let half_cols = cols/2 - 2*2;
		let mut rng = rand::rngs::OsRng;
		let mut ped_row= vec![];
		let mut kzg_row= vec![];
		let k = (rows-1)/3;
		for _i in 0..cols{ 
			kzg_row.push( C::rand(&mut rng).into_affine() ); 
			ped_row.push( C::rand(&mut rng).into_affine() ); 
		}
		let unit = half_cols/k-1; 
		let mut vec_rows = vec![(0, 0, cols)];
		for i in 0..k{
			vec_rows.push( (i*unit, i*unit, unit) );
			vec_rows.push( (i*unit, i*unit + half_cols, unit) );
			vec_rows.push( (i*unit, i*unit, unit/2) );
		}
		let mat = SparseMatrix{rows, cols, ped_row, vec_rows, kzg_row};
		mat
	}
}


	

pub fn setup_qa_nizk<E:Pairing>(mat: &SparseMatrix<E::G1>, b_debug: bool)
-> (QaNizkProverParams<E>, QaNizkVerifierParams<E>){
	//1. sample vec_k, a, 
	let mut rng = rand::rngs::OsRng;
	let mut k = vec![];
	for _i in 0..mat.rows{
		k.push(<E::G1 as Group>::ScalarField::rand(&mut rng) );
	}
	let a = <E::G1 as Group>::ScalarField::rand(&mut rng);
	let mut c = vec![];
	for i in 0..k.len(){ c.push( k[i] * a ); }
	assert!(mat.cols == mat.kzg_row.len());
	assert!(mat.cols == mat.ped_row.len());
	assert!(mat.rows == mat.vec_rows.len());

	let p = (0..mat.cols).into_par_iter().map(|i| {
		let col = mat.get_col(i);
		let mut p_i = E::G1::zero();
		// col is short, so we can just do sequential here
		for j in 0..mat.rows{
			p_i = p_i + col[j] * k[j];
		}
		p_i
	}).collect::<Vec<E::G1>>();
	let g2 = <E::G2 as Group>::generator();
	let a_2 = g2 * a;
	let c_2 = c.into_par_iter().map(|c| g2*c).collect::<Vec<E::G2>>();
	let p_affine = E::G1::normalize_batch(&p);

	let smatrix = if b_debug {Some(mat.clone())} else {None};
	let vk = QaNizkVerifierParams{c: c_2, a:a_2};
	(QaNizkProverParams{p: p_affine, smatrix, matrix: None}, vk)
}

/// the "standard" qa-nizk set up procedure
pub fn setup_qa_nizk_standard<E:Pairing>(mat: &Matrix<E::G1>,
	b_debug: bool)
-> (QaNizkProverParams<E>, QaNizkVerifierParams<E>){
	//1. sample vec_k, a, 
	let mut rng = rand::rngs::OsRng;
	let mut k = vec![];
	for _i in 0..mat.rows{
		k.push(<E::G1 as Group>::ScalarField::rand(&mut rng) );
	}
	let a = <E::G1 as Group>::ScalarField::rand(&mut rng);
	let mut c = vec![];
	for i in 0..k.len(){ c.push( k[i] * a ); }

	let p = (0..mat.cols).into_par_iter().map(|i| {
		let col = mat.get_col(i);
		let mut p_i = E::G1::zero();
		// col is short, so we can just do sequential here
		for j in 0..mat.rows{
			p_i = p_i + col[j] * k[j];
		}
		p_i
	}).collect::<Vec<E::G1>>();
	let g2 = <E::G2 as Group>::generator();
	let a_2 = g2 * a;
	let c_2 = c.into_par_iter().map(|c| g2*c).collect::<Vec<E::G2>>();
	let p_affine = E::G1::normalize_batch(&p);

	let matrix = if b_debug {Some(mat.clone())} else {None};
	(QaNizkProverParams{p: p_affine, smatrix: None, matrix: matrix}, 
		QaNizkVerifierParams{c: c_2, a: a_2})
}

/// returns the statement X and the proof.
/// This function should ONLY be called in debug mode,
/// it's expecting the smatrix is not null (in debug mode)
pub fn prove_qa_nizk<E:Pairing>(
	w: &Vec<<E::G1 as Group>::ScalarField>, 
	r_w: E::ScalarField,
	pkey: &QaNizkProverParams<E> ) 
	-> (Vec<E::G1>, QaNizkProof<E>){
	assert!(pkey.p.len()==w.len()+1, "pkey.len != w in qa_nizk");
	assert!(pkey.smatrix.is_some());
	let mat = pkey.smatrix.as_ref().unwrap().clone();
	let mut w = w.clone();
	w.push(r_w);
	let mut x = vec![];
	for i in 0..mat.rows{
		let (w_idx, k_idx, len) = mat.vec_rows[i];
		let _t1 = Instant::now();
		if i==0 {assert!(w_idx==0 && k_idx==0 && len==mat.cols);}
		let row = if i==0 {&mat.kzg_row[0..len]}
			else {&mat.ped_row[k_idx..k_idx+len]}; 
		let w_i = &w[w_idx..w_idx+len];
		let x_i = E::G1::msm_unchecked(row, w_i);
		x.push(x_i);
	}

	let prf = E::G1::msm_unchecked(&pkey.p, &w);
	(x, QaNizkProof{prf})
}

/// returns the statement X and the proof
pub fn prove_qa_nizk_fast<E:Pairing>(
	w: &Vec<<E::G1 as Group>::ScalarField>, 
	r_w: E::ScalarField,
	pkey: &QaNizkProverParams<E> ) 
	-> QaNizkProof<E>{
	assert!(pkey.p.len()==w.len()+1, "pkey.len: {} != w in qa_nizk: {}",
		pkey.p.len(), w.len());
	let prf1 = E::G1::msm_unchecked(&pkey.p, &w);
	let prf2 = pkey.p[w.len()].mul(r_w);
	let prf = prf1 + prf2;
	QaNizkProof{prf}
}

pub fn compute_x<E:Pairing>(w: &Vec<<E::G1 as Group>::ScalarField>,
	r_w: E::ScalarField,
	matrix: &Matrix<E::G1>) -> Vec<E::G1>{
	assert!(matrix.matrix[0].len() == w.len() + 1);
	matrix.matrix.par_iter().map(|row|
		{
			let g1 = E::G1::msm_unchecked(row, w);
			let g2 = row[w.len()].mul(r_w);
			g1 + g2
		}
	).collect::<Vec<E::G1>>()
}


/// verify
pub fn verify_qa_nizk<E:Pairing>(x: &Vec<E::G1>, prf: &QaNizkProof<E>, 
	vkey: &QaNizkVerifierParams<E>)->bool{
	let mut lhs = E::pairing(x[0], vkey.c[0]);
	for i in 1..x.len(){ lhs += E::pairing(x[i], vkey.c[i]); };
	let rhs = E::pairing(prf.prf, vkey.a);
	lhs==rhs
}


/// A regular matrix for a standard QA-NIZK 
#[derive(Debug,Clone)]
pub struct Matrix<C: CurveGroup>{
	/// numbef of rows
	pub rows: usize,
	/// number of cols
	pub cols: usize,
	/// the 2d matrix needs to match rows and cols
	pub matrix: Vec<Vec<C::Affine>>
}

impl <C:CurveGroup> Matrix<C>{
	/// generate a random matrix. slow: use for testing purpose only
	pub fn rand(rows: usize, cols: usize)->Self{
		assert!(cols>rows, "cols must be greater than rows");
		let mut rng = rand::rngs::OsRng;
		let mut matrix = vec![];
		for _i in 0..rows{
			let mut row = vec![];
			for _j in 0..cols{
				row.push( C::rand(&mut rng).into_affine() ); 
			
			}
			matrix.push( row );
		}
		Matrix{rows, cols, matrix}
	}

	pub fn get_col(&self, i: usize) -> Vec<C::Affine>{
		let mut res = vec![];

		for j in 0..self.rows{ res.push( self.matrix[j][i] );}
		res
	}
}

#[cfg(test)]
pub mod tests_qa_nizk{
	use crate::{ folding::foldpot::qa_nizk::{SparseMatrix, setup_qa_nizk, prove_qa_nizk, prove_qa_nizk_fast, compute_x, verify_qa_nizk, Matrix, setup_qa_nizk_standard} };
    use ark_bn254::{Bn254, Fr, G1Projective as Bn254G1};
	use ark_std::{UniformRand};

	#[test]
	pub fn test_qa_nizk(){
		//1. build a sample matrix
		let mut rng = rand::rngs::OsRng;
		let k = 2;
		let rows = 3*k+1;
		let cols = 48;
		let mat = SparseMatrix::<Bn254G1>::rand(rows, cols);
		let (prover_param, verifier_param) = setup_qa_nizk::<Bn254>(&mat, true);
		let mut w = vec![];
		for _i in 0..cols-1{w.push(Fr::rand(&mut rng));}
		let r_w = Fr::rand(&mut rng);
		let (x, prf) = prove_qa_nizk(&w, r_w, &prover_param);
		let res = verify_qa_nizk(&x, &prf, &verifier_param);
		assert!(res);

	}

	#[test]
	pub fn test_qa_nizk_standard(){
		//1. build a sample matrix
		let mut rng = rand::rngs::OsRng;
		let rows = 4;
		let cols = 12;
		let mat = Matrix::<Bn254G1>::rand(rows, cols);
		let (prover_param, verifier_param) = setup_qa_nizk_standard::<Bn254>(&mat, true);
		let mut w = vec![];
		for _i in 0..cols-1{w.push(Fr::rand(&mut rng));}
		let r_w = Fr::rand(&mut rng);
		let x = compute_x::<Bn254>(&w, r_w, &mat);
		let prf = prove_qa_nizk_fast(&w, r_w, &prover_param);
		let res = verify_qa_nizk(&x, &prf, &verifier_param);
		assert!(res);
	}
}
