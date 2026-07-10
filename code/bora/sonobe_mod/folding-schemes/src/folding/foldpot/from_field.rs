/* Created 10/17/2024 */

use ark_ff::{Field};
use crate::folding::circuits::{CF2,CF3};
use ark_ec::{CurveGroup};
use ark_std::{Zero};
use ark_bn254::{
	Fq, Fq2, G1Affine, G2Affine};

pub trait AffineFromField<F:Field>{
	fn from_fields(f1: F, f2: F)->Self;
}

// NOTE: currently we only support Bn254/Grumpkin
impl AffineFromField<Fq> for G1Affine{
	fn from_fields(f1: Fq, f2: Fq)->Self{
		let b_inf = f1==Fq::zero() && f2==Fq::zero();
		Self{x: f1, y: f2, infinity: b_inf}
	}
}
impl AffineFromField<Fq2> for G2Affine{
	fn from_fields(f1: Fq2, f2: Fq2)->Self{
		let b_inf = f1==Fq2::zero() && f2==Fq2::zero();
		Self{x: f1, y: f2, infinity: b_inf}
	}
}
// TODO: add more implementations for Bls curves if necessary

pub fn curve_from_field_elements<C: CurveGroup>(v: &Vec<CF3<C>>) 
->  C
where C::Affine: AffineFromField<CF2<C>>{
	let n = v.len();
	assert!(n%3==0);
	let (c0, c1, _c2) = (v[0..n/3].to_vec(), v[n/3..2*n/3].to_vec(),
		v[2*n/3..n].to_vec());
	let x = CF2::<C>::from_base_prime_field_elems(&c0).unwrap();
	let y = CF2::<C>::from_base_prime_field_elems(&c1).unwrap();
	let repr = C::Affine::from_fields(x, y);
	repr.into()
}

#[cfg(test)]
pub mod tests_mod_super {
    use ark_bn254::{Bn254, G1Projective as Projective,
		G2Projective as ProjectiveG2};
	use ark_std::{UniformRand,test_rng};
	use ark_ec::{pairing::Pairing};
	use ark_ff::{Field,ToConstraintField};
	use crate::folding::foldpot::from_field::{curve_from_field_elements};

	type TargetField = <Bn254 as Pairing>::TargetField;
    #[test]
    fn test_from_field() {
		let mut rng = test_rng();
		let t1 =  Projective::rand(&mut rng);
		let t2 =  ProjectiveG2::rand(&mut rng);
		let gt1: TargetField= Bn254::pairing(t1, t2).0;
		let vec = gt1.to_field_elements().unwrap();
		let gt2 = TargetField::from_base_prime_field_elems(&vec).unwrap();
		assert!(gt1==gt2);
		println!("PASSED gt1 serialization");

		let t1_vec = t1.to_field_elements().unwrap();
		let t1_2 = curve_from_field_elements::<Projective>(&t1_vec); 
		assert!(t1==t1_2);

		let mut t2_vec = t2.to_field_elements().unwrap(); //somehow there is
		//only one zero element
		t2_vec.push( t2_vec[t2_vec.len()-1].clone() ); //push another zero
		let t2_2= curve_from_field_elements::<ProjectiveG2>(&t2_vec); 
		assert!(t2==t2_2);

	}
	
}
