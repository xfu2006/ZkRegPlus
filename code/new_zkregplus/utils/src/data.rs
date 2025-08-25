/// Data (conversion) related operations
/*
	Created: 07/23/2024. Factored from os.rs of old zkreg project (01/04/2024)
*/

extern crate sha2;
extern crate num_bigint;
extern crate ark_std;
extern crate ark_serialize;
extern crate ark_ff;

use sha2::{Sha256,Digest};
use num_bigint::BigUint;
use ark_serialize::{CanonicalSerialize};
use ark_ff::{PrimeField,BigInteger,UniformRand};
use ark_std::log2;
use ark_std::rand::Rng;
use std::collections::HashMap;

use crate::timer::{Timer};
use rayon::prelude::*;


/** return the ceil of log2(n) */
pub fn ceil_log2(n: usize) -> usize{
	let mut k = log2(n);
	let res = 1<<k;
	if res<n{ k = k + 1; }
	return k as usize;
}



/// convert e.g. "AB" to vec![0x4, 0x1, 0x4, 0x2]
pub fn str_to_u8(s: &str) -> Vec<u8>{
	//1. str to u8
	let mut vec:Vec<u8> = vec![];
	for c in s.chars(){
		let c8 = c as u8;
		vec.push(c8/16);
		vec.push(c8%16);
	}
	vec
}

/// convert e.g., "AB" to "4142"
pub fn str_to_hex(s: &str) -> String{
	let v = str_to_u8(s);
	u8_to_hex(&v)
}

/// e.g., "4142" to "AB" (if string length is odd, padd 0 at the end)
pub fn hex_to_str(s: &str)->String{
	let mut vec: Vec<u8> = hex_to_u8(s);
	if vec.len()%2==1{vec.push(0u8);}
	let mut vec_res:Vec<char> = vec!['0'; vec.len()/2];
	for i in 0..vec.len()/2{
		assert!(vec[i]<16);
		let ch = vec[i*2]*16 + vec[i*2+1];
		vec_res[i] = ch as char;
	}
	let s:String = vec_res.iter().collect();

	s
}

/// hex string to `Vec<u8>` e.g., "12ab" -> `vec![1, 2, 10, 11]`
pub fn hex_to_u8(s: &str)->Vec<u8>{
	let hs_map :HashMap::<char,u8> = [('0', 0), ('1', 1), ('2', 2), ('3', 3), ('4', 4), ('5', 5), ('6', 6), ('7', 7), ('8', 8), ('9', 9), ('a', 10), ('b', 11), ('c', 12), ('d', 13), ('e', 14), ('f', 15)].iter().cloned().collect();
	
	s.chars().map(|c| {*hs_map.get(&c).unwrap()}).collect()
}

// split each element, e.g., 0x41 into 0x4 and 0x1
pub fn char_arr_to_u8(arr: &Vec<u8>) -> Vec<u8>{
	let mut vec:Vec<u8> = vec![];
	for val in arr{
		let v8 = *val as u8;
		vec.push(v8/16);
		vec.push(v8%16);
	}
	vec
}

/// 62 nibbles to f. each nibble 4 bit. Assume f width at least 248 bits.
pub fn nibbles_to_one_packed<F:PrimeField>(nibbles: &Vec<F>)->F{
	#[cfg(test)] assert!(nibbles.len()==62);
	let unit = F::from(16u32);
	let mut factor = F::from(1u32);
	let mut res = F::zero();
	for i in 0..62{
		res = res + nibbles[i]*factor;
		factor = factor * unit;
	}

	res
}

/// convert f to 62 nibbles
pub fn one_packed_to_nibbles<F:PrimeField>(f: &F)->Vec<F>{
	let bits = f.into_bigint().to_bits_le();
	let factors = vec![F::from(1u32), F::from(2u32), F::from(4u32), F::from(8u32)];
	#[cfg(test)] assert!(bits.len()>=248);
	let bits = bits[0..248].to_vec();
	let zero = F::zero();
	let res = bits.chunks(4).map(|v|{
		let mut num = F::zero();
		for i in 0..v.len(){
			num += if v[i] {factors[i]} else {zero};
		}
		num	
	}).collect::<Vec<F>>();

	res
}

/// read nibbles in the form of chunked nibbles (each nibble is 4-bit
/// assuming F is at least 248 bit, we encode 62 units per field 
/// elements, rounding 0-bits are padded at the end
pub fn pack_nibbles<F:PrimeField>(nibbles: &Vec<F>) -> Vec<F>{
	//1. expand vres and pad zeros 
	let mut vres = nibbles.clone();
	let unit = 62;
	let chunks = if vres.len()%unit==0 {vres.len()/unit} 
		else {vres.len()/unit+1};
	let vnew_len = chunks * unit;
	let more_len = vnew_len - vres.len();
	let mut vec_more = vec![F::zero(); more_len];
	vres.append(&mut vec_more);
	assert!(vres.len()==vnew_len);

	//4. assemble field elements
	let res = vres.par_chunks(unit).map(|vec|{
		let vec2 = vec.into_iter().map(|x| F::from(*x)).collect::<Vec<F>>();
		nibbles_to_one_packed(&vec2)
	}).collect::<Vec<F>>();

	res
}

/// return 248-bit packed to nibbles
pub fn packed_to_nibbles<F:PrimeField>(packed: &Vec<F>) -> Vec<F>{
	let res = packed.par_iter().map(|x|
		one_packed_to_nibbles(x)
	).flatten().collect::<Vec<F>>();

	res
}



/// u8 to hex string, e.g., `[1, 2, 11, 12]` -> "12bc"
/// note: assumption: all values are hex numbers in range `[0,15]`
pub fn u8_to_hex(s: &Vec<u8>)->String{
	let hs_map :HashMap::<u8,char> = [ (0, '0'), (1, '1'), (2, '2'), (3, '3'), (4, '4'), (5, '5'), (6, '6'), (7, '7'), (8, '8'), (9, '9'), (10, 'a'), (11, 'b'), (12, 'c'), (13, 'd'), (14, 'e'), (15, 'f'), ].iter().cloned().collect();

	let s: String = s.iter().map(|n| {*hs_map.get(&n).unwrap()}).collect();
	s
}

/// serlialize a vec of T into vec of u8 
pub fn to_vecu8<F: CanonicalSerialize>(v: &Vec<F>)->Vec<u8>{
	if v.len()==0 {return vec![];}
	let unit_size = v[0].uncompressed_size();
	let mut v2 = vec![0; unit_size*v.len()];
	for u in 0..v.len(){
		let slice = &mut v2[unit_size*u..unit_size*(u+1)];
		let _x = v[u].serialize_uncompressed(slice);
	}
	return v2;
}

/// use default 128-bit security generate 128-bit field element
pub fn hash<F:PrimeField>(barr: &Vec<u8>) -> F{
	return hash_worker(barr, 128);
}

/// hash the given byte array into a field element
pub fn hash_worker<F:PrimeField>(barr: &Vec<u8>, bits: usize)->F{
	let mut t1 = Timer::new();
	t1.start();
	let mut hasher = Sha256::new();
	hasher.update(barr);
	let result = hasher.finalize();
	let bi = BigUint::from_bytes_le(&result);
	let bi250 = BigUint::from(1u64) << bits; 
	let bres = bi % bi250;
	let sres = bres.to_str_radix(10);
	let f = str_to_fe::<F>(&sres);
	t1.stop();
	return f;
}

/// parse string as fe
pub fn str_to_fe<F:PrimeField>(v: &String) -> F {
	let s: &str = &v[..];
	let res = F::from_str(s);
	match res{
		Ok(res_f) => return res_f,
		Err(_e) => {println!("ERROR parsing v: {}", v); return F::zero();}
	}
}

/// Create a random field element with the corresponding bits
pub fn rand_fe_by_bits<R: Rng + ?Sized, F: PrimeField>(bits: usize, rng: &mut R) -> F {
    let v1 = F::BigInt::rand(rng);
    let vec_bits = v1.to_bits_le();
    let new_bits = vec_bits[0..bits].to_vec();
    let v2 = F::BigInt::from_bits_le(&new_bits);
    let ret = F::from_bigint(v2).expect("failed conversion from bigint");
    ret
}

#[cfg(test)]
pub mod tests_data_utils{
	use ark_std::{Zero};
	use ark_bn254::{Fr};
	use crate::data::{rand_fe_by_bits, nibbles_to_one_packed, 
		one_packed_to_nibbles, pack_nibbles, packed_to_nibbles};

	#[test]
	pub fn test_one_pack(){
		let mut rng = rand::rngs::OsRng;
		let f = rand_fe_by_bits::<_,Fr>(248, &mut rng);
		let nibbles = one_packed_to_nibbles(&f);
		let f2 = nibbles_to_one_packed(&nibbles);
		println!("f: {}, f2: {}", f, f2);
		assert!(f == f2);
	}

	#[test]
	pub fn test_pack(){
		let mut rng = rand::rngs::OsRng;
		let n = 127;  //need 3 segments
		let n2 = if n%62==0 {n} else {(n/62+1)*62};
		let nibbles = (0..n).map(|_i|
			rand_fe_by_bits::<_,Fr>(4, &mut rng)
		).collect::<Vec<Fr>>();
		let packed = pack_nibbles(&nibbles);
		assert!(packed.len()==3);
		let nibbles2 = packed_to_nibbles(&packed);
		for i in 0..n{ assert!(nibbles[i] == nibbles2[i]);}
		for i in n..n2 {assert!(nibbles2[i].is_zero());}
	}

}
