use ark_bn254::Fr;
use ark_ff::PrimeField;
use std::str::FromStr;

fn main() {
    let s = "2";
    let f = Fr::from_str(s).unwrap();
    println!("to_string: {}", f.to_string());
    println!("format: {}", format!("{}", f));
    // println!("into_bigint: {}", f.into_bigint()); // might not implement Display
}
