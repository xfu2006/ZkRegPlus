use ark_ec::{AffineRepr, CurveGroup, short_weierstrass::{Affine, SWCurveConfig}};
use ark_ff::{PrimeField, Zero};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use rayon::prelude::*;
use std::fs::{File, metadata};
use std::io::{BufWriter, BufReader};
use ark_groth16::{ProvingKey, VerifyingKey};
use ark_bn254::Bn254;

fn main() {}
