/* 
   If `light-test` feature is enabled.
   Small data: (RAM needed: Completion time: )

   Created: 02/05/2025
*/

use zkregplus::zkp_driver::{zkp_driver};
use std::env;
use ark_ff::{PrimeField};
use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
use ark_groth16::Groth16;
use folding_schemes::{commitment::{pedersen::Pedersen, kzg::KZG}};

type CS1 = Pedersen<Projective>;
//EXTERNAL commitment KZG for decider
type CS1E = KZG<'static, Bn254>;
type CS2 = Pedersen<Projective2>;
type C1 = Projective;
type C2 = Projective2;
type GC1 = GVar;
type GC2 = GVar2;
//type FC = SigmaIR1CS_Inst<Fr,Projective,KZG<'static,Bn254>,LK>;
type S = Groth16<Bn254>;
type C2G2 = ProjectiveG2;


fn small_data<F:PrimeField>(){
	let b_read_cache = false;
	let b_write_cache = true;
	zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
		"data/small_data_set/config/sigs.dat", //src sig
		"data/small_data_set/config/binexec.dat", //list of files to discharge
		"data/small_data_set/reports/report.dat", //report
		b_read_cache,
		b_write_cache,
		"small_20", //cache name
		"data/small_data_set/config/dfa.dat", //signs that need dfa
		"data/small_data_set/config/ised.dat", //signs that need ised 
		"data/small_data_set/config/ised_igc.dat", //signs that need ised igc
	);
}

pub fn main(){
	let args: Vec<String> = env::args().collect();
	assert!(args.len()>1, "expecting one argument: 'light', 'mid', 'large'");
	println!("args0: {}", args[0]);
	if args[1]=="small"{ small_data::<Fr>(); }
}
