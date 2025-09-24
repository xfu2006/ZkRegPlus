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
use zkregplus::circs::{
	//composable_gadget_mapper::{CompositeGadgetMapper},
	cp_mapper::{CpCapacity},
	sed_mapper::{SedCapacity},
	dfa_mapper::{DfaCapacity},
};
use data_processor::clam_db::RANGE2_BIT;

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
	let set1 = "data/debug/small_data_set/config_dfa"; //for dfa 
	let max_word= 1; //this is chunk_len
	let sigs = 3;
	let subsigs = 6;
	let avg_pat_per_sig = 8;
	let avg_active_pat_per_sig = 3;
	let basis_pats_in_trace = 60*100;
	let basis_unique_states= 50*100;
	let perc_comp_subsigs = 50;
	let num_category = 1;
	let num_circs_per_category= 1;

	let init_cp_cap= CpCapacity{
		max_word_len: 1, final_states_len: 8, 
		join_buf_capacity: 8, sig_buf_capacity: 6
	};
	let init_sed_cap= SedCapacity::new(
		max_word, RANGE2_BIT, subsigs, 
		avg_pat_per_sig, avg_active_pat_per_sig, 
		basis_pats_in_trace, sigs, perc_comp_subsigs,
		basis_unique_states
	);
	let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


	zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
		&format!("{}/sigs.dat",set1), //src sig
		&format!("{}/binexec.dat",set1), //list of files to discharge
		"data/small_data_set/reports/report.dat", //report
		b_read_cache,
		b_write_cache,
		"small_20", //cache name
		&format!("{}/dfa.dat", set1), //signs that need dfa
		&format!("{}/ised.dat", set1), //signs that need ised 
		&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
		max_word, //this is the chunk len
		&init_cp_cap,
		&init_sed_cap,
		&init_dfa_cap,
		num_category,
		num_circs_per_category
	);
}

pub fn main(){
	let args: Vec<String> = env::args().collect();
	assert!(args.len()>1, "expecting one argument: 'light', 'mid', 'large'");
	println!("args0: {}", args[0]);
	if args[1]=="small"{ small_data::<Fr>(); }
}
