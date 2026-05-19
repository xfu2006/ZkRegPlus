/// Generate all paper data.
/// All reports in data/paper_data
/* Created 07/26/2024
*/

use utils::{
	logger::{log, log_perf, LOG1},
	timer::{Timer},
	consts::B_DEBUG,
};
use paper_data_gen::{
	clam_data::{report_all_discharge_approach_stats},
	debug::{debug},
};
use ark_ff::{PrimeField};

fn gen_clamav_data<F:PrimeField>(){
	log(0, LOG1, &format!("Generating CLAMAV data ..."));
	//let mut timer = Timer::new();
	//1. Generate clamav related data
	let b_cache = false;
	let b_quick = true;

	/* DEBUG USE smaller data set of 20 sigs but with 3 tough sigs
	report_all_discharge_approach_stats::<F>(
		"data/paper_data/config/main_20.dat", //src sig
		"data/paper_data/config/main_dfa_20.dat", //need_dfa_set
		"data/paper_data/config/needs_ised_20.dat", //need_dfa_set
		"data/paper_data/config/needs_ised_igc_20.dat", //need_dfa_set
		"data/paper_data/config/binexec_20.dat", //list of files to discharge
		"data/paper_data/reports/discharge_main20_binexec.dat", //report
		b_cache, //read cache
		"main_20", //cache name
		b_quick);
	*/

	report_all_discharge_approach_stats::<F>(
		"data/paper_data/debug_config/main.dat", //src sig
		"data/paper_data/debug_config/main_dfa.dat", //need_dfa_set
		"data/paper_data/debug_config/needs_ised.dat", //need_dfa_set
		"data/paper_data/debug_config/needs_ised_igc.dat", //need_dfa_set
		"data/paper_data/debug_config/binexec.dat", //list of files to discharge
		"data/paper_data/reports/discharge_main_binexec.dat", //report
		b_cache, //read cache
		"main", //cache name
		b_quick);

/*
	report_all_discharge_approach_stats::<F>(
		"data/paper_data/config/main.dat", //src sig
		"data/paper_data/config/main_dfa.dat", //need_dfa_set
		"data/paper_data/config/emails.dat", //list of files to discharge
		"data/paper_data/reports/discharge_main_emails.dat", //report
		b_cache, //read cache
		"main_20", //cache name
		b_quick);
	log_perf(LOG1, "CLAMAV Data Generation", &mut timer);
	*/
}

/// generate all paper data -> data/paper_data/reports
fn generate_data<F:PrimeField>(){
	let mut timer = Timer::new();
	gen_clamav_data::<F>();
	log_perf(0, LOG1, "Total Reporting Time", &mut timer);
}

fn main() {
	use ark_bn254::{Fr};
	println!("VERSOIN 1.0");
	let b_debug = B_DEBUG;
	if b_debug {
		debug::<Fr>();
	}else{
		use utils::consts::get_global_config;
		get_global_config().range2_bit = 26;
		generate_data::<Fr>();
	}
	println!("**** COMPLETED for mode: {} ****", b_debug);	
}
