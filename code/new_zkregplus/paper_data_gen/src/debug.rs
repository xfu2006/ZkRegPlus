/// Debug use purpose
/* Created 07/26/2024
*/

use utils::{
	logger::{log, log_perf, LOG1},
	timer::{Timer},
};
use crate::{
	clam_data::{report_all_discharge_approach_stats},
};
use ark_ff::{PrimeField};

/// debug use
pub fn debug<F:PrimeField>(){
	log(LOG1, &format!("DEBUG CLAMAV data ..."));
	let mut timer = Timer::new();
	//1. Generate clamav related data
	let b_cache = false;
	let b_quick = true;
	
	report_all_discharge_approach_stats::<F>(
		"data/paper_data/config/non_pm_reg.dat", //src sig
		"data/paper_data/config/non_pm_reg_dfa.dat", //need_dfa_set
		"data/paper_data/config/needs_ised.dat", //need_ised
		"data/paper_data/config/needs_ised_igc.dat", //need_ised_igc
		"data/paper_data/config/binexec.dat", //list of files to discharge
		"data/paper_data/reports/DEBUG.dat", //report
		b_cache, //read cache
		"debug", //cache name
		b_quick);
	log_perf(LOG1, "CLAMAV Data Generation", &mut timer);
}
