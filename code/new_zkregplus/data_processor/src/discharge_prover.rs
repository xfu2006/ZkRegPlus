/// This module contains the prover function for generating discharging
/// proofs (discharging a file against a clamav signature database, i.e.,
/// the file is FREE of matching of these signatures)

/* Created 07/26/2024
*/

use utils::{
	os::{proj_root,read_nibbles},
};
use ark_ff::PrimeField;
use crate::{
	type_def::{ClamavApproxConfig},
	clamav::{quick_discharge_file_by_crit_bag_pm},
	clam_db::{ClamavDB},
	discharge_proof::{FailDischargeRecord},
};

/// WRAPPER of the quick_discharge_file_by_crit_bag_pm in clamav.rs
/// The file path should be "relative" to the project root folder
pub fn quick_discharge_file<F:PrimeField>(fname: &str, db: &ClamavDB<F>,
	cfg: &ClamavApproxConfig
	)->FailDischargeRecord{
		let abspath = format!("{}/{}", &proj_root(), fname);
		let nibbles = read_nibbles(&abspath); 
		quick_discharge_file_by_crit_bag_pm(
			fname, &nibbles,
			&db.vec_sigs,
			&db.map_crit_pat, &db.map_crit_pat_igc, 
			&db.dfa_crit, 
			&db.bundle_subsig.vec_acdfa[0], // dfa_patterns, 
			&db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
			true, cfg) //use optimize mode for 'true'
}

/// Really discharge each one by one by generating the real proof.
pub fn discharge_file<F:PrimeField>(_fname: &str, _db: &ClamavDB<F>,
	_cfg: &ClamavApproxConfig
	)->FailDischargeRecord{
		unimplemented!("discharge_file not done yet")
}

