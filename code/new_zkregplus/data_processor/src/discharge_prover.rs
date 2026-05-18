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
/// The file path should be "relative" to the project root folder.
/// max_word_len comes from the ZKP capacity (chunk_len) — it
/// determines how the gadget pads the file at the F-element level
/// and so how this scan must pad its nibble stream to match.
pub fn quick_discharge_file<F:PrimeField>(fname: &str, db: &ClamavDB<F>,
	cfg: &ClamavApproxConfig, max_word_len: usize
	)->FailDischargeRecord{
		let abspath = format!("{}/{}", &proj_root(), fname);
		let nibbles = read_nibbles(&abspath);
		quick_discharge_file_by_crit_bag_pm(
			fname, &nibbles,
			&db.vec_sigs,
			&db.vec_sigs_no_critical_pat,
			&db.map_crit_pat, &db.map_crit_pat_igc,
			&db.dfa_crit,
			&db.bundle_subsig.vec_acdfa[0], // dfa_patterns,
			&db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
			true, cfg,
			&db.sig_to_id, max_word_len).0 //use optimize for 'true'
}

/// Really discharge each one by one by generating the real proof.
pub fn discharge_file<F:PrimeField>(_fname: &str, _db: &ClamavDB<F>,
	_cfg: &ClamavApproxConfig
	)->FailDischargeRecord{
		unimplemented!("discharge_file not done yet")
}

