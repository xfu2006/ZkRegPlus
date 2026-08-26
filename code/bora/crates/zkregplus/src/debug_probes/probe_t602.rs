//! T602: validate the naive "double chunk_len -> halve steps, double
//! width per rung" estimate (derived purely from T601's already-
//! measured histogram) against REAL rung assignment on an actual DLP
//! corpus sample. Runs the same discharge -> estimate -> ladder
//! pipeline `full_dlp()` uses (zkp_driver.rs ~6733-6928), on a BOUNDED
//! sample (a prefix of the real production job_0.dat manifest), at
//! chunk_len=64 (sanity check vs T601's known widths) and 128 (the
//! actual test). No fold, no proving: discharge + ladder + circuit
//! layout only (build_circs_adv_aggr is a pure function of DB +
//! capacities, per si_census_probe_and_dlp_shape_2026-08-08). Legacy
//! arm throughout (matches T601's prod log). No edits to zkp_driver.rs
//! or clam_db.rs; non-aggressive path untouched.

#[cfg(test)]
pub mod tests_probe_t602 {
	use ark_bn254::{Fr, G1Projective};
	use folding_schemes::commitment::pedersen::Pedersen;
	use folding_schemes::folding::foldpot::sigma_ir1cs::{
		LookupTableTwoCol as _, SigmaIR1CS as _, GadgetMapper as _,
		WordInfo};
	use folding_schemes::transcript::poseidon::poseidon_canonical_config;
	use rayon::prelude::*;
	use utils::consts::get_global_config;

	use crate::bora_data_driver::create_smaller_config;
	use crate::determine_config::caps_from_params_aggr;
	use crate::stats_helper::{estimate_config_aggr,
		estimated_to_capparams_aggr};
	use crate::zkp_driver::{build_circs_adv_aggr, determine_config_aggr};

	type C1 = G1Projective;
	type CS1 = Pedersen<C1>;

	fn knob(name: &str, dflt: usize) -> usize {
		std::env::var(name).ok().and_then(|s| s.parse().ok())
			.unwrap_or(dflt)
	}

	/// T602: real per-rung (width, count) histogram at chunk_len=64 and
	/// 128 on a bounded real-corpus sample, using the exact production
	/// pipeline (discharge -> estimate_config_aggr ->
	/// estimated_to_capparams_aggr -> determine_config_aggr for the
	/// ladder+histogram, build_circs_adv_aggr + gen_statement_structure
	/// for the REAL stmt_len per rung). Compare against T601's fitted
	/// cost model to see whether the naive doubling estimate survives
	/// real rung migration.
	/// `ZKR_T602_N` (default 3000) sets the sample size (prefix of
	/// data/paper_data/dlp/cfg/jobs/jobs8/job_0.dat, 63,105 files).
	#[test]
	pub fn probe_t602_chunk_double() {
		let proot = utils::os::proj_root();
		let cd = "data/paper_data/dlp/cfg";
		let sig_name = "main_data_dlp_internationl.dat";
		let n_sample = knob("ZKR_T602_N", 3000);
		// RAM guard: the full 9,861-sig production DB alone loads to
		// ~77GB RSS (measured: OOM-killed on this 125GB box, which had
		// a concurrent full_dlp job already holding ~47GB). Thin the
		// sig set so DB-load memory stays bounded; this is a KNOWN
		// deviation from T601's real production widths (see report),
		// not a claim of matching absolute magnitudes -- ZKR_T602_SIGS
		// raises it back toward 9861 on a box with more free RAM.
		let n_sigs_use = knob("ZKR_T602_SIGS", 400);

		get_global_config().log_level = utils::logger::LOG1;
		get_global_config().range2_bit = 25;
		get_global_config().b_read_cache = true;
		get_global_config().b_pin_lkup_share = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		// legacy arm: full_dlp() never flips this, matches T601's log.
		get_global_config().clamav_cfg.b_use_discharge_neo = false;

		let src_dir = format!("{}/{}/regex_pat", proot, cd);
		let scratch = format!("{}/data/debug/t602_probe_scratch_{}",
			proot, n_sigs_use);
		create_smaller_config(&src_dir, sig_name, n_sigs_use, &scratch);
		utils::logger::emit_stdout(format!(
			"DEBUG USE 60602.0b: T602 DB thinned to {} sigs at {}",
			n_sigs_use, scratch));

		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = std::sync::Arc::new(
			data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", scratch, sig_name),
			&format!("{}/main_dfa.dat", scratch),
			&format!("{}/needs_ised.dat", scratch),
			&format!("{}/needs_ised_igc.dat", scratch), &mut vlog,
			&format!("t602_probe_{}", n_sigs_use), true, true)
			.expect("build db"));

		// Bounded sample: STRIDED (not prefix) over the REAL production
		// job_0 manifest (one of the 8 jobs whose PERF logs produced
		// T601's histogram). The list is alphabetical by owner (see
		// full_dlp()'s ZKR_DLP_PCT comment, zkp_driver.rs ~6805-6810):
		// a prefix over-samples one owner's folder and is NOT
		// representative (measured: a 200-file prefix gave 39
		// steps/file vs T601's real corpus-wide 1.836 steps/word --
		// throwing that result out, striding fixes it).
		let manifest = format!("{}/{}/jobs/jobs8/job_0.dat", proot, cd);
		let all: Vec<String> = std::fs::read_to_string(&manifest)
			.expect("read job_0.dat")
			.lines().map(|s| s.to_string()).collect();
		let k = (all.len() / n_sample.max(1)).max(1);
		let sample: Vec<String> =
			all.into_iter().step_by(k).take(n_sample).collect();
		utils::logger::emit_stdout(format!(
			"DEBUG USE 60602.0: T602 sample={} files from {}",
			sample.len(), manifest));

		for &mw in &[64usize, 128usize] {
			let trip: Vec<(Vec<Fr>,
				data_processor::discharge_proof::FailDischargeRecord,
				WordInfo)> = sample.par_iter().map(|fp| {
				let nib = utils::os::read_nibbles(
					&format!("{}/{}", proot, fp));
				let fnib: Vec<Fr> = nib.iter()
					.map(|x| Fr::from(*x as u32)).collect();
				let packed = utils::data::pack_nibbles(&fnib);
				let (fdr, rec) =
				  data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
					fp, &nib, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
					&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
					&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
					&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
					&db.sig_to_id, mw, mw);
				(packed, fdr, rec)
			}).collect();
			let (mut words, mut vdata, mut infos) =
				(vec![], vec![], vec![]);
			for (a, b, c) in trip {
				words.push(a); vdata.push(b); infos.push(c);
			}

			let est = estimate_config_aggr::<Fr>(&vdata, &*db, &[100],
				&mut vlog);
			let seed = estimated_to_capparams_aggr(&est[0], mw, 25, 3);
			let total_word_n: usize =
				words.iter().map(|w| w.len()).sum();
			let lkup_len = db.lkup.get_size();
			let (ladder, hist) = determine_config_aggr::<Fr,C1,CS1>(
				false, db.clone(), &words, &infos, &vdata, seed, mw,
				lkup_len, total_word_n, 4, 2048, 60, 4, 8, 90)
				.expect("determine_config_aggr");

			let caps: Vec<_> = ladder.iter()
				.map(caps_from_params_aggr).collect();
			let poseidon = poseidon_canonical_config::<Fr>();
			let circs = build_circs_adv_aggr::<Fr,C1,CS1>(
				&poseidon, mw, mw, lkup_len, db.clone(), &caps, false);

			let mut tot_n = 0usize;
			let mut tot_hr = 0f64;
			for (i, layer) in circs.iter().enumerate() {
				let circ = &layer[0];
				let lk_share = circ.get_lkup_share_size();
				let mapper = circ.get_mapper();
				let (stmt_len,_,_,_,_) = mapper.lock().unwrap()
					.gen_statement_structure(lk_share);
				let n = hist.get(i).copied().unwrap_or(0);
				// T601's exact fitted model: t(w) = 1.675 + 4.075e-6*w
				let t_step = 1.675f64 + 4.075e-6f64 * (stmt_len as f64);
				let hr = (n as f64) * t_step / 3600.0;
				tot_n += n;
				tot_hr += hr;
				utils::logger::emit_stdout(format!(
					"DEBUG USE 60602.1: mw={} rung={} n={} stmt_len={} \
					 t_step={:.3}s subtotal={:.3}hr",
					mw, i, n, stmt_len, t_step, hr));
			}
			utils::logger::emit_stdout(format!(
				"DEBUG USE 60602.2: mw={} TOTAL n={} total={:.3}hr \
				 rungs={}", mw, tot_n, tot_hr, circs.len()));
		}
	}
}
