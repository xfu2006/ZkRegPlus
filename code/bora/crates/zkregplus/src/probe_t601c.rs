//! T601-C: force phase-level (LOG5) log verbosity during
//! `numa_probe_dlp`'s REAL multi-job rayon fold (vendored
//! `driver.rs`'s `jobs.into_par_iter().for_each`), so `prove_step`'s
//! existing phase timers print under genuine job concurrency instead
//! of being extrapolated from a single-job run. `numa_probe_dlp`
//! hardcodes LOG3 at its own start and nothing later in the path
//! restores it, so a background thread keeps re-asserting the target
//! level for the run's duration. Calls `numa_probe_dlp` unmodified;
//! no edits to zkp_driver.rs or the vendored foldpot driver.

#[cfg(test)]
pub mod tests_probe_t601c {
	use std::sync::atomic::{AtomicBool, Ordering};
	use std::sync::Arc;
	use std::time::Duration;
	use utils::consts::{get_global_config, read_global_config};

	use ark_bn254::{constraints::PairingVar, Bn254, Fr, G1Projective,
		G2Projective};
	use ark_groth16::Groth16;
	use ark_grumpkin::{constraints::GVar as GVar2,
		Projective as Projective2};
	use ark_bn254::constraints::GVar;
	use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};

	use crate::circs::{cp_mapper::CpCapacity, sed_mapper::SedCapacity};
	use crate::zkp_driver::{zkp_driver_adv_aggr, DcMode};

	// Driver instantiation, matching zkp_driver.rs's cfg(test) module
	// (those aliases are private there; same duplication bora_data_
	// driver.rs already does, same reason).
	type C1 = G1Projective;
	type CS1 = Pedersen<C1>;
	type C2G2 = G2Projective;
	type C2 = Projective2;
	type GC1 = GVar;
	type GC2 = GVar2;
	type CS1E = KZG<'static, Bn254>;
	type CS2 = Pedersen<C2>;
	type S = Groth16<Bn254>;

	fn knob(name: &str, dflt: usize) -> usize {
		std::env::var(name).ok().and_then(|s| s.parse().ok())
			.unwrap_or(dflt)
	}

	/// T601-C: measure REAL job-concurrency contention on prove_step,
	/// instead of extrapolating from a single-job run. Reuses dlp_hard's
	/// exact setup (crates/zkregplus/src/zkp_driver.rs ~2910-3026,
	/// COPIED not called -- dlp_hard hardcodes a 1-entry scan_files
	/// Vec, and per the project rule zkp_driver.rs itself is not to be
	/// edited) so the circuit is byte-identical to prior T601-B runs;
	/// the only change is passing N copies of the SAME scan manifest,
	/// which zkp_driver_adv_aggr turns into N independent FoldPotJob
	/// entries (zkp_driver.rs:2035-2048), dispatched by the REAL
	/// production mechanism (vendored driver.rs:3092
	/// `jobs.into_par_iter().enumerate().for_each`) -- one shared rayon
	/// pool, exactly like production's per-process job group.
	/// ZKR_PROBE_NJOBS (default 1) sets the job count; ZKR_SCAN/
	/// ZKR_LOG/ZKR_FOLD_ONLY/etc mirror dlp_hard's own knobs so N=1
	/// here reproduces the earlier single-job T601-B measurement.
	#[test]
	pub fn probe_t601c_multijob() {
		let n_jobs = knob("ZKR_PROBE_NJOBS", 1);
		let neo_on = false; // legacy arm, matching the prod log analyzed
		get_global_config().clamav_cfg.b_use_discharge_neo = neo_on;
		get_global_config().snark_cache_dir = "dlp_hard".to_string();
		get_global_config().log_level =
			knob("ZKR_LOG", utils::logger::LOG3);
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().b_folding_only =
			knob("ZKR_FOLD_ONLY", 0) != 0;
		get_global_config().range2_bit = knob("ZKR_RANGE2", 20);
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share =
			knob("ZKR_LKSHARE", if neo_on {20} else {1});
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap =
			knob("ZKR_FANOUT", 100);
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().clamav_cfg.b_sde_rep_tight_first_leg = false;
		get_global_config().b_dryrun_after_capcheck =
			knob("ZKR_DRYRUN", 0) != 0;
		get_global_config().res_small_cost = knob("ZKR_SMALL", 20);
		get_global_config().b_read_cache = false;
		get_global_config().aggr_needs_subsigs = knob("ZKR_NEEDS", 256);

		let set1 = "data/debug/dlp_hard_set/config";
		let scan = std::env::var("ZKR_SCAN")
			.unwrap_or("scan_hard.dat".to_string());
		let max_word = knob("ZKR_CHUNK", 256);
		let sigs = knob("ZKR_SIGS", 111);
		let subsigs = knob("ZKR_SUBSIGS", 500);
		let avg_pats_per_subsig = knob("ZKR_AVGPATS", 4);
		let avg_active_pats_per_subsig = knob("ZKR_AVGACT", 7);
		let perc_comp_subsigs = knob("ZKR_COMPPERC", 20);
		let basis_unique_states = knob("ZKR_UNIQ", 150);
		let basis_acc_states = knob("ZKR_ACC", 600);
		let basis_pats_in_trace = knob("ZKR_TRACE", 700);
		let perc_pats_expansion_rate = knob("ZKR_PERC", 300);

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);

		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);

		let cs_caps: Vec<_> = std::iter::repeat(
			(init_cp_cap, init_sed_cap, init_cp_cap_igc, init_sed_cap_igc))
			.take(1).collect();

		// THE ONLY SUBSTANTIVE CHANGE vs dlp_hard: N copies of the same
		// manifest -> N independent concurrent FoldPotJob entries.
		let scan_files: Vec<String> = std::iter::repeat(
			format!("{}/{}", set1, scan)).take(n_jobs.max(1)).collect();

		utils::logger::log(0, utils::logger::LOG1, &format!(
			"DEBUG USE 60601.2: T601-C multijob probe, n_jobs={}",
			n_jobs));

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main.dat", set1),
			scan_files,
			"data/debug/dlp_hard_set/reports/report.dat",
			false, //b_write_cache
			"dlp_hard", //cache name
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat", set1),
			max_word,
			&cs_caps,
			false, //b_check_lkup
			DcMode::Off,
		);
	}

	#[test]
	pub fn probe_t601c_np_log_bump() {
		let target = std::env::var("ZKR_PROBE_LOG").ok()
			.and_then(|s| s.parse::<usize>().ok())
			.unwrap_or(utils::logger::LOG5);
		let stop = Arc::new(AtomicBool::new(false));
		let stop2 = stop.clone();
		let h = std::thread::spawn(move || {
			while !stop2.load(Ordering::Relaxed) {
				get_global_config().log_level = target;
				std::thread::sleep(Duration::from_millis(20));
			}
		});
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"DEBUG USE 60601.1: T601-C log-bump active, target={}",
			target));
		crate::zkp_driver::tests_zkp_driver::numa_probe_dlp();
		stop.store(true, Ordering::Relaxed);
		let _ = h.join();
	}
}
