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
	use utils::consts::get_global_config;

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
