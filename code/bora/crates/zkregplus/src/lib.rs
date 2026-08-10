// Optional mimalloc global allocator (feature `mimalloc`): returns
// freed memory to the OS, avoiding glibc per-arena retention of the
// Groth16 FFT/MSM scratch. No effect when the feature is off.
#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// main ZkregPlus Driver
pub mod zkp_driver;
/// discharge-approach reporting / stats helpers (ported from
/// paper_data_gen). Driven by test_db_bundle() in zkp_driver.
pub mod stats_helper;
/// the related circuits to handle CP, SED, DFA approx algs.
pub mod circs;
/// the gadgets used by CP, SED, FDA
pub mod gadgets;
/// auto capacity tuner: estimate -> Pass-1 probe -> bump-on-CapErr loop
/// to find the confirmed-lowest config for discharging a sample set.
pub mod determine_config;
/// M11 per-chunk capacity ladder planner (aggressive SDE only).
pub mod band_dp;
/// per-chunk NEEDS distribution study (aggressive SDE mode only).
pub mod needs_dist;
/// M0 flag-off regression fingerprint (caps universe + r1cs dims).
pub mod fingerprint;
/// paper-data support functions (perc-driven dataset thinning, Q2
/// lookup-composition report), sibling to zkp_driver.
pub mod bora_data_driver;
/// T601-C: forces phase-level log verbosity during numa_probe_dlp's
/// real multi-job fold, to measure job-concurrency contention.
pub mod probe_t601c;
/// T602: real chunk_len=64 vs 128 rung histogram on a bounded DLP
/// corpus sample, validating T601's naive doubling estimate.
pub mod probe_t602;
