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
