// Optional mimalloc global allocator (feature `mimalloc`): returns
// freed memory to the OS, avoiding glibc per-arena retention of the
// Groth16 FFT/MSM scratch. No effect when the feature is off.
#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// main ZkregPlus Driver
pub mod zkp_driver;
/// the related circuits to handle CP, SED, DFA approx algs.
pub mod circs;
/// the gadgets used by CP, SED, FDA
pub mod gadgets;
