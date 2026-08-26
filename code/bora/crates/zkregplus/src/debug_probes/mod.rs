//! Investigation-probe harnesses.
//!
//! These are one-off measurement/replay harnesses written to answer a
//! specific internal question; they are entirely `#[cfg(test)]`-gated
//! and compile to nothing in a normal build.  They are NOT part of the
//! golden path that reproduces any paper result -- that is
//! `scripts/INSTALL.py` and `scripts/PAPER_DATA.py`.

/// T601-C: forces phase-level log verbosity during numa_probe_dlp's
/// real multi-job fold, to measure job-concurrency contention.
pub mod probe_t601c;
/// T602: real chunk_len=64 vs 128 rung histogram on a bounded DLP
/// corpus sample, validating T601's naive doubling estimate.
pub mod probe_t602;
/// T9906 PROBE (read-only): replays the neo non-aggr ladder descent
/// from a real ladder.json and scores rung-1 T_qm budget policies.
pub mod probe_t9906;
