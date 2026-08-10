/// Constants system wide
///
/// Created 01/04/2024

//pub const CLAMAV_SRC:&str = "./data/clamav/src/main.ldb";
//pub const CLAMAV_SRC:&str = "./data/clamav/src/test.ldb";
pub const TEST_MODE:bool = true; //if true disable the check of zero length pattern
pub const CLAMAV_GEN_REGEX:&str = "./data/clamav/categories/all_others.dat";
pub const CLAMAV_PCRE_REGEX:&str = "./data/clamav/categories/pcre.dat";
pub const CLAMAV_GEN_REGEX_SAMPLES:&str = "./data/clamav/categories/all_others_samples.dat";
pub const CLAMAV_PM_REGEX:&str = "./data/clamav/categories/pm_reg.dat";
pub const CLAMAV_PM_REGEX_SMALL:&str = "./data/clamav/categories/pm_reg_small.dat";
pub const SNORT_PCRE_REGEX:&str = "./data/snort/snort.ldb";
pub const B_DEBUG:bool = false;
//pub const CLAMAV_PM_REGEX:&str = "./data/clamav/categories/pm_reg_small.dat";
pub const CLAMAV_DST:&str = "./data/clamav/dest/";
pub const CRIT_PAT_FILE_PM:&str = "./data/clamav/dest/crit_pat_pm.dat";
pub const ALL_PAT_FILE_PM:&str = "./data/clamav/dest/all_pat_pm.dat";
pub const SIG_FILE_PM:&str = "./data/clamav/dest/sigs_pm.dat";
pub const CRIT_PAT_FILE_GENERAL:&str = 
	"./data/clamav/dest/crit_pat_general.dat";
pub const ALL_PAT_FILE_GENERAL:&str = "./data/clamav/dest/all_pat_general.dat";
pub const SIG_FILE_GENERAL:&str = "./data/clamav/dest/sigs_general.dat";
pub const LIST_EXEC:&str = "./data/list_exec.txt";
pub const LIST_EXEC_SAMPLE:&str = "./data/list_exec_sample.txt";
pub const LIST_EMAIL:&str = "./data/email_all.txt";
pub const B_SINGLE_JOB_MODE:bool = true;
/// always reload a data file even if it exists
pub const ALWAYS_INIT:bool = true;

pub const ADD_CHAIN_SIZE: usize = 64;

use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, Arc, Mutex};
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use serde::{Serialize, Deserialize};

/// Flag-off regression fingerprint sink: flat (label, value) pairs
/// emitted by build_circs_adv (universe) and gen_step_cs (r1cs dims).
/// None = disabled (default), so production runs are unaffected.
pub type FpSink = Arc<Mutex<Vec<(String, u64)>>>;

/// Probe-only: chunk index of the current chunk-loop iteration. Set
/// by foldpot driver before each gen_nd_advice call so SED probes
/// can correlate StepQueue dumps with chunk_id.
pub static PROBE_CHUNK_ID: AtomicUsize = AtomicUsize::new(0);

/// Set true ONLY at the top of collect_scale_data(); gates the per-step
/// forward-queue membership dump so it can never fire
/// from any other code path (run_full_dlp, normal prover, etc.).
pub static SCALE_DUMP_FWD: AtomicBool = AtomicBool::new(false);

/// Post-convergence cap tightening: max ACTUAL fill seen per fold step,
/// recorded by the gadgets (replaces the 6901.8 / 6902.1 println probes).
/// fwd = discharge forward queue (v2d[0].len); acc = SDE accepting states.
pub static MAX_ACC_CS:  AtomicUsize = AtomicUsize::new(0);
pub static MAX_ACC_IGC: AtomicUsize = AtomicUsize::new(0);
/// Legacy forward-queue saturation, indexed by `b_igc as usize`. Was
/// two independent AtomicUsize maxima; a SatGauge so legacy and neo
/// report the SAME statistic (max over chunks of fill_i/cap_i).
pub static FWD_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];
pub fn record_fwd(b_igc: bool, fill: usize, cap: usize) {
    FWD_SAT[b_igc as usize].record(fill, cap);
}
pub fn record_acc(b_igc: bool, n: usize) {
    (if b_igc {&MAX_ACC_IGC} else {&MAX_ACC_CS}).fetch_max(n, Ordering::Relaxed);
}
/// Self-verification failures (verify_batch / verify_individual).
/// foldpot deliberately does NOT abort on these -- one failed job must
/// not kill the other, very expensive, jobs -- so the failure reaches
/// only the log while cargo still prints `ok`. Tests assert this is 0.
pub static VERIFY_FAILS: AtomicUsize = AtomicUsize::new(0);
pub fn record_verify_fail() {
    VERIFY_FAILS.fetch_add(1, Ordering::Relaxed);
}
pub fn get_verify_fails() -> usize {
    VERIFY_FAILS.load(Ordering::Relaxed)
}
pub fn reset_sat() {
    for a in [&MAX_ACC_CS, &MAX_ACC_IGC] {
        a.store(0, Ordering::Relaxed);
    }
    //runs at the top of each tuner retry, so the count a test reads
    //belongs to the FINAL fold -- the only one whose proof matters.
    VERIFY_FAILS.store(0, Ordering::Relaxed);
    for g in QM_SAT.iter().chain(QC_SAT.iter())
        .chain(QM_WRAP_SAT.iter()).chain(QM_REAL_SAT.iter())
        .chain(QM_SUB_SAT.iter()).chain(FWD_SAT.iter()) { g.reset(); }
    if let Ok(mut v) = STEP_TIMES.lock() { v.clear(); }
    if let Ok(mut v) = CIRC_SIZES.lock() { v.clear(); }
}
/// PEAK fill, independent of cap. Unchanged contract: the tuner seeds
/// its capacity back-solve from the largest emission, not a ratio.
pub fn get_fwd(b_igc: bool) -> usize {
    FWD_SAT[b_igc as usize].get().0
}
pub fn get_fwd_cap(b_igc: bool) -> usize {
    FWD_SAT[b_igc as usize].get().1
}
pub fn get_acc(b_igc: bool) -> usize {
    (if b_igc {&MAX_ACC_IGC} else {&MAX_ACC_CS}).load(Ordering::Relaxed)
}

/// DEBUG USE 62070: single env gate (ZKR_PROBE_P36) for the NewP3.6
/// saturation + lookup-share probes. Read once; every 62070.x site is
/// log-only and must stay behind it.
pub fn b_probe_p36() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var("ZKR_PROBE_P36").is_ok())
}

/// Per-chunk saturation ratios are held as integers scaled by this
/// (parts per million) so the gauge stays lock-free. ppm / 10_000 = %.
pub const SAT_SCALE: usize = 1_000_000;

/// Saturation of one queue. Saturation is the PER-EMISSION ratio
/// fill_i/cap_i maximised over emissions; peak fill and peak cap are
/// also kept, but their quotient is NOT a saturation (they peak on
/// different chunks whenever chunks get different capacities).
pub struct SatGauge {
    fill: AtomicUsize,
    cap: AtomicUsize,
    max_ratio: AtomicUsize,
    max_pair: AtomicUsize,
    sum_ratio: AtomicUsize,
    n: AtomicUsize,
}
impl SatGauge {
    pub const fn new() -> Self {
        Self { fill: AtomicUsize::new(0), cap: AtomicUsize::new(0),
            max_ratio: AtomicUsize::new(0),
            max_pair: AtomicUsize::new(0),
            sum_ratio: AtomicUsize::new(0), n: AtomicUsize::new(0) }
    }
    /// Record ONE emission. fill and cap arrive together, so the ratio
    /// below can never mix one chunk's fill with another's capacity --
    /// which is exactly what the two fetch_max lines do.
    pub fn record(&self, fill: usize, cap: usize) {
        if cap == 0 { return; } //absent gauge, not a 0% chunk
        self.fill.fetch_max(fill, Ordering::Relaxed);
        self.cap.fetch_max(cap, Ordering::Relaxed);
        //u128 intermediate: fill*SAT_SCALE only overflows usize for
        //absurd fills, but the guard is free here.
        let r = ((fill as u128) * (SAT_SCALE as u128)
            / (cap as u128)) as usize;
        self.sum_ratio.fetch_add(r, Ordering::Relaxed);
        self.n.fetch_add(1, Ordering::Relaxed);
        let m = u32::MAX as usize;
        let pair = (fill.min(m) << 32) | cap.min(m);
        //CAS the ratio, then publish the winner's pair. A slower
        //thread may overwrite the pair with a LOWER-ratio one; that
        //blurs only the reported witness, never max_ratio itself.
        let mut cur = self.max_ratio.load(Ordering::Relaxed);
        while r > cur {
            match self.max_ratio.compare_exchange_weak(cur, r,
                Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => { self.max_pair.store(pair,
                    Ordering::Relaxed); break; },
                Err(c) => cur = c,
            }
        }
    }
    /// Peak fill and peak cap, taken INDEPENDENTLY. NOT a saturation
    /// -- use get_max(). Kept because the tuner back-solves capacity
    /// from the largest emission.
    pub fn get(&self) -> (usize, usize) {
        (self.fill.load(Ordering::Relaxed), self.cap.load(Ordering::Relaxed))
    }
    /// (ratio_ppm, fill, cap) of the most saturated single emission.
    /// ratio can exceed SAT_SCALE: gen_qm_table records BEFORE its
    /// CapErr check, so an overflowing chunk reads >100% on the way out.
    pub fn get_max(&self) -> (usize, usize, usize) {
        let r = self.max_ratio.load(Ordering::Relaxed);
        let p = self.max_pair.load(Ordering::Relaxed);
        //an all-empty dataset never wins the CAS, so fall back to the
        //peak cap: "0/32" says the gauge ran and found nothing, while
        //"0/0" reads like the gauge never fired at all.
        if r == 0 { return (0, 0, self.cap.load(Ordering::Relaxed)); }
        (r, p >> 32, p & (u32::MAX as usize))
    }
    /// (mean_ratio_ppm, n). Mean is per EMISSION, not strictly per
    /// chunk -- a chunk whose advice is regenerated records twice.
    pub fn get_mean(&self) -> (usize, usize) {
        let n = self.n.load(Ordering::Relaxed);
        if n == 0 { return (0, 0); }
        (self.sum_ratio.load(Ordering::Relaxed) / n, n)
    }
    fn reset(&self) {
        for a in [&self.fill, &self.cap, &self.max_ratio,
            &self.max_pair, &self.sum_ratio, &self.n] {
            a.store(0, Ordering::Relaxed);
        }
    }
}

/// Neo (App G.1) queue saturation, indexed by `b_igc as usize`. Q_m =
/// T_qm rows vs the budget CapErr guards; Q_c = committed carry, which
/// is the next chunk's Q_i, so one gauge covers both.
pub static QM_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];
pub static QC_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];

/// Q_m split gauges, same indexing. WRAP = (subsig,step) key groups
/// vs the wrap budget; REAL = non-wrap rows vs ResLarge; SUB = active
/// subsigs per chunk vs capacity.subsigs. QM_SAT conflates the first two.
pub static QM_WRAP_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];
pub static QM_REAL_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];
pub static QM_SUB_SAT: [SatGauge; 2] = [SatGauge::new(), SatGauge::new()];

/// Worst-SINGLE-CHUNK saturation of every neo gauge, via get_max (not
/// get, whose fill and cap peaks come from different chunks and so can
/// hide a saturated one). ">100%" marks an over-budget emission.
pub fn sat_report_max() -> String {
    let gs: [(&str, &[SatGauge; 2]); 6] = [
        ("Q_m", &QM_SAT), ("Q_c", &QC_SAT), ("wrap", &QM_WRAP_SAT),
        ("real", &QM_REAL_SAT), ("sub", &QM_SUB_SAT), ("fwd", &FWD_SAT)];
    let mut out: Vec<String> = vec![];
    for (name, g) in gs.iter() {
        for (i, arm) in ["cs", "igc"].iter().enumerate() {
            let (r, f, c) = g[i].get_max();
            if c == 0 { continue; }   // gauge never fired
            let over = if r > SAT_SCALE { " OVER" } else { "" };
            out.push(format!("{} {}={}/{} ({:.1}%{})", name, arm, f, c,
                100.0 * (r as f64) / (SAT_SCALE as f64), over));
        }
    }
    out.join("; ")
}

/// Per-fold-step prove_step wall time in microseconds, in step order.
/// Recorded by the foldpot driver's Pass-3 loop; reset by reset_sat()
/// so each measured fold starts clean. Empty unless a fold ran.
pub static STEP_TIMES: Mutex<Vec<usize>> = Mutex::new(Vec::new());

/// Append one fold step's prove_step cost (microseconds).
pub fn record_step_time(us: usize) {
    if let Ok(mut v) = STEP_TIMES.lock() { v.push(us); }
}
/// Snapshot the per-step times recorded since the last reset_sat().
pub fn get_step_times() -> Vec<usize> {
    STEP_TIMES.lock().map(|v| v.clone()).unwrap_or_default()
}

/// Per-circuit R1CS dimensions (cols, rows), in ladder-rung order, as
/// sized during preprocessing. Same lifecycle as STEP_TIMES.
pub static CIRC_SIZES: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());

/// Append one circuit's R1CS (cols, rows).
pub fn record_circ_size(cols: usize, rows: usize) {
    if let Ok(mut v) = CIRC_SIZES.lock() { v.push((cols, rows)); }
}
/// Snapshot the circuit sizes recorded since the last reset_sat().
pub fn get_circ_sizes() -> Vec<(usize, usize)> {
    CIRC_SIZES.lock().map(|v| v.clone()).unwrap_or_default()
}

/// Knobs that govern ClamAV PCRE approximation when building the
/// pattern DB. Lives in utils so GlobalConfig can embed it;
/// data_processor::type_def re-exports it for legacy imports.
#[derive(Copy,Clone,Debug,PartialEq,Serialize,Deserialize)]
pub struct ClamavApproxConfig{
	/// Max pm-reg sections allowed (longer is approximated).
	/// `(abc.{10,10}){20,inf}` with max=5 -> `(abc.{10,10}){5,5}.*`.
	pub max_pm_sections: usize,
	/// Cap on alternation cartesian expansion in
	/// pcre_to_rustomaton_regex: `(a|b)(c|d)` expands to
	/// `(ac|ad|bc|bd)` only if this limit > 4.
	pub combination_limit: usize,
	/// Repeat unfolding cap. `(abc.{10})+` is approximated as
	/// `(abc.{10}){N,N}.*` with N = repeat_limit; conservative in
	/// non-negative contexts. Saves PM-reg cost.
	pub repeat_limit: usize,
	/// Minimum word length to be included in bag-of-words and
	/// PM-reg. When no words of sufficient length are found the
	/// bag is empty, automatically triggering the subsignature.
	pub min_bag_len: usize,
	/// Minimum word length for inclusion in PM-reg (SED) approach.
	pub min_pm_word_len: usize,
	/// Gate: aggressively fan out class repetitions (e.g.
	/// `[0-9]{n}`) into a union of concrete SED subsig variants.
	/// Default false reproduces baselines exactly.
	pub b_aggressive_sde_for_rep: bool,
	/// M3+: route SDE discharge through discharge_adv_neo (App G.1
	/// constant-queue). Off => legacy discharge_adv. Both modes.
	pub b_use_discharge_neo: bool,
	/// Fan-out budget for aggressive SDE class-rep expansion.
	/// Read only by expand_rep_subsig; inert when
	/// b_aggressive_sde_for_rep is off.
	pub sde_rep_fanout_cap: usize,
	/// Per-variant cap on alternation cartesian expansion when
	/// each aggressive-SDE variant is re-rewritten through
	/// pcre_to_rustomaton_regex. Inert when b_aggressive_sde_for_rep is off.
	pub variant_combine_cap: usize,
	/// Slot picker variant: pin TWO adjacent bytes at the first
	/// leg + ONE byte at the last leg, skip middle legs entirely.
	/// Produces a 5-hex-char first anchor (vs 3 chars) at the
	/// cost of more variants per sig. Inert when
	/// b_aggressive_sde_for_rep is off.
	pub b_sde_rep_tight_first_leg: bool,
	/// Per-sig fan-out multiplier for SITs listed in main_fanout.dat
	/// (co-located with the needs_dfa file). 1 = no boost. Inert when
	/// b_aggressive_sde_for_rep is off or the file is absent.
	#[serde(default = "fanout_boost_default")]
	pub sde_rep_fanout_boost: usize,
}

/// serde fallback for sde_rep_fanout_boost on configs that predate the
/// field: 1 = no boost (so old configs reproduce baseline fan-out).
fn fanout_boost_default() -> usize { 1 }

/// full_clam manifest-slice selector for the two-half NUMA scheme.
/// Full = first pct% of a job's file list; FirstHalf/SecondHalf = the
/// two contiguous pct/2 halves of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClamReadMode { Full, FirstHalf, SecondHalf }

pub struct GlobalConfig {
    pub log_level: usize,
    pub range2_bit: usize,

    /// Compression ratio sizing the ResSmall CARRIED step queue (Q_i on
    /// the way in, Q_c on the way out), as a percent-of-percent factor
    /// in StepQueue::vec_size: n = max_nibble * basis_pats * perc *
    /// res_small_cost / 1e8. 100 = no compression; the shipped default
    /// 20 (= discharge_adv::RES_SMALL_COST, kept as the single source
    /// of truth) is a 5x tightening tuned 2026-05-09. LOWER IT to drive
    /// the carried queue toward full saturation when calibrating a
    /// legacy-vs-neo comparison -- an over-sized carry makes BOTH arms
    /// pay for padding and hides the real cost difference. Copied into
    /// DischargeAdvCapacity at construction, so a change takes effect
    /// for capacities built AFTER the write.
    pub res_small_cost: usize,
    pub min_basis_unique_states: usize,
    pub min_subsigs: usize,
    /// Same floor for the ignore-case SED arm. Separate because the two arms
    /// can have very different obligation-set demand (clam_hard: cs 59, igc
    /// 1); one shared floor would clamp the igc rungs ABOVE the igc top rung.
    /// 0 = inherit min_subsigs, so every cell that sets only min_subsigs
    /// keeps its exact previous ladder. Read via min_subsigs_for(b_igc).
    pub min_subsigs_igc: usize,
    /// CP ladder floor. CpCapacity.subsigs shares min_subsigs with the SED
    /// arm, so a CP seed below the SED floor would be clamped back up.
    /// 0 = inherit min_subsigs. Read via min_cp_subsigs_val().
    pub min_cp_subsigs: usize,
    pub min_dfa_subsigs: usize,
    pub min_sigs: usize,
    pub min_dfa_sigs: usize,
    pub min_avg_pats_per_subsig: usize,
    pub min_avg_active_pats_per_subsig: usize,
    pub min_basis_pats_in_trace: usize,
    pub min_perc_pats_expansion_rate: usize,
    pub min_sigs_sed: usize,
    pub min_perc_comp_subsigs: usize,
    pub min_basis_acc_states: usize,
    pub b_light_test: bool,
    pub b_folding_only: bool,
    // print the 6901.8 forward-queue (StepFwdPrf) saturation rate, but only
    // when it exceeds 85%. Off by default; turned on for collect_scale_data so
    // the run wrapper can audit that each tuned config is well-utilized.
    pub b_show_queue_saturated: bool,
    // SCALE finalize (collect_scale_data_dlp): route fold CapErrs through
    // catchable unwinding instead of process::exit / fail-fast abort, so the
    // scale bump-retry finalizes caps. Default false -> full_dlp/full_clam/
    // full_dna unchanged.
    pub b_scale_catch_caperr: bool,
    pub b_read_cache: bool,
    pub b_write_snark_cache: bool, //write the generated snark key to cache
    pub b_read_snark_cache: bool,
    pub snark_cache_dir: String,
    pub n_par_snark: usize,
    pub n_par_snark_cp: usize,
    pub n_par_batch_claim: usize,
    // Cap for the ENTIRE snark proof-generation region (outer sema).
    // 0 = AUTO: use the sum n_par_snark + n_par_snark_cp (legacy
    // behaviour). A smaller value forces fewer concurrent deciders to
    // cap peak RAM; clamped to the sum at the use-site.
    pub n_par_snark_total: usize,
    pub b_resume: bool,
	pub perc_lkup_share: usize, //percentae of the lkup share
					//compared with nibble length of a segment
					//e.g., for 700MB linux data (8 jobs) with 256M lkup table
					//each job (in total) has 90MB data = 180M nibbes
					// the perc_lkup_share = 256/180 * 100 = 143 percent
	/// NewP3.6 T1: true = the runner's hand-set perc_lkup_share is FINAL and
	/// the driver's back-solve must not touch it. Set by the production
	/// runners (full_clamav / full_dlp / full_dna) to pin legacy behavior.
	pub b_pin_lkup_share: bool,
	/// T217: mirrors the driver's b_check_lkup param, so a mapper (which
	/// only sees GlobalConfig, not the driver call) can tell whether this
	/// run enforces the hab22 lookup balance. The 8_B dummy self-cover in
	/// composable_gadget_mapper.rs reads it: unchecked runs skip the
	/// self-cover so the never-stepped dummy stmt never forces
	/// perc_lkup_share up to cover its own pad-word query universe.
	/// Default true so any path that never calls zkp_driver{,_adv,
	/// _adv_aggr} keeps today's (self-cover always on) behavior.
	pub b_check_lkup: bool,
	/// Optional cap on number of words processed per job (per Pass).
	/// 0 = unlimited. Used for fast diagnostic runs that reproduce the
	/// stall without burning hours. See driver.rs pass_all word loops.
	pub word_cap_per_job: usize,
	/// Stall watchdog: if all per-job logs are silent this many seconds,
	/// foldpot_main dumps thread state and aborts. 0 = disabled.
	pub stall_watchdog_secs: usize,
	/// Single source of truth for ClamavApproxConfig.
	/// default_clamav_cfg() returns a Copy of this field; runners
	/// set knobs via get_global_config().clamav_cfg.X = Y.
	pub clamav_cfg: ClamavApproxConfig,
	/// If true, zkp_driver_adv returns after build_circs_adv
	/// finishes capacity validation, skipping foldpot_main /
	/// Groth16. Lets us cap-tune real DB builds cheaply.
	pub b_dryrun_after_capcheck: bool,
	/// AGGRESSIVE-ONLY (b_aggressive_sde_for_rep). Sizes the per-chunk
	/// failed_subsigs accumulator: size = capacity.universe_subsigs *
	/// this / 10000 (basis points, floored to >=1). Unused when
	/// aggressive mode is off (the accumulator code path is gated).
	pub basis_failed_subsigs: usize,
	/// AGGRESSIVE-ONLY (b_aggressive_sde_for_rep). M5 NEEDS/QUICK filter:
	/// max|NEEDS|/chunk = the forward step-queue capacity (capacity.subsigs)
	/// after pre-filtering anchor-absent subsigs into QUICK. 0 = no shrink
	/// (forward runs over the full universe = pre-M5 behavior). Set by the
	/// runner from the estimator's reported needs_subsigs.
	pub aggr_needs_subsigs: usize,
	/// NEO-AGGRESSIVE (8_C): T_qm wrap-key budget = Sigma(steps+1) over
	/// the seeded NEEDS set. 0 = derive from the discharge capacity
	/// (subsigs*(avg_active+1)). Set by the runner per dataset.
	pub neo_wrap_keys: usize,
	/// Estimator-only: when true, the discharge pass also runs the chunked
	/// SED propagation to fill ChunkPeaks' forward-proof counts. Default
	/// false = normal discharge unaffected. Set by run_db_bundle.
	pub b_estimate_caps: bool,
	/// If true, foldpot_main produces only ONE full batch+individual
	/// proof: every job still runs Phase-1 folding, but only Job 0 runs
	/// the Groth16 deciders + Phase-2 + proof assembly/verify; other jobs
	/// return after folding. Default false = all jobs prove (unchanged).
	pub b_one_proof: bool,
	/// M0 flag-off regression fingerprint sink. None = disabled
	/// (default); Some collects (label,value) pairs for the test gate.
	pub fp_sink: Option<FpSink>,
	/// full_clam two-half NUMA scheme: which manifest slice each job
	/// reads, and the percent of each manifest used. Default Full/100 =
	/// whole list -> every other caller is unchanged.
	pub clam_read_mode: ClamReadMode,
	pub clam_read_pct: usize,
	/// full_clam part-2 gate: Some(path) = foldpot_main 10s-polls until
	/// that flag file exists before the decider. None = no wait (default).
	pub snark_wait_flag: Option<String>,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            log_level: crate::logger::LOG6,
            range2_bit: 18,
            res_small_cost: 20,
            min_basis_unique_states: 2,
            min_subsigs: 0,
            min_subsigs_igc: 0,
            min_cp_subsigs: 0,
            min_dfa_subsigs: 2,
            min_sigs: 2,
            min_dfa_sigs: 0,
            min_avg_pats_per_subsig: 2,
            min_avg_active_pats_per_subsig: 2,
            min_basis_pats_in_trace: 2,
            min_perc_pats_expansion_rate: 1,
            min_sigs_sed: 2,
            min_perc_comp_subsigs: 10,
            min_basis_acc_states: 2,
            b_light_test: true,
            b_folding_only: false,
            b_show_queue_saturated: false,
            b_scale_catch_caperr: false,
            b_read_cache: false,
            b_write_snark_cache: false,
            b_read_snark_cache: false,
            snark_cache_dir: String::new(),
            n_par_snark: 1,
            n_par_snark_cp: 1,
            n_par_batch_claim: 1,
            n_par_snark_total: 0, //0 = auto: sum of inner caps
            b_resume: false,
			perc_lkup_share: 1,
			b_pin_lkup_share: false,
			b_check_lkup: true,
			word_cap_per_job: 0,
			stall_watchdog_secs: 0,
			clamav_cfg: ClamavApproxConfig {
				max_pm_sections: 10,
				combination_limit: 127,
				repeat_limit: 256,
				min_bag_len: 6,
				min_pm_word_len: 4,
				b_aggressive_sde_for_rep: false,
				b_use_discharge_neo: false,
				sde_rep_fanout_cap: 127,
				variant_combine_cap: 4,
				b_sde_rep_tight_first_leg: false,
				sde_rep_fanout_boost: 10,
			},
			b_dryrun_after_capcheck: false,
			basis_failed_subsigs: 0,
			aggr_needs_subsigs: 0,
			neo_wrap_keys: 0,
			b_estimate_caps: false,
			b_one_proof: false,
			fp_sink: None,
			clam_read_mode: ClamReadMode::Full,
			clam_read_pct: 100,
			snark_wait_flag: None,
        }
    }
}

static GLOBAL_CONFIG: RwLock<GlobalConfig> = RwLock::new(GlobalConfig {
    log_level: crate::logger::LOG6,
    range2_bit: 18,
    res_small_cost: 20,
    min_basis_unique_states: 2,
    min_subsigs: 2,
    min_subsigs_igc: 0, // 0 = inherit min_subsigs (see min_subsigs_for)
    min_cp_subsigs: 0, // 0 = inherit min_subsigs (see min_cp_subsigs_val)
    min_dfa_subsigs: 0,
    min_sigs: 2,
    min_dfa_sigs: 0,
    min_avg_pats_per_subsig: 2,
    min_avg_active_pats_per_subsig: 2,
    min_basis_pats_in_trace: 2,
    min_perc_pats_expansion_rate: 1,
    min_sigs_sed: 2,
    min_perc_comp_subsigs: 10,
    min_basis_acc_states: 2,
    b_light_test: true,
    b_folding_only: false,
    b_show_queue_saturated: false,
    b_scale_catch_caperr: false,
    b_read_cache: false,
    b_write_snark_cache: false,
    b_read_snark_cache: false,
    snark_cache_dir: String::new(),
    n_par_snark: 1,
    n_par_snark_cp: 1,
    n_par_batch_claim: 1,
    n_par_snark_total: 0, //0 = auto: sum of inner caps
    b_resume: false,
	perc_lkup_share: 1,
	b_pin_lkup_share: false,
	b_check_lkup: true,
	word_cap_per_job: 0,
	stall_watchdog_secs: 0,
	clamav_cfg: ClamavApproxConfig {
		max_pm_sections: 10,
		combination_limit: 127,
		repeat_limit: 256,
		min_bag_len: 6,
		min_pm_word_len: 4,
		b_aggressive_sde_for_rep: false,
		b_use_discharge_neo: false,
		sde_rep_fanout_cap: 127,
		variant_combine_cap: 4,
		b_sde_rep_tight_first_leg: false,
		sde_rep_fanout_boost: 10,
	},
	b_dryrun_after_capcheck: false,
	basis_failed_subsigs: 0,
	aggr_needs_subsigs: 0,
	neo_wrap_keys: 0,
	b_estimate_caps: false,
	b_one_proof: false,
	fp_sink: None,
	clam_read_mode: ClamReadMode::Full,
	clam_read_pct: 100,
	snark_wait_flag: None,
});

pub fn read_global_config() -> RwLockReadGuard<'static, GlobalConfig> {
    GLOBAL_CONFIG.read().unwrap()
}

pub fn get_global_config() -> RwLockWriteGuard<'static, GlobalConfig> {
    GLOBAL_CONFIG.write().unwrap()
}

/// Per-arm subsigs ladder floor. The igc arm inherits min_subsigs while
/// min_subsigs_igc is 0, so cells that set only min_subsigs are unchanged.
pub fn min_subsigs_for(b_igc: bool) -> usize {
    let c = read_global_config();
    if b_igc && c.min_subsigs_igc > 0 { c.min_subsigs_igc }
    else { c.min_subsigs }
}

/// CP subsigs ladder floor, inheriting min_subsigs while min_cp_subsigs is
/// 0 so cells that set only min_subsigs keep their exact previous ladder.
pub fn min_cp_subsigs_val() -> usize {
    let c = read_global_config();
    if c.min_cp_subsigs > 0 { c.min_cp_subsigs } else { c.min_subsigs }
}

/// Push one (label,value) pair to the fingerprint sink when enabled.
/// No-op (one read-lock + Option check) when fp_sink is None, so it is
/// safe to call from synthesis paths in production.
pub fn fp_emit(label: &str, val: u64) {
    let sink = read_global_config().fp_sink.clone();
    if let Some(sink) = sink {
        sink.lock().unwrap().push((label.to_string(), val));
    }
}

/// Bit-split for the packed (sig_id, subsig_id) identifier produced
/// by HexACDFA::gen_subsig_id_worker, taken from the current
/// GlobalConfig. Default layout gives sig_id 2/3 of the budget
/// (capped at 16); under aggressive SDE-rep mode the layout is
/// equal (each half is range2_bit/2).
pub fn current_bit_parts() -> (usize, usize) {
    let g = read_global_config();
    let bits = g.range2_bit;
    if g.clamav_cfg.b_aggressive_sde_for_rep {
        // Reserve 10 bits (1024) for subsig_id -- M5 fan-out emits at
        // most ~1000 variants/sig -- and give the rest to sig_id (15
        // bits at range2_bit=25 -> 32768 sigs, vs only 1024 under the
        // old equal split). range2_bit=20 still yields (10,10).
        let p2 = 10;
        (bits - p2, p2)
    } else {
        let p1 = if bits > 19 { 16 } else { bits * 2 / 3 };
        (p1, bits - p1)
    }
}

pub const DEFAULT_ACDFA_DA_BITS:usize = 2;
pub const DEFAULT_ACDFA_STATE_PART_BITS:usize=24;

/// limit of exact concat of disjuncted terms, e.g.,
/// given (a|b|c)(d|e|f) if the limit is 10, we will get
/// (ad|ae|af|bd...|cf), but if the limit is 8, we will retain
/// the original sequence
pub const COMBINATION_LIMIT:usize = 127; 
/// sometimes numbered repetions creates too long string
/// for fixed number reps, e.g., [^"]{1000, 2000}, the char
/// class has 255 chars, and the long string is repeated for many times
/// in this case, when length exceeding the limit, approximate the
/// substr with .
pub const REPEAT_LEN_LIMIT:usize = 1024*6; 
pub const RANGE_MAX: usize = 1<<31;
/// maximum number of PM sections
pub const MAX_PM_SECTIONS: usize = 32;
/// MIN len required for being a bag word
//pub const MIN_BAG_WORD_LEN:usize = 4;
pub const MIN_BAG_WORD_LEN:usize = 6;
pub const MIN_PM_WORD_LEN:usize = 4;

