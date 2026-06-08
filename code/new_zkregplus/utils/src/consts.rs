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

use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::sync::atomic::AtomicUsize;
use serde::{Serialize, Deserialize};

/// Probe-only: chunk index of the current chunk-loop iteration. Set
/// by foldpot driver before each gen_nd_advice call so SED probes
/// can correlate StepQueue dumps with chunk_id.
pub static PROBE_CHUNK_ID: AtomicUsize = AtomicUsize::new(0);

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
}

pub struct GlobalConfig {
    pub log_level: usize,
    pub range2_bit: usize,
    pub min_basis_unique_states: usize,
    pub min_subsigs: usize,
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
    pub b_read_cache: bool,
    pub b_write_snark_cache: bool, //write the generated snark key to cache
    pub b_read_snark_cache: bool,
    pub snark_cache_dir: String,
    pub n_par_snark: usize,
    pub n_par_snark_cp: usize,
    pub n_par_batch_claim: usize,
    pub b_resume: bool,
	pub perc_lkup_share: usize, //percentae of the lkup share
					//compared with nibble length of a segment
					//e.g., for 700MB linux data (8 jobs) with 256M lkup table
					//each job (in total) has 90MB data = 180M nibbes
					// the perc_lkup_share = 256/180 * 100 = 143 percent
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
	/// failed_subsigs accumulator: size = capacity.subsigs * this / 10000
	/// (basis points, floored to >=1). Unused when aggressive mode is off
	/// (the accumulator code path is gated).
	pub perc_failed_subsigs: usize,
	/// AGGRESSIVE-ONLY (b_aggressive_sde_for_rep). M5 NEEDS/QUICK filter:
	/// max|NEEDS|/chunk = the forward step-queue capacity (capacity.subsigs)
	/// after pre-filtering anchor-absent subsigs into QUICK. 0 = no shrink
	/// (forward runs over the full universe = pre-M5 behavior). Set by the
	/// runner from the estimator's reported needs_subsigs.
	pub aggr_needs_subsigs: usize,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            log_level: crate::logger::LOG6,
            range2_bit: 18,
            min_basis_unique_states: 2,
            min_subsigs: 0,
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
            b_read_cache: false,
            b_write_snark_cache: false,
            b_read_snark_cache: false,
            snark_cache_dir: String::new(),
            n_par_snark: 1,
            n_par_snark_cp: 1,
            n_par_batch_claim: 1,
            b_resume: false,
			perc_lkup_share: 1,
			word_cap_per_job: 0,
			stall_watchdog_secs: 0,
			clamav_cfg: ClamavApproxConfig {
				max_pm_sections: 10,
				combination_limit: 127,
				repeat_limit: 256,
				min_bag_len: 6,
				min_pm_word_len: 4,
				b_aggressive_sde_for_rep: false,
				sde_rep_fanout_cap: 127,
				variant_combine_cap: 4,
				b_sde_rep_tight_first_leg: false,
			},
			b_dryrun_after_capcheck: false,
			perc_failed_subsigs: 0,
			aggr_needs_subsigs: 0,
        }
    }
}

static GLOBAL_CONFIG: RwLock<GlobalConfig> = RwLock::new(GlobalConfig {
    log_level: crate::logger::LOG6,
    range2_bit: 18,
    min_basis_unique_states: 2,
    min_subsigs: 2,
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
    b_read_cache: false,
    b_write_snark_cache: false,
    b_read_snark_cache: false,
    snark_cache_dir: String::new(),
    n_par_snark: 1,
    n_par_snark_cp: 1,
    n_par_batch_claim: 1,
    b_resume: false,
	perc_lkup_share: 1,
	word_cap_per_job: 0,
	stall_watchdog_secs: 0,
	clamav_cfg: ClamavApproxConfig {
		max_pm_sections: 10,
		combination_limit: 127,
		repeat_limit: 256,
		min_bag_len: 6,
		min_pm_word_len: 4,
		b_aggressive_sde_for_rep: false,
		sde_rep_fanout_cap: 127,
		variant_combine_cap: 4,
		b_sde_rep_tight_first_leg: false,
	},
	b_dryrun_after_capcheck: false,
	perc_failed_subsigs: 0,
	aggr_needs_subsigs: 0,
});

pub fn read_global_config() -> RwLockReadGuard<'static, GlobalConfig> {
    GLOBAL_CONFIG.read().unwrap()
}

pub fn get_global_config() -> RwLockWriteGuard<'static, GlobalConfig> {
    GLOBAL_CONFIG.write().unwrap()
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
        let p1 = bits / 2;
        (p1, bits - p1)
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
