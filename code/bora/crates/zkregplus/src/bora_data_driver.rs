//! bora_data_driver: paper-data support functions, sibling to
//! zkp_driver. Hosts perc-parameterized dataset thinning and the
//! perc-driven Q2 lookup-composition report.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use ark_bn254::{constraints::{GVar, PairingVar}, Bn254, Fr,
	G1Projective, G2Projective};
use ark_groth16::Groth16;
use ark_grumpkin::{constraints::GVar as GVar2,
	Projective as Projective2};
use data_processor::clam_db::ClamavDB;
use data_processor::clamav::{default_clamav_cfg,
	quick_discharge_file_by_crit_bag_pm};
use data_processor::discharge_proof::FailDischargeRecord;
use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};
use folding_schemes::folding::foldpot::capacity_planner
	::CapacityPlanner;
use folding_schemes::folding::foldpot::sigma_ir1cs::{
	LookupTableTwoCol_Inst, SigmaIR1CS_Inst, WordInfo};
use folding_schemes::transcript::poseidon
	::poseidon_canonical_config;
use utils::consts::{get_global_config, read_global_config,
	ClamavApproxConfig};

use crate::circs::composable_gadget_mapper::CompositeGadgetMapper;
use crate::determine_config::{apply_caperr_bumps,
	caps_from_params_aggr, caps_from_params_general, probe_catching,
	save_ladder, CapParams};
use crate::gadgets::word_extract::LEGS;
use crate::stats_helper::{estimate_config_aggr,
	estimated_to_capparams_aggr};
use crate::zkp_driver::{build_circs_adv, build_circs_adv_aggr,
	cover_word_n, determine_config_aggr, determine_config_non_aggr,
	fmt_cross_rollup, fmt_dfa_cross, select_binding_candidates,
	zkp_driver_adv, zkp_driver_adv_aggr, DcMode};

// Driver instantiation, matching zkp_driver.rs:2396-2406 (those
// aliases live in its cfg(test) module, unreachable from here).
type C1 = G1Projective;
type CS1 = Pedersen<C1>;
type C2G2 = G2Projective;
type C2 = Projective2;
type GC1 = GVar;
type GC2 = GVar2;
type CS1E = KZG<'static, Bn254>;
type CS2 = Pedersen<C2>;
type S = Groth16<Bn254>;

/// RAII guard: removes its temp config dir on drop, even on panic.
struct TmpConfigDir(PathBuf);

impl Drop for TmpConfigDir {
	fn drop(&mut self) {
		let _ = fs::remove_dir_all(&self.0);
	}
}

fn read_lines_nonblank(path: &str) -> Vec<String> {
	fs::read_to_string(path)
		.unwrap_or_else(|e| panic!("bora_data_driver: read {}: {}", path, e))
		.lines()
		.filter(|s| !s.starts_with('#') && !s.trim().is_empty())
		.map(|s| s.to_string())
		.collect()
}

/// Seed of the fixed rule/corpus permutation. MUST match zkp_driver's
/// SCALE_PERM_SEED (:7294, :7530) so neo picks legacy's subsets.
const SCALE_PERM_SEED: u64 = 0x5CA1_5EED_0F0F_0F0F;

/// Fixed pseudo-random permutation of 0..n (splitmix64 Fisher-Yates).
/// Transcribed from zkp_driver.rs:7295; the no-touch rule leaves that
/// copy and its twin at :7531 in place, so this one is pinned by test.
fn fixed_perm(n: usize, mut s: u64) -> Vec<usize> {
	let mut v: Vec<usize> = (0..n).collect();
	for i in (1..n).rev() {                  // Fisher-Yates, high->low
		s = s.wrapping_add(0x9E3779B97F4A7C15);
		let mut z = s;
		z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
		z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
		z ^= z >> 31;
		v.swap(i, (z % (i as u64 + 1)) as usize);
	}
	v
}

/// The ONE subsetting policy, for sigs and corpus alike: index 0 pinned,
/// the rest drawn from a fixed permutation, sorted so source order is
/// kept and counts nest. `count` INCLUDES the pin.
fn subset(n: usize, count: usize) -> Vec<usize> {
	if n == 0 {
		return vec![];
	}
	let keep = count.clamp(1, n);
	if keep >= n {
		return (0..n).collect();
	}
	// Permute 1..n exactly as legacy does: shuffle n-1 elements and
	// shift by one. Shuffling n would silently pick a different subset.
	let mut idx: Vec<usize> = vec![0];
	idx.extend(fixed_perm(n - 1, SCALE_PERM_SEED).into_iter()
		.take(keep - 1).map(|i| i + 1));
	idx.sort();
	idx
}

/// subset() mapped over items.
fn subset_items<T: Clone>(items: &[T], count: usize) -> Vec<T> {
	subset(items.len(), count).into_iter()
		.map(|i| items[i].clone()).collect()
}

/// Percentage -> count, the ONE conversion: everything downstream is in
/// counts. perc 0 still yields 1 -- there is no empty run; C103's
/// parse_args rejects 0 at the CLI so this floor is never load-bearing.
fn count_of(n: usize, perc: f64) -> usize {
	assert!(n > 0, "bora_data_driver: count_of on an empty set");
	// f64 is exact here: n*perc <= ~5e7, far below 2^53
	((n as f64 * perc / 100.0).ceil() as usize).clamp(1, n)
}

/// Reads src_path (skip #-comments, matching build_db's own needs-list
/// convention), keeps only names in keep_names, writes the result to
/// dst_path.
fn filter_needs_list(src_path: &str, keep_names: &HashSet<&str>,
	dst_path: &str) {
	let kept: Vec<String> = fs::read_to_string(src_path)
		.unwrap_or_else(|e|
			panic!("bora_data_driver: read {}: {}", src_path, e))
		.lines()
		.filter(|s| !s.starts_with('#'))
		.map(|s| s.trim().to_string())
		.filter(|s| keep_names.contains(s.as_str()))
		.collect();
	fs::write(dst_path, kept.join("\n")).unwrap_or_else(|e|
		panic!("bora_data_driver: write {}: {}", dst_path, e));
}

/// True when every plain-numeric offset prefix ("NNN:...", BYTE
/// units) among the line's subsig fields fits a range table of
/// max_off_nibbles nibbles (bound compared against 2x the prefix).
/// Prefix-less lines (e.g. the alphabet pin) and non-numeric
/// prefixes always fit. usize::MAX = the unbounded sentinel: keep
/// EVERY line (a >usize digit token must not drop a sig there).
fn sig_fits_range(line: &str, max_off_nibbles: usize) -> bool {
	if max_off_nibbles == usize::MAX {
		return true;
	}
	line.split(';').skip(3).all(|f| match f.split_once(':') {
		Some((tok, _)) if !tok.is_empty()
			&& tok.bytes().all(|b| b.is_ascii_digit()) =>
			tok.parse::<usize>().ok()
				.and_then(|off| off.checked_mul(2))
				.map(|n| n < max_off_nibbles)
				.unwrap_or(false),
		_ => true,
	})
}

/// The canonical alphabet-covering rule, byte-identical to line 0 of
/// DLP's and DNA's sig files: two patterns whose union hits all 16 hex
/// digits, which HexACDFA requires (alpha_size == 17).
const ALPHABET_SIG: &str = concat!(
	"Win.Alphabet.SAMPLE-1;Engine:51-255,Target:1;0|1;",
	"09afcdeb1928374650123457890abcde;0123498765423afedc");

/// Deterministically thins src_dir's config down to `count` signatures,
/// writing a self-contained smaller config under dst_dir.
/// src_dir must contain sig_file_name, main_dfa.dat, needs_ised.dat,
/// needs_ised_igc.dat -- panics if any is missing. main_fanout.dat is
/// copied verbatim if present (optional, substring-matched so it can't
/// be meaningfully re-filtered). Returns the thinned sig file's path.
pub fn create_smaller_config(src_dir: &str, sig_file_name: &str,
	count: usize, dst_dir: &str) -> String {
	create_smaller_config_bounded(src_dir, sig_file_name, count,
		dst_dir, usize::MAX)
}

/// create_smaller_config with a range-table bound (M103 dry): sig
/// lines whose offsets reach max_off_nibbles are dropped BEFORE
/// subsetting (sig_fits_range), since the table has no overflow
/// guard -- an out-of-range sig would produce un-lookupable rows.
/// usize::MAX keeps every line, byte-identical to the original.
pub fn create_smaller_config_bounded(src_dir: &str,
	sig_file_name: &str, count: usize, dst_dir: &str,
	max_off_nibbles: usize) -> String {
	fs::create_dir_all(dst_dir).unwrap_or_else(|e|
		panic!("bora_data_driver: mkdir {}: {}", dst_dir, e));

	let mut sig_lines: Vec<String> = read_lines_nonblank(
		&format!("{}/{}", src_dir, sig_file_name))
		.into_iter()
		.filter(|l| sig_fits_range(l, max_off_nibbles))
		.collect();
	assert!(!sig_lines.is_empty(),
		"bora_data_driver: no sig fits a {}-nibble range table",
		max_off_nibbles);
	// DLP/DNA already carry this as line 0; CLAM does not, so a thinned
	// CLAM DB can miss hex digits and fail HexACDFA's alpha_size==17.
	// Prepending makes line 0 the alphabet rule everywhere, so subset()'s
	// index-0 pin covers it by construction. Two guards keep it inert:
	// an exact-name check (datasets that already have it) and count <
	// len (keeping the whole DB keeps the DB's own alphabet).
	let alpha = ALPHABET_SIG.split(';').next().unwrap();
	if count < sig_lines.len()
		&& !sig_lines.iter().any(|l| l.split(';').next() == Some(alpha)) {
		sig_lines.insert(0, ALPHABET_SIG.to_string());
	}
	let keep_idx = subset(sig_lines.len(), count);
	let kept_lines: Vec<&String> = keep_idx.iter()
		.map(|&i| &sig_lines[i]).collect();
	let keep_names: HashSet<&str> = kept_lines.iter()
		.map(|s| s.split(';').next().unwrap_or(""))
		.collect();

	let dst_sig = format!("{}/{}", dst_dir, sig_file_name);
	let body: Vec<&str> = kept_lines.iter().map(|s| s.as_str()).collect();
	fs::write(&dst_sig, body.join("\n")).unwrap_or_else(|e|
		panic!("bora_data_driver: write {}: {}", dst_sig, e));

	filter_needs_list(&format!("{}/main_dfa.dat", src_dir), &keep_names,
		&format!("{}/main_dfa.dat", dst_dir));
	filter_needs_list(&format!("{}/needs_ised.dat", src_dir), &keep_names,
		&format!("{}/needs_ised.dat", dst_dir));
	filter_needs_list(&format!("{}/needs_ised_igc.dat", src_dir),
		&keep_names, &format!("{}/needs_ised_igc.dat", dst_dir));

	let fanout_src = format!("{}/main_fanout.dat", src_dir);
	if Path::new(&fanout_src).exists() {
		fs::copy(&fanout_src, format!("{}/main_fanout.dat", dst_dir))
			.unwrap_or_else(|e|
				panic!("bora_data_driver: copy main_fanout.dat: {}", e));
	}
	dst_sig
}

/// Plan dir for one part's private sandbox: thinned config, job
/// manifests, ladder.json. The part wipes it at every run start.
pub(crate) fn plan_dir(name: &str, part_id: usize) -> String {
	format!("/tmp/bora/{}_neo_p{}", name, part_id)
}

/// Wipes and recreates one part's plan dir (plus its jobs/ subdir).
/// The strict-subdir assert keeps any future edit from pointing the
/// wipe at the shared /tmp/bora framework dir.
fn reset_part_dir(spec: &DatasetSpec, part_id: usize) -> String {
	let pd = plan_dir(spec.name, part_id);
	assert!(pd.starts_with("/tmp/bora/")
		&& pd.len() > "/tmp/bora/".len(),
		"bora_data_driver: refusing to wipe {}", pd);
	if Path::new(&pd).exists() {
		fs::remove_dir_all(&pd).unwrap_or_else(|e| panic!(
			"bora_data_driver: wipe {}: {}", pd, e));
	}
	fs::create_dir_all(format!("{}/jobs", pd)).unwrap_or_else(
		|e| panic!("bora_data_driver: mkdir {}/jobs: {}", pd, e));
	pd
}

/// Reads a newline path list; transparently extracts a .tgz/.tar.gz via
/// `tar -xzO` (no temp file left behind). list_path is repo-relative.
/// Port of zkp_driver's helper, which is cfg(test)-only.
pub(crate) fn read_path_list(list_path: &str) -> Vec<String> {
	let proot = utils::os::proj_root();
	let abs = format!("{}/{}", proot, list_path);
	let raw: Vec<String> =
		if list_path.ends_with(".tgz") || list_path.ends_with(".tar.gz") {
			let out = std::process::Command::new("tar")
				.args(["-xzO", "-f", &abs]).output()
				.expect("tar -xzO path list");
			String::from_utf8_lossy(&out.stdout).lines()
				.map(|l| l.trim().to_string()).collect()
		} else {
			utils::os::read_lines(&abs)
		};
	// Drop blanks and dotfile entries (e.g. a swept-in .gitignore) so
	// discharge never panics opening a non-email path.
	raw.into_iter()
		.filter(|l| !l.is_empty())
		.filter(|l| l.rsplit('/').next()
			.map_or(false, |n| !n.starts_with('.')))
		.collect()
}

/// Deterministic size-balanced split of a path list into num_jobs lists.
/// Sort by (-size, path) then greedy-LPT into the smallest bin, so the
/// same (list, num_jobs) yields identical bins each run.
pub(crate) fn split_paths_balanced(paths: Vec<String>, num_jobs: usize)
	-> Vec<Vec<String>> {
	use rayon::prelude::*;
	let proot = utils::os::proj_root();
	let mut sized: Vec<(u64, String)> = paths.par_iter().map(|p| {
		let sz = std::fs::metadata(format!("{}/{}", proot, p))
			.map(|m| m.len()).unwrap_or(0);
		(sz, p.clone())
	}).collect();
	sized.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
	let n = num_jobs.max(1);
	let (mut bins, mut tot) = (vec![vec![]; n], vec![0u64; n]);
	for (sz, p) in sized {
		let j = (0..n).min_by_key(|&i| (tot[i], i)).unwrap();
		bins[j].push(p);
		tot[j] += sz;
	}
	bins
}

/// Writes bin i to <jobs_dir>/job_<i>.dat (newline-joined), returning the
/// paths in job order. Stale job_<n>.dat from an earlier plan are removed
/// first. The index IS the global job id, parsed back by load_files.
pub(crate) fn write_job_manifests(jobs_dir: &str, bins: &[Vec<String>])
	-> Vec<String> {
	// must be absolute: load_files passes absolute paths through but
	// resolves relative ones against proj_root, and the plan dir is /tmp.
	assert!(Path::new(jobs_dir).is_absolute(),
		"bora_data_driver: jobs_dir must be absolute: {}", jobs_dir);
	fs::create_dir_all(jobs_dir).unwrap_or_else(|e|
		panic!("bora_data_driver: mkdir {}: {}", jobs_dir, e));
	// Drop only job_<n>.dat, never the whole dir: jobs_dir is caller
	// supplied and a remove_dir_all on a mistaken path is unrecoverable.
	// The name test mirrors zkp_driver's dlp_job_idx parse exactly, so
	// what we delete is precisely what the driver reads back as a job.
	for ent in fs::read_dir(jobs_dir).unwrap_or_else(|e|
		panic!("bora_data_driver: read_dir {}: {}", jobs_dir, e)) {
		let p = ent.expect("bora_data_driver: dir entry").path();
		let stale = p.file_name().and_then(|s| s.to_str())
			.and_then(|s| s.strip_prefix("job_"))
			.and_then(|s| s.strip_suffix(".dat"))
			.map_or(false, |s| s.parse::<usize>().is_ok());
		if stale {
			fs::remove_file(&p).unwrap_or_else(|e|
				panic!("bora_data_driver: rm {:?}: {}", p, e));
		}
	}
	bins.iter().enumerate().map(|(i, b)| {
		let p = format!("{}/job_{}.dat", jobs_dir, i);
		fs::write(&p, b.join("\n")).unwrap_or_else(|e|
			panic!("bora_data_driver: write {}: {}", p, e));
		p
	}).collect()
}

/// Scale-sweep tuning profile: the LOW floors + LOW seed a dataset's
/// scale rounds use instead of its full-run values (a high floor
/// pins every subset to full size, zkp_driver.rs:7477-7530).
#[derive(Clone)]
pub(crate) struct ScaleTune {
	pub(crate) min_subsigs: usize,
	pub(crate) min_basis_unique_states: usize,
	pub(crate) min_basis_acc_states: usize,
	pub(crate) min_basis_pats_in_trace: usize,
	pub(crate) min_avg_pats_per_subsig: usize,
	pub(crate) min_dfa_sigs: usize,
	pub(crate) min_dfa_subsigs: usize,
	pub(crate) hand_seed: CapParams,
}

/// One dataset's complete, immutable run configuration. Only the
/// DLP/DNA/CLAM consts exist; tests clone them to redirect dirs.
#[derive(Clone)]
#[allow(dead_code)] // fields read from B101/B102/C101 on
pub struct DatasetSpec {
	/// Dataset tag; plan dir is /tmp/bora/<name>_neo.
	pub(crate) name: &'static str,
	/// Dir holding sig_file + main_dfa/needs_ised/needs_ised_igc .dat.
	pub(crate) config_dir: &'static str,
	/// Signature file basename inside config_dir.
	pub(crate) sig_file: &'static str,
	/// Repo-rel path lists (.tgz ok); their concat is the scan corpus.
	pub(crate) master_sources: &'static [&'static str],
	/// Scale corpora, each swept ALONE (never concatenated).
	pub(crate) scale_sources: &'static [&'static str],
	/// DB cache dir, neo-own so it never collides with legacy's.
	pub(crate) db_cache_dir: &'static str,
	/// Nibbles per folding chunk (the driver's max_word).
	pub(crate) chunk_len: usize,
	/// Dry/light-only replacement for chunk_len (effective_spec);
	/// None = never diverge. The step circuit is per-chunk-nibble-
	/// driven (~55 cs/nibble), so this is the decider-size lever.
	pub(crate) dry_chunk_len: Option<usize>,
	/// Bit width of the range-2 lookup table.
	pub(crate) range2_bit: usize,
	/// Dry/light-only replacement for range2_bit (effective_spec);
	/// None = never diverge. Shrinks the dominant range table so a
	/// dry run fits a small box; out-of-range sigs are filtered at
	/// thinning time (the table has no overflow guard).
	pub(crate) dry_range2_bit: Option<usize>,
	/// Byte-prefix % of the scale corpus a DRY sweep folds. 100.0 =
	/// fold whole (shrink_lone_sample no-ops at >=100), for datasets
	/// whose scale sources are already tiny. Full sweeps always fold
	/// the whole file regardless.
	pub(crate) dry_scale_perc: f64,
	/// SDE repetition fan-out cap (clamav_cfg.sde_rep_fanout_cap).
	pub(crate) fanout_cap: usize,
	/// PM extraction min word length (clamav_cfg.min_pm_word_len).
	/// DB-SHAPE-AFFECTING: DLP legacy sets 3; DNA/CLAM run default 4.
	pub(crate) min_pm_word_len: usize,
	/// Aggressive SDE arm (DLP true; DNA/CLAM false).
	pub(crate) b_aggressive: bool,
	/// Run the in-circuit lookup-share cover check.
	pub(crate) b_check_lkup: bool,
	/// Non-aggr ladder steps; len MUST be num_circs-1. Empty when aggr.
	pub(crate) vec_decrease_level: &'static [usize],
	/// Main-decider concurrency cap (inert while b_one_proof).
	pub(crate) n_par_snark: usize,
	/// CP-decider concurrency cap (inert while b_one_proof).
	pub(crate) n_par_snark_cp: usize,
	/// pass_all batch-claim semaphore width; every job reaches it, so
	/// it is NOT inert (B101). DLP 1 (legacy default), DNA 8.
	pub(crate) n_par_batch_claim: usize,
	/// Floor on subsigs per circuit.
	pub(crate) min_subsigs: usize,
	/// Floor on distinct FSM basis states.
	pub(crate) min_basis_unique_states: usize,
	/// Floor on accepting basis states.
	pub(crate) min_basis_acc_states: usize,
	/// Floor on patterns held in one trace.
	pub(crate) min_basis_pats_in_trace: usize,
	/// Floor on average patterns per subsig.
	pub(crate) min_avg_pats_per_subsig: usize,
	/// Floor on DFA sigs (0 = no floor).
	pub(crate) min_dfa_sigs: usize,
	/// Floor on DFA subsigs (0 = no floor).
	pub(crate) min_dfa_subsigs: usize,
	/// Non-aggr tuner seed (the dataset's legacy hand caps).
	/// None when aggressive.
	pub(crate) hand_seed: Option<CapParams>,
	/// Fold-run log verbosity: full runs LOG3 (6108x probes off),
	/// scale sweeps LOG4 (full probe trace, discharge_adv_neo).
	pub(crate) log_level: usize,
	/// Scale-round floors + seed override (legacy scale's low
	/// "Option A" profile). None = scale keeps the full-run values.
	pub(crate) scale_tune: Option<ScaleTune>,
}

/// DLP: legacy full_dlp()'s exact run configuration (zkp_driver's
/// full_dlp + data/paper_data/dlp/cfg/config/runcfg_full.json), with a
/// neo-own DB cache dir.
pub const DLP: DatasetSpec = DatasetSpec {
	name: "dlp",
	// legacy splits this into cfg/ + a "regex_pat/"-prefixed sig_file;
	// flattened so all four .dat files share one root, as
	// create_smaller_config requires.
	config_dir: "data/paper_data/dlp/cfg/regex_pat",
	sig_file: "main_data_dlp_internationl.dat",
	master_sources:
		&["data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz"],
	scale_sources: &[
		// 1,996 B, ~0% SDE saturation (easy; legacy ran it first)
		"data/samples/email/src/maildir/griffith-j/continental/2.",
		// 805 B, ~91% SDE saturation (dense)
		"data/samples/email/src/maildir/donohoe-t/sent/6."],
	db_cache_dir: "dlp_neo", // never legacy's "dlp_corpus_aggr"
	chunk_len: 64,
	// already the smallest of the three (Enron's median mail is ~50
	// words) -- nothing for a dry shape to cut.
	dry_chunk_len: None,
	range2_bit: 25,
	// 22 like DNA/CLAM: the range table is 2^r2b entries and dominates
	// the dry floor (12 GB of 22.3 GB measured 2026-08-11). Safe by a
	// wide margin -- DLP's ACDFAs run 24-150 states vs 2^22 = 4.19M.
	dry_range2_bit: Some(22),
	// whole file: the two scale sources are 1,996 B and 805 B mails,
	// so a 5% prefix would leave 100 B / 41 B and gut the sweep.
	dry_scale_perc: 100.0,
	fanout_cap: 100,
	// legacy full_dlp sets 3 (zkp_driver.rs:6790).
	min_pm_word_len: 3,
	b_aggressive: true,
	// true is a DELIBERATE departure from legacy full_dlp(), which
	// folded without the hab22 cover check. Neo runs must check.
	b_check_lkup: true,
	vec_decrease_level: &[],
	// 1/1 = legacy full_dlp, which never sets these. Inert regardless:
	// the snark semaphores are taken past driver.rs' b_one_proof and
	// b_folding_only returns, so only one job ever contends.
	n_par_snark: 1,
	n_par_snark_cp: 1,
	// legacy full_dlp never sets it -> the default 1 stands (B101).
	n_par_batch_claim: 1,
	min_subsigs: 1,
	min_basis_unique_states: 2,
	min_basis_acc_states: 2,
	min_basis_pats_in_trace: 4,
	min_avg_pats_per_subsig: 1,
	// 0/0 = legacy full_dlp (never set -> GLOBAL_CONFIG default), and
	// inert for DLP: its main_dfa.dat / needs_ised*.dat are empty.
	min_dfa_sigs: 0,
	min_dfa_subsigs: 0,
	hand_seed: None,
	log_level: utils::logger::LOG3,
	scale_tune: None,
};

/// DNA: legacy full_dna()'s exact run configuration (zkp_driver.rs
/// :5279-5387), with a neo-own DB cache dir. Single job always (the
/// chr17 sample is offset-anchored and cannot split); the cover
/// check stays OFF like legacy (user decision 2026-08-10: corpus too
/// small to pay the check cost), so the share pins to 1 either way.
pub const DNA: DatasetSpec = DatasetSpec {
	name: "dna",
	config_dir: "data/paper_data/dna/config",
	sig_file: "main.dat",
	// one line: data/samples/chr17_samples/NC_000017.11.reef.bin
	master_sources: &["data/paper_data/dna/config/binexec.dat"],
	scale_sources: &[],          // paper excludes DNA from Q4 scale
	db_cache_dir: "dna_neo",     // never legacy's "dna_data"
	chunk_len: 4096,             // 512*8 -> ~328 steps at 41.6MB
	// dry decider lever (user decision 2026-08-10): the step circuit
	// is ~55 cs per chunk-NIBBLE (4096*62 nibbles -> 34.6M-entry
	// all_w_e, decider OOMs 125GB even light + small table). 256
	// -> ~0.9M-cs steps, ~105 steps on the 2% sample. Full = 4096.
	dry_chunk_len: Some(256),
	range2_bit: 27,              // 80.09M-nibble max offset
	// dry MUST shrink the table (user decision 2026-08-10): at 27
	// the 134.2M-row range table alone puts cs1e at 34.6M and the
	// light decider OOMs a 125GB box. 2^22 keeps an ~830-sig
	// in-range pool (>= the 276-sig dry DB); full runs stay at 27.
	dry_range2_bit: Some(22),
	// inert: scale_sources is empty, DNA has no scale sweep.
	dry_scale_perc: 100.0,
	// legacy full_dna touches NO clamav_cfg field: both are the
	// GLOBAL_CONFIG defaults (consts.rs:493/:490), NOT dlp's 100/3.
	fanout_cap: 127,
	min_pm_word_len: 4,
	b_aggressive: false,
	b_check_lkup: false,
	vec_decrease_level: &[],     // single full-cap circuit
	n_par_snark: 2,
	n_par_snark_cp: 2,
	n_par_batch_claim: 8,        // legacy sets 8; inert at 1 job
	// floors set LOW vs clamav (zkp_driver.rs:5288-5294).
	min_subsigs: 64,
	min_basis_unique_states: 100,
	min_basis_acc_states: 2,
	min_basis_pats_in_trace: 4,
	min_avg_pats_per_subsig: 1,
	min_dfa_sigs: 2,
	min_dfa_subsigs: 2,
	// the hand caps of zkp_driver.rs:5309-5361, mapped through
	// caps_from_params_general's field order (igc mirrors cs; only
	// perc_pats_expansion_rate_igc differs, 4 -- igc trace is empty).
	hand_seed: Some(CapParams {
		cp_basis_unique_states: 6500,
		cp_subsigs: 20,
		cp_avg_pats: 1,
		subsigs: 20,
		avg_pats_per_subsig: 1,
		avg_active_pats_per_subsig: 1,
		basis_pats_in_trace: 4,
		perc_pats_expansion_rate: 200,
		prod_pats_expansion: 0,  // non-aggr: gadget reads basis*perc
		qm_real_rows: 0,         // hand-cap era; tune warm-starts to 2
		sigs_sed: 20,
		perc_comp_subsigs: 20,
		basis_unique_states: 6500,
		basis_acc_states: 2,
		subsigs_igc: 20,
		avg_active_pats_per_subsig_igc: 1,
		basis_pats_in_trace_igc: 4,
		perc_pats_expansion_rate_igc: 4,
		prod_pats_expansion_igc: 0,
		qm_real_rows_igc: 0,
		basis_acc_states_igc: 2,
		basis_unique_states_igc: 6500, // unused non-aggr (cs shared)
		dfa_sigs: 0,
		dfa_subsigs: 0,
		aggr_needs_subsigs: 0,
		max_word_len: 4096,
		acdfa_state_part_bits: 27,
		levels: Vec::new(),
	}),
	log_level: utils::logger::LOG3,
	scale_tune: None,
};

/// CLAM: legacy PRODUCTION full_clamav()'s exact run configuration
/// (zkp_driver.rs:4970-5133, the two-half full_clam entry -- NOT
/// the stale examples/main.rs variant), with a neo-own cache dir.
pub const CLAM: DatasetSpec = DatasetSpec {
	name: "clam",
	config_dir: "data/debug/full_clamav/config",
	sig_file: "main.dat",
	// the 8 legacy job manifests; their concat is the corpus. The
	// neo re-split changes per-job composition vs binexec_p0..p7
	// (8.8(a): aggregates comparable, per-job numbers are not).
	master_sources: &[
		"data/debug/full_clamav/config/binexec_p0.dat",
		"data/debug/full_clamav/config/binexec_p1.dat",
		"data/debug/full_clamav/config/binexec_p2.dat",
		"data/debug/full_clamav/config/binexec_p3.dat",
		"data/debug/full_clamav/config/binexec_p4.dat",
		"data/debug/full_clamav/config/binexec_p5.dat",
		"data/debug/full_clamav/config/binexec_p6.dat",
		"data/debug/full_clamav/config/binexec_p7.dat"],
	scale_sources: &[
		// 522,064 B, sparse (easy first, like DLP's order)
		"data/samples/binexec_merged128k/readelf",
		// 6,826,488 B, dense
		"data/samples/binexec_merged128k/gdb"],
	db_cache_dir: "clam_neo",    // never legacy's "full_data"
	chunk_len: 4096,             // 512*8 (zkp_driver.rs:5037)
	// dry decider lever (M103 cost law, ~55 cs/chunk-nibble): 128
	// -> ~436K-cs steps, ~214 steps on the 2-file dry corpus.
	dry_chunk_len: Some(128),
	range2_bit: 26,
	// dry shrinks the table too (user 2026-08-11): CLAM's 26 is NOT
	// offset-driven -- the in-range sig pool is identical (38,241)
	// at bits 22..26. The bound is the LARGEST dry corpus in NIBBLES:
	// the full leaf's 2-file subset (749,976 B = 1.5M) and, since
	// scale folds only a dry_scale_perc prefix, 5% of gdb (341,325 B
	// = 683K). 2^22 = 4.19M clears both by 2.8x; 16x fewer rows than
	// full. Sizing this against the WHOLE gdb (13.65M nibbles) is the
	// trap -- it panics mid-fold, clam_db has no overflow guard.
	dry_range2_bit: Some(22),
	// 5% of gdb (6.8 MB) -- the scale sources are whole binaries and
	// fold work is linear in corpus length, so no chunk_len cuts it.
	dry_scale_perc: 5.0,
	// legacy full_clamav touches NO clamav_cfg field: defaults.
	fanout_cap: 127,
	min_pm_word_len: 4,
	b_aggressive: false,
	// production runs the check (ZKR_CLAM_CHECK_LKUP=1); legacy's
	// hand share pin 143 is NOT copied (8.1(1)) -- tune derives it.
	b_check_lkup: true,
	vec_decrease_level: &[2],    // num_circs = 2, both modes
	n_par_snark: 1,
	n_par_snark_cp: 1,
	n_par_batch_claim: 8,
	// production floors (zkp_driver.rs:5002-5008) = the lkup-budget
	// reference's authoritative DB config.
	min_subsigs: 368,
	min_basis_unique_states: 1054,
	min_basis_acc_states: 268,
	min_basis_pats_in_trace: 295,
	min_avg_pats_per_subsig: 8,
	min_dfa_sigs: 3,
	min_dfa_subsigs: 3,
	// hand caps of zkp_driver.rs:5037-5093 (igc mirrors cs; only
	// perc_pats_expansion_rate_igc differs, 2).
	hand_seed: Some(CapParams {
		cp_basis_unique_states: 1300,
		cp_subsigs: 580,
		cp_avg_pats: 8,
		subsigs: 580,
		avg_pats_per_subsig: 8,
		avg_active_pats_per_subsig: 2,
		basis_pats_in_trace: 820,
		perc_pats_expansion_rate: 104,
		prod_pats_expansion: 0,
		qm_real_rows: 0,
		sigs_sed: 400,
		perc_comp_subsigs: 20,
		basis_unique_states: 1300,
		basis_acc_states: 750,
		subsigs_igc: 580,
		avg_active_pats_per_subsig_igc: 2,
		basis_pats_in_trace_igc: 820,
		perc_pats_expansion_rate_igc: 2,
		prod_pats_expansion_igc: 0,
		qm_real_rows_igc: 0,
		basis_acc_states_igc: 750,
		basis_unique_states_igc: 1300, // unused non-aggr (cs shared)
		dfa_sigs: 8,
		dfa_subsigs: 8,
		aggr_needs_subsigs: 0,
		max_word_len: 4096,
		acdfa_state_part_bits: 26,
		levels: Vec::new(),
	}),
	// legacy collect_scale_data's Option A (zkp_driver.rs:
	// 7480-7550): low floors + low seed per round.
	log_level: utils::logger::LOG3,
	scale_tune: Some(ScaleTune {
		min_subsigs: 64,
		min_basis_unique_states: 100,
		min_basis_acc_states: 2,
		min_basis_pats_in_trace: 4,
		min_avg_pats_per_subsig: 1,
		min_dfa_sigs: 2,
		min_dfa_subsigs: 2,
		hand_seed: CapParams {
			cp_basis_unique_states: 120, // 0-word CP pack floor
			cp_subsigs: 64,
			cp_avg_pats: 8,
			subsigs: 64,
			avg_pats_per_subsig: 8,
			avg_active_pats_per_subsig: 2,
			basis_pats_in_trace: 4,
			perc_pats_expansion_rate: 104,
			prod_pats_expansion: 0,
			qm_real_rows: 0,
			sigs_sed: 64,
			perc_comp_subsigs: 20,
			basis_unique_states: 120,
			basis_acc_states: 2,
			subsigs_igc: 64,
			avg_active_pats_per_subsig_igc: 2,
			basis_pats_in_trace_igc: 4,
			perc_pats_expansion_rate_igc: 104,
			prod_pats_expansion_igc: 0,
			qm_real_rows_igc: 0,
			basis_acc_states_igc: 2,
			basis_unique_states_igc: 120,
			dfa_sigs: 2,
			dfa_subsigs: 2,
			aggr_needs_subsigs: 0,
			max_word_len: 4096,
			acdfa_state_part_bits: 26,
			levels: Vec::new(),
		},
	}),
};

/// Config dir for a run: the real one when nothing is thinned, else the
/// thinned copy under the part's plan dir. Pure -- creates nothing.
fn config_dir_for(spec: &DatasetSpec, db_count: usize,
	n_sigs: usize, part_id: usize) -> String {
	if db_count >= n_sigs {
		spec.config_dir.to_string()
	} else {
		format!("{}/config", plan_dir(spec.name, part_id))
	}
}

/// Per-part DB cache dir: both parts build identical DBs, but the
/// cache writes must never race, so each part owns its own dir.
fn cache_dir_for(spec: &DatasetSpec, part_id: usize) -> String {
	format!("{}_p{}", spec.db_cache_dir, part_id)
}

/// One part's role in a numa_num-way split.
pub(crate) struct PartRole {
	/// This part runs the decider (the LAST part proves).
	pub(crate) b_proves: bool,
	/// Wait on the snark start flag (only when a sibling part folds).
	pub(crate) b_wait_snark: bool,
	/// Half-open range of GLOBAL job indices this part folds.
	pub(crate) jobs: Range<usize>,
}

/// Part topology in one place. The asserts live here so every caller
/// gets them and they stay unit-testable.
pub(crate) fn part_role(part_id: usize, numa_num: usize,
	num_jobs: usize) -> PartRole {
	assert!(numa_num >= 1, "bora_data_driver: numa_num must be >= 1");
	assert!(part_id < numa_num,
		"bora_data_driver: part_id {} >= numa_num {}", part_id, numa_num);
	assert!(num_jobs % numa_num == 0,
		"bora_data_driver: num_jobs {} not a multiple of numa_num {}",
		num_jobs, numa_num);
	let per = num_jobs / numa_num;
	let b_proves = part_id == numa_num - 1;
	PartRole {
		b_proves,
		b_wait_snark: b_proves && numa_num > 1,
		jobs: part_id * per..(part_id + 1) * per,
	}
}

/// Sample `master` down to perc_samples% and split into num_jobs
/// size-balanced bins. Inner half of plan_corpus, taking the already
/// read list so it can be tested without a DatasetSpec.
fn plan_corpus_from(master: &[String], perc_samples: f64,
	num_jobs: usize) -> Vec<Vec<String>> {
	use rayon::prelude::*;
	assert!(!master.is_empty(), "bora_data_driver: empty corpus list");
	let files = subset_items(master,
		count_of(master.len(), perc_samples));
	// Guard: split_paths_balanced treats an unreadable file as size 0,
	// so an unextracted corpus would silently split by path order.
	let proot = utils::os::proj_root();
	let total: u64 = files.par_iter().map(|p|
		fs::metadata(format!("{}/{}", proot, p))
			.map(|m| m.len()).unwrap_or(0)).sum();
	assert!(total > 0,
		"bora_data_driver: corpus has zero total size \
		 (run scripts/INSTALL.py?)");
	split_paths_balanced(files, num_jobs)
}

/// Corpus bins for one run: concat the spec's master lists, sample, and
/// split size-balanced into num_jobs bins.
pub(crate) fn plan_corpus(spec: &DatasetSpec, perc_samples: f64,
	num_jobs: usize) -> Vec<Vec<String>> {
	let master: Vec<String> = spec.master_sources.iter()
		.flat_map(|s| read_path_list(s)).collect();
	plan_corpus_from(&master, perc_samples, num_jobs)
}

/// Dry-run rule for a lone-file corpus (user decision 2026-08-10,
/// M103): a sampled corpus of exactly ONE file at perc_samples<100
/// folds a ceil(perc%) byte-prefix copy written into the part's
/// sandbox. Identity otherwise (DLP's corpora are many-file).
fn shrink_lone_sample(pd: &str, bins: Vec<Vec<String>>,
	perc_samples: f64) -> Vec<Vec<String>> {
	let n_files: usize = bins.iter().map(|b| b.len()).sum();
	if n_files != 1 || perc_samples >= 100.0 {
		return bins;
	}
	let rel = bins.iter().flatten().next().unwrap();
	let abs = if rel.starts_with('/') { rel.clone() }
		else { format!("{}/{}", utils::os::proj_root(), rel) };
	let data = fs::read(&abs).unwrap_or_else(|e| panic!(
		"bora_data_driver: read lone sample {}: {}", abs, e));
	assert!(!data.is_empty(),
		"bora_data_driver: lone sample {} is empty", abs);
	let keep = ((data.len() as f64 * perc_samples / 100.0).ceil()
		as usize).clamp(1, data.len());
	let dir = format!("{}/sample", pd);
	fs::create_dir_all(&dir).unwrap_or_else(|e| panic!(
		"bora_data_driver: mkdir {}: {}", dir, e));
	let base = Path::new(&abs).file_name().unwrap()
		.to_str().unwrap().to_string();
	let dst = format!("{}/{}", dir, base);
	fs::write(&dst, &data[..keep]).unwrap_or_else(|e| panic!(
		"bora_data_driver: write {}: {}", dst, e));
	utils::logger::log(0, utils::logger::LOG1, &format!(
		"shrink_lone_sample: {} -> {} ({} of {} bytes)",
		rel, dst, keep, data.len()));
	let mut out = bins;
	for b in out.iter_mut() {
		for p in b.iter_mut() { *p = dst.clone(); }
	}
	out
}

/// Snark-decider release gate. MUST match PAPER_DATA.py's FLAG
/// (scripts/PAPER_DATA.py:201-202).
const SNARK_WAIT_FLAG: &str = "/tmp/snark_start/flag";

/// The ONE GlobalConfig writer for every neo run (full x3 and scale x2).
/// neo is forced ON unconditionally; the part topology is COPIED from
/// `role`, never re-derived. Legacy's `b_pin_lkup_share = true` pin is
/// deliberately NOT carried: neo needs a far larger share than legacy's
/// hand-set 1, so the driver's back-solve must run.
fn apply_spec_config(spec: &DatasetSpec, b_dry_run: bool,
	role: &PartRole) {
	// ONE write guard for the whole update, so no reader can observe a
	// half-applied config. NOTHING inside this scope may CALL into code
	// that locks GLOBAL_CONFIG again -- the RwLock is not reentrant and
	// the second acquire self-deadlocks on this same thread.
	let mut g = get_global_config();
	// (1) neo ALWAYS -- no env, no opt-out. 0 wrap keys = auto-derive.
	g.clamav_cfg.b_use_discharge_neo = true;
	g.neo_wrap_keys = 0;
	// tune's trial builds read this global; the driver re-mirrors its
	// own param at fold time (zkp_driver.rs:1985).
	g.b_check_lkup = spec.b_check_lkup;
	// SDE arm + discharge knobs.
	g.clamav_cfg.b_aggressive_sde_for_rep = spec.b_aggressive;
	g.clamav_cfg.sde_rep_fanout_cap = spec.fanout_cap;
	g.clamav_cfg.min_pm_word_len = spec.min_pm_word_len;
	g.range2_bit = spec.range2_bit;
	// all 7 ladder floors.
	g.min_subsigs = spec.min_subsigs;
	g.min_basis_unique_states = spec.min_basis_unique_states;
	g.min_basis_acc_states = spec.min_basis_acc_states;
	g.min_basis_pats_in_trace = spec.min_basis_pats_in_trace;
	g.min_avg_pats_per_subsig = spec.min_avg_pats_per_subsig;
	g.min_dfa_sigs = spec.min_dfa_sigs;
	g.min_dfa_subsigs = spec.min_dfa_subsigs;
	g.n_par_snark = spec.n_par_snark;
	g.n_par_snark_cp = spec.n_par_snark_cp;
	// spec-owned (M103): full_dlp leaves the default 1 but full_dna
	// sets 8 (zkp_driver.rs:5297); NOT inert in general -- its
	// semaphore is inside pass_all (driver.rs:1831), before the
	// b_one_proof / b_folding_only returns.
	g.n_par_batch_claim = spec.n_par_batch_claim;
	g.log_level = spec.log_level;
	// legacy couples fold-only with the light decider (zkp_driver.rs
	// :6768-6772): a non-proving part must never build heavy keys.
	g.b_light_test = b_dry_run || !role.b_proves;
	// part topology, copied from part_role -- one source of truth.
	g.b_folding_only = !role.b_proves;
	g.b_one_proof = role.b_proves;
	g.snark_wait_flag =
		role.b_wait_snark.then(|| SNARK_WAIT_FLAG.to_string());
	// the FOLD reloads the DB from cache (2x RAM avoidance); the build
	// passes read=false as a build_or_load PARAM, so the two never
	// conflict. Snark cache fully off under the reset rule.
	g.b_read_cache = true;
	g.b_read_snark_cache = false;
	g.b_write_snark_cache = false;
	// Zeroed explicitly: both drivers read it, and a stale true would
	// silently turn the fold into a no-op dry run.
	g.b_dryrun_after_capcheck = false;
	// Zeroed for the same reason: a stale true (a scale run earlier in
	// this process) would rob a full run of its fail-fast CapErr abort.
	// Scale flips it back on AFTER this call.
	g.b_scale_catch_caperr = false;
	// Both written EXPLICITLY rather than left at their defaults: the
	// config is process-wide, and the CapErr share bump only ever
	// ratchets UP (zkp_driver.rs:2235), so a stale pin or a stale high
	// share would silently survive into this run.
	g.b_pin_lkup_share = false;      // -> driver back-solves the share
	g.perc_lkup_share = 1;           // the ratchet's floor
}

/// Builds the dataset's DB from cfg_dir, ALWAYS from scratch.
/// read=false dodges build_or_load's stale-cache trap (it checks only
/// that a cache EXISTS, not that it matches the sig file -- fatal once
/// the rule count varies); write=true because the fold reloads the DB
/// from this cache. Call AFTER apply_spec_config: default_clamav_cfg()
/// is a snapshot of the global clamav_cfg (clamav.rs:3941).
fn build_fresh_db(spec: &DatasetSpec, cfg_dir: &str, cache_dir: &str)
	-> Arc<ClamavDB<Fr>> {
	let cfg = default_clamav_cfg();
	let mut vlog = vec![];
	let [sig, dfa, ised, ised_igc] = cfg_paths(spec, cfg_dir);
	Arc::new(ClamavDB::<Fr>::build_or_load(&cfg, &sig, &dfa, &ised,
		&ised_igc, &mut vlog, cache_dir, false, true)
		.unwrap_or_else(|e| panic!(
			"bora_data_driver: build {} db from {}: {:?}",
			spec.name, cfg_dir, e)))
}

/// The four config file paths for a run: sig, main_dfa, needs_ised,
/// needs_ised_igc. Shared by the DB build and the fold reload so the
/// two can never drift apart.
fn cfg_paths(spec: &DatasetSpec, cfg_dir: &str) -> [String; 4] {
	[format!("{}/{}", cfg_dir, spec.sig_file),
		format!("{}/main_dfa.dat", cfg_dir),
		format!("{}/needs_ised.dat", cfg_dir),
		format!("{}/needs_ised_igc.dat", cfg_dir)]
}

/// Foldpot's canonical full-length 0-pad word (driver.rs:2900):
/// chunk_len*62 nibbles = exactly chunk_len packed Fr.
const ZERO_WORD_NAME: &str = "__0word__";

fn zero_word_nibbles(chunk_len: usize) -> Vec<u8> {
	utils::data::gen_pad_nibbles(0, chunk_len * 62)
}

/// Holds b_estimate_caps=true for a scope, restoring the prior value
/// on drop. Legacy keeps the flag on from discharge THROUGH tuning
/// (zkp_driver.rs:7718-7897); fold-time flags are the fold's business.
struct EstimateCapsGuard(bool);

impl EstimateCapsGuard {
	fn on() -> Self {
		let prev = read_global_config().b_estimate_caps;
		get_global_config().b_estimate_caps = true;
		EstimateCapsGuard(prev)
	}
}

impl Drop for EstimateCapsGuard {
	fn drop(&mut self) {
		get_global_config().b_estimate_caps = self.0;
	}
}

/// Index-aligned tuning sample; the 0-pad word is always LAST. Both
/// stats fixed at construction: total INCLUDES the pad (aggr axis,
/// zkp_driver.rs:7871), bin_word_lens EXCLUDES it (per-bin axes).
struct TuningSet {
	words: Vec<Vec<Fr>>,
	infos: Vec<WordInfo>,
	vdata: Vec<FailDischargeRecord>,
	total_word_n: usize,
	// One entry per corpus bin, bin order == job order (manifests
	// are written verbatim, :340): that bin's summed packed word
	// length, pad excluded -- same population as the fold's
	// job_word_lens (zkp_driver.rs:1679/:2073). MIN (cover_word_n)
	// sizes the lkup share; MAX feeds the non-aggr probe axis.
	bin_word_lens: Vec<usize>,
}

/// The ONE quick_discharge call site: pack + discharge a single word.
fn discharge_word(db: &ClamavDB<Fr>, cfg: &ClamavApproxConfig,
	name: &str, nibbles: &Vec<u8>, chunk_len: usize)
	-> (Vec<Fr>, WordInfo, FailDischargeRecord) {
	let fnib: Vec<Fr> = nibbles.iter()
		.map(|x| Fr::from(*x as u32)).collect();
	let packed = utils::data::pack_nibbles(&fnib);
	let (fdr, rec) = quick_discharge_file_by_crit_bag_pm(
		name, nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
		&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
		&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
		&db.bundle_subsig_igc.vec_acdfa[0], true, cfg,
		&db.sig_to_id, chunk_len, chunk_len);
	(packed, rec, fdr)
}

/// Discharges the corpus bins (par per bin) then the 0-pad word, which
/// is discharged FOR REAL so its chunks enter the aggr universe
/// (legacy non-aggr seeds WordInfo::dummy() instead, :1762).
fn discharge_for_tuning(spec: &DatasetSpec, db: &ClamavDB<Fr>,
	bins: &[Vec<String>]) -> TuningSet {
	use rayon::prelude::*;
	let _est = EstimateCapsGuard::on();   // ChunkPeaks (clamav.rs:3376)
	let cfg = default_clamav_cfg();
	let proot = utils::os::proj_root();
	let mw = spec.chunk_len;
	let (mut words, mut infos, mut vdata) = (vec![], vec![], vec![]);
	let mut bin_word_lens = vec![];
	for bin in bins {
		let trip: Vec<_> = bin.par_iter().map(|p| {
			let abs = if Path::new(p).is_absolute() { p.clone() }
				else { format!("{}/{}", proot, p) };
			discharge_word(db, &cfg, p, &utils::os::read_nibbles(&abs),
				mw)
		}).collect();
		let bin_n: usize = trip.iter().map(|(w, _, _)| w.len()).sum();
		bin_word_lens.push(bin_n);
		for (w, i, v) in trip {
			words.push(w); infos.push(i); vdata.push(v);
		}
	}
	let (w, i, v) = discharge_word(db, &cfg, ZERO_WORD_NAME,
		&zero_word_nibbles(mw), mw);
	words.push(w); infos.push(i); vdata.push(v);
	let total_word_n = words.iter().map(|w| w.len()).sum();
	TuningSet { words, infos, vdata, total_word_n, bin_word_lens }
}

/// Env-free port of perc_lkup_share_for's MATH (zkp_driver.rs:232-243,
/// incl. the two-ceil truncation fix), minus its ZKR_LKSHARE /
/// ZKR_CLAM_LKUP_SHARE operator override: no env can steer the neo
/// share derivation. Pinned by test against the source copy.
fn perc_lkup_share_neo(lkup_len: usize, chunk_len: usize,
	total_word_n: usize, b_check_lkup: bool) -> usize {
	if !b_check_lkup { return 1; }
	let max_nibble_len = chunk_len * LEGS;
	let chunks = ((total_word_n * LEGS) / max_nibble_len).max(1);
	let need_share = (lkup_len + chunks - 1) / chunks;
	((need_share * 100 + max_nibble_len - 1) / max_nibble_len).max(1)
}

/// Pads an ascending aggr ladder to num_circs rungs with slightly
/// RAISED near-clones of rung 0 (never smaller: an under-sized dummy
/// risks CapErr on the per-rung padding word).
fn pad_ladder_to(lad: &mut Vec<CapParams>, num_circs: usize) {
	assert!(!lad.is_empty(),
		"bora_data_driver: pad of an empty ladder");
	let raise = |v: usize, pct: usize| (v * (100 + pct) + 99) / 100;
	let mut i = 0;
	while lad.len() < num_circs {
		i += 1;
		let pct = 5 * i;
		let mut d = lad[0].clone();
		d.basis_unique_states = raise(d.basis_unique_states, pct);
		d.basis_acc_states = raise(d.basis_acc_states, pct);
		d.basis_pats_in_trace = raise(d.basis_pats_in_trace, pct);
		d.cp_basis_unique_states =
			raise(d.cp_basis_unique_states, pct);
		// subsigs stays equal: routing still first-fits real segs to
		// rung 0 / the real upper rungs, so dummies fold only the
		// padding word, which fits by construction.
		lad.insert(i, d);
	}
}

// ================= T9901 v5: demand-vector ladder =================

use crate::band_dp::{cdiv, raw_perc};

/// Pooled T_qm demand of one unit on one arm, from the gauges of its
/// completed P_max walk (QM_REAL_SAT / QM_SAT / QM_WRAP_SAT).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
struct QmNeed {
	/// Non-wrap rows emitted (QM_REAL_SAT fill side).
	real: usize,
	/// Total rows emitted -- the pooled operand (QM_SAT fill side).
	tot: usize,
	/// Wrap-key budget of the walked rung (QM_WRAP_SAT cap side).
	wrap_b: usize,
}

impl QmNeed {
	/// The pooled CapErr guard inverted (fit iff tot <= cap+wrap_b),
	/// floored at true real demand.
	fn need(&self) -> usize {
		self.real.max(self.tot.saturating_sub(self.wrap_b))
	}
}

/// One routing unit's measured demand on every sized axis. Absolute
/// worst-chunk counts (ChunkPeaks scalars); qm from the unit's walk.
#[derive(Clone, Debug, Default, PartialEq)]
struct UnitVec {
	/// NEEDS-subsig universe max over segs (rung fit: <= subsigs-1).
	univ: usize,
	/// FSM pats-in-trace rows, worst chunk (ChunkPeaks).
	pats: usize,
	/// FSM unique states, worst chunk.
	uniq: usize,
	/// FSM accepting states, worst chunk.
	acc: usize,
	/// CP unique states, worst chunk.
	cpu: usize,
	/// SED forward-queue rows, worst chunk.
	fwd: usize,
	/// Carried-live rows, worst chunk (perc back-solve input).
	live: usize,
	/// Active steps, worst chunk (avg_active input).
	active: usize,
	/// Pooled T_qm need per arm [cs, igc], from the P_max walk.
	qm: [usize; 2],
}

impl UnitVec {
	/// Component-wise max -- the group envelope.
	fn join(&mut self, o: &UnitVec) {
		self.univ = self.univ.max(o.univ);
		self.pats = self.pats.max(o.pats);
		self.uniq = self.uniq.max(o.uniq);
		self.acc = self.acc.max(o.acc);
		self.cpu = self.cpu.max(o.cpu);
		self.fwd = self.fwd.max(o.fwd);
		self.live = self.live.max(o.live);
		self.active = self.active.max(o.active);
		self.qm[0] = self.qm[0].max(o.qm[0]);
		self.qm[1] = self.qm[1].max(o.qm[1]);
	}
}

/// NEEDS universe of one unit: max over its segs of the summed subsig
/// count of the failed critical sigs (the same derivation
/// determine_config_aggr runs per chunk, zkp_driver.rs:516-535).
fn universe_of_unit(wi: &WordInfo,
	cnt_by_id: &HashMap<usize, usize>) -> usize {
	wi.failed_c_all_segs.iter().map(|seg| seg.iter()
		.map(|&id| cnt_by_id.get(&id).copied().unwrap_or(0))
		.sum::<usize>()).max().unwrap_or(0)
}

/// Subsig count per sig id (zkp_driver.rs:516-522 verbatim).
fn subsig_cnt_by_id(db: &ClamavDB<Fr>) -> HashMap<usize, usize> {
	let mut m = HashMap::new();
	for s in db.vec_sigs.iter()
		.chain(db.vec_sigs_no_critical_pat.iter()) {
		if let Some(&id) = db.sig_to_id.get(&s.name) {
			m.insert(id, s.vec_subsig_obj.len());
		}
	}
	m
}

/// Count -> basis-rate conversion, CEILING: the derived container
/// nlen*basis/10000 is then >= count, exactly (no slack term).
fn to_basis(count: usize, nlen: usize) -> usize {
	cdiv(count * 10000, nlen.max(1))
}

/// Rung cost for the DP: per-chunk container rows, every term the
/// builder's own formula (band_dp cost + FSM/CP/qm containers).
fn rung_cost(p: &CapParams) -> usize {
	let nlen = p.max_word_len * LEGS;
	let fsm = nlen * (p.basis_pats_in_trace + p.basis_unique_states
		+ p.basis_acc_states) / 10000;
	let cp = nlen * p.cp_basis_unique_states / 10000;
	// StepQueue::vec_size (discharge_adv.rs:526-586): size_pat vs the
	// prod-driven (aggr) or basis*perc-driven (non-aggr) trace side.
	let pat = p.subsigs * p.avg_active_pats_per_subsig;
	let que = if p.prod_pats_expansion == 0 {
		nlen * p.basis_pats_in_trace * p.perc_pats_expansion_rate
			* crate::gadgets::discharge_adv::RES_LARGE_COST
			/ (10000 * 100 * 100)
	} else {
		p.prod_pats_expansion * nlen
			* crate::gadgets::discharge_adv::FWD_COST
			/ (10000 * 100 * 100)
	};
	fsm + cp + que.max(pat) + p.qm_real_rows
}

/// Non-top rung params from a group envelope: measured axes sized by
/// exact inversion, unmeasured axes ride p_max verbatim. Aggr also
/// sizes subsigs/prod and re-applies the dummy-sentinel floors
/// (zkp_driver.rs:650-661); non-aggr carries subsigs and prod (a
/// nonzero prod flips the gadget into the aggressive override) and
/// re-applies the GlobalConfig min_* clamps decreased_copy would.
fn rung_params_from_env(env: &UnitVec, p_max: &CapParams,
	b_aggr: bool) -> CapParams {
	let mut c = p_max.clone();
	c.levels = vec![];
	let nlen = (p_max.max_word_len * LEGS).max(1);
	let fwd_cost = crate::gadgets::discharge_adv::FWD_COST;
	// non-aggr: the v5 carrier bypasses decreased_copy, so its
	// read_global_config().min_* clamps are re-applied here.
	let (mn_pats, mn_uniq, mn_acc, mn_perc, mn_avg) = if b_aggr {
		(2usize, 2usize, 2usize, 1usize, 1usize)
	} else {
		let g = read_global_config();
		(g.min_basis_pats_in_trace.max(2),
			g.min_basis_unique_states.max(2),
			g.min_basis_acc_states.max(2),
			g.min_perc_pats_expansion_rate.max(1),
			g.min_avg_active_pats_per_subsig.max(1))
	};
	if b_aggr {
		c.subsigs = (env.univ + 1).min(p_max.subsigs);
		c.aggr_needs_subsigs = p_max.subsigs;
	}
	let bas = |cnt: usize, pm: usize, mn: usize| to_basis(cnt, nlen)
		.clamp(mn, pm.max(mn));
	c.basis_pats_in_trace =
		bas(env.pats, p_max.basis_pats_in_trace, mn_pats);
	c.basis_unique_states =
		bas(env.uniq, p_max.basis_unique_states, mn_uniq);
	c.basis_acc_states =
		bas(env.acc, p_max.basis_acc_states, mn_acc)
		.max(c.basis_pats_in_trace / 10 + 1); // fsm_adv floor (:568)
	c.cp_basis_unique_states =
		bas(env.cpu, p_max.cp_basis_unique_states, 2);
	// forward queue: exact measured demand (no +10%, no 5/4 -- an
	// under-count promotes the seg via the per-seg router).
	if b_aggr {
		c.prod_pats_expansion = ((env.fwd + 1) * 100_000_000
			/ (nlen * fwd_cost).max(1) + 1)
			.min(p_max.prod_pats_expansion);
	}
	c.perc_pats_expansion_rate =
		raw_perc(env.fwd, env.live, c.basis_pats_in_trace, nlen)
		.min(p_max.basis_pats_in_trace
			* p_max.perc_pats_expansion_rate
			/ c.basis_pats_in_trace.max(1))
		.max(mn_perc);
	c.avg_active_pats_per_subsig =
		cdiv(env.active, c.subsigs.max(1))
		.min(p_max.subsigs * p_max.avg_active_pats_per_subsig
			/ c.subsigs.max(1))
		.max(mn_avg);
	// qm per arm: v4 reducer (sentinel arm off; floor = smallest
	// shippable non-sentinel cap; ceiling = the fixpoint top).
	c.qm_real_rows = if p_max.qm_real_rows == 0 { 0 }
		else { env.qm[0].min(p_max.qm_real_rows).max(2) };
	c.qm_real_rows_igc = if p_max.qm_real_rows_igc == 0 { 0 }
		else { env.qm[1].min(p_max.qm_real_rows_igc).max(2) };
	if b_aggr {
		// dummy-sentinel floors (zkp_driver.rs:650-661 verbatim).
		let pmin = |bp: usize| 16 * 100_000_000
			/ (nlen * bp.max(1) * fwd_cost).max(1) + 1;
		let prod_min = 16 * 100_000_000 / (nlen * fwd_cost).max(1) + 1;
		c.perc_pats_expansion_rate = c.perc_pats_expansion_rate
			.max(pmin(c.basis_pats_in_trace));
		c.perc_pats_expansion_rate_igc = c.perc_pats_expansion_rate_igc
			.max(pmin(c.basis_pats_in_trace_igc));
		c.prod_pats_expansion = c.prod_pats_expansion.max(prod_min);
		c.prod_pats_expansion_igc =
			c.prod_pats_expansion_igc.max(prod_min);
	}
	c
}

/// Exact weighted DP: <= k contiguous groups over cost-sorted rows
/// minimizing sum(weight * rung_cost(group env)). Returns group end
/// indices into `rows` (exclusive); may return < k groups.
fn dp_partition(rows: &[(UnitVec, usize)], k: usize,
	env_cost: &dyn Fn(&UnitVec) -> usize) -> Vec<usize> {
	let n = rows.len();
	if n == 0 { return vec![]; }
	let k = k.min(n).max(1);
	const INF: usize = usize::MAX / 2;
	// dp[g][j]: best cost of the first j rows in g groups.
	let mut dp = vec![vec![INF; n + 1]; k + 1];
	let mut par = vec![vec![0usize; n + 1]; k + 1];
	dp[0][0] = 0;
	for g in 1..=k {
		for j in 1..=n {
			// walk i = j-1 .. 0, growing the envelope incrementally.
			let mut env = UnitVec::default();
			let mut w = 0usize;
			for i in (0..j).rev() {
				env.join(&rows[i].0);
				w += rows[i].1;
				if dp[g - 1][i] == INF { continue; }
				let cst = dp[g - 1][i] + w * env_cost(&env);
				if cst < dp[g][j] { dp[g][j] = cst; par[g][j] = i; }
			}
		}
	}
	// best g: smallest total; ties -> fewer groups.
	let best_g = (1..=k).min_by_key(|&g| (dp[g][n], g)).unwrap();
	let (mut ends, mut j) = (vec![], n);
	for g in (1..=best_g).rev() {
		ends.push(j);
		j = par[g][j];
	}
	ends.reverse();
	ends
}

/// Sort units by the cost of their OWN one-unit rung, dedup equal
/// vectors into weighted rows, DP-partition into <= k contiguous
/// groups. Returns the groups cheapest-first (rows kept, not envelopes,
/// so a caller can verify per-occupant fit).
fn group_units_v5(units: Vec<UnitVec>, p_max: &CapParams, k: usize,
	b_aggr: bool) -> Vec<Vec<(UnitVec, usize)>> {
	let ucost = |u: &UnitVec| -> usize {
		rung_cost(&rung_params_from_env(u, p_max, b_aggr))
	};
	let mut sorted = units;
	sorted.sort_by_cached_key(|u| ucost(u));
	// lossless dedup: equal vectors are interchangeable in a sorted
	// contiguous partition.
	let mut rows: Vec<(UnitVec, usize)> = vec![];
	for u in sorted {
		match rows.last_mut() {
			Some((v, w)) if *v == u => *w += 1,
			_ => rows.push((u, 1)),
		}
	}
	let ends = dp_partition(&rows, k, &ucost);
	let (mut out, mut start) = (vec![], 0usize);
	for &end in &ends {
		out.push(rows[start..end].to_vec());
		start = end;
	}
	out
}

/// Component-wise envelope of one DP group.
fn env_of(grp: &[(UnitVec, usize)]) -> UnitVec {
	let mut env = UnitVec::default();
	for (u, _) in grp { env.join(u); }
	env
}

/// Occupancy (unit count, dedup weights summed) of one DP group.
fn occ_of(grp: &[(UnitVec, usize)]) -> usize {
	grp.iter().map(|(_, w)| w).sum()
}

/// Serial per-unit qm harvest at P_max: one-rung planner, the meter's
/// own walk pattern (reset -> walk -> read the arm gauges). Walks ONLY
/// `units`; a failed walk is a loud invariant break (P_max is the
/// converged fixpoint -- everything must fit it).
fn qm_walk_units(spec: &DatasetSpec, db: &Arc<ClamavDB<Fr>>,
	ts: &TuningSet, p_max: &CapParams, units: &[usize])
	-> HashMap<usize, [QmNeed; 2]> {
	use folding_schemes::folding::foldpot::sigma_ir1cs
		::LookupTableTwoCol as _;
	use utils::consts::{reset_qm_gauges, QM_REAL_SAT, QM_SAT,
		QM_WRAP_SAT};
	use utils::logger::LOG2;
	let mut out = HashMap::new();
	if units.is_empty() { return out; }
	let poseidon = poseidon_canonical_config::<Fr>();
	let mw = spec.chunk_len;
	let lkup_len = db.lkup.get_size();
	let layered = if spec.b_aggressive {
		let caps = vec![caps_from_params_aggr(p_max)];
		build_circs_adv_aggr::<Fr, C1, CS1>(&poseidon,
			ts.total_word_n, mw, lkup_len, db.clone(), &caps, false)
	} else {
		let (cp, sed, dfa, cp_igc, sed_igc) =
			caps_from_params_general(p_max);
		build_circs_adv::<Fr, C1, CS1>(&poseidon, ts.total_word_n,
			mw, lkup_len, db.clone(), &cp, &sed, &dfa, &cp_igc,
			&sed_igc, &vec![], 1, false)
	};
	let planner = CapacityPlanner::<C1, FC<Fr, C1, CS1>, LK<Fr>,
		GM<Fr>, false>::new(layered);
	for &i in units {
		let padded =
			utils::data::pad_word_to_multiple::<Fr>(&ts.words[i], mw);
		reset_qm_gauges();
		planner.plan_nd_advice(0, LOG2, false, &padded,
			&ts.infos[i], "v5").unwrap_or_else(|e| panic!(
			"v5[{}]: unit {} fails the P_max walk: {:?}",
			spec.name, i, e));
		let mk = |arm: usize| QmNeed {
			real: QM_REAL_SAT[arm].get().0,
			tot: QM_SAT[arm].get().0,
			wrap_b: QM_WRAP_SAT[arm].get().1,
		};
		out.insert(i, [mk(0), mk(1)]);
	}
	out
}

/// Harvest every unit's demand vector: ChunkPeaks scalars + the NEEDS
/// universe (both already computed by the tuning discharge), plus the
/// qm walk. b_walk_all=false screens the walk to units with a nonzero
/// universe (aggr: no obligation -> empty SED store -> empty Q_m).
fn harvest_units(spec: &DatasetSpec, db: &Arc<ClamavDB<Fr>>,
	ts: &TuningSet, p_max: &CapParams, b_walk_all: bool)
	-> Vec<UnitVec> {
	let cnt = subsig_cnt_by_id(db);
	let mut units: Vec<UnitVec> = (0..ts.words.len()).map(|i| {
		let cp = &ts.vdata[i].chunk_peaks;
		UnitVec {
			univ: universe_of_unit(&ts.infos[i], &cnt),
			pats: cp.max_pats_in_trace,
			uniq: cp.max_unique_states,
			acc: cp.max_acc_states,
			cpu: cp.max_cp_unique_states,
			fwd: cp.max_fwd_entries_per_chunk,
			live: cp.max_carried_live_per_chunk,
			active: cp.max_active_steps_per_chunk,
			qm: [0, 0],
		}
	}).collect();
	let need_walk: Vec<usize> = (0..units.len())
		.filter(|&i| b_walk_all || units[i].univ > 0).collect();
	let qm = qm_walk_units(spec, db, ts, p_max, &need_walk);
	for (i, q) in qm {
		units[i].qm = [q[0].need(), q[1].need()];
	}
	units
}

/// v5 aggressive ladder: DP-partition the harvested units and size
/// every non-top rung to its occupants' measured max; the top rung is
/// the fixpoint P_max VERBATIM. Replaces the band/peel ladder.
fn build_ladder_v5_aggr(spec: &DatasetSpec, db: &Arc<ClamavDB<Fr>>,
	ts: &TuningSet, fixpoint: Vec<CapParams>, num_circs: usize)
	-> Vec<CapParams> {
	let p_max = fixpoint.last().expect("v5: empty fixpoint").clone();
	if num_circs <= 1 { return vec![p_max]; }
	let units = harvest_units(spec, db, ts, &p_max, false);
	let grps = group_units_v5(units, &p_max, num_circs, true);
	// size rungs; the LAST group ships P_max verbatim (fixpoint).
	let (mut lad, mut hist) = (vec![], vec![]);
	for (gi, grp) in grps.iter().enumerate() {
		if gi + 1 == grps.len() {
			lad.push(p_max.clone());
		} else {
			lad.push(rung_params_from_env(&env_of(grp), &p_max, true));
		}
		hist.push(occ_of(grp));
	}
	utils::logger::log(0, utils::logger::LOG1, &format!(
		"v5[{}]: {} rungs, occupancy hist={:?}, costs={:?}",
		spec.name, lad.len(), hist,
		lad.iter().map(rung_cost).collect::<Vec<_>>()));
	lad
}

/// v5 non-aggressive levels: same harvest + DP over the job's units;
/// returns the per-descent-step CapParams TOP-FIRST (levels[i] = the
/// circuit built at descent step i+1), len == num_circs-1. Unmeasured
/// axes (avg_pats, sigs_sed, perc_comp, dfa_*, igc) ride P_max.
fn size_levels_v5_non_aggr(spec: &DatasetSpec,
	db: &Arc<ClamavDB<Fr>>, ts: &TuningSet, p_max: &CapParams,
	num_circs: usize) -> Vec<CapParams> {
	let units = harvest_units(spec, db, ts, p_max, true);
	let grps = group_units_v5(units, p_max, num_circs, false);
	// groups ascending; drop the top group (it IS the converged P_max);
	// emit the rest TOP-FIRST for build order; pad with the cheapest
	// group's params if the DP merged below num_circs.
	let mut envs: Vec<UnitVec> =
		grps.iter().map(|g| env_of(g)).collect();
	let hist: Vec<usize> = grps.iter().map(|g| occ_of(g)).collect();
	envs.pop(); // top group -> P_max itself, not a level
	let mut lvls: Vec<CapParams> = envs.iter().rev()
		.map(|e| rung_params_from_env(e, p_max, false)).collect();
	while lvls.len() < num_circs - 1 {
		let pad = lvls.last().cloned()
			.unwrap_or_else(|| rung_params_from_env(
				&UnitVec::default(), p_max, false));
		lvls.push(pad);
	}
	utils::logger::log(0, utils::logger::LOG1, &format!(
		"v5[{}]: {} levels, occupancy hist={:?}, costs={:?}",
		spec.name, lvls.len(), hist,
		lvls.iter().map(rung_cost).collect::<Vec<_>>()));
	lvls
}

/// Capacity tuner for one (db, tuning set): aggr -> rung ladder via
/// determine_config_aggr, non-aggr -> single converged CapParams.
/// GlobalConfig touches: share derive+pin, non-aggr floor write-back.
fn tune(spec: &DatasetSpec, db: &Arc<ClamavDB<Fr>>, ts: &TuningSet,
	num_circs: usize) -> Vec<CapParams> {
	use folding_schemes::folding::foldpot::sigma_ir1cs
		::LookupTableTwoCol as _;
	assert!(num_circs >= 1, "bora_data_driver: num_circs must be >= 1");
	let mw = spec.chunk_len;
	let lkup_len = db.lkup.get_size();
	// The ONE share derivation, via the env-free port, sized off the
	// SMALLEST non-empty bin: bins are the fold's jobs, and Pass 1
	// asserts coverage PER JOB (foldpot driver.rs:2027), so the
	// fewest-chunk job binds (cover_word_n; T9902). tune sees ALL
	// bins, so every part derives the same value; the pin makes the
	// driver skip its own per-slice re-derive at fold time
	// (zkp_driver.rs:1708/:2103), so no env can reach the neo share.
	let cover = cover_word_n(&ts.bin_word_lens);
	assert!(!spec.b_check_lkup || cover > 0,
		"bora_data_driver: {} check-on tune: all bins empty, no \
		 job can cover the lkup table", spec.name);
	let perc = perc_lkup_share_neo(lkup_len, mw, cover,
		spec.b_check_lkup);
	{
		let mut g = get_global_config();
		g.perc_lkup_share = perc;
		g.b_pin_lkup_share = true;
	}
	// 8 = production (attic/scripts/PAPER_DATA.py:329). Hard-coded:
	// thread count is parallelism only, not a tuning input (hist
	// identical), and PAPER_DATA.py sets no env vars.
	let n_threads = 8;
	// neo passed as literal true: apply_spec_config forced it and
	// build_and_tune asserted it. No global reads here -- an inline
	// read guard across these calls self-deadlocks (see :6927).
	if spec.b_aggressive {
		let mut vlog = vec![];
		let est = estimate_config_aggr::<Fr>(&ts.vdata, &**db, &[100],
			&mut vlog);
		let seed = estimated_to_capparams_aggr(&est[0], mw,
			spec.range2_bit, 3);
		let k_max = num_circs;
		// 1 rung needs no log-bucket coarsening (:7711); peel 90 as
		// runcfg_full.json, inert below k_max=3 (:560).
		let n_buckets = if num_circs == 1 { 1 } else { 2048 };
		let (lad, hist) = determine_config_aggr::<Fr, C1, CS1>(true,
			db.clone(), &ts.words, &ts.infos, &ts.vdata, seed, mw,
			lkup_len, ts.total_word_n, k_max, n_buckets, 60,
			n_threads, 8, 90)
			.unwrap_or_else(|e| panic!(
				"bora_data_driver: determine_config_aggr: {}", e));
		// T9901 v5: re-derive every non-top rung from the measured
		// per-unit demand; the fixpoint top carries verbatim.
		let mut lad = build_ladder_v5_aggr(spec, db, ts, lad,
			num_circs);
		if lad.len() < num_circs {
			let short = lad.len();
			pad_ladder_to(&mut lad, num_circs);
			utils::logger::log(0, utils::logger::LOG1, &format!(
				"tune[{}]: demand ladder {} rungs -> padded to {} \
				 (raised clones of rung 0)", spec.name, short,
				num_circs));
		}
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"tune[{}]: ladder {} rungs, hist={:?}", spec.name,
			lad.len(), hist));
		lad
	} else {
		assert_eq!(spec.vec_decrease_level.len(), num_circs - 1,
			"bora_data_driver: vec_decrease_level len != num_circs-1");
		// seed = the dataset's hand caps, warm-started low so the
		// probe converges to the true minimum (:1728-1748).
		let mut p0 = spec.hand_seed.clone().unwrap_or_else(|| panic!(
			"bora_data_driver: {} non-aggr needs hand_seed", spec.name));
		p0.perc_pats_expansion_rate =
			p0.perc_pats_expansion_rate.min(16);
		p0.perc_pats_expansion_rate_igc =
			p0.perc_pats_expansion_rate_igc.min(16);
		p0.avg_active_pats_per_subsig =
			p0.avg_active_pats_per_subsig.min(2);
		p0.avg_active_pats_per_subsig_igc =
			p0.avg_active_pats_per_subsig_igc.min(2);
		p0.qm_real_rows = 2;
		p0.qm_real_rows_igc = 2;
		// the seed follows the EFFECTIVE shape (dry_range2_bit /
		// dry_chunk_len); no-op at full shape.
		p0.acdfa_state_part_bits = spec.range2_bit;
		p0.max_word_len = spec.chunk_len;
		// probe axis only, NOT the share: these probes run the
		// build_circs_adv guard check-off (zkp_driver.rs:1126);
		// legacy passes its max here too (zkp_driver.rs:1807).
		let max_bin = ts.bin_word_lens.iter().copied().max()
			.unwrap_or(0);
		let new = determine_config_non_aggr::<Fr, C1, CS1>(true,
			db.clone(), &ts.words, &ts.infos, p0, mw, lkup_len,
			max_bin, &spec.vec_decrease_level.to_vec(),
			num_circs, 60, n_threads)
			.unwrap_or_else(|e| panic!(
				"bora_data_driver: determine_config_non_aggr: {}", e));
		// ladder floors from the CONVERGED caps: the tuner's own write
		// is reverted by its FloorGuard, and the fold's decreased_copy
		// must see the same flat axis (:1788-1802). Needs the DB, so
		// it cannot move to fold (build_and_tune drops the DB).
		let cp_floor = db.vec_sigs_no_critical_pat.len() + 1;
		let mut g = get_global_config();
		g.min_subsigs = new.subsigs;
		g.min_subsigs_igc = new.subsigs_igc;
		g.min_cp_subsigs = cp_floor.min(new.cp_subsigs);
		drop(g);
		// T9901 v5: measured level targets replace the ratio descent
		// (consumed by build_circs_adv via CapParams.levels).
		let mut new = new;
		if num_circs > 1 {
			new.levels = size_levels_v5_non_aggr(spec, db, ts, &new,
				num_circs);
		}
		vec![new]
	}
}

/// The shared tuning kernel (full x3, scale x2): thin config if asked,
/// fresh DB, discharge, tune. The scope is the point: DB + tuning set
/// are freed at return, before the caller folds.
pub(crate) fn build_and_tune(spec: &DatasetSpec, db_count: usize,
	bins: &[Vec<String>], num_circs: usize, part_id: usize)
	-> Vec<CapParams> {
	// precondition, not re-application: tuning on stale flags would
	// silently tune the wrong arm.
	assert!(read_global_config().clamav_cfg.b_use_discharge_neo,
		"bora_data_driver: apply_spec_config before build_and_tune");
	let proot = utils::os::proj_root();
	let src_dir = format!("{}/{}", proot, spec.config_dir);
	let n_sigs = read_lines_nonblank(
		&format!("{}/{}", src_dir, spec.sig_file)).len();
	if db_count < n_sigs {
		// bound = table size minus one chunk of margin; inert at any
		// full-shape bit (every sig fits), load-bearing only when
		// effective_spec swapped in a dry_range2_bit.
		create_smaller_config_bounded(&src_dir, spec.sig_file,
			db_count, &format!("{}/config", plan_dir(spec.name, part_id)),
			(1usize << spec.range2_bit) - spec.chunk_len * 62);
	}
	let db = build_fresh_db(spec,
		&config_dir_for(spec, db_count, n_sigs, part_id),
		&cache_dir_for(spec, part_id));
	// spans tune as well: probe advice paths may re-discharge, and
	// legacy holds the flag true through determine_config.
	let _est = EstimateCapsGuard::on();
	let ts = discharge_for_tuning(spec, &db, bins);
	let lad = tune(spec, &db, &ts, num_circs);
	// Measurement only, and only under its env gate. It lives here
	// because the DB and the tuning set are still alive at this point
	// and are dropped the moment this function returns.
	if b_meter_t9901() {
		meter_unit_demand(spec, &db, &ts, &lad, part_id);
	}
	lad
}

// Probe-side aliases for the meter, mirroring zkp_driver.rs:71-73.
// Those are private to that module, so this redeclares them from the
// same underlying types rather than widening their visibility.
type LK<F> = LookupTableTwoCol_Inst<F>;
type GM<F> = CompositeGadgetMapper<F, LK<F>>;
type FC<F, C, CS> = SigmaIR1CS_Inst<F, C, CS, LK<F>, GM<F>, false>;

/// T9901 meter gate: unset = wholly inert. Read once, like
/// consts::b_probe_p36.
fn b_meter_t9901() -> bool {
	static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
	*B.get_or_init(|| std::env::var("ZKR_METER_T9901").is_ok())
}

/// One routing unit's measured Q_m demand, read from the gauges the
/// gadget already records (discharge_adv_neo.rs:2003-2005). Each value
/// is the PEAK over the unit's segments; exact for a one-segment unit.
#[derive(Debug, Clone, serde::Serialize)]
pub(crate) struct UnitDemand {
	/// Index of this unit in the tuning set's word list.
	pub unit: usize,
	/// Packed word length; segments = ceil(word_len / chunk_len).
	pub word_len: usize,
	/// TOTAL T_qm rows emitted vs the pooled budget that actually
	/// gates (discharge_adv_neo.rs:1983-1987, guard at :2057). This
	/// is the binding pair: qm_real_rows is only one TERM of the cap,
	/// so real-side demand can exceed its own share without a CapErr
	/// whenever the wrap side has slack. Case-sensitive arm.
	pub qm_tot_cs: usize,
	/// Same, ignore-case arm.
	pub qm_tot_igc: usize,
	/// Pooled budget = qm_real_cap + wrap_budget + 1, cs arm.
	pub qm_tot_cap_cs: usize,
	/// Same, ignore-case arm.
	pub qm_tot_cap_igc: usize,
	/// Non-wrap T_qm rows emitted, case-sensitive arm. THE T9901
	/// number: what qm_real_rows would have to be for this unit alone.
	pub qm_real_cs: usize,
	/// Same, ignore-case arm.
	pub qm_real_igc: usize,
	/// Cap those rows were CHECKED against, case-sensitive arm. Not
	/// the shipped qm_real_rows: qm_real_cap() falls through to the
	/// dense vec_size(ResLarge) bound whenever the field arrives 0,
	/// and telling those two apart is the whole non-aggr question.
	pub qm_real_cap_cs: usize,
	/// Same, ignore-case arm.
	pub qm_real_cap_igc: usize,
	/// (subsig,step) wrap key groups emitted, case-sensitive arm.
	pub wrap_cs: usize,
	/// Same, ignore-case arm.
	pub wrap_igc: usize,
	/// Wrap budget the keys were checked against, case-sensitive arm.
	pub wrap_cap_cs: usize,
	/// Same, ignore-case arm.
	pub wrap_cap_igc: usize,
	/// Active (non-zero) subsigs in a segment, case-sensitive arm.
	pub sub_cs: usize,
	/// Same, ignore-case arm.
	pub sub_igc: usize,
	/// capacity.subsigs the actives were checked against, cs arm.
	pub sub_cap_cs: usize,
	/// Same, ignore-case arm.
	pub sub_cap_igc: usize,
	// PREDICTOR COLUMNS -- measurement only, never read back. Every
	// per-file quantity the discharge trace exposes at this point, so
	// the Q_m rows above can be correlated against each one offline.
	// A column that reproduces the qm_real_cs vector is the candidate
	// to replace max_fwd at determine_config.rs:559.
	/// FailDischargeRecord::flen, bytes. A CONTROL, not a candidate:
	/// DLP demand is size-uncorrelated (the 8402-row outlier is a
	/// 75-word file, while the 2555-word file needs 1530).
	pub flen: usize,
	/// Chunks this unit splits into (needs_per_chunk.len()). 0 when
	/// the aggressive estimator pass left the profile empty.
	pub n_chunks: usize,
	/// ChunkPeaks::max_needs_subsigs -- per-chunk NEEDS universe, max
	/// over chunks. Selector proxy 1.
	pub p_needs: usize,
	/// ChunkPeaks::max_fwd_entries_per_chunk -- what :559 uses TODAY,
	/// via RungSpec::max_fwd. Expected to read 0 across the body.
	pub p_fwd: usize,
	/// ChunkPeaks::max_active_steps_per_chunk -- active pattern-steps
	/// summed across subsigs, max over chunks. Selector proxy 3.
	pub p_active: usize,
	/// ChunkPeaks::max_pats_in_trace -- sum of freq*#patterns in a
	/// chunk, max over chunks. Selector proxy 4.
	pub p_pats: usize,
	/// ChunkPeaks::max_unique_states -- distinct DFA states per chunk,
	/// max over chunks. Selector proxy 5.
	pub p_uniq: usize,
	/// ChunkPeaks::max_acc_states -- accepted-state count per chunk,
	/// max over chunks. Selector proxy 6.
	pub p_acc: usize,
	/// ChunkPeaks::max_cp_unique_states -- distinct crit-pattern DFA
	/// states per chunk, max over chunks. Selector proxy 7.
	pub p_cpu: usize,
	/// ChunkPeaks::max_carried_live_per_chunk -- carried live-location
	/// count summed across subsigs. NOT a selector proxy; included
	/// because the carried StepQueue is the nearest kin to T_qm.
	pub p_live: usize,
	/// ChunkPeaks::seg_size -- nibbles per chunk. A normaliser: a
	/// per-chunk demand may only compare once divided by it.
	pub p_seg: usize,
	/// ChunkPeaks::perc_pats_expansion_rate -- 100*avg chunks a
	/// pattern spans (>=100). Normaliser, not a candidate.
	pub p_perc: usize,
	/// false if this unit CapErr'd even at the ladder top, which makes
	/// every value above a LOWER BOUND rather than the true demand.
	pub ok: bool,
}

/// T9901 measurement: probe each routing unit against a ONE-RUNG
/// ladder (top rung, or ZKR_METER_RUNG) and record its Q_m demand.
/// Writes {plan_dir}/meter.json; changes no capacity and no behaviour.
fn meter_unit_demand(spec: &DatasetSpec, db: &Arc<ClamavDB<Fr>>,
	ts: &TuningSet, lad: &[CapParams], part_id: usize) {
	use folding_schemes::folding::foldpot::sigma_ir1cs
		::LookupTableTwoCol as _;
	use utils::consts::{reset_qm_gauges, QM_REAL_SAT, QM_SAT,
		QM_SUB_SAT, QM_WRAP_SAT};
	use utils::logger::{log, LOG1, LOG2};
	assert!(!lad.is_empty(), "bora_data_driver: empty ladder");
	// The WIDEST rung, so nothing CapErrs and every unit records its
	// true demand. It is the LAST: aggr ladders are cheapest-first
	// (zkp_driver.rs:481, and pad_ladder_to raises clones of rung 0
	// upward), and non-aggr ships a single converged P_max.
	// ZKR_METER_RUNG pins a LOWER rung instead. Sizing a rung to the
	// demand measured at the TOP is only valid if demand is a property
	// of the FILE; if it moves with the capacity the unit runs under,
	// per-rung sizing is circular. Clamped, so an out-of-range value
	// degrades to the top rung rather than panicking.
	let ri = std::env::var("ZKR_METER_RUNG").ok()
		.and_then(|s| s.parse::<usize>().ok())
		.unwrap_or(usize::MAX).min(lad.len() - 1);
	let p = &lad[ri];
	let mw = spec.chunk_len;
	let lkup_len = db.lkup.get_size();
	let poseidon = poseidon_canonical_config::<Fr>();
	// ONE rung, so every unit is measured against the SAME cap and the
	// reading is a demand rather than a routing outcome.
	let layered = if spec.b_aggressive {
		let caps = vec![caps_from_params_aggr(p)];
		build_circs_adv_aggr::<Fr, C1, CS1>(&poseidon,
			ts.total_word_n, mw, lkup_len, db.clone(), &caps, false)
	} else {
		let (cp, sed, dfa, cp_igc, sed_igc) =
			caps_from_params_general(p);
		build_circs_adv::<Fr, C1, CS1>(&poseidon, ts.total_word_n, mw,
			lkup_len, db.clone(), &cp, &sed, &dfa, &cp_igc, &sed_igc,
			&vec![], 1, false)
	};
	let planner = CapacityPlanner::<C1, FC<Fr, C1, CS1>, LK<Fr>,
		GM<Fr>, false>::new(layered);
	// aggr meters legacy's binding-candidate set -- the only files its
	// tuner ever synthesises, so this is not a new cost. ZKR_METER_N
	// widens K to test whether the candidate set misses a peak (there
	// is no Q_m proxy among the seven). non-aggr meters every word,
	// which is already what its tuner probes on EVERY round.
	let units: Vec<usize> = if spec.b_aggressive {
		let k = std::env::var("ZKR_METER_N").ok()
			.and_then(|s| s.parse::<usize>().ok()).unwrap_or(8);
		select_binding_candidates(&ts.vdata, k)
	} else { (0..ts.words.len()).collect() };
	let mut rows: Vec<UnitDemand> = vec![];
	for &i in units.iter() {
		let padded =
			utils::data::pad_word_to_multiple::<Fr>(&ts.words[i], mw);
		reset_qm_gauges();
		let ok = planner.plan_nd_advice(0, LOG2, false, &padded,
			&ts.infos[i], "meter").is_ok();
		let (qt_cs, qtc_cs) = QM_SAT[0].get();
		let (qt_ig, qtc_ig) = QM_SAT[1].get();
		let (qr_cs, qc_cs) = QM_REAL_SAT[0].get();
		let (qr_ig, qc_ig) = QM_REAL_SAT[1].get();
		let (wr_cs, wc_cs) = QM_WRAP_SAT[0].get();
		let (wr_ig, wc_ig) = QM_WRAP_SAT[1].get();
		let (sr_cs, sc_cs) = QM_SUB_SAT[0].get();
		let (sr_ig, sc_ig) = QM_SUB_SAT[1].get();
		// vdata is pushed in lockstep with words/infos, zero-pad word
		// included (:998-1005), so the unit index addresses all three.
		let cp = &ts.vdata[i].chunk_peaks;
		rows.push(UnitDemand {
			unit: i, word_len: ts.words[i].len(),
			flen: ts.vdata[i].flen,
			n_chunks: cp.needs_per_chunk.len(),
			p_needs: cp.max_needs_subsigs,
			p_fwd: cp.max_fwd_entries_per_chunk,
			p_active: cp.max_active_steps_per_chunk,
			p_pats: cp.max_pats_in_trace,
			p_uniq: cp.max_unique_states,
			p_acc: cp.max_acc_states,
			p_cpu: cp.max_cp_unique_states,
			p_live: cp.max_carried_live_per_chunk,
			p_seg: cp.seg_size,
			p_perc: cp.perc_pats_expansion_rate,
			qm_tot_cs: qt_cs, qm_tot_igc: qt_ig,
			qm_tot_cap_cs: qtc_cs, qm_tot_cap_igc: qtc_ig,
			qm_real_cs: qr_cs, qm_real_igc: qr_ig,
			qm_real_cap_cs: qc_cs, qm_real_cap_igc: qc_ig,
			wrap_cs: wr_cs, wrap_igc: wr_ig,
			wrap_cap_cs: wc_cs, wrap_cap_igc: wc_ig,
			sub_cs: sr_cs, sub_igc: sr_ig,
			sub_cap_cs: sc_cs, sub_cap_igc: sc_ig,
			ok });
	}
	let mx = |f: fn(&UnitDemand) -> usize| -> usize {
		rows.iter().map(f).max().unwrap_or(0)
	};
	let (d_cs, d_igc) = (mx(|r| r.qm_real_cs), mx(|r| r.qm_real_igc));
	let n_bad = rows.iter().filter(|r| !r.ok).count();
	// The headline comparison: measured peak demand vs the value the
	// tuner shipped. demand << shipped is exactly the T9901 slack.
	// cap_seen != shipped means the built circuit ignored the ladder
	// field and fell through to the dense bound -- report both.
	log(0, LOG1, &format!("METER[{}]: rung {}/{}, {} units, \
		qm_TOT max cs={}/{} \
		igc={}/{} (the gating pair), qm_real max cs={}/{} \
		igc={}/{} (demand/cap_seen) vs shipped qm_real_rows={}/{}, \
		wrap max cs={}/{} igc={}/{}, sub max cs={}/{} igc={}/{}, \
		caperr_units={}", spec.name, ri, lad.len(), rows.len(),
		mx(|r| r.qm_tot_cs), mx(|r| r.qm_tot_cap_cs),
		mx(|r| r.qm_tot_igc), mx(|r| r.qm_tot_cap_igc),
		d_cs, mx(|r| r.qm_real_cap_cs),
		d_igc, mx(|r| r.qm_real_cap_igc),
		p.qm_real_rows, p.qm_real_rows_igc,
		mx(|r| r.wrap_cs), mx(|r| r.wrap_cap_cs),
		mx(|r| r.wrap_igc), mx(|r| r.wrap_cap_igc),
		mx(|r| r.sub_cs), mx(|r| r.sub_cap_cs),
		mx(|r| r.sub_igc), mx(|r| r.sub_cap_igc), n_bad));
	let path = format!("{}/meter.json", plan_dir(spec.name, part_id));
	match serde_json::to_string_pretty(&rows) {
		Ok(s) => { let _ = fs::write(&path, s); },
		Err(e) => log(0, LOG1,
			&format!("METER[{}]: encode: {}", spec.name, e)),
	}
}

/// Holds b_scale_catch_caperr for a scope so foldpot skips its
/// fail-fast abort hook and a CapErr panic can unwind to
/// probe_catching (vendored driver.rs:2404). Restores on drop.
struct CatchGuard(bool);

impl CatchGuard {
	fn on() -> Self {
		let prev = read_global_config().b_scale_catch_caperr;
		get_global_config().b_scale_catch_caperr = true;
		CatchGuard(prev)
	}
}

impl Drop for CatchGuard {
	fn drop(&mut self) {
		get_global_config().b_scale_catch_caperr = self.0;
	}
}

/// KEY-units -> percent conversion of the dummy self-cover need
/// (port of zkp_driver.rs:2233).
fn share_need_perc(keys: usize, mnl: usize) -> usize {
	(keys * 100 + mnl - 1) / mnl
}

/// One-shot lkup_share bump around a check-on aggressive fold. The
/// self-cover need is only discoverable at foldpot entry (cheap:
/// before any folding), and DcMode::Off has no retry loop of its
/// own -- this is the one bump legacy's step-4 loop performs
/// (zkp_driver.rs:2225-2241). Anything else stays a hard stop.
fn fold_with_self_cover(spec: &DatasetSpec, mut drive: impl FnMut()) {
	let _c = CatchGuard::on();
	for attempt in 0..2 {
		let res = probe_catching(|| {
			drive();
			Ok::<(), Vec<(String, usize)>>(())
		});
		match res {
			Ok(Ok(())) => return,
			Ok(Err(errs)) => {
				let k = match (errs.len(), errs.first()) {
					(1, Some((n, k)))
						if n.starts_with("lkup_share") => *k,
					_ => panic!("bora_data_driver: {} fold: \
						non-share CapErr (HARD STOP): {:?}",
						spec.name, errs),
				};
				assert!(attempt == 0, "bora_data_driver: {} fold: \
					share still short after bump: {:?}",
					spec.name, errs);
				let need = share_need_perc(k, spec.chunk_len * LEGS);
				let mut g = get_global_config();
				assert!(need > g.perc_lkup_share,
					"bora_data_driver: {} fold: non-growing share \
					 bump {} -> {}", spec.name,
					g.perc_lkup_share, need);
				utils::logger::emit_stdout(format!(
					"[{}] fold: dummy self-cover: share {} -> {}",
					spec.name, g.perc_lkup_share, need));
				g.perc_lkup_share = need;
			}
			Err(msg) => panic!("bora_data_driver: {} fold: \
				non-CapErr panic (HARD STOP): {}", spec.name, msg),
		}
	}
}

/// Folds `manifests` (absolute job_<i>.dat paths) with pre-tuned caps
/// via the unmodified legacy driver for the spec's arm. DcMode::Off:
/// the driver must not tune again.
pub(crate) fn fold(spec: &DatasetSpec, cfg_dir: &str, cache_dir: &str,
	manifests: &[String], caps: &[CapParams], num_circs: usize) {
	// caps may arrive from a clone-edited spec, so nothing upstream
	// guarantees these.
	assert!(read_global_config().clamav_cfg.b_use_discharge_neo,
		"bora_data_driver: apply_spec_config before fold");
	assert!(!caps.is_empty(), "bora_data_driver: fold with empty caps");
	let b_chk = spec.b_check_lkup;
	let [sig, dfa, ised, ised_igc] = cfg_paths(spec, cfg_dir);
	{
		// One write scope; nothing inside may lock GLOBAL_CONFIG again.
		let mut g = get_global_config();
		g.b_estimate_caps = false;
		if spec.b_aggressive {
			g.aggr_needs_subsigs = caps[0].aggr_needs_subsigs;
		}
	}
	// NUMA is owned by the launcher: scripts/PAPER_DATA.py pins each
	// part with numactl --cpunodebind (hard CPU) + --preferred-many
	// (soft memory, spills instead of OOM). No in-process policy here.
	if spec.b_aggressive {
		let cs_caps: Vec<_> =
			caps.iter().map(caps_from_params_aggr).collect();
		let drive = || zkp_driver_adv_aggr::<Bn254, PairingVar, C2G2,
			C1, GC1, C2, GC2, CS1, CS2, CS1E, S>(0, &sig,
			manifests.to_vec(), "", false, cache_dir, &dfa, &ised,
			&ised_igc, spec.chunk_len, &cs_caps, b_chk, DcMode::Off);
		if b_chk {
			fold_with_self_cover(spec, drive);
		} else {
			let mut d = drive;
			d();
		}
	} else {
		assert_eq!(caps.len(), 1,
			"bora_data_driver: non-aggr fold wants 1 rung, got {}",
			caps.len());
		assert_eq!(spec.vec_decrease_level.len(), num_circs - 1,
			"bora_data_driver: vec_decrease_level len != num_circs-1");
		let (cp, sed, dfa_cap, cp_igc, sed_igc) =
			caps_from_params_general(&caps[0]);
		zkp_driver_adv::<Bn254, PairingVar, C2G2, C1, GC1, C2, GC2,
			CS1, CS2, CS1E, S>(0, &sig, manifests.to_vec(), "", false,
			cache_dir, &dfa, &ised, &ised_igc, spec.chunk_len,
			&cp, &sed, &dfa_cap, &cp_igc, &sed_igc,
			&spec.vec_decrease_level.to_vec(), num_circs, b_chk,
			DcMode::Off);
	}
}

/// CapErr bump-retry around one fold attempt (port of the legacy scale
/// loop, zkp_driver.rs:7900-7934), generic over the arm. Non-CapErr
/// panics are a HARD STOP; CapErrs bump `p` and retry, at most 30x.
pub(crate) fn retry_caperr(spec: &DatasetSpec, p: &mut CapParams,
	mut f: impl FnMut(&CapParams)) {
	// RULE 1: only scale routes CapErrs through catchable unwinding.
	// Without the flag the first CapErr is a fail-fast abort that
	// never reaches probe_catching below.
	assert!(read_global_config().b_scale_catch_caperr,
		"bora_data_driver: retry_caperr needs b_scale_catch_caperr");
	let mut tries = 0u32;
	loop {
		utils::consts::reset_sat(); // isolate THIS try's saturation
		let res = probe_catching(|| {
			f(p);
			Ok::<(), Vec<(String, usize)>>(())
		});
		match res {
			Ok(Ok(())) => break,
			Ok(Err(errs)) => {
				let (changed, unmapped) =
					apply_caperr_bumps(p, spec.b_aggressive, &errs);
				tries += 1;
				utils::logger::emit_stdout(format!(
					"[{}] fold CapErr bump try {}: {:?}",
					spec.name, tries, errs));
				assert!(changed && unmapped.is_empty(),
					"bora_data_driver: {} CapErr retry stuck \
					 (unmapped={:?}): {:?}", spec.name, unmapped, errs);
				assert!(tries <= 30,
					"bora_data_driver: {} fold: >30 CapErr bumps",
					spec.name);
			}
			Err(msg) => panic!(
				"bora_data_driver: {} fold: non-CapErr panic (HARD \
				 STOP): {}", spec.name, msg),
		}
	}
}

/// Restore legacy dlp_env's two diagnostics under the Python-side
/// ZKR_* scrub: per-part job-log names + per-job coverage PROBE
/// lines. Argv-derived; called at run_neo entry, pre-thread.
fn set_diag_env(part_id: usize) {
	std::env::set_var("ZKR_LOG_TAG", format!("p{}_", part_id));
	std::env::set_var("ZKR_DLP_PROBE_FILES", "1");
}

/// Dry policy (user decisions 2026-08-10): a light run drops the
/// hab22 cover check AND swaps in dry_range2_bit when the spec has
/// one; heavy keeps the spec values. ONE derivation site so every
/// consumer of both fields agrees.
fn effective_spec(spec: &DatasetSpec, b_dry_run: bool)
	-> DatasetSpec {
	let mut s = spec.clone();
	s.b_check_lkup = s.b_check_lkup && !b_dry_run;
	if b_dry_run {
		if let Some(b) = s.dry_range2_bit {
			s.range2_bit = b;
		}
		if let Some(c) = s.dry_chunk_len {
			s.chunk_len = c;
		}
	}
	s
}

/// The full-run pipeline shared by all three datasets. Every part
/// runs it whole-corpus-identically in its own sandbox; the only
/// cross-process file is the snark-start flag.
pub fn run_neo(spec: &DatasetSpec, perc_db: f64,
	perc_samples: f64, num_circs: usize, num_jobs: usize,
	numa_num: usize, part_id: usize, b_dry_run: bool,
	b_ladder_only: bool) -> Vec<CapParams> {
	set_diag_env(part_id);
	let spec = &effective_spec(spec, b_dry_run);
	let role = part_role(part_id, numa_num, num_jobs);
	apply_spec_config(spec, b_dry_run, &role);
	let pd = reset_part_dir(spec, part_id);
	let proot = utils::os::proj_root();
	let n_sigs = read_lines_nonblank(&format!("{}/{}/{}", proot,
		spec.config_dir, spec.sig_file)).len();
	let db_count = count_of(n_sigs, perc_db);
	// reachable only via fractional perc_db: a <2-rule aggressive DB
	// has zero SED demand and underflows the tuner (B102 item 3).
	assert!(!spec.b_aggressive || db_count >= 2,
		"bora_data_driver: {} aggr db_count {} < 2 (perc_db {} too \
		 small)", spec.name, db_count, perc_db);
	let bins = plan_corpus(spec, perc_samples, num_jobs);
	let bins = shrink_lone_sample(&pd, bins, perc_samples);
	let manifests =
		write_job_manifests(&format!("{}/jobs", pd), &bins);
	let ladder = build_and_tune(spec, db_count, &bins, num_circs,
		part_id);
	save_ladder(&ladder, &format!("{}/ladder.json", pd))
		.unwrap_or_else(|e| panic!(
			"bora_data_driver: save ladder: {}", e));
	if b_ladder_only { return ladder; }
	fold(spec, &config_dir_for(spec, db_count, n_sigs, part_id),
		&cache_dir_for(spec, part_id),
		&manifests[role.jobs.clone()], &ladder, num_circs);
	ladder
}

/// DLP full run: run_neo over the DLP const.
pub fn full_dlp_neo(perc_db: f64, perc_samples: f64,
	num_circs: usize, num_jobs: usize, numa_num: usize,
	part_id: usize, b_dry_run: bool, b_ladder_only: bool)
	-> Vec<CapParams> {
	run_neo(&DLP, perc_db, perc_samples, num_circs, num_jobs,
		numa_num, part_id, b_dry_run, b_ladder_only)
}

/// DNA full run: run_neo over the DNA const. Callers pin
/// num_jobs = numa_num = 1 (single offset-anchored sample).
pub fn full_dna_neo(perc_db: f64, perc_samples: f64,
	num_circs: usize, num_jobs: usize, numa_num: usize,
	part_id: usize, b_dry_run: bool, b_ladder_only: bool)
	-> Vec<CapParams> {
	run_neo(&DNA, perc_db, perc_samples, num_circs, num_jobs,
		numa_num, part_id, b_dry_run, b_ladder_only)
}

/// ClamAV full run: run_neo over the CLAM const.
pub fn full_clamav_neo(perc_db: f64, perc_samples: f64,
	num_circs: usize, num_jobs: usize, numa_num: usize,
	part_id: usize, b_dry_run: bool, b_ladder_only: bool)
	-> Vec<CapParams> {
	run_neo(&CLAM, perc_db, perc_samples, num_circs, num_jobs,
		numa_num, part_id, b_dry_run, b_ladder_only)
}

/// Scale variant of a spec: cover check off, ladder emptied (num_circs
/// is pinned 1; legacy's local empty vec, zkp_driver.rs:7511), and
/// "_scale" name/cache renames so a concurrent or prior FULL run's
/// part-0 sandbox and DB cache are never touched (legacy isolated its
/// scale scratch + cache the same way, :7712/:7757). The renamed strs
/// are leaked: the spec fields are &'static and this runs once per
/// invocation.
fn scale_spec_clone(spec: &DatasetSpec) -> DatasetSpec {
	let mut s = spec.clone();
	s.name = Box::leak(
		format!("{}_scale", spec.name).into_boxed_str());
	s.db_cache_dir = Box::leak(
		format!("{}_scale", spec.db_cache_dir).into_boxed_str());
	// scale never cover-checks, so fold's self-cover one-bump path
	// stays disengaged inside retry_caperr's own bump loop.
	s.b_check_lkup = false;
	// scale wants the full 6108x probe trace (discharge_adv_neo);
	// full runs keep LOG3, which silences every LOG4 probe.
	s.log_level = utils::logger::LOG4;
	s.vec_decrease_level = &[];
	// scale-round tuning profile: low floors + low seed (a full-run
	// floor would pin every subset to full size -- flat curve).
	if let Some(st) = spec.scale_tune.clone() {
		s.min_subsigs = st.min_subsigs;
		s.min_basis_unique_states = st.min_basis_unique_states;
		s.min_basis_acc_states = st.min_basis_acc_states;
		s.min_basis_pats_in_trace = st.min_basis_pats_in_trace;
		s.min_avg_pats_per_subsig = st.min_avg_pats_per_subsig;
		s.min_dfa_sigs = st.min_dfa_sigs;
		s.min_dfa_subsigs = st.min_dfa_subsigs;
		s.hand_seed = Some(st.hand_seed);
	}
	s
}

/// Scale sweep (port of collect_scale_data_dlp, zkp_driver.rs:7671):
/// ONE fixed corpus, ascending pin-INCLUSIVE rule counts; per count a
/// fresh thinned DB -> tune -> folding-only fold with CapErr
/// bump-retry. Emits legacy's ROUND markers on stdout; the Python
/// leaf splits on them and packs the bundle. Writes no archive.
pub fn collect_scale_data_neo(spec: &DatasetSpec, corpus_idx: usize,
	vec_count: &[usize], b_dry_run: bool) {
	// Every argument assert fires BEFORE any process-wide write.
	assert!(!vec_count.is_empty(),
		"bora_data_driver: scale vec_count is empty");
	assert!(vec_count.windows(2).all(|w| w[0] < w[1]),
		"bora_data_driver: scale vec_count not strictly ascending: \
		 {:?}", vec_count);
	// counts include the pin: a 1-rule aggressive DB has zero SED
	// demand and underflows the tuner (legacy's smallest is pin+1=2).
	let lo = if spec.b_aggressive { 2 } else { 1 };
	assert!(vec_count[0] >= lo,
		"bora_data_driver: {} scale counts must be >= {} (the count \
		 includes the pin): {:?}", spec.name, lo, vec_count);
	assert!(corpus_idx < spec.scale_sources.len(),
		"bora_data_driver: corpus_idx {} out of range {}",
		corpus_idx, spec.scale_sources.len());
	let proot = utils::os::proj_root();
	let src = spec.scale_sources[corpus_idx];
	let abs_src = format!("{}/{}", proot, src);
	assert!(fs::metadata(&abs_src).map(|m| m.len() > 0)
		.unwrap_or(false),
		"bora_data_driver: scale corpus {} missing or empty (run \
		 scripts/INSTALL.py?)", abs_src);
	let n_sigs = read_lines_nonblank(&format!("{}/{}/{}", proot,
		spec.config_dir, spec.sig_file)).len();
	assert!(*vec_count.last().unwrap() <= n_sigs,
		"bora_data_driver: top scale count {} > {} sigs (an \
		 over-count silently folds the FULL db)",
		vec_count.last().unwrap(), n_sigs);
	// b_dry_run is SHAPE only (effective_spec's dry knobs);
	// scale still never proves, so the flag's decider gates are
	// unreachable either way.
	let eff = effective_spec(spec, b_dry_run);
	let sc = scale_spec_clone(&eff);
	apply_spec_config(&sc, b_dry_run, &part_role(0, 1, 1));
	{
		// One write scope, AFTER apply_spec_config (which zeroes the
		// catch flag). RULE 1: only scale routes fold CapErrs through
		// catchable unwinding, so retry_caperr can bump; full runs
		// keep the fail-fast abort.
		let mut g = get_global_config();
		g.b_folding_only = true;         // scale never proves
		g.b_scale_catch_caperr = true;
	}
	utils::consts::SCALE_DUMP_FWD
		.store(true, std::sync::atomic::Ordering::Relaxed);
	let pd = reset_part_dir(&sc, 0);
	// count-invariant: one bin, one file, written once.
	let bins = vec![vec![src.to_string()]];
	// dry folds a spec-owned byte prefix: fold work is linear in
	// corpus length, so no chunk_len cuts it. Per-dataset because the
	// sources differ in kind -- CLAM's are whole binaries (gdb 6.8 MB,
	// worth truncating), DLP's are 805 B / 1,996 B mails, which at 5%
	// would leave 41 B / 100 B. dry_scale_perc 100.0 = fold whole
	// (shrink_lone_sample no-ops there). Full always folds whole.
	let bins = if b_dry_run {
		shrink_lone_sample(&pd, bins, sc.dry_scale_perc)
	} else {
		bins
	};
	let manifests =
		write_job_manifests(&format!("{}/jobs", pd), &bins);
	for &cnt in vec_count {
		utils::logger::emit_stdout(format!(
			"==== SCALE ROUND BEGIN count={} rules={}/{} corpus={} \
			 ====", cnt, cnt, n_sigs, src));
		utils::logger::flush_logger();
		let mut caps = build_and_tune(&sc, cnt, &bins, 1, 0);
		assert_eq!(caps.len(), 1,
			"bora_data_driver: scale wants 1 rung, got {}",
			caps.len());
		retry_caperr(&sc, &mut caps[0], |p| fold(&sc,
			&config_dir_for(&sc, cnt, n_sigs, 0),
			&cache_dir_for(&sc, 0), &manifests,
			std::slice::from_ref(p), 1));
		// forward-queue saturation of THIS fold (verification only,
		// not plotted); retry_caperr's reset_sat isolated the gauges
		// to the last, successful try. Port of zkp_driver.rs:7936.
		let (fc, fcc) = (utils::consts::get_fwd(false),
			utils::consts::get_fwd_cap(false).max(1));
		let (fi, fic) = (utils::consts::get_fwd(true),
			utils::consts::get_fwd_cap(true).max(1));
		utils::logger::emit_stdout(format!(
			"[{}] count={}: FWD-QUEUE SATURATION cs={:.1}% ({}/{}) \
			 igc={:.1}% ({}/{})", sc.name, cnt,
			100.0 * fc as f32 / fcc as f32, fc, fcc,
			100.0 * fi as f32 / fic as f32, fi, fic));
		utils::logger::flush_logger();
		utils::logger::emit_stdout(format!(
			"==== SCALE ROUND END count={} ====", cnt));
		utils::logger::flush_logger();
	}
}

/// DLP scale sweep: collect_scale_data_neo over the DLP const.
/// DLP scale sweep. b_dry_run is the CLI's dry token (NOT the global
/// flag): it swaps in the dry range table. DLP's corpus is left whole
/// (dry_scale_perc 100.0) and its chunk_len never diverges.
pub fn collect_scale_dlp_neo(corpus_idx: usize, vec_count: &[usize],
	b_dry_run: bool) {
	collect_scale_data_neo(&DLP, corpus_idx, vec_count, b_dry_run)
}

/// ClamAV scale sweep. b_dry_run is the CLI's dry token (NOT the
/// global flag): it swaps in the dry chunk and range table, and cuts
/// the corpus to CLAM's dry_scale_perc.
pub fn collect_scale_clamav_neo(corpus_idx: usize,
	vec_count: &[usize], b_dry_run: bool) {
	collect_scale_data_neo(&CLAM, corpus_idx, vec_count,
		b_dry_run)
}

/// Q2 lookup-composition report, perc-driven. perc>=100 reproduces
/// zkp_driver::tests_zkp_driver::collect_lookup_stats() exactly (same 3
/// hardcoded dataset configs, no thinning). perc<100 builds each
/// dataset's DB over a create_smaller_config-thinned copy under
/// /tmp/bora, removed once that dataset's DB build completes. Prints
/// the report (for the caller's live-log capture) and writes it to
/// dest_path.
pub fn collect_lookup_stats_adv(perc: usize, dest_path: &str) {
	get_global_config().log_level = utils::logger::LOG3;
	// Pristine defaults, captured BEFORE any global writes; the loop
	// restores these on the non-aggressive datasets and re-snapshots
	// its build cfg per iteration (see the comment there).
	let cfg0 = default_clamav_cfg();

	let rc = crate::determine_config::RunCfg::from_path(&format!(
		"{}/data/paper_data/dlp/cfg/config/runcfg_full.json",
		utils::os::proj_root()));
	let dlp_sig_name = Path::new(&rc.sig_file)
		.file_name().and_then(|s| s.to_str())
		.expect("bora_data_driver: bad Dlp sig_file").to_string();

	let datasets: Vec<(String, String, String, usize)> = vec![
		("Mal".to_string(), "data/debug/full_clamav/config".to_string(),
			"main.dat".to_string(), 26),
		("Dna".to_string(), "data/paper_data/dna/config".to_string(),
			"main.dat".to_string(), 27),
		("Dlp".to_string(), format!("{}/regex_pat", rc.config_dir),
			dlp_sig_name, rc.range2_bit),
	];

	let mut rollups: Vec<(&str, Vec<(&'static str, usize)>)> = Vec::new();
	let mut dfa_rollups: Vec<(&str, Vec<(&'static str, usize)>)> = Vec::new();
	let mut blocks: Vec<String> = Vec::new();

	for (name, src_dir, sig_file_name, range2_bit) in &datasets {
		get_global_config().range2_bit = *range2_bit;
		if name.as_str() == "Dlp" {
			get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
			get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
			get_global_config().clamav_cfg.min_pm_word_len = 3;
		} else {
			// restore -- a flip above would outlive its iteration
			let mut g = get_global_config();
			g.clamav_cfg.b_aggressive_sde_for_rep = false;
			g.clamav_cfg.sde_rep_fanout_cap = cfg0.sde_rep_fanout_cap;
			g.clamav_cfg.min_pm_word_len = cfg0.min_pm_word_len;
		}
		// Snapshot AFTER the writes above: expand_rep_subsig and the
		// aggressive shape guard read this THREADED cfg (clam_db.rs
		// :2115), not the global.  The old pre-loop snapshot silently
		// built the Dlp DB with rep expansion OFF while the global
		// said aggressive -- a mixed-mode DB.
		let cfg = default_clamav_cfg();

		let (build_dir, sig_path, tmp_guard):
			(String, String, Option<TmpConfigDir>) = if perc >= 100 {
			(src_dir.clone(), format!("{}/{}", src_dir, sig_file_name), None)
		} else {
			let tmp = format!("/tmp/bora/lkup_adv_{}_{}",
				std::process::id(), name);
			let n_sigs = read_lines_nonblank(
				&format!("{}/{}", src_dir, sig_file_name)).len();
			let sig_path = create_smaller_config(src_dir, sig_file_name,
				count_of(n_sigs, perc as f64), &tmp);
			(tmp.clone(), sig_path, Some(TmpConfigDir(PathBuf::from(tmp))))
		};
		let _tmp_guard = tmp_guard;

		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::build_or_load(&cfg, &sig_path,
			&format!("{}/main_dfa.dat", build_dir),
			&format!("{}/needs_ised.dat", build_dir),
			&format!("{}/needs_ised_igc.dat", build_dir),
			&mut vlog, "lkup_stats_adv_tmp", false, false)
			.expect(&format!("build {} db", name));
		blocks.push(db.fmt_lkup_dist(name, &sig_path));
		rollups.push((name.as_str(), db.lkup_cat_rollup()));
		dfa_rollups.push((name.as_str(), db.dfa_counts()));
	}

	let mut report = String::from(
		"\n\n#################### LOOKUP COMPOSITION REPORT ####################\n");
	for b in &blocks {
		report.push_str(b);
		report.push('\n');
	}
	report.push_str(&fmt_cross_rollup(&rollups));
	report.push_str(&fmt_dfa_cross(&dfa_rollups));
	report.push_str(
		"\n#################### END LOOKUP COMPOSITION REPORT ###############");
	println!("{}", report);
	fs::write(dest_path, &report).unwrap_or_else(|e|
		panic!("bora_data_driver: write {}: {}", dest_path, e));
}

/// One tier block of eval_effective.txt, in the exact line shapes
/// effectiveness.py parses.  Per (file,sig) pair: cp = never critical,
/// sde/dfa = tier reached, fail = |all_dfa|; the four sum to pairs.
fn fmt_tier_block(label: &str, recs: &[FailDischargeRecord],
	total_sigs: usize) -> String {
	if recs.is_empty() { return String::new(); }
	let n = recs.len();
	let (mut cp, mut sde, mut dfa, mut fail) = (0i64, 0i64, 0i64, 0i64);
	for r in recs {
		let (crit, pm, adfa) = (r.crit.len() as i64,
			r.pm.len() as i64, r.all_dfa.len() as i64);
		cp += total_sigs as i64 - crit;
		sde += crit - pm;
		dfa += pm - adfa;
		fail += adfa;
	}
	let total = total_sigs as i64 * n as i64;
	let pct = |x: i64| if total > 0 { 100.0 * x as f64 / total as f64 }
		else { 0.0 };
	let mut s = String::new();
	s.push_str(&format!("=== {} ===\n", label));
	s.push_str(&format!("total_sigs: {}  files: {}  total_pairs: {}\n",
		total_sigs, n, total));
	s.push_str(&format!(
		"cp: {} ({:.4}%)  sde: {} ({:.4}%)  dfa: {} ({:.4}%)  \
fail: {} ({:.4}%)\n",
		cp, pct(cp), sde, pct(sde), dfa, pct(dfa), fail, pct(fail)));
	// sample one-liners only -- the legacy fn also dumped 3 whole
	// FailDischargeRecords (~100KB each dataset) nothing parses
	for (i, r) in recs.iter().take(3).enumerate() {
		s.push_str(&format!(
			"sample {}: fname: {}  flen: {}  |crit|: {}  |bag|: {}  \
|pm|: {}  |all_dfa|: {}\n",
			i + 1, r.fname, r.flen, r.crit.len(), r.bag.len(),
			r.pm.len(), r.all_dfa.len()));
	}
	s.push('\n');
	s
}

/// Refined collect_assess_tier_data (zkp_driver.rs:7428): S7.3 tier
/// shares + the flen filesize re-buckets, written to dest_path.
///
/// Differences from the legacy fn, each one a defect there:
/// - Dlp builds AGGRESSIVE (production DLP.b_aggressive; the legacy
///   forced non-aggr for all three yet read the dlp_corpus_aggr cache,
///   so its output depended on whatever cache happened to exist);
/// - per-dataset knobs are written to the GLOBAL first and the build
///   cfg snapshotted AFTER (both flag channels agree by construction);
/// - no DB cache read or written: (false,false) builds in RAM, so
///   data/cache cannot be poisoned; dry temp configs go to /tmp/bora;
/// - perc thins both the signature set and the scan corpus (dry).
pub fn collect_assess_tier_data_adv(perc: usize, dest_path: &str) {
	use rayon::prelude::*;
	get_global_config().log_level = utils::logger::LOG3;
	// Pristine defaults, captured BEFORE any global writes.
	let cfg0 = default_clamav_cfg();
	let rc = crate::determine_config::RunCfg::from_path(&format!(
		"{}/data/paper_data/dlp/cfg/config/runcfg_full.json",
		utils::os::proj_root()));
	let dlp_sig_name = Path::new(&rc.sig_file)
		.file_name().and_then(|s| s.to_str())
		.expect("bora_data_driver: bad Dlp sig_file").to_string();
	let proot = utils::os::proj_root();

	// (name, config_dir, sig_file, scan lists, range2_bit,
	//  max_word_len, b_aggr); b_aggr mirrors the DatasetSpec arms --
	//  only DLP deploys aggressive.  max_word_len as the legacy fn.
	let mal_scan: Vec<String> = (0..8).map(|i| format!(
		"data/debug/full_clamav/config/binexec_p{}.dat", i)).collect();
	let datasets: Vec<(String, String, String, Vec<String>, usize,
		usize, bool)> = vec![
		("Mal".to_string(),
			"data/debug/full_clamav/config".to_string(),
			"main.dat".to_string(), mal_scan, 26, 512 * 8, false),
		("Dna".to_string(),
			"data/paper_data/dna/config".to_string(),
			"main.dat".to_string(),
			vec!["data/paper_data/dna/config/binexec.dat".to_string()],
			27, 512 * 8, false),
		("Dlp".to_string(), format!("{}/regex_pat", rc.config_dir),
			dlp_sig_name,
			vec!["data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz"
				.to_string()],
			rc.range2_bit, 64, true),
	];

	let mut report = format!(
		"#################### EFFECTIVENESS REPORT (perc={}) \
####################\n\n", perc);
	// records kept per dataset for the filesize re-buckets below
	let mut kept: Vec<(String, Vec<FailDischargeRecord>, usize)> =
		Vec::new();

	for (name, src_dir, sig_file_name, scan_lists, range2_bit,
		max_word_len, b_aggr) in &datasets {
		// Write the per-dataset knobs to the GLOBAL first...
		{
			let mut g = get_global_config();
			g.range2_bit = *range2_bit;
			if *b_aggr {
				g.clamav_cfg.b_aggressive_sde_for_rep = true;
				g.clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
				g.clamav_cfg.min_pm_word_len = 3;
			} else {
				g.clamav_cfg.b_aggressive_sde_for_rep = false;
				g.clamav_cfg.sde_rep_fanout_cap =
					cfg0.sde_rep_fanout_cap;
				g.clamav_cfg.min_pm_word_len = cfg0.min_pm_word_len;
			}
		}
		// ...THEN snapshot: expand_rep_subsig and the shape guard read
		// this threaded cfg (clam_db.rs:2115), not the global.  The
		// write-then-snapshot order is the flag-handling soundness.
		let cfg = default_clamav_cfg();

		let (build_dir, sig_path, tmp_guard):
			(String, String, Option<TmpConfigDir>) = if perc >= 100 {
			(src_dir.clone(),
				format!("{}/{}", src_dir, sig_file_name), None)
		} else {
			let tmp = format!("/tmp/bora/effective_adv_{}_{}",
				std::process::id(), name);
			let n_sigs = read_lines_nonblank(
				&format!("{}/{}", src_dir, sig_file_name)).len();
			let sig_path = create_smaller_config(src_dir,
				sig_file_name, count_of(n_sigs, perc as f64), &tmp);
			(tmp.clone(), sig_path,
				Some(TmpConfigDir(PathBuf::from(tmp))))
		};
		let _tmp_guard = tmp_guard;

		let mut vlog = vec![];
		// (false, false): built in RAM, nothing read from or written
		// to data/cache -- the cache-dir string below is inert.
		let db = ClamavDB::<Fr>::build_or_load(&cfg, &sig_path,
			&format!("{}/main_dfa.dat", build_dir),
			&format!("{}/needs_ised.dat", build_dir),
			&format!("{}/needs_ised_igc.dat", build_dir),
			&mut vlog, "effective_adv_unused", false, false)
			.expect(&format!("build {} db", name));
		let total_sigs = db.vec_sigs.len();

		// scan corpus: concat the lists, then the same perc thins it
		// (strided so the kept subset spans the corpus; >= 1 kept)
		let mut paths: Vec<String> = scan_lists.iter()
			.flat_map(|l| read_path_list(l)).collect();
		if perc < 100 {
			let k = (100 + perc - 1) / perc.max(1);
			paths = paths.into_iter().enumerate()
				.filter(|(i, _)| i % k == 0)
				.map(|(_, p)| p).collect();
		}
		let recs: Vec<FailDischargeRecord> = paths.par_iter()
			.map(|fp| {
				let nib = utils::os::read_nibbles(
					&format!("{}/{}", proot, fp));
				let (fdr, _wi) = quick_discharge_file_by_crit_bag_pm(
					fp, &nib, &db.vec_sigs,
					&db.vec_sigs_no_critical_pat, &db.map_crit_pat,
					&db.map_crit_pat_igc, &db.dfa_crit,
					&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
					&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
					&db.sig_to_id, *max_word_len, *max_word_len);
				fdr
			}).collect();
		report.push_str(&fmt_tier_block(
			&format!("Data for {}", name), &recs, total_sigs));
		kept.push((name.clone(), recs, total_sigs));
	}

	// Filesize re-buckets (fig 9b): Mal and Dlp, same records, split
	// by flen = floor(log2 bytes)+1 as the legacy fn.
	for (name, recs, total_sigs) in &kept {
		if name != "Mal" && name != "Dlp" { continue; }
		report.push_str(&format!(
			"######## Filesize data for {} ########\n", name));
		let mut by_flen: std::collections::BTreeMap<usize,
			Vec<FailDischargeRecord>> =
			std::collections::BTreeMap::new();
		for r in recs {
			by_flen.entry(r.flen).or_default().push(r.clone());
		}
		for (flen, bucket) in &by_flen {
			let lo = if *flen == 0 { 0 } else { 1usize << (flen - 1) };
			let hi = 1usize << flen;
			report.push_str(&fmt_tier_block(
				&format!("Filesize data for {} -- flen={} \
({}..{} bytes)", name, flen, lo, hi),
				bucket, *total_sigs));
		}
	}
	report.push_str(
		"#################### END EFFECTIVENESS REPORT \
####################\n");
	println!("{}", report);
	fs::write(dest_path, &report).unwrap_or_else(|e| panic!(
		"bora_data_driver: write {}: {}", dest_path, e));
}

pub const USAGE: &str = "bora_cli: backend of \
	scripts/PAPER_DATA.py -- run that driver instead; \
	direct invocation is for debugging only.\n\
	usage: bora_cli <subcommand>\n \
	 lkup <perc> <dest_path>\n \
	 effective <perc> <dest_path>\n \
	 full_dlp <perc_db> <perc_samples> <num_circs> <num_jobs> \
	<numa_num> <part_id> <dry 0|1> <ladder_only 0|1>\n \
	   (dry=1 also drops the hab22 cover check)\n \
	 full_dna <same 8 args as full_dlp>\n \
	 full_clam <same 8 args as full_dlp>\n \
	 scale_dlp <corpus_idx> <c1,c2,...> <dry 0|1>\n \
	 scale_clam <corpus_idx> <c1,c2,...> <dry 0|1>";

/// Parsed CLI command for examples/bora_cli.rs.
#[derive(Debug, PartialEq)]
pub enum Cmd {
	Lkup { perc: usize, dest_path: String },
	Effective { perc: usize, dest_path: String },
	FullDlp { perc_db: f64, perc_samples: f64, num_circs: usize,
		num_jobs: usize, numa_num: usize, part_id: usize,
		b_dry_run: bool, b_ladder_only: bool },
	FullDna { perc_db: f64, perc_samples: f64, num_circs: usize,
		num_jobs: usize, numa_num: usize, part_id: usize,
		b_dry_run: bool, b_ladder_only: bool },
	FullClam { perc_db: f64, perc_samples: f64, num_circs: usize,
		num_jobs: usize, numa_num: usize, part_id: usize,
		b_dry_run: bool, b_ladder_only: bool },
	ScaleDlp { corpus_idx: usize, vec_count: Vec<usize>,
		b_dry_run: bool },
	ScaleClam { corpus_idx: usize, vec_count: Vec<usize>,
		b_dry_run: bool },
}

fn arg_usize(args: &[String], i: usize, name: &str) -> usize {
	args[i].parse().unwrap_or_else(|_| panic!(
		"bora_data_driver: <{}> not a usize: {:?}\n{}",
		name, args[i], USAGE))
}

fn arg_f64(args: &[String], i: usize, name: &str) -> f64 {
	args[i].parse().unwrap_or_else(|_| panic!(
		"bora_data_driver: <{}> not a number: {:?}\n{}",
		name, args[i], USAGE))
}

fn arg_counts(args: &[String], i: usize) -> Vec<usize> {
	args[i].split(',').map(|t| t.parse().unwrap_or_else(|_| panic!(
		"bora_data_driver: count not a usize: {:?}\n{}", t, USAGE)))
		.collect()
}

fn arg_bool(args: &[String], i: usize, name: &str) -> bool {
	match args[i].as_str() {
		"0" => false,
		"1" => true,
		other => panic!(
			"bora_data_driver: <{}> must be 0|1, got {:?}\n{}",
			name, other, USAGE),
	}
}

/// The shared 8-arg tail of the full_* subcommands. Panics with
/// USAGE on wrong arity, out-of-range percs, zero counts, or
/// part_id >= numa_num.
fn parse_full8(args: &[String], sub: &str)
	-> (f64, f64, usize, usize, usize, usize, bool, bool) {
	assert!(args.len() == 9,
		"bora_data_driver: {} takes 8 args, got {}\n{}",
		sub, args.len() - 1, USAGE);
	let perc_db = arg_f64(args, 1, "perc_db");
	let perc_samples = arg_f64(args, 2, "perc_samples");
	let num_circs = arg_usize(args, 3, "num_circs");
	let num_jobs = arg_usize(args, 4, "num_jobs");
	let numa_num = arg_usize(args, 5, "numa_num");
	let part_id = arg_usize(args, 6, "part_id");
	assert!(perc_db > 0.0 && perc_db <= 100.0
		&& perc_samples > 0.0 && perc_samples <= 100.0,
		"bora_data_driver: {} percs must be in (0, 100] \
		 (perc_db {} perc_samples {})", sub, perc_db, perc_samples);
	assert!(num_circs >= 1 && num_jobs >= 1 && numa_num >= 1,
		"bora_data_driver: {} counts must be >= 1 \
		 (num_circs {} num_jobs {} numa_num {})",
		sub, num_circs, num_jobs, numa_num);
	assert!(part_id < numa_num,
		"bora_data_driver: part_id {} >= numa_num {}",
		part_id, numa_num);
	(perc_db, perc_samples, num_circs, num_jobs, numa_num, part_id,
		arg_bool(args, 7, "dry"), arg_bool(args, 8, "ladder_only"))
}

/// argv[1..] -> Cmd. Panics with a usage line on unknown subcommand,
/// wrong arity, non-integer, a zero that has no meaning (percs,
/// circs, jobs, numa), or part_id >= numa_num.
pub fn parse_args(args: &[String]) -> Cmd {
	match args.first().map(|s| s.as_str()) {
		Some("lkup") => {
			assert!(args.len() == 3,
				"bora_data_driver: lkup takes 2 args, got {}\n{}",
				args.len() - 1, USAGE);
			Cmd::Lkup { perc: arg_usize(args, 1, "perc"),
				dest_path: args[2].clone() }
		}
		Some("effective") => {
			assert!(args.len() == 3,
				"bora_data_driver: effective takes 2 args, got {}\n{}",
				args.len() - 1, USAGE);
			Cmd::Effective { perc: arg_usize(args, 1, "perc"),
				dest_path: args[2].clone() }
		}
		Some("full_dlp") => {
			let (perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_dry_run, b_ladder_only) =
				parse_full8(args, "full_dlp");
			Cmd::FullDlp { perc_db, perc_samples, num_circs,
				num_jobs, numa_num, part_id, b_dry_run,
				b_ladder_only }
		}
		Some("full_dna") => {
			let (perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_dry_run, b_ladder_only) =
				parse_full8(args, "full_dna");
			Cmd::FullDna { perc_db, perc_samples, num_circs,
				num_jobs, numa_num, part_id, b_dry_run,
				b_ladder_only }
		}
		Some("full_clam") => {
			let (perc_db, perc_samples, num_circs, num_jobs,
				numa_num, part_id, b_dry_run, b_ladder_only) =
				parse_full8(args, "full_clam");
			Cmd::FullClam { perc_db, perc_samples, num_circs,
				num_jobs, numa_num, part_id, b_dry_run,
				b_ladder_only }
		}
		Some("scale_dlp") => {
			assert!(args.len() == 4,
				"bora_data_driver: scale_dlp takes 3 args, got {}\n{}",
				args.len() - 1, USAGE);
			Cmd::ScaleDlp {
				corpus_idx: arg_usize(args, 1, "corpus_idx"),
				vec_count: arg_counts(args, 2),
				b_dry_run: arg_bool(args, 3, "dry") }
		}
		Some("scale_clam") => {
			assert!(args.len() == 4,
				"bora_data_driver: scale_clam takes 3 args, \
				 got {}\n{}", args.len() - 1, USAGE);
			Cmd::ScaleClam {
				corpus_idx: arg_usize(args, 1, "corpus_idx"),
				vec_count: arg_counts(args, 2),
				b_dry_run: arg_bool(args, 3, "dry") }
		}
		other => panic!(
			"bora_data_driver: unknown subcommand {:?}\n{}",
			other, USAGE),
	}
}

#[cfg(test)]
pub mod tests_bora_data_driver {
	use super::*;
	use std::sync::atomic::{AtomicUsize, Ordering};

	static COUNTER: AtomicUsize = AtomicUsize::new(0);

	/// Serializes tests that mutate the process-wide GlobalConfig.
	fn cfg_lock() -> std::sync::MutexGuard<'static, ()> {
		static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
		LOCK.lock().unwrap_or_else(|e| e.into_inner())
	}

	/// Sets b_scale_catch_caperr for a retry test; restores on drop,
	/// including on the should_panic unwinds.
	struct CatchFlag;
	impl CatchFlag {
		fn on() -> CatchFlag {
			get_global_config().b_scale_catch_caperr = true;
			CatchFlag
		}
	}
	impl Drop for CatchFlag {
		fn drop(&mut self) {
			get_global_config().b_scale_catch_caperr = false;
		}
	}

	/// Minimal valid CapParams for the retry tests (values arbitrary;
	/// only the bumped fields are asserted).
	fn tiny_caps() -> CapParams {
		CapParams {
			cp_basis_unique_states: 2, cp_subsigs: 2, cp_avg_pats: 1,
			subsigs: 2, avg_pats_per_subsig: 1,
			avg_active_pats_per_subsig: 1, basis_pats_in_trace: 4,
			perc_pats_expansion_rate: 16, prod_pats_expansion: 0,
			qm_real_rows: 2, sigs_sed: 1, perc_comp_subsigs: 100,
			basis_unique_states: 2, basis_acc_states: 2,
			subsigs_igc: 1, avg_active_pats_per_subsig_igc: 1,
			basis_pats_in_trace_igc: 8,
			perc_pats_expansion_rate_igc: 64,
			prod_pats_expansion_igc: 0, qm_real_rows_igc: 2,
			basis_acc_states_igc: 2, basis_unique_states_igc: 4,
			dfa_sigs: 0, dfa_subsigs: 0, aggr_needs_subsigs: 0,
			max_word_len: 64, acdfa_state_part_bits: 4,
			levels: vec![],
		}
	}

	/// Generous P_max for the v5 sizing tests: every measured axis has
	/// headroom, so any clamp that fires means measurement, not P_max.
	fn big_pmax_fixture() -> CapParams {
		CapParams {
			cp_basis_unique_states: 9999, cp_subsigs: 2001,
			cp_avg_pats: 4, subsigs: 2001, avg_pats_per_subsig: 4,
			avg_active_pats_per_subsig: 8, basis_pats_in_trace: 9999,
			perc_pats_expansion_rate: 64,
			prod_pats_expansion: 16_000_000, qm_real_rows: 20000,
			sigs_sed: 16, perc_comp_subsigs: 100,
			basis_unique_states: 9999, basis_acc_states: 9999,
			subsigs_igc: 1, avg_active_pats_per_subsig_igc: 1,
			basis_pats_in_trace_igc: 8,
			perc_pats_expansion_rate_igc: 64,
			prod_pats_expansion_igc: 0, qm_real_rows_igc: 20000,
			basis_acc_states_igc: 2, basis_unique_states_igc: 4,
			dfa_sigs: 0, dfa_subsigs: 0, aggr_needs_subsigs: 0,
			max_word_len: 64, acdfa_state_part_bits: 4,
			levels: vec![],
		}
	}

	fn fresh_tmp_dir(tag: &str) -> PathBuf {
		let n = COUNTER.fetch_add(1, Ordering::SeqCst);
		let dir = std::env::temp_dir()
			.join(format!("bora_data_driver_test_{}_{}_{}",
				std::process::id(), tag, n));
		fs::create_dir_all(&dir).unwrap();
		dir
	}

	/// Writes a tiny synthetic config dir: n_sigs sigs named sig0..N-1,
	/// each ";"-delimited like a real ClamAV signature line; needs_ised
	/// / needs_ised_igc list every 3rd sig; needs_dfa lists every 2nd.
	fn write_fixture(dir: &Path, n_sigs: usize, sig_file_name: &str,
		with_fanout: bool) {
		fs::create_dir_all(dir).unwrap();
		let sig_lines: Vec<String> = (0..n_sigs)
			.map(|i| format!("sig{};Engine:1-255,Target:1;0;deadbeef", i))
			.collect();
		fs::write(dir.join(sig_file_name), sig_lines.join("\n")).unwrap();

		let dfa: Vec<String> = (0..n_sigs).step_by(2)
			.map(|i| format!("sig{}", i)).collect();
		fs::write(dir.join("main_dfa.dat"), dfa.join("\n")).unwrap();

		let ised: Vec<String> = (0..n_sigs).step_by(3)
			.map(|i| format!("sig{}", i)).collect();
		fs::write(dir.join("needs_ised.dat"), ised.join("\n")).unwrap();
		fs::write(dir.join("needs_ised_igc.dat"), ised.join("\n")).unwrap();

		if with_fanout {
			fs::write(dir.join("main_fanout.dat"), "sig").unwrap();
		}
	}

	fn read_names(path: &Path) -> HashSet<String> {
		if !path.exists() {
			return HashSet::new();
		}
		fs::read_to_string(path).unwrap().lines()
			.filter(|s| !s.trim().is_empty())
			.map(|s| s.trim().to_string()).collect()
	}

	#[test]
	fn perc_100_keeps_every_sig() {
		let src = fresh_tmp_dir("p100_src");
		let dst = fresh_tmp_dir("p100_dst");
		write_fixture(&src, 20, "main.dat", false);
		create_smaller_config(src.to_str().unwrap(), "main.dat",
			count_of(20, 100.0), dst.to_str().unwrap());
		let src_names = read_names(&src.join("main.dat"))
			.iter().map(|l| l.split(';').next().unwrap().to_string())
			.collect::<HashSet<_>>();
		let dst_names = read_names(&dst.join("main.dat"))
			.iter().map(|l| l.split(';').next().unwrap().to_string())
			.collect::<HashSet<_>>();
		assert_eq!(src_names, dst_names);
	}

	#[test]
	fn deterministic_across_repeated_calls() {
		let src = fresh_tmp_dir("det_src");
		write_fixture(&src, 37, "main.dat", false);
		let dst1 = fresh_tmp_dir("det_dst1");
		let dst2 = fresh_tmp_dir("det_dst2");
		create_smaller_config(src.to_str().unwrap(), "main.dat",
			count_of(37, 30.0), dst1.to_str().unwrap());
		create_smaller_config(src.to_str().unwrap(), "main.dat",
			count_of(37, 30.0), dst2.to_str().unwrap());
		let c1 = fs::read_to_string(dst1.join("main.dat")).unwrap();
		let c2 = fs::read_to_string(dst2.join("main.dat")).unwrap();
		assert_eq!(c1, c2);
	}

	#[test]
	fn ised_names_are_subset_of_thinned_sigs() {
		let src = fresh_tmp_dir("subset_src");
		let dst = fresh_tmp_dir("subset_dst");
		write_fixture(&src, 50, "main.dat", true);
		create_smaller_config(src.to_str().unwrap(), "main.dat",
			count_of(50, 20.0), dst.to_str().unwrap());

		let sig_names: HashSet<String> =
			read_names(&dst.join("main.dat")).iter()
			.map(|l| l.split(';').next().unwrap().to_string()).collect();
		for f in ["needs_ised.dat", "needs_ised_igc.dat", "main_dfa.dat"] {
			for n in read_names(&dst.join(f)) {
				assert!(sig_names.contains(&n),
					"{}: {} not in thinned sig set", f, n);
			}
		}
		assert!(dst.join("main_fanout.dat").exists());
	}

	#[test]
	fn non_main_dat_sig_filename_is_honored() {
		let src = fresh_tmp_dir("dlpname_src");
		let dst = fresh_tmp_dir("dlpname_dst");
		write_fixture(&src, 10, "main_data_dlp_internationl.dat", false);
		let out = create_smaller_config(src.to_str().unwrap(),
			"main_data_dlp_internationl.dat", count_of(10, 50.0),
			dst.to_str().unwrap());
		assert!(out.ends_with("main_data_dlp_internationl.dat"));
		assert!(Path::new(&out).exists());
	}

	#[test]
	#[should_panic]
	fn missing_needs_ised_panics() {
		let src = fresh_tmp_dir("missing_src");
		let dst = fresh_tmp_dir("missing_dst");
		fs::create_dir_all(&src).unwrap();
		fs::write(src.join("main.dat"), "sig0;Engine:1-255,Target:1;0;ab")
			.unwrap();
		fs::write(src.join("main_dfa.dat"), "sig0").unwrap();
		// needs_ised.dat / needs_ised_igc.dat deliberately absent.
		create_smaller_config(src.to_str().unwrap(), "main.dat", 1,
			dst.to_str().unwrap());
	}

	/// A101: the plan dir literal lives in exactly one place, and can
	/// never point at the shared /tmp/bora framework dir itself.
	#[test]
	fn test_a101_plan_dir() {
		let d = plan_dir("dlp", 0);
		assert_eq!(d, "/tmp/bora/dlp_neo_p0");
		assert!(Path::new(&d).is_absolute());
		assert!(d.starts_with("/tmp/bora/") && d.len() > "/tmp/bora/".len(),
			"plan dir must be a strict subdir of /tmp/bora: {}", d);
		assert_eq!(plan_dir("clam", 1), "/tmp/bora/clam_neo_p1");
	}

	/// A101: the recomputed split must reproduce the committed jobs8/
	/// manifests bin-for-bin -- this is what licenses M102 to recompute
	/// the split instead of shipping job_i.dat files.
	#[test]
	fn test_a101_split_matches_jobs8() {
		let cd = "data/paper_data/dlp/cfg";
		let t = std::time::Instant::now();
		let all = read_path_list(
			&format!("{}/jobs/final_enron_list.txt.tgz", cd));
		assert!(!all.is_empty(), "empty corpus list");
		let n = all.len();
		let bins = split_paths_balanced(all, 8);
		println!("A101 split: {} files -> 8 bins in {:?}", n, t.elapsed());
		let mut total = 0;
		for i in 0..8 {
			let want = read_path_list(
				&format!("{}/jobs/jobs8/job_{}.dat", cd, i));
			assert!(!want.is_empty(), "committed job_{}.dat is empty", i);
			assert_eq!(bins[i], want, "bin {} differs from job_{}.dat", i, i);
			total += want.len();
		}
		assert_eq!(total, n, "bins do not cover the corpus exactly");
	}

	/// A101: manifest writer -- names carry the global job id, missing
	/// dirs are created, and a re-plan overwrites in place.
	#[test]
	fn test_a101_write_job_manifests() {
		let dir = fresh_tmp_dir("manifests").join("jobs");
		let jd = dir.to_str().unwrap().to_string();
		assert!(!dir.exists(), "test precondition: jobs dir absent");
		let bins = vec![
			vec!["a/1".to_string(), "a/2".to_string()],
			vec![],
			vec!["c/3".to_string()],
		];
		let paths = write_job_manifests(&jd, &bins);
		assert_eq!(paths.len(), 3);
		for (i, p) in paths.iter().enumerate() {
			assert!(Path::new(p).is_absolute());
			assert_eq!(*p, format!("{}/job_{}.dat", jd, i));
			assert_eq!(fs::read_to_string(p).unwrap(), bins[i].join("\n"));
		}
		// re-plan with FEWER jobs: stale job_2.dat must be gone, and an
		// unrelated neighbour in the plan dir must survive.
		fs::write(format!("{}/ladder.json", jd), "{}").unwrap();
		let bins2 = vec![vec!["z/9".to_string()], vec![]];
		let again = write_job_manifests(&jd, &bins2);
		assert_eq!(again.len(), 2);
		assert_eq!(fs::read_to_string(&again[0]).unwrap(), "z/9");
		assert!(!Path::new(&paths[2]).exists(), "stale job_2.dat kept");
		assert!(Path::new(&format!("{}/ladder.json", jd)).exists(),
			"unrelated plan file deleted");
	}

	/// A102: the DLP const points at real files and pins legacy
	/// full_dlp()'s configuration field for field.
	#[test]
	fn test_a102_dlp_const_sane() {
		let proot = utils::os::proj_root();
		let abs = |p: &str| format!("{}/{}", proot, p);

		// 1. every path the pipeline will open exists on disk.
		assert!(Path::new(&abs(DLP.config_dir)).is_dir(),
			"config_dir missing: {}", DLP.config_dir);
		for f in [DLP.sig_file, "main_dfa.dat", "needs_ised.dat",
			"needs_ised_igc.dat"] {
			let p = abs(&format!("{}/{}", DLP.config_dir, f));
			assert!(Path::new(&p).is_file(), "missing {}", p);
		}
		for s in DLP.master_sources.iter().chain(DLP.scale_sources) {
			assert!(Path::new(&abs(s)).is_file(), "missing {}", s);
		}

		// 2. shape.
		assert_eq!(DLP.name, "dlp");
		assert_eq!(DLP.scale_sources.len(), 2);
		assert!(!DLP.master_sources.is_empty());
		assert!(DLP.vec_decrease_level.is_empty()); // aggressive arm

		// 3. neo-own cache: a neo run can never write legacy's dir.
		assert_eq!(DLP.db_cache_dir, "dlp_neo");
		assert_eq!(plan_dir(DLP.name, 0), "/tmp/bora/dlp_neo_p0");

		// 4. legacy full_dlp() parity, field by field.
		assert_eq!(DLP.chunk_len, 64);
		assert_eq!(DLP.range2_bit, 25);
		assert_eq!(DLP.fanout_cap, 100);
		assert!(DLP.b_aggressive);
		assert!(DLP.b_check_lkup,
			"deliberate departure from legacy full_dlp");
		assert_eq!(DLP.n_par_snark, 1);
		assert_eq!(DLP.n_par_snark_cp, 1);
		assert_eq!(DLP.min_subsigs, 1);
		assert_eq!(DLP.min_basis_unique_states, 2);
		assert_eq!(DLP.min_basis_acc_states, 2);
		assert_eq!(DLP.min_basis_pats_in_trace, 4);
		assert_eq!(DLP.min_avg_pats_per_subsig, 1);
		assert_eq!(DLP.min_dfa_sigs, 0);
		assert_eq!(DLP.min_dfa_subsigs, 0);
	}

	/// A103: fixed_perm is byte-identical to zkp_driver's two private
	/// copies. Goldens generated by an independent Python transcription
	/// of zkp_driver.rs:7295-7307, so a mis-transcription here fails.
	#[test]
	fn test_a103_fixed_perm_matches_legacy() {
		assert_eq!(fixed_perm(8, SCALE_PERM_SEED),
			vec![3, 4, 6, 2, 5, 7, 0, 1]);
		assert_eq!(fixed_perm(12, SCALE_PERM_SEED),
			vec![11, 6, 4, 0, 9, 3, 7, 2, 8, 10, 1, 5]);
		assert_eq!(fixed_perm(0, SCALE_PERM_SEED), Vec::<usize>::new());
		assert_eq!(fixed_perm(1, SCALE_PERM_SEED), vec![0]);
	}

	/// A103: count >= n reproduces the source exactly -- the property
	/// that keeps the 100% lkup/full runs byte-identical to T13's.
	#[test]
	fn test_a103_subset_identity_at_full() {
		let all: Vec<usize> = (0..40).collect();
		assert_eq!(subset(40, 40), all);
		assert_eq!(subset(40, 41), all);
		assert_eq!(subset(40, usize::MAX), all);
		assert_eq!(subset(0, 5), Vec::<usize>::new());
	}

	/// A103: pinned 0, sorted, exact length, and counts NEST.
	#[test]
	fn test_a103_subset_pins_sorts_and_nests() {
		assert_eq!(subset(9, 1), vec![0]);
		assert_eq!(subset(9, 4), vec![0, 4, 5, 7]);
		assert_eq!(subset(9, 5), vec![0, 3, 4, 5, 7]);
		let mut prev: Vec<usize> = vec![];
		for c in 1..=200usize {
			let s = subset(200, c);
			assert_eq!(s.len(), c);
			assert_eq!(s[0], 0, "index 0 must be pinned");
			assert!(s.windows(2).all(|w| w[0] < w[1]), "sorted, distinct");
			assert!(prev.iter().all(|p| s.contains(p)), "counts must nest");
			assert_eq!(subset(200, c), s, "deterministic");
			prev = s;
		}
	}

	/// A103: subset(n, cnt+1) is exactly legacy DLP scale's rule set
	/// ([pinned] + perm.take(cnt), zkp_driver.rs:7620) at every count.
	#[test]
	fn test_a103_subset_matches_legacy_dlp_scale() {
		let n = 9861;                       // DLP's real rule-line count
		let perm = fixed_perm(n - 1, SCALE_PERM_SEED);
		for cnt in [1usize, 986, 4930, 9860] {
			let mut legacy: Vec<usize> = vec![0];
			legacy.extend(perm.iter().take(cnt).map(|&i| i + 1));
			legacy.sort();
			assert_eq!(subset(n, cnt + 1), legacy,
				"neo count {} must equal legacy cnt {}", cnt + 1, cnt);
		}
	}

	#[test]
	fn test_a103_count_of() {
		assert_eq!(count_of(9861, 100.0), 9861);
		assert_eq!(count_of(9861, 10.0), 987);
		assert_eq!(count_of(9861, 1.0), 99);
		assert_eq!(count_of(9861, 0.0), 1);       // documented floor
		assert_eq!(count_of(9861, 200.0), 9861);  // capped at n
		assert_eq!(count_of(10, 25.0), 3);        // ceil, not floor
		assert_eq!(count_of(1, 100.0), 1);
		assert_eq!(count_of(9861, 0.05), 5);      // ceil(4.93)
		assert_eq!(count_of(504854, 0.05), 253);  // the 0.05% smoke
		assert_eq!(count_of(504854, 0.1), 505);
	}

	#[test]
	#[should_panic(expected = "count_of on an empty set")]
	fn test_a103_count_of_empty_panics() {
		count_of(0, 50.0);
	}

	#[test]
	fn test_a103_config_dir_for() {
		assert_eq!(config_dir_for(&DLP, 9861, 9861, 0), DLP.config_dir);
		assert_eq!(config_dir_for(&DLP, 99, 9861, 1),
			"/tmp/bora/dlp_neo_p1/config");
	}

	#[test]
	fn test_a103_part_role() {
		let r = part_role(0, 1, 8);
		assert!(r.b_proves && !r.b_wait_snark);
		assert_eq!(r.jobs, 0..8);
		let r0 = part_role(0, 2, 8);
		assert!(!r0.b_proves && !r0.b_wait_snark);
		assert_eq!(r0.jobs, 0..4);
		let r1 = part_role(1, 2, 8);
		assert!(r1.b_proves && r1.b_wait_snark);
		assert_eq!(r1.jobs, 4..8);
		assert_eq!(part_role(0, 4, 8).jobs, 0..2);
		assert_eq!(part_role(3, 4, 8).jobs, 6..8);
	}

	#[test]
	#[should_panic(expected = "part_id 2 >= numa_num 2")]
	fn test_a103_part_role_rejects_part_id() {
		part_role(2, 2, 8);
	}

	#[test]
	#[should_panic(expected = "not a multiple of")]
	fn test_a103_part_role_rejects_indivisible() {
		part_role(0, 3, 8);
	}

	/// A103: sampling + balanced split over a real 20-path master, so
	/// the zero-size guard runs against files that actually exist.
	#[test]
	fn test_a103_plan_corpus_from() {
		let master: Vec<String> = read_path_list(DLP.master_sources[0])
			.into_iter().take(20).collect();
		assert_eq!(master.len(), 20);
		let bins = plan_corpus_from(&master, 50.0, 4);
		assert_eq!(bins.len(), 4);
		let flat: Vec<&String> = bins.iter().flatten().collect();
		assert_eq!(flat.len(), 10);             // count_of(20, 50)
		let kept: HashSet<&String> = flat.into_iter().collect();
		assert_eq!(kept.len(), 10, "no duplicates across bins");
		assert!(kept.contains(&master[0]), "file 0 pinned");
		assert!(kept.iter().all(|p| master.contains(p)));
		assert_eq!(plan_corpus_from(&master, 50.0, 4), bins);
	}

	#[test]
	#[should_panic(expected = "zero total size")]
	fn test_a103_plan_corpus_from_rejects_missing_files() {
		let ghost: Vec<String> =
			(0..4).map(|i| format!("data/no_such_file_{}", i)).collect();
		plan_corpus_from(&ghost, 100.0, 2);
	}

	/// B101: every field apply_spec_config names, over all three part
	/// roles. ONE test on purpose -- GlobalConfig is process-wide, so
	/// two config tests running on parallel threads would race.
	#[test]
	fn test_b101_apply_spec_config() {
		use utils::consts::read_global_config;
		let _g = cfg_lock();

		// Poison every field first with the legacy/opposite value, so
		// each assert proves apply_spec_config WROTE it rather than
		// finding it already right by default.
		{
			let mut g = get_global_config();
			g.clamav_cfg.b_use_discharge_neo = false;
			g.clamav_cfg.b_aggressive_sde_for_rep = false;
			g.clamav_cfg.sde_rep_fanout_cap = 7;
			g.clamav_cfg.min_pm_word_len = 99;
			g.neo_wrap_keys = 7;
			g.range2_bit = 3;
			g.min_subsigs = 99;
			g.min_basis_unique_states = 99;
			g.min_basis_acc_states = 99;
			g.min_basis_pats_in_trace = 99;
			g.min_avg_pats_per_subsig = 99;
			g.min_dfa_sigs = 99;
			g.min_dfa_subsigs = 99;
			g.n_par_snark = 99;
			g.n_par_snark_cp = 99;
			g.n_par_batch_claim = 99;
			g.b_light_test = true;
			g.b_read_cache = false;
			g.b_read_snark_cache = true;
			g.b_write_snark_cache = true;
			g.b_dryrun_after_capcheck = true;   // would no-op the fold
			g.b_scale_catch_caperr = true;      // would kill fail-fast
			g.b_check_lkup = !DLP.b_check_lkup; // must come from spec
			g.log_level = 99;               // must come from spec
			g.b_pin_lkup_share = true;      // the legacy pin
			g.perc_lkup_share = 42;         // a stale ratchet value
			g.snark_wait_flag = Some("/tmp/stale".to_string());
		}

		// numa 1: the single part folds AND proves, and waits on nobody.
		apply_spec_config(&DLP, false, &part_role(0, 1, 8));
		let c = read_global_config();
		assert!(c.clamav_cfg.b_use_discharge_neo, "neo is ALWAYS on");
		assert_eq!(c.neo_wrap_keys, 0, "0 = auto-derive");
		assert!(c.clamav_cfg.b_aggressive_sde_for_rep);
		assert_eq!(c.clamav_cfg.sde_rep_fanout_cap, DLP.fanout_cap);
		assert_eq!(c.clamav_cfg.min_pm_word_len, DLP.min_pm_word_len);
		assert_eq!(c.range2_bit, DLP.range2_bit);
		assert_eq!(c.min_subsigs, DLP.min_subsigs);
		assert_eq!(c.min_basis_unique_states, DLP.min_basis_unique_states);
		assert_eq!(c.min_basis_acc_states, DLP.min_basis_acc_states);
		assert_eq!(c.min_basis_pats_in_trace, DLP.min_basis_pats_in_trace);
		assert_eq!(c.min_avg_pats_per_subsig, DLP.min_avg_pats_per_subsig);
		assert_eq!(c.min_dfa_sigs, DLP.min_dfa_sigs);
		assert_eq!(c.min_dfa_subsigs, DLP.min_dfa_subsigs);
		assert_eq!(c.n_par_snark, DLP.n_par_snark);
		assert_eq!(c.n_par_snark_cp, DLP.n_par_snark_cp);
		// spec-owned since M103 (was the hardcoded default-1 rule).
		assert_eq!(c.n_par_batch_claim, DLP.n_par_batch_claim);
		assert_eq!(c.log_level, DLP.log_level, "from the spec");
		assert_eq!(c.log_level, utils::logger::LOG3);
		assert_eq!(scale_spec_clone(&DLP).log_level,
			utils::logger::LOG4, "scale flips the probe trace on");
		assert_eq!(c.b_check_lkup, DLP.b_check_lkup, "from the spec");
		assert!(!c.b_light_test,
			"prover part at b_light=false stays heavy");
		assert!(!c.b_folding_only, "numa 1: the one part proves");
		assert!(c.b_one_proof);
		assert_eq!(c.snark_wait_flag, None, "nobody to wait for");
		assert!(c.b_read_cache, "the fold reloads the DB from cache");
		assert!(!c.b_read_snark_cache);
		assert!(!c.b_write_snark_cache);
		assert!(!c.b_dryrun_after_capcheck);
		assert!(!c.b_scale_catch_caperr,
			"a stale scale catch flag must not survive into a run");
		assert!(!c.b_pin_lkup_share, "the legacy pin must NOT be copied");
		assert_eq!(c.perc_lkup_share, 1, "ratchet floor, not the stale 42");
		drop(c);

		// numa 2 part 0: folds only, does not wait (it IS the folder).
		// b_light=false on purpose: the fold-only part must be FORCED
		// light (legacy's ZKR_DLP_FOLD_ONLY coupling).
		apply_spec_config(&DLP, false, &part_role(0, 2, 8));
		let c = read_global_config();
		assert!(c.b_light_test, "fold-only part is forced light");
		assert!(c.b_folding_only);
		assert!(!c.b_one_proof);
		assert_eq!(c.snark_wait_flag, None);
		drop(c);

		// numa 2 part 1: proves, and gates on the flag Python touches.
		apply_spec_config(&DLP, false, &part_role(1, 2, 8));
		let c = read_global_config();
		assert!(!c.b_light_test, "the proving part stays heavy");
		assert!(!c.b_folding_only);
		assert!(c.b_one_proof);
		assert_eq!(c.snark_wait_flag,
			Some("/tmp/snark_start/flag".to_string()),
			"MUST match PAPER_DATA.py's FLAG");
		drop(c);

		// DNA (M103): the non-aggr spec's distinct knobs all land;
		// the DLP apply above is the poison for every one of them.
		apply_spec_config(&DNA, true, &part_role(0, 1, 1));
		let c = read_global_config();
		assert!(!c.clamav_cfg.b_aggressive_sde_for_rep);
		assert_eq!(c.clamav_cfg.min_pm_word_len, 4);
		assert_eq!(c.clamav_cfg.sde_rep_fanout_cap, 127);
		assert_eq!(c.n_par_batch_claim, 8);
		assert!(!c.b_check_lkup, "user decision: check stays off");
		assert_eq!(c.range2_bit, 27);
		assert_eq!(c.min_subsigs, 64);
		assert_eq!(c.min_dfa_sigs, 2);
	}

	#[test]
	fn test_b102_zero_word_nibbles() {
		let mw = 64;
		let nib = zero_word_nibbles(mw);
		assert_eq!(nib.len(), mw * 62);
		assert!(nib.iter().all(|&n| n < 16));
		let fnib: Vec<Fr> = nib.iter()
			.map(|x| Fr::from(*x as u32)).collect();
		// packs to EXACTLY chunk_len Fr, the word the fold preprocesses
		assert_eq!(utils::data::pack_nibbles(&fnib).len(), mw);
	}

	/// B102 kernel: 2-rule (alphabet pin + 1) DLP DB + one real email,
	/// pieces then end-to-end. 2 = legacy scale's SMALLEST tuned DB
	/// (cnt=1 writes pin+1 rules); 1 rule is outside the tuner's domain
	/// (zero SED demand underflows gen_fwdprf_valid_prf). Structure
	/// asserts only: rung VALUES belong to the tuner (T506 moves
	/// qm_real_rows; never pin it).
	#[test]
	fn test_b102_build_and_tune_tiny() {
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		// redirected clone: never touch the live dlp_neo dirs.
		let mut spec = DLP.clone();
		spec.name = "dlp_test";            // /tmp/bora/dlp_test_neo_p0
		spec.db_cache_dir = "dlp_test_neo";
		// isolate the kernel from the check axis (scale's clone does
		// the same); the check-on path is C103/D102's E2E territory.
		spec.b_check_lkup = false;
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		// rule 0 must be the all-16-nibble alphabet sig: it is the ONE
		// rule subset(n,1) keeps; the DB is degenerate without it.
		let src_dir = format!("{}/{}", proot, spec.config_dir);
		let sig_lines = read_lines_nonblank(
			&format!("{}/{}", src_dir, spec.sig_file));
		assert!(sig_lines[0].starts_with("Win.Alphabet"),
			"DLP rule 0 must be the alphabet pin");
		apply_spec_config(&spec, true, &part_role(0, 1, 1));
		// one real 805 B email (the dense scale corpus), one bin.
		let bins = vec![vec![DLP.scale_sources[1].to_string()]];
		// pieces first: thin + build + discharge, to see the TuningSet.
		create_smaller_config(&src_dir, spec.sig_file, 2,
			&format!("{}/config", plan_dir(spec.name, 0)));
		let db = build_fresh_db(&spec,
			&config_dir_for(&spec, 2, sig_lines.len(), 0),
			&cache_dir_for(&spec, 0));
		let ts = discharge_for_tuning(&spec, &db, &bins);
		assert_eq!(ts.words.len(), 2);            // email + 0-word
		assert_eq!(ts.infos.len(), 2);
		assert_eq!(ts.vdata.len(), 2);
		assert_eq!(ts.vdata[1].fname, ZERO_WORD_NAME);   // LAST
		assert_eq!(ts.words[1].len(), spec.chunk_len);
		let sum: usize = ts.words.iter().map(|w| w.len()).sum();
		assert_eq!(ts.total_word_n, sum);         // pad INCLUDED
		assert_eq!(ts.bin_word_lens, vec![ts.words[0].len()]); // pad NOT
		drop(ts);
		drop(db);
		// end-to-end kernel (rebuilds the tiny DB: read=false rule).
		// num_circs=1 -> k_max=1 -> the single P_max rung, which
		// T506's per-rung pass leaves untouched: immune to it landing.
		let caps = build_and_tune(&spec, 2, &bins, 1, 0);
		assert_eq!(caps.len(), 1);
		let p = &caps[0];
		assert_eq!(p.max_word_len, spec.chunk_len);
		assert!(p.subsigs >= 1 && p.avg_pats_per_subsig >= 1);
		assert!(p.basis_unique_states >= 2 && p.basis_acc_states >= 2);
		// C101: tune derived+pinned the share (check=false -> 1).
		let c = read_global_config();
		assert_eq!(c.perc_lkup_share, 1);
		assert!(c.b_pin_lkup_share, "tune must pin its derived share");
	}

	/// Share derives from the min non-empty bin; the max-derived
	/// share under-covers the binding job (small_data_par numbers).
	#[test]
	fn test_t9902_share_min_bin_math() {
		let lkup = 271_354usize;
		let mnl = 1 * LEGS;                        // chunk_len = 1
		let bins = vec![309usize, 28];
		assert_eq!(cover_word_n(&bins), 28);
		assert_eq!(cover_word_n(&[309, 0, 28]), 28);  // 0 filtered
		let p_old = perc_lkup_share_neo(lkup, 1, 309, true);
		let p_new = perc_lkup_share_neo(lkup, 1, 28, true);
		assert_eq!((p_old, p_new), (1_418, 15_633));
		// lk_share as build_circs_adv computes it (zkp_driver.rs:318)
		let (s_old, s_new) = (p_old * mnl / 100, p_new * mnl / 100);
		assert_eq!((s_old, s_new), (879, 9_692));
		assert!(s_old * 28 < lkup);               // OLD: violated
		assert_eq!(s_new * 28 - lkup, 22);        // NEW: margin +22
		assert!(s_new * 309 >= lkup);             // big job a fortiori
		assert_eq!(perc_lkup_share_neo(lkup, 1, 28, false), 1);
	}

	/// tune pins the share derived from the MIN non-empty bin, not
	/// the max; empty-corpus check-on tune panics.
	#[test]
	fn test_t9902_pin_wired_min_bin() {
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		// redirected clone: never touch the live dlp_neo dirs.
		let mut spec = DLP.clone();
		spec.name = "dlp_t9902";         // /tmp/bora/dlp_t9902_neo_p0
		spec.db_cache_dir = "dlp_t9902_neo";
		spec.b_check_lkup = true;        // the share axis IS the test
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		apply_spec_config(&spec, true, &part_role(0, 1, 1));
		// bin A: one 805 B email -> 1 chunk at mw=64. bin B: an 8 KB
		// repeat of it -> >= 2 chunks. Absolute path is honored by
		// discharge_for_tuning.
		let small = DLP.scale_sources[1].to_string();
		let body = std::fs::read(format!("{}/{}", proot, small))
			.unwrap();
		let big_path = format!("/tmp/bora/{}_big.dat", spec.name);
		std::fs::write(&big_path,
			body.repeat(1 + 8192 / body.len())).unwrap();
		let bins = vec![vec![small], vec![big_path.clone()]];
		let src_dir = format!("{}/{}", proot, spec.config_dir);
		let sig_lines = read_lines_nonblank(
			&format!("{}/{}", src_dir, spec.sig_file));
		create_smaller_config(&src_dir, spec.sig_file, 2,
			&format!("{}/config", plan_dir(spec.name, 0)));
		let db = build_fresh_db(&spec,
			&config_dir_for(&spec, 2, sig_lines.len(), 0),
			&cache_dir_for(&spec, 0));
		let ts = discharge_for_tuning(&spec, &db, &bins);
		// bin_word_lens == hand-computed per-bin packed sums, pad out
		let sums: Vec<usize> = bins.iter().map(|b| b.iter().map(|p| {
			let abs = if Path::new(p).is_absolute() { p.clone() }
				else { format!("{}/{}", proot, p) };
			let fnib: Vec<Fr> = utils::os::read_nibbles(&abs).iter()
				.map(|x| Fr::from(*x as u32)).collect();
			utils::data::pack_nibbles(&fnib).len()
		}).sum()).collect();
		assert_eq!(ts.bin_word_lens, sums);
		let (mn, mx) = (sums[0].min(sums[1]), sums[0].max(sums[1]));
		let mw = spec.chunk_len;
		// the fixture must discriminate min from max or it is vacuous
		let lkup_len = db.lkup.get_size();
		let p_min = perc_lkup_share_neo(lkup_len, mw, mn, true);
		let p_max = perc_lkup_share_neo(lkup_len, mw, mx, true);
		assert!(p_min > p_max, "fixture lost its imbalance");
		// (c) the coverage falsifier, independent of exact lkup size
		let mnl = mw * LEGS;
		let chunks_min = ((mn * LEGS) / mnl).max(1);
		assert!(p_max * mnl / 100 * chunks_min < lkup_len);
		assert!(p_min * mnl / 100 * chunks_min >= lkup_len);
		// (b) WIRING: tune pins exactly the min-derived value.
		let caps = tune(&spec, &db, &ts, 1);
		assert_eq!(caps.len(), 1);
		let c = read_global_config();
		assert!(c.b_pin_lkup_share, "tune must pin its share");
		assert_eq!(c.perc_lkup_share,
			perc_lkup_share_neo(lkup_len, mw,
				cover_word_n(&ts.bin_word_lens), true));
		assert_ne!(c.perc_lkup_share, p_max);
		drop(c);
		// (d) all-empty corpus + check-on must die at the new assert
		// (fires before the config write lock: catch_unwind-safe).
		let mut ts0 = ts;
		ts0.bin_word_lens = vec![0];
		let r = std::panic::catch_unwind(
			std::panic::AssertUnwindSafe(
				|| tune(&spec, &db, &ts0, 1)));
		assert!(r.is_err(), "empty-corpus check-on tune must panic");
		std::fs::remove_file(&big_path).ok();
	}

	/// Per-manifest summed packed word length, one entry per job in
	/// job order -- the population the FOLD measures (:1683).
	fn manifest_word_sums(manifests: &[String]) -> Vec<usize> {
		// repo root: manifests may hold repo-relative paths.
		let proot = utils::os::proj_root();
		manifests.iter().map(|m| {
			// job_<i>.dat is the newline path list load_files reads;
			// relative entries resolve against proj_root, absolute
			// ones are taken as-is (zkp_driver.rs:120).
			let list = fs::read_to_string(m).unwrap_or_else(|e| panic!(
				"bora_data_driver: read manifest {}: {}", m, e));
			list.lines().filter(|l| !l.trim().is_empty()).map(|p| {
				let abs = if Path::new(p).is_absolute() {
					p.to_string()
				} else {
					format!("{}/{}", proot, p)
				};
				let fnib: Vec<Fr> = utils::os::read_nibbles(&abs)
					.iter().map(|x| Fr::from(*x as u32)).collect();
				utils::data::pack_nibbles(&fnib).len()
			}).sum()
		}).collect()
	}

	/// First byte-sorted maildir path whose size is in [lo, hi) --
	/// the E2E's many-chunk bin, resolved at run time (no size pinned).
	fn pick_big_fixture_file(lo: u64, hi: u64) -> String {
		// repo root: the master list is repo-relative.
		let proot = utils::os::proj_root();
		// candidates: DLP's master list IS the Enron maildir corpus.
		let mut cand: Vec<String> = read_path_list(DLP.master_sources[0])
			.into_iter()
			.filter(|p| p.starts_with("data/samples/email/src/maildir/"))
			.collect();
		cand.sort();
		cand.into_iter().find(|p| {
			fs::metadata(format!("{}/{}", proot, p))
				.map(|m| m.len() >= lo && m.len() < hi).unwrap_or(false)
		}).unwrap_or_else(|| panic!(
			"bora_data_driver: no maildir file in [{}, {}) bytes",
			lo, hi))
	}

	/// LARGE-set MANUAL arm (idle box): an imbalanced two-job check-on
	/// fold -- only the min-derived share covers the binding job.
	#[test]
	#[ignore]
	fn test_t9902_e2e_imbalanced() {
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		// redirected clone: never touch the live dlp_neo dirs.
		let mut spec = DLP.clone();
		spec.name = "dlp_t9902_e2e"; // /tmp/bora/dlp_t9902_e2e_neo_p0
		spec.db_cache_dir = "dlp_t9902_e2e_neo";
		spec.b_check_lkup = true;    // the share axis IS the arm
		// dry SHAPE without dry POLICY: effective_spec is never called
		// here, so the cover check survives the cheap shape (inert for
		// DLP, whose dry_chunk_len is None).
		if let Some(c) = DLP.dry_chunk_len { spec.chunk_len = c; }
		// FIXTURE bit, NOT DLP's dry 22 (deviation, reported): lkup
		// carries 2^range2_bit+1 range rows (clam_db.rs:2298) and the
		// binding bin is ONE chunk, so at 22 EVERY step would carry a
		// 4.19M-key share -- prod-class, not the minutes-class this
		// arm is budgeted at. 18 = 262,145 rows, still far above what
		// the max-derived share buys one chunk (asserted below), and
		// it covers the big fixture file in nibbles (asserted below).
		spec.range2_bit = 18;
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		// 2 bins == 2 jobs == 2 manifests; part 0 of 1 folds both and
		// proves. b_dry_run=true here selects the LIGHT decider ONLY
		// (the check is spec-owned), which is what keeps this cheap.
		let role = part_role(0, 1, 2);
		apply_spec_config(&spec, true, &role);
		// pd: the part sandbox (thinned config + jobs/ live under it).
		let pd = reset_part_dir(&spec, 0);
		// bin 0: the 805 B dense email -> ONE chunk at chunk_len 64,
		// the job that binds coverage. bin 1: the first byte-sorted
		// maildir file in [50 KB, 96 KB) -> ~29 chunks; the window's
		// top is what keeps the corpus inside the 2^18 range table.
		let small = DLP.scale_sources[1].to_string();
		let big = pick_big_fixture_file(50 * 1024, 96 * 1024);
		// big_len: fixture file size in BYTES (2 nibbles per byte).
		let big_len = fs::metadata(format!("{}/{}", proot, big))
			.expect("big fixture file").len() as usize;
		// the range table must cover the LONGEST file in NIBBLES --
		// clam_db has no overflow guard (M104's dry sizing rule).
		assert!(2 * big_len + spec.chunk_len * LEGS
			< (1usize << spec.range2_bit),
			"fixture {} ({} B) overflows the 2^{} range table",
			big, big_len, spec.range2_bit);
		// bins: index IS the job id, written verbatim as manifests.
		let bins = vec![vec![small], vec![big]];
		// db_count: 2 rules = the smallest tuned DB (B102 item 3; 1
		// underflows the aggressive tuner).
		let db_count = 2;
		// src_dir: the real DLP config, thinned into the sandbox.
		let src_dir = format!("{}/{}", proot, spec.config_dir);
		// n_sigs: full rule count, only used to route config_dir_for.
		let n_sigs = read_lines_nonblank(
			&format!("{}/{}", src_dir, spec.sig_file)).len();
		// same bound build_and_tune applies (:1602), so the config it
		// rewrites below is byte-identical to the one built here.
		create_smaller_config_bounded(&src_dir, spec.sig_file, db_count,
			&format!("{}/config", pd),
			(1usize << spec.range2_bit) - spec.chunk_len * LEGS);
		// cfg_dir / cache_dir: shared by the tune build and the fold
		// reload, exactly as run_neo pairs them.
		let cfg_dir = config_dir_for(&spec, db_count, n_sigs, 0);
		let cache_dir = cache_dir_for(&spec, 0);
		// pieces first (B102 recipe): this DB carries lkup_len and its
		// TuningSet fixes the per-bin population the asserts pin.
		let db = build_fresh_db(&spec, &cfg_dir, &cache_dir);
		// lkup_len: folded table row count, the coverage target.
		let lkup_len = db.lkup.get_size();
		// ts_bins: per-bin packed sums as the TUNER sees them (pad
		// excluded), to be matched against the written manifests.
		let ts_bins =
			discharge_for_tuning(&spec, &db, &bins).bin_word_lens;
		drop(db);                    // build_and_tune builds its own
		// num_circs 1: the legacy aggressive default (zkp_driver.rs
		// :2156) and B102's kernel -- a ladder is not measured here.
		let num_circs = 1;
		// manifests: absolute job_<i>.dat paths, in job order.
		let manifests =
			write_job_manifests(&format!("{}/jobs", pd), &bins);
		// ladder: the tuned caps; tune pins the share on the way.
		let ladder = build_and_tune(&spec, db_count, &bins, num_circs, 0);
		// (1) tune-vs-fold population equality, end to end: the pinned
		// share is the one the WRITTEN manifests derive. Read BEFORE
		// folding -- a check-on aggressive fold may bump the share once
		// for the dummy self-cover (fold_with_self_cover) and mask it.
		let sums = manifest_word_sums(&manifests);
		assert_eq!(sums, ts_bins, "manifest population != tuning bins");
		// mw: the chunk axis of the share math.
		let mw = spec.chunk_len;
		let c = read_global_config();
		assert!(c.b_pin_lkup_share, "tune must pin its share");
		assert_eq!(c.perc_lkup_share, perc_lkup_share_neo(lkup_len, mw,
			cover_word_n(&sums), true));
		drop(c);
		// (2) the falsifier at fold scale: the OLD max-derived share
		// fails build_circs_adv_aggr's guard (zkp_driver.rs:453) on the
		// binding job; the min-derived one clears it.
		let mn = cover_word_n(&sums);            // the binding job
		let mx = sums.iter().copied().max().unwrap();
		let p_min = perc_lkup_share_neo(lkup_len, mw, mn, true);
		let p_max = perc_lkup_share_neo(lkup_len, mw, mx, true);
		assert!(p_min > p_max, "fixture lost its imbalance");
		let mnl = mw * LEGS;                     // nibbles per chunk
		let chunks_min = ((mn * LEGS) / mnl).max(1);
		assert!(p_max * mnl / 100 * chunks_min < lkup_len,
			"max-derived share already covers: fixture is vacuous");
		assert!(p_min * mnl / 100 * chunks_min >= lkup_len);
		println!("T9902 f1: lkup {} bins {:?} perc_min {} perc_max {}",
			lkup_len, sums, p_min, p_max);
		// (3) Pass 1 asserts lkup coverage PER JOB inside the fold
		// (foldpot driver.rs:2027), so fold() RETURNING is the
		// coverage assert -- there is nothing to check afterwards.
		// That assert is SKIPPED when word_cap_per_job > 0 (:2032), so
		// a stale cap from another test would make (3) vacuous.
		assert_eq!(read_global_config().word_cap_per_job, 0,
			"word_cap_per_job must be 0 or Pass 1 skips coverage");
		fold(&spec, &cfg_dir, &cache_dir, &manifests[role.jobs.clone()],
			&ladder, num_circs);
	}

	/// LARGE-set MANUAL arm (idle box): a balanced 8-job run_neo, to
	/// MEASURE the prod min-vs-max share delta instead of simulating.
	#[test]
	#[ignore]
	fn test_t9902_e2e_balanced_large() {
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		// redirected clone: never touch the live dlp_neo dirs.
		let mut spec = DLP.clone();
		spec.name = "dlp_t9902_e2e2"; // /tmp/bora/dlp_t9902_e2e2_neo_p0
		spec.db_cache_dir = "dlp_t9902_e2e2_neo";
		spec.b_check_lkup = true;     // the share axis IS the arm
		// dry SHAPE without dry POLICY: run_neo is called NOT dry, so
		// only these two fields move and the check survives (:2035).
		spec.range2_bit = DLP.dry_range2_bit
			.expect("DLP must carry a dry range2_bit");
		if let Some(c) = DLP.dry_chunk_len { spec.chunk_len = c; }
		assert!(effective_spec(&spec, false).b_check_lkup,
			"a non-dry run must keep the clone's cover check");
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		// perc_samples 0.06% of the 504,854-file Enron master = 303
		// files / 751 KB: the design's "few hundred files", and LPT
		// lands 48 chunks in EVERY one of the 8 bins, which is what
		// makes a delta of 0 a measurement, not a rounding accident.
		let perc_samples = 0.06;
		// Pass 1's per-job coverage assert is SKIPPED when
		// word_cap_per_job > 0 (foldpot driver.rs:2032); a stale cap
		// from another test would make the run prove nothing.
		assert_eq!(read_global_config().word_cap_per_job, 0,
			"word_cap_per_job must be 0 or Pass 1 skips coverage");
		// num_jobs 8, single part, 2 rungs, NOT dry, not ladder-only:
		// the production call shape. perc_db is 40 not 100 because the
		// aggressive sig-id bit split caps sig_id < 2^(range2_bit-10) =
		// 4096 at this dry-shape range2_bit=22 (hex_acdfa.rs:76 asserts
		// it) and all 9,861 rules blow it; count_of(9861, 40.0) = 3945
		// fits, and this arm measures a delta-0 on corpus BALANCE,
		// which does not need the prod rule count.
		let num_jobs = 8;
		let ladder = run_neo(&spec, 40.0, perc_samples, 2, num_jobs, 1,
			0, false, false);
		assert_eq!(ladder.len(), 2, "num_circs rungs come back");
		// manifests: run_neo wrote one per job under its plan dir and
		// they survive the run (only its ENTRY resets that dir).
		let jobs_dir = format!("{}/jobs", plan_dir(spec.name, 0));
		let manifests: Vec<String> = (0..num_jobs)
			.map(|i| format!("{}/job_{}.dat", jobs_dir, i)).collect();
		// fixture guard: perc_samples must still land a few hundred
		// files, or the shape measured is not the reviewed one.
		let n_files: usize = manifests.iter()
			.map(|m| read_lines_nonblank(m).len()).sum();
		assert!((200..=400).contains(&n_files),
			"corpus drifted to {} files, retune perc_samples", n_files);
		// lkup_len needs the DB, which the fold dropped. RELOAD it from
		// the cache this run wrote (read=true, write=false) rather than
		// rebuilding: it is the very cache the fold reloaded from
		// (:881), so the table -- and lkup_len -- are the folded ones.
		let n_sigs = read_lines_nonblank(&format!("{}/{}/{}", proot,
			spec.config_dir, spec.sig_file)).len();
		let cfg = default_clamav_cfg();
		let [sig, dfa, ised, ised_igc] = cfg_paths(&spec,
			&config_dir_for(&spec, n_sigs, n_sigs, 0));
		// vlog: build_or_load's log sink, unused here.
		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::build_or_load(&cfg, &sig, &dfa, &ised,
			&ised_igc, &mut vlog, &cache_dir_for(&spec, 0), true, false)
			.expect("bora_data_driver: reload db for lkup_len");
		// lkup_len: folded table row count, the coverage target.
		let lkup_len = db.lkup.get_size();
		drop(db);
		// sums: per-job packed sums recomputed from the manifests the
		// fold read; mw/mnl: the chunk axis of the share math.
		let sums = manifest_word_sums(&manifests);
		let mw = spec.chunk_len;
		let mnl = mw * LEGS;
		// chunks: per-job step count, the axis the share divides by.
		let chunks: Vec<usize> = sums.iter()
			.map(|n| ((n * LEGS) / mnl).max(1)).collect();
		let p_min = perc_lkup_share_neo(lkup_len, mw,
			cover_word_n(&sums), true);
		let p_max = perc_lkup_share_neo(lkup_len, mw,
			sums.iter().copied().max().unwrap(), true);
		println!("T9902 f2: files {} lkup {} chunks {:?} sums {:?} \
			perc_min {} perc_max {}", n_files, lkup_len, chunks, sums,
			p_min, p_max);
		// the pin is min-derived; a check-on aggressive fold may have
		// bumped it once for the dummy self-cover, hence >= not ==.
		let c = read_global_config();
		assert!(c.b_pin_lkup_share, "tune must pin its share");
		assert!(c.perc_lkup_share >= p_min,
			"pinned share {} below the min-derived {}",
			c.perc_lkup_share, p_min);
		drop(c);
		// THE measurement: equal chunk counts => the two sizings agree
		// exactly (prod delta 0); a straddled chunk boundary must still
		// cost at most one percent point.
		if chunks.iter().all(|&k| k == chunks[0]) {
			assert_eq!(p_min, p_max,
				"equal chunk counts must give equal shares");
		} else {
			assert!(p_min >= p_max, "min sizing must not under-cover");
			assert!(p_min - p_max <= 1,
				"prod delta {} > 1 perc point", p_min - p_max);
		}
		// run_neo folded and proved before returning, so reaching here
		// IS Pass 1's per-job coverage assert under the pinned share.
	}

	#[test]
	fn test_b103_retry_caperr_bumps() {
		use std::cell::{Cell, RefCell};
		let _lock = cfg_lock();
		let _catch = CatchFlag::on();
		// Real emission shapes (discharge_adv.rs:1178, fsm_adv.rs:1336,
		// discharge_adv.rs:2531), in the Debug form the parser expects.
		let e1 = "advice: CapErr([(\"dis_adv::prod_pats_expansion, \
			StepQueue b_igc: false\", 7777)])";
		let e2 = "advice: CapErr([(\"fsm_adv::basis_pats_in_trace for \
			loc_state_pat_tbl, b_igc: true\", 55), \
			(\"dis_adv::subsigs\", 40)])";
		let seen: RefCell<Vec<CapParams>> = RefCell::new(vec![]);
		let mut p = tiny_caps();
		retry_caperr(&DLP, &mut p, |c| {
			seen.borrow_mut().push(c.clone());
			match seen.borrow().len() {
				1 => panic!("{}", e1),
				2 => panic!("{}", e2),
				_ => {}
			}
		});
		let seen = seen.into_inner();
		assert_eq!(seen.len(), 3, "two CapErr rounds then success");
		// each round observed the previous round's bumps.
		assert_eq!(seen[1].prod_pats_expansion, 7777);
		assert_eq!(seen[2].basis_pats_in_trace_igc, 55);
		assert_eq!(p.prod_pats_expansion, 7777);
		assert_eq!(p.basis_pats_in_trace_igc, 55);
		assert_eq!(p.subsigs, 41, "+1 comp_sig dummy entry");
		assert_eq!(p.aggr_needs_subsigs, 40, "b_aggr routing (DLP)");
		// first-try success: exactly one call, p untouched.
		let p0 = p.clone();
		let n = Cell::new(0usize);
		retry_caperr(&DLP, &mut p, |_| n.set(n.get() + 1));
		assert_eq!(n.get(), 1);
		assert_eq!(p, p0);
	}

	#[test]
	#[should_panic(expected = "non-CapErr")]
	fn test_b103_retry_caperr_hard_stop() {
		let _lock = cfg_lock();
		let _catch = CatchFlag::on();
		let mut p = tiny_caps();
		retry_caperr(&DLP, &mut p, |_| panic!("plain fold crash"));
	}

	#[test]
	#[should_panic(expected = "stuck")]
	fn test_b103_retry_caperr_stuck_unmapped() {
		let _lock = cfg_lock();
		let _catch = CatchFlag::on();
		let mut p = tiny_caps();
		retry_caperr(&DLP, &mut p, |_| panic!(
			"advice: CapErr([(\"no_such_gadget::mystery_cap\", 9)])"));
	}

	#[test]
	#[should_panic(expected = ">30")]
	fn test_b103_retry_caperr_over_30() {
		use std::cell::Cell;
		let _lock = cfg_lock();
		let _catch = CatchFlag::on();
		let mut p = tiny_caps();
		let n = Cell::new(0usize);
		retry_caperr(&DLP, &mut p, |_| {
			n.set(n.get() + 1);
			// requirement grows every try so `changed` stays true.
			panic!("advice: CapErr([(\"dis_adv::prod_pats_expansion, \
				StepQueue b_igc: false\", {})])", 1000 + n.get());
		});
	}

	/// C101: per-part paths are pairwise disjoint; the full-DB config
	/// dir is the one deliberately shared (read-only) path.
	#[test]
	fn test_c101_part_paths_disjoint() {
		assert_ne!(plan_dir("dlp", 0), plan_dir("dlp", 1));
		assert_eq!(cache_dir_for(&DLP, 1), "dlp_neo_p1");
		assert_ne!(cache_dir_for(&DLP, 0), cache_dir_for(&DLP, 1));
		assert_ne!(config_dir_for(&DLP, 99, 9861, 0),
			config_dir_for(&DLP, 99, 9861, 1));
		assert_eq!(config_dir_for(&DLP, 9861, 9861, 0),
			config_dir_for(&DLP, 9861, 9861, 1));
	}

	/// C101: the wipe hits ONLY the named part's sandbox.
	#[test]
	fn test_c101_reset_part_dir() {
		let mut spec = DLP.clone();
		spec.name = "dlp_reset_test";
		let _t0 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 1)));
		let p1 = plan_dir(spec.name, 1);
		fs::create_dir_all(&p1).unwrap();
		fs::write(format!("{}/keep.txt", p1), "x").unwrap();
		let p0 = reset_part_dir(&spec, 0);
		fs::write(format!("{}/stale.txt", p0), "x").unwrap();
		assert_eq!(reset_part_dir(&spec, 0), p0);
		assert!(!Path::new(&format!("{}/stale.txt", p0)).exists(),
			"stale file survived the wipe");
		assert!(Path::new(&format!("{}/jobs", p0)).is_dir());
		assert!(Path::new(&format!("{}/keep.txt", p1)).exists(),
			"sibling part's sandbox must survive");
	}

	/// C101: KEY units -> percent (zkp_driver.rs:2233), ceil edges.
	/// mnl for chunk 64 = 64*62 = 3968.
	#[test]
	fn test_c101_share_need_perc() {
		assert_eq!(share_need_perc(850, 3968), 22);
		assert_eq!(share_need_perc(1, 3968), 1);
		assert_eq!(share_need_perc(3968, 3968), 100);
		assert_eq!(share_need_perc(3969, 3968), 101);
	}

	/// The env-free share port stays byte-equal to the frozen source
	/// (zkp_driver.rs:222) on every path the two share, including the
	/// measured truncation edge its comment documents. Requires the
	/// share env vars unset -- the source reads them first.
	#[test]
	fn test_c102_perc_lkup_share_port() {
		for k in ["ZKR_LKSHARE", "ZKR_CLAM_LKUP_SHARE"] {
			assert!(std::env::var(k).is_err(),
				"unset {} before running this test", k);
		}
		// lkup 9466 over 4 chunks of mnl 62: the naive bound's 3817
		// truncates to share 2366 (2366*4 < 9466); the two-ceil math
		// must give 3818.
		assert_eq!(perc_lkup_share_neo(9466, 1, 4, true), 3818);
		assert_eq!(perc_lkup_share_neo(9466, 64, 4, false), 1,
			"check-off floor");
		for &(l, c, t, b) in &[
			(9466usize, 1usize, 4usize, true),
			(246_420_000, 64, 1_000_000, true),
			(33_700_000, 64, 3_968, true),
			(1, 64, 1, true),
			(9466, 64, 4, false),
		] {
			assert_eq!(perc_lkup_share_neo(l, c, t, b),
				crate::zkp_driver::perc_lkup_share_for(l, c, t, b),
				"port drifted from source at ({},{},{},{})", l, c, t, b);
		}
	}

	/// cover_word_n picks the SMALLEST non-empty job: coverage is
	/// achieved per job, so the fewest-step job binds the share.
	#[test]
	fn test_cover_word_n_picks_min_nonempty() {
		use crate::zkp_driver::cover_word_n;
		// single job: min == max, so single-job sizing is unchanged.
		assert_eq!(cover_word_n(&[309]), 309, "single job is identity");
		// uneven split: the small job binds, not the big one.
		assert_eq!(cover_word_n(&[309, 60, 120, 240]), 60);
		assert_eq!(cover_word_n(&[60, 309]), cover_word_n(&[309, 60]),
			"order must not matter");
		// an EMPTY job dispatches no step; counting its 0 would drive
		// chunks to 1 and the share to ~lkup_len (a RAM blowup).
		assert_eq!(cover_word_n(&[0, 309, 60]), 60, "skip empty jobs");
		assert_eq!(cover_word_n(&[0, 0]), 0, "all empty -> 0");
		assert_eq!(cover_word_n(&[]), 0, "no jobs -> 0");
	}

	/// small_data_par's MEASURED numbers: sizing off the max job (309)
	/// under-covers the min job (28); sizing off the min covers it.
	#[test]
	fn test_lkup_share_min_covers_small_data_par() {
		for k in ["ZKR_LKSHARE", "ZKR_CLAM_LKUP_SHARE"] {
			assert!(std::env::var(k).is_err(),
				"unset {} before running this test", k);
		}
		use crate::zkp_driver::perc_lkup_share_for;
		let (lkup_len, chunk_len, mnl) = (271_354usize, 1usize, 62usize);
		// 28 = the SMALLEST job's packed word length, read from a real
		// run (T1 log line "perc 1 -> 15633"). NOT derivable from the
		// assert's "total:" number, which is whichever of the 4 parallel
		// jobs panics first and is therefore non-deterministic.
		let cover_n = 28usize;
		// OLD: sized off the LARGEST job (309).
		let perc_max = perc_lkup_share_for(lkup_len, chunk_len, 309, true);
		assert_eq!(perc_max, 1418, "the shipped-but-wrong share");
		let share_max = perc_max * mnl / 100;
		assert_eq!(share_max, 879);
		assert!(share_max * cover_n < lkup_len,
			"max-sizing must UNDER-cover: {} < {}",
			share_max * cover_n, lkup_len);
		// NEW: sized off the SMALLEST job.
		let perc_min = perc_lkup_share_for(lkup_len, chunk_len,
			cover_n, true);
		assert_eq!(perc_min, 15633);
		let share_min = perc_min * mnl / 100;
		assert_eq!(share_min, 9692);
		assert!(share_min * cover_n >= lkup_len,
			"min-sizing must cover: {} >= {}",
			share_min * cover_n, lkup_len);
	}

	// C102: every argument assert fires BEFORE any process-wide
	// write, so none of these five need cfg_lock.

	#[test]
	#[should_panic(expected = "vec_count is empty")]
	fn test_c102_scale_args_empty() {
		collect_scale_data_neo(&DLP, 0, &[], false);
	}

	#[test]
	#[should_panic(expected = "strictly ascending")]
	fn test_c102_scale_args_descending() {
		collect_scale_data_neo(&DLP, 0, &[987, 2], false);
	}

	#[test]
	#[should_panic(expected = "must be >= 2")]
	fn test_c102_scale_args_aggr_min() {
		// count 1 = the pin alone: zero SED demand underflows the
		// aggressive tuner, so the entry assert must catch it.
		collect_scale_data_neo(&DLP, 0, &[1, 987], false);
	}

	#[test]
	#[should_panic(expected = "corpus_idx 2 out of range")]
	fn test_c102_scale_args_corpus_oob() {
		collect_scale_data_neo(&DLP, 2, &[2, 987], false);
	}

	#[test]
	#[should_panic(expected = "over-count")]
	fn test_c102_scale_args_over_total() {
		collect_scale_data_neo(&DLP, 0, &[2, 1_000_000], false);
	}

	/// C102: the scale clone flips exactly {check, ladder, names};
	/// the renames keep scale's sandbox + DB cache disjoint from the
	/// full run's part dirs.
	#[test]
	fn test_c102_scale_spec_clone() {
		let sc = scale_spec_clone(&DLP);
		assert_eq!(sc.name, "dlp_scale");
		assert_eq!(sc.db_cache_dir, "dlp_neo_scale");
		assert!(!sc.b_check_lkup, "scale never cover-checks");
		assert!(sc.vec_decrease_level.is_empty());
		assert_eq!(sc.config_dir, DLP.config_dir);
		assert_eq!(sc.sig_file, DLP.sig_file);
		assert_eq!(sc.master_sources, DLP.master_sources);
		assert_eq!(sc.scale_sources, DLP.scale_sources);
		assert_eq!(sc.chunk_len, DLP.chunk_len);
		assert_eq!(sc.range2_bit, DLP.range2_bit);
		assert_eq!(sc.fanout_cap, DLP.fanout_cap);
		assert_eq!(sc.b_aggressive, DLP.b_aggressive);
		assert_ne!(plan_dir(sc.name, 0), plan_dir(DLP.name, 0));
		assert_ne!(cache_dir_for(&sc, 0), cache_dir_for(&DLP, 0));
	}

	fn argv(v: &[&str]) -> Vec<String> {
		v.iter().map(|s| s.to_string()).collect()
	}

	/// C103: happy-path parses for lkup + the smoke-run full_dlp line.
	#[test]
	fn test_c103_parse_args_full() {
		assert_eq!(parse_args(&argv(&["lkup", "5", "/tmp/x"])),
			Cmd::Lkup { perc: 5, dest_path: "/tmp/x".to_string() });
		assert_eq!(parse_args(&argv(&["full_dlp", "1", "1", "1",
			"2", "1", "0", "1", "1"])),
			Cmd::FullDlp { perc_db: 1.0, perc_samples: 1.0,
				num_circs: 1, num_jobs: 2, numa_num: 1, part_id: 0,
				b_dry_run: true, b_ladder_only: true });
		// fractional percs: the sub-1% smoke unit
		assert_eq!(parse_args(&argv(&["full_dlp", "0.1", "0.05",
			"4", "2", "1", "0", "1", "0"])),
			Cmd::FullDlp { perc_db: 0.1, perc_samples: 0.05,
				num_circs: 4, num_jobs: 2, numa_num: 1, part_id: 0,
				b_dry_run: true, b_ladder_only: false });
	}

	/// C103: counts CSV -> Vec<usize>, pin-inclusive units untouched.
	#[test]
	fn test_c103_parse_args_scale() {
		assert_eq!(parse_args(&argv(&["scale_dlp", "0",
			"2,987,9861", "0"])),
			Cmd::ScaleDlp { corpus_idx: 0,
				vec_count: vec![2, 987, 9861],
				b_dry_run: false });
	}

	/// scale_dlp carries a dry token like scale_clam; dry=1 parses.
	#[test]
	fn test_parse_args_scale_dlp_dry_token() {
		assert_eq!(parse_args(&argv(&["scale_dlp", "1", "2,494", "1"])),
			Cmd::ScaleDlp { corpus_idx: 1, vec_count: vec![2, 494],
				b_dry_run: true });
	}

	/// The dry token is REQUIRED -- the old 2-arg form must not parse
	/// silently as a full sweep.
	#[test]
	#[should_panic(expected = "scale_dlp takes 3 args, got 2")]
	fn test_parse_args_scale_dlp_rejects_old_arity() {
		parse_args(&argv(&["scale_dlp", "0", "2,987"]));
	}

	/// effective parses (perc, dest_path), same shape as lkup.
	#[test]
	fn test_parse_args_effective() {
		assert_eq!(parse_args(&argv(&["effective", "2", "/tmp/e.txt"])),
			Cmd::Effective { perc: 2,
				dest_path: "/tmp/e.txt".to_string() });
	}

	/// effective without a dest_path must refuse, not default one.
	#[test]
	#[should_panic(expected = "effective takes 2 args, got 1")]
	fn test_parse_args_effective_rejects_short() {
		parse_args(&argv(&["effective", "2"]));
	}

	/// DLP dry swaps in the 22-bit range table; full keeps 25.
	#[test]
	fn test_dlp_dry_range2_bit_swaps() {
		assert_eq!(effective_spec(&DLP, true).range2_bit, 22);
		assert_eq!(effective_spec(&DLP, false).range2_bit, 25);
	}

	/// DLP/DNA fold their scale corpus WHOLE (2 KB mails / no sweep);
	/// only CLAM's binaries are big enough to truncate.
	#[test]
	fn test_dry_scale_perc_is_per_dataset() {
		assert_eq!(DLP.dry_scale_perc, 100.0);
		assert_eq!(DNA.dry_scale_perc, 100.0);
		assert_eq!(CLAM.dry_scale_perc, 5.0);
	}

	/// shrink_lone_sample no-ops at 100.0, so a dry DLP sweep folds
	/// the whole mail instead of a 41-byte fragment.
	#[test]
	fn test_dlp_dry_scale_does_not_shrink() {
		let proot = utils::os::proj_root();
		for s in DLP.scale_sources {
			let n = fs::metadata(format!("{}/{}", proot, s))
				.unwrap_or_else(|e| panic!("scale source {}: {}", s, e))
				.len() as usize;
			let bins = vec![vec![s.to_string()]];
			let out = shrink_lone_sample("/tmp/bora/unused", bins,
				DLP.dry_scale_perc);
			assert_eq!(out, vec![vec![s.to_string()]],
				"DLP scale source {} ({} B) must not be truncated",
				s, n);
		}
	}

	#[test]
	#[should_panic(expected = "full_dlp takes 8 args, got 7")]
	fn test_c103_parse_args_bad_arity() {
		parse_args(&argv(&["full_dlp", "1", "1", "1", "2", "1",
			"0", "1"]));
	}

	#[test]
	#[should_panic(expected = "count not a usize")]
	fn test_c103_parse_args_bad_count() {
		parse_args(&argv(&["scale_dlp", "0", "2,x,9861", "0"]));
	}

	#[test]
	#[should_panic(expected = "must be 0|1")]
	fn test_c103_parse_args_bad_bool() {
		parse_args(&argv(&["full_dlp", "1", "1", "1", "2", "1",
			"0", "2", "1"]));
	}

	#[test]
	#[should_panic(expected = "percs must be in (0, 100]")]
	fn test_c103_parse_args_zero_perc() {
		parse_args(&argv(&["full_dlp", "0", "1", "1", "2", "1",
			"0", "1", "1"]));
	}

	#[test]
	#[should_panic(expected = "percs must be in (0, 100]")]
	fn test_c103_parse_args_perc_over_100() {
		parse_args(&argv(&["full_dlp", "101", "1", "1", "2", "1",
			"0", "1", "1"]));
	}

	#[test]
	#[should_panic(expected = "unknown subcommand")]
	fn test_c103_parse_args_unknown() {
		parse_args(&argv(&["scale_dna", "0", "2,987"]));
	}

	/// C103: ladder padding -- dummies are raised clones of rung 0
	/// inserted between rung 0 and the real upper rungs; equal subsigs
	/// so routing is unchanged; long-enough ladders untouched.
	#[test]
	fn test_c103_pad_ladder_to() {
		let mut r0 = tiny_caps();
		r0.basis_unique_states = 100;
		r0.basis_acc_states = 200;
		r0.basis_pats_in_trace = 400;
		r0.cp_basis_unique_states = 40;
		let mut r1 = r0.clone();
		r1.subsigs = 9;
		r1.basis_unique_states = 9999;
		let mut lad = vec![r0.clone(), r1.clone()];
		pad_ladder_to(&mut lad, 4);
		assert_eq!(lad.len(), 4);
		assert_eq!(lad[0], r0);
		assert_eq!(lad[3], r1);
		let ax = |c: &CapParams| [c.basis_unique_states,
			c.basis_acc_states, c.basis_pats_in_trace,
			c.cp_basis_unique_states];
		for d in &lad[1..3] {
			assert_eq!(d.subsigs, r0.subsigs);
		}
		for k in 0..4 {
			assert!(ax(&lad[1])[k] > ax(&lad[0])[k]);
			assert!(ax(&lad[2])[k] > ax(&lad[1])[k]);
		}
		assert_eq!(lad[1].basis_unique_states, 105);   // +5% ceil
		assert_eq!(lad[2].basis_unique_states, 110);   // +10% ceil
		let mut same = vec![r0.clone(), r1.clone()];
		pad_ladder_to(&mut same, 2);
		assert_eq!(same, vec![r0.clone(), r1.clone()]);
		let mut longer = vec![r0.clone(), r0.clone(), r1.clone()];
		pad_ladder_to(&mut longer, 2);
		assert_eq!(longer.len(), 3);                   // never truncates
	}

	/// D101: the scrub-compensating env self-sets. Mutates process
	/// env -- serial (--test-threads=1) like the rest of the module.
	#[test]
	fn test_d101_set_diag_env() {
		let _g = cfg_lock();
		set_diag_env(1);
		assert_eq!(std::env::var("ZKR_LOG_TAG").unwrap(), "p1_");
		assert_eq!(
			std::env::var("ZKR_DLP_PROBE_FILES").unwrap(), "1");
		std::env::remove_var("ZKR_LOG_TAG");
		std::env::remove_var("ZKR_DLP_PROBE_FILES");
	}

	/// D102: light drops the cover check, heavy keeps the spec
	/// value, false stays false; nothing else changes.
	#[test]
	fn test_d102_effective_spec() {
		assert!(DLP.b_check_lkup);
		let e = effective_spec(&DLP, true);
		assert!(!e.b_check_lkup, "light run must not cover-check");
		assert_eq!(e.name, DLP.name);
		assert_eq!(e.db_cache_dir, DLP.db_cache_dir);
		assert!(effective_spec(&DLP, false).b_check_lkup);
		let sc = scale_spec_clone(&DLP);
		assert!(!effective_spec(&sc, false).b_check_lkup);
	}

	/// M103: the DNA const points at real files and pins legacy
	/// full_dna()'s configuration (zkp_driver.rs:5279-5387) field
	/// for field, hand caps included.
	#[test]
	fn test_m103_dna_const_sane() {
		let proot = utils::os::proj_root();
		let abs = |p: &str| format!("{}/{}", proot, p);

		// 1. every path the pipeline will open exists on disk.
		assert!(Path::new(&abs(DNA.config_dir)).is_dir(),
			"config_dir missing: {}", DNA.config_dir);
		for f in [DNA.sig_file, "main_dfa.dat", "needs_ised.dat",
			"needs_ised_igc.dat"] {
			let p = abs(&format!("{}/{}", DNA.config_dir, f));
			assert!(Path::new(&p).is_file(), "missing {}", p);
		}
		let corpus = read_path_list(DNA.master_sources[0]);
		assert_eq!(corpus.len(), 1, "DNA master must be ONE sample");
		let sample = abs(&corpus[0]);
		assert!(fs::metadata(&sample).map(|m| m.len() > 1_000_000)
			.unwrap_or(false), "chr17 sample missing: {}", sample);
		// the sole main_dfa entry is a FULL SIG LINE (== line 0);
		// clam_db matches dfa entries by NAME (clam_db.rs:2135), so
		// it is INERT -- DNA runs 0 dfa sigs even in legacy.
		let sigs = read_lines_nonblank(
			&abs(&format!("{}/{}", DNA.config_dir, DNA.sig_file)));
		let dfa = read_lines_nonblank(
			&abs(&format!("{}/main_dfa.dat", DNA.config_dir)));
		assert_eq!(dfa.len(), 1);
		assert_eq!(dfa[0], sigs[0], "dfa entry must be pinned line 0");
		assert!(sigs[0].starts_with("Win.Alphabet"));

		// 2. shape.
		assert_eq!(DNA.name, "dna");
		assert!(DNA.scale_sources.is_empty(), "no Q4 scale for DNA");
		assert!(DNA.vec_decrease_level.is_empty());
		assert!(!DNA.b_aggressive);
		assert!(!DNA.b_check_lkup, "user decision: check stays off");

		// 3. neo-own cache.
		assert_eq!(DNA.db_cache_dir, "dna_neo");
		assert_eq!(plan_dir(DNA.name, 0), "/tmp/bora/dna_neo_p0");

		// 4. legacy full_dna() parity, field by field.
		assert_eq!(DNA.chunk_len, 4096);
		assert_eq!(DNA.range2_bit, 27);
		assert_eq!(DNA.fanout_cap, 127);      // untouched default
		assert_eq!(DNA.min_pm_word_len, 4);   // untouched default
		assert_eq!(DNA.n_par_snark, 2);
		assert_eq!(DNA.n_par_snark_cp, 2);
		assert_eq!(DNA.n_par_batch_claim, 8);
		assert_eq!(DNA.min_subsigs, 64);
		assert_eq!(DNA.min_basis_unique_states, 100);
		assert_eq!(DNA.min_basis_acc_states, 2);
		assert_eq!(DNA.min_basis_pats_in_trace, 4);
		assert_eq!(DNA.min_avg_pats_per_subsig, 1);
		assert_eq!(DNA.min_dfa_sigs, 2);
		assert_eq!(DNA.min_dfa_subsigs, 2);

		// 5. hand caps (zkp_driver.rs:5309-5361), the non-aggr seed.
		// bound: CapParams carries a Vec (v5 levels), so the const is
		// no longer promoted to a 'static temporary.
		let dna = DNA;
		let h = dna.hand_seed.as_ref().expect("DNA needs hand_seed");
		assert_eq!((h.max_word_len, h.acdfa_state_part_bits),
			(4096, 27));
		assert_eq!((h.cp_basis_unique_states, h.cp_subsigs,
			h.cp_avg_pats), (6500, 20, 1));
		assert_eq!((h.subsigs, h.avg_pats_per_subsig,
			h.avg_active_pats_per_subsig), (20, 1, 1));
		assert_eq!((h.basis_pats_in_trace,
			h.perc_pats_expansion_rate), (4, 200));
		assert_eq!((h.sigs_sed, h.perc_comp_subsigs), (20, 20));
		assert_eq!((h.basis_unique_states, h.basis_acc_states),
			(6500, 2));
		assert_eq!((h.subsigs_igc,
			h.avg_active_pats_per_subsig_igc), (20, 1));
		assert_eq!((h.basis_pats_in_trace_igc,
			h.perc_pats_expansion_rate_igc), (4, 4));
		assert_eq!((h.basis_acc_states_igc,
			h.basis_unique_states_igc), (2, 6500));
		assert_eq!((h.dfa_sigs, h.dfa_subsigs), (0, 0));
		assert_eq!((h.prod_pats_expansion, h.qm_real_rows,
			h.aggr_needs_subsigs), (0, 0, 0));
		assert_eq!((h.prod_pats_expansion_igc, h.qm_real_rows_igc),
			(0, 0));
	}

	/// M103: lone-file corpora shrink to a ceil(perc%) byte prefix
	/// under <pd>/sample/; multi-file and perc>=100 pass through.
	#[test]
	fn test_m103_shrink_lone_sample() {
		let td = fresh_tmp_dir("shrink");
		let pd = td.to_str().unwrap();
		let f1 = td.join("s1.bin");
		fs::write(&f1, vec![7u8; 1000]).unwrap();
		let one = vec![vec![f1.to_str().unwrap().to_string()]];
		let f2 = td.join("s2.bin");
		fs::write(&f2, b"xy").unwrap();
		let two = vec![one[0].clone(),
			vec![f2.to_str().unwrap().to_string()]];
		// identity: 2 files, and 1 file at perc >= 100.
		assert_eq!(shrink_lone_sample(pd, two.clone(), 2.0), two);
		assert_eq!(shrink_lone_sample(pd, one.clone(), 100.0), one);
		// shrink: 2% of 1000 -> 20 bytes, a prefix, under pd/sample/.
		let out = shrink_lone_sample(pd, one.clone(), 2.0);
		let p = &out[0][0];
		assert!(p.starts_with(pd) && p.contains("/sample/")
			&& p.ends_with("s1.bin"), "bad shrunk path {}", p);
		assert_eq!(fs::read(p).unwrap(), vec![7u8; 20]);
		// floor of 1 byte, and ceil (0.15% of 1000 = 1.5 -> 2).
		let o2 = shrink_lone_sample(pd, one.clone(), 0.001);
		assert_eq!(fs::read(&o2[0][0]).unwrap().len(), 1);
		let o3 = shrink_lone_sample(pd, one, 0.15);
		assert_eq!(fs::read(&o3[0][0]).unwrap().len(), 2);
	}

	/// M103: full_dna parses through the shared parse_full8, and the
	/// refactored full_dlp arm did not drift.
	#[test]
	fn test_m103_parse_full_dna() {
		let a = |v: &[&str]| v.iter().map(|s| s.to_string())
			.collect::<Vec<String>>();
		assert_eq!(parse_args(&a(&["full_dna", "1", "2", "1", "1",
			"1", "0", "1", "0"])),
			Cmd::FullDna { perc_db: 1.0, perc_samples: 2.0,
				num_circs: 1, num_jobs: 1, numa_num: 1, part_id: 0,
				b_dry_run: true, b_ladder_only: false });
		assert_eq!(parse_args(&a(&["full_dlp", "0.25", "0.0198",
			"2", "2", "1", "0", "1", "0"])),
			Cmd::FullDlp { perc_db: 0.25, perc_samples: 0.0198,
				num_circs: 2, num_jobs: 2, numa_num: 1, part_id: 0,
				b_dry_run: true, b_ladder_only: false });
	}

	/// M103: full_dna arity reject goes through the shared helper.
	#[test]
	#[should_panic(expected = "full_dna takes 8 args")]
	fn test_m103_parse_full_dna_arity() {
		let v: Vec<String> = ["full_dna", "1", "2"].iter()
			.map(|s| s.to_string()).collect();
		parse_args(&v);
	}

	/// M103 kernel: FIRST real execution of tune's non-aggr arm --
	/// thinned real DNA DB + a shrink_lone_sample'd chr17 prefix.
	/// Structure asserts only; rung values belong to the tuner.
	#[test]
	fn test_m103_build_and_tune_tiny_dna() {
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		// redirected clone: never touch the live dna_neo dirs.
		let mut spec = DNA.clone();
		spec.name = "dna_test";          // /tmp/bora/dna_test_neo_p0
		spec.db_cache_dir = "dna_test_neo";
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		apply_spec_config(&spec, true, &part_role(0, 1, 1));
		// lone-sample corpus at 0.05% -> ~21KB -> a single chunk.
		let pd = plan_dir(spec.name, 0);
		fs::create_dir_all(&pd).unwrap();
		let bins = shrink_lone_sample(&pd,
			plan_corpus(&spec, 100.0, 1), 0.05);
		assert!(bins[0][0].contains("/sample/"), "shrink must fire");
		// build_and_tune thins the 27,501-sig config to 64 itself.
		let caps = build_and_tune(&spec, 64, &bins, 1, 0);
		assert_eq!(caps.len(), 1, "non-aggr = single rung");
		let p = &caps[0];
		assert_eq!(p.max_word_len, spec.chunk_len);
		assert_eq!(p.acdfa_state_part_bits, spec.range2_bit);
		assert!(p.qm_real_rows >= 2,
			"converged qm, not the dense-fallback 0 (T604)");
		let c = read_global_config();
		// tune wrote the non-aggr ladder floors from the converged
		// caps, and pinned the check-off share at 1.
		assert_eq!(c.min_subsigs, p.subsigs);
		assert_eq!(c.min_subsigs_igc, p.subsigs_igc);
		assert!(c.min_cp_subsigs >= 1);
		assert_eq!(c.perc_lkup_share, 1);
		assert!(c.b_pin_lkup_share, "tune must pin its share");
	}

	/// M103: numeric byte-offset prefixes are compared in nibbles
	/// (2x) against the bound; prefix-less lines always fit.
	#[test]
	fn test_m103_sig_fits_range() {
		let pin = "Win.Alphabet;Engine:51-255,Target:1;0|1;09af;0123";
		assert!(sig_fits_range(pin, 100));       // no prefix
		let s = "N.x;Engine:81-255,Target:0;0;50:abcd";
		assert!(sig_fits_range(s, 101));         // 2*50 < 101
		assert!(!sig_fits_range(s, 100));        // 2*50 !< 100
		let two = "N.y;E;0&1;10:aa;60:bb";       // worst subsig rules
		assert!(sig_fits_range(two, 121));
		assert!(!sig_fits_range(two, 120));
		// hex-looking pattern WITHOUT ':' is not an offset.
		assert!(sig_fits_range("N.z;E;0;1234", 1));
		// non-numeric prefix (EOF-40:) is kept.
		assert!(sig_fits_range("N.w;E;0;EOF-40:aa", 1));
	}

	/// M103: light swaps in dry_range2_bit (DNA 27->22) AND
	/// dry_chunk_len (4096->256); heavy and specs without the
	/// fields keep the REAL shape.
	#[test]
	fn test_m103_effective_spec_dry_shape() {
		assert_eq!(DNA.dry_range2_bit, Some(22));
		assert_eq!(DNA.dry_chunk_len, Some(256));
		assert_eq!(DLP.dry_range2_bit, Some(22));
		assert_eq!(DLP.dry_chunk_len, None);
		let d = effective_spec(&DNA, true);
		assert_eq!((d.range2_bit, d.chunk_len), (22, 256));
		let h = effective_spec(&DNA, false);
		assert_eq!((h.range2_bit, h.chunk_len), (27, 4096),
			"full run must keep the REAL shape");
		// DLP dry shrinks the table (2026-08-11) but keeps chunk_len:
		// 64 is already the smallest of the three.
		let dl = effective_spec(&DLP, true);
		assert_eq!((dl.range2_bit, dl.chunk_len), (22, 64));
		let dh = effective_spec(&DLP, false);
		assert_eq!((dh.range2_bit, dh.chunk_len), (25, 64));
	}

	/// M103: bounded thinning of the REAL DNA config keeps only
	/// in-range sigs (pool ~830 at 2^22) with the pin at line 0.
	#[test]
	fn test_m103_smaller_config_offset_filter() {
		let proot = utils::os::proj_root();
		let src = format!("{}/{}", proot, DNA.config_dir);
		let td = fresh_tmp_dir("offfilter");
		let bound = (1usize << 22) - DNA.chunk_len * 62;
		let out = create_smaller_config_bounded(&src, DNA.sig_file,
			usize::MAX, td.to_str().unwrap(), bound);
		let kept = read_lines_nonblank(&out);
		assert!(kept[0].starts_with("Win.Alphabet"), "pin survives");
		assert!(kept.len() >= 276 && kept.len() < 2000,
			"in-range pool {} outside expected band", kept.len());
		for l in &kept {
			assert!(sig_fits_range(l, bound));
		}
		// the dfa file's sole entry is a FULL SIG LINE; clam_db
		// matches dfa entries by NAME (clam_db.rs:2135), so it is
		// inert even in legacy full_dna (hand caps: dfa_sigs=0) and
		// the name-keyed needs filter drops it -- 0 entries thinned,
		// behaviorally identical to legacy.
		let dfa = read_lines_nonblank(&format!("{}/main_dfa.dat",
			td.to_str().unwrap()));
		assert_eq!(dfa.len(), 0);
	}

	/// M104: the CLAM const points at real files and pins the
	/// PRODUCTION full_clamav configuration (zkp_driver.rs:
	/// 4970-5133) field for field, hand caps + scale profile incl.
	#[test]
	fn test_m104_clam_const_sane() {
		let proot = utils::os::proj_root();
		let abs = |p: &str| format!("{}/{}", proot, p);
		assert!(Path::new(&abs(CLAM.config_dir)).is_dir());
		for f in [CLAM.sig_file, "main_dfa.dat", "needs_ised.dat",
			"needs_ised_igc.dat"] {
			let p = abs(&format!("{}/{}", CLAM.config_dir, f));
			assert!(Path::new(&p).is_file(), "missing {}", p);
		}
		assert_eq!(CLAM.master_sources.len(), 8);
		let corpus: Vec<String> = CLAM.master_sources.iter()
			.flat_map(|s| read_path_list(s)).collect();
		assert_eq!(corpus.len(), 1209);
		for s in CLAM.scale_sources {
			assert!(Path::new(&abs(s)).is_file(), "missing {}", s);
		}
		let n = read_lines_nonblank(&abs(&format!("{}/{}",
			CLAM.config_dir, CLAM.sig_file))).len();
		assert_eq!(n, 38_875);
		assert_eq!(CLAM.name, "clam");
		assert!(!CLAM.b_aggressive);
		assert!(CLAM.b_check_lkup, "production runs the check");
		assert_eq!(CLAM.vec_decrease_level, &[2]);
		assert_eq!(CLAM.db_cache_dir, "clam_neo");
		assert_eq!(plan_dir(CLAM.name, 0), "/tmp/bora/clam_neo_p0");
		assert_eq!(CLAM.chunk_len, 4096);
		assert_eq!(CLAM.dry_chunk_len, Some(128));
		assert_eq!(CLAM.range2_bit, 26);
		assert_eq!(CLAM.dry_range2_bit, Some(22));
		assert_eq!(CLAM.fanout_cap, 127);     // untouched default
		assert_eq!(CLAM.min_pm_word_len, 4);  // untouched default
		assert_eq!((CLAM.n_par_snark, CLAM.n_par_snark_cp,
			CLAM.n_par_batch_claim), (1, 1, 8));
		assert_eq!((CLAM.min_subsigs, CLAM.min_basis_unique_states,
			CLAM.min_basis_acc_states, CLAM.min_basis_pats_in_trace,
			CLAM.min_avg_pats_per_subsig), (368, 1054, 268, 295, 8));
		assert_eq!((CLAM.min_dfa_sigs, CLAM.min_dfa_subsigs), (3, 3));
		let clam = CLAM;   // see the DNA note: const holds a Vec now
		let h = clam.hand_seed.as_ref().unwrap();
		assert_eq!((h.max_word_len, h.acdfa_state_part_bits),
			(4096, 26));
		assert_eq!((h.cp_basis_unique_states, h.cp_subsigs,
			h.cp_avg_pats), (1300, 580, 8));
		assert_eq!((h.subsigs, h.avg_pats_per_subsig,
			h.avg_active_pats_per_subsig), (580, 8, 2));
		assert_eq!((h.basis_pats_in_trace,
			h.perc_pats_expansion_rate), (820, 104));
		assert_eq!((h.sigs_sed, h.perc_comp_subsigs), (400, 20));
		assert_eq!((h.basis_unique_states, h.basis_acc_states),
			(1300, 750));
		assert_eq!((h.subsigs_igc, h.basis_pats_in_trace_igc,
			h.perc_pats_expansion_rate_igc, h.basis_acc_states_igc),
			(580, 820, 2, 750));
		assert_eq!((h.dfa_sigs, h.dfa_subsigs), (8, 8));
		let st = clam.scale_tune.as_ref().unwrap();
		assert_eq!((st.min_subsigs, st.min_basis_unique_states,
			st.min_basis_acc_states, st.min_basis_pats_in_trace,
			st.min_avg_pats_per_subsig), (64, 100, 2, 4, 1));
		assert_eq!((st.min_dfa_sigs, st.min_dfa_subsigs), (2, 2));
		let s = &st.hand_seed;
		assert_eq!((s.cp_basis_unique_states, s.cp_subsigs,
			s.subsigs, s.sigs_sed), (120, 64, 64, 64));
		assert_eq!((s.basis_unique_states, s.basis_acc_states,
			s.basis_pats_in_trace), (120, 2, 4));
		assert_eq!((s.perc_pats_expansion_rate,
			s.perc_pats_expansion_rate_igc), (104, 104));
		assert_eq!((s.dfa_sigs, s.dfa_subsigs), (2, 2));
		assert!(DLP.scale_tune.is_none());
		assert!(DNA.scale_tune.is_none());
	}

	/// M104: a >usize all-digit token (a hex pattern behind a ':')
	/// must NOT drop the sig at the unbounded sentinel; at any real
	/// bound it is conservatively dropped.
	#[test]
	fn test_m104_sig_fits_range_unbounded() {
		let monster =
			"N.m;E;0;123456789012345678901234567890:aa";
		assert!(sig_fits_range(monster, usize::MAX),
			"unbounded must keep every line");
		assert!(!sig_fits_range(monster, 1 << 26));
		assert!(sig_fits_range("N.x;E;0;50:abcd", usize::MAX));
		// the REAL sig set: unbounded keeps ALL 38,875 (the
		// byte-identical delegation promise for the lkup path).
		let proot = utils::os::proj_root();
		let lines = read_lines_nonblank(&format!("{}/{}/{}",
			proot, CLAM.config_dir, CLAM.sig_file));
		assert!(lines.iter().all(|l| sig_fits_range(l, usize::MAX)));
		// a real bound drops the monsters but keeps a large pool.
		let bound = (1usize << 26) - CLAM.chunk_len * 62;
		let pool = lines.iter()
			.filter(|l| sig_fits_range(l, bound)).count();
		assert_eq!(pool, 38_241);
	}

	/// M104: the CLAM scale clone applies the low Option A profile
	/// (floors + seed); DLP's clone (scale_tune None) is unchanged.
	#[test]
	fn test_m104_scale_spec_clone_tune() {
		let sc = scale_spec_clone(&CLAM);
		assert_eq!(sc.name, "clam_scale");
		assert_eq!(sc.db_cache_dir, "clam_neo_scale");
		assert!(!sc.b_check_lkup);
		assert!(sc.vec_decrease_level.is_empty(),
			"8.10g: the CLAM ladder must be emptied for scale");
		assert_eq!((sc.min_subsigs, sc.min_basis_unique_states,
			sc.min_basis_acc_states, sc.min_basis_pats_in_trace,
			sc.min_avg_pats_per_subsig), (64, 100, 2, 4, 1));
		assert_eq!((sc.min_dfa_sigs, sc.min_dfa_subsigs), (2, 2));
		assert_eq!(sc.hand_seed.as_ref().unwrap().subsigs, 64);
		assert_eq!(sc.chunk_len, CLAM.chunk_len);
		assert_eq!(sc.range2_bit, CLAM.range2_bit);
		assert_eq!(sc.n_par_batch_claim, 8);
		let sd = scale_spec_clone(&DLP);
		assert_eq!(sd.min_subsigs, DLP.min_subsigs);
		assert!(sd.hand_seed.is_none());
	}

	/// M104: light swaps in BOTH dry knobs (26/4096 -> 22/128);
	/// heavy keeps the REAL shape -- the cut is dry-run-ONLY, and
	/// effective_spec's light branch is its only consumer.
	#[test]
	fn test_m104_effective_spec_clam() {
		let d = effective_spec(&CLAM, true);
		assert_eq!((d.range2_bit, d.chunk_len), (22, 128));
		assert!(!d.b_check_lkup);
		let h = effective_spec(&CLAM, false);
		assert_eq!((h.range2_bit, h.chunk_len), (26, 4096),
			"full run must keep the REAL shape");
		assert!(h.b_check_lkup);
		// the scale clone preserves the same dry-only property.
		let sh = effective_spec(&scale_spec_clone(&CLAM), false);
		assert_eq!((sh.range2_bit, sh.chunk_len), (26, 4096));
	}

	/// M104: full_clam parses through the shared parse_full8;
	/// scale_clam takes the extra light token.
	#[test]
	fn test_m104_parse_clam() {
		assert_eq!(parse_args(&argv(&["full_clam", "0.5", "0.1",
			"2", "2", "1", "0", "1", "0"])),
			Cmd::FullClam { perc_db: 0.5, perc_samples: 0.1,
				num_circs: 2, num_jobs: 2, numa_num: 1, part_id: 0,
				b_dry_run: true, b_ladder_only: false });
		assert_eq!(parse_args(&argv(&["scale_clam", "1", "1,300",
			"1"])),
			Cmd::ScaleClam { corpus_idx: 1,
				vec_count: vec![1, 300], b_dry_run: true });
		// the token that gates BOTH dry shape and the 5% corpus cut:
		// a full sweep must parse it false (Python sends "0").
		assert_eq!(parse_args(&argv(&["scale_clam", "1", "1,300",
			"0"])),
			Cmd::ScaleClam { corpus_idx: 1,
				vec_count: vec![1, 300], b_dry_run: false });
	}

	#[test]
	#[should_panic(expected = "scale_clam takes 3 args")]
	fn test_m104_parse_scale_clam_arity() {
		parse_args(&argv(&["scale_clam", "0", "1,300"]));
	}

	/// M104 kernel: first CLAM execution of the non-aggr tuner --
	/// scale-clone shape (Option A floors/seed) at the dry chunk on
	/// a thinned real DB with the readelf corpus.
	#[test]
	fn test_m104_build_and_tune_tiny_clam() {
		let _g = cfg_lock();
		let proot = utils::os::proj_root();
		let mut spec =
			scale_spec_clone(&effective_spec(&CLAM, true));
		spec.name = "clam_test";     // /tmp/bora/clam_test_neo_p0
		spec.db_cache_dir = "clam_test_neo";
		let _t1 = TmpConfigDir(PathBuf::from(plan_dir(spec.name, 0)));
		let _t2 = TmpConfigDir(PathBuf::from(format!(
			"{}/data/cache/{}", proot, cache_dir_for(&spec, 0))));
		apply_spec_config(&spec, true, &part_role(0, 1, 1));
		let bins = vec![vec![spec.scale_sources[0].to_string()]];
		let caps = build_and_tune(&spec, 40, &bins, 1, 0);
		assert_eq!(caps.len(), 1, "non-aggr = single rung");
		let p = &caps[0];
		assert_eq!(p.max_word_len, 128);
		assert_eq!(p.acdfa_state_part_bits, 22);
		assert!(p.qm_real_rows >= 2, "converged qm (T604)");
		let c = read_global_config();
		assert_eq!(c.min_subsigs, p.subsigs);
		assert_eq!(c.perc_lkup_share, 1);
		assert!(c.b_pin_lkup_share);
	}

	/// M104: every CLAM scale source's DRY fragment must fit the dry
	/// range table -- the axis that panicked mid-fold when mis-sized.
	#[test]
	fn test_m104_dry_scale_fragment_fits_table() {
		let proot = utils::os::proj_root();
		let eff = effective_spec(&CLAM, true);
		let table = 1usize << eff.range2_bit;
		assert_eq!(CLAM.dry_scale_perc, 5.0);
		for s in CLAM.scale_sources {
			let n = fs::metadata(format!("{}/{}", proot, s))
				.unwrap_or_else(|e| panic!("scale source {}: {}", s, e))
				.len() as usize;
			let keep = (n as f64 * CLAM.dry_scale_perc / 100.0).ceil()
				as usize;
			assert!(keep * 2 + eff.chunk_len * 62 < table,
				"{}: dry fragment {} nibbles overflows 2^{} ({} B raw)",
				s, keep * 2, eff.range2_bit, n);
			assert!(n > keep, "{}: fragment is not a cut", s);
		}
	}

	/// M104: the pad constant really covers all 16 hex digits, which is
	/// the whole point of it (HexACDFA asserts alpha_size == 17).
	#[test]
	fn test_m104_alphabet_sig_covers_hex() {
		let digits: HashSet<char> = ALPHABET_SIG.split(';').skip(3)
			.flat_map(|p| p.chars()).collect();
		assert_eq!(digits.len(), 16, "pad must span all 16 nibbles");
		assert!(digits.iter().all(|c| c.is_ascii_hexdigit()));
		assert_eq!(ALPHABET_SIG.split(';').next(),
			Some("Win.Alphabet.SAMPLE-1"));
	}

	/// M104: thinning a source with no alphabet rule prepends the pad,
	/// so subset(n,1)'s index-0 pin is alphabet-complete.
	#[test]
	fn test_m104_alphabet_pad_when_absent() {
		let src = fresh_tmp_dir("padabs_src");
		let dst = fresh_tmp_dir("padabs_dst");
		write_fixture(&src, 20, "main.dat", false);
		let out = create_smaller_config(src.to_str().unwrap(),
			"main.dat", 1, dst.to_str().unwrap());
		let kept = read_lines_nonblank(&out);
		assert_eq!(kept, vec![ALPHABET_SIG.to_string()]);
		// count=5 keeps the pad plus 4 real sigs: label == line count.
		let dst2 = fresh_tmp_dir("padabs_dst2");
		let out2 = create_smaller_config(src.to_str().unwrap(),
			"main.dat", 5, dst2.to_str().unwrap());
		let k2 = read_lines_nonblank(&out2);
		assert_eq!(k2.len(), 5);
		assert_eq!(k2[0], ALPHABET_SIG);
	}

	/// M104: the pad is inert where the rule already exists (DLP/DNA)
	/// and inert when the whole DB is kept (count >= source len).
	#[test]
	fn test_m104_alphabet_pad_inert() {
		let proot = utils::os::proj_root();
		let src = format!("{}/{}", proot, DNA.config_dir);
		let td = fresh_tmp_dir("padinert");
		let out = create_smaller_config(&src, DNA.sig_file, 3,
			td.to_str().unwrap());
		let kept = read_lines_nonblank(&out);
		assert_eq!(kept.len(), 3);
		assert_eq!(kept.iter()
			.filter(|l| l.starts_with("Win.Alphabet")).count(), 1,
			"real alphabet rule must not be duplicated");
		assert!(kept[0].starts_with("Win.Alphabet"));

		let s2 = fresh_tmp_dir("padfull_src");
		let d2 = fresh_tmp_dir("padfull_dst");
		write_fixture(&s2, 12, "main.dat", false);
		let o2 = create_smaller_config(s2.to_str().unwrap(), "main.dat",
			12, d2.to_str().unwrap());
		let k2 = read_lines_nonblank(&o2);
		assert_eq!(k2.len(), 12, "count == len keeps every real sig");
		assert!(!k2.iter().any(|l| l.starts_with("Win.Alphabet")));
	}

	// ---------------- T9901 v5: demand-vector ladder ----------------

	/// qm_need = max(real, tot - wrap_b), saturating; the pooled
	/// CapErr guard inverted.
	#[test]
	fn test_v5_qm_need() {
		let q = |r, t, w| QmNeed { real: r, tot: t, wrap_b: w };
		assert_eq!(q(0, 0, 10).need(), 0);            // zero unit
		assert_eq!(q(60, 70, 25).need(), 60);         // real binds
		assert_eq!(q(90, 130, 25).need(), 105);       // pool binds
		assert_eq!(q(7, 12, 87).need(), 7);           // CLAM dry shape
		assert_eq!(q(1700, 2700, 1407).need(), 1700); // unit 443
	}

	/// DP: boundaries land on the demand jumps; uniform input collapses
	/// to one group; the 12-unit design example verbatim.
	#[test]
	fn test_v5_dp_partition() {
		let u = |pats: usize| (UnitVec { pats, ..Default::default() },
			1usize);
		let cost = |e: &UnitVec| e.pats;   // transparent stand-in
		// uniform -> 1 group regardless of k.
		let rows: Vec<_> = (0..10).map(|_| u(100)).collect();
		assert_eq!(dp_partition(&rows, 4, &cost), vec![10]);
		// design example A: bulk 100..300, tail 650/700, body
		// 1610..3000, outlier 14402 -> 4 groups at the jumps.
		let vals = [100, 150, 200, 250, 280, 300, 650, 700,
			1610, 2330, 3000, 14402];
		let rows: Vec<_> = vals.iter().map(|&v| u(v)).collect();
		assert_eq!(dp_partition(&rows, 4, &cost), vec![6, 8, 11, 12]);
	}

	/// Weighted dedup == the expanded multiset (DP invariance).
	#[test]
	fn test_v5_dp_weights() {
		let u = |p: usize, w: usize|
			(UnitVec { pats: p, ..Default::default() }, w);
		let cost = |e: &UnitVec| e.pats;
		let a = dp_partition(&[u(10, 5), u(1000, 1)], 2, &cost);
		let mut rows = vec![];
		for _ in 0..5 { rows.push(u(10, 1)); }
		rows.push(u(1000, 1));
		let b = dp_partition(&rows, 2, &cost);
		// same group STRUCTURE: {all 10s}{1000}.
		assert_eq!(a, vec![1, 2]);
		assert_eq!(b, vec![5, 6]);
	}

	/// Ceiling inversion: derived container >= count, exact at the
	/// boundary; plus the acc/pats structural floor and the qm floor.
	#[test]
	fn test_v5_rung_params_inversion() {
		let p_max = big_pmax_fixture();   // subsigs 2001, rates 9999
		let env = UnitVec { univ: 200, pats: 1991, uniq: 633,
			acc: 1263, cpu: 317, fwd: 3550, live: 100, active: 400,
			qm: [1700, 0] };
		let c = rung_params_from_env(&env, &p_max, true);
		let nlen = p_max.max_word_len * LEGS;
		assert!(nlen * c.basis_pats_in_trace / 10000 >= env.pats);
		assert!(nlen * c.basis_unique_states / 10000 >= env.uniq);
		assert!(nlen * c.basis_acc_states / 10000 >= env.acc);
		assert!(nlen * c.cp_basis_unique_states / 10000 >= env.cpu);
		assert!(c.basis_acc_states >= c.basis_pats_in_trace / 10 + 1);
		assert_eq!(c.subsigs, 201);
		assert_eq!(c.qm_real_rows, 1700);
		assert_eq!(c.qm_real_rows_igc, 2);    // floor, arm on
	}

	/// Sentinel: a 0 qm arm at P_max stays 0 on every rung; non-aggr
	/// keeps prod at 0 (a nonzero one flips the aggressive override).
	#[test]
	fn test_v5_rung_params_sentinel() {
		let mut p_max = big_pmax_fixture();
		p_max.qm_real_rows = 0;
		let env = UnitVec { qm: [500, 0], ..Default::default() };
		let c = rung_params_from_env(&env, &p_max, true);
		assert_eq!(c.qm_real_rows, 0);
		let _lk = cfg_lock();
		let mut q = big_pmax_fixture();
		q.prod_pats_expansion = 0;
		let n = rung_params_from_env(&env, &q, false);
		assert_eq!(n.prod_pats_expansion, 0, "non-aggr keeps prod 0");
		assert_eq!(n.subsigs, q.subsigs, "non-aggr carries subsigs");
	}

	/// Coverage: every unit fits its own group's rung on every
	/// arithmetic axis (the no-eviction invariant), 200 random units.
	#[test]
	fn test_v5_ladder_coverage() {
		// deterministic pseudo-random units (no Date/rand: LCG).
		let mut s = 12345usize;
		let mut units = vec![];
		for _ in 0..200 {
			s = s.wrapping_mul(1103515245).wrapping_add(12345);
			let r = |k: usize| (s >> k) % 1000;
			units.push(UnitVec { univ: r(3) % 50, pats: r(5),
				uniq: r(7), acc: r(9), cpu: r(11), fwd: r(13),
				live: r(15), active: r(17), qm: [r(19), 0] });
		}
		let p_max = big_pmax_fixture();
		let k = 4usize;
		let grps = group_units_v5(units.clone(), &p_max, k, true);
		assert!(!grps.is_empty() && grps.len() <= k,
			"<= K rungs, got {}", grps.len());
		let occ: usize = grps.iter().map(|g| occ_of(g)).sum();
		assert_eq!(occ, units.len(), "every unit is placed once");
		let nlen = p_max.max_word_len * LEGS;
		let mut prev = 0usize;
		for (gi, grp) in grps.iter().enumerate() {
			assert!(!grp.is_empty(), "rung {} is dead", gi);
			let c = if gi + 1 == grps.len() { p_max.clone() }
				else { rung_params_from_env(&env_of(grp), &p_max,
					true) };
			for (u, _) in grp.iter() {
				assert!(u.univ + 1 <= c.subsigs,
					"rung {}: univ {} > subsigs-1 {}", gi, u.univ,
					c.subsigs - 1);
				assert!(nlen * c.basis_pats_in_trace / 10000 >= u.pats,
					"rung {}: pats {}", gi, u.pats);
				assert!(nlen * c.basis_unique_states / 10000 >= u.uniq,
					"rung {}: uniq {}", gi, u.uniq);
				assert!(nlen * c.basis_acc_states / 10000 >= u.acc,
					"rung {}: acc {}", gi, u.acc);
				assert!(nlen * c.cp_basis_unique_states / 10000
					>= u.cpu, "rung {}: cpu {}", gi, u.cpu);
				assert!(c.qm_real_rows == 0
					|| u.qm[0] <= c.qm_real_rows,
					"rung {}: qm {} > {}", gi, u.qm[0],
					c.qm_real_rows);
			}
			let cost = rung_cost(&c);
			assert!(cost >= prev,
				"rung {} cost {} < previous {}", gi, cost, prev);
			prev = cost;
		}
	}

	/// CapParams.levels survives the save/load_ladder round trip and
	/// the SedCapacity carrier pops it TOP-FIRST, then exhausts.
	#[test]
	fn test_v5_levels_carrier() {
		let mut top = big_pmax_fixture();
		let mut l1 = top.clone();
		l1.basis_pats_in_trace = 100;
		top.levels = vec![l1.clone()];
		let dir = fresh_tmp_dir("v5levels");
		let path = dir.join("ladder.json");
		let p = path.to_str().unwrap();
		save_ladder(&vec![top.clone()], p).unwrap();
		let back = crate::determine_config::load_ladder(p);
		assert_eq!(back[0].levels.len(), 1);
		assert_eq!(back[0].levels[0].basis_pats_in_trace, 100);
		let (_, mut sed, _, _, _) = caps_from_params_general(&top);
		let lv = sed.next_level().expect("target installed");
		assert_eq!(lv.basis_pats_in_trace, 100);
		assert!(sed.next_level().is_none()); // exhausted -> legacy
		let _ = fs::remove_dir_all(&dir);
	}

	/// small_full_snark -- the Rust side of PAPER_DATA.py menu #2.
	///
	/// A deliberate COPY of zkp_driver's small_par_full_snark rather than a
	/// call into it: that function belongs to another workstream, and this
	/// menu entry must not change meaning when it is retuned there. Keep the
	/// capacities below in sync if small_data_par is ever retuned.
	///
	/// Two differences from the original:
	///   * DcMode::ProbeThenFold, not DcMode::Off -- determine_config runs
	///     the probe and then folds with the TUNED capacities, so the hand
	///     capacities below only SEED the probe rather than fixing the run.
	///   * b_folding_only is set EXPLICITLY. false is its GlobalConfig
	///     default, but that config is PROCESS-GLOBAL: an earlier test in
	///     the same `cargo test` process can leave it true, which would
	///     silently turn this into a folding-only run that emits no proof.
	///
	/// The three flags ARE the definition of this entry -- fold for real,
	/// full decider, exactly one proof (Job 0 only).
	fn small_full_snark(b_check_lkup: bool) {
		use crate::circs::cp_mapper::CpCapacity;
		use crate::circs::dfa_mapper::DfaCapacity;
		use crate::circs::sed_mapper::SedCapacity;

		utils::os::print_computer_config(Some("small_full_snark"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().b_light_test = false;   // full decider
		get_global_config().b_folding_only = false; // fold THEN prove
		get_global_config().b_one_proof = true;     // only Job 0 proves
		get_global_config().log_level = utils::logger::LOG3;

		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; // for dfa
		let max_word = 1;    // this is chunk_len
		let sigs = 2;        // good setting: 2
		let subsigs = 4;
		let avg_pats_per_subsig = 3;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 26;  // 26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 25*100;
		let basis_acc_states = 807;  // 6.46 percent
		let basis_pats_in_trace = 1500;
		let perc_pats_expansion_rate = 200;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap = DfaCapacity::new(max_word, sigs, subsigs);

		let scan_files: Vec<String> = (1..=4).map(|i|
			format!("{}/binexec_p{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(0,
			&format!("{}/sigs.dat", set1),
			scan_files,
			"data/small_data_set/reports/report.dat",
			b_write_cache,
			"small_20",
			&format!("{}/dfa.dat", set1),
			&format!("{}/ised.dat", set1),
			&format!("{}/ised_igc.dat", set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap,
			&init_sed_cap,
			&vec![],
			1,
			b_check_lkup, DcMode::ProbeThenFold
		);
	}

	/// PAPER_DATA.py menu #2 selects this by exact path:
	/// `cargo test -p zkregplus --release -- \
	///   bora_data_driver::tests_bora_data_driver::test_small_full_snark \
	///   --exact --nocapture`
	#[test]
	pub fn test_small_full_snark() {
		// small_full_snark writes the process-wide GlobalConfig.
		let _g = cfg_lock();
		small_full_snark(false);
	}
}
