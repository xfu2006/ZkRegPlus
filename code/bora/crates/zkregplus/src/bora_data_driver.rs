//! bora_data_driver: paper-data support functions, sibling to
//! zkp_driver. Hosts perc-parameterized dataset thinning and the
//! perc-driven Q2 lookup-composition report.

use std::collections::HashSet;
use std::fs;
use std::ops::Range;
use std::path::{Path, PathBuf};

use ark_bn254::Fr;
use data_processor::clam_db::ClamavDB;
use data_processor::clamav::default_clamav_cfg;
use utils::consts::get_global_config;

use crate::zkp_driver::{fmt_cross_rollup, fmt_dfa_cross};

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
fn count_of(n: usize, perc: usize) -> usize {
	assert!(n > 0, "bora_data_driver: count_of on an empty set");
	((n * perc + 99) / 100).clamp(1, n)
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

/// Deterministically thins src_dir's config down to `count` signatures,
/// writing a self-contained smaller config under dst_dir.
/// src_dir must contain sig_file_name, main_dfa.dat, needs_ised.dat,
/// needs_ised_igc.dat -- panics if any is missing. main_fanout.dat is
/// copied verbatim if present (optional, substring-matched so it can't
/// be meaningfully re-filtered). Returns the thinned sig file's path.
pub fn create_smaller_config(src_dir: &str, sig_file_name: &str,
	count: usize, dst_dir: &str) -> String {
	fs::create_dir_all(dst_dir).unwrap_or_else(|e|
		panic!("bora_data_driver: mkdir {}: {}", dst_dir, e));

	let sig_lines = read_lines_nonblank(
		&format!("{}/{}", src_dir, sig_file_name));
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

/// Plan dir for a dataset: derived state only (thinned config, job
/// manifests, ladder.json, PLAN_READY). Part 0 wipes it every run.
pub(crate) fn plan_dir(name: &str) -> String {
	format!("/tmp/bora/{}_neo", name)
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

/// One dataset's complete, immutable run configuration. Nobody ever
/// constructs one -- only the DLP/DNA/CLAM consts exist.
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
	/// Bit width of the range-2 lookup table.
	pub(crate) range2_bit: usize,
	/// SDE repetition fan-out cap (clamav_cfg.sde_rep_fanout_cap).
	pub(crate) fanout_cap: usize,
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
	range2_bit: 25,
	fanout_cap: 100,
	b_aggressive: true,
	b_check_lkup: false,
	vec_decrease_level: &[],
	// 1/1 = legacy full_dlp, which never sets these. Inert regardless:
	// the snark semaphores are taken past driver.rs' b_one_proof and
	// b_folding_only returns, so only one job ever contends.
	n_par_snark: 1,
	n_par_snark_cp: 1,
	min_subsigs: 1,
	min_basis_unique_states: 2,
	min_basis_acc_states: 2,
	min_basis_pats_in_trace: 4,
	min_avg_pats_per_subsig: 1,
	// 0/0 = legacy full_dlp (never set -> GLOBAL_CONFIG default), and
	// inert for DLP: its main_dfa.dat / needs_ised*.dat are empty.
	min_dfa_sigs: 0,
	min_dfa_subsigs: 0,
};

/// Config dir for a run: the real one when nothing is thinned, else the
/// thinned copy under the plan dir. Pure -- creates nothing.
#[allow(dead_code)] // read from B101 on
fn config_dir_for(spec: &DatasetSpec, db_count: usize,
	n_sigs: usize) -> String {
	if db_count >= n_sigs {
		spec.config_dir.to_string()
	} else {
		format!("{}/config", plan_dir(spec.name))
	}
}

/// One part's role in a numa_num-way split.
#[allow(dead_code)] // read from B101/C101 on
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
fn plan_corpus_from(master: &[String], perc_samples: usize,
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
		"bora_data_driver: corpus has zero total size (run DOWNLOAD.py?)");
	split_paths_balanced(files, num_jobs)
}

/// Corpus bins for one run: concat the spec's master lists, sample, and
/// split size-balanced into num_jobs bins.
#[allow(dead_code)] // read from C101 on
pub(crate) fn plan_corpus(spec: &DatasetSpec, perc_samples: usize,
	num_jobs: usize) -> Vec<Vec<String>> {
	let master: Vec<String> = spec.master_sources.iter()
		.flat_map(|s| read_path_list(s)).collect();
	plan_corpus_from(&master, perc_samples, num_jobs)
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
	let cfg = default_clamav_cfg();

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
		}

		let (build_dir, sig_path, tmp_guard):
			(String, String, Option<TmpConfigDir>) = if perc >= 100 {
			(src_dir.clone(), format!("{}/{}", src_dir, sig_file_name), None)
		} else {
			let tmp = format!("/tmp/bora/lkup_adv_{}_{}",
				std::process::id(), name);
			let n_sigs = read_lines_nonblank(
				&format!("{}/{}", src_dir, sig_file_name)).len();
			let sig_path = create_smaller_config(src_dir, sig_file_name,
				count_of(n_sigs, perc), &tmp);
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

#[cfg(test)]
pub mod tests_bora_data_driver {
	use super::*;
	use std::sync::atomic::{AtomicUsize, Ordering};

	static COUNTER: AtomicUsize = AtomicUsize::new(0);

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
			count_of(20, 100), dst.to_str().unwrap());
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
			count_of(37, 30), dst1.to_str().unwrap());
		create_smaller_config(src.to_str().unwrap(), "main.dat",
			count_of(37, 30), dst2.to_str().unwrap());
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
			count_of(50, 20), dst.to_str().unwrap());

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
			"main_data_dlp_internationl.dat", count_of(10, 50),
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
		let d = plan_dir("dlp");
		assert_eq!(d, "/tmp/bora/dlp_neo");
		assert!(Path::new(&d).is_absolute());
		assert!(d.starts_with("/tmp/bora/") && d.len() > "/tmp/bora/".len(),
			"plan dir must be a strict subdir of /tmp/bora: {}", d);
		assert_eq!(plan_dir("clam"), "/tmp/bora/clam_neo");
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
		assert_eq!(plan_dir(DLP.name), "/tmp/bora/dlp_neo");

		// 4. legacy full_dlp() parity, field by field.
		assert_eq!(DLP.chunk_len, 64);
		assert_eq!(DLP.range2_bit, 25);
		assert_eq!(DLP.fanout_cap, 100);
		assert!(DLP.b_aggressive);
		assert!(!DLP.b_check_lkup);
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
		assert_eq!(count_of(9861, 100), 9861);
		assert_eq!(count_of(9861, 10), 987);
		assert_eq!(count_of(9861, 1), 99);
		assert_eq!(count_of(9861, 0), 1);       // documented floor
		assert_eq!(count_of(9861, 200), 9861);  // capped at n
		assert_eq!(count_of(10, 25), 3);        // ceil, not floor
		assert_eq!(count_of(1, 100), 1);
	}

	#[test]
	#[should_panic(expected = "count_of on an empty set")]
	fn test_a103_count_of_empty_panics() {
		count_of(0, 50);
	}

	#[test]
	fn test_a103_config_dir_for() {
		assert_eq!(config_dir_for(&DLP, 9861, 9861), DLP.config_dir);
		assert_eq!(config_dir_for(&DLP, 99, 9861),
			"/tmp/bora/dlp_neo/config");
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
		let bins = plan_corpus_from(&master, 50, 4);
		assert_eq!(bins.len(), 4);
		let flat: Vec<&String> = bins.iter().flatten().collect();
		assert_eq!(flat.len(), 10);             // count_of(20, 50)
		let kept: HashSet<&String> = flat.into_iter().collect();
		assert_eq!(kept.len(), 10, "no duplicates across bins");
		assert!(kept.contains(&master[0]), "file 0 pinned");
		assert!(kept.iter().all(|p| master.contains(p)));
		assert_eq!(plan_corpus_from(&master, 50, 4), bins);
	}

	#[test]
	#[should_panic(expected = "zero total size")]
	fn test_a103_plan_corpus_from_rejects_missing_files() {
		let ghost: Vec<String> =
			(0..4).map(|i| format!("data/no_such_file_{}", i)).collect();
		plan_corpus_from(&ghost, 100, 2);
	}
}
