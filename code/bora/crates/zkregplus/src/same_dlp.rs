//! same_dlp: the BORA side of the same-sample Zombie vs BORA job
//! (DLP_T1001). Child module of bora_data_driver (declared there via
//! #[path]), so it reuses that module's private pipeline pieces.

use std::path::Path;
use std::sync::Arc;

use ark_bn254::Fr;
use data_processor::clam_db::ClamavDB;
use data_processor::clamav::default_clamav_cfg;
use data_processor::discharge_proof::FailDischargeRecord;
use utils::consts::read_global_config;
use utils::logger::{emit_stdout, flush_logger};

use crate::determine_config::{save_ladder, CapParams};

use super::{apply_spec_config, arg_bool, arg_counts, arg_f64, arg_usize,
	build_fresh_db, cache_dir_for, cfg_paths, config_dir_for, count_of,
	create_smaller_config_bounded, discharge_for_tuning, effective_spec,
	fold, part_role, plan_dir, read_lines_nonblank, reset_part_dir, tune,
	write_job_manifests, Cmd, DatasetSpec, EstimateCapsGuard, DLP, USAGE};

/// DLP_T1001: DLP's literal with its own name, cache dir and the lookup check off.
pub const SAME_DLP: DatasetSpec = DatasetSpec {
	name: "dlp_same",
	config_dir: DLP.config_dir,
	sig_file: DLP.sig_file,
	master_sources: &[],
	scale_sources: &[],
	db_cache_dir: "dlp_same",
	chunk_len: DLP.chunk_len,
	dry_chunk_len: DLP.dry_chunk_len,
	range2_bit: DLP.range2_bit,
	dry_range2_bit: DLP.dry_range2_bit,
	dry_scale_perc: DLP.dry_scale_perc,
	fanout_cap: DLP.fanout_cap,
	min_pm_word_len: DLP.min_pm_word_len,
	b_aggressive: DLP.b_aggressive,
	b_check_lkup: false,
	vec_decrease_level: DLP.vec_decrease_level,
	rung0_scale: DLP.rung0_scale,
	n_par_snark: DLP.n_par_snark,
	n_par_snark_cp: DLP.n_par_snark_cp,
	n_par_batch_claim: DLP.n_par_batch_claim,
	min_subsigs: DLP.min_subsigs,
	min_basis_unique_states: DLP.min_basis_unique_states,
	min_basis_acc_states: DLP.min_basis_acc_states,
	min_basis_pats_in_trace: DLP.min_basis_pats_in_trace,
	min_avg_pats_per_subsig: DLP.min_avg_pats_per_subsig,
	min_dfa_sigs: DLP.min_dfa_sigs,
	min_dfa_subsigs: DLP.min_dfa_subsigs,
	hand_seed: None,
	log_level: DLP.log_level,
	scale_tune: None,
	b_fold_only: false,
	b_tune_v2: false,
};

/// DLP_T1001: the same-sample e-mail fixture, repo-relative.
pub const SAME_DLP_FIXTURE: &str =
	"data/src_sig/ms_dlp/docs/zombie_bugs/emails/fixture";

/// DLP_T1001: the sizes the fixture holds, one arm each.
const SAME_SIZES: [usize; 3] = [1000, 2000, 4000];

/// DLP_T1001: needs_max above this is a WARN (ZD's corpus prune cut).
const SAME_NEEDS_WARN: usize = 4000;

/// DLP_T1001: one SAME line, flushed so it orders against driver prints.
fn say(line: String) {
	emit_stdout(line);
	flush_logger();
}

/// DLP_T1001: argv[1..] of `same_dlp` -> Cmd::SameDlp.
pub(super) fn parse_same_dlp(args: &[String]) -> Cmd {
	assert!(args.len() == 7,
		"bora_data_driver: same_dlp takes 6 args, got {}\n{}",
		args.len() - 1, USAGE);
	let perc_db = arg_f64(args, 1, "perc_db");
	let num_circs = arg_usize(args, 2, "num_circs");
	let n = arg_usize(args, 3, "n");
	let b_dry_run = arg_bool(args, 4, "dry");
	let sizes = arg_counts(args, 5);
	let b_ladder_only = arg_bool(args, 6, "ladder_only");
	assert!(perc_db > 0.0 && perc_db <= 100.0,
		"bora_data_driver: same_dlp perc_db must be in (0, 100], got {}",
		perc_db);
	assert!(num_circs >= 1 && n >= 1,
		"bora_data_driver: same_dlp counts must be >= 1 \
		 (num_circs {} n {})", num_circs, n);
	for (i, s) in sizes.iter().enumerate() {
		assert!(SAME_SIZES.contains(s),
			"bora_data_driver: same_dlp size {} not in {:?}", s,
			SAME_SIZES);
		assert!(!sizes[..i].contains(s),
			"bora_data_driver: same_dlp duplicate size {}", s);
	}
	Cmd::SameDlp { perc_db, num_circs, n, b_dry_run, sizes,
		b_ladder_only }
}

/// DLP_T1001: picks (id, path) per size from ids.tsv text: arm == S,
/// sorted by id, first n. Panics if an arm has fewer than n.
fn pick_ids(tsv: &str, sizes: &[usize], n: usize)
	-> Vec<Vec<(String, String)>> {
	let rows: Vec<(String, usize)> = tsv.lines().skip(1)
		.filter(|l| !l.trim().is_empty())
		.map(|l| {
			let f: Vec<&str> = l.split('\t').collect();
			assert!(f.len() >= 4,
				"bora_data_driver: same_dlp bad ids.tsv row {:?}", l);
			(f[0].to_string(), f[3].parse().unwrap_or_else(|_| panic!(
				"bora_data_driver: same_dlp bad arm in {:?}", l)))
		}).collect();
	sizes.iter().map(|&s| {
		let mut ids: Vec<&String> = rows.iter()
			.filter(|(_, a)| *a == s).map(|(id, _)| id).collect();
		ids.sort();
		assert!(ids.len() >= n,
			"bora_data_driver: same_dlp arm {} has {} e-mails, need {}",
			s, ids.len(), n);
		ids.into_iter().take(n).map(|id| (id.clone(), format!(
			"{}/emails/padded/{}.eml", SAME_DLP_FIXTURE, id))).collect()
	}).collect()
}

/// DLP_T1001: one bin per size from the fixture; asserts n and that
/// every padded file is exactly the arm length.
pub(crate) fn same_bins(sizes: &[usize], n: usize)
	-> Vec<Vec<(String, String)>> {
	let proot = utils::os::proj_root();
	let tsv_path = format!("{}/{}/ids.tsv", proot, SAME_DLP_FIXTURE);
	let tsv = std::fs::read_to_string(&tsv_path).unwrap_or_else(|e|
		panic!("bora_data_driver: read {}: {}", tsv_path, e));
	let picked = pick_ids(&tsv, sizes, n);
	for (bin, &s) in picked.iter().zip(sizes) {
		assert_eq!(bin.len(), n,
			"bora_data_driver: same_dlp size {} bin len", s);
		for (_, p) in bin {
			let abs = format!("{}/{}", proot, p);
			let len = std::fs::metadata(&abs).map(|m| m.len())
				.unwrap_or_else(|e| panic!(
					"bora_data_driver: stat {}: {}", abs, e));
			assert_eq!(len, s as u64,
				"bora_data_driver: same_dlp {} is {} bytes, arm {}",
				p, len, s);
		}
	}
	picked
}

/// DLP_T1001: config path as build_or_load joins it (absolute as is).
fn abs_cfg_path(p: &str, proot: &str) -> String {
	if Path::new(p).is_absolute() { p.to_string() }
	else { format!("{}/{}", proot, p) }
}

/// DLP_T1001: the loaded DB's sig names must equal the sig file's.
fn names_check(sig_path: &str, db_names: &[&str]) {
	let want: Vec<String> = read_lines_nonblank(sig_path).iter()
		.map(|l| l.split(';').next().unwrap_or("").to_string())
		.collect();
	assert_eq!(want.len(), db_names.len(),
		"bora_data_driver: same_dlp names check: {} has {} sigs, \
		 cached DB {}", sig_path, want.len(), db_names.len());
	if let Some(i) = (0..want.len()).find(|&i| want[i] != db_names[i]) {
		panic!("bora_data_driver: same_dlp names check: sig {} is {:?} \
			in {}, {:?} in the cached DB", i, want[i], sig_path,
			db_names[i]);
	}
}

/// DLP_T1001: load the main DB read only when cached, else build our own.
fn same_db(spec: &DatasetSpec, cfg_dir: &str)
	-> (Arc<ClamavDB<Fr>>, String) {
	let main = cache_dir_for(&DLP, 0);
	if !ClamavDB::<Fr>::cache_exists(&main) {
		let own = cache_dir_for(spec, 0);
		say(format!("SAME db path build {}", own));
		return (build_fresh_db(spec, cfg_dir, &own), own);
	}
	say(format!("SAME db path load {}", main));
	let cfg = default_clamav_cfg();
	let mut vlog = vec![];
	let [sig, dfa, ised, ised_igc] = cfg_paths(spec, cfg_dir);
	let db = ClamavDB::<Fr>::build_or_load(&cfg, &sig, &dfa, &ised,
		&ised_igc, &mut vlog, &main, true, false)
		.unwrap_or_else(|e| panic!(
			"bora_data_driver: same_dlp load {}: {:?}", main, e));
	let names: Vec<&str> =
		db.vec_sigs.iter().map(|s| s.name.as_str()).collect();
	names_check(&abs_cfg_path(&sig, &utils::os::proj_root()), &names);
	(Arc::new(db), main)
}

/// DLP_T1001: the discharge lines for (id, is_fail, needs_max); Err
/// names the rejected ids.
fn discharge_lines(ids: &[String], recs: &[(bool, usize)])
	-> (Vec<String>, Result<(), String>) {
	assert_eq!(ids.len(), recs.len(),
		"bora_data_driver: same_dlp {} ids vs {} records", ids.len(),
		recs.len());
	let mut lines = vec![];
	let mut bad = vec![];
	for (id, &(fail, nm)) in ids.iter().zip(recs) {
		lines.push(format!("SAME discharge {} fail {} needs_max {}", id,
			fail, nm));
		if nm > SAME_NEEDS_WARN {
			lines.push(format!("SAME WARN needs_max {} > {} for {}", nm,
				SAME_NEEDS_WARN, id));
		}
		if fail { bad.push(id.clone()); }
	}
	let res = if bad.is_empty() { Ok(()) } else {
		lines.push(format!("SAME discharge rejected {}", bad.join(",")));
		Err(bad.join(","))
	};
	(lines, res)
}

/// DLP_T1001: per corpus word (the zero word is last, not printed).
fn same_discharge_check(ids: &[String], vdata: &[FailDischargeRecord])
	-> Result<(), String> {
	assert!(!vdata.is_empty(), "bora_data_driver: same_dlp no records");
	let recs: Vec<(bool, usize)> = vdata[..vdata.len() - 1].iter()
		.map(|v| (v.is_fail(), v.chunk_peaks.needs_per_chunk.iter()
			.copied().max().unwrap_or(0))).collect();
	let (lines, res) = discharge_lines(ids, &recs);
	for l in lines { emit_stdout(l); }
	flush_logger();
	res
}

/// DLP_T1001: build_and_tune with same_db and the discharge check.
fn same_build_and_tune(spec: &DatasetSpec, db_count: usize,
	n_sigs: usize, bins: &[Vec<String>], ids: &[String],
	num_circs: usize) -> (Vec<CapParams>, String) {
	assert!(read_global_config().clamav_cfg.b_use_discharge_neo,
		"bora_data_driver: apply_spec_config before same_build_and_tune");
	let proot = utils::os::proj_root();
	if db_count < n_sigs {
		create_smaller_config_bounded(
			&format!("{}/{}", proot, spec.config_dir), spec.sig_file,
			db_count, &format!("{}/config", plan_dir(spec.name, 0)),
			(1usize << spec.range2_bit) - spec.chunk_len * 62);
	}
	let (db, cache_dir) = same_db(spec,
		&config_dir_for(spec, db_count, n_sigs, 0));
	let _est = EstimateCapsGuard::on();
	let ts = discharge_for_tuning(spec, &db, bins);
	same_discharge_check(ids, &ts.vdata).unwrap_or_else(|e| panic!(
		"bora_data_driver: same_dlp discharge rejected: {}", e));
	(tune(spec, &db, &ts, num_circs), cache_dir)
}

/// DLP_T1001: hex sha256 of a file (coreutils; zkregplus has no sha2 dep).
fn sha256_file(path: &str) -> String {
	let out = std::process::Command::new("sha256sum").arg(path).output()
		.unwrap_or_else(|e| panic!("bora_data_driver: sha256sum: {}", e));
	assert!(out.status.success(), "bora_data_driver: sha256sum {}", path);
	String::from_utf8_lossy(&out.stdout).split_whitespace().next()
		.unwrap_or("").to_string()
}

/// DLP_T1001: begin marker of fold call i.
fn fold_begin_line(i: usize, size: usize, n: usize) -> String {
	format!("SAME fold begin i={} size={} n={}", i, size, n)
}

/// DLP_T1001: end marker of fold call i.
fn fold_end_line(i: usize) -> String {
	format!("SAME fold end i={}", i)
}

/// DLP_T1001: the same-sample BORA job, one one-job fold per size.
pub fn same_dlp_neo(perc_db: f64, num_circs: usize, n: usize,
	b_dry_run: bool, sizes: &[usize], b_ladder_only: bool)
	-> Vec<CapParams> {
	std::env::set_var("ZKR_LOG_TAG", "same_p0_");
	std::env::set_var("ZKR_DLP_PROBE_FILES", "1");
	let spec = &effective_spec(&SAME_DLP, b_dry_run, 100.0);
	assert!(!spec.b_check_lkup, "bora_data_driver: same_dlp lookup on");
	let role = part_role(0, 1, sizes.len());
	apply_spec_config(spec, b_dry_run, &role);
	let pd = reset_part_dir(spec, 0);
	let proot = utils::os::proj_root();
	let n_sigs = read_lines_nonblank(&format!("{}/{}/{}", proot,
		spec.config_dir, spec.sig_file)).len();
	let db_count = count_of(n_sigs, perc_db);
	assert!(!spec.b_aggressive || db_count >= 2,
		"bora_data_driver: same_dlp aggr db_count {} < 2", db_count);
	let picked = same_bins(sizes, n);
	let bins: Vec<Vec<String>> = picked.iter()
		.map(|b| b.iter().map(|(_, p)| p.clone()).collect()).collect();
	let ids: Vec<String> =
		picked.iter().flatten().map(|(id, _)| id.clone()).collect();
	let manifests = write_job_manifests(&format!("{}/jobs", pd), &bins);
	let (ladder, cache_dir) = same_build_and_tune(spec, db_count, n_sigs,
		&bins, &ids, num_circs);
	let lp = format!("{}/ladder.json", pd);
	save_ladder(&ladder, &lp).unwrap_or_else(|e| panic!(
		"bora_data_driver: save ladder: {}", e));
	say(format!("SAME ladder sha256 {}", sha256_file(&lp)));
	say("SAME lookup check OFF, share 1".to_string());
	if b_ladder_only { return ladder; }
	let cfg_dir = config_dir_for(spec, db_count, n_sigs, 0);
	for (i, &s) in sizes.iter().enumerate() {
		say(fold_begin_line(i, s, n));
		fold(spec, &cfg_dir, &cache_dir, &manifests[i..i + 1], &ladder,
			num_circs);
		flush_logger();
		say(fold_end_line(i));
	}
	ladder
}

#[cfg(test)]
mod tests_same_dlp {
	use super::*;
	use super::super::{parse_args, plan_dir, TmpConfigDir, DLP};

	fn argv(v: &[&str]) -> Vec<String> {
		v.iter().map(|s| s.to_string()).collect()
	}

	/// DLP_T1001: the dry and full argv shapes P sends parse.
	#[test]
	fn test_same_dlp_parse_ok() {
		assert_eq!(parse_args(&argv(&["same_dlp", "0.25", "2", "2", "1",
			"1000", "0"])),
			Cmd::SameDlp { perc_db: 0.25, num_circs: 2, n: 2,
				b_dry_run: true, sizes: vec![1000], b_ladder_only: false });
		assert_eq!(parse_args(&argv(&["same_dlp", "100", "4", "32", "0",
			"1000,2000,4000", "1"])),
			Cmd::SameDlp { perc_db: 100.0, num_circs: 4, n: 32,
				b_dry_run: false, sizes: vec![1000, 2000, 4000],
				b_ladder_only: true });
	}

	#[test]
	#[should_panic(expected = "same_dlp takes 6 args, got 5")]
	fn test_same_dlp_parse_arity() {
		parse_args(&argv(&["same_dlp", "100", "4", "32", "0", "1000"]));
	}

	#[test]
	#[should_panic(expected = "same_dlp size 3000 not in")]
	fn test_same_dlp_parse_bad_size() {
		parse_args(&argv(&["same_dlp", "100", "4", "32", "0",
			"1000,3000", "0"]));
	}

	#[test]
	#[should_panic(expected = "same_dlp duplicate size 1000")]
	fn test_same_dlp_parse_dup_size() {
		parse_args(&argv(&["same_dlp", "100", "4", "32", "0",
			"1000,2000,1000", "0"]));
	}

	#[test]
	#[should_panic(expected = "<dry> must be 0|1")]
	fn test_same_dlp_parse_bad_bool() {
		parse_args(&argv(&["same_dlp", "100", "4", "32", "2", "1000",
			"0"]));
	}

	/// DLP_T1001: SAME_DLP is DLP but for its own dirs, no corpus, no lookup check.
	#[test]
	fn test_same_dlp_spec_matches_dlp() {
		let (s, d) = (&SAME_DLP, &DLP);
		assert_eq!(plan_dir(s.name, 0), "/tmp/bora/dlp_same_neo_p0");
		assert_eq!(cache_dir_for(s, 0), "dlp_same_p0");
		assert_eq!(cache_dir_for(d, 0), "dlp_neo_p0");
		assert!(s.master_sources.is_empty() && s.scale_sources.is_empty());
		assert!(!s.b_check_lkup && !s.b_fold_only && !s.b_tune_v2);
		assert_eq!((s.config_dir, s.sig_file), (d.config_dir, d.sig_file));
		assert_eq!((s.chunk_len, s.dry_chunk_len, s.range2_bit,
			s.dry_range2_bit), (d.chunk_len, d.dry_chunk_len,
			d.range2_bit, d.dry_range2_bit));
		assert_eq!((s.fanout_cap, s.min_pm_word_len, s.b_aggressive),
			(d.fanout_cap, d.min_pm_word_len, d.b_aggressive));
		assert_eq!(s.vec_decrease_level, d.vec_decrease_level);
		assert!(s.rung0_scale.is_none() && d.rung0_scale.is_none());
		assert!(s.hand_seed.is_none() && d.hand_seed.is_none());
		assert!(s.scale_tune.is_none() && d.scale_tune.is_none());
		assert_eq!((s.n_par_snark, s.n_par_snark_cp, s.n_par_batch_claim),
			(d.n_par_snark, d.n_par_snark_cp, d.n_par_batch_claim));
		assert_eq!([s.min_subsigs, s.min_basis_unique_states,
			s.min_basis_acc_states, s.min_basis_pats_in_trace,
			s.min_avg_pats_per_subsig, s.min_dfa_sigs, s.min_dfa_subsigs,
			s.log_level], [d.min_subsigs, d.min_basis_unique_states,
			d.min_basis_acc_states, d.min_basis_pats_in_trace,
			d.min_avg_pats_per_subsig, d.min_dfa_sigs, d.min_dfa_subsigs,
			d.log_level]);
		// the lookup check never turns back on, dry or full
		assert!(!effective_spec(s, false, 100.0).b_check_lkup);
		assert!(!effective_spec(s, true, 100.0).b_check_lkup);
		// DLP itself is untouched by the new const
		assert!(d.b_check_lkup && d.name == "dlp");
	}

	/// DLP_T1001: picks arm == S, sorted by id, first n, padded path.
	#[test]
	fn test_same_pick_ids() {
		let tsv = "id\tsrc\tbytes\tarm\tsha\tsha_p\n\
			1000_02\ta\t1\t1000\tx\ty\n\
			2000_01\ta\t1\t2000\tx\ty\n\
			1000_01\ta\t1\t1000\tx\ty\n\
			1000_03\ta\t1\t1000\tx\ty\n";
		let p = pick_ids(tsv, &[2000, 1000], 1);
		let f = |id: &str| (id.to_string(), format!(
			"{}/emails/padded/{}.eml", SAME_DLP_FIXTURE, id));
		assert_eq!(p, vec![vec![f("2000_01")], vec![f("1000_01")]]);
		let p = pick_ids(tsv, &[1000], 2);
		assert_eq!(p, vec![vec![f("1000_01"), f("1000_02")]]);
	}

	#[test]
	#[should_panic(expected = "arm 2000 has 1 e-mails, need 2")]
	fn test_same_pick_ids_short_arm() {
		let tsv = "id\tsrc\tbytes\tarm\tsha\tsha_p\n\
			2000_01\ta\t1\t2000\tx\ty\n";
		pick_ids(tsv, &[2000], 2);
	}

	/// DLP_T1001: the real fixture gives 32 per size, exact arm length.
	#[test]
	fn test_same_bins_fixture() {
		let b = same_bins(&[1000, 2000, 4000], 32);
		assert_eq!(b.iter().map(|x| x.len()).collect::<Vec<_>>(),
			vec![32, 32, 32]);
		assert_eq!(b[0][0], ("1000_01".to_string(), format!(
			"{}/emails/padded/1000_01.eml", SAME_DLP_FIXTURE)));
		for (bin, s) in b.iter().zip([1000, 2000, 4000]) {
			assert!(bin.iter().all(|(id, _)| id.starts_with(
				&format!("{}_", s))));
			assert!(bin.windows(2).all(|w| w[0].0 < w[1].0));
		}
		let dry = same_bins(&[1000], 2);
		assert_eq!(dry, vec![b[0][..2].to_vec()]);
	}

	#[test]
	#[should_panic(expected = "arm 1000 has 32 e-mails, need 33")]
	fn test_same_bins_fixture_short() {
		same_bins(&[1000], 33);
	}

	/// DLP_T1001: temp sig file; the guard removes its dir, even on panic.
	fn tmp_sig(tag: &str, body: &str) -> (TmpConfigDir, String) {
		let d = std::env::temp_dir().join(format!("same_dlp_{}_{}", tag,
			std::process::id()));
		std::fs::create_dir_all(&d).unwrap();
		let p = d.join("sig.dat");
		std::fs::write(&p, body).unwrap();
		(TmpConfigDir(d), p.to_str().unwrap().to_string())
	}

	/// DLP_T1001: absolute paths pass through, relative ones join proj_root.
	#[test]
	fn test_same_abs_cfg_path() {
		assert_eq!(abs_cfg_path("/tmp/bora/dlp_same_neo_p0/config/s.dat",
			"/r"), "/tmp/bora/dlp_same_neo_p0/config/s.dat");
		assert_eq!(abs_cfg_path("data/paper_data/dlp/cfg/regex_pat/s.dat",
			"/r"), "/r/data/paper_data/dlp/cfg/regex_pat/s.dat");
	}

	/// DLP_T1001: names check passes on the real relative config path.
	#[test]
	fn test_same_names_check_real_relative() {
		let proot = utils::os::proj_root();
		let [sig, _, _, _] = cfg_paths(&SAME_DLP, SAME_DLP.config_dir);
		let p = abs_cfg_path(&sig, &proot);
		let names: Vec<String> = read_lines_nonblank(&p).iter()
			.map(|l| l.split(';').next().unwrap().to_string()).collect();
		let r: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
		names_check(&p, &r);
	}

	/// DLP_T1001: names check skips comments and blanks like build_db.
	#[test]
	fn test_same_names_check_pass() {
		let (_g, p) = tmp_sig("pass", "# c\nA;d;0;x\n\nB;d;0;y\n");
		names_check(&p, &["A", "B"]);
	}

	#[test]
	#[should_panic(expected = "sig 1 is \"B\"")]
	fn test_same_names_check_mismatch() {
		let (_g, p) = tmp_sig("bad", "A;d;0;x\nB;d;0;y\n");
		names_check(&p, &["A", "C"]);
	}

	#[test]
	#[should_panic(expected = "has 2 sigs, cached DB 3")]
	fn test_same_names_check_count() {
		let (_g, p) = tmp_sig("cnt", "A;d;0;x\nB;d;0;y\n");
		names_check(&p, &["A", "B", "C"]);
	}

	/// DLP_T1001: one line per word; any fail is Err and a rejected line.
	#[test]
	fn test_same_discharge_lines() {
		let ids: Vec<String> = vec!["1000_01".into(), "1000_02".into()];
		let (l, r) = discharge_lines(&ids, &[(false, 3), (false, 4001)]);
		assert!(r.is_ok());
		assert_eq!(l, vec![
			"SAME discharge 1000_01 fail false needs_max 3".to_string(),
			"SAME discharge 1000_02 fail false needs_max 4001".into(),
			"SAME WARN needs_max 4001 > 4000 for 1000_02".into()]);
		let (l, r) = discharge_lines(&ids, &[(true, 1), (false, 2)]);
		assert_eq!(r, Err("1000_01".to_string()));
		assert_eq!(l[0], "SAME discharge 1000_01 fail true needs_max 1");
		assert_eq!(l.last().unwrap(), "SAME discharge rejected 1000_01");
	}

	#[test]
	#[should_panic(expected = "2 ids vs 1 records")]
	fn test_same_discharge_lines_len() {
		let ids: Vec<String> = vec!["a".into(), "b".into()];
		let _ = discharge_lines(&ids, &[(false, 0)]);
	}

	/// DLP_T1001: marker text exactly as d9 3a parses it.
	#[test]
	fn test_same_fold_markers() {
		assert_eq!(fold_begin_line(1, 2000, 32),
			"SAME fold begin i=1 size=2000 n=32");
		assert_eq!(fold_end_line(1), "SAME fold end i=1");
	}

	/// DLP_T1001: sha256 helper agrees with a known digest.
	#[test]
	fn test_same_sha256_file() {
		let (_g, p) = tmp_sig("sha", "abc");
		assert_eq!(sha256_file(&p), "ba7816bf8f01cfea414140de5dae2223b00361a3\
			96177a9cb410ff61f20015ad");
	}
}
