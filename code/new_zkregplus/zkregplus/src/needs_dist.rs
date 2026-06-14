//! Per-chunk NEEDS distribution study (aggressive SDE mode only).
//! NEEDS = per-chunk count of universe subsigs whose keyword anchor is
//! present -- the binding aggressive ZK-cost knob. These helpers keep the
//! full per-chunk profile (not just the file max) and summarize it.

use ark_ff::PrimeField;
use rayon::prelude::*;
use data_processor::clam_db::ClamavDB;
use data_processor::type_def::ClamavApproxConfig;
use data_processor::clamav::quick_discharge_file_by_crit_bag_pm;
use utils::os::{read_nibbles, write_lines};
use utils::consts::read_global_config;

/// (1) Per-chunk NEEDS for one file. fpath is relative to proot. Requires
/// the aggressive flag (else chunk_peaks.needs_per_chunk is empty).
pub fn file_needs_per_chunk<F: PrimeField>(fpath: &str, proot: &str,
	db: &ClamavDB<F>, cfg: &ClamavApproxConfig, mw: usize) -> Vec<usize> {
	let nibbles = read_nibbles(&format!("{}/{}", proot, fpath));
	//empty/1-nibble files have no NEEDS and would panic the shared
	//discharge (ilog2(0) at clamav.rs file_len). Skip -> no chunks.
	if nibbles.len() < 2 { return vec![]; }
	let (fdr, _rec) = quick_discharge_file_by_crit_bag_pm(
		fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
		&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
		&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
		&db.bundle_subsig_igc.vec_acdfa[0], true, cfg,
		&db.sig_to_id, mw, mw);
	fdr.chunk_peaks.needs_per_chunk
}

/// (2) Per-chunk NEEDS for many files (2D: file -> per-chunk array).
/// Hard-requires the aggressive flag (db must be built aggressive).
pub fn collect_needs_per_chunk<F: PrimeField + Send + Sync>(
	files: &[String], proot: &str, db: &ClamavDB<F>,
	cfg: &ClamavApproxConfig, mw: usize) -> Vec<Vec<usize>> {
	assert!(read_global_config().clamav_cfg.b_aggressive_sde_for_rep,
		"needs_dist requires b_aggressive_sde_for_rep (build db aggressive)");
	files.par_iter()
		.map(|f| file_needs_per_chunk(f, proot, db, cfg, mw))
		.collect()
}

/// (3) Discharge `files`, then print the NEEDS distribution (top-10% file
/// view + pooled all-chunks view). Self-contained convenience wrapper.
pub fn print_needs_distribution<F: PrimeField + Send + Sync>(
	files: &[String], proot: &str, db: &ClamavDB<F>,
	cfg: &ClamavApproxConfig, mw: usize) {
	let rows = collect_needs_per_chunk(files, proot, db, cfg, mw);
	print_needs_dist_rows(&rows, files);
}

/// percentile of an ascending-sorted slice; q in permille (0..=1000).
fn pct(sorted: &[usize], q: usize) -> usize {
	if sorted.is_empty() { 0 }
	else { sorted[(q*(sorted.len()-1))/1000] }
}

fn median(xs: &mut Vec<f64>) -> f64 {
	if xs.is_empty() { return 0.0; }
	xs.sort_by(|a,b| a.partial_cmp(b).unwrap());
	xs[xs.len()/2]
}

/// Print the distribution from precomputed per-file per-chunk NEEDS rows
/// (rows[i] aligns with fnames[i]). Lets a caller that already discharged
/// (e.g. full_dlp_sample3) reuse its data without a second pass.
pub fn print_needs_dist_rows(rows: &Vec<Vec<usize>>, fnames: &[String]) {
	let mut v: Vec<String> = vec![];
	macro_rules! pl { ($($a:tt)*) => {{
		let s = format!($($a)*); println!("{}", s); v.push(s); }}; }

	let n_files = rows.len();
	pl!("=== NEEDS distribution: {} files ===", n_files);

	let mut pool: Vec<usize> = rows.iter().flatten().copied().collect();
	let total = pool.len();
	if total == 0 {
		pl!("no chunks (empty corpus or all files single empty)");
		write_lines("data/paper_data/dlp/report/needs_dist_report.txt", &v, true);
		return;
	}
	pool.sort_unstable();
	let zero = pool.iter().take_while(|&&x| x==0).count();
	let nz: Vec<usize> = pool[zero..].to_vec(); //ascending nonzero
	let maxv = pool[total-1];
	let p90_global = pct(&pool, 900);
	let hi_thresh = 4*maxv/5;

	// ---- View A: per-file, top 10% by max NEEDS ----
	let mut fmax: Vec<(usize,usize)> = rows.iter().enumerate()
		.map(|(i,r)| (i, r.iter().copied().max().unwrap_or(0))).collect();
	fmax.sort_by(|a,b| b.1.cmp(&a.1)); //desc by file max
	let k = ((n_files + 9) / 10).max(1).min(n_files);
	pl!("");
	pl!("-- View A: top {} files (10%) by max NEEDS --", k);
	pl!("global p90(all chunks)={}  hi_thresh(4*MAX/5)={}  MAX={}",
		p90_global, hi_thresh, maxv);

	let cnt_ge = |r: &Vec<usize>, t: usize|
		r.iter().filter(|&&x| x>0 && x>=t).count();
	let (mut r90, mut rhi) = (vec![], vec![]);
	let mut nch_sum = 0usize;
	for &(i,_) in fmax[..k].iter() {
		let r = &rows[i];
		let nc = r.len().max(1);
		r90.push(cnt_ge(r, p90_global) as f64 / nc as f64);
		rhi.push(cnt_ge(r, hi_thresh) as f64 / nc as f64);
		nch_sum += r.len();
	}
	let (med90, medhi) = (median(&mut r90.clone()), median(&mut rhi.clone()));
	let mn = |xs:&[f64]| xs.iter().cloned().fold(f64::INFINITY,f64::min);
	let mx = |xs:&[f64]| xs.iter().cloned().fold(0.0f64,f64::max);
	pl!("ratio_ge_p90 (chunks>=p90 / file chunks): min={:.3} med={:.3} \
		max={:.3}", mn(&r90), med90, mx(&r90));
	pl!("ratio_hi     (chunks>=hi  / file chunks): min={:.3} med={:.3} \
		max={:.3}", mn(&rhi), medhi, mx(&rhi));
	pl!("mean chunks/file (cohort) = {:.1}", nch_sum as f64 / k as f64);
	pl!("worst {} files (by max NEEDS):", 10.min(k));
	pl!("  {:<42} {:>7} {:>9} {:>8} {:>8}",
		"file", "chunks", "maxNEEDS", "r>=p90", "r_hi");
	for &(i,mxn) in fmax[..k.min(10)].iter() {
		let r = &rows[i];
		let nc = r.len().max(1);
		let name = fnames.get(i).map(|s| s.as_str()).unwrap_or("?");
		let short = if name.len()>42 {&name[name.len()-42..]} else {name};
		pl!("  {:<42} {:>7} {:>9} {:>8.3} {:>8.3}", short, r.len(), mxn,
			cnt_ge(r,p90_global) as f64/nc as f64,
			cnt_ge(r,hi_thresh) as f64/nc as f64);
	}

	// ---- File-level cut table: drop a file if its max-chunk NEEDS > T ----
	let fmaxes: Vec<usize> = rows.iter()
		.map(|r| r.iter().copied().max().unwrap_or(0)).collect();
	pl!("");
	pl!("-- File cut table (remove file if its max-chunk NEEDS > T) --");
	for &t in &[0usize,1000,2840,3500,4500,5680,8520,11360,14199]{
		let rem = fmaxes.iter().filter(|&&m| m > t).count();
		pl!("  T={:>6}: remove {:>7} of {} files ({:.4}%)",
			t, rem, n_files, 100.0*rem as f64/n_files.max(1) as f64);
	}

	// ---- View B: all chunks pooled ----
	let pc = |c: usize| 100.0*c as f64/total as f64;
	pl!("");
	pl!("-- View B: all chunks pooled --");
	pl!("total_chunks={}  zero={} ({:.1}%)  nonzero={} ({:.1}%)",
		total, zero, pc(zero), nz.len(), pc(nz.len()));
	pl!("nonzero percentiles: p50={} p80={} p90={} p95={} p99={} \
		p99.9={} MAX={}", pct(&nz,500), pct(&nz,800), pct(&nz,900),
		pct(&nz,950), pct(&nz,990), pct(&nz,999), maxv);
	pl!("5-bucket histogram over (0, MAX={}]:", maxv);
	pl!("  zeros{:>28}  {:>10}  ({:.1}% all)", "", zero, pc(zero));
	let w = ((maxv + 4) / 5).max(1); //ceil(MAX/5)
	let nz_n = nz.len().max(1);
	for b in 0..5 {
		let lo = b*w + 1;
		let hi = ((b+1)*w).min(maxv);
		if lo > maxv { break; }
		let cnt = nz.iter().filter(|&&x| x>=lo && x<=hi).count();
		pl!("  [{:>7}, {:>7}]  {:>10}  ({:.2}% all, {:.2}% nz)",
			lo, hi, cnt, pc(cnt), 100.0*cnt as f64/nz_n as f64);
	}

	write_lines("data/paper_data/dlp/report/needs_dist_report.txt", &v, true);
	println!("[needs_dist] report -> /tmp/needs_dist_report.txt");
}
