/* ZkregPlus Main Driver
	Created: 01/31/2025
*/

//use std::collections::{HashSet};
use utils::{logger::{log,LOG1,log_perf}, timer::Timer as GTimer, consts::{read_global_config, get_global_config, ClamReadMode}};
use ark_ff::{Field,PrimeField,ToConstraintField};
use ark_ec::{Group, CurveGroup,
	pairing::{Pairing},
	short_weierstrass::SWCurveConfig
};
use ark_r1cs_std::{
	prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	ToConstraintFieldGadget,
};
use ark_snark::SNARK;
use ark_crypto_primitives::sponge::{
	poseidon::PoseidonConfig,
	Absorb,
};
use folding_schemes::folding::foldpot::container_config::ColEle;
use utils::{
	os::{proj_root, read_lines,read_nibbles,
//		read,write_to_file
	},
	data::{pack_nibbles}
};
use data_processor::{
	clamav::{default_clamav_cfg, quick_discharge_file_by_crit_bag_pm},
	clam_db::{ClamavDB},
	discharge_proof::FailDischargeRecord,
	type_def::ClamavApproxConfig,
};
use folding_schemes::{
	transcript::poseidon::poseidon_canonical_config,
	commitment::{
		kzg::{Proof as KZGProof },
		pedersen::Params as PedersenParams,
		CommitmentScheme,
	},
	folding::{
		circuits::{CF1, CF2, CF3},
		foldpot::{
			sigma_ir1cs::{LookupTableTwoCol_Inst,SigmaIR1CS_Inst,WordInfo,SigmaIR1CS,LookupTableTwoCol},
			from_field::{AffineFromField},
			driver::{foldpot_main, FoldPotJob},
		}
	}
};
use std::sync::{Arc, Mutex};
use crate::circs::{
	composable_gadget_mapper::{CompositeGadgetMapper},
	cp_mapper::{CpComponentMapper,CpCapacity},
	sed_mapper::{SedComponentMapper,SedCapacity},
	dfa_mapper::{DfaComponentMapper,DfaCapacity},
};
use crate::gadgets::word_extract::LEGS;

use rayon::prelude::*;


// --------- type aliases for zkp_driver below -------------
type LK<F> = LookupTableTwoCol_Inst<F>;
type GM<F> = CompositeGadgetMapper<F,LK<F>>;
type FC<F,C,CS> = SigmaIR1CS_Inst<F,C,CS,LK<F>,GM<F>,false>;
// --------- type aliases for zkp_driver above -------------

/// Take the first pct% of a manifest's file list (deterministic, on-disk
/// order). pct=100 returns the whole list (byte-identical for non-split
/// callers, e.g. full_dlp); pct<100 is the debug/numa speed mode.
fn clam_take_pct(all_names: &[String]) -> Vec<String> {
	let pct = read_global_config().clam_read_pct;
	let k = (all_names.len() * pct / 100).min(all_names.len());
	all_names[..k].to_vec()
}

/// Parse the job index j from a manifest path .../binexec_p{j}.dat so the
/// PROBE lines carry the GLOBAL manifest id (part2 reports jobs 4-7, not
/// 0-3). Returns the fallback job_id for non-binexec paths.
fn clam_manifest_idx(path: &str, fallback: usize) -> usize {
	path.rsplit('/').next().unwrap_or(path)
		.strip_prefix("binexec_p").and_then(|s| s.strip_suffix(".dat"))
		.and_then(|s| s.parse::<usize>().ok()).unwrap_or(fallback)
}

/// Parse the GLOBAL job index i from a full_dlp split path .../job_{i}.dat
/// so the two-half PROBE DLP lines report jobs 0..h-1 (part1) and h..N-1
/// (part2). Returns the fallback for non job_ paths.
fn dlp_job_idx(path: &str, fallback: usize) -> usize {
	path.rsplit('/').next().unwrap_or(path)
		.strip_prefix("job_").and_then(|s| s.strip_suffix(".dat"))
		.and_then(|s| s.parse::<usize>().ok()).unwrap_or(fallback)
}

/// load the files and pack them as nibbles
/// return (words in packed nibbles, word info, file names)
/// max_word_len is forwarded into the discharge_prover so it can
/// extend its nibble scan to match the circuit's padded view
/// (Step 4 of the pad-invariant rework).
/// Returns (packed words, WordInfo, file names, FailDischargeRecord). The 4th
/// is the per-file discharge record the aggressive tuner needs; it is produced
/// here anyway and was previously dropped. Its ChunkPeaks profiles are only
/// populated when b_estimate_caps is on (clamav.rs:3376), so callers that do
/// not tune get the same empty-profile records at no extra cost.
fn load_files<F:PrimeField + ColEle>(job_id: usize, list_file_path: &str, db: &ClamavDB<F>, cfg:&ClamavApproxConfig, _b_write_cache: bool, _cache_dir: &str, max_word_len: usize)
	->(Vec<Vec<F>>, Vec<WordInfo>, Vec<String>, Vec<FailDischargeRecord>){
	//1. read the list of files
	let _b_debug = false;
	let proot = proj_root();
	// absolute paths (e.g. /tmp/bora/scale corpus) are used as-is; relative
	// ones are proot-prefixed. Same guard as clam_db::build_or_load.
	let resolve = |p: &str| if std::path::Path::new(p).is_absolute()
		{ p.to_string() } else { format!("{}/{}", proot, p) };
	// full_clam two-half scheme: the split is by whole manifest (job), so
	// here we keep the FULL list and only trim to pct% for the debug/numa
	// speed mode (Full/100 = whole list, byte-identical for full_dlp/bare).
	let all_names = read_lines(&resolve(list_file_path));
	let file_names_owned = clam_take_pct(&all_names);
	let file_names = &file_names_owned;
	let (pmode, ppct) = { let g = read_global_config();
		(g.clam_read_mode, g.clam_read_pct) };
	if pmode != ClamReadMode::Full || ppct != 100 {   // quiet for full_dlp/bare
		// Dump the exact files this job processes so the driver can check
		// that the two parts together emit all 8 manifests' files. The job
		// id is the GLOBAL manifest index (binexec_p{j}) so part2 reports
		// jobs 4-7. One self-contained line per file (parses interleaved).
		let mj = clam_manifest_idx(list_file_path, job_id);
		println!("PROBE FILES job {} mode {:?} pct {} n {} took {}",
			mj, pmode, ppct, all_names.len(), file_names.len());
		for f in file_names {
			println!("PROBE FILE job {} {}", mj, f);
		}
	}
	// full_dlp two-half scheme: one summary line per job (global id parsed
	// from job_{i}.dat) so the driver can confirm part1 folded jobs 0..h-1
	// and part2 folded h..N-1, with no per-job file trimming. Unset env =>
	// silent (bare cargo test / clam unaffected). File-level coverage is
	// checked by the driver against the on-disk job_{i}.dat split.
	if std::env::var("ZKR_DLP_PROBE_FILES").map(|v| v == "1")
		.unwrap_or(false) {
		println!("PROBE DLP job {} n {}",
			dlp_job_idx(list_file_path, job_id), file_names.len());
	}
	if file_names.len() > 0 {
		println!("  First file: {}", file_names[0]);
	}

	//2. parallel for each file read its nibbles and convert
	let final_data = file_names.into_par_iter().map(|fpath|
	{
		let nibbles = read_nibbles(&resolve(fpath));
		let f_nibbles = nibbles.into_iter().map(|x| F::from(x as u32))
			.collect::<Vec<F>>();
		let packed = pack_nibbles(&f_nibbles);
		packed
	}).collect::<Vec<Vec<F>>>();

	//let sdir = format!("{}/data/cache/{}/", &proj_root(), cache_dir);
	/* DON'T - as each new bin-exec pack will cause loading outdated
	let vec_word_info= 
		cache
		if b_read_cache{
		let s_wi= read(&format!("{}/vec_word_info.txt", sdir));
		let vec_word_info:Vec<WordInfo> = serde_json::from_str(&s_wi)
				.expect("Convert vec_sigs fails");
		vec_word_info
	}else{
	*/
	let vec_wi_vd: Vec<(WordInfo, FailDischargeRecord)> =
		file_names.into_par_iter().map(|fpath|
		{
			let abspath = resolve(fpath);
			let nibbles = read_nibbles(&abspath);
			let (fail_info, rec) = quick_discharge_file_by_crit_bag_pm(
				fpath,
				&nibbles,
				&db.vec_sigs,
				&db.vec_sigs_no_critical_pat,
				&db.map_crit_pat,
				&db.map_crit_pat_igc,
				&db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], //dfa_patterns,
				&db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], //dfa_patterns_igc,
				true, cfg,
				&db.sig_to_id, max_word_len, max_word_len);//optimize
			if !rec.is_success(){
				println!("FAILED discharging file: {} on sigs: {:?}",
					fail_info.fname,
					fail_info.all_dfa);
				println!(" -- word_info: {:?}", rec.vec_ised_sigs);
			}
			assert!(rec.is_success());
			assert!(!fail_info.is_fail());
			(rec, fail_info)
		}).collect::<Vec<(WordInfo, FailDischargeRecord)>>();
	let (vec_word_info, vec_vdata): (Vec<WordInfo>, Vec<FailDischargeRecord>)
		= vec_wi_vd.into_iter().unzip();

		/*
		if b_write_cache{
			let s_wi = serde_json::to_string(&vec_word_info).unwrap();
			write_to_file(&format!("{}/vec_word_info.txt", &sdir), &s_wi);
		}
		vec_word_info
	};
	*/

	(final_data, vec_word_info, file_names.clone(), vec_vdata)
}


/// build the circuits. Notice that we keep the legacy layered circuit
/// model (see driver.rs in foldpot module). However, we make the
/// simplication that 
/// *** EACH LAYER has ONE CIRC ***
///
/// Return: 2d layer of circs, but each layer has 1 circ. (2d is just
///  for legacy reason)
/// It's arranged from low cost to high cost so that the first
/// circ satisfying a certain capacity will be the best one.
/// vec_decrease_level allows 1, or 2, to be passed,
/// its length should be num_circs - 1 (we use these levels)
/// to call decrease_copy of capacity for the next circ
/// Eventually list of circs will be sorted in ascending order
#[allow(dead_code)]
pub(crate) fn build_circs_adv<F,C,CS>(
	poseidon_config: &PoseidonConfig<F>,
	total_word_n: usize, //sum of word length, each word is packed,
						//e.g., every 62 nibbles count as 1 in length (packed)
						//e.g., two words each 124 bytes means total_word_n
						// is 8 because each word has 248 nibbles, and
						// they are packed into 4 Fr each (containing 62 
						// nibbles)
	chunk_len: usize, //it's also counted in packed length (62 nibbles per
					  //1 char in word).
					  //e.g., given LEGS = 62 for bn254, it means 
					  //chunk length is 62 nibbles * 4-bits.
					  //e.g., chunk_len:1024 means 31kb actual chunk length.
					  //for 128kb chunk length it's chunk_len is 4130.
	lkup_len: usize,
	db: Arc<ClamavDB<F>>,
	init_cp_capacity_cs: &CpCapacity,
	init_sed_capacity_cs: &SedCapacity,
	init_dfa_capacity: &DfaCapacity, //no cs/igc distinction
	init_cp_capacity_igc: &CpCapacity,
	init_sed_capacity_igc: &SedCapacity,
	vec_decrease_level: &Vec<usize>, //decrease levels
	n_circs: usize,
	b_check_lkup: bool
)->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle + ColEle,
{
	//1. check the seed capacity consistency with the info
	assert!(init_cp_capacity_cs.max_word_len == chunk_len);
	assert!(init_cp_capacity_igc.max_word_len == chunk_len);
	assert!(init_sed_capacity_cs.wea_capacity().max_word_len == chunk_len);
	assert!(init_sed_capacity_igc.wea_capacity().max_word_len == chunk_len);
	assert!(init_dfa_capacity.wea_capacity().max_word_len == chunk_len);

	//2. given fixed chunk_len and total_word_len computes the
	//lkup_share needed to build up circuit
	//HERE: we use the global_config.perc_share_size to determine
	//the lkup size. if b_check_lkup is true, we make sure that it's large
	//enough (and later in circuit, it WILL perform the check in circ,
	//if malicious prover fake here, it will fail the circ eventually).
	let max_nibble_len = chunk_len * LEGS; //31 nibbles per 
	let total_nibbles = total_word_n * LEGS;
	let chunks = total_nibbles/max_nibble_len;
	let lk_share = read_global_config().perc_lkup_share* max_nibble_len/100;
	let lk_share = if lk_share == 0 {1} else {lk_share};
	if b_check_lkup && lk_share*chunks < lkup_len{
		panic!("ERROR: lk_share: {} *chunks: {}  < lkup_len: {}",
			lk_share, chunks, lkup_len);

	}

	//M0 fingerprint: DB-determinism counters (inert unless fp_sink set).
	utils::consts::fp_emit("universe.sigs", db.vec_sigs.len() as u64);
	utils::consts::fp_emit("universe.subsig_ids", db.sig_to_id.len() as u64);
	utils::consts::fp_emit("universe.lkup_len", lkup_len as u64);
	utils::consts::fp_emit("config.chunk_len", chunk_len as u64);
	utils::consts::fp_emit("config.lk_share", lk_share as u64);

	//3. build up each category
	let mut layer_circs = vec![];
	let mut cp_cap_cs= init_cp_capacity_cs.clone();
	let mut cp_cap_igc= init_cp_capacity_igc.clone();
	let mut sed_cap_cs = init_sed_capacity_cs.clone();
	let mut sed_cap_igc = init_sed_capacity_igc.clone();
	let mut dfa_cap= init_dfa_capacity.clone();


	//3.4 build the circs
	for i in 0..n_circs{
		//3.4.1 create cp (cs and igc)
		let cp_cs = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_cs.clone(), db.clone(), false);
		let cp_igc = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_igc.clone(), db.clone(), true);

		//3.4.2 create sed (it has both cs and igc built in)
		let sed = SedComponentMapper::<F,LK<F>>::new(
			sed_cap_cs.clone(), 
			sed_cap_igc.clone(), 
			db.clone());

		//3.4.3 dfa is optional depending if config supports 0 subsigs
		//which enforces dfa to be nil.
		let dfa = if dfa_cap.subsigs==0{ None }else{
			Some(
				DfaComponentMapper::<F,LK<F>>::new(dfa_cap.clone(), 
					db.clone())
			)
		};
		//3.4.4 construct the circuit
		let hybrid_cgm1 =if dfa_cap.subsigs==0{
			CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
				vec![
					Arc::new(Mutex::new(cp_cs)),
					Arc::new(Mutex::new(cp_igc)),
					Arc::new(Mutex::new(sed)),
				]
			)
		}else{//including the dfa
			CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
				vec![
					Arc::new(Mutex::new(cp_cs)),
					Arc::new(Mutex::new(cp_igc)),
					Arc::new(Mutex::new(sed)),
					Arc::new(Mutex::new(dfa.unwrap())),
				]
			)
		};
		let b_cyclepair = false;	
		let circ= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>> ,false> ::new_adv(
			format!("circ_cat_{}_circ_{}", i, 0), 
			poseidon_config.clone(), 
			Arc::new(Mutex::new(hybrid_cgm1)), 
			false, //b_full_mode (whether supporting cyclepair - no for 
					//regular circuit) 
			lk_share,
			b_cyclepair, b_check_lkup
		).expect("error building circ");
		layer_circs.push( vec![circ] ); //legacy to keep 2d layer

		//3.4.5 update the capacities.
		if i<vec_decrease_level.len(){
			let level = vec_decrease_level[i];
			cp_cap_cs = cp_cap_cs.decreased_copy(level); 
			sed_cap_cs = sed_cap_cs.decreased_copy(level,
				utils::consts::min_subsigs_for(false));
			cp_cap_igc = cp_cap_igc.decreased_copy(level);
			sed_cap_igc = sed_cap_igc.decreased_copy(level,
				utils::consts::min_subsigs_for(true));
			dfa_cap= dfa_cap.decreased_copy(level); 
		}
	}//for category

	//return
	layer_circs.reverse();

	layer_circs
}

/// Aggressive-mode circuit builder: assembles CS-only circuits. The igc
/// CP/SED capacities collapse to a 1-subsig sentinel (aggressive mode
/// guarantees all-CS subsigs), cutting the dead igc gadget cost. Takes an
/// explicit CS capacity ladder, lowest-cost first; one circuit per entry,
/// no decreased_copy. There is no DFA gadget in aggressive mode.
pub(crate) fn build_circs_adv_aggr<F,C,CS>(
	poseidon_config: &PoseidonConfig<F>,
	total_word_n: usize,
	chunk_len: usize,
	lkup_len: usize,
	db: Arc<ClamavDB<F>>,
	cs_caps: &Vec<(CpCapacity, SedCapacity, CpCapacity, SedCapacity)>,
	b_check_lkup: bool
)->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle + ColEle,
{
	//1. lkup share (identical to build_circs_adv)
	let max_nibble_len = chunk_len * LEGS;
	let total_nibbles = total_word_n * LEGS;
	let chunks = total_nibbles/max_nibble_len;
	let lk_share = read_global_config().perc_lkup_share* max_nibble_len/100;
	let lk_share = if lk_share == 0 {1} else {lk_share};
	if b_check_lkup && lk_share*chunks < lkup_len{
		panic!("ERROR: lk_share: {} *chunks: {}  < lkup_len: {}",
			lk_share, chunks, lkup_len);
	}

	//2. one circuit per cs cap entry, caller order (lowest cost first). Both
	//   igc caps are supplied per entry: cp_igc runs the real igc crit DFA
	//   (caller sizes its basis_unique_states); sed_igc is the subsigs=1
	//   sentinel tuned via the _igc params.
	let mut layer_circs = vec![];
	for (i,(cp_cap_cs, sed_cap_cs, cp_cap_igc, sed_cap_igc))
		in cs_caps.iter().enumerate(){
		assert!(cp_cap_cs.max_word_len == chunk_len);
		assert!(sed_cap_cs.wea_capacity().max_word_len == chunk_len);
		let cp_cs = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_cs.clone(), db.clone(), false);
		let cp_igc = CpComponentMapper::<F,LK<F>>::new(
			cp_cap_igc.clone(), db.clone(), true);
		let sed = SedComponentMapper::<F,LK<F>>::new(
			sed_cap_cs.clone(), sed_cap_igc.clone(), db.clone());
		let hybrid = CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
			vec![
				Arc::new(Mutex::new(cp_cs)),
				Arc::new(Mutex::new(cp_igc)),
				Arc::new(Mutex::new(sed)),
			]);
		let circ= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
			CompositeGadgetMapper<F,LK<F>> ,false> ::new_adv(
			format!("circ_cat_{}_circ_{}", i, 0),
			poseidon_config.clone(),
			Arc::new(Mutex::new(hybrid)),
			false, lk_share, false, b_check_lkup
		).expect("error building aggr circ");
		layer_circs.push( vec![circ] );
	}
	layer_circs //caller already lowest-cost first: no reverse
}

/// determine_config (aggressive, M11): produce a per-chunk capacity LADDER
/// (rungs, cheapest-first) + a per-rung chunk histogram. P_max = fast_finalize
/// over the binding candidates (global-sufficient config); the per-chunk demand
/// (universe=|failed_c|, plus fwd/active/live) is DP-partitioned into <= k_max
/// cost-bands; each rung = P_max with {subsigs,perc,avg_active} set from its band
/// (monotone envelopes), so every chunk routes to the cheapest sufficient rung
/// at fold time. Aggressive only; the foldpot framework is untouched.
pub(crate) fn determine_config_aggr<F,C,CS>(
	db: Arc<ClamavDB<F>>,
	words: &Vec<Vec<F>>,
	infos: &Vec<WordInfo>,
	vdata: &Vec<data_processor::discharge_proof::FailDischargeRecord>,
	seed: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize,
	k_max: usize, n_buckets: usize, max_rounds: usize, n_threads: usize,
	k_cand: usize, peel_pct: usize,
)->Result<(Vec<crate::determine_config::CapParams>, Vec<usize>), String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	// 1. P_max: the global-sufficient config (existing fast_finalize machinery).
	let mut p_max = fast_finalize::<F,C,CS>(db.clone(), words, infos, vdata,
		seed, chunk_len, lkup_len, total_word_n, max_rounds, n_threads,
		ShrinkMode::Quick, k_cand)?;

	// 2. flatten per-chunk demand (aligned by file,seg). universe = compute_sig's
	// inp_subsigs = sum over the failed sigs of their (fanned) subsig count, NOT
	// the failed-sig COUNT: comp_sig ingests every subsig of each failed sig, so
	// the subsigs cap must be sized on that. fwd/active/live from ChunkPeaks.
	let n_ids = db.sig_to_id.values().copied().max()
		.map(|m| m + 1).unwrap_or(0);
	let mut subsig_cnt_by_id = vec![0usize; n_ids];
	for s in db.vec_sigs.iter().chain(db.vec_sigs_no_critical_pat.iter()) {
		if let Some(&id) = db.sig_to_id.get(&s.name) {
			subsig_cnt_by_id[id] = s.vec_subsig_obj.len();
		}
	}
	let (mut universe, mut fwd, mut active, mut live) =
		(vec![], vec![], vec![], vec![]);
	// per-rung FSM/CP structural demand (B2): aligned 1-1 with the chunks.
	let (mut uniq, mut acc, mut pats, mut cpu) =
		(vec![], vec![], vec![], vec![]);
	let mut nseg_dbg: Vec<usize> = vec![];   // probe-only: per-chunk num_segs
	for (wi, fdr) in infos.iter().zip(vdata.iter()) {
		let cp = &fdr.chunk_peaks;
		for s in 0..wi.failed_c_all_segs.len() {
			let n_sub: usize = wi.failed_c_all_segs[s].iter()
				.map(|&id| subsig_cnt_by_id.get(id).copied().unwrap_or(0))
				.sum();
			universe.push(n_sub);
			// Q1: universe==0 => CP discharged every sig this seg
			// (failed_c empty), so discharge_adv seeds NO inp_subsigs and
			// the SED step queue is empty (discharge_adv.rs:2281-2298).
			// eval_pm_bounds is cross-chunk and still tallies phantom
			// fwd/active for crit sigs never seeded; zero them so the
			// universe-0 rung sizes to perc=1. (aggressive-only path.)
			let z = n_sub == 0;
			fwd.push(if z {0} else {
				cp.fwd_entries_per_chunk.get(s).copied().unwrap_or(0)});
			active.push(if z {0} else {
				cp.active_steps_per_chunk.get(s).copied().unwrap_or(0)});
			live.push(if z {0} else {
				cp.carried_live_per_chunk.get(s).copied().unwrap_or(0)});
			// basis cap unit = count*10000/seg_size = the gadget per-chunk
			// back-solve (cp_mapper.rs:253, fsm_adv). seg_size = ONE chunk's
			// nibbles, not the file (was *num_segs: caps num_segs x too small).
			let wn = cp.seg_size.max(1);
			let rate = |v: usize| v * 10000 / wn;
			uniq.push(rate(cp.unique_acc_pats_per_chunk.get(s)
				.copied().unwrap_or(0)));
			acc.push(rate(cp.acc_states_per_chunk.get(s).copied()
				.unwrap_or(0)));
			pats.push(rate(cp.pats_in_trace_per_chunk.get(s).copied()
				.unwrap_or(0)));
			cpu.push(rate(cp.cp_unique_states_per_chunk.get(s).copied()
				.unwrap_or(0)));
			nseg_dbg.push(wi.failed_c_all_segs.len());
		}
	}
	if universe.is_empty() {
		return Err("determine_config_aggr: no chunks in sample".into());
	}

	// 3. sufficiency guard: P_max.subsigs must cover the worst chunk universe.
	let max_u = *universe.iter().max().unwrap();
	if max_u + 1 > p_max.subsigs { p_max.subsigs = max_u + 1; }
	p_max.aggr_needs_subsigs = p_max.subsigs;   // global clamp = per-rung no-op

	// 4. band DP -> rung specs + histogram (seg_size from the discharge itself).
	// Reserve one rung for the p{peel_pct} peel of rung 0 when k_max>=3.
	let do_peel = k_max >= 3 && peel_pct > 0 && peel_pct < 100;
	let band_k = if do_peel { k_max - 1 } else { k_max };
	let seg_size = vdata.first().map(|f| f.chunk_peaks.seg_size)
		.unwrap_or(chunk_len * crate::gadgets::word_extract::LEGS);
	// Per-chunk prod = forward-queue cap INFERRED from container_rows (= fwd),
	// rung-independent (no basis_pats): prod=(fwd+1)*1e8/(max_nib*FWD_COST)+1,
	// 0 when fwd==0 (=> universe==0). band_dp ranks/groups by this so high-fwd
	// outliers form their own rung instead of inflating the bulk.
	let legs = crate::gadgets::word_extract::LEGS;
	let fwd_cost = crate::gadgets::discharge_adv::FWD_COST;
	let max_nib_c = (p_max.max_word_len * legs).max(1);
	// +10% headroom: the offline fwd predictor under-counts the online
	// gadget queue by <1% on the worst (highest-subsig) chunk, and the
	// top rung has no rung above to promote into, so a bare estimate
	// CapErr-panics. Inflate every chunk's prod so all rung caps carry
	// margin (band_dp sets each rung cap = bucket max prod).
	let prod: Vec<usize> = fwd.iter().map(|&f|
		if f == 0 { 0 }
		else { (f + 1) * 100_000_000 * 11 / 10
			/ (max_nib_c * fwd_cost).max(1) + 1 })
		.collect();
	// rank/group by prod; universe + FSM/CP arrays ride as envelopes.
	let (specs, hist) = crate::band_dp::plan_rungs(&prod, &universe, &fwd,
		&active, &live, &uniq, &acc, &pats, &cpu, p_max.basis_pats_in_trace,
		seg_size, p_max.subsigs.saturating_sub(1),
		p_max.perc_pats_expansion_rate,
		p_max.avg_active_pats_per_subsig, band_k, n_buckets);

	// 5. assemble ladder; optionally peel a smaller rung 0' at the p{peel_pct}
	// of rung 0's FSM/CP demand. The bulk fits rung 0'; the FSM-tail CapErr-
	// bumps to rung 0 at fold time (cap-aware per-seg router). No extra probe.
	let mut ladder = crate::determine_config::assemble_ladder(&p_max, &specs);
	let mut hist = hist;
	if do_peel && !ladder.is_empty() {
		let r0 = ladder[0].clone();
		let ceil0 = r0.subsigs.saturating_sub(1);
		let idxs: Vec<usize> = (0..universe.len())
			.filter(|&i| universe[i] <= ceil0).collect();
		let pctl = |arr: &Vec<usize>| -> usize {
			let mut v: Vec<usize> = idxs.iter().map(|&i| arr[i]).collect();
			if v.is_empty() { return 0; }
			v.sort_unstable();
			v[(peel_pct * (v.len() - 1)) / 100]
		};
		let gmax = |arr: &Vec<usize>| arr.iter().copied().max().unwrap_or(0);
		let sc = |cap: usize, p: usize, g: usize| -> usize {
			if g == 0 { cap } else { ((cap * p + g - 1) / g).min(cap).max(2) }
		};
		let (pu, pa, pp, pc) =
			(pctl(&uniq), pctl(&acc), pctl(&pats), pctl(&cpu));
		let mut peeled = r0.clone();
		peeled.basis_unique_states = sc(r0.basis_unique_states, pu, gmax(&uniq));
		peeled.basis_acc_states = sc(r0.basis_acc_states, pa, gmax(&acc));
		peeled.basis_pats_in_trace = sc(r0.basis_pats_in_trace, pp, gmax(&pats));
		peeled.cp_basis_unique_states =
			sc(r0.cp_basis_unique_states, pc, gmax(&cpu));
		peeled.basis_acc_states = peeled.basis_acc_states
			.max(peeled.basis_pats_in_trace / 10 + 1);
		// informational hist: rung0 chunks fitting the peeled caps (all axes).
		let bulk = idxs.iter().filter(|&&i| uniq[i] <= pu && acc[i] <= pa
			&& pats[i] <= pp && cpu[i] <= pc).count();
		let tail = idxs.len().saturating_sub(bulk);
		ladder.insert(0, peeled);
		if !hist.is_empty() { hist[0] = tail; }
		hist.insert(0, bulk);
		log(0, LOG1, &format!("peel rung0' p{}: bulk={} tail={} (FSM-tail \
			bumps to rung0)", peel_pct, bulk, tail));
	}
	// Dummy-sentinel floor: preprocess builds a 1-subsig dummy whose +2N
	// boundary rows need a minimum forward-queue size. Floor each rung's perc
	// (legacy back-solve) AND prod (aggressive, rung-independent: no
	// basis_pats) so the universe==0 rung still sizes the dummy. Generous
	// (len+1)=16 margin -- tiny vs a real prod, no-op for active rungs. The
	// igc prod gets only this floor (collapsed sentinel in aggressive).
	for r in ladder.iter_mut() {
		let max_nib = (r.max_word_len * legs).max(1);
		let pmin = |bp: usize| 16 * 100_000_000
			/ (max_nib * bp.max(1) * fwd_cost).max(1) + 1;
		let prod_min = 16 * 100_000_000 / (max_nib * fwd_cost).max(1) + 1;
		r.perc_pats_expansion_rate = r.perc_pats_expansion_rate
			.max(pmin(r.basis_pats_in_trace));
		r.perc_pats_expansion_rate_igc = r.perc_pats_expansion_rate_igc
			.max(pmin(r.basis_pats_in_trace_igc));
		r.prod_pats_expansion = r.prod_pats_expansion.max(prod_min);
		r.prod_pats_expansion_igc = r.prod_pats_expansion_igc.max(prod_min);
	}
	log(0, LOG1, &format!("determine_config_aggr: {} rungs, hist={:?}, \
		P_max.subsigs={}, perc={}, avg_active={}", ladder.len(), hist,
		p_max.subsigs, p_max.perc_pats_expansion_rate,
		p_max.avg_active_pats_per_subsig));
	// DIAGNOSTIC (ZKR_FSM_DIST): per-rung distribution of the FSM/CP basis
	// rates, to see if rung 0's caps are forced by a few outlier chunks
	// (peelable) or most chunks. Read-only; no effect when unset.
	if std::env::var("ZKR_FSM_DIST").is_ok() {
		let ceils: Vec<usize> = ladder.iter()
			.map(|c| c.subsigs.saturating_sub(1)).collect();
		let route = |u: usize| ceils.iter().position(|&c| u <= c)
			.unwrap_or(ceils.len().saturating_sub(1));
		let axes: [(&str, &Vec<usize>); 4] =
			[("uniq", &uniq), ("acc", &acc), ("pats", &pats),
			 ("cp_uniq", &cpu)];
		let pct = |v: &mut Vec<usize>, q: usize| -> usize {
			if v.is_empty() { 0 } else { v.sort_unstable();
				v[(q * (v.len() - 1)) / 100] } };
		for r in 0..ladder.len() {
			let idxs: Vec<usize> = (0..universe.len())
				.filter(|&i| route(universe[i]) == r).collect();
			log(0, LOG1, &format!(
				"=== FSM_DIST rung{} (universe<={}, n={} chunks) ===",
				r, ceils.get(r).copied().unwrap_or(0), idxs.len()));
			for (name, arr) in axes.iter() {
				let mut vals: Vec<usize> = idxs.iter()
					.map(|&i| arr[i]).collect();
				let gmax = arr.iter().copied().max().unwrap_or(0);
				log(0, LOG1, &format!(
					"  {:<8} p50={} p90={} p99={} max={} (global max={})",
					name, pct(&mut vals, 50), pct(&mut vals, 90),
					pct(&mut vals, 99), pct(&mut vals, 100), gmax));
			}
		}
	}
	Ok((ladder, hist))
}

/// Shrink precision: Quick = stop at CapErr-led demands (C_low); Precise =
/// tighten to the exact boundary (C_high, for BORA scaling data).
#[derive(Clone,Copy,PartialEq)]
pub(crate) enum ShrinkMode { Quick, Precise }

type CapGet = fn(&crate::determine_config::CapParams)->usize;
type CapSet = fn(&mut crate::determine_config::CapParams, usize);
type CapFloor = fn(&crate::determine_config::CapParams)->usize;

/// Non-source caps shrunk during finalize: (name, get, set, floor-fn). The
/// SOURCE caps {subsigs, basis_pats_in_trace, aggr_needs_subsigs} are NEVER
/// reset -- they stay at their Phase-A CapErr-exact count, which is what makes
/// the subsig->avg_active overshoot structurally impossible. avg_active &
/// perc_pats substitute for one max-buffer; policy (a) lets the gadget floor
/// one, carry the other. Floors are config-dependent so they respect hard
/// gadget constraints (e.g. basis_pats <= 10*basis_acc, else fsm_adv panics).
fn shrink_fields()->Vec<(&'static str, CapGet, CapSet, CapFloor)>{
	vec![
	 ("basis_unique",    |p| p.basis_unique_states,
	    |p,v| p.basis_unique_states=v, |_| 2),
	 ("basis_acc",       |p| p.basis_acc_states,
	    |p,v| p.basis_acc_states=v, |p| p.basis_pats_in_trace/10 + 2),
	 ("cp_basis_unique", |p| p.cp_basis_unique_states,
	    |p,v| p.cp_basis_unique_states=v, |_| 2),
	 ("avg_active",      |p| p.avg_active_pats_per_subsig,
	    |p,v| p.avg_active_pats_per_subsig=v, |_| 1),
	 ("perc_pats",       |p| p.perc_pats_expansion_rate,
	    |p,v| p.perc_pats_expansion_rate=v, |_| 2),
	 ("perc_comp",       |p| p.perc_comp_subsigs,
	    |p,v| p.perc_comp_subsigs=v, |_| 0),
	]
}

/// Run the increase loop from `p` over `padded` until every word plans
/// (collect-probe + CapErr bump, re-probing only failures). Caps only grow,
/// so passed words stay valid. Returns the converged config or Err.
fn reconverge_probe<F,C,CS>(
	db: &Arc<ClamavDB<F>>, poseidon: &PoseidonConfig<F>,
	padded: &Vec<Vec<F>>, word_infos: &Vec<WordInfo>,
	mut p: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize,
	max_rounds: usize, n_threads: usize,
)->Result<crate::determine_config::CapParams, String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	use folding_schemes::folding::foldpot::capacity_planner::CapacityPlanner;
	use crate::determine_config::{apply_caperr_bumps, caps_from_params_aggr,
		parse_caperr_from_panic};
	let mut pending: Vec<usize> = (0..padded.len()).collect();
	for _round in 0..max_rounds {
		utils::consts::get_global_config().aggr_needs_subsigs =
			p.aggr_needs_subsigs;
		let sub_w: Vec<Vec<F>> = pending.iter().map(|&i| padded[i].clone())
			.collect();
		let sub_i: Vec<WordInfo> = pending.iter()
			.map(|&i| word_infos[i].clone()).collect();
		let probe_res = crate::determine_config::probe_catching(|| {
			let (cp, sed, cp_igc, sed_igc) = caps_from_params_aggr(&p);
			let cs_caps = vec![(cp, sed, cp_igc, sed_igc)];
			let layered = build_circs_adv_aggr::<F,C,CS>(poseidon,
				total_word_n, chunk_len, lkup_len, db.clone(), &cs_caps,
				false);
			let planner = CapacityPlanner::<C, FC<F,C,CS>, LK<F>, GM<F>,
				false>::new(layered);
			Ok(planner.capacity_probe_collect(&sub_w, &sub_i, n_threads))
		})?;
		let results = match probe_res {
			Ok(r) => r,
			Err(errs) => {
				let (changed, unmapped) =
					apply_caperr_bumps(&mut p, true, &errs);
				if !unmapped.is_empty() || !changed {
					return Err(format!("reconverge: construction CapErr \
						not bumpable: {:?}", errs));
				}
				continue;
			}
		};
		let mut all_errs: Vec<(String, usize)> = vec![];
		let mut failed: Vec<usize> = vec![];
		for (k, r) in results.iter().enumerate(){
			if let Some(errs) = r {
				failed.push(pending[k]);
				for (name, req) in errs {
					if *req == 0 {
						match parse_caperr_from_panic(name) {
							Some(v) => all_errs.extend(v),
							None => return Err(format!(
								"reconverge: non-CapErr word {}: {}",
								pending[k], name)),
						}
					} else { all_errs.push((name.clone(), *req)); }
				}
			}
		}
		if failed.is_empty() { return Ok(p); }
		let (changed, unmapped) = apply_caperr_bumps(&mut p, true, &all_errs);
		if !unmapped.is_empty() {
			return Err(format!("reconverge: unmapped: {:?}", unmapped)); }
		if !changed {
			return Err(format!("reconverge: no bump: {:?}", all_errs)); }
		pending = failed;
	}
	Err(format!("reconverge: max_rounds {} reached", max_rounds))
}

/// Seed-then-finalize with shrink. Phase A increases from the estimate seed to
/// a sufficient config; Phase B resets the non-source caps to floor and
/// reconverges to the CapErr-exact minimum (sources kept -> no overshoot).
/// Precise then tightens by 1 until stable (exact boundary, for BORA scaling).
pub(crate) fn finalize_caps_probe<F,C,CS>(
	db: Arc<ClamavDB<F>>, words: &Vec<Vec<F>>, word_infos: &Vec<WordInfo>,
	seed: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize,
	max_rounds: usize, n_threads: usize, mode: ShrinkMode,
)->Result<crate::determine_config::CapParams, String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	let poseidon = poseidon_canonical_config::<F>();
	let padded: Vec<Vec<F>> = words.iter()
		.map(|w| utils::data::pad_word_to_multiple::<F>(w, chunk_len)).collect();
	let mut t = GTimer::new();
	macro_rules! rc { ($p:expr) => { reconverge_probe::<F,C,CS>(&db, &poseidon,
		&padded, word_infos, $p, chunk_len, lkup_len, total_word_n, max_rounds,
		n_threads) }; }
	//Phase A: increase from estimate seed -> sufficient.
	let s = rc!(seed)?;
	log(0, LOG1, &format!("finalize Phase A done: {:?}", s));
	//Phase B: reset non-source caps to floor, reconverge -> min (sources kept).
	let mut p0 = s.clone();
	for (_n,_g,set,floor) in shrink_fields(){ set(&mut p0, floor(&s)); }
	let mut shrunk = match rc!(p0) {
		Ok(c) => c,
		Err(e) if e.contains("non-CapErr") => {
			//floor-reset hit an unparseable panic: keep the valid sufficient
			//config, warn loudly (exp-decrease gallop is the deferred upgrade).
			log(0, LOG1, &format!("ERROR finalize: floor-reset panicked \
				({}); returning un-shrunk sufficient config", e));
			s.clone()
		}
		Err(e) => return Err(e),
	};
	log(0, LOG1, &format!("finalize Phase B (shrink) done: {:?}", shrunk));
	//Precise: tighten each shrink cap by 1 until a round is net no-change
	//(strips the even-rounding slack -> exact boundary for BORA).
	if mode == ShrinkMode::Precise {
		for _ in 0..12 {
			let mut dec = shrunk.clone();
			for (_n,g,set,floor) in shrink_fields(){
				let v = g(&dec); let fl = floor(&dec);
				if v>fl { set(&mut dec, v-1); }
			}
			let re = rc!(dec)?;
			if re == shrunk { break; }
			shrunk = re;
		}
		log(0, LOG1, &format!("finalize Precise done: {:?}", shrunk));
	}
	t.stop();
	log(0, LOG1, &format!("finalize_caps_probe TOTAL {} ms", t.ms()));
	Ok(shrunk)
}

/// Pick the small set of "binding candidate" files that drive the caps. Each
/// cap is a max over files of a per-file ChunkPeaks proxy; the file that maxes
/// a proxy is (monotonically) the file that maxes that cap, so tuning over the
/// per-proxy top-K covers every file by construction. Returns sorted unique
/// indices. n<=k -> all files (small sets need no pruning). This is what makes
/// the tuner cost O(#caps * K) probes instead of O(#files).
pub(crate) fn select_binding_candidates(
	vdata: &Vec<data_processor::discharge_proof::FailDischargeRecord>,
	k: usize) -> Vec<usize> {
	let peaks: Vec<_> = vdata.iter().map(|r| r.chunk_peaks.clone()).collect();
	select_candidates_from_peaks(&peaks, k)
}

/// Pure core of select_binding_candidates over the ChunkPeaks alone (so it is
/// unit-testable without building full discharge records).
pub(crate) fn select_candidates_from_peaks(
	peaks: &[data_processor::discharge_proof::ChunkPeaks],
	k: usize) -> Vec<usize> {
	use data_processor::discharge_proof::ChunkPeaks;
	let n = peaks.len();
	if n <= k { return (0..n).collect(); }
	//One proxy per multiplicity/structural cap (the count caps subsigs/
	//aggr_needs are seeded exact from discharge, but max_needs still selects
	//the SED-dense files, so include it).
	let proxies: Vec<fn(&ChunkPeaks)->usize> = vec![
		|c: &ChunkPeaks| c.max_needs_subsigs,
		|c: &ChunkPeaks| c.max_fwd_entries_per_chunk,
		|c: &ChunkPeaks| c.max_active_steps_per_chunk,
		|c: &ChunkPeaks| c.max_pats_in_trace,
		|c: &ChunkPeaks| c.max_unique_states,
		|c: &ChunkPeaks| c.max_acc_states,
		|c: &ChunkPeaks| c.max_cp_unique_states,
	];
	let mut set = std::collections::BTreeSet::<usize>::new();
	for proj in proxies {
		let mut idx: Vec<usize> = (0..n).collect();
		idx.sort_by_key(|&i| std::cmp::Reverse(proj(&peaks[i])));
		for &i in idx.iter().take(k) { set.insert(i); }
	}
	set.into_iter().collect()
}

/// Fast cap tuner: select the binding candidates (per-proxy top-K), then run
/// finalize_caps_probe over ONLY those, instead of the whole file list. The
/// result is identical to finalizing over all files (sufficiency holds because
/// the candidates include each cap's argmax file; the count caps come from the
/// estimate seed which is already exact from discharge), at O(#caps*K) probe
/// cost -- corpus-size-independent. Giant-file single-chunk slicing (idea B)
/// is a separate step; here each candidate is probed whole.
pub(crate) fn fast_finalize<F,C,CS>(
	db: Arc<ClamavDB<F>>, words: &Vec<Vec<F>>, word_infos: &Vec<WordInfo>,
	vdata: &Vec<data_processor::discharge_proof::FailDischargeRecord>,
	seed: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize,
	max_rounds: usize, n_threads: usize, mode: ShrinkMode, k_cand: usize,
)->Result<crate::determine_config::CapParams, String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	let cand = select_binding_candidates(vdata, k_cand);
	log(0, LOG1, &format!("fast_finalize: {} files -> {} binding candidates \
		(K={})", words.len(), cand.len(), k_cand));
	let cw: Vec<Vec<F>> = cand.iter().map(|&i| words[i].clone()).collect();
	let ci: Vec<WordInfo> = cand.iter().map(|&i| word_infos[i].clone())
		.collect();
	finalize_caps_probe::<F,C,CS>(db, &cw, &ci, seed, chunk_len, lkup_len,
		total_word_n, max_rounds, n_threads, mode)
}

/// Exact per-word max SDE obligation-set size, per b_igc arm. This is the set
/// non-aggressive neo seeds its step queue from, so it is the true floor for
/// capacity.subsigs -- derivable up front from (db, WordInfo) with no probe.
/// Mirrors sed_mapper's non-aggressive derivation: whole-word sigs (the
/// aggressive failed_c per-segment branch does not apply), collect_subsig_ids,
/// then the neo `needs` filter (drop empty-chain subsigs, which can never
/// reach LAST_STEP). Per-word constant: that branch ignores seg_id.
fn neo_subsig_demand<F,C,CS>(db: &ClamavDB<F>, infos: &[WordInfo],
	b_igc: bool) -> usize
where C: CurveGroup<ScalarField=F>, CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle,
{
	let bundle_cs = &db.bundle_subsig;
	let acdfa = if b_igc { &db.bundle_subsig_igc.vec_acdfa[0] }
		else { &bundle_cs.vec_acdfa[0] };
	let store = if b_igc { &db.bundle_subsig_igc.vec_subsig_step_stores[0] }
		else { &bundle_cs.vec_subsig_step_stores[0] };
	let mut max_n = 0usize;
	for wi in infos.iter() {
		if wi.vec_sed_sigs.is_empty() { continue; } // dummy pad word
		let sigs: Vec<Arc<data_processor::type_def::ClamavSig>>
			= bundle_cs.vec_sigs[0].iter()
			.filter(|s| db.sig_to_id.get(&s.name)
				.map_or(false, |id| wi.vec_sed_sigs.contains(id)))
			.cloned().collect();
		if sigs.len() != wi.vec_sed_sigs_info.len() { continue; } // 1-1 or skip
		let inp = crate::circs::sed_mapper::SedAdvice::<F>::collect_subsig_ids(
			&sigs, &wi.vec_sed_sigs_info, &db.sig_to_id, b_igc, acdfa);
		// neo seeds only non-empty-chain subsigs (sed_mapper's `needs`).
		let n = inp.iter().filter(|s| {
			let u = folding_schemes::folding::foldpot::circuits_super
				::field_to_usize(*s);
			store.subsig_to_steps.get(&u)
				.map_or(false, |it| !it.vec_pm_bounds.is_empty())
		}).count();
		max_n = max_n.max(n);
	}
	max_n
}

/// Exact per-word max DFA subsig count, the true floor for DfaCapacity.subsigs.
/// dfa_mapper flattens word_info.vec_dfa_sigs_info into v_subsig_ids and
/// CapErrs when it exceeds capacity.subsigs, so the demand is just that
/// flattened length -- a pure function of WordInfo, needing no probe.
fn neo_dfa_subsig_demand(infos: &[WordInfo]) -> usize {
	infos.iter().map(|wi| wi.vec_dfa_sigs_info.iter()
		.map(|i| i.subsig_ids.len()).sum::<usize>()).max().unwrap_or(0)
}

/// determine_config (non-aggressive): same loop as the aggressive variant but
/// builds the full cs/igc/dfa ladder via build_circs_adv. CapErr bumps route
/// to cs or igc fields by the b_igc suffix. Returns the confirmed-lowest base
/// caps (decreased_copy regenerates the ladder).
pub(crate) fn determine_config_general<F,C,CS>(
	db: Arc<ClamavDB<F>>,
	sample_words: &Vec<Vec<F>>,
	sample_word_infos: &Vec<WordInfo>,
	mut p: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize,
	vec_decrease_level: &Vec<usize>, n_circs: usize, max_iters: usize,
	n_threads: usize,
)->Result<crate::determine_config::CapParams, String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	use folding_schemes::folding::foldpot::capacity_planner::CapacityPlanner;
	use crate::determine_config::{apply_caperr_bumps, caps_from_params_general};
	let poseidon = poseidon_canonical_config::<F>();
	let padded: Vec<Vec<F>> = sample_words.iter()
		.map(|w| utils::data::pad_word_to_multiple::<F>(w, chunk_len))
		.collect();
	let mut t_all = GTimer::new();
	// Restores the two subsigs ladder floors on EVERY exit of this function
	// (Ok, Err, or `?`). The seed block below writes them so the probes'
	// build_circs_adv ladders correctly; without this they would persist
	// process-wide and a later cell that sets only min_subsigs would inherit
	// this cell's min_subsigs_igc instead of the "0 = inherit" default.
	struct FloorGuard(usize, usize, usize);
	impl Drop for FloorGuard {
		fn drop(&mut self) {
			let mut c = get_global_config();
			c.min_subsigs = self.0;
			c.min_subsigs_igc = self.1;
			c.min_cp_subsigs = self.2;
		}
	}
	let _floor_guard = {
		let c = read_global_config();
		FloorGuard(c.min_subsigs, c.min_subsigs_igc, c.min_cp_subsigs)
	};
	// NEO ONLY: seed subsigs from the exact obligation-set max instead of the
	// caller's knob. The tuner has no downward move on subsigs (shrink_fields
	// omits it; apply_caperr_bumps is max-semantics), so an over-large knob is
	// returned verbatim -- clam_hard measured 256 in / 256 out at demand 59.
	// The set is per-word constant here, so EVERY ladder rung faces the same
	// demand: min_subsigs is pinned to the seed too, keeping the subsig axis
	// FLAT. Without that pin decreased_copy's *9/16 would drop a lower rung
	// below demand and CapErr. Legacy is untouched (gate + hard rule).
	if read_global_config().clamav_cfg.b_use_discharge_neo {
		let d_cs = neo_subsig_demand::<F,C,CS>(&db, sample_word_infos, false);
		let d_igc = neo_subsig_demand::<F,C,CS>(&db, sample_word_infos, true);
		// +1 reserves the comp_sig dummy entry (inp_subsigs[0] must be 0),
		// the same convention apply_caperr_bumps uses on every subsigs bump.
		let (s_cs, s_igc) = (d_cs + 1, d_igc + 1);
		// never RAISE past the caller's knob: that would be a silent capacity
		// increase rather than the tightening this is for. An under-seed is
		// recovered by the neo_subsig_slots ratchet (one extra probe round).
		let (n_cs, n_igc) = (s_cs.min(p.subsigs), s_igc.min(p.subsigs_igc));
		log(0, LOG1, &format!("NEO SUBSIG SEED: demand cs={} igc={} -> \
			subsigs {}->{}, subsigs_igc {}->{}",
			d_cs, d_igc, p.subsigs, n_cs, p.subsigs_igc, n_igc));
		p.subsigs = n_cs;
		p.subsigs_igc = n_igc;
		// Pin each arm's ladder floor to its OWN seed: demand is per-word
		// constant, so every rung faces the same set and the axis must stay
		// FLAT. A single shared floor would clamp the igc rungs above the
		// igc top rung (cs 60 vs igc 2). SCOPED: _floor_guard restores both
		// fields on every exit, so the write cannot leak into the next cell
		// of a multi-cell process (cargo test runs all cells in one). The
		// fold path re-applies them from the RETURNED CapParams.
		let mut cfg = get_global_config();
		cfg.min_subsigs = n_cs;
		cfg.min_subsigs_igc = n_igc;
		drop(cfg);

		// CP and DFA subsigs are ALSO up()-only in the tuner, so the caller's
		// knob is returned verbatim there too. clam_hard feeds ONE ZKR_SUBSIGS
		// into all three capacities, so hand-tuning it cut CP/DFA as well while
		// the SED-only seed above left them at 256 -- measured 2.09x worse cols
		// than the hand-tune, with framework logup (capacity-slot driven, not
		// data driven) as the bulk of the gap. Seed both DOWN here.

		// CP: exact and DB-static. Subsigs with no critical pattern can never
		// discharge in CP, so EVERY word hands all of them to SED -- there is
		// no per-word variation to probe for. This is the value cp_mapper.rs's
		// ctor assert itself recommends; that assert is bare (not a CapErr), so
		// an under-seed would panic unparseably -- hence exact, not a ratchet.
		// Any per-word excess is still caught by the cp::subsigs CapErr.
		let cp_need = db.vec_sigs_no_critical_pat.len() + 1;
		let n_cp = cp_need.min(p.cp_subsigs);
		log(0, LOG1, &format!("NEO CP SEED: no_crit_pat={} -> cp_subsigs \
			{}->{}", cp_need - 1, p.cp_subsigs, n_cp));
		p.cp_subsigs = n_cp;
		// pin CP's ladder floor to the SAME DB-static bound: it is a per-word
		// invariant, so no rung may fall below it. CP has its own floor because
		// CpCapacity.subsigs otherwise shares min_subsigs with the SED arm.
		get_global_config().min_cp_subsigs = n_cp;

		// DFA: per-word VARYING (v_subsig_ids from vec_dfa_sigs_info), so
		// laddering is legitimate and no floor pin is wanted. Seed to the EXACT
		// max over the sample rather than to min_dfa_subsigs + the
		// dfa_mapper::subsigs ratchet: the ratchet only observes words the
		// probe actually runs, and a CapErr raised at FOLD time is not
		// recoverable. The ratchet stays as a backstop. Keep the floor as a
		// lower bound so a zero-DFA corpus still gets a valid capacity.
		let d_dfa = neo_dfa_subsig_demand(sample_word_infos);
		let n_dfa = d_dfa.max(read_global_config().min_dfa_subsigs).max(1)
			.min(p.dfa_subsigs);
		log(0, LOG1, &format!("NEO DFA SEED: demand={} -> dfa_subsigs {}->{}",
			d_dfa, p.dfa_subsigs, n_dfa));
		p.dfa_subsigs = n_dfa;
	}
	// reusable probe: same body as the convergence loop, callable for the
	// post-convergence perc tightening (binary search) with the probe as oracle.
	let run_probe = |p: &crate::determine_config::CapParams| {
		crate::determine_config::probe_catching(|| {
			let (cp_cs, sed_cs, dfa, cp_igc, sed_igc) =
				caps_from_params_general(p);
			let layered = build_circs_adv::<F,C,CS>(&poseidon, total_word_n,
				chunk_len, lkup_len, db.clone(), &cp_cs, &sed_cs, &dfa,
				&cp_igc, &sed_igc, vec_decrease_level, n_circs, false);
			let planner = CapacityPlanner::<C, FC<F,C,CS>, LK<F>, GM<F>,
				false>::new(layered);
			planner.capacity_probe_par(&padded, sample_word_infos, n_threads)
		})
	};
	for iter in 0..max_iters {
		let mut t_round = GTimer::new();
		utils::consts::reset_sat();
		let probe_res = run_probe(&p)?;
		t_round.stop();
		match probe_res {
			Ok(steps) => {
				t_all.stop();
				log(0, LOG1, &format!("determine_config_general CONVERGED \
					@iter {}: steps={}, perc_cs={}, perc_igc={}, subsigs={}, \
					basis_acc={}; round {} ms, TOTAL {} ms", iter, steps,
					p.perc_pats_expansion_rate, p.perc_pats_expansion_rate_igc,
					p.subsigs, p.basis_acc_states, t_round.ms(), t_all.ms()));
				// --- post-convergence tightening of the decoupled forward
				// queue cap. perc_pats_expansion_rate feeds ONLY the discharge
				// fwd queue (no SED container reads it), so binary-search it
				// DOWN with the probe as oracle, all other caps frozen. The
				// converged pass above (after reset_sat) populated the true
				// max fill. acc-states is the BINDING SED cap -> reported only,
				// never cut. ---
				let min_perc = read_global_config()
					.min_perc_pats_expansion_rate.max(1);
				// safety headroom over the sample-measured minimum so a full
				// fold step heavier than the probe sample cannot CapErr; capped
				// at the (known-good) converged value, floored at min_perc.
				// Single-word case (scale experiment): sample == fold corpus, so
				// the measured max is exact -> 0% margin. Multi-word full runs
				// sample a subset -> 10% headroom.
				// NOTE: the caller always appends one dummy 0-pad word (the
				// foldpot pad) to sample_words, so the REAL word count is
				// len-1; <=2 means a single real word -> exact -> 0% margin.
				let margin_pct = if sample_words.len() <= 2 { 0 } else { 10 };
				let with_margin = |v: usize, lo: usize, cap: usize|
					((v * (100 + margin_pct) + 99) / 100)
						.clamp(lo, cap);
				let (mfwd_cs, mfwd_igc) =
					(utils::consts::get_fwd(false), utils::consts::get_fwd(true));
				let (macc_cs, macc_igc) =
					(utils::consts::get_acc(false), utils::consts::get_acc(true));
				let (old_cs, old_igc) =
					(p.perc_pats_expansion_rate, p.perc_pats_expansion_rate_igc);
				use crate::gadgets::discharge_adv::backsolve_perc;
				// cs arm: smallest perc in [min_perc, old_cs] that still probes
				// Ok; seed the first probe at the back-solve of measured fill.
				// Dummy-sentinel floor (mirrors the aggressive pmin in
				// determine_config_aggr): the final build always lays out a
				// 1-subsig dummy whose +2N boundary rows need a non-empty
				// forward queue, so perc must NOT tighten below the buffer that
				// holds it -- even when the measured fill is 0. Without this the
				// single-word scale run (margin 0) tightens down to min_perc and
				// the fail-fast final build CapErrs on perc_pats_expansion_rate.
				let pfloor = |bp: usize|
					backsolve_perc(15, bp, chunk_len).max(min_perc);
				{
					let lo_f = pfloor(p.basis_pats_in_trace);
					let (mut lo, mut hi) = (lo_f, old_cs.max(lo_f));
					let seed = backsolve_perc(mfwd_cs,
						p.basis_pats_in_trace, chunk_len).clamp(lo_f, hi);
					let mut next = if seed < hi { Some(seed) } else { None };
					while lo < hi {
						let mid = next.take().unwrap_or(lo + (hi - lo) / 2);
						p.perc_pats_expansion_rate = mid;
						if matches!(run_probe(&p), Ok(Ok(_))) { hi = mid; }
						else { lo = mid + 1; }
					}
					p.perc_pats_expansion_rate =
						with_margin(hi, lo_f, old_cs.max(lo_f));
				}
				// igc arm (cs perc now frozen at its tightened value).
				{
					let lo_f = pfloor(p.basis_pats_in_trace_igc);
					let (mut lo, mut hi) = (lo_f, old_igc.max(lo_f));
					let seed = backsolve_perc(mfwd_igc,
						p.basis_pats_in_trace_igc, chunk_len).clamp(lo_f, hi);
					let mut next = if seed < hi { Some(seed) } else { None };
					while lo < hi {
						let mid = next.take().unwrap_or(lo + (hi - lo) / 2);
						p.perc_pats_expansion_rate_igc = mid;
						if matches!(run_probe(&p), Ok(Ok(_))) { hi = mid; }
						else { lo = mid + 1; }
					}
					p.perc_pats_expansion_rate_igc =
						with_margin(hi, lo_f, old_igc.max(lo_f));
				}
				// avg-active-pats arms: size_pat = subsigs * avg_active is the
				// perc-INDEPENDENT term of n = max(size_pat, size_trace). At LOW
				// rule-set fractions the trace demand is small, so this floor
				// BINDS and perc has no leverage -- bin-search avg_active DOWN
				// too (perc now frozen), probe as oracle. At high fractions the
				// trace term binds and this harmlessly floors size_pat for free
				// (see DischargeAdvCapacity vec_size doc). cs then igc. Floored
				// at 1 (a subsig holds >=1 active pat); same margin as perc.
				let (old_ap_cs, old_ap_igc) =
					(p.avg_active_pats_per_subsig, p.avg_active_pats_per_subsig_igc);
				let with_margin1 = |v: usize, cap: usize|
					((v * (100 + margin_pct) + 99) / 100).clamp(1, cap);
				{
					let (mut lo, mut hi) = (1usize, old_ap_cs);
					while lo < hi {
						let mid = lo + (hi - lo) / 2;
						p.avg_active_pats_per_subsig = mid;
						if matches!(run_probe(&p), Ok(Ok(_))) { hi = mid; }
						else { lo = mid + 1; }
					}
					p.avg_active_pats_per_subsig = with_margin1(hi, old_ap_cs);
				}
				{
					let (mut lo, mut hi) = (1usize, old_ap_igc);
					while lo < hi {
						let mid = lo + (hi - lo) / 2;
						p.avg_active_pats_per_subsig_igc = mid;
						if matches!(run_probe(&p), Ok(Ok(_))) { hi = mid; }
						else { lo = mid + 1; }
					}
					p.avg_active_pats_per_subsig_igc = with_margin1(hi, old_ap_igc);
				}
				log(0, LOG1, &format!("PERC TIGHTEN: perc_cs {}->{} \
					(max_fwd={}), perc_igc {}->{} (max_fwd={}); avg_active_cs \
					{}->{}, avg_active_igc {}->{}; SDE acc max \
					cs={} igc={} (binding cap, reported only)",
					old_cs, p.perc_pats_expansion_rate, mfwd_cs,
					old_igc, p.perc_pats_expansion_rate_igc, mfwd_igc,
					old_ap_cs, p.avg_active_pats_per_subsig,
					old_ap_igc, p.avg_active_pats_per_subsig_igc,
					macc_cs, macc_igc));
				return Ok(p);
			}
			Err(errs) => {
				let (changed, unmapped) =
					apply_caperr_bumps(&mut p, false, &errs);
				if !unmapped.is_empty() {
					return Err(format!("unmapped CapErr(s): {:?}", unmapped));
				}
				if !changed {
					return Err(format!(
						"CapErr with no bump applied: {:?}", errs));
				}
				log(0, LOG1, &format!("determine_config_general iter {}: \
					round {} ms, bumped {:?}", iter, t_round.ms(), errs));
			}
		}
	}
	Err(format!("max_iters {} reached without convergence", max_iters))
}

/// build the list of circs. Note: for convenience of implementation,
/// we put the circ config hard coded in this function. To change
/// config, modify the local variables at the beginning of this function.
/// DEPRECATED
#[allow(dead_code)]
fn build_circs<F,C,CS>(poseidon_config: &PoseidonConfig<F>, total_word_n: usize, lkup_len: usize, db: Arc<ClamavDB<F>>, b_check_lkup: bool ) 
->Vec<Vec<FC<F,C,CS>>>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  F: PrimeField + Absorb + ColEle + ColEle,
{

	// TEMP PLAN: remove later
	// each circ has one composite mapper which consists of one component 
	// mapper which has fixed length. Two circs, one handling length 8,
	// one handling length 4.

	//1. create cp_components
	if 1>0 {panic!("this function is depcrecated");}
	let avg_lk_wd = lkup_len/total_word_n + 1;
	let avg_lk_wd = if avg_lk_wd<1 {1} else {avg_lk_wd};
	let max_word = 1;
	let sigs = 3;
	let subsigs = 6;
	let avg_pats_per_subsig = 8;
	let avg_active_pats_per_subsig = 3;
	let basis_pats_in_trace = 6*100;
	let perc_comp_subsigs = 50;
	let basis_unique_states = 100; //1 percent
	let basis_acc_states = 500; //5 percent
	let perc_pats_expansion_rate = 100;
 
	//let avg_subsig_per_sig = 2;
	let cap1 = CpCapacity{
		max_word_len: max_word, 
		basis_unique_states,
		subsigs,
		avg_pats_per_subsig,
	};
	let comp1 = CpComponentMapper::<F,LK<F>>::new(cap1.clone(), 
		db.clone(), false);
	let comp1_igc = CpComponentMapper::<F,LK<F>>::new(cap1, db.clone(), true);
	/*
	let cap2 = CpCapacity{max_word_len: 2, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 2};
	let cap3 = CpCapacity{max_word_len: 3, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let cap4 = CpCapacity{max_word_len: 4, final_states_len: 16, join_buf_capacity: 8, sig_buf_capacity: 4};
	let b_igc = false;
	let comp2 = CpComponentMapper::<F,LK<F>>::new(cap2, db.clone(), b_igc);
	let comp3 = CpComponentMapper::<F,LK<F>>::new(cap3, db.clone(), b_igc);
	let comp4 = CpComponentMapper::<F,LK<F>>::new(cap4, db.clone(), b_igc);
	let _cg4 = CompositeGadgetMapper::<F,LK<F>>::new("w4",vec![Arc::new(Mutex::new(comp4))]); 
	let _cg3 = CompositeGadgetMapper::<F,LK<F>>::new("w3",vec![Arc::new(Mutex::new(comp3))]); 
	let _cg2 = CompositeGadgetMapper::<F,LK<F>>::new("w2",vec![Arc::new(Mutex::new(comp2))]); 
	*/
	let cg1 = CompositeGadgetMapper::<F,LK<F>>::new("cp1",vec![
		Arc::new(Mutex::new(comp1.clone())), 
		Arc::new(Mutex::new(comp1_igc.clone())), 
	]); 

	//2. create sed components
	let scap1= SedCapacity::new(max_word, db.dfa_crit.state_part_bits, subsigs, 
		avg_pats_per_subsig, avg_active_pats_per_subsig, basis_pats_in_trace, perc_pats_expansion_rate, sigs, perc_comp_subsigs, basis_unique_states, basis_acc_states);
	let scomp1 = SedComponentMapper::<F,LK<F>>::new(scap1.clone(), scap1, db.clone());
	//let scg1 = CompositeGadgetMapper::<F,LK<F>>::new("sed1",vec![Arc::new(Mutex::new(scomp1))]); 


	let lk_share1 = max_word*avg_lk_wd;
	let b_cyclepair = false;
	//let lk_share2 = max_word*2*avg_lk_wd;
	let _c1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c1"), poseidon_config.clone(), 
			Arc::new(Mutex::new(cg1)), false, lk_share1,
			b_cyclepair, b_check_lkup).expect("c1");
	/*
	let _c2 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c2"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg2)), false, lk_share2).expect("c2");
	let _c3 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c3"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg3)), false, lk_share2).expect("c3");
	let _c4 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("c4"), poseidon_config.clone(), 
			Arc::new(Mutex::new(_cg4)), false, lk_share2).expect("c4");
	*/

	//4. create sed instances
	//let sc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("sc1"), poseidon_config.clone(), 
	//		Arc::new(Mutex::new(scg1)), false, lk_share1).expect("sc1");

	//5. create dfa components and instances
	let sigs=3;
	let subsigs=6;
	let d_cap1 = DfaCapacity::new(max_word, sigs, subsigs);
	let dcomp1 = DfaComponentMapper::<F,LK<F>>::new(d_cap1, db.clone());
	//let dcg1 = CompositeGadgetMapper::<F,LK<F>>::new("d1",
	//	vec![Arc::new(Mutex::new(dcomp1))]);
	//let dc1 = SigmaIR1CS_Inst::<F,C,CS,LK<F>,
	//	CompositeGadgetMapper<F,LK<F>>
	//	,false>
	//	::new_adv(format!("dfa1"), poseidon_config.clone(), 
	//		Arc::new(Mutex::new(dcg1)), false, lk_share1).expect("dc1");

	let hybrid_cgm1 = CompositeGadgetMapper::<F,LK<F>>::new("hybrid_cgm1",
		vec![
			Arc::new(Mutex::new(comp1)),
			Arc::new(Mutex::new(comp1_igc)),
			Arc::new(Mutex::new(scomp1)),
			Arc::new(Mutex::new(dcomp1)),
		]);
	let _hc1= SigmaIR1CS_Inst::<F,C,CS,LK<F>,
		CompositeGadgetMapper<F,LK<F>>
		,false>
		::new_adv(format!("hc1"), poseidon_config.clone(), 
			Arc::new(Mutex::new(hybrid_cgm1)), false, lk_share1,
			b_cyclepair, b_check_lkup).expect("hc1");

	//vec![ vec![c4,c3], vec![c2,c1] ]
	//vec![ vec![_c2,_c1] ] //for saving cost
	//vec![ vec![_c1] ] //for saving cost
	//vec![ vec![sc1] ] //for saving cost
	//vec![ vec![dc1] ] //for saving cost
	vec![ vec![_hc1] ] //compsite of cg, sed, and dfa
}


/// This is the main function of ZkregPlus framework.
/// Given a signature file, the list of data file to discharge,
/// It generates the entire workflow to discharge them first via
/// folding and then a decider proof.
///
/// * `sig_file`: the virus signature file (see examples/small_dataset for example).
/// * `list_files_to_scan`:  the file which contains the list of data files to be scanned using the virus signature
/// * `b_read_cahe`: if to read cache for pre-processed DFAs
/// * `cache_prefix`: the cache file prefix to determine which cache to read or write
/// * `list_of_dfa_sigs`: the file contains the list of signatures that to build into DFA
/// * `list_of_ised:`: the list of signatures that need ISED ACDFA to be constructed
/// * `job_id`: The ID of the job being processed.
pub fn zkp_driver<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S> 
(
	job_id: usize,
	sig_file: &str, 
	list_file_to_scan: &str, 
	_logfile: &str, 
	b_write_cache: bool, 
	cache_dir: &str, 
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize, //see the definition of params for build_circs for below
	init_cp_capacity: &CpCapacity, 
	init_sed_capacity: &SedCapacity,
	init_dfa_capacity: &DfaCapacity,
	vec_decrease_levels: &Vec<usize>,
	num_circs: usize,
	b_check_lkup: bool,
)
where
	GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
	GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	// CS1E is a KZG commitment, where challenge is C1::Fr elem
	CS1E: CommitmentScheme<
		C1,
		ProverChallenge = C1::ScalarField,
		Challenge = C1::ScalarField,
		Proof = KZGProof<C1>,
	>,
	<CS1E as CommitmentScheme<C1>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	// enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
	CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2>>::VerifierParams: Send + Sync,
	S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<C2 as CurveGroup>::BaseField: PrimeField,
	<C1 as Group>::ScalarField: Absorb,
	<C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
	for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
	for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	//C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	<C2 as CurveGroup>::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	<E as Pairing>::ScalarField: ColEle,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
	// re-use the capacity for BOTH cs and ignore_case
	// this is usaully inefficient for ignore_case (but
	// we do this for small samples for convenience)
	//last arg: env ZKR_DC picks the capacity auto-tuner mode. Unset/0
	//keeps the hand caps above, so this call is unchanged by default.
	zkp_driver_adv::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(job_id, sig_file, vec![list_file_to_scan.to_string()], _logfile,
		b_write_cache, cache_dir,
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		chunk_len,
		init_cp_capacity, init_sed_capacity, init_dfa_capacity,
		init_cp_capacity, init_sed_capacity,
		vec_decrease_levels, num_circs, b_check_lkup, dc_mode_from_env()
	);
}

/// ZKR_DC selects the tuner mode for the cells routed through `zkp_driver`:
/// 0 = Off, 1 = ProbeOnly, 2 = ProbeThenFold. An explicit value always
/// wins. UNSET defaults to ProbeThenFold under neo and Off otherwise, so
/// LEGACY keeps its hand caps byte-for-byte while neo cells auto-tune:
/// hand caps are neo's dominant cost (clam_hard measured 2.45x cols /
/// 2.15x wall vs the best hand-tune), and the seeds that make that work
/// are neo-gated anyway. `ZKR_DC=0` restores neo's old hand-cap behavior.
fn dc_mode_from_env() -> DcMode {
	match std::env::var("ZKR_DC").ok()
		.and_then(|s| s.parse::<usize>().ok()) {
		Some(1) => DcMode::ProbeOnly,
		Some(2) => DcMode::ProbeThenFold,
		Some(_) => DcMode::Off,
		None => if read_global_config().clamav_cfg.b_use_discharge_neo {
			DcMode::ProbeThenFold
		} else { DcMode::Off },
	}
}

/// Neo on/off for comparative runs. ZKR_USE_NEO=1 forces neo, =0 forces
/// legacy; ZKR_NO_NEO is the legacy-side alias (=1 legacy, =0 neo).
/// Unset keeps `dflt`, so each cell's own default is preserved.
fn neo_from_env(dflt: bool) -> bool {
	if let Ok(v) = std::env::var("ZKR_USE_NEO") { return v == "1"; }
	if let Ok(v) = std::env::var("ZKR_NO_NEO")  { return v != "1"; }
	dflt
}
/// How the determine_config (capacity auto-tuning) probe interacts with
/// folding in `zkp_driver_adv`:
///  - `Off`           : skip the probe, fold with the caller's hand caps.
///  - `ProbeOnly`     : run the probe, report, and RETURN without folding (the
///                      manual capacity-tuning workflow).
///  - `ProbeThenFold` : run the probe and fold with the TUNED caps (used by
///                      collect_scale_data so each rule-set subset folds at its
///                      own optimized capacities).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DcMode { Off, ProbeOnly, ProbeThenFold }

/// `job_id`: The ID of the job being processed.
pub fn zkp_driver_adv<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S>
(
	job_id: usize,
	sig_file: &str, 
	list_files_to_scan: Vec<String>, 
	_logfile: &str, 
	b_write_cache: bool, 
	cache_dir: &str, 
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize, //see the definition of params for build_circs for below
	init_cp_capacity_cs: &CpCapacity, 
	init_sed_capacity_cs: &SedCapacity,
	init_dfa_capacity: &DfaCapacity, //only one DFA (no cs/igc distinction)
	init_cp_capacity_igc: &CpCapacity, 
	init_sed_capacity_igc: &SedCapacity,
	vec_decrease_level: &Vec<usize>,
	num_circs: usize,
	b_check_lkup: bool,
	dc_mode: DcMode,
)
where
	GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
	GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	// CS1E is a KZG commitment, where challenge is C1::Fr elem
	CS1E: CommitmentScheme<
		C1,
		ProverChallenge = C1::ScalarField,
		Challenge = C1::ScalarField,
		Proof = KZGProof<C1>,
	>,
	<CS1E as CommitmentScheme<C1>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	// enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
	CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2>>::VerifierParams: Send + Sync,
	S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<C2 as CurveGroup>::BaseField: PrimeField,
	<C1 as Group>::ScalarField: Absorb,
	<C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
	for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
	for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	//C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	//C2G2: CurveGroup,
	<E as Pairing>::ScalarField: Absorb,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	<C2 as CurveGroup>::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	<E as Pairing>::ScalarField: ColEle,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
	//1. build or load the clamdb
	let log_level = LOG1;
	let mut gt1 = GTimer::new();
	log(0, log_level, &format!("=== ZKP driver starts ===="));
	let poseidon_config = poseidon_canonical_config::<CF1<C1>>();
	let mut vlog = vec![];
	let cfg = default_clamav_cfg();
	let db = ClamavDB::<CF1<C1>>::build_or_load(&cfg, sig_file, 
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		&mut vlog, cache_dir, read_global_config().b_read_cache, b_write_cache)
		.expect("build db err");
	if log_level>=LOG1+1{
		db.print_summary(&mut vlog);
	}
	log_perf(0, log_level, &format!("ZIP driver step 1: build DB."), &mut gt1);
	
	//2. load the files as vec of words
	let mut max_total_word_len = 0;
	let mut jobs = vec![];
	for list_file_to_scan in list_files_to_scan{
		let (vec_words, vec_word_info, vec_word_fnames, _vdata) = load_files::<CF1<C1>>(job_id, &list_file_to_scan, &db, &cfg, b_write_cache, cache_dir, chunk_len);
		let total_word_len:usize = vec_words.iter().map(|w| w.len()).sum();
		if total_word_len > max_total_word_len{
			max_total_word_len = total_word_len;
		}
		jobs.push(FoldPotJob{
			vec_words,
			vec_word_info,
			vec_word_fnames,
			idx_individual_prf: 0,
		});
	}
	let lkup_len = db.lkup.get_size();
	log_perf(0, log_level, &format!("ZIP driver step 2: load words and prepare {} jobs.", jobs.len()), &mut gt1);

	//3. build the circuits
	let rc_db = Arc::new(db.clone());

	// Capacity source for folding. `DcMode::Off` -> the caller's hand caps.
	// Otherwise the determine_config Pass-1 probe auto-tunes the lowest
	// CapParams for THIS (DB, corpus): it reuses the built DB + loaded jobs,
	// warm-starts perc/avg_active (cs+igc) low to exercise convergence, and
	// compares vs the hand caps with the +10% rule. `ProbeOnly` stops after
	// reporting; `ProbeThenFold` folds with the tuned caps.
	let tuned: Option<(CpCapacity, SedCapacity, DfaCapacity,
		CpCapacity, SedCapacity)> = if dc_mode == DcMode::Off {
		None
	} else {
		use crate::determine_config::{capparams_from_caps_general,
			compare_caps, caps_from_params_general};
		let cur = capparams_from_caps_general(init_cp_capacity_cs,
			init_sed_capacity_cs, init_dfa_capacity, init_sed_capacity_igc);
		// Warm-start carry-over: each scale round's rule set is a superset of
		// the previous, so caps only grow. If the prior round saved its
		// converged caps, start the probe there (skips the floor-to-converged
		// climb); else warm-start LOW (floor 16/2) to converge to the true
		// minimum -- build_circs panics below a structural floor and
		// probe_catching converts that into a bump.
		let warmstart = "/tmp/bora/scale/warmstart_caps.json";
		let b_warm = dc_mode == DcMode::ProbeThenFold;
		let p0 = if b_warm && std::path::Path::new(warmstart).exists() {
			crate::determine_config::CapParams::load_json(warmstart)
		} else {
			let mut p = cur.clone();
			p.perc_pats_expansion_rate = cur.perc_pats_expansion_rate.min(16);
			p.perc_pats_expansion_rate_igc =
				cur.perc_pats_expansion_rate_igc.min(16);
			p.avg_active_pats_per_subsig = cur.avg_active_pats_per_subsig.min(2);
			p.avg_active_pats_per_subsig_igc =
				cur.avg_active_pats_per_subsig_igc.min(2);
			p
		};
		// tune over ALL scan files (worst-case across the sample set).
		let mut all_words: Vec<Vec<CF1<C1>>> = jobs.iter()
			.flat_map(|j| j.vec_words.iter().cloned()).collect();
		let mut all_infos: Vec<WordInfo> = jobs.iter()
			.flat_map(|j| j.vec_word_info.iter().cloned()).collect();
		// Also converge against foldpot's preprocessing word: the full-length
		// pseudo-random 0-pad word (driver.rs:2900) it sizes every circuit
		// with. Probing it back-solves caps that exactly cover it, so the
		// fold's 0-word advice passes with NO blind headroom and the forward
		// queue stays at its saturated converged size.
		all_words.push(utils::data::pack_nibbles(
			&utils::data::gen_pad_nibbles_fe::<CF1<C1>>(0, chunk_len * 62)));
		all_infos.push(WordInfo::dummy());
		// concurrency degree for the probe (bounds peak RAM = N ladder clones).
		let n_threads = std::env::var("ZKR_DC_THREADS").ok()
			.and_then(|s| s.parse().ok()).unwrap_or(4);
		log(0, log_level, &format!("DETERMINE_CONFIG: probing {} words over \
			{} threads", all_words.len(), n_threads));
		match determine_config_general::<CF1<C1>,C1,CS1>(rc_db.clone(),
			&all_words, &all_infos, p0, chunk_len,
			lkup_len, max_total_word_len, vec_decrease_level, num_circs, 60,
			n_threads) {
			Ok(new) => {
				log(0, log_level, &format!(
					"DETERMINE_CONFIG RESULT (new): {:?}", new));
				log(0, log_level, &format!(
					"DETERMINE_CONFIG hand cfg (cur): {:?}", cur));
				match compare_caps(&new, &cur) {
					Ok(()) => log(0, log_level,
						&format!("DETERMINE_CONFIG compare_caps: PASS")),
					Err(bad) => log(0, log_level, &format!(
						"DETERMINE_CONFIG compare_caps: FAIL {:?}", bad)),
				}
				// ProbeOnly: report and stop (no folding).
				if dc_mode == DcMode::ProbeOnly { return; }
				// Fold with the converged caps directly: the probe now includes
				// foldpot's 0-pad word (above), so `new` already covers it -- no
				// headroom, so the forward queue stays at its saturated size.
				// Re-apply the neo ladder floors from the RETURNED caps: the
				// tuner's own write is scoped to its call (FloorGuard), and the
				// fold's decreased_copy must see the same flat axis the probe
				// converged against or a lower rung drops below demand.
				// CP's floor is its OWN DB-static bound, not `new.cp_subsigs`:
				// a cp::subsigs bump raises the top rung, but the invariant
				// every rung must clear stays the no-critical-pattern count.
				// DFA laddering is legitimate, so min_dfa_subsigs is untouched.
				if read_global_config().clamav_cfg.b_use_discharge_neo {
					let cp_floor = db.vec_sigs_no_critical_pat.len() + 1;
					let mut c = get_global_config();
					c.min_subsigs = new.subsigs;
					c.min_subsigs_igc = new.subsigs_igc;
					c.min_cp_subsigs = cp_floor.min(new.cp_subsigs);
				}
				log(0, log_level, &format!(
					"DETERMINE_CONFIG: folding with converged caps: {:?}", new));
				if b_warm { let _ = new.save_json(warmstart); } // -> next round
				Some(caps_from_params_general(&new))
			}
			Err(e) => {
				log(0, log_level, &format!("DETERMINE_CONFIG FAILED: {}", e));
				if dc_mode == DcMode::ProbeThenFold {
					panic!("ProbeThenFold: determine_config failed: {}", e);
				}
				return; // ProbeOnly with a failed probe: report and stop.
			}
		}
	};

	// Pick the caps build_circs_adv folds with: tuned per-subset caps when the
	// probe ran (ProbeThenFold), else the caller's hand caps.
	let (cp_cs, sed_cs, dfa_c, cp_igc, sed_igc) = match &tuned {
		Some(t) => (&t.0, &t.1, &t.2, &t.3, &t.4),
		None => (init_cp_capacity_cs, init_sed_capacity_cs, init_dfa_capacity,
			init_cp_capacity_igc, init_sed_capacity_igc),
	};

	let vec_circs = build_circs_adv::<CF1<C1>,C1,CS1>(
		&poseidon_config,
		max_total_word_len,
		chunk_len,
		lkup_len,
		rc_db,
		cp_cs,
		sed_cs,
		dfa_c,
		cp_igc,
		sed_igc,
		vec_decrease_level,
		num_circs,
		b_check_lkup
	);
	log_perf(0, log_level, &format!("ZIP driver step 2: build circs."), &mut gt1);

	// M8 (2026-06-02): capacity-check-only mode. build_circs_adv
	// enforces per-circuit capacity asserts; reaching here means
	// caps are sufficient for this DB+files. Stop before
	// foldpot_main so we can tune caps without paying for folding
	// / Groth16. Toggle via get_global_config().b_dryrun_after_capcheck.
	if read_global_config().b_dryrun_after_capcheck {
		log(0, log_level, &format!(
			"=== M8 DRYRUN: build_circs_adv passed, exiting before \
			 foldpot_main. circs={} ===", vec_circs.len()));
		return;
	}

	// fold-time saturation audit: clear the probe's collectors so the
	// numbers below reflect ONLY the real fold, proving the forward queue
	// is saturated during proving (not just at probe time).
	utils::consts::reset_sat();

	//4. run the foldpot_main
	let lkup = Arc::new(db.lkup);
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
		lkup, vec_circs, &mut jobs, cache_dir).expect("main err");

	log_sat_audit(log_level);

}

/// Run-level saturation audit: peak queue fill vs its matched cap. The
/// NEO line is emitted only when the neo discharge actually ran, so its
/// absence means the legacy path served the run.
fn log_sat_audit(log_level: usize) {
	let pct = |f: usize, c: usize| if c == 0 { 0.0 } else { 100.0 * f as f64 / c as f64 };
	let (ff_cs, fc_cs)   = (utils::consts::get_fwd(false), utils::consts::get_fwd_cap(false));
	let (ff_igc, fc_igc) = (utils::consts::get_fwd(true),  utils::consts::get_fwd_cap(true));
	log(0, log_level, &format!(
		"FOLD FWD SAT: cs fill={}/cap={} ({:.1}%), igc fill={}/cap={} ({:.1}%); \
		 SDE acc max cs={} igc={}",
		ff_cs, fc_cs, pct(ff_cs, fc_cs), ff_igc, fc_igc, pct(ff_igc, fc_igc),
		utils::consts::get_acc(false), utils::consts::get_acc(true)));
	let (qm_cs, qmc_cs) = utils::consts::QM_SAT[0].get();
	let (qm_ig, qmc_ig) = utils::consts::QM_SAT[1].get();
	let (qc_cs, qcc_cs) = utils::consts::QC_SAT[0].get();
	let (qc_ig, qcc_ig) = utils::consts::QC_SAT[1].get();
	if qmc_cs + qmc_ig + qcc_cs + qcc_ig > 0 {
		log(0, log_level, &format!(
			"NEO SAT: Q_m cs={}/{} ({:.1}%) igc={}/{} ({:.1}%); \
			 Q_c cs={}/{} ({:.1}%) igc={}/{} ({:.1}%)",
			qm_cs, qmc_cs, pct(qm_cs, qmc_cs),
			qm_ig, qmc_ig, pct(qm_ig, qmc_ig),
			qc_cs, qcc_cs, pct(qc_cs, qcc_cs),
			qc_ig, qcc_ig, pct(qc_ig, qcc_ig)));
		let (wf_cs, wc_cs) = utils::consts::QM_WRAP_SAT[0].get();
		let (wf_ig, wc_ig) = utils::consts::QM_WRAP_SAT[1].get();
		let (rf_cs, rc_cs) = utils::consts::QM_REAL_SAT[0].get();
		let (rf_ig, rc_ig) = utils::consts::QM_REAL_SAT[1].get();
		let (sf_cs, sc_cs) = utils::consts::QM_SUB_SAT[0].get();
		let (sf_ig, sc_ig) = utils::consts::QM_SUB_SAT[1].get();
		log(0, log_level, &format!(
			"NEO SAT SPLIT: wrap cs={}/{} ({:.1}%) igc={}/{} ({:.1}%); \
			 real cs={}/{} ({:.1}%) igc={}/{} ({:.1}%); \
			 subsig cs={}/{} ({:.1}%) igc={}/{} ({:.1}%)",
			wf_cs, wc_cs, pct(wf_cs, wc_cs),
			wf_ig, wc_ig, pct(wf_ig, wc_ig),
			rf_cs, rc_cs, pct(rf_cs, rc_cs),
			rf_ig, rc_ig, pct(rf_ig, rc_ig),
			sf_cs, sc_cs, pct(sf_cs, sc_cs),
			sf_ig, sc_ig, pct(sf_ig, sc_ig)));
	}
}

/// Aggressive-mode driver: same flow as zkp_driver_adv but builds
/// CS-only circuits from an explicit CS capacity ladder (lowest-cost
/// first, one circuit per entry) via build_circs_adv_aggr. zkp_driver_adv
/// and the non-aggressive path are unchanged.
pub fn zkp_driver_adv_aggr<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, S>
(
	job_id: usize,
	sig_file: &str,
	list_files_to_scan: Vec<String>,
	_logfile: &str,
	b_write_cache: bool,
	cache_dir: &str,
	list_of_dfa_sigs: &str,
	list_of_ised_sigs: &str,
	list_of_ised_igc_sigs: &str,
	chunk_len: usize,
	cs_caps: &Vec<(CpCapacity, SedCapacity, CpCapacity, SedCapacity)>,
	b_check_lkup: bool,
	dc_mode: DcMode,
)
where
	GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
	GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	CS1E: CommitmentScheme<
		C1,
		ProverChallenge = C1::ScalarField,
		Challenge = C1::ScalarField,
		Proof = KZGProof<C1>,
	>,
	<CS1E as CommitmentScheme<C1>>::ProverParams: Send + Sync,
	<CS1E as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C1>>,
	<CS1 as CommitmentScheme<C1>>::VerifierParams: Send + Sync,
	CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>, VerifierParams = PedersenParams<C2>>,
	<CS2 as CommitmentScheme<C2>>::VerifierParams: Send + Sync,
	S: SNARK<C1::ScalarField> + SNARK<<E as Pairing>::ScalarField>,
	<C1 as CurveGroup>::BaseField: PrimeField,
	<C2 as CurveGroup>::BaseField: PrimeField,
	<C1 as Group>::ScalarField: Absorb,
	<C2 as Group>::ScalarField: Absorb,
	for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
	for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
	<E as Pairing>::ScalarField: Absorb,
	C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=E::ScalarField>,
	C2G2: CurveGroup<ScalarField=E::ScalarField>,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField,
		Affine = ark_ec::short_weierstrass::Affine<<C2 as CurveGroup>::Config>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C1::Config: SWCurveConfig,
	<C2 as CurveGroup>::Config: SWCurveConfig,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
	<E as Pairing>::ScalarField: ColEle,
	<S as SNARK<C1::ScalarField>>::ProvingKey: 'static,
	<S as SNARK<C1::ScalarField>>::VerifyingKey: 'static,
	<S as SNARK<<E as Pairing>::ScalarField>>::ProvingKey: Send,
	<S as SNARK<<E as Pairing>::ScalarField>>::VerifyingKey: Send,
{
	//1. build or load the clamdb
	let log_level = LOG1;
	let mut gt1 = GTimer::new();
	log(0, log_level, &format!("=== ZKP driver (aggr) starts ===="));
	// Tuner prerequisites, set BEFORE load_files because they change what the
	// discharge below records: b_estimate_caps populates the per-chunk
	// ChunkPeaks profiles determine_config_aggr partitions (clamav.rs:3376),
	// and b_scale_catch_caperr makes a fold CapErr unwind (catchable by
	// probe_catching) instead of aborting the process. Both are additive: the
	// WordInfo the fold consumes is unchanged. Restored on every exit by
	// AggrDcGuard so DcMode::Off callers, which set these themselves, are
	// untouched.
	struct AggrDcGuard{ est: bool, catch: bool, b: bool }
	impl Drop for AggrDcGuard{
		fn drop(&mut self){
			if self.b {
				let mut c = get_global_config();
				c.b_estimate_caps = self.est;
				c.b_scale_catch_caperr = self.catch;
			}
		}
	}
	let _dc_guard = {
		let b = dc_mode != DcMode::Off;
		let (est, catch) = { let c = read_global_config();
			(c.b_estimate_caps, c.b_scale_catch_caperr) };
		if b {
			let mut c = get_global_config();
			c.b_estimate_caps = true;
			c.b_scale_catch_caperr = true;
		}
		AggrDcGuard{ est, catch, b }
	};
	let poseidon_config = poseidon_canonical_config::<CF1<C1>>();
	let mut vlog = vec![];
	let cfg = default_clamav_cfg();
	let db = ClamavDB::<CF1<C1>>::build_or_load(&cfg, sig_file,
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		&mut vlog, cache_dir, read_global_config().b_read_cache, b_write_cache)
		.expect("build db err");
	if log_level>=LOG1+1{
		db.print_summary(&mut vlog);
	}
	log_perf(0, log_level, &format!("ZIP driver step 1: build DB."), &mut gt1);

	//2. load the files as vec of words
	let mut max_total_word_len = 0;
	let mut jobs = vec![];
	let mut all_vdata: Vec<FailDischargeRecord> = vec![];
	for list_file_to_scan in list_files_to_scan{
		let (vec_words, vec_word_info, vec_word_fnames, vdata) = load_files::<CF1<C1>>(job_id, &list_file_to_scan, &db, &cfg, b_write_cache, cache_dir, chunk_len);
		let total_word_len:usize = vec_words.iter().map(|w| w.len()).sum();
		if total_word_len > max_total_word_len{
			max_total_word_len = total_word_len;
		}
		all_vdata.extend(vdata);
		jobs.push(FoldPotJob{
			vec_words,
			vec_word_info,
			vec_word_fnames,
			idx_individual_prf: 0,
		});
	}
	let lkup_len = db.lkup.get_size();
	log_perf(0, log_level, &format!("ZIP driver step 2: load words and prepare {} jobs.", jobs.len()), &mut gt1);

	//3. build the circuits (CS-only aggressive)
	let rc_db = Arc::new(db.clone());
	// M11: the aggressive determine_config also lives in the run paths
	// (run_dlp_sample_config / full_dlp_sample3), which carry their own vdata
	// and emit a rung ladder; those pass DcMode::Off so they are not re-tuned
	// here. DcMode != Off makes THIS driver tune, mirroring zkp_driver_adv's
	// non-aggressive hop. The non-aggressive probe stays separate.
	let tuned: Option<Vec<crate::determine_config::CapParams>> =
		if dc_mode == DcMode::Off { None } else {
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		let mut words: Vec<Vec<CF1<C1>>> = jobs.iter()
			.flat_map(|j| j.vec_words.iter().cloned()).collect();
		let mut infos: Vec<WordInfo> = jobs.iter()
			.flat_map(|j| j.vec_word_info.iter().cloned()).collect();
		let mut vdata = all_vdata.clone();
		// foldpot sizes every circuit against a full-length 0-pad word
		// (driver.rs:2900), so discharge it into the TUNING set only (never
		// the fold corpus) and let Phase-A size the caps to cover it. Not
		// sufficient alone -- the probe skips foldpot's stricter 0-word
		// preprocessing -- hence the bump-retry loop in step 4.
		{
			let pad = utils::data::gen_pad_nibbles(0, chunk_len * LEGS);
			let pad_f: Vec<CF1<C1>> = pad.iter()
				.map(|x| CF1::<C1>::from(*x as u32)).collect();
			words.push(utils::data::pack_nibbles(&pad_f));
			let (fdr, rec) = quick_discharge_file_by_crit_bag_pm(
				"__0word__", &pad, &db.vec_sigs,
				&db.vec_sigs_no_critical_pat, &db.map_crit_pat,
				&db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, chunk_len, chunk_len);
			vdata.push(fdr); infos.push(rec);
		}
		let est = estimate_config_aggr::<CF1<C1>>(&vdata, &db, &[100],
			&mut vlog);
		let seed = estimated_to_capparams_aggr(&est[0], chunk_len,
			read_global_config().range2_bit, 3);
		let total_word_n: usize = words.iter().map(|w| w.len()).sum();
		let knob = |k: &str, d: usize| std::env::var(k).ok()
			.and_then(|s| s.parse().ok()).unwrap_or(d);
		// ONE full-cap rung by default (collect_scale_data_dlp:6488 explains
		// why): a decrease ladder starves the smaller rung on the 0-pad word.
		let k_max = knob("ZKR_DC_KMAX", 1);
		let n_buckets = knob("ZKR_DC_BUCKETS", 1);
		let peel_pct = knob("ZKR_DC_PEEL", 100);
		let n_threads = knob("ZKR_DC_THREADS", 4);
		log(0, log_level, &format!("DETERMINE_CONFIG (aggr): probing {} \
			words over {} threads", words.len(), n_threads));
		match determine_config_aggr::<CF1<C1>,C1,CS1>(rc_db.clone(), &words,
			&infos, &vdata, seed, chunk_len, lkup_len, total_word_n, k_max,
			n_buckets, 60, n_threads, 8, peel_pct) {
			Ok((lad, hist)) => {
				log(0, log_level, &format!("DETERMINE_CONFIG (aggr) RESULT: \
					{} rungs, hist={:?}", lad.len(), hist));
				log(0, log_level, &format!(
					"DETERMINE_CONFIG (aggr) rung0: {:?}", lad.first()));
				//ProbeOnly: report and stop (no folding).
				if dc_mode == DcMode::ProbeOnly { return; }
				Some(lad)
			}
			Err(e) => {
				log(0, log_level, &format!(
					"DETERMINE_CONFIG (aggr) FAILED: {}", e));
				if dc_mode == DcMode::ProbeThenFold {
					panic!("ProbeThenFold: determine_config_aggr failed: {}",
						e);
				}
				return; //ProbeOnly with a failed probe: report and stop.
			}
		}
	};

	//4. build the circs and fold.
	match tuned {
		//DcMode::Off: unchanged hand-cap path. Keeps the lkup MOVE (no
		//clone), so production runs pay no extra RAM.
		None => {
			let vec_circs = build_circs_adv_aggr::<CF1<C1>,C1,CS1>(
				&poseidon_config,
				max_total_word_len,
				chunk_len,
				lkup_len,
				rc_db,
				cs_caps,
				b_check_lkup
			);
			log_perf(0, log_level, &format!("ZIP driver step 2: build circs."),
				&mut gt1);

			if read_global_config().b_dryrun_after_capcheck {
				log(0, log_level, &format!(
					"=== M8 DRYRUN: build_circs_adv_aggr passed, exiting before \
					 foldpot_main. circs={} ===", vec_circs.len()));
				return;
			}

			// clear the probe's collectors so the audit below reflects ONLY the
			// real fold (same reason as the non-aggressive driver).
			utils::consts::reset_sat();

			let lkup = Arc::new(db.lkup);
			foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
				S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
				lkup, vec_circs, &mut jobs, cache_dir).expect("main err");
		}
		// Tuned: finalize against foldpot's full-0-word advice check
		// (driver.rs:2939), which is stricter than the probe and so can still
		// under-size CP/FSM. Catch that CapErr, bump EVERY rung (each must
		// clear the 0-word on its own), and retry. Failed tries die at the
		// 0-word check before COST/folding, so they are cheap.
		Some(lad) => {
			use crate::determine_config::{caps_from_params_aggr,
				apply_caperr_bumps, probe_catching};
			let mut ladder = lad;
			let mut tries = 0u32;
			loop {
				get_global_config().aggr_needs_subsigs = ladder.first()
					.map(|c| c.aggr_needs_subsigs).unwrap_or(0);
				let caps: Vec<_> = ladder.iter()
					.map(caps_from_params_aggr).collect();
				utils::consts::reset_sat();
				let rcd = rc_db.clone();
				let lk = db.lkup.clone();
				let res = probe_catching(|| {
					let vec_circs = build_circs_adv_aggr::<CF1<C1>,C1,CS1>(
						&poseidon_config, max_total_word_len, chunk_len,
						lkup_len, rcd, &caps, b_check_lkup);
					if read_global_config().b_dryrun_after_capcheck {
						log(0, log_level, &format!("=== M8 DRYRUN: \
							build_circs_adv_aggr passed, exiting before \
							foldpot_main. circs={} ===", vec_circs.len()));
						return Ok(true);
					}
					foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,
						FC<CF1<C1>,C1,CS1>,S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
						Arc::new(lk), vec_circs, &mut jobs, cache_dir)
						.expect("main err");
					Ok(false)
				});
				match res {
					Ok(Ok(b_dry)) => { if b_dry { return; } break }
					Ok(Err(errs)) => {
						let mut changed = false;
						let mut unmapped = vec![];
						for p in ladder.iter_mut() {
							let (c, u) = apply_caperr_bumps(p, true, &errs);
							changed |= c;
							if !u.is_empty() { unmapped = u; }
						}
						tries += 1;
						log(0, log_level, &format!("DETERMINE_CONFIG (aggr): \
							0-word bump try {}: {:?}", tries, errs));
						assert!(changed && unmapped.is_empty(),
							"aggr tuner: 0-word finalize stuck \
							 (unmapped={:?}): {:?}", unmapped, errs);
						assert!(tries <= 30, "aggr tuner: >30 0-word bumps");
					}
					Err(msg) => panic!("aggr tuner: {}", msg),
				}
			}
			log_perf(0, log_level,
				&format!("ZIP driver step 2: build circs."), &mut gt1);
		}
	}

	log_sat_audit(log_level);

}

/// Discharge a bundle of files against a ClamavDB and report the
/// per-approach (CP/SED/ISED/DFA) stats. Ported from the old
/// paper_data_gen main (gen_clamav_data). Standard file names are
/// assumed under config_dir (main.dat, main_dfa.dat, needs_ised.dat,
/// needs_ised_igc.dat, binexec.dat); the report is written under
/// report_dir as discharge_main_binexec.dat.
/// max_word_len = the ZK chunk length (words/F-elements per fold step,
/// as in the test runners). It drives the per-chunk segmentation used
/// by estimate_config (seg_size = max_word_len*62 nibbles); the
/// discharge classification itself stays F-pad-free, so the report is
/// unchanged. percentiles = coverage ladder, e.g. [20,50,100].
pub fn run_db_bundle<F:PrimeField>(config_dir: &str, report_dir: &str,
	b_cache: bool, b_write_cache: bool, b_quick: bool, range_bits: usize,
	max_word_len: usize, percentiles: &[usize], sig_file_name: &str,
	scan_file_name: &str, cache_dir: &str){
	utils::os::print_computer_config(Some("run_db_bundle"));
	utils::consts::get_global_config().range2_bit = range_bits;
	//enable the chunked SED propagation so ChunkPeaks gets the forward-
	//proof counts the estimator back-solves perc / avg_active from.
	utils::consts::get_global_config().b_estimate_caps = true;
	crate::stats_helper::report_all_discharge_approach_stats::<F>(
		&format!("{}/{}", config_dir, sig_file_name), //src sig
		&format!("{}/main_dfa.dat", config_dir), //need_dfa
		&format!("{}/needs_ised.dat", config_dir), //need_ised
		&format!("{}/needs_ised_igc.dat", config_dir), //ised_igc
		&format!("{}/{}", config_dir, scan_file_name), //files to discharge
		&format!("{}/discharge_main_binexec.dat", report_dir), //report
		b_cache, //read cache
		b_write_cache, //write the built DB to cache_dir for reuse
		cache_dir, //cache name
		b_quick,
		max_word_len, percentiles);
}

#[cfg(test)]
pub mod tests_zkp_driver{
	use ark_ff::{PrimeField};
	use utils::consts::{read_global_config, get_global_config, ClamReadMode};
	//use folding_schemes::folding::foldpot::container_config::ColEle;
	use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
	use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
	use ark_groth16::Groth16;
	use folding_schemes::{commitment::{pedersen::Pedersen, kzg::KZG}};
	use crate::zkp_driver::{zkp_driver, zkp_driver_adv,
		zkp_driver_adv_aggr, WordInfo, DcMode};
	use crate::circs::{
		cp_mapper::{CpCapacity},
		sed_mapper::{SedCapacity},
		dfa_mapper::{DfaCapacity},
	};

	type CS1 = Pedersen<Projective>;
	//EXTERNAL commitment KZG for decider
	type CS1E = KZG<'static, Bn254>;
	type CS2 = Pedersen<Projective2>;
	type C1 = Projective;
	type C2 = Projective2;
	type GC1 = GVar;
	type GC2 = GVar2;
	//type FC = SigmaIR1CS_Inst<Fr,Projective,KZG<'static,Bn254>,LK>;
	type S = Groth16<Bn254>;
	type C2G2 = ProjectiveG2;

	/// small data: each cat of signatures got one sample, one 2-Fr word
	/// read the READ me in data/small_data_set/README for the design of sigs
	/// COST: 7GB and 36 sec.
	/// BASELINE 2026-05-31: wall=39.5s, RAM_peak=4.27GB
	///   (pre-ApproxConfig->GlobalConfig refactor; warm cache, test bin)
	#[allow(dead_code)]
	fn small_data<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		// ZKR_USE_NEO=1 routes SDE discharge through neo (M8b broadening
		// experiment); default off keeps test_zkreg_main byte-identical.
		if std::env::var("ZKR_USE_NEO").is_ok() {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
		}
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 8;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1} 
			else {8320}; //needed for 96k lkup entries for 4 chunks
					//twice larger than what's really needed to
					//leave out room to test the empty entries
		get_global_config().log_level = utils::logger::LOG3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; //for dfa 
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;  
		let avg_pats_per_subsig = 3;  
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 23*100; 
		let basis_acc_states = 646;  //6.46 percent
		let basis_pats_in_trace = 1291;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 171;

		let vec_decrease_level = vec![];
		let num_circs = 1; 

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// neo_hard: preserved local hard NON-AGGRESSIVE SDE case for the
	/// neo (App G.1) vs legacy discharge cost comparison. Fresh tiny DFA
	/// (b_read_cache=false), one 8-step tracked-literal sig that keeps a
	/// long carrying step-queue and then discharges. See the config
	/// README in data/debug/neo_hard_set/config_dfa. Runs LEGACY today;
	/// flips to neo once M8b wires DischargeAdvNeoAdvice (default
	/// b_use_discharge_neo=false until then).
	#[allow(dead_code)]
	fn neo_hard<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("neo_hard"));
		// ZKR_USE_NEO=1 routes SDE discharge through discharge_adv_neo
		// (App G.1). Off => legacy discharge_adv. Lets the same runner
		// measure both via the COST report without editing config.
		if std::env::var("ZKR_USE_NEO").is_ok() {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
		}
		get_global_config().snark_cache_dir = "neo_hard".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 14; //must cover total scan nibbles
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {8320};
		get_global_config().log_level = utils::logger::LOG3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/neo_hard_set/config_dfa"; //for dfa
		let max_word= 8; //this is chunk_len (small => multi-chunk carry)
		let sigs = 2; //sed_hard + cp_cover (nibble coverage)
		let subsigs = 3;
		let avg_pats_per_subsig = 10; //sed_hard has 8 literal steps
		let avg_active_pats_per_subsig = knob("ZKR_AVGACT", 8);
		let perc_comp_subsigs = 26;
		let basis_unique_states = 4000;
		let basis_acc_states = 2000; //CapErr floor was 1613
		let basis_pats_in_trace = 4000;
		// legacy fwd fill ~97% at perc=195; neo Q_m only needs ~79 rows
		// (constant queue), so ZKR_USE_NEO tightens perc to ~full Q_m.
		//New8 P4: saturation levers. ZKR_SMALL tunes the CARRIED queue
		//(ResSmall) alone; perc tunes both queues' trace term.
		get_global_config().res_small_cost = knob("ZKR_SMALL", 20);
		let perc_pats_expansion_rate = knob("ZKR_PERC",
			if std::env::var("ZKR_USE_NEO").is_ok() { 45 } else { 195 });

		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);

		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0,
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/debug/neo_hard_set/reports/report.dat", //report
			b_write_cache,
			"neo_hard", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// Runs the preserved neo_hard local hard non-aggressive SDE case.
	/// `cargo test -p zkregplus --release -- test_neo_hard
	///  --show-output --nocapture`
	#[test]
	pub fn test_neo_hard(){
		neo_hard::<Fr>(true);
	}

	/// 8_A end-to-end: AGGRESSIVE fixed-size neo statement must FOLD.
	/// Builds a small aggressive DB (fwd keyword + fanned class) and
	/// runs the full driver over a multi-chunk scan with neo on -- the
	/// per-chunk stmt.len() must stay constant (the 8_A invariant), so
	/// gen_cmF's stmt.len()==stmt_len assert holds across the fold.
	fn neo_hard_aggr<F:PrimeField>(){
		use data_processor::clam_db::ClamavDB;
		use data_processor::clamav::default_clamav_cfg;
		utils::os::print_computer_config(Some("neo_hard_aggr"));
		//ZKR_NO_NEO=1 runs the SAME aggressive dataset via LEGACY
		//discharge (diagnostic: isolate neo coupling vs aggr-general).
		get_global_config().clamav_cfg.b_use_discharge_neo =
			std::env::var("ZKR_NO_NEO").is_err();
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		//keep subsigs = universe (8_A needs subsigs >= U; no shrink)
		get_global_config().aggr_needs_subsigs = 0;
		get_global_config().snark_cache_dir = "neo_hard_aggr".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 14;
		get_global_config().b_read_cache = false;
		get_global_config().basis_failed_subsigs = 10000;
		get_global_config().perc_lkup_share = 8320; //b_check_lkup path
		get_global_config().log_level = utils::logger::LOG3;
		let b_write_cache = !read_global_config().b_read_cache;

		//build the aggressive DB dataset (build_test_db writes sigs.db
		//+ needs_*.txt under data/<dir> and adds the alphabet pad sig).
		let dir = "debug/neo_hard_aggr_set";
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 4;
		cfg.min_bag_len = 2;
		let src_sigs = vec![
			"aggneo.fwd;Engine:51-255,Target:1;0;/HELLO.{0,4}[ab][ab]/"
				.to_string()];
		let base = format!("{}/data/{}", utils::os::proj_root(), dir);
		std::fs::create_dir_all(&base).unwrap();
		ClamavDB::<F>::build_test_db(&cfg, dir, &src_sigs, &vec![],
			&vec![], &vec![]).expect("aggr db");
		//multi-chunk SDE-hard NON-match scan: the ab-class words appear
		//(so CP cannot discharge on an absent critical word) but only
		//BEFORE each HELLO, so HELLO's forward .{0,4} window never sees
		//[ab][ab] -> the sig never completes in-range -> SDE discharges.
		//ZKR_SCANLEN is the DENSITY knob: more cycles => more live
		//locations carried at each tracked step.
		let scan: Vec<u8> =
			b"abab__HELLOwxyz__".to_vec()
			.iter().cloned().cycle().take(knob("ZKR_SCANLEN", 720))
			.collect();
		let scan_path = format!("{}/scan.bin", base);
		std::fs::write(&scan_path, &scan).unwrap();
		utils::os::write_to_file(&format!("{}/binexec.dat", base),
			&scan_path);

		let max_word = 8; //chunk len (small => multi-chunk carry)
		let sigs_n = 2; //aggr + alphabet pad
		let subsigs = 8; //>= universe U (fanout variants); tune if CapErr
		let avg_pats_per_subsig = 6;
		//8_A saturation knob: sizes the neo queue = subsigs*avg_active.
		//tuned so the constant queue covers the densest chunk (~114
		//rows) with high fill -- the paper's saturation lever.
		let avg_active_pats_per_subsig = knob("ZKR_AVGACT", 16);
		let perc_comp_subsigs = 26;
		let basis_unique_states = 4000;
		let basis_acc_states = 2000;
		let basis_pats_in_trace = 4000;
		get_global_config().res_small_cost = knob("ZKR_SMALL", 20);
		let perc_pats_expansion_rate = knob("ZKR_PERC",
			if std::env::var("ZKR_NO_NEO").is_ok() { 200 } else { 45 });
		let init_cp_cap = CpCapacity{ max_word_len: max_word,
			basis_unique_states, subsigs, avg_pats_per_subsig };
		let init_sed_cap = SedCapacity::new(max_word,
			read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs_n, perc_comp_subsigs, basis_unique_states,
			basis_acc_states);
		let init_dfa_cap = DfaCapacity::new(max_word, sigs_n, subsigs);
		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/sigs.db", base),
			&format!("{}/binexec.dat", base),
			&format!("{}/report.dat", base),
			b_write_cache,
			"neo_hard_aggr",
			&format!("{}/needs_dfa.txt", base),
			&format!("{}/needs_ised.txt", base),
			&format!("{}/needs_ised_igc.txt", base),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec![],
			1,
			true
		);
	}

	/// 8_A aggressive fold e2e. `cargo test -p zkregplus --release --
	/// test_neo_hard_aggr --show-output --nocapture`
	#[test]
	pub fn test_neo_hard_aggr(){
		neo_hard_aggr::<Fr>();
	}

	/// Env knob for the New8 P4 comparative sweep, so density and
	/// capacity can be swept without a recompile.
	fn knob(name: &str, dflt: usize) -> usize {
		std::env::var(name).ok()
			.and_then(|s| s.parse::<usize>().ok()).unwrap_or(dflt)
	}

	/// clam_hard: NON-AGGRESSIVE legacy-vs-neo comparison cell over a
	/// small SDE-dense ClamAV subset (924 sigs carrying bounded gaps,
	/// built fresh by data/debug/clam_hard_set/config/gen.py).
	///
	/// ZKR_USE_NEO=1 selects neo, else legacy -- the ONLY difference
	/// between the two runs of a cell. ZKR_SCAN names the manifest, so
	/// easy vs hard is a scan-target swap on one fixed sig set. The
	/// remaining knobs tune capacity against the NEO SAT audit line.
	#[allow(dead_code)]
	fn clam_hard<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("clam_hard"));
		if std::env::var("ZKR_USE_NEO").is_ok() {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
		}
		get_global_config().snark_cache_dir = "clam_hard".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		//must cover total scan nibbles (2^22 = 2 MB) AND the packed
		//subsig_id: non-aggressive splits (16, bits-16), so 22 gives 6
		//bits = 64 subsigs -- the subset's widest sig has 35.
		get_global_config().range2_bit = knob("ZKR_RANGE2", 22);
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {8320};
		get_global_config().log_level = utils::logger::LOG3;
		//ZKR_DRYRUN=1 stops right after the capacity check, so the
		//per-cell minimum-capacity search costs seconds, not a fold.
		get_global_config().b_dryrun_after_capcheck =
			knob("ZKR_DRYRUN", 0) != 0;
		get_global_config().res_small_cost = knob("ZKR_SMALL", 20);
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/clam_hard_set/config";
		let scan = std::env::var("ZKR_SCAN")
			.unwrap_or("binexec.dat".to_string());
		let max_word = knob("ZKR_CHUNK", 64); //chunk_len
		let sigs = knob("ZKR_SIGS", 924);
		//the 40-sig set expands to 247 subsigs (comp_sig::subsigs_cs)
		let subsigs = knob("ZKR_SUBSIGS", 256);
		let avg_pats_per_subsig = knob("ZKR_AVGPATS", 8);
		let avg_active_pats_per_subsig = knob("ZKR_AVGACT", 6);
		let perc_comp_subsigs = knob("ZKR_COMPPERC", 26);
		let basis_unique_states = knob("ZKR_UNIQ", 4000);
		let basis_acc_states = knob("ZKR_ACC", 2000);
		let basis_pats_in_trace = knob("ZKR_TRACE", 4000);
		let perc_pats_expansion_rate = knob("ZKR_PERC", 195);

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

		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1), //src sig
			&format!("{}/{}", set1, scan), //files to discharge
			"data/debug/clam_hard_set/reports/report.dat", //report
			b_write_cache,
			"clam_hard", //cache name
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //sigs needing ised
			&format!("{}/needs_ised_igc.dat", set1), //ised igc
			max_word, //chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec![],
			1, //num_circs
			b_check_lkup
		);
	}

	/// New8 P4 non-aggressive cell. `ZKR_USE_NEO=1 ZKR_SCAN=hard.dat
	/// cargo test -p zkregplus --release -- test_clam_hard
	/// --show-output --nocapture`
	#[test]
	pub fn test_clam_hard(){
		clam_hard::<Fr>(false);
	}

	/// dlp_hard: AGGRESSIVE legacy-vs-neo comparison cell over the five
	/// DLP SITs whose keywords actually drive the paper's worst-NEEDS
	/// Enron files (data/debug/dlp_hard_set/config/gen.py explains the
	/// selection). ZKR_SCAN picks scan_easy.dat or scan_hard.dat -- the
	/// SAME sig set both ways, so the cells differ only in density.
	#[allow(dead_code)]
	fn dlp_hard<F:PrimeField>(){
		utils::os::print_computer_config(Some("dlp_hard"));
		let neo_on = std::env::var("ZKR_USE_NEO").is_ok();
		if neo_on {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
			//0 = derive subsigs*(max_chain+1); measured NEEDS peak
			//on both DLP scans is 0, so the old 5600 was pure slack.
			get_global_config().neo_wrap_keys = knob("ZKR_WRAPKEYS", 0);
		}
		get_global_config().snark_cache_dir = "dlp_hard".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().b_folding_only = false; //REAL decider
		get_global_config().range2_bit = knob("ZKR_RANGE2", 20);
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		//neo's per-chunk advice widens the distinct range-key set, so the
		//dummy self-cover needs more lkup share than the legacy arm.
		get_global_config().perc_lkup_share =
			knob("ZKR_LKSHARE", if neo_on {20} else {1});
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap =
			knob("ZKR_FANOUT", 100);
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().clamav_cfg.b_sde_rep_tight_first_leg = false;
		//ZKR_DRYRUN=1 stops right after the capacity check (see clam_hard)
		get_global_config().b_dryrun_after_capcheck =
			knob("ZKR_DRYRUN", 0) != 0;
		get_global_config().res_small_cost = knob("ZKR_SMALL", 20);
		get_global_config().b_read_cache = false;
		get_global_config().aggr_needs_subsigs = knob("ZKR_NEEDS", 256);

		let set1 = "data/debug/dlp_hard_set/config";
		let scan = std::env::var("ZKR_SCAN")
			.unwrap_or("scan_hard.dat".to_string());
		let max_word = knob("ZKR_CHUNK", 256);
		let sigs = knob("ZKR_SIGS", 111);
		let subsigs = knob("ZKR_SUBSIGS", 500);
		let avg_pats_per_subsig = knob("ZKR_AVGPATS", 4);
		let avg_active_pats_per_subsig = knob("ZKR_AVGACT", 7);
		let perc_comp_subsigs = knob("ZKR_COMPPERC", 20);
		let basis_unique_states = knob("ZKR_UNIQ", 150);
		let basis_acc_states = knob("ZKR_ACC", 600);
		let basis_pats_in_trace = knob("ZKR_TRACE", 700);
		let perc_pats_expansion_rate = knob("ZKR_PERC", 300);

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);

		//igc arm stays a trivial sentinel (same shape as small_debug).
		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);

		let cs_caps = vec![(init_cp_cap, init_sed_cap,
			init_cp_cap_igc, init_sed_cap_igc)];

		let scan_files: Vec<String> = vec![format!("{}/{}", set1, scan)];

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main.dat", set1), //src sig
			scan_files, //manifest of files to discharge
			"data/debug/dlp_hard_set/reports/report.dat", //report
			false, //b_write_cache
			"dlp_hard", //cache name
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&cs_caps,
			false, //b_check_lkup
			//env ZKR_DC picks the aggressive capacity auto-tuner mode.
			//Unset = ProbeThenFold under neo (the hand caps above then act
			//only as the CapErr fallback), Off for legacy. ZKR_DC=0 pins
			//the hand caps for both.
			super::dc_mode_from_env(),
		);
	}

	/// New8 P4 aggressive cell. `ZKR_USE_NEO=1 ZKR_SCAN=scan_easy.dat
	/// cargo test -p zkregplus --release -- test_dlp_hard
	/// --show-output --nocapture`
	#[test]
	pub fn test_dlp_hard(){
		dlp_hard::<Fr>();
	}

	/// small_multi_dnf: permanent local regression repro for the
	/// DfaAdvGadget discharge-combo bug. Same non-aggressive DFA path as
	/// small_data(), but the DFA sig MULTIDNF_cs has a 2-subsig OR-clause
	/// so its discharge combo has count=2 (dnf_step 0,1). That count>=2
	/// case exercises validate_discharge_sig_combo step-2.1, which is
	/// vacuous for the count=1 sigs small_data uses. Buggy code => a per-
	/// step DFA gadget UNSAT => assert!(verify_batch) panics; fixed => the
	/// test passes. Config: data/debug/small_multi_dnf_set/config_dfa.
	fn small_multi_dnf<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_multi_dnf"));
		get_global_config().snark_cache_dir = "small_multi_dnf".to_string();
		// ZKR_USE_NEO=1 routes SDE discharge through neo (same gate as
		// small_data); default off keeps the legacy run byte-identical.
		if std::env::var("ZKR_USE_NEO").is_ok() {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
		}
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 8;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {8320};
		get_global_config().log_level = utils::logger::LOG3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_multi_dnf_set/config_dfa"; //for dfa
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		let subsigs = 4;
		let avg_pats_per_subsig = 3;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 23*100;
		let basis_acc_states = 646;  //6.46 percent
		let basis_pats_in_trace = 1291;   //(at most twice of basis_acc)
		let perc_pats_expansion_rate = 171;

		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);

		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0,
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_multi_dnf_set/reports/report.dat", //report
			b_write_cache,
			"small_multi_dnf", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// small dna: used for debugging the comparison set with reef on
	/// Chromosome 17 dna set.
	/// COST: 7GB and 34 sec.
	/// BASELINE 2026-05-31: wall=35.2s, RAM_peak=4.22GB
	///   (pre-ApproxConfig->GlobalConfig refactor; warm cache, test bin)
	#[allow(dead_code)]
	fn small_dna<F:PrimeField>(){
		utils::os::print_computer_config(Some("small_dna"));
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 8;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {8320}; //needed for 96k lkup entries for 4 chunks
					//twice larger than what's really needed to
					//leave out room to test the empty entries
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_dna/config"; //for dfa 
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;  
		let avg_pats_per_subsig = 3;  
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 33*100; //needs >=3226 for this dataset
		let basis_acc_states = 646;  //6.46 percent
		let basis_pats_in_trace = 1291;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 171;

		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0,
			&format!("{}/sigs.dat",set1), //src sig
			&format!("{}/binexec.dat",set1), //list of files to discharge
			"data/small_nda/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}


	/// small_debug: local aggressive fold+decider, neo-vs-legacy cost.
	/// ZKR_SIZE=light(default)|max sizes to the local box; ZKR_USE_NEO=1
	/// routes SDE discharge through neo. Real Groth16 decider (not probe).
	#[allow(dead_code)]
	fn small_debug<F:PrimeField>(_b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_debug"));
		//ZKR_SIZE=max -> small_email2 full-set caps (~66GB+, maxes the
		//local box); default light -> small_email caps (~15GB). Both run
		//the REAL aggressive fold + Groth16 decider (b_folding_only=false).
		let is_max = std::env::var("ZKR_SIZE")
			.map(|v| v == "max").unwrap_or(false);
		let b_check_lkup = false; //skip in-circuit lkup-share (small set)
		get_global_config().snark_cache_dir = "email_dlp".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().b_folding_only = false; //REAL decider
		get_global_config().range2_bit = if is_max {25} else {20};
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().clamav_cfg.b_sde_rep_tight_first_leg = false;
		get_global_config().b_dryrun_after_capcheck = false;
		//ZKR_USE_NEO=1 routes aggressive SDE discharge through neo;
		//default off = legacy aggressive (byte-identical to small_email).
		let neo_on = std::env::var("ZKR_USE_NEO").is_ok();
		if neo_on {
			get_global_config().clamav_cfg.b_use_discharge_neo = true;
			//neo's constant full-store D-dict advice (d_diff etc.)
			//adds ~1K distinct range keys per chunk; the dummy
			//self-cover needs lk_share >= that (perc=1 -> 158).
			get_global_config().perc_lkup_share = 20;
			//T_qm wrap budget: 0 = derive subsigs*(max_chain+1).
			//The old 5600 charged the whole 10400-row demand to
			//wrap; the split gauge shows 800 wrap + 8800 real.
			get_global_config().neo_wrap_keys = knob("ZKR_WRAPKEYS", 0);
		}
		//No DB cache: always rebuild fresh (avoids the 2GiB per-file
		//write truncation on the full set; the corpus is small enough).
		get_global_config().b_read_cache = false;
		let b_write_cache = false;
		let set1 = "data/debug/small_email/config";
		let max_word = 256; //~17 fold steps over ~260k nibbles

		//size-specific caps: light=small_email, max=small_email2.
		get_global_config().aggr_needs_subsigs = if is_max {700} else {256};
		let sig_file = if is_max {"main_full.dat"} else {"main.dat"};
		let scan_file = if is_max {"binexec2.dat"} else {"binexec.dat"};
		let sigs = if is_max {12} else {10};
		let subsigs = if is_max {700} else {500};
		let avg_pats_per_subsig = 4;
		let avg_active_pats_per_subsig = 7;
		let perc_comp_subsigs = 20;
		let basis_unique_states = if is_max {350} else {150};
		let basis_acc_states = if is_max {1200} else {600};
		let basis_pats_in_trace = if is_max {1400} else {700};
		let perc_pats_expansion_rate = 300;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);

		//8_C: neo seeds the per-chunk NEEDS set (capacity budgets), so
		//the igc arm keeps the same trivial-arm sentinel as legacy.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);

		//light: 2-rung ladder (small_email); max: 1 rung (small_email2).
		let cs_caps = if is_max {
			vec![(init_cp_cap, init_sed_cap,
				init_cp_cap_igc, init_sed_cap_igc)]
		} else {
			let r0_subsigs = 8;
			let r0_cp = CpCapacity{ max_word_len: max_word,
				basis_unique_states,
				subsigs: r0_subsigs, avg_pats_per_subsig };
			let r0_sed = SedCapacity::new(
				max_word, read_global_config().range2_bit,
				r0_subsigs, avg_pats_per_subsig, avg_active_pats_per_subsig,
				basis_pats_in_trace, perc_pats_expansion_rate,
				sigs, perc_comp_subsigs,
				basis_unique_states, basis_acc_states);
			vec![
				(r0_cp, r0_sed,
					init_cp_cap_igc.clone(), init_sed_cap_igc.clone()),
				(init_cp_cap, init_sed_cap,
					init_cp_cap_igc, init_sed_cap_igc)]
		};

		let scan_files: Vec<String> = vec![
			format!("{}/{}", set1, scan_file)];

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/{}", set1, sig_file), //src sig
			scan_files, //list of files to discharge
			"data/debug/small_email/reports/report_zk.dat", //report
			b_write_cache,
			"email_data", //cache name (SHARED w/ small_email*)
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&cs_caps,
			b_check_lkup,
			DcMode::Off, //hand caps: no auto-tune (env cannot override)
		);
	}

	/// small data: multiple parallel jobs.
	/// COST  4 jobs: 14 GB and 228 sec (reason: folding doesn't take much time)
	/// BASELINE 2026-05-31: wall=200.6s, RAM_peak=6.25GB (4 jobs)
	///   (pre-ApproxConfig->GlobalConfig refactor; warm cache, test bin)
	#[allow(dead_code)]
	fn small_data_par<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data_par"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {10000}; //enough lkup coverage for binexec_p* (4 files)
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; //for dfa
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		//let subsigs = 6; GOOD setting
		let subsigs = 4;
		let avg_pats_per_subsig = 3;
		let avg_active_pats_per_subsig = 2; //good value 0 (does not matter)
		//let avg_subsig_per_sig = 2; //NO NEED ANY MORE
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 25*100;
		let basis_acc_states = 807;  //6.46 percent
		let basis_pats_in_trace = 1500;   //(at most twice of basis_acc_states)
		let perc_pats_expansion_rate = 200;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);


		let scan_files: Vec<String> = (1..=4).map(|i|
			format!("{}/binexec_p{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(0,
			&format!("{}/sigs.dat",set1), //src sig
			scan_files, //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap, //as igc
			&init_sed_cap, //as igc
			&vec![],
			1,
			b_check_lkup, DcMode::Off
		);
	}


	/// 2026-06-22: small_par_full_snark — identical config to
	/// small_data_par but runs the FULL Groth16 decider
	/// (b_light_test=false) and produces ONE proof only
	/// (b_one_proof: every job folds, only Job 0 proves). For a
	/// server full-snark validation run. Keep capacities in sync with
	/// small_data_par if that is tuned.
	#[allow(dead_code)]
	fn small_par_full_snark<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_par_full_snark"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().b_light_test = false; // full snark
		get_global_config().b_one_proof = true;    // only Job 0 proves
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {10000}; //enough lkup coverage for binexec_p* (4 files)
		get_global_config().log_level = utils::logger::LOG3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set/config_dfa"; //for dfa
		let max_word= 1; //this is chunk_len
		let sigs = 2; //good setting: 2
		let subsigs = 4;
		let avg_pats_per_subsig = 3;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 26;  //26 for subsigs=4, 34 for subsigs=3
		let basis_unique_states = 25*100;
		let basis_acc_states = 807;  //6.46 percent
		let basis_pats_in_trace = 1500;
		let perc_pats_expansion_rate = 200;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states
		);
		let init_dfa_cap= DfaCapacity::new(max_word, sigs, subsigs);

		let scan_files: Vec<String> = (1..=4).map(|i|
			format!("{}/binexec_p{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(0,
			&format!("{}/sigs.dat",set1),
			scan_files,
			"data/small_data_set/reports/report.dat",
			b_write_cache,
			"small_20",
			&format!("{}/dfa.dat", set1),
			&format!("{}/ised.dat", set1),
			&format!("{}/ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap,
			&init_sed_cap,
			&vec![],
			1,
			b_check_lkup, DcMode::Off
		);
	}



	/// the sigs are the same as small data
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// COST: 18GB and 160 sec
	/// BASELINE 2026-05-31: wall=207.5s, RAM_peak=25.1GB
	///   (pre-ApproxConfig->GlobalConfig refactor; warm DB cache, test bin)
	///   ADJUSTED to run green: b_read_snark_cache true->false (no key
	///   cache present, so regen -> higher RAM/time vs old note);
	///   added perc_lkup_share=200 (lk_share*chunks must cover
	///   lkup_len 271354); basis_unique_states 5->6 (CapErr pack.rs).
	#[allow(dead_code)]
	fn small_data2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data2"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false; //baseline: regen keys
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200}; //lk_share*chunks must cover lkup_len(271354)
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa
		let max_word= 512; 
		let sigs = 2; 
		let subsigs = 4; 
		let avg_pats_per_subsig = 4; 
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_pats_in_trace = 6;
		let perc_comp_subsigs = 26;
		let basis_unique_states = 6; //CapErr: pack.rs needs >=6
		let basis_acc_states = 2;
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);

		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states: basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig: avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, 
			subsigs, 
			 avg_pats_per_subsig, 
			 avg_active_pats_per_subsig, 
			 basis_pats_in_trace-1, 
			 perc_pats_expansion_rate,

			 sigs, 
			 perc_comp_subsigs,
			 basis_unique_states,
			 basis_acc_states,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			vec![format!("{}/binexec.dat",set1)], //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec![],
			1,
			b_check_lkup, DcMode::Off
		);
	}

	/// This function is used for debugging
	#[allow(dead_code)]
	fn small_data_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data_debug"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 24;
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512*4; 
		let sigs = 2; 
		let subsigs = 4; 
		let avg_pats_per_subsig = 4; 
		let avg_active_pats_per_subsig = 0; //good value 0, actually does
			//not matter?
		let perc_comp_subsigs = 26; 
		let basis_unique_states = 5; 
		let basis_acc_states = 400; 
		let basis_pats_in_trace = 450; 
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs_debug2.dat",set1), //src sig
			&format!("{}/binexec_debug2.dat",set1), //list of files to discharge
			"data/small_data_set/reports/report.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec![],
			1,
			b_check_lkup
		);
	}


	/// the sigs are the same as small data2
	/// has 1 long words (1k-packed nibbles - around 31kb)
	/// has 2 second long word (eady and almost no match)
	/// read the READ me in data/small_data_set2/README for the design of sigs
	/// Difference: 2 categories and 2 circs each (multiple circs) -> 4 circs
	/// for testing circ selection
	/// WARNING: you need 128GB RAM for small_data3 as it has 4 circs
	/// at the last stage of snark generation it's costly.
	#[allow(dead_code)]
	fn small_data3<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data3"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().min_subsigs = 3;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 8;  //good value 2
		let subsigs = 8;  //good value 4
		let avg_pats_per_subsig = 3;  //good value 4
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_acc_states = 10;  //good value 2
		let basis_pats_in_trace = 22;  //good value 4
		let perc_comp_subsigs = 104;  //good value 34 
		let basis_unique_states = 20;  //good value 5 * 4 and similar for all others
		let dfa_sigs = 4;
		let dfa_subsigs= 2*dfa_sigs;
		let perc_pats_expansion_rate = 160;

		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let perc_pats_expansion_rate_igc = 136 ;
		let basis_pats_in_trace_igc = 20;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs.dat",set1), //src sig
			vec![format!("{}/binexec2.dat",set1)], //list of files to discharge
			"data/small_data_set/reports/small_data3.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// This allows to try 4 circ on variety of small files
	/// setting min_idx and max_idx to try 1M, 2M, 4M files.
	/// BASELINE 2026-05-31: wall=969s(16:09), RAM_peak=27.3GB (idx=1,2M)
	///   (pre-ApproxConfig->GlobalConfig refactor; warm DB cache, test bin)
	///   ADJUSTED to run green: b_read_snark_cache true->false (no key
	///   cache present -> regen); added perc_lkup_share=200
	///   (lk_share 63488 * chunks 135 >> lkup_len 313433).
	#[allow(dead_code)]
	fn small_data4<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_data4"));
		get_global_config().snark_cache_dir = "small_20".to_string();
		get_global_config().b_read_snark_cache = false; //baseline: regen keys
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 18;
		get_global_config().b_read_cache = false;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200}; //tune from lk_share*chunks>=lkup_len guard
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_data_set2/config_dfa"; //for dfa 
		let max_word= 512; 
		let sigs = 4;  //good value 2
		let subsigs = 4;  //good value 4
		let avg_pats_per_subsig = 3;  //good value 4
		let avg_active_pats_per_subsig = 1; //good value 0, actually does
			//not matter?
		let basis_acc_states = 5;  //good value 10 
		let basis_pats_in_trace = 11;  //good value 22 
		let perc_comp_subsigs = 40;  //good value 104 
		let basis_unique_states = 16;  //good value 20
		let dfa_sigs = 2;
		let dfa_subsigs= 2*dfa_sigs;
		let perc_pats_expansion_rate = 40; //good value 160

		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let perc_pats_expansion_rate_igc = 78; //good value 136
		let basis_pats_in_trace_igc = 30; //good value 20

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let files = vec![
			vec![format!("{}/sample_1M.dat",set1)], 
			vec![format!("{}/sample_2M.dat",set1)], 
			vec![format!("{}/sample_4M.dat",set1)], 
		];
		let idx = 1; //max 2
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/sigs2.dat",set1), //src sig
			files[idx].clone(),
			"data/small_data_set/reports/small_data4.dat", //report
			b_write_cache,
			"small_20", //cache name
			&format!("{}/dfa.dat", set1), //signs that need dfa
			&format!("{}/ised.dat", set1), //signs that need ised 
			&format!("{}/ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// the sigs are the FULL SET of sigs
	/// However, just run a small file
	#[allow(dead_code)]
	fn full_data1<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data1"));
		get_global_config().snark_cache_dir = "full_data".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa 
		//let max_word= 512; 
		let max_word= 512 * 4; 
		let sigs = 320;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 500; //last known good vlaue: 1900
		let basis_acc_states = 1000; //9 cpercent
		let basis_pats_in_trace = 1200; //10 percent
		let perc_pats_expansion_rate = 200;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_1.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}
	/// the sigs are the FULL SET of sigs
	/// It runs a small but challenging file _codecs_hk.so (158kb)
	#[allow(dead_code)]
	fn full_data2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data2"));
		get_global_config().snark_cache_dir = "full_data".to_string();
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		//let max_word= 512;
		let max_word= 512 * 4;
		let sigs = 320;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 1000; //ld vlaue 19 cpercent
	//	let basis_acc_states = 200; //old value 9 cpercent --> GOOD setting
	 //   let basis_pats_in_trace = 250 ; //1.2 * basis_acc_states
		let basis_acc_states = 1200; //old value 9 cpercent --> GOOD setting
		let basis_pats_in_trace = 1440 ; //1.2 * basis_acc_states
		let perc_pats_expansion_rate = 100;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let dfa_sigs = 2;
		let dfa_subsigs= 3;
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);


		zkp_driver::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			&format!("{}/binexec_2.dat",set1), //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&vec_decrease_level,
			num_circs,
			b_check_lkup
		);
	}

	/// the sigs are the FULL SET of sigs
	/// It runs a large but difficult file: gdb (6.6M)
	/// COST: stmt_len: 12.7M => all_w_e = 42M => circ1 100M R1CS
	/// prove_step: 39 sec
	/// if using max_word 512 *8 (128kb) => it's 21M. prove_step: 60 sec
	/// IMPROVEC COST: after applying the tricks of separating
	///	igc and cs. stmt_len: 10M, all_w_e: 33M => circ1 72M R1CS
	#[allow(dead_code)]
	fn full_data3<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data3"));
		get_global_config().b_read_snark_cache = true;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		let max_word= 512 * 4;
		let sigs = 350;
		let subsigs = 500; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 3;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![];
		let num_circs = 1; 
		let basis_unique_states = 1600; //15 cpercent
		let basis_acc_states = 1200; //9 cpercent
		let basis_pats_in_trace = 2200; //old value 100 cur value 1/1000.
		let dfa_sigs = 3;
		let dfa_subsigs= 4;
		let perc_pats_expansion_rate = 100;
		//let avg_subsig_per_sig = 3;

		let shrink=8;
		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
	   let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs/2,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace/shrink,
			perc_pats_expansion_rate,

			sigs/shrink,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states/shrink,
		);


		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
   0, 
			&format!("{}/main.dat",set1), //src sig
			vec![format!("{}/binexec_3.dat",set1)], //list of files to discharge
			"data/debug/full_data_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// This runs the full signature set on the most difficult files
	/// each is 15-32MB file
	/// details:
	/// 1: -rw-rw-r-- 1 anon anon 33554416 Jun  8  2025 anthoscli__00
	/// 2: -rw-rw-r-- 1 anon anon 33554416 Jun  8  2025 anthoscli__01
	/// 3: -rwxrwxr-x 1 anon anon 22720144 Jun  8  2025 libpython3.9.so (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 4: -rwxrwxr-x 1 anon anon 22720144 Jun  8  2025 libpython3.9.so.1.0 (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 5: -rwxrwxr-x 1 anon anon 20785824 Jun  8  2025 libicudata.so.50.2 (Max Acc Rate: 5.32%, Max Pat Rate: 5.38%)
	/// 6: -rwxrwxr-x 1 anon anon 15603008 Jun  8  2025 cc1plus (Max Acc Rate: 12.33%, Max Pat Rate: 12.36%)
	/// 7: -rwxrwxr-x 1 anon anon 15022144 Jun  8  2025 data/samples/binexec_merged128k/f951 (Max Acc Rate: 12.42%, Max Pat Rate: 12.45%)
	/// 8: -rwxrwxr-x 1 anon anon 13676928 Jun  8  2025 data/samples/binexec_merged128k/lto1 (Max Acc Rate: 11.57%, Max Pat Rate: 11.63%)
	/// Total: 173MB. 
	#[allow(dead_code)]
	fn full_data4<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_data4"));
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = true;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 361; // OLD value: 150
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().min_basis_unique_states= 600; //OLD value 20
		get_global_config().min_basis_acc_states =  113; // OLD value: 100
		get_global_config().min_basis_pats_in_trace=  134; // OLD value: 110
		get_global_config().min_dfa_subsigs =  3; //OLD val 2
		get_global_config().min_avg_pats_per_subsig= 8; // OLD value: 6
		get_global_config().min_dfa_sigs = 2; // OLD value: 0 (default)
		get_global_config().b_read_cache = true;
		get_global_config().perc_lkup_share = 143; //this is for
			//full_clam() setting (700MB linux data for 38k clamav) in 8 jobs
			//see full_clam

		let b_write_cache = !read_global_config().b_read_cache;
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 1300; //15 cpercent
		let vec_decrease_level = vec![2];
		let num_circs = 2; 
		let basis_acc_states = 750; // 1260; //last good value 1800
		let basis_pats_in_trace = 820; //1400; //last good value 3000
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = 6;
		let dfa_subsigs= 6;
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		//just ranges allowed 0 to 8test one at a time
		//APPROACH 1:
		let min = 0; //starting: 0
		let max = 1; //max possible: 8

		//APPROACH 2:
		//IF using min = 8, max=9 it uses binexec_4_9.dat (which
		//has ALL the files listed (about 87MB)
		//let min = 8;
		//let max = 9;
				//
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		//let num_jobs:usize = 1;
		//let num_jobs:usize = 16;
		let data_files = vec![format!("{}/sample_1M.dat",set1)];

		for _id in min..max{
			zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
	0, 
				&format!("{}/main.dat",set1), //src sig
				//vec![format!("{}/binexec_4_{}.dat",set1, id+1)], //list of files to discharge
								data_files.clone(),
				"data/debug/full_data_set/reports/report2.dat", //report
				b_write_cache,
				"full_data", //cache name
				&format!("{}/main_dfa.dat", set1), //signs that need dfa
				&format!("{}/needs_ised.dat", set1), //signs that need ised 
				&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
				max_word, //this is the chunk len
				&init_cp_cap,
				&init_sed_cap,
				&init_dfa_cap,
				&init_cp_cap_igc,
				&init_sed_cap_igc,
				&vec_decrease_level,
				num_circs,
				b_check_lkup, DcMode::Off
			);
		}
	}
	
	
	/// Used for explorting parallel execution efficiency.
	/// For b_small = true, can run with 16 GB
	/// For b_small = false,needs 128GB. 4 jobs fills 50% cpu.
	#[allow(dead_code)]
	fn full_par<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_par"));
		let b_small = true;
		get_global_config().b_read_cache = true;

		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 148;
		get_global_config().b_light_test = true;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().b_folding_only = true;
		let b_write_cache = !read_global_config().b_read_cache;


		let set1 = "data/debug/full_par_set/config/"; //for dfa
		let max_word= if b_small {512} else {512 * 4};
		let sigs = if b_small {20} else {400};
		let subsigs = if b_small {142} else {580}; 
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = if b_small {500} else {2000}; //15 cpercent
		let vec_decrease_level = if b_small {vec![]}
			else { vec![2,1] };
		let num_circs = if b_small {1} else {3}; 
		let basis_acc_states = if b_small {200} else {1260}; 
		let basis_pats_in_trace = if b_small {220} else {1400}; 
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = if b_small {1} else {6};
		let dfa_subsigs= if b_small {1} else {6};
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let num_jobs:usize = 1;
		//let num_jobs:usize = 16;

		let data_files = (0..num_jobs).map(|i|
			format!("{}/sample_1M_{}.dat",set1,i)
		).collect::<Vec<String>>();

		let suffix = if b_small { "_small" } else { "" };
		let [main_file, main_dfa_file, needs_ised_file,
			needs_ised_igc_file] =
			["main", "main_dfa", "needs_ised", "needs_ised_igc"]
			.map(|n| format!("{}/{}{}.dat", set1, n, suffix));

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&main_file,
			data_files,
			"data/debug/full_par_set/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&main_dfa_file, //signs that need dfa
			&needs_ised_file, //signs that need ised
			&needs_ised_igc_file, //sigs that need ised igc
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// Like `full_data4`, but feeds binexec_4_1..binexec_4_8 (8 files,
	/// excluding the merged binexec_4_9) into a single `zkp_driver_adv`
	/// call so foldpot runs them as parallel jobs. Capacities and the
	/// config dir are taken from `full_data4`; parallel/snark knobs
	/// come from `full_par`. Total 173MB. do not generate snark proof.
	/// This function is used to figure out the optimized circ setting
	/// for clamav data (with the most difficult files).
	#[allow(dead_code)]
	fn full_par2<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_par2"));
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 148;
		get_global_config().min_avg_pats_per_subsig = 4;
		get_global_config().b_light_test = true;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().b_folding_only = true;
		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_data_set/config/"; //for dfa
		let max_word= 512 * 8; //compared with full4, we are doing 128k seg 
		let sigs = 400;
		let subsigs = 562;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 1300; //OLD VLAUE: 2000
		let vec_decrease_level = vec![];
		let num_circs = 1;
		let basis_acc_states = 750; //OLD VALUE: 1260;
		let basis_pats_in_trace = 820; //OLD VALUE: 1400;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 6;
		let dfa_subsigs= 6;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs/2,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let data_files = (1..=8).map(|i|
			format!("{}/binexec_4_{}.dat", set1, i)
		).collect::<Vec<String>>();

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1),
			data_files,
			"data/debug/full_data_set/reports/report2.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}


	/// This tests the full clamav signatures against linux executables
	/// There are 756MB Linux binary executable
	/// We split them into 8 jobs.
	/// E.g., run on m3m machine with 2TB (xx cpu)
	/// Can finish in xxx hrs.
	#[allow(dead_code)]
	fn full_clamav<F:PrimeField>(b_check_lkup: bool, b_light_test: bool,
		b_setup: bool, read_mode: ClamReadMode, read_pct: usize){
		utils::os::print_computer_config(Some("full_clamav"));
		//extra setting
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = b_setup;
		get_global_config().b_read_snark_cache = !b_setup;
		get_global_config().range2_bit = 26;
		let _ = b_light_test; // forced full snark below
		get_global_config().b_light_test = false; // full snark (one proof)
		get_global_config().b_one_proof = false;  // every job proves
		// full_clam two-half NUMA scheme (env-driven; unset = unchanged).
		get_global_config().clam_read_mode = read_mode;
		get_global_config().clam_read_pct = read_pct;
		if let Ok(v) = std::env::var("ZKR_CLAM_ONE_PROOF") {
			get_global_config().b_one_proof = v == "1"; }
		if let Ok(v) = std::env::var("ZKR_CLAM_FOLD_ONLY") {
			get_global_config().b_folding_only = v == "1"; }
		if let Ok(p) = std::env::var("ZKR_SNARK_WAIT_FLAG") {
			get_global_config().snark_wait_flag = Some(p); }
		// NewP3 probe knobs, mirroring clam_hard/dlp_hard. Both OFF by
		// default: production full_clam behavior is unchanged.
		if std::env::var("ZKR_USE_NEO").is_ok() {
			get_global_config().clamav_cfg.b_use_discharge_neo = true; }
		get_global_config().b_dryrun_after_capcheck =
			knob("ZKR_DRYRUN", 0) != 0;
		// The lkup-share invariant only holds at full per-job data;
		// partial-load (debug/numa) modes false-trip it. The driver sets
		// ZKR_CLAM_CHECK_LKUP=1 only for production, 0 otherwise. Unset =
		// keep the caller's value (bare cargo test unchanged).
		let b_check_lkup = std::env::var("ZKR_CLAM_CHECK_LKUP")
			.map(|v| v == "1").unwrap_or(b_check_lkup);
		get_global_config().min_subsigs = 368; // OLD value: 361
		get_global_config().min_basis_unique_states= 1054; // OLD value: 600
		get_global_config().min_basis_acc_states =  268; // OLD value: 113
		get_global_config().min_basis_pats_in_trace=  295; // OLD value: 134
		get_global_config().min_avg_pats_per_subsig= 8; // OLD value: 6
		get_global_config().min_dfa_sigs = 3; // OLD value: 2
		get_global_config().min_dfa_subsigs =  3; //OLD val 2
		get_global_config().n_par_snark = 1;            // part 1 (main): 1
		get_global_config().n_par_snark_cp = 1;         // part 2 (cp): 1
		// outer cap auto (n_par_snark_total=0) = sum = 2 -> max 2 at a time
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143; //this is for
		get_global_config().log_level = utils::logger::LOG3;
			//700MB data in 8 jobs and 256M lkup entries
			//so we have per job: 90MB data = 180M nibbles
			// then: 256/180 * 100 = 142.2% that's 142
		// The two-half split is by whole manifest, so each job still reads a
		// FULL manifest (same per-job data as the 8-job run) -> no per-job
		// scaling needed; base 143 holds for prod. The debug/numa pct trim
		// shrinks per-job data, so those modes keep the check OFF instead.
		// ZKR_CLAM_LKUP_SHARE overrides the share outright as a safety hatch
		// (no recompile) if a job ever trips the check.
		let _ = read_pct;
		if let Some(v) = std::env::var("ZKR_CLAM_LKUP_SHARE").ok()
			.and_then(|s| s.parse::<usize>().ok()) {
			get_global_config().perc_lkup_share = v;
		}


		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_clamav/config/"; //for dfa
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580; //220 for prev db
		let avg_pats_per_subsig = 8; //old value 8
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2; 
		let basis_unique_states = 1300; //2000; //15 cpercent
		let basis_acc_states = 750; //1260; //last good value 1800
		let basis_pats_in_trace = 820; //last good value 3000
		let basis_acc_states_igc = basis_acc_states ; //9 cpercent
		let basis_pats_in_trace_igc = basis_pats_in_trace;
			//old value 100 cur value 1/1000.
		let dfa_sigs = 8;
		let dfa_subsigs= 8;
		let perc_pats_expansion_rate = 104; //old good value 2
		let perc_pats_expansion_rate_igc = 2;
		//let avg_subsig_per_sig = 3;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word, 
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs, 
			avg_pats_per_subsig, 
			avg_active_pats_per_subsig, 
			basis_pats_in_trace, 
			perc_pats_expansion_rate,
			sigs, 
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
 		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
			//avg_subsig_per_sig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		// Two-half scheme: split is by whole manifest. There are 8 manifests
		// (binexec_p0..p7). Full = all 8 jobs; FirstHalf = jobs 0-3 (part1);
		// SecondHalf = jobs 4-7 (part2). Per-job data is a full manifest in
		// every mode, so the lkup share is unchanged from the 8-job run.
		let scan_files: Vec<String> = if b_setup {
			(0..1).map(|i|
				format!("{}/sample_1M_{}.dat", set1, i)).collect()
		} else {
			let (js, je) = match read_mode {
				ClamReadMode::Full       => (0, 8),
				ClamReadMode::FirstHalf  => (0, 4),
				ClamReadMode::SecondHalf => (4, 8),
			};
			(js..je).map(|i|
				format!("{}/binexec_p{}.dat", set1, i)).collect()
		};
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1), //src sig
			scan_files, //list of files to discharge
			"data/debug/full_clamav/reports/report2.dat", //report
			b_write_cache,
			"full_data", //cache name
			&format!("{}/main_dfa.dat", set1), //signs that need dfa
			&format!("{}/needs_ised.dat", set1), //signs that need ised 
					//actually not used
			&format!("{}/needs_ised_igc.dat",set1), //sigs that need ised igc
					//actually not used
			max_word, //this is the chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}


	/// full_clam_bisect: 8-way concurrent bisection of job 3's verify_batch
	/// failure. Faithful clone of full_clamav (b_setup=false): SAME config and
	/// SAME capacities, so the cached full_clamav g16 keys are reused read-only
	/// and circuit sizes match. Differs ONLY in (1) per-job scan list from env
	/// (ZKR_BISECT_DIR holds slice_0.dat..slice_{N-1}.dat, ZKR_BISECT_NJOBS=N)
	/// and (2) report under data/debug/full_clam_bisect/. b_one_proof stays
	/// false so every share proves+verifies and the failing share's
	/// log_job_{id}.txt carries BATCH PROOF VERIFICATION FAILED. Splits ONLY
	/// job 3's list; never calls or modifies full_clamav().
	fn full_clam_bisect<F:PrimeField>(){
		utils::os::print_computer_config(Some("full_clam_bisect"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false; // read-only key reuse
		get_global_config().b_read_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = false; // full snark
		get_global_config().b_one_proof = false;  // every share proves+verifies
		if let Ok(v) = std::env::var("ZKR_BISECT_FOLD_ONLY") {
			get_global_config().b_folding_only = v == "1"; }
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states= 1054;
		get_global_config().min_basis_acc_states =  268;
		get_global_config().min_basis_pats_in_trace=  295;
		get_global_config().min_avg_pats_per_subsig= 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs =  3;
		get_global_config().n_par_snark = 1;
		get_global_config().n_par_snark_cp = 1;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;
		get_global_config().log_level = utils::logger::LOG3;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_clamav/config/"; // DB/dfa/main: read-only
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states ;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs= 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		// vs full_clamav: per-job scan list from env (N shares of job 3).
		let dir = std::env::var("ZKR_BISECT_DIR")
			.expect("ZKR_BISECT_DIR must point at the slice dir");
		let n_jobs: usize = std::env::var("ZKR_BISECT_NJOBS").ok()
			.and_then(|s| s.trim().parse().ok()).unwrap_or(8);
		let scan_files: Vec<String> = (0..n_jobs)
			.map(|i| format!("{}/slice_{}.dat", dir, i)).collect();
		// vs full_clamav: report under our own folder.
		let report = "data/debug/full_clam_bisect/reports/report2.dat";

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1),
			scan_files,
			report,
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			std::env::var("ZKR_BISECT_CHECK_LKUP")
				.map(|s| s.trim()!="0").unwrap_or(true),
			DcMode::Off
		);
	}




	#[test]
	pub fn test_full_clam_bisect(){
		full_clam_bisect::<Fr>();
		utils::logger::flush_logger();
		let sentinel = format!("{}/data/cache/run_complete.sentinel",
			utils::os::proj_root());
		let _ = std::fs::write(&sentinel, "ok\n");
	}

	/// full_dna: ZK discharge of the full clean chr17 sample
	/// (NC_000017.11.reef.bin, 41.6MB) against the 27,501-sig DNA DB.
	/// Light-test, no prior snark setup. Single job (the file is
	/// offset-anchored, so it can't be split across jobs). Capacities
	/// inferred from test_db_bundle's discharge stats on the same
	/// sample; basis_unique_states and perc_pats_expansion_rate are
	/// starting values that the capacity self-check (CapErr back-solve
	/// in discharge_adv / fsm_adv) refines on the first run.
	#[allow(dead_code)]
	fn full_dna<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_dna"));
		get_global_config().snark_cache_dir = "dna_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = false; // full snark (was true)
		get_global_config().b_one_proof = true;   // emit ONE proof only
		get_global_config().range2_bit = 27; //80.09M-nibble max offset
		//min_* floors set LOW (DNA workload is tiny vs clamav)
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().log_level = utils::logger::LOG3;
		//~200 needed when b_check_lkup (164M lkup / ~328 chunks);
		//1 when not checking (panic guard is gated on b_check_lkup).
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200};

		get_global_config().b_read_cache = true; //reuse cached DNA DB
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/paper_data/dna/config";
		let max_word = 512 * 8; //4096 -> ~328 folding steps
		let sigs = 20; //crit/SED peak = 17 (clean sample) + headroom
		let subsigs = 20; //1 subsig/sig
		let avg_pats_per_subsig = 1; //single literal pattern
		let avg_active_pats_per_subsig = 1;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 6500; //CapErr crept 1837->1906; +hdrm
		let basis_acc_states = 2; //max_seg acc rate ~0.39 bp
		let basis_pats_in_trace = 4; //max_seg_pat_rate ~0.39 bp +hdrm
		let perc_pats_expansion_rate = 200; //START; CapErr back-solves
		let dfa_sigs = 0; //0 reached DFA + margin
		let dfa_subsigs = 0;
		let vec_decrease_level = vec![];
		let num_circs = 1;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word,                  //max_word_len: packed words per chunk
			read_global_config().range2_bit, //acdfa_state_part_bits
			subsigs,                   //subsigs: SED universe size
			avg_pats_per_subsig,       //avg_pats_per_subsig: pats per subsig
			avg_active_pats_per_subsig,//active pats per subsig (per chunk)
			basis_pats_in_trace,       //basis_pats_in_trace (basis points)
			perc_pats_expansion_rate,  //perc_pats_expansion_rate: StepFwdPrf
			sigs,                      //sigs_sed: sigs discharged via SED
			perc_comp_subsigs,         //perc_comp_subsigs: compute-sig share
			basis_unique_states,       //unique DFA states (basis points)
			basis_acc_states);         //accepting DFA states (basis points)
		let init_dfa_cap = DfaCapacity::new(max_word, dfa_sigs,
			dfa_subsigs);

		//IGC: 0 ignore-case patterns, BUT compute_sig_adv merges cs+igc
		//and asserts subsigs_cs==subsigs_igc and inp_sigs==capacity.sigs
		//(compute_sig_adv.rs:368,1160), so IGC must mirror CS on
		//subsigs/sigs. Only perc_pats_expansion_rate_igc is shrunk (igc
		//trace is empty). Mirrors full_clamav's cs/igc symmetry.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, 4, //perc_pats_expansion_rate_igc small
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);

		let scan_files: Vec<String> = vec![
			format!("{}/binexec.dat", set1)]; //single job

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main.dat", set1), //src sig
			scan_files, //list of files to discharge
			"data/paper_data/dna/reports/report_zk.dat", //report
			b_write_cache,
			"dna_data", //cache name
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// Take a few MS DLP regex and discharge a couple of 
	/// Enron 128k emails.
	/// NOTE: capacities below are an initial estimate mirrored from
	/// full_dna (generous); a CapErr-driven tuning pass may be needed
	/// for a minimal circuit. Invoke via test_small_email.
	/// MEASURED (CS-only build_circs_adv_aggr, 2026-06-10): GREEN
	/// end-to-end (Phase1+Phase2+Groth16, verify_batch ok). cs1e 2.14M,
	/// decider 4.73M, peak RAM ~15GB, 17 fold steps. CS-only cut vs the
	/// prior igc-ON build: -24% (igc was ~37% of the gadget here).
	#[allow(dead_code)]
	fn small_email<F:PrimeField>(_b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_email"));
		//Small set: do NOT distribute / enforce the lkup-share table.
		//b_check_lkup=false skips the in-circuit Hab22 lookup-sum
		//check (matches small_dna), so the large fan-out lookup table
		//need not be covered by lk_share*chunks. Verdict soundness is
		//cross-checked out-of-circuit (Phase-3 rustomaton oracle).
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "email_dlp".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = true;
		//range2_bit=20 unlocks the equal 10/10 bit_parts split
		//(max 1024 sigs * 1024 subsigs) used when
		//b_aggressive_sde_for_rep is on. M5 emits 1 base +
		//<=1000 variants per sig, fitting under 1024.
		get_global_config().range2_bit = 20;
		//min_* floors set LOW (single tiny regex sig)
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		//Small set: skip the distributed lkup-share check
		//(b_check_lkup=false below), so perc=1 / lk_share is a small
		//non-binding hint. The fan-out lookup table (lkup_len=1133682)
		//need not be distributed across the 16 chunks here.
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200};

		//SDE-rep fan-out gate ON for the DLP sigs;
		//sde_rep_fanout_cap=100: only 2 digits extracted per leg.
		//variant_combine_cap keeps default 4 to bound the per-
		//variant PCRE->rustomaton-hex rewrite. Dryrun returns
		//from zkp_driver_adv right after build_circs_adv
		//validates capacities -- skips folding/Groth16 so
		//capacity tuning is cheap.
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		//Lower pm-reg word floor so fan-out borrowed bytes
		//(1-2 chars per pin) can qualify as SDE anchors.
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		//Distributed-pin mode: pins spread across legs (priority
		//1st, last, middles R->L), within-leg ascending order.
		get_global_config().clamav_cfg
			.b_sde_rep_tight_first_leg = false;
		//M5 NEEDS/QUICK filter: shrink per-chunk SED universe to the
		//active NEEDS set. Estimator (test_db_bundle) reports max
		//needs/chunk=200; 256 adds margin. capacity.subsigs->256,
		//universe_subsigs stays at `subsigs` (500) for the accumulator.
		get_global_config().aggr_needs_subsigs = 256;
		//Per-chunk failed-subsig set acc_out (local IDX_DATA witness, not
		//carried): acc_size = universe_subsigs*basis_failed_subsigs/10000.
		//Default 0 (acc_size=2): clean discharge -> no subsig reaches a
		//final step -> acc_out empty, so 2 (1 zero-pad) suffices. A CapErr
		//here would signal a real match (data not clean).
		get_global_config().b_dryrun_after_capcheck = false;

		//no cached email DB -> build fresh from main.dat
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_email/config";
		let max_word = 256; //~17 fold steps over 260k nibbles
		//Empirical caps from test_db_bundle ESTIMATE_CONFIG
		//(10 F-only DLP sigs, range_bits=20, max_word_len=256,
		//fanout_cap=100 i.e. <=2 digits/leg, tight-first-leg).
		let sigs = 10; //empirical sigs_sed=5
		let subsigs = 500; //comp_sig::subsigs_cs needs universe=467
		let avg_pats_per_subsig = 4; //empirical avg_pats=2
		let avg_active_pats_per_subsig = 7;
		let perc_comp_subsigs = 20;
		let basis_unique_states = 150; //empirical b_uniq=15, cp_pack=102
		let basis_acc_states = 600; //empirical b_acc=512
		let basis_pats_in_trace = 700; //empirical b_pat=514, joinwide buffer
		//Aggressive reseeds the step queue per chunk (no F+B carry growth),
		//so StepFwdPrf stays tiny: peak usage 1.36% at perc=10000 (probe
		//6901.8). 300 -> ~45% usage, 2x margin (was 10000).
		let perc_pats_expansion_rate = 300; //F+B StepFwdPrf, see 6901.8
		let _dfa_sigs = 0; //no DFA gadget in aggressive mode
		let _dfa_subsigs = 0;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word,                  //max_word_len: packed words per chunk
			read_global_config().range2_bit, //acdfa_state_part_bits
			subsigs,                   //subsigs: SED universe size
			avg_pats_per_subsig,       //avg_pats_per_subsig: pats per subsig
			avg_active_pats_per_subsig,//active pats per subsig (per chunk)
			basis_pats_in_trace,       //basis_pats_in_trace (basis points)
			perc_pats_expansion_rate,  //perc_pats_expansion_rate: StepFwdPrf
			sigs,                      //sigs_sed: sigs discharged via SED
			perc_comp_subsigs,         //perc_comp_subsigs: compute-sig share
			basis_unique_states,       //unique DFA states (basis points)
			basis_acc_states);         //accepting DFA states (basis points)

		//CS-only aggressive ladder (lowest cost first). Both igc caps
		//reproduce the prior hardcoded sentinel (CP basis_unique=4; SED
		//subsigs=1, basis_unique tracks the cs cap). One circuit per entry.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);
		//M10: carry is now AC-DFA-state-only, so heterogeneous rungs
		//fold. 2-rung ladder (lowest cost first): rung 0 shrinks only the
		//subsig universe (compute_sig+discharge), keeping the per-nibble
		//FSM/CP structure; rung 1 = full universe (covers max failed_c).
		let r0_subsigs = 8;
		let r0_cp = CpCapacity{ max_word_len: max_word,
			basis_unique_states,
			subsigs: r0_subsigs, avg_pats_per_subsig };
		let r0_sed = SedCapacity::new(
			max_word, read_global_config().range2_bit,
			r0_subsigs, avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate,
			sigs, perc_comp_subsigs,
			basis_unique_states, basis_acc_states);
		let cs_caps = vec![
			(r0_cp, r0_sed,
				init_cp_cap_igc.clone(), init_sed_cap_igc.clone()),
			(init_cp_cap, init_sed_cap,
				init_cp_cap_igc, init_sed_cap_igc)];

		let scan_files: Vec<String> = vec![
			format!("{}/binexec.dat", set1)]; //single job

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main.dat", set1), //src sig
			scan_files, //list of files to discharge
			"data/debug/small_email/reports/report_zk.dat", //report
			b_write_cache,
			//WARNING: small_email and small_email2 SHARE this
			//"email_data" DB cache, but use different range2_bit
			//(20 vs 25) and sigs (main.dat vs main_full.dat), so a
			//cache from one is INVALID for the other. Both rebuild
			//fresh (b_read_cache=false) and overwrite it each run;
			//never set b_read_cache=true without first rebuilding
			//the cache for the matching runner.
			"email_data", //cache name (SHARED w/ small_email2)
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&cs_caps,
			b_check_lkup,
			DcMode::Off, //hand caps: no auto-tune (env cannot override)
		);
	}

	/// Take the FULL ms-dlp and dischage several average enron emails
	/// end-to-end on merged_000005 (binexec2; discharges clean under
	/// cap-100/distributed). cs1e 3.02M, decider 6.68M, peak RAM ~66GB,
	/// 17 fold steps. ~41% bigger than small_email (full-set caps:
	/// subsigs 700, basis_acc 1200, basis_pat 1400, dfa_crit 25720
	/// states), NOT arm-count -- a 5-arm slice matched small_email.
	#[allow(dead_code)]
	fn small_email2<F:PrimeField>(_b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_email2"));
		//Small set: do NOT distribute / enforce the lkup-share table.
		//b_check_lkup=false skips the in-circuit Hab22 lookup-sum
		//check (matches small_dna), so the large fan-out lookup table
		//need not be covered by lk_share*chunks. Verdict soundness is
		//cross-checked out-of-circuit (Phase-3 rustomaton oracle).
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "email_dlp".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = true;
		//range2_bit=25 gives the aggressive (15,10) bit_parts split:
		//sig_id 15 bits (max 32768 sigs, full MS-DLP set has 3142) and
		//subsig_id 10 bits (max 1024; M5 emits 1 base + <=1000 variants
		//per sig). The old 20 (10/10) capped sigs at 1024 -> overflowed
		//at sig 3139 in hex_acdfa. 25 < full_clamav's 26, so feasible.
		get_global_config().range2_bit = 25;
		//min_* floors set LOW (single tiny regex sig)
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		//Small set: skip the distributed lkup-share check
		//(b_check_lkup=false below), so perc=1 / lk_share is a small
		//non-binding hint. The fan-out lookup table (lkup_len=1133682)
		//need not be distributed across the 16 chunks here.
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200};

		//SDE-rep fan-out gate ON for the DLP sigs;
		//sde_rep_fanout_cap=100: only 2 digits extracted per leg.
		//variant_combine_cap keeps default 4 to bound the per-
		//variant PCRE->rustomaton-hex rewrite. Dryrun returns
		//from zkp_driver_adv right after build_circs_adv
		//validates capacities -- skips folding/Groth16 so
		//capacity tuning is cheap.
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		//Lower pm-reg word floor so fan-out borrowed bytes
		//(1-2 chars per pin) can qualify as SDE anchors.
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		//Distributed-pin mode: pins spread across legs (priority
		//1st, last, middles R->L), within-leg ascending order.
		get_global_config().clamav_cfg
			.b_sde_rep_tight_first_leg = false;
		//M5 NEEDS/QUICK filter: shrink per-chunk SED universe to the
		//active NEEDS set. Full-set estimator (test_db_bundle on
		//main_full.dat) reports max needs/chunk=600; 700 adds margin.
		get_global_config().aggr_needs_subsigs = 700;
		//M2 failed_subsigs accumulator (basis points): acc_size =
		//universe_subsigs * this / 10000. Left at default 0 (acc_size=2):
		//subsigs are discharged early by the QUICK absence cert, so
		//few/none reach a final step -> the accumulator stays empty.
		get_global_config().b_dryrun_after_capcheck = false;

		//Build the DB fresh: the data/cache/email_data write hits a 2GiB
		//per-file truncation (vec_sigs/bundle_subsig .txt capped at
		//2147479552 B), so the cache is not safely readable yet. Flip to
		//true only after the write-truncation is fixed. SHARED w/
		//small_email (see warning at the zkp_driver_adv call below).
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_email/config";
		let max_word = 256; //~17 fold steps over 260k nibbles
		//Empirical caps from test_db_bundle ESTIMATE_CONFIG on the
		//REGENERATED full MS DLP set (6729 arms, ws-boundary keywords +
		//alternation split, range_bits=25, max_word=256, fanout_cap=100,
		//cap-26 leg select), scan=merged_000020 (conservative). The ws
		//boundaries kill the false-positive keyword hits, so only 6 SITs
		//reach SED (universe ~600) vs 2708 on the old stripped set.
		let sigs = 12; //estimator sigs_sed=6
		let subsigs = 700; //estimator SED universe=600
		let avg_pats_per_subsig = 4; //estimator avg_pats=3
		let avg_active_pats_per_subsig = 7;
		let perc_comp_subsigs = 20;
		//cp::basis_unique_states demand=249 on merged_000005 (CapErr;
		//estimator on _000020 gave 96 -> under-predicted); 350 = ~40%
		//margin. Feeds both CpCapacity and SedCapacity.
		let basis_unique_states = 350; //demand 249 (CapErr), est b_uniq=96
		let basis_acc_states = 1200; //estimator b_acc=1143 (passed)
		//merged_000005 joinwide demand=1257 (estimator on _000020 gave
		//1157 -> under-predicted); 1400 adds ~11% margin.
		let basis_pats_in_trace = 1400; //demand 1257 (CapErr), est b_pat=1157
		//Aggressive reseeds the step queue per chunk (no F+B carry growth),
		//so StepFwdPrf stays tiny: peak usage 1.36% at perc=10000 (probe
		//6901.8). 300 -> ~45% usage, 2x margin (was 10000).
		let perc_pats_expansion_rate = 300; //F+B StepFwdPrf, see 6901.8
		let _dfa_sigs = 0; //no DFA gadget in aggressive mode
		let _dfa_subsigs = 0;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word,                  //max_word_len: packed words per chunk
			read_global_config().range2_bit, //acdfa_state_part_bits
			subsigs,                   //subsigs: SED universe size
			avg_pats_per_subsig,       //avg_pats_per_subsig: pats per subsig
			avg_active_pats_per_subsig,//active pats per subsig (per chunk)
			basis_pats_in_trace,       //basis_pats_in_trace (basis points)
			perc_pats_expansion_rate,  //perc_pats_expansion_rate: StepFwdPrf
			sigs,                      //sigs_sed: sigs discharged via SED
			perc_comp_subsigs,         //perc_comp_subsigs: compute-sig share
			basis_unique_states,       //unique DFA states (basis points)
			basis_acc_states);         //accepting DFA states (basis points)

		//CS-only aggressive ladder (lowest cost first). Both igc caps
		//reproduce the prior hardcoded sentinel (CP basis_unique=4; SED
		//subsigs=1, basis_unique tracks the cs cap). One circuit per entry.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);
		let cs_caps = vec![(init_cp_cap, init_sed_cap,
			init_cp_cap_igc, init_sed_cap_igc)];

		//binexec2.dat scans merged_000005 (in clean_email_list -> clean
		//discharge vs all 60 SITs; merged_000020 is flagged).
		let scan_files: Vec<String> = vec![
			format!("{}/binexec2.dat", set1)]; //single job

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main_full.dat", set1), //src sig
			scan_files, //list of files to discharge
			"data/debug/small_email/reports/report_zk.dat", //report
			b_write_cache,
			//WARNING: small_email2 and small_email SHARE this
			//"email_data" DB cache, but use different range2_bit
			//(25 vs 20) and sigs (main_full.dat vs main.dat), so a
			//cache from one is INVALID for the other. Both rebuild
			//fresh (b_read_cache=false) and overwrite it each run;
			//running small_email2 clobbers the small_email cache.
			"email_data", //cache name (SHARED w/ small_email)
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&cs_caps,
			b_check_lkup,
			DcMode::Off, //hand caps: no auto-tune (env cannot override)
		);
	}

	/// Take full ms_dlp regex and discharge several HARD instances
	#[allow(dead_code)]
	fn small_email3<F:PrimeField>(_b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_email3"));
		//ESTIMATOR pass (commented; uncomment to re-estimate caps / rebuild
		//the boosted email_data cache). Sweeps binexec3.dat=merged_004945 vs
		//the full MS DLP set, prints ESTIMATE_CONFIG, and WRITES the boosted
		//DB to "email_data" (b_write_cache=true). The ZK path below READS it.
		/* ESTIMATOR/SWEEP pass disabled -- ZK path active below.
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.sde_rep_fanout_boost = 1; //BONUS off: 100 for all
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().clamav_cfg.b_sde_rep_tight_first_leg = false;
		super::run_db_bundle::<F>(
			"data/debug/small_email/config","data/debug/small_email/reports",
			false, false, true, 25, 256, &[20usize,50,100],
			"main_full.dat", "binexec4.dat", "email_data");
		return;
		*/

		//ZK discharge path: prove merged_004945 (boosted NINO fan-out)
		//discharges vs the full MS DLP set. Reads the boosted email_data
		//cache written by the estimator pass above.
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "email_dlp".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_light_test = true;
		get_global_config().range2_bit = 25;
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = if !b_check_lkup {1}
			else {200};
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		//boost=10 (cap 1000) required: boost 5 and 7 both fail to discharge
		//merged_004945 (uk-NINO kw03.p00), so universe ~3000 is the minimum.
		get_global_config().clamav_cfg.sde_rep_fanout_boost = 10;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().clamav_cfg
			.b_sde_rep_tight_first_leg = false;
		//binexec3 (merged_004945) estimator reports needs=2880 (boosted NINO
		//fan-out grows the forward step queue); 3000 adds margin.
		get_global_config().aggr_needs_subsigs = 3000;
		get_global_config().b_dryrun_after_capcheck = false;

		//Read the shared "email_data" DB cache (built by test_db_bundle
		//on main_full.dat, range2_bit=25 -- the identical DB) to skip the
		//~10min rebuild. The 2GiB write-truncation is fixed (write_all),
		//so the cache is complete. Flip to false if main_full.dat or the
		//DB-build code changes. SHARED w/ small_email, small_email2.
		//Rebuild fresh (false): the boosted cache is easily clobbered by the
		//other two runners; set true only right after a matching rebuild.
		get_global_config().b_read_cache = false;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/small_email/config";
		let max_word = 256;
		//Caps from the binexec3 estimator (scan=merged_004945, boosted) +
		//margin for the estimator's known under-prediction (esp. CP
		//basis_unique: merged_000005 went 96->249, ~2.6x). Bump on CapErr.
		let sigs = 8; //estimator sigs_sed=4
		//dryrun demand dis_adv::universe_subsigs=3000 (boosted NINO emits
		//~2880 variants globally; estimator subsigs col=800 under-predicts
		//the accumulator universe). 3100 adds margin.
		let subsigs = 3100; //dryrun universe demand=3000
		let avg_pats_per_subsig = 4; //estimator avg_pats=3
		//Not estimated (estimator uses defaults). Fold-time advice demand
		//dis_adv::avg_active_pats_per_subsig=12 (boosted NINO variants are
		//pattern-dense); 14 adds margin.
		let avg_active_pats_per_subsig = 14; //fold demand=12
		let perc_comp_subsigs = 20;
		let basis_unique_states = 500; //est b_uniq=113; CP demand higher
		let basis_acc_states = 1000; //estimator b_acc=719
		let basis_pats_in_trace = 1100; //estimator b_pat=800
		//Fold-time StepFwdPrf demand climbs per chunk (9560 then 10380):
		//the boosted NINO fan-out (3000-subsig universe) makes the per-
		//chunk forward-step expansion ~30x denser than small_email (300).
		//14000 over-provisions to clear all chunks; perc is NOT the RAM
		//driver (300->10000 moved RAM only 1.3x), so this is cheap.
		//StepFwdPrf forward buffer. This is the dominant cost driver of the
		//DischargeAdv gadget (cs1e scales ~linearly with it). Measured demand
		//~10380 (merged_004945); 14000 was 26% over-provisioned. 10500 fits
		//(99% used) but is the floor; 11000 gives ~5% margin. 14000->11000
		//cuts cs1e ~40.2M->~32M (-20%), DischargeAdv 11.05M->~8.6M.
		let perc_pats_expansion_rate = 11000; //demand ~10380; margin over floor
		let _dfa_sigs = 0; //no DFA gadget in aggressive mode
		let _dfa_subsigs = 0;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word,                  //max_word_len: packed words per chunk
			read_global_config().range2_bit, //acdfa_state_part_bits
			subsigs,                   //subsigs: SED universe size
			avg_pats_per_subsig,       //avg_pats_per_subsig: pats per subsig
			avg_active_pats_per_subsig,//active pats per subsig (per chunk)
			basis_pats_in_trace,       //basis_pats_in_trace (basis points)
			perc_pats_expansion_rate,  //perc_pats_expansion_rate: StepFwdPrf
			sigs,                      //sigs_sed: sigs discharged via SED
			perc_comp_subsigs,         //perc_comp_subsigs: compute-sig share
			basis_unique_states,       //unique DFA states (basis points)
			basis_acc_states);         //accepting DFA states (basis points)

		//CS-only aggressive ladder (lowest cost first). Both igc caps
		//reproduce the prior hardcoded sentinel (CP basis_unique=4; SED
		//subsigs=1, basis_unique tracks the cs cap). One circuit per entry.
		let init_cp_cap_igc = CpCapacity{
			max_word_len: init_cp_cap.max_word_len,
			basis_unique_states: 4, subsigs: 1, avg_pats_per_subsig: 1};
		let init_sed_cap_igc = SedCapacity::new(
			init_sed_cap.max_word_len, init_sed_cap.acdfa_state_part_bits,
			1, 1, 1, 4, 64, 1, 1,
			init_sed_cap.basis_unique_states, 2);
		let cs_caps = vec![(init_cp_cap, init_sed_cap,
			init_cp_cap_igc, init_sed_cap_igc)];

		//binexec3.dat scans merged_004945 (the dischargeable one of the
		//challenge pair; merged_005547 is blocked by sql-conn-string).
		let scan_files: Vec<String> = vec![
			format!("{}/binexec3.dat", set1)]; //single job

		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0,
			&format!("{}/main_full.dat", set1), //src sig
			scan_files, //list of files to discharge
			"data/debug/small_email/reports/report_zk.dat", //report
			b_write_cache,
			//WARNING: small_email3, small_email2 and small_email SHARE
			//this "email_data" DB cache. _3/_2 use range2_bit=25 +
			//main_full.dat; small_email uses 20 + main.dat (INVALID to
			//cross-read). Here b_read_cache=true reads the cache built
			//by test_db_bundle (binexec3) / small_email2.
			"email_data", //cache (SHARED w/ small_email, small_email2)
			&format!("{}/main_dfa.dat", set1), //sigs needing dfa
			&format!("{}/needs_ised.dat", set1), //ised (empty)
			&format!("{}/needs_ised_igc.dat", set1), //ised_igc (empty)
			max_word, //chunk len
			&cs_caps,
			b_check_lkup,
			DcMode::Off, //hand caps: no auto-tune (env cannot override)
		);
	}

	/// 2026-05-21: full_clam_short_file — mirrors full_clamav with
	/// b_light_test=false and b_setup=false hardcoded, and scan
	/// targets swapped to 8x ~1MB sample_1M_*.dat files. Goal:
	/// measure SNARK time (Phase 1 main + Phase 2 cp) in isolation
	/// from folding cost. Snark keys are READ from cache; setup is
	/// skipped. All other config knobs (capacities, range2_bit,
	/// n_par_snark*, min_*) are byte-identical to full_clamav —
	/// keep them in sync if you tune full_clamav.
	#[allow(dead_code)]
	fn full_clam_short_file<F:PrimeField>(){
		utils::os::print_computer_config(Some("full_clam_short_file"));
		//extra setting
		let b_check_lkup = false;
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = false;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states= 1054;
		get_global_config().min_basis_acc_states =  268;
		get_global_config().min_basis_pats_in_trace=  295;
		get_global_config().min_avg_pats_per_subsig= 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs =  3;
		get_global_config().n_par_snark = 1;
		get_global_config().n_par_snark_cp = 1;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1 = "data/debug/full_clamav/config/";
		let max_word= 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs= 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap= DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc= CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc= SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		let num_jobs = 8;
		let scan_files: Vec<String> = (0..num_jobs).map(|i|
			format!("{}/sample_1M_{}.dat", set1, i)).collect();
		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
			0,
			&format!("{}/main.dat",set1),
			scan_files,
			"data/debug/full_clamav/reports/report2.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat",set1),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// 2026-06-27: full_debug — job-3 fault isolation. Now a FAITHFUL
	/// mirror of full_clamav() (full SNARK, one proof, b_read_snark_cache
	/// from data/cache/full_data + full_data DB cache), but scans a
	/// SINGLE job: ZKR_DBG_LIST if set (an explicit slice list written by
	/// bisect_job3.py, absolute path), else the full job-3 list
	/// binexec_p3.dat. n_jobs=1 => runtime job_id=0, so the batch-verify
	/// ERROR prints as "Job 0 BATCH PROOF VERIFICATION FAILED". All caps
	/// below are byte-identical to full_clamav — keep in sync if tuned.
	/// Snark keys must already exist (data/cache/full_data/g16_*.key*),
	/// else driver.rs auto-flips to a multi-hour key rebuild.
	fn full_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_debug"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = false; // full snark (one proof)
		get_global_config().b_one_proof = false;  // every job proves
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().n_par_snark = 1;
		get_global_config().n_par_snark_cp = 1;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;
		get_global_config().log_level = utils::logger::LOG3;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1_cfg  = "data/debug/full_clamav/config/";
		let max_word = 512 * 8;
		let sigs = 400;
		let subsigs = 580;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		let vec_decrease_level = vec![2];
		let num_circs = 2;
		let basis_unique_states = 1300;
		let basis_acc_states = 750;
		let basis_pats_in_trace = 820;
		let basis_acc_states_igc = basis_acc_states;
		let basis_pats_in_trace_igc = basis_pats_in_trace;
		let dfa_sigs = 8;
		let dfa_subsigs = 8;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 2;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace,
			perc_pats_expansion_rate,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states,
		);
		let init_dfa_cap = DfaCapacity::new(
			max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word,
			basis_unique_states,
			subsigs: subsigs,
			avg_pats_per_subsig,
		};
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig,
			avg_active_pats_per_subsig,
			basis_pats_in_trace_igc,
			perc_pats_expansion_rate_igc,
			sigs,
			perc_comp_subsigs,
			basis_unique_states,
			basis_acc_states_igc,
		);

		// Job-3 isolation: scan ZKR_DBG_LIST if set (bisect_job3.py writes
		// an explicit slice list there, absolute path), else the full
		// job-3 list. Single list file => n_jobs = 1, runtime job_id = 0.
		let scan_files: Vec<String> = match std::env::var("ZKR_DBG_LIST") {
			Ok(p) if !p.trim().is_empty() => {
				println!("ZKR_DBG_LIST override: scanning {}", p);
				vec![p]
			}
			_ => vec![format!("{}/binexec_p3.dat", set1_cfg)],
		};

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,
			CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1_cfg),
			scan_files,
			// distinct filename in full_clamav's existing reports dir
			// (avoids clobbering the real run's report2.dat)
			"data/debug/full_clamav/reports/report_dbg.dat",
			b_write_cache,
			"full_data",
			&format!("{}/main_dfa.dat", set1_cfg),
			&format!("{}/needs_ised.dat", set1_cfg),
			&format!("{}/needs_ised_igc.dat", set1_cfg),
			max_word,
			&init_cp_cap,
			&init_sed_cap,
			&init_dfa_cap,
			&init_cp_cap_igc,
			&init_sed_cap_igc,
			&vec_decrease_level,
			num_circs,
			b_check_lkup, DcMode::Off
		);
	}

	/// 2026-05-16: dedicated test entry for full_debug_watch.py.
	/// Invoked via `cargo test ... test_full_debug_main`.
	#[test]
	pub fn test_full_debug_main(){
		full_debug::<Fr>(true); // b_check_lkup=true, matching full_clam()
		utils::logger::flush_logger();
		let sentinel = format!(
			"{}/data/cache/run_complete.sentinel",
			utils::os::proj_root());
		let _ = std::fs::write(&sentinel, "ok\n");
	}

	/// 2026-05-18 (Plan D): test entry for the compute_sig_adv:1269
	/// repro via cached full_clamav DFA + single-file scan. Passes
	/// b_check_lkup=false (matching test_full_debug_main) so the
	/// pre-check_logup lk_share*chunks>=lkup_len guard doesn't fire
	/// — the panic we're chasing is host-side in gen_nd_advice,
	/// well before check_logup gets to run.
	#[test]
	pub fn test_small_debug_main(){
		let b_check_lkup = false;
		small_debug::<Fr>(b_check_lkup);
	}


	#[test]
	pub fn test_zkreg_main(){//test zkreg.main
		let b_check_lkup = true;
		let _b_light_test = false;
		let _b_setup = false;
		small_data::<Fr>(b_check_lkup); //small data
		//small_email::<Fr>(b_check_lkup); //M6: aggressive multi-chunk run
		//small_dna::<Fr>(); //small data dna set
		//full_dna::<Fr>(b_check_lkup);
		//small_debug::<Fr>(b_check_lkup); //small_data + max_word=2
		//small_data2::<Fr>(b_check_lkup);  //10k data
		//small_data3::<Fr>(b_check_lkup); //multi circ of 10k data -> fails
		//small_data_par::<Fr>(b_check_lkup); //small data (parallel jobs)
		//small_data_debug::<Fr>(b_check_lkup);  //for debug
		//small_data4::<Fr>(b_check_lkup); //multi circ of 1M, 2M, 4M data
		//full_data1::<Fr>(b_check_lkup);
		//full_data2::<Fr>(b_check_lkup); //full data high acc state
		//full_data3::<Fr>(b_check_lkup); //full data large file
		//full_data4::<Fr>(b_check_lkup); //full data large file
		//full_par::<Fr>(b_check_lkup); //full data large file
		//full_par2::<Fr>(b_check_lkup); //full_data4 files, 8 parallel jobs
		//full_clam_short_file::<Fr>();
		//full_clamav::<Fr>(b_check_lkup, _b_light_test, _b_setup); //full data large file

		// Drain any in-flight log lines on the stdout drainer before
		// declaring success, so the sentinel is never written ahead of
		// the final lines that prove "ok".
		utils::logger::flush_logger();

		// Completion sentinel for run_checkpoints.py. Not reached if
		// full_par panics -- panic aborts the test, no sentinel written.
		let sentinel = format!(
			"{}/data/cache/run_complete.sentinel",
			utils::os::proj_root());
		let _ = std::fs::write(&sentinel, "ok\n");
	}

	/// Discharge-approach stats over the paper_data debug bundle.
	/// TEMP (gen dlp list -- remove after): discharge the clean Enron emails
	/// against the DLP-international bora regex and write pass/fail lists.
	/// `cargo test -p zkregplus -- test_gen_dlp_list --show-output --nocapture`
	#[test]
	pub fn test_gen_dlp_list(){
		std::env::set_var("ZKR_DLP_LIST_DIR",
			"data/paper_data/dlp/cfg");
		// aggressive SDE-for-rep fan-out: expand [0-9]{n} reps into concrete
		// variants (less-conservative discharge).
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		super::run_db_bundle::<Fr>(
			"data/paper_data/dlp/cfg", //config dir
			"data/paper_data/dlp/cfg", //report dir
			false, false, true, //b_cache, b_write_cache, b_quick
			25, 512, &[100usize], //range_bits, max_word_len, percentiles
			"regex_pat/main_data_dlp_internationl.dat", //src sig (NEW)
			"jobs/binexec_dlp_intl.dat", //scan manifest (NEW)
			"dlp_intl_data_aggr"); //cache name (NEW)
	}

	/// Discharge the FULL clean Enron international list (~515K files)
	/// against the DLP-international bora set; write full/pass/fail_
	/// clean_enron_list to the config dir. Lean path + heartbeat probes
	/// (see stats_helper::collect_discharge_pass_fail). Run from compile.sh:
	/// `cargo test -p zkregplus --release -- \
	///   zkp_driver::tests_zkp_driver::collect_enron_list --exact --nocapture`
	#[test]
	pub fn collect_enron_list(){
		get_global_config().range2_bit = 25;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let dir = "data/paper_data/dlp/cfg";
		crate::stats_helper::collect_discharge_pass_fail::<Fr>(
			&format!("{}/regex_pat/main_data_dlp_internationl.dat", dir),
			&format!("{}/regex_pat/main_dfa.dat", dir),
			&format!("{}/regex_pat/needs_ised.dat", dir),
			&format!("{}/regex_pat/needs_ised_igc.dat", dir),
			"data/src_sig/ms_dlp/docs/\
clean_email_list_email_regex_zombie_international.txt", //515K list
			"data/samples/email",  //base prefix for list entries
			&format!("{}/corpus", dir), //out dir for full/pass/fail lists
			true, true,            //b_read_cache, b_write_cache
			"dlp_intl_data_aggr",  //DB cache name
			64);                   //seg_word_len: 64w*31B ~= 2KB
	}                              //(median email fills ~78%)

	/// Pure-logic check of select_candidates_from_peaks: the per-proxy top-K
	/// must include every cap's argmax file, and n<=k returns all files.
	#[test]
	fn test_select_binding_candidates(){
		use data_processor::discharge_proof::ChunkPeaks;
		let mk = |needs, fwd, act, pats, uniq, acc, cp| {
			let mut c = ChunkPeaks::default();
			c.max_needs_subsigs = needs;
			c.max_fwd_entries_per_chunk = fwd;
			c.max_active_steps_per_chunk = act;
			c.max_pats_in_trace = pats;
			c.max_unique_states = uniq;
			c.max_acc_states = acc;
			c.max_cp_unique_states = cp;
			c
		};
		// file 5 = SED argmax (needs/fwd/act/pats/acc); file 0 = structural
		// (unique) argmax; file 4 = cp argmax.
		let peaks = vec![
			mk(1, 1, 1, 1, 100, 1, 1),
			mk(2, 2, 2, 2, 2, 2, 2),
			mk(3, 3, 3, 3, 3, 3, 3),
			mk(4, 4, 4, 4, 4, 4, 4),
			mk(5, 5, 5, 5, 5, 5, 99),
			mk(99, 99, 99, 99, 6, 6, 6),
		];
		// k=1: candidate set = union of per-proxy argmax = {0,4,5}.
		assert_eq!(super::select_candidates_from_peaks(&peaks, 1),
			vec![0usize,4,5]);
		// n<=k: all files, sorted.
		assert_eq!(super::select_candidates_from_peaks(&peaks, 6),
			vec![0usize,1,2,3,4,5]);
		assert_eq!(super::select_candidates_from_peaks(&peaks, 100),
			vec![0usize,1,2,3,4,5]);
		// k=2: needs top-2 = {5,4} both present.
		let c2 = super::select_candidates_from_peaks(&peaks, 2);
		assert!(c2.contains(&5) && c2.contains(&4),
			"k=2 needs top-2 missing: {:?}", c2);
	}

	/// One-off: aggressive NEEDS scan over the scan_file list. Dump
	/// "maxNEEDS<TAB>foldable<TAB>fpath" sorted desc so the sample's
	/// forced expensive file (and foldable peers) can be picked. Cached.
	#[test]
	pub fn dlp_dump_file_needs(){
		use rayon::prelude::*;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_read_cache = true;
		get_global_config().b_estimate_caps = false;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		let files = utils::os::read_lines(
			&format!("{}/{}", proot, rc.scan_file));
		let mut rank: Vec<(usize, bool, String)> = files.par_iter()
			.filter_map(|f| crate::needs_dist::discharge_one::<Fr>(
				f, &proot, &db, &cfg, mw).map(|fdr| {
				let mx = fdr.chunk_peaks.needs_per_chunk.iter()
					.copied().max().unwrap_or(0);
				(mx, !fdr.is_fail(), f.clone())
			})).collect();
		rank.sort_by(|a, b| b.0.cmp(&a.0));
		let body: String = rank.iter()
			.map(|(n, ok, f)| format!("{}\t{}\t{}\n", n, *ok as u8, f))
			.collect();
		let out = format!("{}/{}", proot, rc.report_out);
		std::fs::write(&out, body).expect("write rank");
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"[dump_file_needs] {} files ranked -> {}", rank.len(), out));
	}

	/// Sampled full_dlp: same DB as full_dlp (symlinked regex), discharge
	/// a 500-file sample, print the NEEDS distribution, tune a k_max-rung
	/// cap ladder, then fold-only for per-step stats + cs1e.
	#[test]
	pub fn full_dlp_sample(){
		use crate::determine_config::caps_from_params_aggr;
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		if let Ok(lp) = std::env::var("ZKR_LOAD_LADDER") {
			let lp_abs = format!("{}/{}", proot, lp);
			assert!(std::path::Path::new(&lp_abs).exists(),
				"ZKR_LOAD_LADDER points to a missing file: {} \
				 (run full_dlp to regenerate the ladder, or fix the path)",
				lp_abs);
		}
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		//aggressive CS-only, folding-only, estimate-on for the tuning.
		//ZKR_LOG6: per-gadget constraint breakdown (gen_step_cs "after msg3
		//of module") to see which gadget bloats each rung at preprocess.
		get_global_config().log_level = if std::env::var("ZKR_LOG6").is_ok() {
			utils::logger::LOG6 } else { utils::logger::LOG3 };
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = false;
		get_global_config().b_folding_only = false;
		//cap the entire snark proof-generation region at 1 concurrent
		//decider (0 = auto: sum of n_par_snark + n_par_snark_cp).
		get_global_config().n_par_snark_total = 1;
		get_global_config().b_read_cache = true;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_estimate_caps = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		//discharge the sample -> vdata + words + infos (one pass).
		let files = utils::os::read_lines(
			&format!("{}/{}/{}", proot, cd, rc.scan_file));
		let (mut vdata, mut words, mut infos) = (vec![], vec![], vec![]);
		for fpath in &files{
			let nibbles = utils::os::read_nibbles(
				&format!("{}/{}", proot, fpath));
			let f_nib: Vec<Fr> = nibbles.iter().map(|x| Fr::from(*x as u32))
				.collect();
			words.push(utils::data::pack_nibbles(&f_nib));
			let (fdr, rec) =
				data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
				fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, mw, mw);
			vdata.push(fdr);
			infos.push(rec);
		}
		//PROBE FAILSEG (ZKR_PROBE_FAILSEG): per-segment failed_c (= the CP
		//"needs discharge" set that SED must cover that chunk) for every
		//file, with WHICH SUBSIG of WHICH SIG. The b_correct desync chunk
		//(e.g. seg 33 of kean-s/166: sigs 890/891) shows here -- compare the
		//bad file's segs against a passing file's. Runs in the cheap
		//discharge phase, before key setup. DEBUG -- remove with the harness.
		if std::env::var("ZKR_PROBE_FAILSEG").is_ok() {
			for (fi, (fpath, wi)) in files.iter().zip(infos.iter())
				.enumerate() {
				let nseg = wi.failed_c_all_segs.len();
				let tot: usize = wi.failed_c_all_segs.iter()
					.map(|v| v.len()).sum();
				utils::logger::emit_stdout(format!(
					"PROBE FAILSEG file[{}]={} nibble_len={} n_segs={} \
					 total_failed={}", fi, fpath, wi.file_nibble_len, nseg,
					tot));
				for s in 0..nseg {
					let ids = &wi.failed_c_all_segs[s];
					if ids.is_empty() { continue; }
					let info = wi.failed_c_info_all_segs.get(s);
					let detail: Vec<String> = ids.iter().enumerate()
						.map(|(k, id)| {
							match info.and_then(|v| v.get(k)) {
								Some(di) => format!(
									"sid={} {} subsigs={:?} igc={:?} \
									 mincost={} ok={}", id, di.sig_name,
									di.subsig_ids, di.subsig_igc,
									di.min_cost, di.b_success),
								None => format!("sid={} <no-info>", id),
							}
						}).collect();
					utils::logger::emit_stdout(format!(
						"PROBE FAILSEG   file[{}] seg={} n_failed={} :: {}",
						fi, s, ids.len(), detail.join(" || ")));
				}
			}
		}
		//(1) NEEDS distribution over the sample (stdout + sample report).
		let rows: Vec<Vec<usize>> = vdata.iter()
			.map(|r| r.chunk_peaks.needs_per_chunk.clone()).collect();
		crate::needs_dist::print_needs_dist_rows(&rows, &files,
			"data/debug/full_dlp_sample/config/needs_dist.txt");
		//(2) capacity ladder. ZKR_LOAD_LADDER=<repo-rel JSON>: load
		//full_dlp's saved FULL-CORPUS ladder so a handful of files route
		//through the REAL full-run caps and the b_correct overflow
		//resurfaces; unset => rebuild from the sample (original behavior).
		//DEBUG repro knob -- REMOVE once the crash file is identified.
		let db_arc = std::sync::Arc::new(db);
		let ladder: Vec<crate::determine_config::CapParams> =
			if let Ok(lp) = std::env::var("ZKR_LOAD_LADDER") {
				let lp_abs = format!("{}/{}", proot, lp);
				utils::logger::log(0, utils::logger::LOG1, &format!(
					"full_dlp_sample: LOAD full-corpus ladder {}", lp_abs));
				crate::determine_config::load_ladder(&lp_abs)
			} else {
				let est = estimate_config_aggr::<Fr>(&vdata, &*db_arc,
					&[100], &mut vlog);
				let seed = estimated_to_capparams_aggr(&est[0], mw,
					rc.range2_bit, 3);
				let total_word_n: usize =
					words.iter().map(|w| w.len()).sum();
				let lkup_len = db_arc.lkup.get_size();
				let n_threads = std::env::var("ZKR_DC_THREADS").ok()
					.and_then(|s| s.parse().ok()).unwrap_or(4);
				let (lad, hist) = super::determine_config_aggr::<Fr,C1,CS1>(
					db_arc.clone(), &words, &infos, &vdata, seed, mw,
					lkup_len, total_word_n, rc.k_max, rc.n_buckets, 60,
					n_threads, 8, rc.peel_pct)
					.expect("determine_config_aggr");
				crate::determine_config::save_ladder(&lad,
					&format!("{}/{}", proot, rc.config_out))
					.expect("save ladder");
				utils::logger::log(0, utils::logger::LOG1, &format!(
					"full_dlp_sample ladder: {} rungs, hist={:?}",
					lad.len(), hist));
				lad
			};
		//ZKR_FSM_DIST: determine-only diagnostic, skip the fold.
		if std::env::var("ZKR_FSM_DIST").is_ok() { return; }
		//fold-only: load own DB from cache (avoid 2x RAM); stats + cs1e.
		drop(db_arc);
		get_global_config().b_estimate_caps = false;
		get_global_config().aggr_needs_subsigs =
			ladder.first().map(|c| c.aggr_needs_subsigs).unwrap_or(0);
		let cs_caps: Vec<_> = ladder.iter().map(caps_from_params_aggr)
			.collect();
		let scan = vec![format!("{}/{}", cd, rc.scan_file)];
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), scan, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), mw, &cs_caps,
			//cs_caps IS the tuned ladder (determine_config_aggr above), so
			//the driver must NOT tune again.
			false, DcMode::Off);
	}

	/// Read a newline path list; transparently extracts a .tgz/.tar.gz
	/// via `tar -xzO` (no temp file left behind). list_path is repo-rel.
	fn read_path_list(list_path: &str) -> Vec<String> {
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

	/// Deterministic size-balanced split of a path list into num_jobs
	/// lists. Sort by (-size, path) then greedy-LPT into the smallest
	/// bin, so the same (list, num_jobs) yields identical bins each run.
	fn split_jobs_balanced(list_path: &str, num_jobs: usize)
		-> Vec<Vec<String>> {
		split_paths_balanced(read_path_list(list_path), num_jobs)
	}

	/// In-memory variant of split_jobs_balanced over an already-read path
	/// list (e.g. a strided pct sample) -- same (-size, path) sort + greedy
	/// LPT, so identical bins for identical input.
	fn split_paths_balanced(paths: Vec<String>, num_jobs: usize)
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

	/// Discharge-cache dir, keyed only by params that change discharge
	/// output (NOT num_jobs); lives beside the DB cache under data/cache.
	fn discharge_cache_dir(cache_dir: &str, mw: usize, fanout: usize,
		range2_bit: usize, min_pm: usize) -> String {
		format!("{}/data/cache/{}/discharge/mw{}_fo{}_rb{}_pm{}_agg1",
			utils::os::proj_root(), cache_dir, mw, fanout, range2_bit,
			min_pm)
	}

	/// Load (vdata, infos) from the cache dir, or None if absent/bad.
	fn load_discharge_cache(dir: &str)
		-> Option<(Vec<data_processor::discharge_proof::FailDischargeRecord>,
			Vec<WordInfo>)> {
		let vf = std::fs::File::open(format!("{}/vdata.json", dir)).ok()?;
		let inf = std::fs::File::open(format!("{}/infos.json", dir)).ok()?;
		let vdata = serde_json::from_reader(
			std::io::BufReader::new(vf)).ok()?;
		let infos = serde_json::from_reader(
			std::io::BufReader::new(inf)).ok()?;
		Some((vdata, infos))
	}

	/// Persist (vdata, infos) to the cache dir (best-effort).
	fn save_discharge_cache(dir: &str,
		vdata: &Vec<data_processor::discharge_proof::FailDischargeRecord>,
		infos: &Vec<WordInfo>) {
		let _ = std::fs::create_dir_all(dir);
		if let Ok(f) = std::fs::File::create(format!("{}/vdata.json", dir)) {
			let _ = serde_json::to_writer(std::io::BufWriter::new(f), vdata);
		}
		if let Ok(f) = std::fs::File::create(format!("{}/infos.json", dir)) {
			let _ = serde_json::to_writer(std::io::BufWriter::new(f), infos);
		}
	}

	/// Full DLP run over rc.num_jobs balanced jobs: deterministic split,
	/// cached discharge + ladder for sizing, then the multi-job fold for
	/// cs1e / per-step cost. rc.reset recomputes split, discharge, ladder.
	#[test]
	pub fn full_dlp(){
		use crate::determine_config::caps_from_params_aggr;
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		use rayon::prelude::*;
		utils::os::print_computer_config(Some("full_dlp"));
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		let reset = rc.reset;
		let num_jobs = rc.num_jobs.max(1);
		let l = utils::logger::LOG1;
		let mut gt = utils::timer::Timer::new();
		// NUMA (ZKR_NUMA=perjob): interleave the shared DB/ACDFA across nodes so
		// the per-job worker threads (pinned in driver.rs) read it with balanced
		// bandwidth instead of hammering one remote node. No-op unless multi-node
		// + flag set. See folding_schemes::folding::foldpot::numa.
		folding_schemes::folding::foldpot::numa::set_interleave_all();
		//aggressive CS-only, estimate-on (mirror sample). Full-snark run:
		//b_light_test=false + b_folding_only=false so a SNARK is emitted,
		//b_one_proof=true so only Job 0 proves (ONE proof for all jobs).
		get_global_config().log_level = utils::logger::LOG3;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = false; // full snark (was true)
		get_global_config().b_folding_only = false; // emit snark (was true)
		get_global_config().b_one_proof = true;     // ONE proof only
		// full_dlp two-half NUMA scheme (env-driven; unset => unchanged full
		// snark above). fold-only => folding only + light decider; one-proof
		// and snark-wait mirror the clam two-half driver.
		if let Ok(v) = std::env::var("ZKR_DLP_FOLD_ONLY") {
			let fo = v == "1";
			get_global_config().b_folding_only = fo;
			get_global_config().b_light_test = fo;
		}
		if let Ok(v) = std::env::var("ZKR_DLP_ONE_PROOF") {
			get_global_config().b_one_proof = v == "1"; }
		if let Ok(p) = std::env::var("ZKR_SNARK_WAIT_FLAG") {
			get_global_config().snark_wait_flag = Some(p); }
		get_global_config().b_read_cache = true;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_estimate_caps = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().log_level = utils::logger::LOG3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];

		// step 1: load DB.
		utils::logger::log(0, l, &"PROGRESS step 1/6: load DB".to_string());
		let db = std::sync::Arc::new(
			data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db"));
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 1 time".to_string(), &mut gt);

		// two-half NUMA scheme: ZKR_DLP_PCT takes a strided every-k-th
		// sample of the master list (k=round(100/pct)); the list is
		// alphabetical by owner, so striding (not a prefix) keeps every
		// owner/difficulty. pct=100 => full list, byte-identical. The
		// sample feeds split/discharge/ladder/fold; pct<100 uses pct-tagged
		// job + cache dirs so it never clobbers the 100% artifacts.
		let pct = std::env::var("ZKR_DLP_PCT").ok()
			.and_then(|s| s.parse::<usize>().ok()).unwrap_or(100)
			.clamp(1, 100);
		let k = ((100 + pct / 2) / pct).max(1);
		let all_files_full =
			read_path_list(&format!("{}/{}", cd, rc.full_list));
		let n_full = all_files_full.len();
		let all_files: Vec<String> = if k <= 1 { all_files_full }
			else { all_files_full.iter().step_by(k).cloned().collect() };
		let tag = if pct >= 100 { String::new() }
			else { format!("_pct{}", pct) };
		utils::logger::log(0, l, &format!(
			"  pct={} stride k={} -> {} of {} files", pct, k,
			all_files.len(), n_full));

		// step 2: deterministic size-balanced split -> job_<i>.dat (reuse).
		utils::logger::log(0, l,
			&format!("PROGRESS step 2/6: split {} jobs", num_jobs));
		let jobs_dir =
			format!("{}/{}/jobs/jobs{}{}", proot, cd, num_jobs, tag);
		let job_rel: Vec<String> = (0..num_jobs).map(|i|
			format!("{}/jobs/jobs{}{}/job_{}.dat", cd, num_jobs, tag, i))
			.collect();
		let have_all = job_rel.iter().all(|p|
			std::path::Path::new(&format!("{}/{}", proot, p)).exists());
		if reset || !have_all {
			let bins = split_paths_balanced(all_files.clone(), num_jobs);
			let _ = std::fs::create_dir_all(&jobs_dir);
			for (i, b) in bins.iter().enumerate() {
				std::fs::write(format!("{}/job_{}.dat", jobs_dir, i),
					b.join("\n")).expect("write job file");
			}
		}
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 2 time".to_string(), &mut gt);

		// step 3: discharge the sampled list (cache vdata+infos; lazy).
		utils::logger::log(0, l,
			&"PROGRESS step 3/6: discharge full list".to_string());
		let dcache = format!("{}{}", discharge_cache_dir(&rc.cache_dir,
			mw, rc.fanout_cap, rc.range2_bit, 3), tag);
		let cached = if reset { None } else { load_discharge_cache(&dcache) };
		let (mut words_opt, infos, vdata):
			(Option<Vec<Vec<Fr>>>,
			 Vec<WordInfo>,
			 Vec<data_processor::discharge_proof::FailDischargeRecord>) =
			match cached {
			Some((vd, inf)) => {
				utils::logger::log(0, l, &format!(
					"  discharge cache HIT: {} records", inf.len()));
				(None, inf, vd)
			}
			None => {
				let trip: Vec<(Vec<Fr>,
					data_processor::discharge_proof::FailDischargeRecord,
					WordInfo)> = all_files.par_iter().map(|fp| {
					let nib = utils::os::read_nibbles(
						&format!("{}/{}", proot, fp));
					let fnib: Vec<Fr> = nib.iter()
						.map(|x| Fr::from(*x as u32)).collect();
					let packed = utils::data::pack_nibbles(&fnib);
					let (fdr, rec) =
					  data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
						fp, &nib, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
						&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
						&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
						&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
						&db.sig_to_id, mw, mw);
					(packed, fdr, rec)
				}).collect();
				let (mut w, mut v, mut i) = (vec![], vec![], vec![]);
				for (a, b, c) in trip { w.push(a); v.push(b); i.push(c); }
				save_discharge_cache(&dcache, &v, &i);
				(Some(w), i, v)
			}
		};
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 3 time".to_string(), &mut gt);

		// step 4: NEEDS distribution over the full list.
		utils::logger::log(0, l,
			&"PROGRESS step 4/6: NEEDS distribution".to_string());
		let rows: Vec<Vec<usize>> = vdata.iter()
			.map(|r| r.chunk_peaks.needs_per_chunk.clone()).collect();
		crate::needs_dist::print_needs_dist_rows(&rows, &all_files,
			&format!("{}/config/needs_dist.txt", cd));
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 4 time".to_string(), &mut gt);

		// step 5: capacity ladder (load if present, else estimate+determine).
		utils::logger::log(0, l,
			&"PROGRESS step 5/6: capacity ladder".to_string());
		let ladder_path = format!("{}/{}", proot, rc.config_out);
		let ladder: Vec<crate::determine_config::CapParams> =
			if !reset && std::path::Path::new(&ladder_path).exists() {
				utils::logger::log(0, l, &"  ladder cache HIT".to_string());
				crate::determine_config::load_ladder(&ladder_path)
			} else {
				let words = words_opt.take().unwrap_or_else(|| {
					all_files.par_iter().map(|fp| {
						let nib = utils::os::read_nibbles(
							&format!("{}/{}", proot, fp));
						let fnib: Vec<Fr> = nib.iter()
							.map(|x| Fr::from(*x as u32)).collect();
						utils::data::pack_nibbles(&fnib)
					}).collect()
				});
				let est = estimate_config_aggr::<Fr>(&vdata, &*db, &[100],
					&mut vlog);
				let seed = estimated_to_capparams_aggr(&est[0], mw,
					rc.range2_bit, 3);
				let total_word_n: usize = words.iter().map(|w| w.len()).sum();
				let lkup_len = db.lkup.get_size();
				let n_threads = std::env::var("ZKR_DC_THREADS").ok()
					.and_then(|s| s.parse().ok()).unwrap_or(4);
				let (lad, hist) = super::determine_config_aggr::<Fr,C1,CS1>(
					db.clone(), &words, &infos, &vdata, seed, mw, lkup_len,
					total_word_n, rc.k_max, rc.n_buckets, 60, n_threads, 8,
					rc.peel_pct).expect("determine_config_aggr");
				crate::determine_config::save_ladder(&lad, &ladder_path)
					.expect("save ladder");
				utils::logger::log(0, l, &format!(
					"  ladder: {} rungs, hist={:?}", lad.len(), hist));
				lad
			};
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 5 time".to_string(), &mut gt);

		// ladder-only harvest (ZKR_DLP_LADDER_ONLY=1): stop right after the
		// ladder is built+saved, before the expensive fold. Unset =>
		// unchanged (bare `cargo test full_dlp` byte-identical).
		if std::env::var("ZKR_DLP_LADDER_ONLY").as_deref() == Ok("1") {
			utils::logger::log(0, l, &format!(
				"LADDER ONLY: ladder saved ({} rungs); stop before fold",
				ladder.len()));
			return;
		}

		// step 6: multi-job fold (re-discharges per job; CS-only aggressive).
		utils::logger::log(0, l,
			&format!("PROGRESS step 6/6: fold {} jobs", num_jobs));
		drop(words_opt); drop(infos); drop(vdata); drop(db);
		get_global_config().b_estimate_caps = false;
		get_global_config().aggr_needs_subsigs =
			ladder.first().map(|c| c.aggr_needs_subsigs).unwrap_or(0);
		let cs_caps: Vec<_> = ladder.iter().map(caps_from_params_aggr)
			.collect();
		// two-half scheme: fold only this process's job half. read_mode
		// first => jobs 0..h-1, second => h..N-1, full/unset => all (bare
		// test byte-identical). job_{i}.dat names carry the global id, so
		// load_files' PROBE DLP lines report the right jobs per part.
		let h = num_jobs / 2;
		let job_fold: Vec<String> =
			match std::env::var("ZKR_DLP_READ_MODE").as_deref() {
				Ok("first") => job_rel[..h].to_vec(),
				Ok("second") => job_rel[h..].to_vec(),
				_ => job_rel.clone(),
			};
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), job_fold, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), mw, &cs_caps,
			//cs_caps IS the tuned ladder (determine_config_aggr above), so
			//the driver must NOT tune again.
			false, DcMode::Off);
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 6 time".to_string(), &mut gt);
	}

	/// NUMA-probe sibling of full_dlp(): SAME discharge -> ladder ->
	/// multi-job fold path, but folding-only (no decider) on the tiny
	/// data/debug/numa_probe corpus. For numa_probe.py per-step fold ms
	/// under a numactl matrix. full_dlp() itself is left untouched.
	#[test]
	pub fn numa_probe_dlp(){
		use crate::determine_config::caps_from_params_aggr;
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		use rayon::prelude::*;
		utils::os::print_computer_config(Some("full_dlp"));
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		let reset = rc.reset;
		let num_jobs = rc.num_jobs.max(1);
		let l = utils::logger::LOG1;
		let mut gt = utils::timer::Timer::new();
		// NUMA (ZKR_NUMA=perjob): interleave the shared DB/ACDFA across nodes so
		// the per-job worker threads (pinned in driver.rs) read it with balanced
		// bandwidth instead of hammering one remote node. No-op unless multi-node
		// + flag set. See folding_schemes::folding::foldpot::numa.
		folding_schemes::folding::foldpot::numa::set_interleave_all();
		//NUMA probe: folding-only (no decider) so each policy run ends at
		//the fold; b_light_test=false mirrors full_dlp's production config.
		//b_one_proof=true is moot when folding-only (no proof emitted).
		get_global_config().log_level = utils::logger::LOG3;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = false; // match full_dlp config
		get_global_config().b_folding_only = true; // folding-only (probe)
		get_global_config().b_one_proof = true;     // ONE proof only
		get_global_config().b_read_cache = true;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_estimate_caps = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().log_level = utils::logger::LOG3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];

		// step 1: load DB.
		utils::logger::log(0, l, &"PROGRESS step 1/6: load DB".to_string());
		let db = std::sync::Arc::new(
			data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db"));
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 1 time".to_string(), &mut gt);

		// step 2: deterministic size-balanced split -> job_<i>.dat (reuse).
		utils::logger::log(0, l,
			&format!("PROGRESS step 2/6: split {} jobs", num_jobs));
		let jobs_dir = format!("{}/{}/jobs/jobs{}", proot, cd, num_jobs);
		let job_rel: Vec<String> = (0..num_jobs).map(|i|
			format!("{}/jobs/jobs{}/job_{}.dat", cd, num_jobs, i)).collect();
		let have_all = job_rel.iter().all(|p|
			std::path::Path::new(&format!("{}/{}", proot, p)).exists());
		if reset || !have_all {
			let bins = split_jobs_balanced(
				&format!("{}/{}", cd, rc.full_list), num_jobs);
			let _ = std::fs::create_dir_all(&jobs_dir);
			for (i, b) in bins.iter().enumerate() {
				std::fs::write(format!("{}/job_{}.dat", jobs_dir, i),
					b.join("\n")).expect("write job file");
			}
		}
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 2 time".to_string(), &mut gt);

		// step 3: discharge the full list (cache vdata+infos; words lazy).
		utils::logger::log(0, l,
			&"PROGRESS step 3/6: discharge full list".to_string());
		let all_files = read_path_list(&format!("{}/{}", cd, rc.full_list));
		let dcache = discharge_cache_dir(&rc.cache_dir, mw, rc.fanout_cap,
			rc.range2_bit, 3);
		let cached = if reset { None } else { load_discharge_cache(&dcache) };
		let (mut words_opt, infos, vdata):
			(Option<Vec<Vec<Fr>>>,
			 Vec<WordInfo>,
			 Vec<data_processor::discharge_proof::FailDischargeRecord>) =
			match cached {
			Some((vd, inf)) => {
				utils::logger::log(0, l, &format!(
					"  discharge cache HIT: {} records", inf.len()));
				(None, inf, vd)
			}
			None => {
				let trip: Vec<(Vec<Fr>,
					data_processor::discharge_proof::FailDischargeRecord,
					WordInfo)> = all_files.par_iter().map(|fp| {
					let nib = utils::os::read_nibbles(
						&format!("{}/{}", proot, fp));
					let fnib: Vec<Fr> = nib.iter()
						.map(|x| Fr::from(*x as u32)).collect();
					let packed = utils::data::pack_nibbles(&fnib);
					let (fdr, rec) =
					  data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
						fp, &nib, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
						&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
						&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
						&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
						&db.sig_to_id, mw, mw);
					(packed, fdr, rec)
				}).collect();
				let (mut w, mut v, mut i) = (vec![], vec![], vec![]);
				for (a, b, c) in trip { w.push(a); v.push(b); i.push(c); }
				save_discharge_cache(&dcache, &v, &i);
				(Some(w), i, v)
			}
		};
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 3 time".to_string(), &mut gt);

		// step 4: NEEDS distribution over the full list.
		utils::logger::log(0, l,
			&"PROGRESS step 4/6: NEEDS distribution".to_string());
		let rows: Vec<Vec<usize>> = vdata.iter()
			.map(|r| r.chunk_peaks.needs_per_chunk.clone()).collect();
		crate::needs_dist::print_needs_dist_rows(&rows, &all_files,
			&format!("{}/config/needs_dist.txt", cd));
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 4 time".to_string(), &mut gt);

		// step 5: capacity ladder (load if present, else estimate+determine).
		utils::logger::log(0, l,
			&"PROGRESS step 5/6: capacity ladder".to_string());
		let ladder_path = format!("{}/{}", proot, rc.config_out);
		let ladder: Vec<crate::determine_config::CapParams> =
			if let Ok(lp) = std::env::var("ZKR_LOAD_LADDER") {
				// NUMA probe: pin the PRODUCTION ladder so the folded
				// circuits match production sizes (faithful per-step).
				let p = format!("{}/{}", proot, lp);
				utils::logger::log(0, l,
					&format!("  ladder PINNED: {}", p));
				crate::determine_config::load_ladder(&p)
			} else if !reset
				&& std::path::Path::new(&ladder_path).exists() {
				utils::logger::log(0, l, &"  ladder cache HIT".to_string());
				crate::determine_config::load_ladder(&ladder_path)
			} else {
				let words = words_opt.take().unwrap_or_else(|| {
					all_files.par_iter().map(|fp| {
						let nib = utils::os::read_nibbles(
							&format!("{}/{}", proot, fp));
						let fnib: Vec<Fr> = nib.iter()
							.map(|x| Fr::from(*x as u32)).collect();
						utils::data::pack_nibbles(&fnib)
					}).collect()
				});
				let est = estimate_config_aggr::<Fr>(&vdata, &*db, &[100],
					&mut vlog);
				let seed = estimated_to_capparams_aggr(&est[0], mw,
					rc.range2_bit, 3);
				let total_word_n: usize = words.iter().map(|w| w.len()).sum();
				let lkup_len = db.lkup.get_size();
				let n_threads = std::env::var("ZKR_DC_THREADS").ok()
					.and_then(|s| s.parse().ok()).unwrap_or(4);
				let (lad, hist) = super::determine_config_aggr::<Fr,C1,CS1>(
					db.clone(), &words, &infos, &vdata, seed, mw, lkup_len,
					total_word_n, rc.k_max, rc.n_buckets, 60, n_threads, 8,
					rc.peel_pct).expect("determine_config_aggr");
				crate::determine_config::save_ladder(&lad, &ladder_path)
					.expect("save ladder");
				utils::logger::log(0, l, &format!(
					"  ladder: {} rungs, hist={:?}", lad.len(), hist));
				lad
			};
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 5 time".to_string(), &mut gt);

		// step 6: multi-job fold (re-discharges per job; CS-only aggressive).
		utils::logger::log(0, l,
			&format!("PROGRESS step 6/6: fold {} jobs", num_jobs));
		drop(words_opt); drop(infos); drop(vdata); drop(db);
		get_global_config().b_estimate_caps = false;
		get_global_config().aggr_needs_subsigs =
			ladder.first().map(|c| c.aggr_needs_subsigs).unwrap_or(0);
		let cs_caps: Vec<_> = ladder.iter().map(caps_from_params_aggr)
			.collect();
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), job_rel, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), mw, &cs_caps,
			//cs_caps IS the tuned ladder (determine_config_aggr above), so
			//the driver must NOT tune again.
			false, DcMode::Off);
		utils::logger::log_perf(0, l,
			&"PERF WORKFLOW Step 6 time".to_string(), &mut gt);
	}

	/// Q2 lookup-composition report. Builds each dataset's DB FRESH (no
	/// cache, no folding, no proving) and prints the per-source lookup
	/// breakdown one dataset at a time, then a cross-dataset roll-up.
	/// All three build with default_clamav_cfg(); only sig paths and
	/// range2_bit differ (Dlp also mirrors full_dlp's RunCfg + aggressive
	/// globals). Runs on a local machine.
	///   cargo run --release --example main -- collect_lookup_stats
	#[test]
	pub fn collect_lookup_stats() {
		use data_processor::clam_db::ClamavDB;
		use data_processor::clamav::default_clamav_cfg;

		get_global_config().log_level = utils::logger::LOG3;

		let cfg = default_clamav_cfg();
		let mut rollups: Vec<(&str, Vec<(&'static str, usize)>)> = Vec::new();
		// parallel to rollups: per-dataset #DFAs folded into the lookup.
		let mut dfa_rollups: Vec<(&str, Vec<(&'static str, usize)>)> = Vec::new();
		// buffer each dataset block so all three print together at the end,
		// uncluttered by the LOG3 build chatter above.
		let mut blocks: Vec<String> = Vec::new();

		// ---- Mal (CentOS x ClamAV) : full_clamav db-build config ----
		get_global_config().range2_bit = 26;
		let d = "data/debug/full_clamav/config";
		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::build_or_load(&cfg,
			&format!("{}/main.dat", d), &format!("{}/main_dfa.dat", d),
			&format!("{}/needs_ised.dat", d), &format!("{}/needs_ised_igc.dat", d),
			&mut vlog, "lkup_stats_tmp", false, false).expect("build Mal db");
		blocks.push(db.fmt_lkup_dist("Mal", &format!("{}/main.dat", d)));
		rollups.push(("Mal", db.lkup_cat_rollup()));
		dfa_rollups.push(("Mal", db.dfa_counts()));

		// ---- Dna (chr17 x NCBI) : full_dna db-build config ----
		get_global_config().range2_bit = 27;
		let d = "data/paper_data/dna/config";
		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::build_or_load(&cfg,
			&format!("{}/main.dat", d), &format!("{}/main_dfa.dat", d),
			&format!("{}/needs_ised.dat", d), &format!("{}/needs_ised_igc.dat", d),
			&mut vlog, "lkup_stats_tmp", false, false).expect("build Dna db");
		blocks.push(db.fmt_lkup_dist("Dna", &format!("{}/main.dat", d)));
		rollups.push(("Dna", db.lkup_cat_rollup()));
		dfa_rollups.push(("Dna", db.dfa_counts()));

		// ---- Dlp (Enron x MS-DLP) : full_dlp db-build config ----
		// hard-coded full-run Dlp config (read from disk; no env needed)
		let rc = crate::determine_config::RunCfg::from_path(&format!(
			"{}/data/paper_data/dlp/cfg/config/runcfg_full.json",
			utils::os::proj_root()));
		let cd = rc.config_dir.clone();
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let sig = format!("{}/{}", cd, rc.sig_file);
		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::build_or_load(&cfg, &sig,
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd),
			&mut vlog, "lkup_stats_tmp", false, false).expect("build Dlp db");
		blocks.push(db.fmt_lkup_dist("Dlp", &sig));
		rollups.push(("Dlp", db.lkup_cat_rollup()));
		dfa_rollups.push(("Dlp", db.dfa_counts()));

		// machine config + all three blocks + cross-dataset roll-up,
		// together at the end (uncluttered by the LOG3 build chatter above).
		// Route the whole report through the same async stdout channel as
		// print_computer_config so it stays FIFO-ordered after the config
		// block (a direct println! would race ahead of the logger thread).
		utils::os::print_computer_config(Some("collect_lookup_stats"));
		let mut report = String::from(
			"\n\n#################### LOOKUP COMPOSITION REPORT ####################\n");
		for b in &blocks { report.push_str(b); report.push('\n'); }
		report.push_str(&fmt_cross_rollup(&rollups));
		report.push_str(&fmt_dfa_cross(&dfa_rollups));
		report.push_str(
			"\n#################### END LOOKUP COMPOSITION REPORT ###############");
		utils::logger::emit_stdout(report);
	}

	/// Cross-dataset category roll-up (% of each dataset's populated
	/// entries), one column per dataset. Categories arrive in fixed order.
	/// Returned as a String so it prints with the per-dataset blocks.
	fn fmt_cross_rollup(rollups: &[(&str, Vec<(&'static str, usize)>)]) -> String {
		use std::fmt::Write as _;
		let totals: Vec<usize> = rollups.iter()
			.map(|(_, r)| r.iter().map(|(_, n)| n).sum()).collect();
		let bar: String = rollups.iter().map(|_| "  --------").collect();

		let mut s = String::new();
		let _ = writeln!(s, "=============== Cross-Dataset Roll-up (% of populated) ========");
		let _ = write!(s, "  {:<12}", "Category");
		for (name, _) in rollups { let _ = write!(s, "  {:>8}", name); }
		let _ = writeln!(s, "\n  {:<12}{}", "----------", bar);
		let ncat = rollups.first().map(|(_, r)| r.len()).unwrap_or(0);
		for ci in 0..ncat {
			let _ = write!(s, "  {:<12}", rollups[0].1[ci].0);
			for (di, (_, r)) in rollups.iter().enumerate() {
				let p = if totals[di] > 0 { 100.0 * r[ci].1 as f64 / totals[di] as f64 } else { 0.0 };
				let _ = write!(s, "  {:>8.1}", p);
			}
			let _ = writeln!(s);
		}
		let _ = writeln!(s, "  {:<12}{}", "----------", bar);
		let _ = write!(s, "  {:<12}", "TOTAL (M)");
		for t in &totals { let _ = write!(s, "  {:>8.1}", *t as f64 / 1e6); }
		let _ = writeln!(s, "\n===============================================================");
		s
	}

	/// Cross-dataset DFA-count table: absolute number of DFAs folded into
	/// the lookup table, one column per dataset, one row per source, with a
	/// TOTAL row. Sources arrive in fixed order (db.dfa_counts()).
	fn fmt_dfa_cross(rollups: &[(&str, Vec<(&'static str, usize)>)]) -> String {
		use std::fmt::Write as _;
		let totals: Vec<usize> = rollups.iter()
			.map(|(_, r)| r.iter().map(|(_, n)| n).sum()).collect();
		let bar: String = rollups.iter().map(|_| "  ----------").collect();

		let mut s = String::new();
		let _ = writeln!(s, "\n=============== Cross-Dataset #DFAs in Lookup ==================");
		let _ = write!(s, "  {:<18}", "Source");
		for (name, _) in rollups { let _ = write!(s, "  {:>10}", name); }
		let _ = writeln!(s, "\n  {:<18}{}", "----------------", bar);
		let nsrc = rollups.first().map(|(_, r)| r.len()).unwrap_or(0);
		for si in 0..nsrc {
			let _ = write!(s, "  {:<18}", rollups[0].1[si].0);
			for (_, r) in rollups { let _ = write!(s, "  {:>10}", r[si].1); }
			let _ = writeln!(s);
		}
		let _ = writeln!(s, "  {:<18}{}", "----------------", bar);
		let _ = write!(s, "  {:<18}", "TOTAL");
		for t in &totals { let _ = write!(s, "  {:>10}", t); }
		let _ = writeln!(s, "\n===============================================================");
		s
	}

	/// Build/load a dataset DB and quick-discharge its corpus (NON-aggressive),
	/// returning the per-file records + the ruleset size. Sets only the two
	/// globals that affect classification (range2_bit; aggressive OFF); the DB
	/// is loaded from its cache, which already encodes its build params.
	fn discharge_dataset(
		sig_file: &str, dfa_file: &str, ised_file: &str, ised_igc_file: &str,
		cache_dir: &str, scan_paths: &[String],
		range2_bit: usize, max_word_len: usize,
		b_read_cache: bool, b_write_cache: bool,
	) -> (Vec<data_processor::discharge_proof::FailDischargeRecord>, usize) {
		use rayon::prelude::*;
		get_global_config().range2_bit = range2_bit;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = false;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let proot = utils::os::proj_root();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, sig_file, dfa_file, ised_file, ised_igc_file,
			&mut vlog, cache_dir, b_read_cache, b_write_cache)
			.expect("build/load db");
		let total_sigs = db.vec_sigs.len();
		let recs: Vec<_> = scan_paths.par_iter().map(|fp| {
			let nib = utils::os::read_nibbles(&format!("{}/{}", proot, fp));
			let (fdr, _wi) =
				data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
					fp, &nib, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
					&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
					&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
					&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
					&db.sig_to_id, max_word_len, max_word_len);
			fdr
		}).collect();
		(recs, total_sigs)
	}

	/// Print one tier block: aggregate pair shares + up to 3 sample records.
	/// cp = total_sigs-|crit|, sde = |crit|-|pm|, dfa = |pm|-|all_dfa|,
	/// fail = |all_dfa| (summed over files). total_pairs = total_sigs*#files.
	fn report_tier_block(
		label: &str,
		recs: &[data_processor::discharge_proof::FailDischargeRecord],
		total_sigs: usize,
	) {
		if recs.is_empty() { return; }
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
		println!("=== {} ===", label);
		println!("total_sigs: {}  files: {}  total_pairs: {}",
			total_sigs, n, total);
		println!("cp: {} ({:.4}%)  sde: {} ({:.4}%)  dfa: {} ({:.4}%)  \
fail: {} ({:.4}%)",
			cp, pct(cp), sde, pct(sde), dfa, pct(dfa), fail, pct(fail));
		for (i, r) in recs.iter().take(3).enumerate() {
			println!("sample {}: fname: {}  flen: {}  |crit|: {}  |bag|: {}  \
|pm|: {}  |all_dfa|: {}",
				i + 1, r.fname, r.flen,
				r.crit.len(), r.bag.len(), r.pm.len(), r.all_dfa.len());
			println!("  record: {:?}", r);
		}
		println!();
	}

	/// Collect Figure-9 data. (a) per-dataset tier shares for Mal/Dna/Dlp;
	/// (b) Mal stratified by file size (flen = floor(log2 bytes)+1 bucket).
	/// Non-aggressive for all three; Dlp = full ~505K list (from .tgz).
	pub fn collect_assess_tier_data() {
		utils::os::print_computer_config(Some("collect_assess_tier_data"));

		// -------- Figure 9(a) --------
		let mal_scan: Vec<String> = (0..8)
			.flat_map(|i| read_path_list(
				&format!("data/debug/full_clamav/config/binexec_p{}.dat", i)))
			.collect();
		let (mal, mal_sigs) = discharge_dataset(
			"data/debug/full_clamav/config/main.dat",
			"data/debug/full_clamav/config/main_dfa.dat",
			"data/debug/full_clamav/config/needs_ised.dat",
			"data/debug/full_clamav/config/needs_ised_igc.dat",
			"clamav_full", &mal_scan, 26, 512 * 8, true, false);
		report_tier_block("Data for Mal", &mal, mal_sigs);

		let dna_scan = read_path_list("data/paper_data/dna/config/binexec.dat");
		let (dna, dna_sigs) = discharge_dataset(
			"data/paper_data/dna/config/main.dat",
			"data/paper_data/dna/config/main_dfa.dat",
			"data/paper_data/dna/config/needs_ised.dat",
			"data/paper_data/dna/config/needs_ised_igc.dat",
			"dna_data", &dna_scan, 27, 512 * 8, true, false);
		report_tier_block("Data for Dna", &dna, dna_sigs);

		let dlp_scan = read_path_list(
			"data/paper_data/dlp/cfg/jobs/final_enron_list.txt.tgz");
		let (dlp, dlp_sigs) = discharge_dataset(
			"data/paper_data/dlp/cfg/regex_pat/main_data_dlp_internationl.dat",
			"data/paper_data/dlp/cfg/regex_pat/main_dfa.dat",
			"data/paper_data/dlp/cfg/regex_pat/needs_ised.dat",
			"data/paper_data/dlp/cfg/regex_pat/needs_ised_igc.dat",
			"dlp_corpus_aggr", &dlp_scan, 25, 64, true, false);
		report_tier_block("Data for Dlp", &dlp, dlp_sigs);

		// -------- Figure 9(b): Mal/Dlp by file size --------
		let by_size = |ds: &str,
			recs: &[data_processor::discharge_proof::FailDischargeRecord],
			sigs: usize| {
			println!("######## Filesize data for {} ########", ds);
			let mut by_flen: std::collections::BTreeMap<usize, Vec<_>> =
				std::collections::BTreeMap::new();
			for r in recs { by_flen.entry(r.flen).or_default().push(r.clone()); }
			for (flen, bucket) in &by_flen {
				let lo = if *flen == 0 { 0 } else { 1usize << (flen - 1) };
				let hi = 1usize << flen;
				report_tier_block(
					&format!("Filesize data for {} -- flen={} ({}..{} bytes)",
						ds, flen, lo, hi),
					bucket, sigs);
			}
		};
		by_size("Mal", &mal, mal_sigs);
		by_size("Dlp", &dlp, dlp_sigs);
	}

	#[test]
	pub fn test_collect_assess_tier_data() {
		collect_assess_tier_data();
	}

	/// Collect §7.5 scalability-in-regex-set-size data (Q4). The corpus is
	/// FIXED (the difficult gdb 6.6M file); only the rule set grows. We
	/// sweep it in `num_rounds` rounds of `base_share_pct` each, so round
	/// `r in 1..=num_rounds` uses `pct = r*base_share_pct` percent of the
	/// rules; `(10,5)` => 10,20,30,40,50. The subset is the modulo-100
	/// stratification "keep rule `j` iff `j%100 < pct`": the share is spread
	/// across the whole file (not the first N rules) and every round is a
	/// STRICT SUPERSET of the previous one. Settings, capacities and the
	/// rule set are copied from `full_clamav()`; we run folding-only and
	/// REBUILD the DB from each subset into the isolated `scale_data` cache
	/// (overwriting the previous round -- never touches a production cache).
	///
	/// Each round's run log is bracketed on stdout with
	/// `==== SCALE ROUND {BEGIN,END} pct=<P> ====`. `COST GRAND TOTAL` is
	/// emitted to stdout only (no per-job file), so `run_collect_scale_data.py`
	/// splits the captured stdout on these markers into per-round
	/// `log_<pct>.txt` files. No tgz here -- the Python wrapper compresses.
	#[allow(dead_code)]
	pub fn collect_scale_data(vec_count: Vec<usize>) {
		utils::os::print_computer_config(Some("collect_scale_data"));
		// enable the forward-queue membership dump for THIS function only.
		utils::consts::SCALE_DUMP_FWD
			.store(true, std::sync::atomic::Ordering::Relaxed);
		// vec_count: strictly ascending, distinct, each >= 1. Each round folds
		// the first `cnt` rules of a FIXED pseudo-random permutation of the
		// rule set (raw sig count), so rounds are nested supersets. The upper
		// bound (cnt <= n_rules) is checked once n_rules is known.
		assert!(!vec_count.is_empty(), "vec_count must be non-empty");
		assert!(vec_count.iter().all(|&c| c >= 1),
			"vec_count entries must be >= 1: {:?}", vec_count);
		assert!(vec_count.windows(2).all(|w| w[0] < w[1]),
			"vec_count must be strictly ascending and distinct: {:?}", vec_count);
		// FIXED pseudo-random permutation (splitmix64 Fisher-Yates; identical
		// every run, independent of the rand crate version).
		const SCALE_PERM_SEED: u64 = 0x5CA1_5EED_0F0F_0F0F;
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

		// ---- settings: identical to full_clamav() (non-setup), except
		// folding-only and pointed at the isolated scale_data cache. ----
		get_global_config().snark_cache_dir = "scale_data".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_folding_only = true;   // discharge: folding only
		get_global_config().b_show_queue_saturated = true; // audit fwd-queue >85%
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = false;
		// Option A: LOW floors so determine_config's CapErr back-solve derives
		// each subset's real caps (it only bumps UP from the floor; a high
		// floor pins every subset to full-clamav size -> flat curve + OOM).
		get_global_config().min_subsigs = 64;
		get_global_config().min_basis_unique_states = 100;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().min_dfa_sigs = 2;
		get_global_config().min_dfa_subsigs = 2;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;
		get_global_config().log_level = utils::logger::LOG3;

		// REBUILD the DB from each subset every round (never read a stale
		// cache; b_write_cache writes the fresh subset DB into scale_data).
		get_global_config().b_read_cache = false;
		let b_write_cache = true;

		// ---- LOW starting caps (Option A). These are the determine_config
		// warm-start baseline (cur/p0); the per-round probe CapErr-bumps each
		// UP to the subset's actual need, so the circuit (and RAM) tracks the
		// rule-set size instead of being pinned at full-clamav size. ----
		let set1 = "data/debug/full_clamav/config/";
		let max_word = 512 * 8;
		let sigs = 64;
		let subsigs = 64;
		let avg_pats_per_subsig = 8;
		let avg_active_pats_per_subsig = 2;
		let perc_comp_subsigs = 20;
		// Single full-cap circuit (like full_dna): no decrease ladder, so the
		// full-length 0-pad word always lands in a full-cap circuit (the
		// reversed ladder otherwise starves the decreased layer-0 circuit).
		let vec_decrease_level: Vec<usize> = vec![];
		let num_circs = 1;
		// basis_unique_states floored at the 0-word's required minimum: the CP
		// pack gadget needs >=120 for the full-length 0-pad word (memorized from
		// prior runs). The probe bumps it higher for larger subsets.
		let basis_unique_states = 120;
		let basis_acc_states = 2;
		let basis_pats_in_trace = 4;
		// igc arm starts LOW like the cs arm (Option A): the old 750/820 pin
		// was unreal for these subsets (measured igc acc=0, igc fill=0) and
		// inflated FsmAdvGadget by ~0.8M/step. basis_acc/basis_pats start at
		// the cs floors and bump UP per subset via fsm_adv CapErr; the forward
		// queue's room is carried by perc_pats_expansion_rate_igc (FSM-free)
		// instead of basis_pats_in_trace_igc (FSM-coupled). The earlier
		// "perc CapErr can't converge" risk is covered by the dummy-sentinel
		// pfloor added to the perc tightener above.
		let basis_acc_states_igc = 2;
		let basis_pats_in_trace_igc = 4;
		let dfa_sigs = 2;
		let dfa_subsigs = 2;
		let perc_pats_expansion_rate = 104;
		let perc_pats_expansion_rate_igc = 104;

		let init_cp_cap = CpCapacity{
			max_word_len: max_word, basis_unique_states, subsigs,
			avg_pats_per_subsig };
		let init_sed_cap = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace, perc_pats_expansion_rate, sigs,
			perc_comp_subsigs, basis_unique_states, basis_acc_states);
		let init_dfa_cap = DfaCapacity::new(max_word, dfa_sigs, dfa_subsigs);
		let init_cp_cap_igc = CpCapacity{
			max_word_len: max_word, basis_unique_states, subsigs,
			avg_pats_per_subsig };
		let init_sed_cap_igc = SedCapacity::new(
			max_word, read_global_config().range2_bit, subsigs,
			avg_pats_per_subsig, avg_active_pats_per_subsig,
			basis_pats_in_trace_igc, perc_pats_expansion_rate_igc, sigs,
			perc_comp_subsigs, basis_unique_states, basis_acc_states_igc);

		// ---- fixed corpus: the difficult gdb (6.6M) single file ----
		// Own isolated list file in /tmp (written by run_collect_scale_data.py:
		// the foldpot 0-word prepended to gdb). Absolute -> load_files's
		// is_absolute guard reads it as-is; no existing sample/config touched.
		let scan_files = vec![
			"/tmp/bora/scale/binexec_3.dat".to_string()];

		// ---- full rule set (read once, same filter as build_db so the
		// modulo index lines up with the DB's sig ordering) ----
		let proot = utils::os::proj_root();
		let all_rules: Vec<String> = utils::os::read_lines(
				&format!("{}/{}main.dat", proot, set1))
			.into_iter()
			.filter(|s| !s.starts_with('#') && !s.trim().is_empty())
			.collect();
		let n_rules = all_rules.len();
		let perm = fixed_perm(n_rules, SCALE_PERM_SEED);   // fixed shuffled order

		// full auxiliary "needs" lists (sig NAMES, one per line). A rule
		// subset must not reference a name it dropped, so each round we filter
		// these to the subset's names -- build_ised_bundle asserts every listed
		// name resolves to exactly one loaded sig.
		let needs_dfa_full = utils::os::read_lines(
			&format!("{}/{}main_dfa.dat", proot, set1));
		let needs_ised_full = utils::os::read_lines(
			&format!("{}/{}needs_ised.dat", proot, set1));
		let needs_ised_igc_full = utils::os::read_lines(
			&format!("{}/{}needs_ised_igc.dat", proot, set1));

		// runtime scratch -- kept OUT of the project tree (cache stays in
		// data/cache/scale_data; only the subset sig + needs files live here).
		let scratch = "/tmp/bora/scale";
		std::fs::create_dir_all(scratch).expect("mkdir /tmp/bora/scale");
		// fresh sweep: drop any warm-start caps from a prior invocation so
		// round 1 converges from the floors (zkp_driver_adv re-saves per round).
		let _ = std::fs::remove_file(format!("{}/warmstart_caps.json", scratch));
		let sub_main = format!("{}/main_scale.dat", scratch);
		let sub_dfa = format!("{}/needs_dfa.dat", scratch);
		let sub_ised = format!("{}/needs_ised.dat", scratch);
		let sub_ised_igc = format!("{}/needs_ised_igc.dat", scratch);

		for &cnt in vec_count.iter() {
			// take exactly the first `cnt` rules of the fixed permutation =>
			// nested supersets.
			assert!(cnt <= n_rules,
				"count {} exceeds rule total {}", cnt, n_rules);
			let count = cnt;
			let subset: Vec<&str> = perm.iter().take(count)
				.map(|&i| all_rules[i].as_str())
				.collect();
			std::fs::write(&sub_main, subset.join("\n") + "\n")
				.expect("write subset main_scale.dat");

			// drop needs-list entries whose sig is not in this subset (the sig
			// name is the token before the first ';' or ':').
			let names: std::collections::HashSet<String> = subset.iter()
				.map(|l| l.split(|c| c == ';' || c == ':')
					.next().unwrap_or("").trim().to_string())
				.collect();
			let filt = |full: &[String]| -> String {
				let kept: Vec<&str> = full.iter()
					.map(|s| s.trim())
					.filter(|n| !n.is_empty() && !n.starts_with('#')
						&& names.contains(*n))
					.collect();
				if kept.is_empty() { String::new() }
				else { kept.join("\n") + "\n" }
			};
			std::fs::write(&sub_dfa, filt(&needs_dfa_full))
				.expect("write needs_dfa");
			std::fs::write(&sub_ised, filt(&needs_ised_full))
				.expect("write needs_ised");
			std::fs::write(&sub_ised_igc, filt(&needs_ised_igc_full))
				.expect("write needs_ised_igc");

			let corpus = std::env::var("ZKR_SCALE_CORPUS")
				.unwrap_or_else(|_| "unknown".to_string());
			utils::logger::emit_stdout(format!(
				"==== SCALE ROUND BEGIN count={} rules={}/{} corpus={} ====",
				cnt, subset.len(), n_rules, corpus));
			utils::logger::flush_logger();

			zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(
				0,
				&sub_main,                                  // subset sig file
				scan_files.clone(),
				"data/debug/full_clamav/reports/report2.dat",
				b_write_cache,
				"scale_data",                               // isolated cache
				&sub_dfa,
				&sub_ised,
				&sub_ised_igc,
				max_word,
				&init_cp_cap, &init_sed_cap, &init_dfa_cap,
				&init_cp_cap_igc, &init_sed_cap_igc,
				&vec_decrease_level, num_circs, false, DcMode::ProbeThenFold);

			utils::logger::flush_logger();
			utils::logger::emit_stdout(format!(
				"==== SCALE ROUND END count={} ====", cnt));
			utils::logger::flush_logger();
		}
	}

	#[test]
	pub fn test_collect_scale_data() {
		// Full sweep: 1 rule, then 10%, 20%, ..., 100% of the 38,875-rule
		// ClamAV set (rounded to nearest). Strictly ascending; last = full set.
		let n_rules = 38875usize;
		let mut counts: Vec<usize> = vec![1];
		for p in 1..=10 { counts.push((p * n_rules + 5) / 10); }
		println!("collect_scale_data: counts={:?}", counts);
		collect_scale_data(counts);
	}

	/// DLP twin of collect_scale_data using the AGGRESSIVE tuner (the same path
	/// full_dlp uses). Corpus FIXED (one short email via the /tmp scan list);
	/// sweeps the 9,860 Dlp.* rules (Win.Alphabet.SAMPLE-1 pinned). Folding-only,
	/// isolated scale_data_dlp cache.
	pub fn collect_scale_data_dlp(vec_count: Vec<usize>) {
		use crate::determine_config::{caps_from_params_aggr,
			apply_caperr_bumps, probe_catching};
		use crate::stats_helper::{estimate_config_aggr, estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs::LookupTableTwoCol as _;
		// SCALE finalize: route fold CapErrs (main-thread 0-word advice AND
		// job-thread Pass-1) through catchable unwinding instead of
		// process::exit / fail-fast abort, so the bump-retry below finalizes the
		// caps. Per-process; only this run sets it -> full_dlp/full_clam/full_dna
		// leave it false (RULE 1).
		get_global_config().b_scale_catch_caperr = true;
		utils::os::print_computer_config(Some("collect_scale_data_dlp"));
		utils::consts::SCALE_DUMP_FWD
			.store(true, std::sync::atomic::Ordering::Relaxed);
		assert!(!vec_count.is_empty(), "vec_count must be non-empty");
		assert!(vec_count.iter().all(|&c| c >= 1),
			"vec_count entries must be >= 1: {:?}", vec_count);
		assert!(vec_count.windows(2).all(|w| w[0] < w[1]),
			"vec_count must be strictly ascending and distinct: {:?}", vec_count);
		const SCALE_PERM_SEED: u64 = 0x5CA1_5EED_0F0F_0F0F;
		fn fixed_perm(n: usize, mut s: u64) -> Vec<usize> {
			let mut v: Vec<usize> = (0..n).collect();
			for i in (1..n).rev() {
				s = s.wrapping_add(0x9E3779B97F4A7C15);
				let mut z = s;
				z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
				z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
				z ^= z >> 31;
				v.swap(i, (z % (i as u64 + 1)) as usize);
			}
			v
		}

		// ---- config COPIED FROM full_dlp() (runcfg_full.json + the fn). ----
		let mw = 64usize;            // chunk_len
		let range2_bit = 25usize;
		let fanout_cap = 100usize;
		// SINGLE full-cap rung (like the ClamAV scale's num_circs=1): a decrease
		// ladder starves the smaller rung of capacity for the full 0-pad word
		// (driver.rs:2939). k_max=1, n_buckets=1 -> one rung sized for everything.
		let k_max = 1usize; let n_buckets = 1usize; let peel_pct = 100usize;
		get_global_config().snark_cache_dir = "scale_data_dlp".to_string();
		get_global_config().log_level = utils::logger::LOG3;
		get_global_config().range2_bit = range2_bit;
		get_global_config().b_light_test = false;
		get_global_config().b_folding_only = true;       // scale: folding only
		get_global_config().b_show_queue_saturated = true;
		get_global_config().b_estimate_caps = true;      // aggressive estimate path
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		get_global_config().b_read_cache = false;        // rebuild DB per subset

		let proot = utils::os::proj_root();
		let set1 = "data/paper_data/dlp/cfg/regex_pat/";  // READ-ONLY (rule source)
		let cache_dir = "scale_data_dlp";                 // isolated, NOT full_dlp's
		let report = "/tmp/bora/scale_dlp/report2.dat";   // isolated, NOT full_dlp's
		let cfg = data_processor::clamav::default_clamav_cfg();

		// ---- rule set: pin Win.Alphabet.SAMPLE-1 (line 0), permute the rest. --
		let all_lines: Vec<String> = utils::os::read_lines(
				&format!("{}/{}main_data_dlp_internationl.dat", proot, set1))
			.into_iter()
			.filter(|s| !s.starts_with('#') && !s.trim().is_empty())
			.collect();
		assert!(all_lines.first().map(|l| l.starts_with("Win.Alphabet"))
			.unwrap_or(false), "expected Win.Alphabet.SAMPLE-1 as DLP rule 0");
		let pinned = all_lines[0].clone();
		let all_rules: Vec<String> = all_lines[1..].to_vec();        // 9,860
		let n_rules = all_rules.len();
		let perm = fixed_perm(n_rules, SCALE_PERM_SEED);
		let needs_dfa_full = utils::os::read_lines(
			&format!("{}/{}main_dfa.dat", proot, set1));
		let needs_ised_full = utils::os::read_lines(
			&format!("{}/{}needs_ised.dat", proot, set1));
		let needs_ised_igc_full = utils::os::read_lines(
			&format!("{}/{}needs_ised_igc.dat", proot, set1));

		let scratch = "/tmp/bora/scale_dlp";
		std::fs::create_dir_all(scratch).expect("mkdir /tmp/bora/scale_dlp");
		let sub_main = format!("{}/main_scale.dat", scratch);
		let sub_dfa = format!("{}/needs_dfa.dat", scratch);
		let sub_ised = format!("{}/needs_ised.dat", scratch);
		let sub_ised_igc = format!("{}/needs_ised_igc.dat", scratch);
		let sub_fanout = format!("{}/main_fanout.dat", scratch);
		// master SDE fan-out boost list (the sole-blocker SITs); filtered per
		// subset below and co-located with sub_dfa so the DB build boosts the
		// right wide-proximity SITs for THIS ruleset (matches full_dlp). Without
		// it those SITs fall to the empty DFA tier and fail discharge.
		let fanout_master: Vec<String> = utils::os::read_lines(
				&format!("{}/{}main_fanout.dat", proot, set1))
			.into_iter()
			.filter(|s| !s.starts_with('#') && !s.trim().is_empty())
			.map(|s| s.trim().to_string())
			.collect();
		// corpus list (built by run_collect_scale_dlp.py): one absolute word path.
		let scan_list = format!("{}/binexec_3.dat", scratch);
		let scan_files = vec![scan_list.clone()];
		let corpus_files = utils::os::read_lines(&scan_list);  // absolute paths

		for &cnt in vec_count.iter() {
			assert!(cnt <= n_rules, "count {} exceeds rule total {}", cnt, n_rules);
			// PINNED alphabet + first `cnt` of the permutation.
			let mut subset: Vec<&str> = vec![pinned.as_str()];
			subset.extend(perm.iter().take(cnt).map(|&i| all_rules[i].as_str()));
			std::fs::write(&sub_main, subset.join("\n") + "\n")
				.expect("write subset main_scale.dat");
			let names: std::collections::HashSet<String> = subset.iter()
				.map(|l| l.split(|c| c == ';' || c == ':')
					.next().unwrap_or("").trim().to_string())
				.collect();
			let filt = |full: &[String]| -> String {
				let kept: Vec<&str> = full.iter().map(|s| s.trim())
					.filter(|n| !n.is_empty() && !n.starts_with('#')
						&& names.contains(*n)).collect();
				if kept.is_empty() { String::new() } else { kept.join("\n") + "\n" }
			};
			std::fs::write(&sub_dfa, filt(&needs_dfa_full)).expect("w dfa");
			std::fs::write(&sub_ised, filt(&needs_ised_full)).expect("w ised");
			std::fs::write(&sub_ised_igc, filt(&needs_ised_igc_full)).expect("w isedigc");
			// main_fanout.dat for THIS subset: keep a SIT entry iff some subset
			// sig name contains it. Generated each iteration from the ruleset.
			let kept_fanout: Vec<&str> = fanout_master.iter()
				.filter(|e| names.iter().any(|n| n.contains(e.as_str())))
				.map(|s| s.as_str()).collect();
			std::fs::write(&sub_fanout, kept_fanout.join("\n") + "\n")
				.expect("write main_fanout.dat");

			let corpus = std::env::var("ZKR_SCALE_CORPUS")
				.unwrap_or_else(|_| "unknown".to_string());
			utils::logger::emit_stdout(format!(
				"==== SCALE ROUND BEGIN count={} rules={}/{} corpus={} ====",
				cnt, cnt, n_rules, corpus));
			utils::logger::flush_logger();

			// 1. Build subset DB FRESH for THIS ruleset. b_read_cache=false ->
			// rebuild (NEVER reuse a prior count's cached DB: build_or_load only
			// checks cache_exists, not the sig file, so reading would discharge
			// against the wrong ruleset). Writes the cache (b_write=true) so the
			// fold + its bump-retries -- SAME ruleset, only caps change -- reuse
			// it instead of rebuilding (~21 min each). The DB is rebuilt only
			// here, i.e. exactly once per count when the ruleset changes.
			let mut vlog: Vec<String> = vec![];
			let db = std::sync::Arc::new(
				data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
					&cfg, &sub_main, &sub_dfa, &sub_ised, &sub_ised_igc,
					&mut vlog, cache_dir, false, true).expect("build db"));
			// fold + bump-retries below read THIS fresh cache (same ruleset);
			// the next count's step 1 above rebuilds (b_read_cache=false there).
			get_global_config().b_read_cache = true;

			// 2. discharge the corpus -> words/infos/vdata (mirror full_dlp_sample).
			let (mut vdata, mut words, mut infos) = (vec![], vec![], vec![]);
			for fpath in &corpus_files {
				let nibbles = utils::os::read_nibbles(fpath);  // absolute path
				let f_nib: Vec<Fr> = nibbles.iter().map(|x| Fr::from(*x as u32))
					.collect();
				words.push(utils::data::pack_nibbles(&f_nib));
				let (fdr, rec) =
					data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
						fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
						&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
						&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
						&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
						&db.sig_to_id, mw, mw);
				vdata.push(fdr); infos.push(rec);
			}

			// 2b. Add foldpot's canonical full 0-pad word to the TUNING set ONLY
			// (not the fold corpus): determine_config_aggr's Phase-A then sizes
			// every cap to discharge it, mirroring ProbeThenFold's 0-word probe
			// push (zkp_driver_adv:1510). Without it the aggressive lower-bound
			// caps miss the 0-word advice demands and the fold panics
			// (driver.rs:2939). LOCAL to collect_scale_data_dlp.
			{
				let pad_nibs = utils::data::gen_pad_nibbles(0, mw * 62);
				let pad_fnib: Vec<Fr> = pad_nibs.iter()
					.map(|x| Fr::from(*x as u32)).collect();
				words.push(utils::data::pack_nibbles(&pad_fnib));
				let (fdr, rec) =
					data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
						"__0word__", &pad_nibs, &db.vec_sigs,
						&db.vec_sigs_no_critical_pat, &db.map_crit_pat,
						&db.map_crit_pat_igc, &db.dfa_crit,
						&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
						&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
						&db.sig_to_id, mw, mw);
				vdata.push(fdr); infos.push(rec);
			}

			// 3. estimate -> seed -> aggressive ladder.
			let est = estimate_config_aggr::<Fr>(&vdata, &*db, &[100], &mut vlog);
			let seed = estimated_to_capparams_aggr(&est[0], mw, range2_bit, 3);
			let total_word_n: usize = words.iter().map(|w| w.len()).sum();
			let lkup_len = db.lkup.get_size();
			let n_threads = std::env::var("ZKR_DC_THREADS").ok()
				.and_then(|s| s.parse().ok()).unwrap_or(4);
			let (ladder, hist) = super::determine_config_aggr::<Fr,C1,CS1>(
				db.clone(), &words, &infos, &vdata, seed, mw, lkup_len,
				total_word_n, k_max, n_buckets, 60, n_threads, 8, peel_pct)
				.expect("determine_config_aggr");
			utils::logger::emit_stdout(format!(
				"[scale_dlp] count={}: ladder {} rungs hist={:?}",
				cnt, ladder.len(), hist));

			// 4. Finalize caps against foldpot's full-0-word advice
			// (driver.rs:2925) via the EXISTING bump machinery, then fold. The
			// tuner's probe (capacity_probe_collect) never runs that stricter
			// 0-word preprocessing, so it under-sizes the CP/FSM caps. Here we
			// run the fold, catch the main-thread 0-word CapErr with
			// probe_catching, apply_caperr_bumps, and retry. Failed tries die
			// early at the 0-word check (before COST/folding) so they are cheap;
			// only the final try emits COST + folds. A non-CapErr panic is a
			// HARD STOP (no fallback). All LOCAL to collect_scale_data_dlp.
			get_global_config().b_estimate_caps = false;
			drop(db);  // zkp_driver_adv_aggr reloads the DB from the cache
			let mut p = ladder[0].clone();
			let mut tries = 0u32;
			loop {
				get_global_config().aggr_needs_subsigs = p.aggr_needs_subsigs;
				let cs_caps = vec![caps_from_params_aggr(&p)];
				utils::consts::reset_sat();  // isolate THIS fold's saturation
				let res = probe_catching(|| {
					zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,
						CS1,CS2,CS1E,S>(
						0, &sub_main, scan_files.clone(), report, true,
						cache_dir, &sub_dfa, &sub_ised, &sub_ised_igc, mw,
						//this fn runs its OWN tuner + bump loop around the
						//driver, so the driver must not tune again.
						&cs_caps, false, DcMode::Off);
					Ok(())
				});
				match res {
					Ok(Ok(())) => break,                 // fold passed
					Ok(Err(errs)) => {                   // 0-word CapErr -> bump
						let (changed, unmapped) =
							apply_caperr_bumps(&mut p, true, &errs);
						tries += 1;
						utils::logger::emit_stdout(format!(
							"[scale_dlp] count={}: 0-word bump try {}: {:?}",
							cnt, tries, errs));
						assert!(changed && unmapped.is_empty(),
							"scale_dlp count={}: 0-word finalize stuck \
							 (unmapped={:?}): {:?}", cnt, unmapped, errs);
						assert!(tries <= 30,
							"scale_dlp count={}: >30 0-word bumps", cnt);
					}
					Err(msg) => panic!(
						"scale_dlp count={}: non-CapErr fold panic (HARD STOP): \
						 {}", cnt, msg),
				}
			}
			get_global_config().b_estimate_caps = true;  // restore for next subset
			// Forward-queue saturation for THIS fold (for verification; NOT
			// plotted). saturation = max fill / matched cap (exact, no recon).
			let (fc, fcc) = (utils::consts::get_fwd(false),
				utils::consts::get_fwd_cap(false).max(1));
			let (fi, fic) = (utils::consts::get_fwd(true),
				utils::consts::get_fwd_cap(true).max(1));
			utils::logger::emit_stdout(format!(
				"[scale_dlp] count={}: FWD-QUEUE SATURATION cs={:.1}% ({}/{}) \
				 igc={:.1}% ({}/{})", cnt,
				100.0 * fc as f32 / fcc as f32, fc, fcc,
				100.0 * fi as f32 / fic as f32, fi, fic));

			utils::logger::flush_logger();
			utils::logger::emit_stdout(format!(
				"==== SCALE ROUND END count={} ====", cnt));
			utils::logger::flush_logger();
		}
	}

	#[test]
	pub fn test_collect_scale_dlp() {
		// SMOKE TEST: two layers [1, 4]. Full sweep later: 1, 10%..100% of 9,860.
		// Full sweep: 1 rule, then 10%..100% of the 9,860 sweepable DLP rules
		// (rounded). Mirrors test_collect_scale_data (ClamAV) for a matching
		// x-axis. = [1, 986, 1972, 2958, 3944, 4930, 5916, 6902, 7888, 8874, 9860].
		let n_rules = 9860usize;
		let mut counts: Vec<usize> = vec![1];
		for p in 1..=10 { counts.push((p * n_rules + 5) / 10); }
		println!("collect_scale_data_dlp: counts={:?}", counts);
		collect_scale_data_dlp(counts);
	}

	/// Experiment: is the accept-vs-fold discharge gap the (max_word_len,
	/// seg_word_len) SEGMENTATION (same function both sides)? Re-discharge
	/// ZKR_CMP_LIST on the compressed DB at the fold's (mw,mw) vs the accept
	/// shape (1, seg) for seg in {mw, whole-file}, bucket is_fail/is_success.
	#[test]
	pub fn dlp_discharge_seg_compare(){
		use data_processor::clamav::quick_discharge_file_by_crit_bag_pm;
		use data_processor::discharge_prover::quick_discharge_file;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = true;
		get_global_config().b_read_cache = true;
		get_global_config().b_estimate_caps = false;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		let min_pm = std::env::var("ZKR_MIN_PM").ok()
			.and_then(|s| s.parse().ok()).unwrap_or(3usize);
		get_global_config().clamav_cfg.min_pm_word_len = min_pm;
		println!("ZKR_MIN_PM (min_pm_word_len) = {}", min_pm);
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		let list = std::env::var("ZKR_CMP_LIST").expect("set ZKR_CMP_LIST");
		let files = utils::os::read_lines(&list);
		let id2name: std::collections::HashMap<usize, String> =
			db.sig_to_id.iter().map(|(k, v)| (*v, k.clone())).collect();
		let big = 1_000_000usize;
		let (mut fold_ok, mut acc64_clean, mut accbig_clean) = (0, 0, 0);
		let (mut gap, mut truematch, mut skip) = (0, 0, 0);
		let mut ex = vec![];
		for f in &files {
			let nib = utils::os::read_nibbles(&format!("{}/{}", proot, f));
			if nib.len() < 2 { skip += 1; continue; }
			let (fi, rec) = quick_discharge_file_by_crit_bag_pm(
				f, &nib, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, mw, mw);
			let fold = rec.is_success() && !fi.is_fail();
			let a64 = !quick_discharge_file(f, &db, &cfg, 1, mw).is_fail();
			let abig = !quick_discharge_file(f, &db, &cfg, 1, big).is_fail();
			if fold { fold_ok += 1; }
			if a64 { acc64_clean += 1; }
			if abig { accbig_clean += 1; }
			if !fold && abig { gap += 1; }
			if !fold && !abig { truematch += 1;
				if ex.len() < 12 {
					let names: Vec<String> = rec.vec_ised_sigs.iter()
						.map(|id| id2name.get(id).cloned()
							.unwrap_or(format!("id{}", id))).collect();
					ex.push((f.clone(), names)); } }
		}
		println!("=== discharge seg compare: {} files ({} skipped) ===",
			files.len(), skip);
		println!("fold (mw={},seg={}) is_success & !is_fail : {}",
			mw, mw, fold_ok);
		println!("accept-shape (mw=1, seg={})   !is_fail   : {}",
			mw, acc64_clean);
		println!("accept-shape (mw=1, whole)    !is_fail   : {}",
			accbig_clean);
		println!("-> GAP (fold-fail BUT whole-clean) : {}  [SEGMENTATION]",
			gap);
		println!("-> TRUE-MATCH (fold-fail & whole-fail): {} [DB/real]",
			truematch);
		println!("-- TRUE-MATCH examples (matched SIT under compressed DB) --");
		for (f, names) in &ex {
			println!("  {}\n     -> {:?}", f, names);
		}
	}

	// --- corpus generation: paths (all proot-relative) ---------------
	const RULES_SRC: &str =
		"data/src_sig/ms_dlp/regex_bora_international/main_full.dat";
	const RULES_DST: &str = "data/paper_data/dlp/cfg/regex_pat/\
		main_data_dlp_internationl.dat";
	const CLEAN_TGZ: &str = "data/src_sig/ms_dlp/docs/\
		clean_email_list_email_regex_zombie_international.txt.tgz";
	const CLEAN_NAME: &str =
		"clean_email_list_email_regex_zombie_international.txt";
	const CORPUS_DIR: &str = "data/paper_data/dlp/cfg/corpus";
	const JOBS_DIR: &str = "data/paper_data/dlp/cfg/jobs";
	const RAW_ENRON: &str = "data/samples/email";
	const CFG_DIR: &str = "data/paper_data/dlp/cfg";

	/// Copy the freshly generated BORA international rule DB into the DLP
	/// config tree as the discharge sig file. Returns sig-line count.
	fn compile_dlp_rules(proot: &str) -> usize {
		let src = format!("{}/{}", proot, RULES_SRC);
		let dst = format!("{}/{}", proot, RULES_DST);
		std::fs::copy(&src, &dst)
			.unwrap_or_else(|e| panic!("copy {} -> {}: {}",
				src, dst, e));
		let n = utils::os::read_lines(&dst).len();
		println!("[corpus] compiled rules -> {} ({} sigs)",
			RULES_DST, n);
		n
	}

	/// Extract the one-file clean-list .tgz into /tmp; return its path.
	/// Caller removes it when done.
	fn extract_clean_list(proot: &str) -> String {
		let tgz = format!("{}/{}", proot, CLEAN_TGZ);
		let st = std::process::Command::new("tar")
			.args(["-xzf", &tgz, "-C", "/tmp"]).status()
			.expect("spawn tar -xzf");
		assert!(st.success(), "tar -xzf {} failed", tgz);
		format!("/tmp/{}", CLEAN_NAME)
	}

	/// Read the clean-email list (paths relative to data/samples/email)
	/// and normalize to proot-relative paths the discharge can read.
	fn load_email_list(list_path: &str) -> Vec<String> {
		utils::os::read_lines(list_path).iter().map(|l| l.trim())
			.filter(|l| !l.is_empty() && !l.starts_with('#'))
			.map(|l| if l.starts_with("data/") { l.to_string() }
				else { format!("{}/{}", RAW_ENRON, l) })
			.collect()
	}

	/// gzip-tar `names` (files/dirs under parent_rel) into out_rel.
	/// All args proot-relative; out gets the proot prefix.
	fn tar_czf(proot: &str, out_rel: &str, parent_rel: &str,
		names: &[&str]) {
		let out = format!("{}/{}", proot, out_rel);
		let parent = format!("{}/{}", proot, parent_rel);
		let mut args: Vec<&str> = vec!["-czf", &out, "-C", &parent];
		args.extend_from_slice(names);
		let st = std::process::Command::new("tar").args(&args)
			.status().expect("spawn tar -czf");
		assert!(st.success(), "tar -czf {} ({}) failed",
			out_rel, parent_rel);
	}

	/// (file count, total bytes) under an absolute dir, recursive.
	fn dir_stats(dir: &str) -> (usize, u64) {
		let (mut n, mut sz) = (0usize, 0u64);
		let mut stack = vec![std::path::PathBuf::from(dir)];
		while let Some(d) = stack.pop() {
			let rd = match std::fs::read_dir(&d) {
				Ok(r) => r, Err(_) => continue };
			for ent in rd.flatten() {
				let p = ent.path();
				if p.is_dir() { stack.push(p); }
				else if let Ok(m) = ent.metadata() {
					n += 1; sz += m.len();
				}
			}
		}
		(n, sz)
	}

	/// Build the corpus.stat body from the screening funnel counts.
	/// r0..r3 = (files, bytes) RETAINED after each stage (r0 = raw).
	/// Step 1 = regex selectivity (% vs raw); steps 2-3 = approximation
	/// loss, so their %/baseline is step 1's outcome r1, not raw.
	fn corpus_readme_body(r0: (usize,u64), r1: (usize,u64),
		r2: (usize,u64), r3: (usize,u64),
		needs_cut: usize) -> Vec<String> {
		let mb = |b: u64| b as f64 / 1e6;
		let pn = |a: usize, b: usize| if b==0 {0.0}
			else {100.0*a as f64/b as f64};
		let pb = |a: u64, b: u64| if b==0 {0.0}
			else {100.0*a as f64/b as f64};
		let dc = |b:(usize,u64), a:(usize,u64)|
			(b.0.saturating_sub(a.0), b.1.saturating_sub(a.1));
		//retained line, percentages vs base (bn files, bb bytes, lbl)
		let ret = |r:(usize,u64), bn:usize, bb:u64, lbl:&str| format!(
			"        retained {} files ({:.2}% {}), {:.0} MB \
			({:.2}%)", r.0, pn(r.0,bn), lbl, mb(r.1), pb(r.1,bb));
		let drp = |b:(usize,u64), a:(usize,u64), bn:usize, bb:u64| {
			let (c,s) = dc(b,a);
			format!("        dropped  {} files ({:.2}%), {:.0} MB \
			({:.2}%)", c, pn(c,bn), mb(s), pb(s,bb)) };
		vec![
		"screened Enron corpus -- final_enron_list.txt.tgz".to_string(),
		"Generated by gen_email_corpus_for_full_dlp() in \
			zkregplus/src/zkp_driver.rs.".to_string(),
		String::new(),
		"step 1 % vs raw (regex selectivity); steps 2-3 % vs step 1 \
			(approximation loss)".to_string(),
		format!("  0. raw maildir   {}", RAW_ENRON),
		ret(r0, r0.0, r0.1, "raw"),
		"  1. Zombie RE2 screen (eval_dlp.py): emails marked clean"
			.to_string(),
		drp(r0, r1, r0.0, r0.1), ret(r1, r0.0, r0.1, "raw"),
		"  2. BORA discharge (main_data_dlp_internationl.dat)"
			.to_string(),
		drp(r1, r2, r1.0, r1.1), ret(r2, r1.0, r1.1, "step1"),
		format!("  3. high-NEEDS prune (max-chunk NEEDS > {})",
			needs_cut),
		drp(r2, r3, r1.0, r1.1), ret(r3, r1.0, r1.1, "step1"),
		"  final  cfg/jobs/final_enron_list.txt.tgz".to_string(),
		format!("        {} files, {:.0} MB = {:.2}% files / {:.2}% \
			size of step1", r3.0, mb(r3.1), pn(r3.0,r1.0),
			pb(r3.1,r1.1)),
		]
	}

	/// Build the screened Enron corpus for the full DLP run. Compiles the
	/// BORA international rules, discharges the Zombie-clean email list in
	/// ONE aggressive pass (yields pass/fail AND per-file NEEDS), prunes
	/// NEEDS>4000, packs the final list, and writes the funnel to README.
	#[test]
	fn gen_email_corpus_for_full_dlp() {
		use rayon::prelude::*;
		let proot = utils::os::proj_root();
		let mw = 64; //chunk_len for the real DLP dataset
		//ZKR_CORPUS_NEEDS_CUT overrides the high-cost prune threshold (default
		//4000); the final list keeps foldable emails with max-NEEDS <= this.
		let needs_cut = std::env::var("ZKR_CORPUS_NEEDS_CUT").ok()
			.and_then(|s| s.parse().ok()).unwrap_or(4000usize);
		get_global_config().range2_bit = 25;
		//rules recompiled -> rebuild by default; ZKR_CORPUS_CACHE=1
		//reuses the dlp_corpus_aggr cache for fast reruns/diagnostics.
		let b_cache = std::env::var("ZKR_CORPUS_CACHE").is_ok();
		//ZKR_CORPUS_CACHE_NAME overrides the DB cache (default dlp_corpus_aggr,
		//the 39GB fanout DB). Point it at the experiment's dlp_intl_data_aggr
		//(18GB) for a RAM-safe, experiment-consistent split.
		let cache_name = std::env::var("ZKR_CORPUS_CACHE_NAME")
			.unwrap_or_else(|_| "dlp_corpus_aggr".to_string());
		get_global_config().b_read_cache = b_cache;
		get_global_config().b_estimate_caps = false;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;

		// 1. compile rules; 2. extract the Zombie-clean list to /tmp
		compile_dlp_rules(&proot);
		let list_tmp = extract_clean_list(&proot);
		let files = load_email_list(&list_tmp);
		let n_stage1 = files.len();
		println!("[corpus] stage1 zombie-clean: {} emails", n_stage1);

		// 3. build the aggressive DB once over the compiled rules
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, RULES_DST,
			&format!("{}/regex_pat/main_dfa.dat", CFG_DIR),
			&format!("{}/regex_pat/needs_ised.dat", CFG_DIR),
			&format!("{}/regex_pat/needs_ised_igc.dat", CFG_DIR),
			&mut vlog, &cache_name, b_cache, true)
			.expect("build db");

		// 4. ONE discharge pass -> (fname, is_fail, max_needs, size).
		let recs: Vec<(String, bool, usize, u64)> = files.par_iter()
			.map(|f| {
				let sz = std::fs::metadata(
					format!("{}/{}", proot, f))
					.map(|m| m.len()).unwrap_or(0);
				match crate::needs_dist::discharge_one(
					f, &proot, &db, &cfg, mw) {
				Some(fdr) => (f.clone(), fdr.is_fail(),
					fdr.chunk_peaks.needs_per_chunk.iter()
						.copied().max().unwrap_or(0), sz),
				None => (f.clone(), false, 0, sz),
			}}).collect();

		// 5. split + prune. passed = discharged; final = passed minus
		// the high-NEEDS (too costly to fold) emails.
		let passed: Vec<String> = recs.iter().filter(|r| !r.1)
			.map(|r| r.0.clone()).collect();
		let failed: Vec<String> = recs.iter().filter(|r| r.1)
			.map(|r| r.0.clone()).collect();
		let high: Vec<String> = recs.iter()
			.filter(|r| !r.1 && r.2 > needs_cut)
			.map(|r| r.0.clone()).collect();
		let final_list: Vec<String> = recs.iter()
			.filter(|r| !r.1 && r.2 <= needs_cut)
			.map(|r| r.0.clone()).collect();
		let _ = std::fs::create_dir_all(
			format!("{}/{}", proot, CORPUS_DIR)); //recreated each run
		utils::os::write_lines(
			&format!("{}/passed_clean_email.txt", CORPUS_DIR),
			&passed, true);
		utils::os::write_lines(
			&format!("{}/failed_clean_email.txt", CORPUS_DIR),
			&failed, true);
		utils::os::write_lines(
			&format!("{}/high_cost_email_removed.txt", CORPUS_DIR),
			&high, true);

		// 6. final list -> jobs/final_enron_list.txt.tgz (drop .txt)
		utils::os::write_lines(
			&format!("{}/final_enron_list.txt", JOBS_DIR),
			&final_list, true);
		tar_czf(&proot, &format!("{}/final_enron_list.txt.tgz",
			JOBS_DIR), JOBS_DIR, &["final_enron_list.txt"]);
		let _ = std::fs::remove_file(format!(
			"{}/{}/final_enron_list.txt", proot, JOBS_DIR));

		// 7. pack the 3 generated lists into corpus.tgz, then drop
		// the corpus/ dir (the .tgz is the only retained copy).
		tar_czf(&proot, "data/paper_data/dlp/cfg/corpus.tgz",
			CORPUS_DIR, &["passed_clean_email.txt",
			"failed_clean_email.txt",
			"high_cost_email_removed.txt"]);
		let _ = std::fs::remove_dir_all(
			format!("{}/{}", proot, CORPUS_DIR));

		// 8. measured funnel -> corpus.stat; cleanup the /tmp list.
		// retained (files,bytes) after each stage; bytes summed from
		// the per-file stat captured during discharge.
		let (raw_n, raw_sz) =
			dir_stats(&format!("{}/{}", proot, RAW_ENRON));
		let sz_stage1: u64 = recs.iter().map(|r| r.3).sum();
		let sz_passed: u64 = recs.iter().filter(|r| !r.1)
			.map(|r| r.3).sum();
		let sz_final: u64 = recs.iter()
			.filter(|r| !r.1 && r.2 <= needs_cut).map(|r| r.3).sum();
		let body = corpus_readme_body(
			(raw_n, raw_sz), (n_stage1, sz_stage1),
			(passed.len(), sz_passed),
			(final_list.len(), sz_final), needs_cut);
		//funnel snapshot under the DLP config dir
		utils::os::write_lines(
			"data/paper_data/dlp/cfg/corpus.stat", &body, true);
		let _ = std::fs::remove_file(&list_tmp);
		println!("[corpus] DONE raw={} stage1={} passed={} \
failed={} high={} final={}", raw_n, n_stage1, passed.len(),
			failed.len(), high.len(), final_list.len());
	}

	/// DEBUG USE 62060: standalone non-ZK NEEDS pre-pass. Prints
	/// per-file max_needs_subsigs (the estimator input) so it can be
	/// compared against the QM_SUB_SAT gauge peak. Writes no files.
	/// Defaults to the small_debug corpus; ZKR_CFG/ZKR_SIG/ZKR_SCAN/
	/// ZKR_CHUNK/ZKR_RANGE2 retarget it.
	#[test]
	pub fn test_needs_prepass(){
		let proot = utils::os::proj_root();
		let cd = std::env::var("ZKR_CFG").unwrap_or(
			"data/debug/small_email/config".to_string());
		let sig = std::env::var("ZKR_SIG")
			.unwrap_or("main.dat".to_string());
		let scan = std::env::var("ZKR_SCAN")
			.unwrap_or("binexec.dat".to_string());
		let mw = knob("ZKR_CHUNK", 256);
		get_global_config().range2_bit = knob("ZKR_RANGE2", 20);
		get_global_config().b_read_cache = false;
		get_global_config().b_estimate_caps = false;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let cfg = read_global_config().clamav_cfg.clone();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, sig),
			&format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), &mut vlog,
			"needs_prepass", false, false).expect("build db");
		let raw = utils::os::read_lines(
			&format!("{}/{}/{}", proot, cd, scan));
		let files: Vec<String> = raw.iter().map(|l| l.trim())
			.filter(|l| !l.is_empty() && !l.starts_with('#'))
			.map(|l| l.to_string()).collect();
		let mut peak = 0usize;
		for rel in &files{
			let nibbles = utils::os::read_nibbles(
				&format!("{}/{}", proot, rel));
			let (fdr, _w) =
			 data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
				rel, &nibbles, &db.vec_sigs,
				&db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, mw, mw);
			let n = fdr.chunk_peaks.max_needs_subsigs;
			if n > peak { peak = n; }
			println!("DEBUG USE 62060.1: NEEDS={} nchunks={} {}",
				n, fdr.chunk_peaks.needs_per_chunk.len(), rel);
		}
		println!("DEBUG USE 62060.2: files={} PEAK_NEEDS={}",
			files.len(), peak);
	}

	/// NEEDS-distribution study over the full Enron clean list (parallel,
	/// lean: keeps only per-chunk needs vectors, not full records). Loads
	/// the aggressive DB, normalizes rc.scan_file (proot-relative list,
	/// '#'/blank lines dropped, base "data/samples/email" prepended), then
	/// prints the distribution. No tuning, no folding.
	#[test]
	pub fn full_enron_needs_dist(){
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_read_cache = true;
		get_global_config().b_estimate_caps = false; //NEEDS doesn't need it
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		let base = "data/samples/email";
		let raw = utils::os::read_lines(
			&format!("{}/{}", proot, rc.scan_file));
		let files: Vec<String> = raw.iter().map(|l| l.trim())
			.filter(|l| !l.is_empty() && !l.starts_with('#'))
			.map(|l| if l.starts_with("data/") { l.to_string() }
				else { format!("{}/{}", base, l) }).collect();
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"[needs_dist] list={} kept={} (raw={})",
			rc.scan_file, files.len(), raw.len()));
		crate::needs_dist::print_needs_distribution::<Fr>(
			&files, &proot, &db, &cfg, mw,
			"data/paper_data/dlp/report/needs_dist_report.txt");
	}

	/// EXPERIMENT: real r1cs/cs1e at the corpus max NEEDS (~14200) and whether
	/// the full SNARK (decider) fits 125GB. Estimates the aggressive config
	/// from the densest corpus files, then folds a SHORT high-NEEDS file under
	/// that (cap-driven) config -- cs1e equals the 14200-config circuit but
	/// reached in ~3 steps not 111. ZKR_EXP_DECIDER=1 => run the Groth16
	/// decider (full SNARK); else Phase-1 folding only. cs1e logs at step 0.
	#[test]
	pub fn full_enron_max_needs_cost(){
		use crate::determine_config::caps_from_params_aggr;
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = true;
		//decider (full SNARK) iff ZKR_EXP_DECIDER set; else fold-only.
		get_global_config().b_folding_only =
			std::env::var("ZKR_EXP_DECIDER").is_err();
		get_global_config().b_read_cache = true;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_estimate_caps = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", cd, rc.sig_file),
			&format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		//densest corpus files (NEEDS up to 14200) + the short fold file ->
		//estimate the config so it COVERS the fold file (no CapErr).
		let base = "data/samples/email";
		let fold_rel = std::env::var("ZKR_EXP_FOLDFILE").unwrap_or(
			"src/maildir/taylor-m/inbox/137.".to_string());
		let seed = ["src/maildir/dasovich-j/all_documents/8681.".to_string(),
			"src/maildir/dasovich-j/notes_inbox/5594.".to_string(),
			fold_rel.clone()];
		let mut vdata = vec![];
		for rel in &seed{
			let fpath = format!("{}/{}", base, rel);
			let nibbles = utils::os::read_nibbles(
				&format!("{}/{}", proot, fpath));
			let (fdr, _r) =
				data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
				&fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, mw, mw);
			utils::logger::log(0, utils::logger::LOG1, &format!(
				"[exp] seed {} NEEDS={}", rel,
				fdr.chunk_peaks.max_needs_subsigs));
			vdata.push(fdr);
		}
		let est = estimate_config_aggr::<Fr>(&vdata, &db, &[100], &mut vlog);
		let mut p = estimated_to_capparams_aggr(&est[0], mw, rc.range2_bit, 3);
		//estimator mins the IGC arm (aggressive collapses igc subsigs), but
		//the igc discharge gadget still must cover the fold file's igc DFA
		//diversity (CapErr basis_unique_states_igc). Lift igc structural caps
		//to the cs arm so the build succeeds; NEEDS-driven cost is unchanged.
		p.basis_unique_states_igc = p.basis_unique_states_igc
			.max(p.basis_unique_states);
		p.basis_acc_states_igc = p.basis_acc_states_igc
			.max(p.basis_acc_states);
		p.basis_pats_in_trace_igc = p.basis_pats_in_trace_igc
			.max(p.basis_pats_in_trace);
		//ZKR_EXP_PERC clamps the StepFwdPrf buffer (perc) so the circuit can
		//synthesize in 125GB -- yields a cs1e LOWER BOUND for this subsigs
		//universe; the real perc (logged above) makes the true circuit bigger.
		if let Ok(s) = std::env::var("ZKR_EXP_PERC"){
			if let Ok(v) = s.parse::<usize>(){
				p.perc_pats_expansion_rate = v;
				p.perc_pats_expansion_rate_igc = v.min(64).max(2);
			}
		}
		//ZKR_EXP_NEEDS clamps the SED universe (aggr_needs + subsigs) to map
		//the cs1e(NEEDS) curve and locate the 125GB synthesis ceiling.
		if let Ok(s) = std::env::var("ZKR_EXP_NEEDS"){
			if let Ok(v) = s.parse::<usize>(){
				p.aggr_needs_subsigs = v;
				p.subsigs = v + 1;
			}
		}
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"[exp] NEEDS~14200 config: aggr_needs_subsigs={} subsigs={} \
			 basis_unique_states={} basis_pats_in_trace={} \
			 perc_pats_expansion_rate={} cp_subsigs={}",
			p.aggr_needs_subsigs, p.subsigs, p.basis_unique_states,
			p.basis_pats_in_trace, p.perc_pats_expansion_rate, p.cp_subsigs));
		let _ = p.save_json(&format!("{}/{}/exp_config_needs14200.json",
			proot, cd));
		drop(db); //fold driver loads its own DB copy
		get_global_config().b_estimate_caps = false;
		get_global_config().aggr_needs_subsigs = p.aggr_needs_subsigs;
		let cs_caps = vec![caps_from_params_aggr(&p)];
		let manifest = format!("{}/exp_fold_manifest.dat", cd);
		let _ = std::fs::write(&format!("{}/{}", proot, manifest),
			format!("{}/{}\n", base, fold_rel));
		let report = format!("{}/exp_max_needs_report.txt", cd);
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"[exp] folding {} (decider={})", fold_rel,
			!get_global_config().b_folding_only));
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), vec![manifest], &report,
			false, &rc.cache_dir, &format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), mw, &cs_caps,
			false, DcMode::Off); //config-file caps: no auto-tune
	}

	/// full_enron: read the C_low/C_high configs produced by determine_config
	/// (a ZKR_DLP_DETERMINE_ONLY run) and FOLD the scan manifest over the
	/// 2-tier ladder -- NO tuning. Sibling of full_clam but config-file-driven:
	/// run determine_config once on the 500k workload, then point this at the
	/// resulting C1/C2 jsons (RunCfg.config_c1/c2) to prove.
	#[test]
	pub fn full_enron(){
		use crate::determine_config::{caps_from_params_aggr, CapParams};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = true;
		get_global_config().b_folding_only = true;
		get_global_config().b_read_cache = true;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_estimate_caps = false;
		get_global_config().perc_lkup_share = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		//M11: the per-chunk rung ladder (cheapest-first) written by sample3.
		let ladder = crate::determine_config::load_ladder(
			&format!("{}/{}", proot, rc.config_ladder));
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"full_enron: loaded {}-rung ladder", ladder.len()));
		get_global_config().aggr_needs_subsigs =
			ladder.first().map(|c| c.aggr_needs_subsigs).unwrap_or(0);
		let cs_caps: Vec<_> = ladder.iter().map(caps_from_params_aggr).collect();
		let scan = vec![format!("{}/{}", cd, rc.scan_file)];
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), scan, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/regex_pat/main_dfa.dat", cd),
			&format!("{}/regex_pat/needs_ised.dat", cd),
			&format!("{}/regex_pat/needs_ised_igc.dat", cd), mw, &cs_caps,
			false, DcMode::Off); //config-file caps: no auto-tune
	}

	/// Invoke via:
	/// `cargo test -p zkregplus -- test_db_bundle --show-output --nocapture`
	/// BASELINE 2026-05-31 (b_cache=false, b_quick=true; pre-ApproxConfig
	///   ->GlobalConfig refactor; test bin):
	///   debug_config (range_bits=26): wall=577s(9:36), RAM_peak=46.1GB
	///   dna/config   (range_bits=27): wall=112s(1:52), RAM_peak=26.3GB
	#[test]
	pub fn test_db_bundle(){
		let b_cache = false;
		let b_quick = true;
		/*
		let range_bits = 26;
		super::run_db_bundle::<Fr>(
			"data/paper_data/debug_config", //config dir
			"data/paper_data/reports", //report dir
			b_cache, b_quick, range_bits, "main.dat");
		*/

		//small_email2 cap estimator: matches the small_email2 runner
		//(range2_bit=25, max_word=256, aggressive SDE-rep fan-out) on
		//the FULL MS DLP set. dfa_sigs/dfa_subsigs in the report are
		//unreliable here - treat as 0 and seed caps from FSM/SED cols.
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep
			= true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = 100;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		//Tight first-leg mode: 2 adj pins at first leg + 1 pin
		//Distributed-pin mode: pins spread across legs (priority
		//1st, last, middles R->L), within-leg ascending order.
		get_global_config().clamav_cfg
			.b_sde_rep_tight_first_leg = false;
		let range_bits_email = 25;
		let max_word_len_email = 256;
		let percentiles_email = [20usize, 50, 100];
		//Scan binexec3.dat (the most challenging clean emails) so the
		//estimate reflects small_email3's targets, and WRITE the DB to
		//the shared "email_data" cache (same main_full.dat/range2_bit=25/
		//fanout as small_email2/3) so small_email3 can read it (no
		//rebuild). b_cache=false here => build fresh + write cache.
		super::run_db_bundle::<Fr>(
			"data/debug/small_email/config", //config dir
			"data/debug/small_email/reports", //report dir
			b_cache, true, b_quick, range_bits_email,
			max_word_len_email, &percentiles_email,
			"main_full.dat", //full MS DLP set
			"binexec3.dat", //scan: challenging clean emails
			"email_data"); //write DB cache (shared w/ small_email2/3)

		/*
		let range_bits = 27;
		// max_word_len=2048 reproduces the baseline seg_size
		// (2048*62 == 62*512*4), so the report stays byte-identical.
		let max_word_len = 2048;
		let percentiles = [20usize, 50, 100];
		super::run_db_bundle::<Fr>(
			"data/paper_data/dna/config", //config dir
			"data/paper_data/dna/reports", //report dir
			b_cache, b_quick, range_bits,
			max_word_len, &percentiles, "main.dat");
		*/
	}

	/// ZK discharge of the full clean chr17 sample (light-test,
	/// single job). HEAVY — expect hours / large RAM. Invoke via:
	/// `cargo test -p zkregplus -- test_full_dna --show-output --nocapture`
	#[test]
	pub fn test_full_dna(){
		full_dna::<Fr>(false);
	}

	/// full_clamav 8-job run (one full-mode proof). Reads the snark
	/// cache, self-building it on first run. Invoke via run_full_clam.py
	/// or: `cargo test -p zkregplus -- full_clam --exact --nocapture`
	#[test]
	pub fn full_clam(){
		let read_mode = match std::env::var("ZKR_CLAM_READ_MODE")
			.as_deref() {
			Ok("first") => ClamReadMode::FirstHalf,
			Ok("second") => ClamReadMode::SecondHalf,
			_ => ClamReadMode::Full,
		};
		let read_pct = std::env::var("ZKR_CLAM_PCT").ok()
			.and_then(|s| s.parse().ok()).unwrap_or(100);
		full_clamav::<Fr>(true, false, false, read_mode, read_pct);
	}

	/// Report the AC-DFA accepting-state density rho (perc_acc) over the
	/// FULL ClamAV corpus, reusing full_clam()'s DB cache ("full_data") and
	/// its binexec_p0..p7 scan manifests. Stats-only (b_quick => discharge
	/// classifier, NO ZK circuit), so it is cheap relative to full_clam.
	/// run_db_bundle -> report_all_discharge_approach_stats ->
	/// print_discharge_stats emits "acc_states/path_len: avg: X%, max: Y%"
	/// (= rho) to stdout. Capture and parse via:
	///   cargo test --lib --release -- test_acc_state_rate \
	///     --show-output --nocapture 2>&1 \
	///     | tee <paper>/data/raw_data/any_server/dump_acc_state_ratio.txt
	///   python3 <paper>/data/scripts/eval/extract_acc_state_rate.py
	fn report_acc_state_rate<F:PrimeField>(){
		utils::os::print_computer_config(Some("report_acc_state_rate"));
		println!("######## ACC-STATE-RATE DUMP (full_clam DB 'full_data', \
binexec_p0..p7; via report_acc_state_rate -> run_db_bundle) ########");
		// Match full_clam's DB-affecting settings so the cached DB loads
		// identically (these floors are harmless on the stats-only path).
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().perc_lkup_share = 143;
		get_global_config().log_level = utils::logger::LOG3;

		let set1 = "data/paper_data/clamav/config";
		let proot = utils::os::proj_root();
		// run_db_bundle reads ONE scan manifest, but full_clam (Full mode)
		// splits the corpus across binexec_p0..p7.dat -> concatenate them
		// into one combined list under the config dir.
		let mut all: Vec<String> = vec![];
		for i in 0..8 {
			all.extend(utils::os::read_lines(
				&format!("{}/{}/binexec_p{}.dat", proot, set1, i)));
		}
		let combined = "binexec_acc_all.dat";
		// write_lines prepends proj_root() internally, so pass a
		// proot-relative path (read_lines above takes the path as-is).
		utils::os::write_lines(
			&format!("{}/{}", set1, combined), &all, true);
		println!("acc-rate scan: {} corpus files across binexec_p0..p7",
			all.len());

		// b_cache=true reads full_clam's "full_data" DB (no rebuild);
		// b_quick=true = discharge classifier only (no ZK circuit).
		super::run_db_bundle::<F>(
			set1,                              // config_dir
			"data/paper_data/clamav/reports",  // report_dir
			true,   // b_cache (read DB cache)
			false,  // b_write_cache
			true,   // b_quick (stats-only)
			26,     // range_bits
			512 * 8,// max_word_len (chunk len; = full_clam)
			&[100usize],           // percentiles (estimator tail only)
			"main.dat",            // sig_file_name
			combined,              // scan_file_name (combined 8 jobs)
			"full_data",           // cache_dir (full_clam DB)
		);
	}

	/// See report_acc_state_rate. Invoke via:
	/// `cargo test -p zkregplus --release -- test_acc_state_rate \
	///   --exact --nocapture`
	#[test]
	pub fn test_acc_state_rate(){
		report_acc_state_rate::<Fr>();
	}

	/// M2: emit singleton-distance corpus stat B (+ nu) per dataset. B =
	/// max nibble-distance from a pattern to its closest downstream
	/// singleton; feeds apdx_sde c = ceil(B/chunklen)+1. Loads each
	/// authoritative cached DB (no rebuild) and maxes max_dist_and_nu over
	/// its cs+igc SED stores. Parsed by extract_acc_state_rate.py. Invoke:
	///   cargo test -p zkregplus --release -- report_singleton_dist \
	///     --exact --nocapture | tee data/.../dump_singleton_dist.txt
	#[test]
	fn report_singleton_dist() {
		use data_processor::clam_db::ClamavDB;
		let emit = |ds: &str, db: &ClamavDB<Fr>, rb: usize| {
			let (mut b, mut nu) = (0usize, 0usize);
			for st in db.bundle_subsig.vec_subsig_step_stores.iter()
				.chain(db.bundle_subsig_igc.vec_subsig_step_stores.iter()) {
				let (sb, sn) = st.max_dist_and_nu();
				b = b.max(sb); nu = nu.max(sn);
			}
			println!("SDE-SINGLETON-DIST: {} B_nibbles={} nu_max={} \
range2_bit={}", ds, b, nu, rb);
		};
		let load = |dir: &str, cache: &str| {
			get_global_config().clamav_cfg.b_aggressive_sde_for_rep = false;
			let cfg = data_processor::clamav::default_clamav_cfg();
			let mut vlog = vec![];
			ClamavDB::<Fr>::build_or_load(&cfg,
				&format!("{}/main.dat", dir),
				&format!("{}/main_dfa.dat", dir),
				&format!("{}/needs_ised.dat", dir),
				&format!("{}/needs_ised_igc.dat", dir),
				&mut vlog, cache, true, false).expect("load db")
		};
		// ClamAV: authoritative full_data DB (mirror report_acc_state_rate
		// floors so the cache loads identically).
		get_global_config().range2_bit = 26;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		emit("clamav",
			&load("data/paper_data/clamav/config", "full_data"), 26);
		// DNA
		get_global_config().range2_bit = 27;
		emit("dna", &load("data/paper_data/dna/config", "dna_data"), 27);
		// DLP (non-aggressive forward build; corpus-B semantics)
		get_global_config().range2_bit = 25;
		emit("dlp",
			&load("data/paper_data/dlp/cfg/regex_pat", "dlp_corpus_aggr"),
			25);
	}

	/// ZK discharge of one Enron email (merged_000001) against the
	/// Zombie-style DL proximity policy (light-test, single job).
	/// Invoke via:
	/// `cargo test -p zkregplus -- test_small_email --show-output --nocapture`
	#[test]
	pub fn test_small_email(){
		small_email::<Fr>(false);
	}

	/// small_email against a 5-arm slice of the full MS DLP set
	/// (main_full2.dat = anchor + aba-routing arms). Invoke via:
	/// `cargo test -p zkregplus -- test_small_email2 --show-output --nocapture`
	#[test]
	pub fn test_small_email2(){
		small_email2::<Fr>(false);
	}

	/// Permanent regression: multi-subsig DFA discharge combo (count>=2).
	/// Fails (assert!(verify_batch)) on the step-2.1 well-formedness bug,
	/// passes once dfa_adv.rs matches its compute_sig_adv.rs twin.
	/// `cargo test -p zkregplus --release --lib -- \
	///   zkp_driver::tests_zkp_driver::test_small_multi_dnf \
	///   --exact --nocapture`
	#[test]
	pub fn test_small_multi_dnf(){
		small_multi_dnf::<Fr>(false);
	}

	/// small_email3: full MS DLP set vs binexec3.dat (the two most
	/// challenging clean emails). Reads the shared email_data DB cache.
	/// `cargo test -p zkregplus -- test_small_email3 --show-output --nocapture`
	#[test]
	pub fn test_small_email3(){
		small_email3::<Fr>(false);
	}

	/// Full Groth16 snark on the small_data_par config, one proof only.
	/// `cargo test -p zkregplus --release -- test_small_par_full_snark \
	///   --show-output --nocapture`
	#[test]
	pub fn test_small_par_full_snark(){
		small_par_full_snark::<Fr>(false);
	}


	// ===== M2.5: estimator validation (OLD/NEW/REAL coverage) =====
	use crate::determine_config::CapParams;

	/// Per-cap OLD (pre-CP-extension) / NEW (estimator seed) / FIN
	/// (probe-finalized) / REAL (determine_config oracle). Returns true
	/// iff FIN >= REAL on every cap (the crash-proof coverage property).
	fn cmp_caps(label:&str, old:&CapParams, new:&CapParams,
		fin:&CapParams, real:&CapParams)->bool{
		let rows: [(&str,usize,usize,usize,usize);9] = [
		 ("cp_basis_unique", old.cp_basis_unique_states,
		   new.cp_basis_unique_states, fin.cp_basis_unique_states,
		   real.cp_basis_unique_states),
		 ("basis_unique", old.basis_unique_states,
		   new.basis_unique_states, fin.basis_unique_states,
		   real.basis_unique_states),
		 ("basis_acc", old.basis_acc_states, new.basis_acc_states,
		   fin.basis_acc_states, real.basis_acc_states),
		 ("basis_pats", old.basis_pats_in_trace,
		   new.basis_pats_in_trace, fin.basis_pats_in_trace,
		   real.basis_pats_in_trace),
		 ("subsigs", old.subsigs, new.subsigs, fin.subsigs, real.subsigs),
		 ("perc_pats", old.perc_pats_expansion_rate,
		   new.perc_pats_expansion_rate, fin.perc_pats_expansion_rate,
		   real.perc_pats_expansion_rate),
		 ("avg_active", old.avg_active_pats_per_subsig,
		   new.avg_active_pats_per_subsig, fin.avg_active_pats_per_subsig,
		   real.avg_active_pats_per_subsig),
		 ("aggr_needs", old.aggr_needs_subsigs, new.aggr_needs_subsigs,
		   fin.aggr_needs_subsigs, real.aggr_needs_subsigs),
		 ("cp_subsigs", old.cp_subsigs, new.cp_subsigs, fin.cp_subsigs,
		   real.cp_subsigs),
		];
		let mut all_ok = true;
		println!("== ESTIMATOR VALIDATION [{}] ==", label);
		println!("{:<16} {:>9} {:>9} {:>9} {:>9}  FINok", "cap",
			"OLD","NEW","FIN","REAL");
		for (n,o,ne,f,r) in rows.iter(){
			let ok = f>=r;
			if !ok { all_ok=false; }
			println!("{:<16} {:>9} {:>9} {:>9} {:>9}  {}", n,o,ne,f,r,
				if ok {"yes"} else {"COVERAGE-GAP"});
		}
		println!("[{}] FIN covers REAL on ALL caps: {}", label, all_ok);
		all_ok
	}

	/// Aggressive estimator validation: discharge `scan` (one pass for vdata
	/// + words + infos), build NEW via the estimator, OLD = NEW without the
	/// CP field, REAL via determine_config_aggr; print the comparison.
	fn estimator_validate_aggr(label:&str, set1:&str, sig:&str, scan:&str,
		range_bits:usize, max_word:usize, fanout:usize, cache:&str,
		real_json:&str)->bool{
		get_global_config().range2_bit = range_bits;
		get_global_config().b_light_test = true;
		get_global_config().b_read_cache = false;
		get_global_config().b_estimate_caps = true;
		get_global_config().perc_lkup_share = 1;
		get_global_config().min_subsigs = 1;
		get_global_config().min_basis_unique_states = 2;
		get_global_config().min_basis_acc_states = 2;
		get_global_config().min_basis_pats_in_trace = 4;
		get_global_config().min_avg_pats_per_subsig = 1;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
		get_global_config().clamav_cfg.sde_rep_fanout_cap = fanout;
		get_global_config().clamav_cfg.min_pm_word_len = 3;
		let proot = utils::os::proj_root();
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", set1, sig),
			&format!("{}/regex_pat/main_dfa.dat", set1),
			&format!("{}/regex_pat/needs_ised.dat", set1),
			&format!("{}/regex_pat/needs_ised_igc.dat", set1), &mut vlog,
			cache, true, true).expect("build db");
		//discharge: vdata (estimator input) + packed words + word infos
		//(finalize-probe input), one pass
		let files = utils::os::read_lines(
			&format!("{}/{}/{}", proot, set1, scan));
		let (mut vdata, mut words, mut infos) = (vec![], vec![], vec![]);
		for fpath in &files{
			let nibbles = utils::os::read_nibbles(
				&format!("{}/{}", proot, fpath));
			let f_nib: Vec<Fr> = nibbles.iter().map(|x| Fr::from(*x as u32))
				.collect();
			words.push(utils::data::pack_nibbles(&f_nib));
			let (fdr, rec) =
				data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
				fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, max_word, max_word);
			vdata.push(fdr);
			infos.push(rec);
		}
		//NEW estimate + OLD (cp field zeroed = pre-extension)
		let configs = crate::stats_helper::estimate_config_aggr::<Fr>(
			&vdata, &db, &[100], &mut vlog);
		assert!(!configs.is_empty(), "estimator produced no config");
		let c_new = crate::stats_helper::estimated_to_capparams_aggr(
			&configs[0], max_word, range_bits, 3);
		let mut c_old = c_new.clone();
		c_old.cp_basis_unique_states = 0;
		//REAL = the saved determine_config output for this scan/chunk.
		let c_real = crate::determine_config::CapParams::load_json(
			&format!("{}/{}", proot, real_json));
		//FIN = estimator seed finalized by the collect-probe
		let total_word_n: usize = words.iter().map(|w| w.len()).sum();
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let lkup_len = db.lkup.get_size();
		let db_arc = std::sync::Arc::new(db);
		let c_fin = super::finalize_caps_probe::<Fr,C1,CS1>(
			db_arc, &words, &infos, c_new.clone(), max_word, lkup_len,
			total_word_n, 60, 4, super::ShrinkMode::Precise)
			.expect("finalize failed");
		cmp_caps(label, &c_old, &c_new, &c_fin, &c_real)
	}

	/// Non-aggressive regression: with b_estimate_caps OFF, the M1 CP-peak
	/// must stay 0 (discharge byte-identical to before).
	fn estimator_regress_nonaggr(label:&str, set1:&str, sig:&str, dfa:&str,
		ised:&str, ised_igc:&str, scan:&str, max_word:usize){
		get_global_config().b_estimate_caps = false;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = false;
		get_global_config().b_read_cache = false;
		let proot = utils::os::proj_root();
		let cfg = data_processor::clamav::default_clamav_cfg();
		let mut vlog = vec![];
		let db = data_processor::clam_db::ClamavDB::<Fr>::build_or_load(
			&cfg, &format!("{}/{}", set1, sig),
			&format!("{}/{}", set1, dfa), &format!("{}/{}", set1, ised),
			&format!("{}/{}", set1, ised_igc), &mut vlog,
			&format!("regress_{}", label), false, false).expect("build db");
		let files = utils::os::read_lines(
			&format!("{}/{}/{}", proot, set1, scan));
		let mut all_zero = true;
		for fpath in &files{
			let nibbles = utils::os::read_nibbles(
				&format!("{}/{}", proot, fpath));
			let (fdr, _rec) =
				data_processor::clamav::quick_discharge_file_by_crit_bag_pm(
				fpath, &nibbles, &db.vec_sigs, &db.vec_sigs_no_critical_pat,
				&db.map_crit_pat, &db.map_crit_pat_igc, &db.dfa_crit,
				&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
				&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
				&db.sig_to_id, max_word, max_word);
			if fdr.chunk_peaks.max_cp_unique_states != 0 { all_zero = false; }
		}
		println!("[{}] flag-off max_cp_unique_states all zero: {}",
			label, all_zero);
		assert!(all_zero, "M1 gate leaked with b_estimate_caps=false");
	}

	/// `cargo test -p zkregplus -- tests_estimator_coverage --nocapture`
	#[test]
	pub fn tests_estimator_coverage(){
		estimator_regress_nonaggr("small_data",
			"data/debug/small_data_set/config_dfa", "sigs.dat", "dfa.dat",
			"ised.dat", "ised_igc.dat", "binexec.dat", 1);
		// Aggressive validation on the international DLP set sample3 uses
		// (directional fwd/bwd sigs; small_email main.dat predates that
		// shape and panics under aggressive mode). chunk_len=42 (1.3 KB).
		// REAL oracle = the saved C1/C2 (server determine_config output) at
		// max_word_len=64; rebuild the real DLP DB (dlp_intl_data_aggr,
		// what C1/C2 were tuned on) on first run, cached thereafter.
		let cd = "data/paper_data/dlp/cfg";
		let sg = "regex_pat/main_data_dlp_internationl.dat";
		let ca = "dlp_intl_data_aggr";
		// PASS CRITERION = finalize converges (every word plans under FIN),
		// gated inside estimator_validate_aggr via .expect("finalize failed").
		// The four-way OLD/NEW/FIN/REAL table is INFORMATIONAL: FIN may sit
		// below an over-provisioned REAL (determine_config overshoots the
		// multiplicative density caps) and still be a valid covering config.
		let _fin_ge_real_1 = estimator_validate_aggr("dlp_sample1", cd, sg,
			"jobs/binexec_sample1.dat", 25, 64, 100, ca,
			"data/paper_data/dlp/cfg/config/full_dlp/dlp_config_C1.json");
		let _fin_ge_real_2 = estimator_validate_aggr("dlp_sample2", cd, sg,
			"jobs/binexec_sample2.dat", 25, 64, 100, ca,
			"data/paper_data/dlp/cfg/config/full_dlp/dlp_config_C2.json");
	}

	/// M0 flag-off regression gate. Runs small_data non-aggressive with
	/// the fingerprint sink on; first run writes the baseline, later runs
	/// assert an empty structured diff.
	#[test]
	fn fingerprint_small_data_flag_off(){
		use std::sync::{Arc, Mutex};
		let b_check_lkup = true;
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = false;
		let sink = Arc::new(Mutex::new(Vec::new()));
		get_global_config().fp_sink = Some(sink.clone());
		small_data::<Fr>(b_check_lkup);
		get_global_config().fp_sink = None;
		let raw = sink.lock().unwrap().clone();
		let fp = crate::fingerprint::RunFingerprint::from_sink(&raw);
		let path = format!("{}/data/debug/small_data_set/small_data.fp",
			utils::os::proj_root());
		if !std::path::Path::new(&path).exists(){
			fp.save(&path).expect("write baseline");
			println!("[M0] baseline written: {} ({} fields)",
				path, fp.fields.len());
			return;
		}
		let base = crate::fingerprint::RunFingerprint::load(&path)
			.expect("load baseline");
		let d = fp.diff(&base);
		assert!(d.is_empty(), "flag-off fingerprint drift:\n{}",
			d.join("\n"));
		println!("[M0] flag-off fingerprint matches baseline ({} fields)",
			fp.fields.len());
	}

	/// Flag-off byte-identical guard on the small_dna circuit shape
	/// (different dims than small_data). Mirrors the small_data gate.
	#[test]
	fn fingerprint_small_dna_flag_off(){
		use std::sync::{Arc, Mutex};
		get_global_config().clamav_cfg.b_aggressive_sde_for_rep = false;
		let sink = Arc::new(Mutex::new(Vec::new()));
		get_global_config().fp_sink = Some(sink.clone());
		small_dna::<Fr>();
		get_global_config().fp_sink = None;
		let raw = sink.lock().unwrap().clone();
		let fp = crate::fingerprint::RunFingerprint::from_sink(&raw);
		let path = format!("{}/data/debug/small_dna/small_dna.fp",
			utils::os::proj_root());
		if !std::path::Path::new(&path).exists(){
			fp.save(&path).expect("write baseline");
			println!("[M2] dna baseline written: {} ({} fields)",
				path, fp.fields.len());
			return;
		}
		let base = crate::fingerprint::RunFingerprint::load(&path)
			.expect("load baseline");
		let d = fp.diff(&base);
		assert!(d.is_empty(), "flag-off dna fingerprint drift:\n{}",
			d.join("\n"));
		println!("[M2] flag-off dna fingerprint matches ({} fields)",
			fp.fields.len());
	}
}
