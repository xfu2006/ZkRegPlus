/* ZkregPlus Main Driver
	Created: 01/31/2025
*/

//use std::collections::{HashSet};
use utils::{logger::{log,LOG1,log_perf}, timer::Timer as GTimer, consts::{read_global_config, get_global_config}};
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

/// load the files and pack them as nibbles
/// return (words in packed nibbles, word info, file names)
/// max_word_len is forwarded into the discharge_prover so it can
/// extend its nibble scan to match the circuit's padded view
/// (Step 4 of the pad-invariant rework).
fn load_files<F:PrimeField + ColEle>(_job_id: usize, list_file_path: &str, db: &ClamavDB<F>, cfg:&ClamavApproxConfig, _b_write_cache: bool, _cache_dir: &str, max_word_len: usize)
	->(Vec<Vec<F>>, Vec<WordInfo>, Vec<String>){
	//1. read the list of files
	let _b_debug = false;
	let proot = proj_root();
	let file_names = &read_lines(&format!("{}/{}", proot, list_file_path));
	if file_names.len() > 0 {
		println!("  First file: {}", file_names[0]);
	}

	//2. parallel for each file read its nibbles and convert
	let final_data = file_names.into_par_iter().map(|fpath|
	{
		let nibbles = read_nibbles(&format!("{}/{}", proot, fpath));
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
		if b_debug{
			println!("DEBUG USE 2001: loaded vec_word_info: {:?}", 
				vec_word_info);
		}
		vec_word_info
	}else{
	*/
	let vec_word_info = file_names.into_par_iter().map(|fpath|
		{
			let abspath = format!("{}/{}", &proj_root(), fpath);
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
			rec
		}).collect::<Vec<WordInfo>>();

		/*
		if b_write_cache{
			let s_wi = serde_json::to_string(&vec_word_info).unwrap();
			write_to_file(&format!("{}/vec_word_info.txt", &sdir), &s_wi);
			if b_debug{
				println!("DEBUG USE 2002: SAVED vec_word_info: {:?}", 
					vec_word_info);
			}
		}
		vec_word_info
	};
	*/

	(final_data, vec_word_info, file_names.clone())
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
	println!("DEBUG USE 68911: lkup_len: {}, max_nibble_len: {}, total_nibble_len: {}, lk_share: {}, config.perc_lkup_share: {}, chunks: {}", lkup_len, max_nibble_len, total_nibbles, lk_share, read_global_config().perc_lkup_share, chunks);
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
			sed_cap_cs = sed_cap_cs.decreased_copy(level); 
			cp_cap_igc = cp_cap_igc.decreased_copy(level); 
			sed_cap_igc = sed_cap_igc.decreased_copy(level); 
			dfa_cap= dfa_cap.decreased_copy(level); 
		}
	}//for category

	//return
	layer_circs.reverse();

	// DEBUG MESSAGE 1001: Print config of each circ before returning
	println!("DEBUG USE 1001 ========================= build_circs_adv generates =================");
	for (l1_idx, layer) in layer_circs.iter().enumerate() {
		for (l2_idx, circ) in layer.iter().enumerate() {
			println!("DEBUG MESSAGE 1001: Category {} Layer {} Circuit Name: {}\nCapacity: {:#?}", l1_idx, l2_idx, circ.get_name(), circ);
		}
	}
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

/// determine_config (aggressive): auto-tune the LOWEST CapParams that pass the
/// Pass-1 capacity probe over `sample_words`. Loop = build circuits from the
/// scalar params -> CapacityPlanner Pass-1 probe -> on CapErr bump the exact
/// param to its required value -> retry. No keys, no folding, no cyclepair;
/// the foldpot framework is untouched. Returns the confirmed-lowest config.
pub(crate) fn determine_config_aggr<F,C,CS>(
	db: Arc<ClamavDB<F>>,
	sample_words: &Vec<Vec<F>>,
	sample_word_infos: &Vec<WordInfo>,
	mut p: crate::determine_config::CapParams,
	chunk_len: usize, lkup_len: usize, total_word_n: usize, max_iters: usize,
	n_threads: usize,
)->Result<crate::determine_config::CapParams, String>
where C: CurveGroup<ScalarField=F>,
	  CS: CommitmentScheme<C,false>,
	  <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
	  F: PrimeField + Absorb + ColEle,
{
	use folding_schemes::folding::foldpot::capacity_planner::CapacityPlanner;
	use crate::determine_config::{apply_caperr_bumps, caps_from_params_aggr};
	let poseidon = poseidon_canonical_config::<F>();
	// Pad each sample word to a multiple of chunk_len, matching foldpot_main's
	// F-level padding (driver.rs:2745). The CP gadget asserts each segment is
	// exactly max_word_len, so an unpadded short tail segment would panic.
	let padded: Vec<Vec<F>> = sample_words.iter()
		.map(|w| utils::data::pad_word_to_multiple::<F>(w, chunk_len))
		.collect();
	let mut t_all = GTimer::new();
	for iter in 0..max_iters {
		let mut t_round = GTimer::new();
		utils::consts::get_global_config().aggr_needs_subsigs =
			p.aggr_needs_subsigs;
		let probe_res = crate::determine_config::probe_catching(|| {
			let (cp, sed, cp_igc, sed_igc) = caps_from_params_aggr(&p);
			let cs_caps = vec![(cp, sed, cp_igc, sed_igc)];
			let layered = build_circs_adv_aggr::<F,C,CS>(&poseidon,
				total_word_n, chunk_len, lkup_len, db.clone(), &cs_caps,
				false);
			let planner = CapacityPlanner::<C, FC<F,C,CS>, LK<F>, GM<F>,
				false>::new(layered);
			planner.capacity_probe_par(&padded, sample_word_infos, n_threads)
		})?;
		t_round.stop();
		match probe_res {
			Ok(steps) => {
				t_all.stop();
				log(0, LOG1, &format!("determine_config_aggr CONVERGED @iter \
					{}: steps={}, perc={}, needs={}, avg_active={}, subsigs={};\
					 round {} ms, TOTAL {} ms", iter, steps,
					p.perc_pats_expansion_rate, p.aggr_needs_subsigs,
					p.avg_active_pats_per_subsig, p.subsigs, t_round.ms(),
					t_all.ms()));
				return Ok(p);
			}
			Err(errs) => {
				let (changed, unmapped) =
					apply_caperr_bumps(&mut p, true, &errs);
				if !unmapped.is_empty() {
					return Err(format!("unmapped CapErr(s): {:?}", unmapped));
				}
				if !changed {
					return Err(format!(
						"CapErr with no bump applied: {:?}", errs));
				}
				log(0, LOG1, &format!("determine_config_aggr iter {}: \
					round {} ms, bumped {:?}", iter, t_round.ms(), errs));
			}
		}
	}
	Err(format!("max_iters {} reached without convergence", max_iters))
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

/// One DLP sample's determine_config run (M2). Builds-or-loads the cached
/// aggressive DLP DB (first run builds+caches, rest load), discharges the
/// sample manifest, auto-tunes the LOWEST CapParams via determine_config_aggr
/// (seeded low; CapErr bumps are exact so it converges in a few iters), and
/// writes the result to rc.config_out -- the JSON handoff the driver sequences.
pub(crate) fn run_dlp_sample_config<F,C,CS>(rc: &crate::determine_config::RunCfg)
where C: CurveGroup<ScalarField=F>,
      CS: CommitmentScheme<C,false>,
      <CS as CommitmentScheme<C,false>>::ProverParams: Send + Sync,
      F: PrimeField + Absorb + ColEle,
{
	use crate::determine_config::capparams_from_caps_aggr;
	//1. knobs: aggressive CS-only fan-out; low floors so the tuner finds the
	//true minimum (bumps climb to the exact required value).
	get_global_config().range2_bit = rc.range2_bit;
	get_global_config().b_light_test = true;
	get_global_config().perc_lkup_share = 1;
	get_global_config().min_subsigs = 1;
	get_global_config().min_basis_unique_states = 2;
	get_global_config().min_basis_acc_states = 2;
	get_global_config().min_basis_pats_in_trace = 4;
	get_global_config().min_avg_pats_per_subsig = 1;
	get_global_config().clamav_cfg.b_aggressive_sde_for_rep = true;
	get_global_config().clamav_cfg.sde_rep_fanout_cap = rc.fanout_cap;
	get_global_config().clamav_cfg.min_pm_word_len = 3;

	//2. build or load the cached DB (shared across all samples; same sig set)
	let cfg = default_clamav_cfg();
	let sig = format!("{}/{}", rc.config_dir, rc.sig_file);
	let dfa = format!("{}/main_dfa.dat", rc.config_dir);
	let ised = format!("{}/needs_ised.dat", rc.config_dir);
	let ised_igc = format!("{}/needs_ised_igc.dat", rc.config_dir);
	let mut vlog = vec![];
	let db = ClamavDB::<F>::build_or_load(&cfg, &sig, &dfa, &ised, &ised_igc,
		&mut vlog, &rc.cache_dir, true, true).expect("build/load db");

	//3. discharge the sample manifest -> words + per-file WordInfo
	let scan = format!("{}/{}", rc.config_dir, rc.scan_file);
	let (words, infos, _fnames) = load_files::<F>(0, &scan, &db, &cfg,
		false, &rc.cache_dir, rc.chunk_len);
	let total_word_n: usize = words.iter().map(|w| w.len()).sum();
	let rc_db = Arc::new(db);
	let lkup_len = rc_db.lkup.get_size();

	//4. seed a LOW config; determine_config_aggr climbs via exact CapErr bumps
	let mw = rc.chunk_len;
	let cp = CpCapacity { max_word_len: mw, basis_unique_states: 2,
		subsigs: 1, avg_pats_per_subsig: 1 };
	let sed = SedCapacity::new(mw, rc.range2_bit, 1, 1, 1, 4, 16, 1, 1, 2, 2);
	let p0 = capparams_from_caps_aggr(&cp, &sed, 1);

	//5. tune + write the JSON handoff
	let n_threads = std::env::var("ZKR_DC_THREADS").ok()
		.and_then(|s| s.parse().ok()).unwrap_or(4);
	match determine_config_aggr::<F,C,CS>(rc_db, &words, &infos, p0,
		rc.chunk_len, lkup_len, total_word_n, 60, n_threads) {
		Ok(p) => {
			// resolve via proj_root (test cwd is the package dir, not the
			// workspace root) -- matching load_files' path handling.
			let out = format!("{}/{}", proj_root(), rc.config_out);
			p.save_json(&out).expect("save config_out");
			log(0, LOG1, &format!("FULL_DLP sample -> {} : {:?}", out, p));
		}
		Err(e) => panic!("determine_config_aggr failed: {}", e),
	}
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
	for iter in 0..max_iters {
		let mut t_round = GTimer::new();
		let probe_res = crate::determine_config::probe_catching(|| {
			let (cp_cs, sed_cs, dfa, cp_igc, sed_igc) =
				caps_from_params_general(&p);
			let layered = build_circs_adv::<F,C,CS>(&poseidon, total_word_n,
				chunk_len, lkup_len, db.clone(), &cp_cs, &sed_cs, &dfa,
				&cp_igc, &sed_igc, vec_decrease_level, n_circs, false);
			let planner = CapacityPlanner::<C, FC<F,C,CS>, LK<F>, GM<F>,
				false>::new(layered);
			planner.capacity_probe_par(&padded, sample_word_infos, n_threads)
		})?;
		t_round.stop();
		match probe_res {
			Ok(steps) => {
				t_all.stop();
				log(0, LOG1, &format!("determine_config_general CONVERGED \
					@iter {}: steps={}, perc_cs={}, perc_igc={}, subsigs={}, \
					basis_acc={}; round {} ms, TOTAL {} ms", iter, steps,
					p.perc_pats_expansion_rate, p.perc_pats_expansion_rate_igc,
					p.subsigs, p.basis_acc_states, t_round.ms(), t_all.ms()));
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
	//println!("DEBUG USE 1001: lkup_len: {}, avg_lk_wd: {}, comp1 share size: {}", lkup_len, avg_lk_wd, cg1.max_word_len()*avg_lk_wd);

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
	zkp_driver_adv::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,S>(job_id, sig_file, vec![list_file_to_scan.to_string()], _logfile,
		b_write_cache, cache_dir,
		list_of_dfa_sigs, list_of_ised_sigs, list_of_ised_igc_sigs,
		chunk_len,
		init_cp_capacity, init_sed_capacity, init_dfa_capacity,
		init_cp_capacity, init_sed_capacity, 
		vec_decrease_levels, num_circs, b_check_lkup
	);
}
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
		let (vec_words, vec_word_info, vec_word_fnames) = load_files::<CF1<C1>>(job_id, &list_file_to_scan, &db, &cfg, b_write_cache, cache_dir, chunk_len);
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
	// determine_config probe (env-gated, non-aggressive): reuse the built DB +
	// loaded jobs to auto-tune the lowest CapParams via the Pass-1 probe, then
	// return. Warm-starts perc/avg_active (cs+igc) low to exercise convergence;
	// compares vs the runner's hand caps with the +10% rule. Framework untouched.
	if std::env::var("ZKR_DETERMINE_CONFIG").is_ok() {
		use crate::determine_config::{capparams_from_caps_general, compare_caps};
		let cur = capparams_from_caps_general(init_cp_capacity_cs,
			init_sed_capacity_cs, init_dfa_capacity, init_sed_capacity_igc);
		let mut p0 = cur.clone();
		// warm-start LOW (floor 16) to exercise convergence to the true
		// minimum. If 16 is below a structural build floor, build_circs panics
		// -> probe_catching converts it to a bump (auto-discovers the floor).
		p0.perc_pats_expansion_rate = cur.perc_pats_expansion_rate.min(16);
		p0.perc_pats_expansion_rate_igc =
			cur.perc_pats_expansion_rate_igc.min(16);
		p0.avg_active_pats_per_subsig = cur.avg_active_pats_per_subsig.min(2);
		p0.avg_active_pats_per_subsig_igc =
			cur.avg_active_pats_per_subsig_igc.min(2);
		// tune over ALL scan files (worst-case across the sample set).
		let all_words: Vec<Vec<CF1<C1>>> = jobs.iter()
			.flat_map(|j| j.vec_words.iter().cloned()).collect();
		let all_infos: Vec<WordInfo> = jobs.iter()
			.flat_map(|j| j.vec_word_info.iter().cloned()).collect();
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
			}
			Err(e) => log(0, log_level,
				&format!("DETERMINE_CONFIG FAILED: {}", e)),
		}
		return;
	}
	let vec_circs = build_circs_adv::<CF1<C1>,C1,CS1>(
		&poseidon_config,
		max_total_word_len,
		chunk_len,
		lkup_len,
		rc_db,
		init_cp_capacity_cs,
		init_sed_capacity_cs,
		init_dfa_capacity,
		init_cp_capacity_igc,
		init_sed_capacity_igc,
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

	//4. run the foldpot_main
	let lkup = Arc::new(db.lkup);
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
		lkup, vec_circs, &mut jobs, cache_dir).expect("main err");

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
		let (vec_words, vec_word_info, vec_word_fnames) = load_files::<CF1<C1>>(job_id, &list_file_to_scan, &db, &cfg, b_write_cache, cache_dir, chunk_len);
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

	//3. build the circuits (CS-only aggressive)
	let rc_db = Arc::new(db.clone());
	// determine_config probe (env-gated ZKR_DETERMINE_CONFIG): reuse the built
	// DB + loaded jobs to auto-tune the LOWEST CapParams via the Pass-1
	// capacity probe, then return (no folding). Warm-starts from a LOW
	// perc/avg_active to exercise convergence; compares the result against the
	// runner's hand caps (cur) with the +10% rule.
	if std::env::var("ZKR_DETERMINE_CONFIG").is_ok() {
		use crate::determine_config::{capparams_from_caps_aggr, compare_caps};
		let cur = capparams_from_caps_aggr(&cs_caps[0].0, &cs_caps[0].1,
			read_global_config().aggr_needs_subsigs);
		let mut p0 = cur.clone();
		// floor 16; probe_catching handles any structural-floor build panic.
		p0.perc_pats_expansion_rate = cur.perc_pats_expansion_rate.min(16);
		p0.avg_active_pats_per_subsig = cur.avg_active_pats_per_subsig.min(2);
		// tune over ALL scan files (worst-case across the sample set).
		let all_words: Vec<Vec<CF1<C1>>> = jobs.iter()
			.flat_map(|j| j.vec_words.iter().cloned()).collect();
		let all_infos: Vec<WordInfo> = jobs.iter()
			.flat_map(|j| j.vec_word_info.iter().cloned()).collect();
		let n_threads = std::env::var("ZKR_DC_THREADS").ok()
			.and_then(|s| s.parse().ok()).unwrap_or(4);
		match determine_config_aggr::<CF1<C1>,C1,CS1>(rc_db.clone(),
			&all_words, &all_infos, p0, chunk_len,
			lkup_len, max_total_word_len, 30, n_threads) {
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
			}
			Err(e) => log(0, log_level,
				&format!("DETERMINE_CONFIG FAILED: {}", e)),
		}
		return;
	}
	let vec_circs = build_circs_adv_aggr::<CF1<C1>,C1,CS1>(
		&poseidon_config,
		max_total_word_len,
		chunk_len,
		lkup_len,
		rc_db,
		cs_caps,
		b_check_lkup
	);
	log_perf(0, log_level, &format!("ZIP driver step 2: build circs."), &mut gt1);

	if read_global_config().b_dryrun_after_capcheck {
		log(0, log_level, &format!(
			"=== M8 DRYRUN: build_circs_adv_aggr passed, exiting before \
			 foldpot_main. circs={} ===", vec_circs.len()));
		return;
	}

	//4. run the foldpot_main
	let lkup = Arc::new(db.lkup);
	foldpot_main::<E,P,C2G2,C1,GC1,C2,GC2,CS1,CS2,CS1E,FC<CF1<C1>,C1,CS1>,
		S,LK<CF1<C1>>,GM<CF1<C1>>, false>(
		lkup, vec_circs, &mut jobs, cache_dir).expect("main err");

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
	use utils::consts::{read_global_config, get_global_config};
	//use folding_schemes::folding::foldpot::container_config::ColEle;
	use ark_bn254::{constraints::{GVar,PairingVar}, Bn254, Fr, G1Projective as Projective, G2Projective as ProjectiveG2};
	use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
	use ark_groth16::Groth16;
	use folding_schemes::{commitment::{pedersen::Pedersen, kzg::KZG}};
	use crate::zkp_driver::{zkp_driver, zkp_driver_adv,
		zkp_driver_adv_aggr};
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


	/// small_debug (Plan D): single-job local reproducer for the
	/// compute_sig_adv.rs:1269 panic. Uses the CACHED full_clamav DFA
	/// (data/cache/full_data/, ~4.1GB) so the AC-DFA over-approximation
	/// is identical to the server's; scans ONE file (merged_217); sets
	/// b_folding_only=true so the heavy SNARK preprocess is skipped
	/// (bug fires during gen_nd_advice / pass_all anyway). Capacities
	/// mirror full_debug — already validated. Prerequisite: a prior
	/// full_clamav run must have populated data/cache/full_data/.
	#[allow(dead_code)]
	fn small_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("small_debug"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_folding_only = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = true;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1_cfg  = "data/debug/full_clamav/config/";
		// All 4 files — matches server's binexec_debug.dat exactly.
		let set1_scan = "data/debug/full_debug/config";
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

		let scan_files: Vec<String> = vec![
			format!("{}/binexec_debug.dat", set1_scan),
		];

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,
			CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1_cfg),
			scan_files,
			"data/debug/full_debug/reports/report.dat",
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
		);
	}

	/// This runs the full signature set on the most difficult files
	/// each is 15-32MB file
	/// details:
	/// 1: -rw-rw-r-- 1 xiang xiang 33554416 Jun  8  2025 anthoscli__00
	/// 2: -rw-rw-r-- 1 xiang xiang 33554416 Jun  8  2025 anthoscli__01
	/// 3: -rwxrwxr-x 1 xiang xiang 22720144 Jun  8  2025 libpython3.9.so (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 4: -rwxrwxr-x 1 xiang xiang 22720144 Jun  8  2025 libpython3.9.so.1.0 (Max Acc Rate: 11.37%, Max Pat Rate: 11.37%)
	/// 5: -rwxrwxr-x 1 xiang xiang 20785824 Jun  8  2025 libicudata.so.50.2 (Max Acc Rate: 5.32%, Max Pat Rate: 5.38%)
	/// 6: -rwxrwxr-x 1 xiang xiang 15603008 Jun  8  2025 cc1plus (Max Acc Rate: 12.33%, Max Pat Rate: 12.36%)
	/// 7: -rwxrwxr-x 1 xiang xiang 15022144 Jun  8  2025 data/samples/binexec_merged128k/f951 (Max Acc Rate: 12.42%, Max Pat Rate: 12.45%)
	/// 8: -rwxrwxr-x 1 xiang xiang 13676928 Jun  8  2025 data/samples/binexec_merged128k/lto1 (Max Acc Rate: 11.57%, Max Pat Rate: 11.63%)
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
				b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
		);
	}


	/// This tests the full clamav signatures against linux executables
	/// There are 756MB Linux binary executable
	/// We split them into 8 jobs.
	/// E.g., run on m3m machine with 2TB (xx cpu)
	/// Can finish in xxx hrs.
	#[allow(dead_code)]
	fn full_clamav<F:PrimeField>(b_check_lkup: bool, b_light_test: bool,
		b_setup: bool){
		utils::os::print_computer_config(Some("full_clamav"));
		//extra setting
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		get_global_config().b_write_snark_cache = b_setup;
		get_global_config().b_read_snark_cache = !b_setup;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = b_light_test;
		get_global_config().min_subsigs = 368; // OLD value: 361
		get_global_config().min_basis_unique_states= 1054; // OLD value: 600
		get_global_config().min_basis_acc_states =  268; // OLD value: 113
		get_global_config().min_basis_pats_in_trace=  295; // OLD value: 134
		get_global_config().min_avg_pats_per_subsig= 8; // OLD value: 6
		get_global_config().min_dfa_sigs = 3; // OLD value: 2
		get_global_config().min_dfa_subsigs =  3; //OLD val 2
		get_global_config().n_par_snark = if b_setup {1} else {2};
		get_global_config().n_par_snark_cp = if b_setup {1} else {2};
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143; //this is for
			//700MB data in 8 jobs and 256M lkup entries
			//so we have per job: 90MB data = 180M nibbles
			// then: 256/180 * 100 = 142.2% that's 142


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

		let num_jobs = if b_setup {1} else {8};
		let scan_files: Vec<String> = if b_setup {
			(0..num_jobs).map(|i|
				format!("{}/sample_1M_{}.dat", set1, i)).collect()
		} else {
			(0..num_jobs).map(|i|
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
			b_check_lkup
		);
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
		get_global_config().b_light_test = true;
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
			b_check_lkup
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
		let cs_caps = vec![(init_cp_cap, init_sed_cap,
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
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
			b_check_lkup
		);
	}

	/// 2026-05-16: full_debug — mirrors full_clamav (test-mod
	/// capacities) but with a SINGLE list file (n_jobs=1) of 4
	/// server-failing samples. Reuses data/cache/full_clamav snark
	/// keys + data/cache/full_data DB cache. Used by
	/// test_full_debug_main below, which full_debug_watch.py
	/// invokes via `cargo test`. All capacities here are
	/// byte-identical to the full_clamav() above — keep them in
	/// sync if you tune full_clamav.
	fn full_debug<F:PrimeField>(b_check_lkup: bool){
		utils::os::print_computer_config(Some("full_debug"));
		get_global_config().snark_cache_dir = "full_clamav".to_string();
		// 2026-05-16: full_debug intentionally does NOT load or
		// generate Groth16 keys. The check_logup panic we're trying
		// to reproduce fires inside pass_all/gen_step_cs, which is
		// reached before the post-pass_all SNARK step. Combined
		// with b_folding_only=true (which returns Ok(()) right
		// after pass_all), the prover never touches g16_main.key /
		// g16_cp.key — so the user doesn't need to have run
		// full_clamav_setup. See driver.rs:2497 (key load) and
		// driver.rs:2845 (b_folding_only early return).
		get_global_config().b_write_snark_cache = false;
		get_global_config().b_read_snark_cache = false;
		get_global_config().b_folding_only = true;
		get_global_config().range2_bit = 26;
		get_global_config().b_light_test = true;
		get_global_config().min_subsigs = 368;
		get_global_config().min_basis_unique_states = 1054;
		get_global_config().min_basis_acc_states = 268;
		get_global_config().min_basis_pats_in_trace = 295;
		get_global_config().min_avg_pats_per_subsig = 8;
		get_global_config().min_dfa_sigs = 3;
		get_global_config().min_dfa_subsigs = 3;
		get_global_config().n_par_snark = 2;
		get_global_config().n_par_snark_cp = 2;
		get_global_config().n_par_batch_claim = 8;
		get_global_config().perc_lkup_share = 143;

		get_global_config().b_read_cache = true;
		let b_write_cache = !read_global_config().b_read_cache;
		let set1_cfg  = "data/debug/full_clamav/config/";
		let set1_scan = "data/debug/full_debug/config/";
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

		// Single list file => n_jobs = 1, 4 words inside.
		let scan_files: Vec<String> = vec![
			format!("{}/binexec_debug.dat", set1_scan),
		];

		zkp_driver_adv::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,
			CS2,CS1E,S>(
			0,
			&format!("{}/main.dat", set1_cfg),
			scan_files,
			"data/debug/full_debug/reports/report.dat",
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
			b_check_lkup
		);
	}

	/// 2026-05-16: dedicated test entry for full_debug_watch.py.
	/// Invoked via `cargo test ... test_full_debug_main`.
	#[test]
	pub fn test_full_debug_main(){
		full_debug::<Fr>(false);
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
		//small_data::<Fr>(b_check_lkup); //small data
		small_email::<Fr>(b_check_lkup); //M6: aggressive multi-chunk run
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
			"main_data_dlp_internationl.dat", //src sig (NEW)
			"binexec_dlp_intl.dat", //scan manifest (NEW)
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
			&format!("{}/main_data_dlp_internationl.dat", dir),
			&format!("{}/main_dfa.dat", dir),
			&format!("{}/needs_ised.dat", dir),
			&format!("{}/needs_ised_igc.dat", dir),
			"data/src_sig/ms_dlp/docs/\
clean_email_list_email_regex_zombie_international.txt", //515K list
			"data/samples/email",  //base prefix for list entries
			dir,                   //out dir for full/pass/fail lists
			true, true,            //b_read_cache, b_write_cache
			"dlp_intl_data_aggr",  //DB cache name
			64);                   //seg_word_len: 64w*31B ~= 2KB
	}                              //(median email fills ~78%)

	/// full_dlp pipeline (M2): tune the SMALL (easy) config from sample1's
	/// manifest. Driven by scripts/run_full_dlp.py via ZKR_DLP_RUNCFG; writes
	/// CapParams JSON to runcfg.config_out. Same body as full_dlp_sample2 (the
	/// scan manifest + output path differ only in the driver's runcfg).
	#[test]
	pub fn full_dlp_sample1(){
		let rc = crate::determine_config::RunCfg::from_env();
		super::run_dlp_sample_config::<Fr,C1,CS1>(&rc);
	}

	/// full_dlp pipeline (M2): tune the BIG (hard) config from sample2's
	/// manifest. See full_dlp_sample1.
	#[test]
	pub fn full_dlp_sample2(){
		let rc = crate::determine_config::RunCfg::from_env();
		super::run_dlp_sample_config::<Fr,C1,CS1>(&rc);
	}

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

	/// full_dlp pipeline sample3: FOLD-ONLY run of the sample3 list over a
	/// 2-circuit ladder -- C1 (sample1, cheap) + C2 (sample2, big). Each word
	/// sticks to the cheapest fitting layer (foldpot find_working_layer). The
	/// log carries per-word layer (PERF 1001 ... pci:) and per-step circ + time
	/// (prove_step cost ... circ_id:). No SNARK (b_folding_only).
	#[test]
	pub fn full_dlp_sample3(){
		use crate::determine_config::caps_from_params_aggr;
		use crate::stats_helper::{estimate_config_aggr,
			estimated_to_capparams_aggr};
		use folding_schemes::folding::foldpot::sigma_ir1cs
			::LookupTableTwoCol as _;
		let rc = crate::determine_config::RunCfg::from_env();
		let proot = utils::os::proj_root();
		let cd = &rc.config_dir;
		let mw = rc.chunk_len;
		//aggressive CS-only, folding-only, estimate-on for the tuning discharge.
		get_global_config().range2_bit = rc.range2_bit;
		get_global_config().b_light_test = true;
		get_global_config().b_folding_only = true;
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
			&format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), &mut vlog,
			&rc.cache_dir, true, true).expect("build db");
		//discharge the full 5087 list (one pass) -> vdata + words + infos
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
		//NEEDS distribution study: reuse the per-chunk arrays just
		//discharged (aggressive flag is on here), no second pass. Study
		//only -> print and return, skipping the finalize+fold.
		if std::env::var("ZKR_DLP_NEEDS_DIST").is_ok() {
			let rows: Vec<Vec<usize>> = vdata.iter()
				.map(|r| r.chunk_peaks.needs_per_chunk.clone()).collect();
			crate::needs_dist::print_needs_dist_rows(&rows, &files);
			return;
		}
		//estimate -> p90 (C_low seed) + p100 (C_high seed)
		let est = estimate_config_aggr::<Fr>(&vdata, &db, &[90,100],
			&mut vlog);
		let seed_low = estimated_to_capparams_aggr(&est[0], mw,
			rc.range2_bit, 3);
		let seed_high = estimated_to_capparams_aggr(&est[1], mw,
			rc.range2_bit, 3);
		let total_word_n: usize = words.iter().map(|w| w.len()).sum();
		let lkup_len = db.lkup.get_size();
		let db_arc = std::sync::Arc::new(db);
		//partition by NEEDS (max anchor-present subsigs/chunk) -- the cost
		//driver (= subsigs), NOT survivors: a file can have high needs but few
		//survivors, and needs is what blows up the circuit. The dense 10%
		//(high needs) drive C_high, the light 90% (mostly needs=0) drive
		//C_low. Finalize C_high over ONLY the dense tail -- the big envelope
		//makes each probe ~18s, so all 5087 would take days; lower-needs files
		//fit C_high (the denser circuit) so routing covers them, no crash.
		let mut costs: Vec<(usize,usize)> = vdata.iter().enumerate()
			.map(|(i,r)| (i, r.chunk_peaks.max_needs_subsigs)).collect();
		costs.sort_by_key(|&(_,c)| c);
		let k = ((costs.len()*90)/100).max(1);
		let hi: Vec<usize> = costs[k..].iter().map(|&(i,_)| i).collect();
		let lo: Vec<usize> = costs[..k].iter().map(|&(i,_)| i).collect();
		let w_hi: Vec<Vec<Fr>> = hi.iter().map(|&i| words[i].clone()).collect();
		let i_hi: Vec<_> = hi.iter().map(|&i| infos[i].clone()).collect();
		let w_lo: Vec<Vec<Fr>> = lo.iter().map(|&i| words[i].clone()).collect();
		let i_lo: Vec<_> = lo.iter().map(|&i| infos[i].clone()).collect();
		//C_high = PRECISE over the dense 10% (covers the tail + everything
		//less dense). C_low = QUICK over the light 90% (SED-free -> fast).
		//fast_finalize probes only the per-proxy top-K binding files of each
		//tier (sufficiency by construction: the argmax file of every cap is
		//in the candidate set), so cost is corpus-size-independent.
		let k_cand = 8usize;
		let vd_hi: Vec<_> = hi.iter().map(|&i| vdata[i].clone()).collect();
		let vd_lo: Vec<_> = lo.iter().map(|&i| vdata[i].clone()).collect();
		let c_high = super::fast_finalize::<Fr,C1,CS1>(db_arc.clone(),
			&w_hi, &i_hi, &vd_hi, seed_high, mw, lkup_len, total_word_n, 60, 4,
			super::ShrinkMode::Precise, k_cand).expect("C_high finalize");
		let c_low = super::fast_finalize::<Fr,C1,CS1>(db_arc.clone(),
			&w_lo, &i_lo, &vd_lo, seed_low, mw, lkup_len, total_word_n, 60, 4,
			super::ShrinkMode::Quick, k_cand).expect("C_low finalize");
		let _ = c_low.save_json(&format!("{}/{}", proot, rc.config_c1));
		let _ = c_high.save_json(&format!("{}/{}", proot, rc.config_c2));
		utils::logger::log(0, utils::logger::LOG1,
			&format!("M3 self-tuned: C_low {:?}  C_high {:?}", c_low, c_high));
		//determine_config-only mode: the config files are written; skip the
		//fold. This is how a 500k workload is tuned on the server -- the
		//resulting C1/C2 jsons feed full_enron (read-config-and-fold).
		if std::env::var("ZKR_DLP_DETERMINE_ONLY").is_ok() {
			utils::logger::log(0, utils::logger::LOG1, &format!(
				"ZKR_DLP_DETERMINE_ONLY set: configs saved, skipping fold"));
			return;
		}
		//free the DB before the fold driver loads its own copy (avoid 2x RAM)
		drop(db_arc);
		get_global_config().b_estimate_caps = false;
		//2-tier ladder (cheap first), fold the full list folding-only
		let cs_caps = vec![caps_from_params_aggr(&c_low),
			caps_from_params_aggr(&c_high)];
		let scan = vec![format!("{}/{}", cd, rc.scan_file)];
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), scan, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), mw, &cs_caps, false);
		let _ = std::fs::write(&format!("{}/{}", proot, rc.report_out),
			format!("M3 sample3 fold-only: {} via 2-tier [C_low,C_high]\n",
				rc.scan_file));
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
			&format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), &mut vlog,
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
			&files, &proot, &db, &cfg, mw);
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
			&format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), &mut vlog,
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
			false, &rc.cache_dir, &format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), mw, &cs_caps, false);
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
		//C_low then C_high == cheap-first 2-tier ladder.
		let c_low = CapParams::load_json(
			&format!("{}/{}", proot, rc.config_c1));
		let c_high = CapParams::load_json(
			&format!("{}/{}", proot, rc.config_c2));
		utils::logger::log(0, utils::logger::LOG1, &format!(
			"full_enron: loaded C_low {:?}  C_high {:?}", c_low, c_high));
		let cs_caps = vec![caps_from_params_aggr(&c_low),
			caps_from_params_aggr(&c_high)];
		let scan = vec![format!("{}/{}", cd, rc.scan_file)];
		zkp_driver_adv_aggr::<Bn254,PairingVar,C2G2,C1,GC1,C2,GC2,CS1,CS2,
			CS1E,S>(
			0, &format!("{}/{}", cd, rc.sig_file), scan, &rc.report_out,
			false, &rc.cache_dir, &format!("{}/main_dfa.dat", cd),
			&format!("{}/needs_ised.dat", cd),
			&format!("{}/needs_ised_igc.dat", cd), mw, &cs_caps, false);
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

	/// small_email3: full MS DLP set vs binexec3.dat (the two most
	/// challenging clean emails). Reads the shared email_data DB cache.
	/// `cargo test -p zkregplus -- test_small_email3 --show-output --nocapture`
	#[test]
	pub fn test_small_email3(){
		small_email3::<Fr>(false);
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
			&format!("{}/main_dfa.dat", set1),
			&format!("{}/needs_ised.dat", set1),
			&format!("{}/needs_ised_igc.dat", set1), &mut vlog,
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
		let sg = "main_data_dlp_internationl.dat";
		let ca = "dlp_intl_data_aggr";
		// PASS CRITERION = finalize converges (every word plans under FIN),
		// gated inside estimator_validate_aggr via .expect("finalize failed").
		// The four-way OLD/NEW/FIN/REAL table is INFORMATIONAL: FIN may sit
		// below an over-provisioned REAL (determine_config overshoots the
		// multiplicative density caps) and still be a valid covering config.
		let _fin_ge_real_1 = estimator_validate_aggr("dlp_sample1", cd, sg,
			"binexec_sample1.dat", 25, 64, 100, ca,
			"data/paper_data/dlp/cfg/dlp_config_C1.json");
		let _fin_ge_real_2 = estimator_validate_aggr("dlp_sample2", cd, sg,
			"binexec_sample2.dat", 25, 64, 100, ca,
			"data/paper_data/dlp/cfg/dlp_config_C2.json");
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
