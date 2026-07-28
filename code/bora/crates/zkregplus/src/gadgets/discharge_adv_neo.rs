// discharge_adv_neo.rs
// Created 2026-07-19.
// Design by the BORA paper author. Code implemented by Claude Opus.
// Code reviewed by the paper author and unit tested.
//
// M3 coexistence stub for the Appendix G.1 constant-queue SDE. This
// stub delegates every SigmaGadget method to DischargeAdvGadget, so the
// neo path is byte-identical to the legacy SDE. The real G.1
// certificates (C/FP/BP/SP over StepQueueNeo) replace the body in M4-M7.

use ark_ff::{PrimeField, Zero, batch_inversion};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::lc;
use ark_relations::r1cs::{SynthesisError, ConstraintSystemRef};
use data_processor::type_def::SubsigStepStore;
use data_processor::clam_db::{reverse_pm_bounds, RANGE2,
	ID_ENCODED_NORMAL_STEP, ID_ENCODED_LAST_STEP, ID_ENCODED_SUBSIG,
	ID_ENCODED_PAT, ID_ENCODED_RG_START, ID_ENCODED_RG_END,
	ID_ENCODED_PREV_ENCODED, ID_ENCODED_FZ, ID_SUBSIG_IS_BACKWARD};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use utils::consts::read_global_config;
use utils::logger::{log, LOG3};
use ark_r1cs_std::R1CSVar;
use folding_schemes::Error;
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget, WitnessSigmaIR1CSVar,
		WitnessSigmaIR1CSConfig, NdAdvice},
	container_config::{ColEle, ContainerConfig},
	circuits_super::field_to_usize,
};
use crate::gadgets::commons::{encode_cols, is_zero_better_adv,
	check_eq, check_prod_zero, better_select, new_const_var,
	gen_m_table_cond, gen_m_table};
use crate::gadgets::db::{assert_logup, assert_logup_cond,
	assert_well_formed_sorted};
use crate::gadgets::traits::{Container, Col, IDX_DATA, IDX_SI_DATA,
	ComponentAdvice};
use crate::gadgets::discharge_adv::{DischargeAdvGadget,
	DischargeAdvAdvice, DischargeAdvCapacity, FailedSubsigAcc,
	StepQueue, StepQueueItem, StepQueueType};

/// M3 stub wrapping the legacy SDE gadget; forwards all trait methods.
#[derive(Clone, Debug)]
pub struct DischargeAdvNeoGadget<F: PrimeField + ColEle> {
	/// delegate target; replaced by native G.1 state in M4+.
	pub inner: DischargeAdvGadget<F>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// mirrors DischargeAdvGadget::new so the sed_mapper swap is 1:1.
	/// The neo SigmaGadget plumbing (container config, stmt map, msg
	/// sizes) delegates to `inner`; to make it describe the NEO
	/// statement {neo_core, q_i, q_c} we overwrite inner.dummy_cfg with
	/// a config built from a dummy neo advice (same idea as legacy new).
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		capacity: &DischargeAdvCapacity,
		fsm_id: u32,
		prev_cfgs: &Vec<ContainerConfig>,
		store_steps: &SubsigStepStore,
	) -> Self {
		let mut inner = DischargeAdvGadget::<F>::new(
			b_igc, offset_fsm, capacity, fsm_id, prev_cfgs,
			store_steps);
		inner.dummy_cfg = Self::build_neo_dummy_cfg(b_igc,
			offset_fsm, capacity, fsm_id, prev_cfgs, store_steps);
		Self { inner }
	}

	/// Build the neo statement's container config from an all-dummy
	/// neo advice (structure only -- sizes come from capacity, not the
	/// zero data), mirroring DischargeAdvGadget::new's dummy_cfg build.
	fn build_neo_dummy_cfg(
		b_igc: bool,
		offset_fsm: usize,
		capacity: &DischargeAdvCapacity,
		fsm_id: u32,
		prev_cfgs: &Vec<ContainerConfig>,
		store_steps: &SubsigStepStore,
	) -> ContainerConfig {
		let zero = F::zero();
		let pats_len = capacity.get_pat_loc_len();
		// EMPTY pat_loc (all-zero, length = capacity):
		// gen_merge_dict's D-dict base = the FULL store's distinct
		// pats (8_C constant), and a real chunk's matched pats are a
		// SUBSET of those -> same d_pat length as real chunks (so the
		// dummy config size == every real chunk's statement size).
		let pat_loc = Container::<F>::new("pat_loc");
		pat_loc.lock().unwrap().add_col(Col::<F>::new(
			vec![zero; pats_len], "sorted_key", IDX_DATA));
		pat_loc.lock().unwrap().add_col(Col::<F>::new(
			vec![zero; pats_len], "sorted_id", IDX_DATA));
		pat_loc.lock().unwrap().add_col(Col::<F>::new(
			vec![zero; pats_len], "sorted_val", IDX_DATA));
		// Legacy-style all-zero carried seed (fits any capacity).
		// 8_C: every store-derived size is a capacity budget (qm
		// wrap budget, K subsig slots, S_cap pad, full-store D), so
		// the dummy (empty NEEDS -> all-pad tables) has the same
		// statement size as every real chunk.
		let sigs = vec![zero; capacity.subsigs];
		let (step_q_size, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResSmall, capacity);
		let inp_steps_queue = vec![zero; step_q_size * 2];
		let inp_steps_queue_obj = StepQueue::parse_from(
			&inp_steps_queue, StepQueueType::ResSmall, capacity,
			b_igc);
		let dummy_adv = DischargeAdvNeoAdvice::new(b_igc, offset_fsm,
			&pat_loc, &sigs, fsm_id, store_steps, capacity,
			&inp_steps_queue_obj, zero, 0, 0)
			.expect("neo dummy advice");
		let mut vec_cfg = prev_cfgs.clone();
		vec_cfg.push(dummy_adv.stmt_container.lock().unwrap()
			.get_cfg());
		ContainerConfig::adjust_locations(&mut vec_cfg);
		vec_cfg[vec_cfg.len() - 1].clone()
	}
}

impl<F: PrimeField + ColEle> SigmaGadget<F>
	for DischargeAdvNeoGadget<F> {
	fn get_name(&self) -> &str { self.inner.get_name() }

	fn set_job_id(&mut self, job_id: usize) {
		self.inner.set_job_id(job_id);
	}

	fn get_job_id(&self) -> usize { self.inner.get_job_id() }

	fn set_container_cfg(&mut self,
		cfgs_context: std::sync::Arc<Vec<ContainerConfig>>,
		idx: usize) {
		self.inner.set_container_cfg(cfgs_context, idx);
	}

	fn get_container_config(&self) -> ContainerConfig {
		self.inner.get_container_config()
	}

	fn est_cost(&self) -> usize { self.inner.est_cost() }

	fn get_msg_size(&self) -> (usize, usize, usize, usize) {
		self.inner.get_msg_size()
	}

	fn get_to_add_size(&self)
		-> (usize, usize, usize, usize, usize) {
		self.inner.get_to_add_size()
	}

	fn get_stmt_map_instructions(&self)
		-> Vec<(i32, usize, usize, usize)> {
		self.inner.get_stmt_map_instructions()
	}

	fn gen_msg1(&self, stmt_vec: &Vec<F>,
		v_idx: &Vec<(usize, usize)>) -> Vec<F> {
		self.inner.gen_msg1(stmt_vec, v_idx)
	}

	fn gen_msg3(&self, stmt_vec: &Vec<F>,
		stmt_idx: &Vec<(usize, usize)>,
		msg1_vec: &Vec<F>, idx_msg1: usize, len_msg1: usize,
		msg2_vec: &Vec<F>, idx_msg2: usize, len_msg2: usize)
		-> Vec<F> {
		self.inner.gen_msg3(stmt_vec, stmt_idx, msg1_vec,
			idx_msg1, len_msg1, msg2_vec, idx_msg2, len_msg2)
	}

	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>,
		wtns: &WitnessSigmaIR1CSVar<F>,
		cfg: &WitnessSigmaIR1CSConfig,
		_word_id: FpVar<F>, _subsig_id: FpVar<F>)
		-> Result<(), SynthesisError> {
		// M6: aggressive arm = the G.1 {C,FP} core; M7:
		// non-aggressive arm = the full C.1 partition with the
		// committed q_i/q_c carry. Both consume the NEO statement
		// (DischargeAdvNeoAdvice); wiring the sed_mapper advice
		// path onto it is M8 -- until then the non-aggressive arm
		// is exercised by the tier-1/tier-2 tests only.
		if self.inner.capacity.b_aggressive {
			self.assert_msg3_neo_aggr(i, cs, wtns, cfg)
		} else {
			self.assert_msg3_neo_nonaggr(i, cs, wtns, cfg)
		}
	}
}

// ============================================================
//   M4: StepQueueNeo + attributes + (A) carry / (B) full
//        serialization + MIN/LEN relations
// ============================================================

// ---- G.1 partition classes (0 = unset/dummy row) ----
pub const CAT_UNSET: u32 = 0;
pub const CAT_C:  u32 = 1;   // carry
pub const CAT_FP: u32 = 2;   // forward-pruned
pub const CAT_BP: u32 = 3;   // backward-pruned
pub const CAT_SP: u32 = 4;   // singleton-pruned

/// full (B) serialization column count:
/// [encoded, loc, cat, prev_id1, prev_loc1, prev_loc2,
///  min_next, fz, queue_len]
pub const N_NEO_COLS: usize = 9;

/// One (subsig, step) neo item: a standard StepQueueItem plus G.1 witness
/// columns. cat/prev_* are parallel to base.locs; min_next/fz/queue_len are
/// per-item scalars (replicated per row on serialize).
#[derive(Clone, Debug, PartialEq)]
pub struct StepQueueItemNeo<F: PrimeField + ColEle> {
	/// standard item: supplies encoded/locs/subsig/step/pat/rg_start/rg_end.
	pub base: StepQueueItem<F>,
	/// partition class per loc (CAT_C/FP/BP/SP); parallel to base.locs.
	pub cat: Vec<F>,
	/// predecessor id in Q_m step i-1 (carry/FP cert); parallel to base.locs.
	pub prev_id1: Vec<F>,
	/// lower predecessor loc (carry reach / FP lower bracket); par to locs.
	pub prev_loc1: Vec<F>,
	/// upper predecessor loc (FP upper bracket, id1+1); par to locs.
	pub prev_loc2: Vec<F>,
	/// MIN carried loc at step i+1 (BP cert); per-item scalar.
	pub min_next: F,
	/// freeze threshold fz(subsig, step) from DB (SP cert); per-item scalar.
	pub fz: F,
	/// LEN = per-subsig carried queue length (SP freeze test); per-item.
	pub queue_len: F,
}

impl<F: PrimeField + ColEle> StepQueueItemNeo<F> {
	/// wrap a base item with zeroed attributes (attrs recomputed in-chunk).
	pub fn from_base(base: StepQueueItem<F>) -> Self {
		let n = base.locs.len();
		let z = F::zero();
		Self {
			cat: vec![z; n], prev_id1: vec![z; n],
			prev_loc1: vec![z; n], prev_loc2: vec![z; n],
			min_next: z, fz: z, queue_len: z, base,
		}
	}
}

/// Constant-queue step queue (paper App G.1). Mirrors StepQueue's non-item
/// fields; store_items holds neo items. Carry (A) crosses the fold; the full
/// attribute set (B) is within-chunk advice only.
#[derive(Clone, Debug, PartialEq)]
pub struct StepQueueNeo<F: PrimeField + ColEle> {
	pub b_igc: bool,
	pub subsigs: Vec<F>,
	pub store_items: HashMap<F, Vec<StepQueueItemNeo<F>>>,
	pub capacity: DischargeAdvCapacity,
	pub q_type: StepQueueType,
}

impl<F: PrimeField + ColEle> StepQueueNeo<F> {
	// ---------- (A) carry: byte-identical to standard StepQueue ----------

	/// project down to a plain StepQueue (drops neo attributes).
	pub fn to_stepqueue(&self) -> StepQueue<F> {
		let store_items = self.store_items.iter().map(|(k, v)|
			(*k, v.iter().map(|it| it.base.clone()).collect())
		).collect::<HashMap<F, Vec<StepQueueItem<F>>>>();
		StepQueue {
			b_igc: self.b_igc, subsigs: self.subsigs.clone(),
			store_items, capacity: self.capacity.clone(),
			q_type: self.q_type.clone(),
		}
	}

	/// wrap a plain StepQueue as neo with zeroed attributes.
	pub fn from_stepqueue(sq: StepQueue<F>) -> Self {
		let store_items = sq.store_items.into_iter().map(|(k, v)|
			(k, v.into_iter().map(StepQueueItemNeo::from_base).collect())
		).collect::<HashMap<F, Vec<StepQueueItemNeo<F>>>>();
		Self {
			b_igc: sq.b_igc, subsigs: sq.subsigs, store_items,
			capacity: sq.capacity, q_type: sq.q_type,
		}
	}

	/// (A) carry vec size == standard StepQueue size (fold width unchanged).
	pub fn carry_vec_size(q_type: &StepQueueType,
		capacity: &DischargeAdvCapacity) -> (usize, usize, usize) {
		StepQueue::<F>::vec_size(q_type, capacity)
	}

	/// (A) serialize carry set; identical bytes to StepQueue::to_vec.
	pub fn to_carry_vec(&self, info: &SubsigStepStore)
		-> Result<Vec<F>, Error> {
		self.to_stepqueue().to_vec(info)
	}

	/// (A) parse carried-in vec (attributes recomputed in-chunk).
	pub fn parse_carry(vec: &Vec<F>, q_type: StepQueueType,
		capacity: &DischargeAdvCapacity, b_igc: bool) -> Self {
		Self::from_stepqueue(
			StepQueue::parse_from(vec, q_type, capacity, b_igc))
	}

	// ---------- (B) full advice: neo-internal flat table ----------

	/// (B) full advice table is ALWAYS ResLarge-sized (Q_m/Q_r);
	/// independent of self.q_type. Length = N_NEO_COLS * n_m.
	pub fn full_vec_size(capacity: &DischargeAdvCapacity) -> usize {
		let (n, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResLarge, capacity);
		N_NEO_COLS * n
	}

	/// Q_c carry size (encoded+locs cols), ResSmall = the legacy
	/// compute_sig seed sizing; what carry_only().to_vec emits.
	pub fn qc_vec_size(capacity: &DischargeAdvCapacity) -> usize {
		let (n, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResSmall, capacity);
		2 * n
	}

	/// (B) serialize base + attrs as N_NEO_COLS columns of length n,
	/// concatenated. Per-item scalars replicated per row; tail padded with
	/// dummy (encoded 0) rows. CapErr if rows exceed n (n = ResLarge).
	pub fn to_full_vec(&self,
		capacity: &DischargeAdvCapacity) -> Result<Vec<F>, Error> {
		let (n, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResLarge, capacity);
		let mut cols: Vec<Vec<F>> = vec![Vec::new(); N_NEO_COLS];
		let mut subsigs = self.subsigs.clone();
		subsigs.sort();
		for subsig in &subsigs {
			let mut items = self.store_items.get(subsig).unwrap().clone();
			items.sort_by(|a, b|
				a.base.step.partial_cmp(&b.base.step).unwrap());
			for it in &items {
				for j in 0..it.base.locs.len() {
					cols[0].push(it.base.encoded);
					cols[1].push(it.base.locs[j]);
					cols[2].push(it.cat[j]);
					cols[3].push(it.prev_id1[j]);
					cols[4].push(it.prev_loc1[j]);
					cols[5].push(it.prev_loc2[j]);
					cols[6].push(it.min_next);
					cols[7].push(it.fz);
					cols[8].push(it.queue_len);
				}
			}
		}
		if cols[0].len() > n {
			return Err(Error::CapErr(vec![(
				"discharge_adv_neo::to_full_vec".to_string(),
				cols[0].len())]));
		}
		let z = F::zero();
		for c in cols.iter_mut() { c.resize(n, z); }
		Ok(cols.concat())
	}

	/// (B) inverse of to_full_vec; drops dummy rows, regroups per
	/// (subsig, step), sorts locs (attrs follow), rebuilds items.
	/// Result q_type is always ResLarge (the Q_m table type).
	pub fn parse_full(vec: &Vec<F>,
		capacity: &DischargeAdvCapacity, b_igc: bool) -> Self {
		assert!(vec.len() % N_NEO_COLS == 0);
		let n = vec.len() / N_NEO_COLS;
		let col = |c: usize, i: usize| vec[c * n + i];

		let mut groups: HashMap<F, (Vec<[F; 5]>, [F; 3])> = HashMap::new();
		for i in 0..n {
			let encoded = col(0, i);
			if encoded.is_zero() { continue; }
			let row = [col(1, i), col(2, i), col(3, i), col(4, i),
				col(5, i)];
			let scal = [col(6, i), col(7, i), col(8, i)];
			let e = groups.entry(encoded).or_insert((Vec::new(), scal));
			e.0.push(row);
			e.1 = scal;
		}

		let mut store_items: HashMap<F, Vec<StepQueueItemNeo<F>>> =
			HashMap::new();
		for (encoded, (mut rows, scal)) in groups {
			rows.sort_by(|a, b| a[0].partial_cmp(&b[0]).unwrap());
			let locs = rows.iter().map(|r| r[0]).collect::<Vec<F>>();
			let base = StepQueueItem::parse_from(encoded, &locs);
			let item = StepQueueItemNeo {
				cat: rows.iter().map(|r| r[1]).collect(),
				prev_id1: rows.iter().map(|r| r[2]).collect(),
				prev_loc1: rows.iter().map(|r| r[3]).collect(),
				prev_loc2: rows.iter().map(|r| r[4]).collect(),
				min_next: scal[0], fz: scal[1], queue_len: scal[2], base,
			};
			store_items.entry(item.base.subsig).or_insert(vec![])
				.push(item);
		}
		for v in store_items.values_mut() {
			v.sort_by(|a, b|
				a.base.step.partial_cmp(&b.base.step).unwrap());
		}
		let mut subsigs = store_items.keys().cloned().collect::<Vec<F>>();
		subsigs.sort();
		Self { b_igc, subsigs, store_items,
			capacity: capacity.clone(),
			q_type: StepQueueType::ResLarge }
	}

	// ---------- MIN / LEN relations (derived from CAT_C entries) --------

	/// MIN: per (subsig, step) minimum carried loc.
	pub fn derive_min(&self) -> MinRelation<F> {
		let cat_c = F::from(CAT_C);
		let mut map: HashMap<(F, F), F> = HashMap::new();
		for (subsig, items) in &self.store_items {
			for it in items {
				for j in 0..it.base.locs.len() {
					if it.cat[j] != cat_c { continue; }
					let loc = it.base.locs[j];
					let e = map.entry((*subsig, it.base.step))
						.or_insert(loc);
					if loc < *e { *e = loc; }
				}
			}
		}
		MinRelation { map }
	}

	/// LEN: per subsig max carried step (queue length).
	pub fn derive_len(&self) -> LenRelation<F> {
		let cat_c = F::from(CAT_C);
		let mut map: HashMap<F, F> = HashMap::new();
		for (subsig, items) in &self.store_items {
			for it in items {
				if !it.cat.iter().any(|c| *c == cat_c) { continue; }
				let e = map.entry(*subsig).or_insert(it.base.step);
				if it.base.step > *e { *e = it.base.step; }
			}
		}
		LenRelation { map }
	}

	// ---------- M5 shared core: merge -> closure -> BP -> certs ---------

	/// G.1 shared core over one chunk. self = carried queue (attrs
	/// ignored); pat_loc = this chunk's matches; returns tagged Q_m.
	pub fn gen_shared_core_advice(&self, job_id: usize,
		pat_loc: &Arc<Mutex<Container<F>>>, info: &SubsigStepStore,
		default_min_loc: F) -> Result<StepQueueNeo<F>, Error> {
		let hm_loc = StepQueue::<F>::pat_loc_to_hm(pat_loc);
		self.gen_shared_core_from_hm(job_id, &hm_loc, info,
			default_min_loc)
	}

	/// core of gen_shared_core_advice on the pat->locs map directly
	/// (entries keep the two dummy wrap rows, like pat_loc_to_hm).
	/// NOTE (backward subsigs): the BP walk applies the LEGACY
	/// forward-direction condition (loc + rg_end < min) uniformly,
	/// mirroring gen_backward_prf, which has no is_backward branch
	/// either. That condition is directionally wrong for a reversed
	/// (keyword-first) chain, but it is never load-bearing: backward
	/// subsigs exist only in AGGRESSIVE mode, and aggressive
	/// emission retags BP->C (gen_qm_table), so no BP decision on a
	/// backward subsig ever reaches the circuit. Kept as-is for the
	/// single shared code path + byte-oracle parity with legacy
	/// (test_m5_oracle_backward).
	pub fn gen_shared_core_from_hm(&self, job_id: usize,
		hm_loc: &HashMap<F, Vec<(F, F)>>, info: &SubsigStepStore,
		default_min_loc: F) -> Result<StepQueueNeo<F>, Error> {
		let max_val: usize = (1 << read_global_config().range2_bit) - 1;
		let (zero, one) = (F::zero(), F::one());
		let f_max = F::from(max_val as u32);
		let (f_c, f_fp, f_bp) =
			(F::from(CAT_C), F::from(CAT_FP), F::from(CAT_BP));

		let mut store_items: HashMap<F, Vec<StepQueueItemNeo<F>>> =
			HashMap::new();
		for subsig in &self.subsigs {
			let u_subsig = field_to_usize(subsig);
			let rec = info.subsig_to_steps.get(&u_subsig).expect(
				&format!("no step info for subsig {}", subsig));
			let max_steps = rec.vec_pm_bounds.len();
			let reversed_pm;
			let pm_bounds = if rec.is_backward {
				reversed_pm = reverse_pm_bounds(
					&rec.vec_pm_bounds, (0, max_val));
				&reversed_pm
			} else { &rec.vec_pm_bounds };
			let fz = fz_from_pm_bounds::<F>(pm_bounds, max_val);
			let carried = self.store_items.get(subsig).unwrap();
			let seed = &carried[0].base;
			assert!(seed.locs.len() == 1 && seed.step == zero
				&& seed.locs[0] == one);

			//1. MERGE: Q_m = Q_i union (S join db join L): per step,
			// carried locs + ALL chunk matches of that step's pat.
			let mut merged: Vec<Vec<F>> = vec![vec![one]];
			for i in 1..=max_steps {
				let pat = F::from(pm_bounds[i - 1].0 as u32);
				let mut locs: Vec<F> = if i < carried.len() {
					carried[i].base.locs.clone()} else {vec![]};
				if let Some(v) = hm_loc.get(&pat) {
					//strip the two dummy wrap entries (0/max)
					locs.extend(v[1..v.len() - 1].iter()
						.map(|e| e.1));
				}
				let mut locs = locs.into_iter()
					.collect::<HashSet<F>>()
					.into_iter().collect::<Vec<F>>();
				locs.sort();
				merged.push(locs);
			}
			while merged.len() > carried.len()
				&& merged[merged.len() - 1].is_empty() {
				merged.pop();
			}
			let last_step = merged.len() - 1;

			//2. CLOSURE ASC: reachable iff covered by a reachable
			// prev row's window; roots = seed. Unreachable => FP w/
			// Q_r-local bracket (missing side = 0 sentinel).
			let mut cat: Vec<Vec<F>> = merged.iter()
				.map(|v| vec![zero; v.len()]).collect();
			let mut p_id1 = cat.clone();
			let mut p_lc1 = cat.clone();
			let mut p_lc2 = cat.clone();
			cat[0][0] = f_c;
			//reach[i] = step-i non-FP rows as (loc, qm_idx)
			let mut reach: Vec<Vec<(F, usize)>> = vec![vec![(one, 0)]];
			for i in 1..=last_step {
				let (a, b) = (pm_bounds[i - 1].1.0,
					pm_bounds[i - 1].1.1);
				let (f_a, f_b) =
					(F::from(a as u32), F::from(b as u32));
				let b_bwd = rec.is_backward && i >= 2;
				let prev = &reach[i - 1];
				//window of prev row u (fwd: [u+a, min(u+b,max-1)];
				// bwd: [u-b, u-a]); monotone in u either way.
				let win = |u: F| -> (F, F) {
					if b_bwd { (u - f_b, u - f_a) }
					else {
						let hi = u + f_b;
						(u + f_a,
						 if hi >= f_max {f_max - one} else {hi})
					}
				};
				for (j, loc) in merged[i].iter().enumerate() {
					let mut hit = None;
					for (k, (u, _)) in prev.iter().enumerate() {
						let (lo, hi) = win(*u);
						if *loc >= lo && *loc <= hi {
							hit = Some(k); break;
						}
					}
					if let Some(k) = hit {
						p_id1[i][j] = F::from(k as u32);
						p_lc1[i][j] = prev[k].0;
					} else {
						cat[i][j] = f_fp;
						//p1 = last row reaching short of loc;
						//p2 = its successor (starts beyond).
						let mut k1 = None;
						for (k, (u, _)) in prev.iter()
							.enumerate() {
							let (_lo, hi) = win(*u);
							if hi < *loc { k1 = Some(k); }
							else { break; }
						}
						if let Some(k) = k1 {
							p_id1[i][j] = F::from(k as u32);
							p_lc1[i][j] = prev[k].0;
							if k + 1 < prev.len() {
								p_lc2[i][j] = prev[k + 1].0;
							}
						} else if !prev.is_empty() {
							//below-first: upper row only
							p_lc2[i][j] = prev[0].0;
						}
					}
				}
				let rl = merged[i].iter().enumerate()
					.filter(|(j, _)| cat[i][*j] != f_fp)
					.map(|(j, l)| (*l, j))
					.collect::<Vec<(F, usize)>>();
				reach.push(rl);
			}

			//3. BP DESC (legacy gen_backward_prf semantics): start
			// at last_step+1 w/ default_min when under max_steps;
			// min = map_or(default_min); prune loc+rg_end(src)<min;
			// BREAK on first empty to_del; step 0 never pruned.
			let mut surv: Vec<Vec<F>> = (0..=last_step).map(|i|
				merged[i].iter().enumerate()
					.filter(|(j, _)| cat[i][*j] != f_fp)
					.map(|(_, l)| *l).collect()).collect();
			//BP walk anchor = the legacy queue's last step, NOT
			//Q_m's: reachability chains, so trailing steps whose
			//rows are ALL FP never exist in the legacy fwd result;
			//anchoring there would place the walk start on an empty
			//surv layer and break the cascade instantly.
			let mut r_last = 0usize;
			for i in 0..=last_step {
				if !reach[i].is_empty() { r_last = i; }
			}
			let l_anchor = if carried.len() - 1 > r_last
				{carried.len() - 1} else {r_last};
			let b_added = l_anchor < max_steps;
			let start = if b_added {l_anchor + 1} else {l_anchor};
			for src in (2..=start).rev() {
				let min_loc = if src > l_anchor {default_min_loc}
					else {
						surv[src].iter().cloned().min()
							.map_or(default_min_loc, |x| x)
					};
				let rg_end =
					F::from(pm_bounds[src - 1].1.1 as u32);
				let mut kept = vec![];
				let mut del = 0usize;
				for l in &surv[src - 1] {
					if *l + rg_end < min_loc { del += 1; }
					else { kept.push(*l); }
				}
				if del == 0 { break; }
				surv[src - 1] = kept;
			}
			for i in 1..=last_step {
				let sv = surv[i].iter().cloned()
					.collect::<HashSet<F>>();
				for j in 0..merged[i].len() {
					if cat[i][j] == f_fp { continue; }
					cat[i][j] = if sv.contains(&merged[i][j])
						{f_c} else {f_bp};
				}
			}

			//4. assemble neo items (scalars filled by post-pass)
			let mut its: Vec<StepQueueItemNeo<F>> = vec![];
			let mut it0 = StepQueueItemNeo::from_base(seed.clone());
			it0.cat[0] = f_c;
			its.push(it0);
			for i in 1..=last_step {
				let (pat, (a, b)) =
					(pm_bounds[i - 1].0, pm_bounds[i - 1].1);
				let base = StepQueueItem::new(*subsig,
					F::from(i as u32), F::from(pat as u32),
					F::from(a as u32), F::from(b as u32),
					merged[i].clone());
				let mut it = StepQueueItemNeo::from_base(base);
				it.cat = cat[i].clone();
				it.prev_id1 = p_id1[i].clone();
				it.prev_loc1 = p_lc1[i].clone();
				it.prev_loc2 = p_lc2[i].clone();
				it.fz = fz[i - 1];
				its.push(it);
			}
			store_items.insert(*subsig, its);
		}

		let mut res = StepQueueNeo {
			b_igc: self.b_igc, subsigs: self.subsigs.clone(),
			store_items, capacity: self.capacity.clone(),
			q_type: StepQueueType::ResLarge,
		};
		//scalars via the relations (same post-pass as the fixture);
		//empty next-C falls back to default_min (legacy map_or).
		let (minr, lenr) = (res.derive_min(), res.derive_len());
		for its in res.store_items.values_mut() {
			for it in its.iter_mut() {
				it.min_next = minr.get(it.base.subsig,
					it.base.step + F::one())
					.unwrap_or(default_min_loc);
				it.queue_len = lenr.get(it.base.subsig)
					.unwrap_or(F::zero());
			}
		}
		//PERF 61080: .1 Q_m saturation, .3 busiest-step raw peak
		//(.2 Q_c is logged by the carry consumer in M6).
		let (n_cap, _, _) = Self::carry_vec_size(
			&StepQueueType::ResLarge, &self.capacity);
		let mut rows = 0usize;
		let mut peak = 0usize;
		let mut per_step: HashMap<F, usize> = HashMap::new();
		for its in res.store_items.values() {
			for it in its {
				rows += it.base.locs.len();
				let e = per_step.entry(it.base.step).or_insert(0);
				*e += it.base.locs.len();
				if *e > peak { peak = *e; }
			}
		}
		log(job_id, LOG3, &format!(
			"PERF 61080.1 qm_rows={} qm_cap={} sat_pm={}",
			rows, n_cap, rows * 1000 / n_cap.max(1)));
		log(job_id, LOG3,
			&format!("PERF 61080.3 step_peak={}", peak));
		Ok(res)
	}

	/// keep only rows whose cat is in `keep`; emptied items are
	/// retained so step contiguity matches the legacy carried queue.
	fn filter_cats(&self, keep: &[u32]) -> StepQueueNeo<F> {
		let ks = keep.iter().map(|c| F::from(*c))
			.collect::<Vec<F>>();
		let store_items = self.store_items.iter().map(|(k, its)| {
			let v = its.iter().map(|it| {
				let idx = (0..it.base.locs.len())
					.filter(|j| ks.contains(&it.cat[*j]))
					.collect::<Vec<usize>>();
				let mut base = it.base.clone();
				base.locs = idx.iter()
					.map(|j| it.base.locs[*j]).collect();
				StepQueueItemNeo {
					cat: idx.iter().map(|j| it.cat[*j])
						.collect(),
					prev_id1: idx.iter()
						.map(|j| it.prev_id1[*j]).collect(),
					prev_loc1: idx.iter()
						.map(|j| it.prev_loc1[*j]).collect(),
					prev_loc2: idx.iter()
						.map(|j| it.prev_loc2[*j]).collect(),
					min_next: it.min_next, fz: it.fz,
					queue_len: it.queue_len, base,
				}
			}).collect::<Vec<_>>();
			(*k, v)
		}).collect::<HashMap<_, _>>();
		StepQueueNeo { b_igc: self.b_igc,
			subsigs: self.subsigs.clone(), store_items,
			capacity: self.capacity.clone(),
			q_type: self.q_type.clone() }
	}

	/// Q_r = sigma_{cat in {C,BP,SP}}: the reachable rows (positive
	/// list, paper Q_r = Q_m \ Q_fp). SP rows are reachable -- they
	/// are dropped as redundant, not dead.
	pub fn to_qr(&self) -> StepQueueNeo<F> {
		self.filter_cats(&[CAT_C, CAT_BP, CAT_SP])
	}

	/// Q_c = sigma_{cat==C} tight carry crossing the fold (legacy
	/// ResSmall / compute_sig seed layout).
	pub fn carry_only(&self) -> StepQueue<F> {
		let mut sq = self.filter_cats(&[CAT_C]).to_stepqueue();
		sq.q_type = StepQueueType::ResSmall;
		sq
	}

	/// SINGLETON-PRUNING pass (paper C.1, NON-AGGRESSIVE only): run
	/// AFTER gen_shared_core_from_hm on its {C,FP,BP} output. Per
	/// subsig, len = deepest step holding a C row; a step is FROZEN
	/// iff len >= fz(step) (fz=0 singleton => always frozen). At a
	/// frozen step every C row except the MINIMUM is demoted to SP:
	/// the kept min dominates (paper "Certificates"), and pinning
	/// the min is what stops a prover raising downstream minimums.
	/// Scalars (min_next/queue_len) stay valid: SP never demotes a
	/// step's min, so derive_min/derive_len are unchanged.
	///
	/// EXAMPLE (Fig-14 chunk 2): post-BP C steps are 1..5 => len=5;
	/// step 2 has fz=5 (downstream singleton a5) => frozen; its C
	/// rows {21, 111} keep min 21, demote 111 -> SP. Steps 3,4
	/// (fz=5, single C row) are no-ops; steps 1,5 (fz=0) keep their
	/// single min.
	pub fn apply_sp_pass(&mut self, info: &SubsigStepStore) {
		let max_val: usize =
			(1 << read_global_config().range2_bit) - 1;
		let (f_c, f_sp) = (F::from(CAT_C), F::from(CAT_SP));
		let lenr = self.derive_len();
		for (subsig, items) in self.store_items.iter_mut() {
			let len = lenr.get(*subsig).unwrap_or(F::zero());
			let u_subsig = field_to_usize(subsig);
			let rec = info.subsig_to_steps.get(&u_subsig).expect(
				&format!("no step info for subsig {}", subsig));
			let reversed_pm;
			let pm = if rec.is_backward {
				reversed_pm = reverse_pm_bounds(
					&rec.vec_pm_bounds, (0, max_val));
				&reversed_pm
			} else { &rec.vec_pm_bounds };
			let fz = fz_from_pm_bounds::<F>(pm, max_val);
			for it in items.iter_mut() {
				let step = field_to_usize(&it.base.step);
				if step == 0 { continue; } //seed never demoted
				it.fz = fz[step - 1];
				if len < it.fz { continue; } //not frozen
				//frozen: demote all C rows above the min
				let min = (0..it.base.locs.len())
					.filter(|j| it.cat[*j] == f_c)
					.map(|j| it.base.locs[j]).min();
				let min = match min { Some(m) => m,
					None => continue }; //no C row at this step
				for j in 0..it.base.locs.len() {
					if it.cat[j] == f_c
						&& it.base.locs[j] != min {
						it.cat[j] = f_sp;
					}
				}
			}
		}
	}
}

/// Per-step fz from pm_bounds (mirrors clam_db gen_fz_col): a step is
/// singleton iff the next step's rg_end==max (terminal included);
/// fz=0 for singletons, else id1 of closest downstream singleton.
fn fz_from_pm_bounds<F: PrimeField>(
	pm_bounds: &Vec<(usize, (usize, usize))>, max_val: usize) -> Vec<F> {
	let k = pm_bounds.len();
	let mut fz = vec![F::zero(); k];
	let mut last_sing = F::zero();
	for i in (0..k).rev() {
		let sing = i + 1 >= k || pm_bounds[i + 1].1.1 == max_val;
		if sing { last_sing = F::from((i + 1) as u32); }
		else { fz[i] = last_sing; }
	}
	fz
}

/// MIN relation: (subsig, step) -> min carried loc.
#[derive(Clone, Debug, PartialEq)]
pub struct MinRelation<F: PrimeField + ColEle> {
	pub map: HashMap<(F, F), F>,
}
impl<F: PrimeField + ColEle> MinRelation<F> {
	pub fn get(&self, subsig: F, step: F) -> Option<F> {
		self.map.get(&(subsig, step)).cloned()
	}
}

/// LEN relation: subsig -> queue length (max carried step).
#[derive(Clone, Debug, PartialEq)]
pub struct LenRelation<F: PrimeField + ColEle> {
	pub map: HashMap<F, F>,
}
impl<F: PrimeField + ColEle> LenRelation<F> {
	pub fn get(&self, subsig: F) -> Option<F> {
		self.map.get(&subsig).cloned()
	}
}

// ============================================================
//   M6: aggressive {C,FP} cert layer -- T_qm synthesis (native)
// ============================================================

/// NON-AGGRESSIVE witness columns of T_qm (paper C.1 full 4-class
/// partition). One field on QmTable; stays Default (all vecs empty)
/// under aggressive and is never emitted there, so the aggressive
/// statement is byte-identical to M6. Filled by fill_nonaggr_cols
/// AFTER gen_qm_table; every vec is row-parallel to QmTable.enc.
///
/// EXAMPLE (Fig-14 chunk 2, default_min=161): BP row a6:73 gets
/// enc_next=enc(step7), rg2_next=9, w_next=max (step 7 carries
/// nothing) => min_eff=161, d_bp=161-73-9-1=78. SP row a2:111 gets
/// fz=5, enc_fz=enc(step5), w_fz=39 (a5 carries), w_sp=21 (kept min
/// at step 2), d_sp=111-21-1=89.
#[derive(Clone, Debug, PartialEq, Default)]
pub(crate) struct QmNonAggrCols<F: PrimeField + ColEle> {
	// ---- merge (union-present) ----
	/// 1 iff this row's (pat,loc) is demanded against L in the
	/// counting logup; 0 on carried-only rows. Self-enforcing: off
	/// on an L row shorts the cnt(pat) demand, on for a non-L row
	/// leaves the query unmatched.
	pub b_l: Vec<F>,
	// ---- BP certificate (loc + rg2_next < min_{i+1}) ----
	/// successor step's DB key; free advice, forced to be THE
	/// successor by the PREV_ENCODED (si,val) pair on bp_prev_val.
	pub enc_next: Vec<F>,
	/// masked copy of this row's enc under si tag(enc_next,
	/// PREV_ENCODED): the DB stores prev(enc_next)=enc, and the
	/// step chain is a path, so enc_next is unique given enc.
	pub bp_prev_val: Vec<F>,
	/// masked rg_end INTO step i+1 under si tag(enc_next, RG_END);
	/// the max sentinel (unbounded, into a singleton) makes d_bp
	/// underflow => BP structurally impossible there.
	pub rg2_next: Vec<F>,
	/// QC-lookup witness: loc of the (enc_next, cid=1) row = the
	/// least carried loc at step i+1; == max iff step i+1 carries
	/// nothing (the max-wrap is the first QC row then).
	pub w_next: Vec<F>,
	/// RANGE2 diff min_eff - loc - rg2_next - 1 where min_eff =
	/// select(w_next==max, default_min, w_next); single limb since
	/// min_eff <= max.
	pub d_bp: Vec<F>,
	// ---- SP certificate (frozen step keeps only its min) ----
	/// freeze threshold under si tag(enc, ID_ENCODED_FZ); 0 =
	/// singleton step (always frozen).
	pub fz: Vec<F>,
	/// DB key of step fz of THIS subsig. fz>=1: authenticated by
	/// the two (si,val) pairs below. fz==0: structurally pinned to
	/// the seed key subsig*2^(4*rb), whose C row always exists.
	pub enc_fz: Vec<F>,
	/// masked copy of fz under si tag(enc_fz, NORMAL|LAST STEP):
	/// proves enc_fz's step number IS fz.
	pub fz_step_val: Vec<F>,
	/// masked copy of subsig under si tag(enc_fz, SUBSIG): proves
	/// enc_fz belongs to THIS subsig (blocks borrowing another
	/// subsig's populated step-fz group).
	pub fz_sub_val: Vec<F>,
	/// QC witness: loc of the (enc_fz, cid=1) row; a real C loc
	/// proves the downstream singleton already carries (freeze
	/// condition len>=fz via C-prefix contiguity).
	pub w_fz: Vec<F>,
	/// RANGE2 diff max - w_fz - 1: fails exactly when w_fz==max,
	/// i.e. step fz carries nothing => not frozen.
	pub d_fz: Vec<F>,
	/// QC witness: loc of this row's own-group (enc, cid=1) row =
	/// the kept minimum at this step.
	pub w_sp: Vec<F>,
	/// RANGE2 diff loc - w_sp - 1 (min-domination); underflows if
	/// the prover tries to SP the minimum itself.
	pub d_sp: Vec<F>,
	// ---- carry binding ----
	/// per-row multiplicity for the carry-in logup: 1 iff this row
	/// is a carried Q_i row ({0,1}: Q_i locs are a per-step set).
	pub m_carry_in: Vec<F>,
	// ---- variable si columns (RANGE2 + val 0 when masked) ----
	/// tag(enc_next, PREV_ENCODED), masked to is_bp.
	pub si_bp_prev: Vec<F>,
	/// tag(enc_next, RG_END), masked to is_bp.
	pub si_rg2_next: Vec<F>,
	/// tag(enc, ID_ENCODED_FZ), masked to is_sp.
	pub si_fz: Vec<F>,
	/// tag(enc_fz, NORMAL|LAST STEP), masked to is_sp AND fz!=0
	/// (the seed key has no keyed cats except its step tag).
	pub si_fz_step: Vec<F>,
	/// tag(enc_fz, SUBSIG), masked to is_sp AND fz!=0.
	pub si_fz_sub: Vec<F>,
}

/// Finished T_qm statement table as parallel columns: pads first, then
/// per (subsig,step) group [0-wrap, real rows, max-wrap]. Built once
/// per chunk by gen_qm_table; consumed by gen_core_stmt and the tests.
#[derive(Clone, Debug, PartialEq, Default)]
pub(crate) struct QmTable<F: PrimeField + ColEle> {
	// core
	pub enc: Vec<F>, pub id: Vec<F>, pub loc: Vec<F>, pub cat: Vec<F>,
	pub step: Vec<F>, pub subsig: Vec<F>,
	// per-row witnesses (remapped to wrap coords at emission)
	pub prev_id1: Vec<F>, pub prev_loc1: Vec<F>, pub prev_loc2: Vec<F>,
	// store bindings (read from item.base; masked rows: 0 + RANGE2 si)
	pub pat: Vec<F>, pub rg1: Vec<F>, pub rg2: Vec<F>,
	pub enc_prev: Vec<F>, pub b_bwd: Vec<F>,
	// masked cert diffs; lo parts RANGE2-si'd, hi parts 0/1 bits
	pub d_c1: Vec<F>, pub d_c2: Vec<F>,
	pub d_below_lo: Vec<F>, pub d_below_hi: Vec<F>,
	pub d_above_lo: Vec<F>, pub d_above_hi: Vec<F>,
	/// strict-sort diff advice: loc[i]-loc[i-1]-1 on same-group
	/// adjacencies (RANGE2-si'd), 0 elsewhere.
	pub d_sort: Vec<F>,
	// si columns (variable; const RANGE2 si cols are emitted at
	// container-assembly time for the d_* advice)
	pub si_step: Vec<F>, pub si_subsig: Vec<F>, pub si_pat: Vec<F>,
	pub si_rg1: Vec<F>, pub si_rg2: Vec<F>, pub si_enc_prev: Vec<F>,
	pub si_b_bwd: Vec<F>,
	/// non-aggressive extension (empty + never emitted under
	/// aggressive); filled by fill_nonaggr_cols after gen_qm_table.
	pub nonaggr: QmNonAggrCols<F>,
	pub n_pad: usize,
}

/// Split a cert diff (honest bound < 2^(rb+1)) into (hi bit, lo) with
/// lo in [0, 2^rb): d = hi*2^rb + lo. hi is boolean-checked in-circuit;
/// lo carries the RANGE2 si.
fn split_rg2_limb<F: PrimeField + ColEle>(d: &F, max_val: usize)
-> (F, F) {
	let u = field_to_usize(d);
	let m = max_val + 1;
	if u >= m { (F::one(), F::from((u - m) as u32)) }
	else { (F::zero(), F::from(u as u32)) }
}

impl<F: PrimeField + ColEle> QmTable<F> {
	/// Append one wrap row (loc 0 or max) for group `enc`; cert and
	/// binding cols zeroed with benign si. f_bwd = the subsig's real
	/// backward flag (the (si,val) pair must exist on EVERY row).
	fn push_wrap(&mut self, enc: F, id: F, loc: F, f_step: F,
		subsig: F, b_last: bool, b_ge1: bool, f_bwd: F) {
		let (z, rg2t) = (F::zero(), F::from(RANGE2));
		let tag = if b_last { ID_ENCODED_LAST_STEP }
			else { ID_ENCODED_NORMAL_STEP };
		self.enc.push(enc); self.id.push(id); self.loc.push(loc);
		self.cat.push(z); self.step.push(f_step);
		self.subsig.push(subsig); self.b_bwd.push(f_bwd);
		for v in [&mut self.prev_id1, &mut self.prev_loc1,
			&mut self.prev_loc2, &mut self.pat, &mut self.rg1,
			&mut self.rg2, &mut self.enc_prev, &mut self.d_c1,
			&mut self.d_c2, &mut self.d_below_lo,
			&mut self.d_below_hi, &mut self.d_above_lo,
			&mut self.d_above_hi] { v.push(z); }
		self.si_step.push(SubsigStepStore::gen_step_tbl_id(enc, tag));
		self.si_subsig.push(if b_ge1 {
			SubsigStepStore::gen_step_tbl_id(enc, ID_ENCODED_SUBSIG)
		} else { rg2t });
		for v in [&mut self.si_pat, &mut self.si_rg1,
			&mut self.si_rg2, &mut self.si_enc_prev] { v.push(rg2t); }
		self.si_b_bwd.push(F::from(1u64 << 32)
			* F::from(ID_SUBSIG_IS_BACKWARD) + subsig);
	}

	/// Append one real row from item `it`, loc index k. Derives the
	/// witness remaps, base bindings and cert diffs. bwd = mirrored
	/// window (backward subsig AND step>=2). Mode split (b_aggr):
	///  - aggressive: BP->C retag (forward-only, no BP class) and
	///    C-cert witnesses from the closure advice -- M6 unchanged.
	///  - non-aggressive: all four cats kept as tagged; C/BP/SP rows
	///    get ZEROED prev_*/d_c* here, because fill_nonaggr_cols
	///    re-picks the C predecessor against the FINAL C sets (an
	///    SP pass may demote the closure-time pred) and re-ranks
	///    prev_id1 in QC coordinates. FP rows are identical in both
	///    modes (QR brackets are unaffected by SP: Q_r keeps SP).
	fn push_real(&mut self, it: &StepQueueItemNeo<F>, k: usize,
		f_step: F, b_last: bool, bwd: bool, enc_prev: F, f_bwd: F,
		max_val: usize, b_aggr: bool) {
		let (z, one) = (F::zero(), F::one());
		let f_max = F::from(max_val as u32);
		let enc = it.base.encoded;
		let (loc, pl1) = (it.base.locs[k], it.prev_loc1[k]);
		let c0 = it.cat[k];
		if b_aggr {
			assert!(c0 == F::from(CAT_C) || c0 == F::from(CAT_FP)
				|| c0 == F::from(CAT_BP),
				"aggr: unexpected cat");
		} else {
			assert!(c0 == F::from(CAT_C) || c0 == F::from(CAT_FP)
				|| c0 == F::from(CAT_BP)
				|| c0 == F::from(CAT_SP),
				"nonaggr: unexpected cat");
		}
		let cat = if b_aggr && c0 == F::from(CAT_BP)
			{ F::from(CAT_C) } else { c0 };
		let b_seed = it.base.step.is_zero();
		assert!(!(b_seed && cat != F::from(CAT_C)));
		//witness policy: FP always carries its bracket; C carries
		//its closure pred only in aggressive (nonaggr re-picked in
		//fill_nonaggr_cols); BP/SP carry nothing here.
		let b_fp = cat == F::from(CAT_FP);
		let b_keep_prev = b_fp || (b_aggr && cat == F::from(CAT_C));
		// remaps: +1 wrap-coord shift iff a real lower pred; FP
		// "no upper row" 0-sentinel -> max (targets the max-wrap).
		let pl1 = if b_keep_prev { pl1 } else { z };
		let p1 = if !b_keep_prev || pl1.is_zero() { z }
			else { it.prev_id1[k] + one };
		let pl2 = if b_fp && it.prev_loc2[k].is_zero() { f_max }
			else if b_fp { it.prev_loc2[k] }
			else { z };
		self.enc.push(enc); self.id.push(F::from((k + 1) as u32));
		self.loc.push(loc); self.cat.push(cat); self.step.push(f_step);
		self.subsig.push(it.base.subsig); self.b_bwd.push(f_bwd);
		self.prev_id1.push(p1); self.prev_loc1.push(pl1);
		self.prev_loc2.push(pl2);
		let (f_p, f_a, f_b) = if b_seed { (z, z, z) } else {
			(it.base.pat, it.base.rg_start, it.base.rg_end) };
		self.pat.push(f_p); self.rg1.push(f_a); self.rg2.push(f_b);
		self.enc_prev.push(if b_seed { z } else { enc_prev });
		// masked cert diffs (0 off-class / on seed)
		let (mut dc1, mut dc2) = (z, z);
		let (mut dbl, mut dbh, mut dal, mut dah) = (z, z, z, z);
		if !b_seed && b_aggr && cat == F::from(CAT_C) {
			let gap = if bwd { pl1 - loc } else { loc - pl1 };
			dc1 = gap - f_a; dc2 = f_b - gap;
		}
		if cat == F::from(CAT_FP) {
			if !pl1.is_zero() {
				let d = if bwd { loc + f_a - pl1 - one }
					else { loc - pl1 - f_b - one };
				let (h, l) = split_rg2_limb(&d, max_val);
				dbh = h; dbl = l;
			}
			if pl2 != f_max {
				let d = if bwd { pl2 - loc - f_b - one }
					else { pl2 + f_a - loc - one };
				let (h, l) = split_rg2_limb(&d, max_val);
				dah = h; dal = l;
			}
		}
		self.d_c1.push(dc1); self.d_c2.push(dc2);
		self.d_below_lo.push(dbl); self.d_below_hi.push(dbh);
		self.d_above_lo.push(dal); self.d_above_hi.push(dah);
		// si tags: step always; store cats masked on the seed row
		let rg2t = F::from(RANGE2);
		let tag = if b_last { ID_ENCODED_LAST_STEP }
			else { ID_ENCODED_NORMAL_STEP };
		let m = |b: bool, cid: u32| if b {
			SubsigStepStore::gen_step_tbl_id(enc, cid) } else { rg2t };
		self.si_step.push(SubsigStepStore::gen_step_tbl_id(enc, tag));
		self.si_subsig.push(m(!b_seed, ID_ENCODED_SUBSIG));
		self.si_pat.push(m(!b_seed, ID_ENCODED_PAT));
		self.si_rg1.push(m(!b_seed, ID_ENCODED_RG_START));
		self.si_rg2.push(m(!b_seed, ID_ENCODED_RG_END));
		self.si_enc_prev.push(m(!b_seed, ID_ENCODED_PREV_ENCODED));
		self.si_b_bwd.push(F::from(1u64 << 32)
			* F::from(ID_SUBSIG_IS_BACKWARD) + it.base.subsig);
	}

	/// Prepend n all-zero pad rows. si_step gets the subsig-0 dummy
	/// tag (legacy convention) and si_b_bwd the subsig-0 flag key, so
	/// pad (si,value) pairs exist in the global lookup.
	fn pad_front(&mut self, n: usize) {
		let (z, rg2t) = (F::zero(), F::from(RANGE2));
		let sid_step = SubsigStepStore::gen_step_tbl_id(
			z, ID_ENCODED_LAST_STEP);
		let sid_bwd = F::from(1u64 << 32)
			* F::from(ID_SUBSIG_IS_BACKWARD);
		let pz = |v: &mut Vec<F>, x: F| {
			let mut w = vec![x; n]; w.append(v); *v = w; };
		for v in [&mut self.enc, &mut self.id, &mut self.loc,
			&mut self.cat, &mut self.step, &mut self.subsig,
			&mut self.prev_id1, &mut self.prev_loc1,
			&mut self.prev_loc2, &mut self.pat, &mut self.rg1,
			&mut self.rg2, &mut self.enc_prev, &mut self.b_bwd,
			&mut self.d_c1, &mut self.d_c2, &mut self.d_below_lo,
			&mut self.d_below_hi, &mut self.d_above_lo,
			&mut self.d_above_hi, &mut self.d_sort] { pz(v, z); }
		pz(&mut self.si_step, sid_step);
		for v in [&mut self.si_subsig, &mut self.si_pat,
			&mut self.si_rg1, &mut self.si_rg2,
			&mut self.si_enc_prev] { pz(v, rg2t); }
		pz(&mut self.si_b_bwd, sid_bwd);
		//nonaggr cols need no handling here: fill_nonaggr runs on
		//the ALREADY-PADDED table and allocates full-length vecs
		//(pad rows get masked defaults there).
		self.n_pad = n;
	}

	/// Fill the NON-AGGRESSIVE witness columns on the PADDED table
	/// (run right after gen_qm_table(.., false)). Three jobs:
	///  (1) merge bits: b_l (row demanded against L) and m_carry_in
	///      (row is a carried Q_i row) -- a duplicate (carried AND
	///      matched again) legitimately gets both;
	///  (2) C rows: RE-PICK the predecessor against the FINAL C
	///      sets and re-rank prev_id1 in QC coordinates. Needed
	///      because apply_sp_pass may demote the closure-time pred:
	///      at a frozen step only the min survives, and the min
	///      always reaches (min-chain lemma), so a C pred exists.
	///      EXAMPLE: a3:27 closure pred was a2:21; had it been 111
	///      (now SP), the re-pick lands on the kept min 21, rank 1.
	///  (3) BP/SP rows: successor/freeze witnesses (see the
	///      QmNonAggrCols field docs for the certificates).
	/// PARAMS: hm_loc = chunk L map pat -> [(id,loc)] WITH the two
	/// wrap rows (pat_loc_to_hm layout); carried = this chunk's Q_i
	/// (the fold input); default_min = last_loc + 1.
	pub(crate) fn fill_nonaggr(&mut self, info: &SubsigStepStore,
		hm_loc: &HashMap<F, Vec<(F, F)>>, carried: &StepQueue<F>,
		default_min: F) {
		let n = self.enc.len();
		let rb = read_global_config().range2_bit;
		let max_val: usize = (1 << rb) - 1;
		let f_max = F::from(max_val as u32);
		let (z, one, rg2t) = (F::zero(), F::one(), F::from(RANGE2));
		let (f_c, f_bp, f_sp) =
			(F::from(CAT_C), F::from(CAT_BP), F::from(CAT_SP));
		//0. masked defaults on every row (pads/wraps stay so)
		self.nonaggr = QmNonAggrCols {
			b_l: vec![z; n], enc_next: vec![z; n],
			bp_prev_val: vec![z; n], rg2_next: vec![z; n],
			w_next: vec![z; n], d_bp: vec![z; n], fz: vec![z; n],
			enc_fz: vec![z; n], fz_step_val: vec![z; n],
			fz_sub_val: vec![z; n], w_fz: vec![z; n],
			d_fz: vec![z; n], w_sp: vec![z; n], d_sp: vec![z; n],
			m_carry_in: vec![z; n],
			si_bp_prev: vec![rg2t; n], si_rg2_next: vec![rg2t; n],
			si_fz: vec![rg2t; n], si_fz_step: vec![rg2t; n],
			si_fz_sub: vec![rg2t; n],
		};
		//1. group indices off the finished table: (subsig,step)->enc
		//   (every group exists: gen_qm_table wraps ALL steps) and
		//   enc -> its C locs in ascending order.
		let mut enc_of: HashMap<(F, F), F> = HashMap::new();
		let mut c_locs: HashMap<F, Vec<F>> = HashMap::new();
		for i in self.n_pad..n {
			enc_of.insert((self.subsig[i], self.step[i]),
				self.enc[i]);
			if self.cat[i] == f_c {
				c_locs.entry(self.enc[i]).or_insert(vec![])
					.push(self.loc[i]); //rows loc-sorted in-group
			}
		}
		//first QC loc of a group = least C loc, or the max-wrap
		//when the step carries nothing (cid-1 row either way).
		let qc1 = |enc: &F| -> F {
			c_locs.get(enc).map_or(f_max, |v| v[0])
		};
		//2. membership sets for the merge bits
		let mut in_l: HashSet<(F, F)> = HashSet::new();
		for (p, v) in hm_loc {
			for e in &v[1..v.len() - 1] { in_l.insert((*p, e.1)); }
		}
		let mut in_qi: HashSet<(F, F)> = HashSet::new();
		for its in carried.store_items.values() {
			for it in its {
				for l in &it.locs {
					in_qi.insert((it.encoded, *l));
				}
			}
		}
		//3. per-subsig step metadata (non-aggr = forward-only)
		let mut meta: HashMap<F, Vec<(usize, (usize, usize))>> =
			HashMap::new();
		for i in self.n_pad..n {
			let subsig = self.subsig[i];
			if subsig.is_zero() || meta.contains_key(&subsig)
				{ continue; }
			let rec = info.subsig_to_steps
				.get(&field_to_usize(&subsig)).expect(
				&format!("no step info for subsig {}", subsig));
			assert!(!rec.is_backward,
				"nonaggr has no backward subsigs");
			meta.insert(subsig, rec.vec_pm_bounds.clone());
		}
		//4. row pass
		for i in self.n_pad..n {
			let cat = self.cat[i];
			if cat.is_zero() { continue; } //wrap sentinel rows
			let (subsig, loc) = (self.subsig[i], self.loc[i]);
			let step = field_to_usize(&self.step[i]);
			//(1) merge bits (any class; seed rows are neither)
			if step >= 1 && in_l.contains(&(self.pat[i], loc)) {
				self.nonaggr.b_l[i] = one;
			}
			if in_qi.contains(&(self.enc[i], loc)) {
				self.nonaggr.m_carry_in[i] = one;
			}
			if step == 0 { continue; } //seed: no certificate
			let pm = &meta[&subsig];
			//(2) C re-pick: least final-C loc at step-1 inside the
			//predecessor window [loc-rg2, loc-rg1]; rank in QC
			//coordinates (0-wrap holds rank 0, C rows 1..k).
			if cat == f_c {
				let (a, b) = pm[step - 1].1;
				let ul = field_to_usize(&loc);
				let (w_lo, w_hi) =
					(ul.saturating_sub(b), ul - a);
				let empty: Vec<F> = vec![];
				let plist = c_locs.get(&self.enc_prev[i])
					.unwrap_or(&empty);
				let hit = plist.iter().enumerate().find(|(_, p)| {
					let up = field_to_usize(*p);
					up >= w_lo && up <= w_hi
				});
				let (idx, pl) = hit.expect(
					"nonaggr C row: no final-C predecessor");
				let gap = loc - *pl;
				self.prev_id1[i] = F::from((idx + 1) as u32);
				self.prev_loc1[i] = *pl;
				self.d_c1[i] = gap - F::from(a as u32);
				self.d_c2[i] = F::from(b as u32) - gap;
			}
			//(3a) BP: successor key + range + carried-min witness
			if cat == f_bp {
				let max_steps = pm.len();
				assert!(step < max_steps, "BP on terminal step");
				let enc_next =
					enc_of[&(subsig, F::from((step + 1) as u32))];
				let rg2n = pm[step].1.1; //range INTO step i+1
				debug_assert!(rg2n != max_val,
					"BP before a singleton step");
				let w = qc1(&enc_next);
				let min_eff = if w == f_max { default_min }
					else { w };
				let na = &mut self.nonaggr;
				na.enc_next[i] = enc_next;
				na.bp_prev_val[i] = self.enc[i];
				na.rg2_next[i] = F::from(rg2n as u32);
				na.w_next[i] = w;
				na.d_bp[i] = min_eff - loc
					- F::from(rg2n as u32) - one;
				na.si_bp_prev[i] = SubsigStepStore
					::gen_step_tbl_id(enc_next,
						ID_ENCODED_PREV_ENCODED);
				na.si_rg2_next[i] = SubsigStepStore
					::gen_step_tbl_id(enc_next,
						ID_ENCODED_RG_END);
			}
			//(3b) SP: freeze (C row at step fz) + min-domination
			if cat == f_sp {
				let max_steps = pm.len();
				let fzv = fz_from_pm_bounds::<F>(pm, max_val)
					[step - 1];
				let fz_us = field_to_usize(&fzv);
				let enc_fz = enc_of[&(subsig, fzv)];
				let w_fz = qc1(&enc_fz);
				let w_sp = qc1(&self.enc[i]);
				let na = &mut self.nonaggr;
				na.fz[i] = fzv;
				na.si_fz[i] = SubsigStepStore::gen_step_tbl_id(
					self.enc[i], ID_ENCODED_FZ);
				na.enc_fz[i] = enc_fz;
				if fz_us >= 1 {
					//seed key (fz==0) has no SUBSIG/step cats in
					//the DB: the circuit pins it structurally.
					let tag = if fz_us == max_steps
						{ ID_ENCODED_LAST_STEP }
						else { ID_ENCODED_NORMAL_STEP };
					na.fz_step_val[i] = fzv;
					na.si_fz_step[i] = SubsigStepStore
						::gen_step_tbl_id(enc_fz, tag);
					na.fz_sub_val[i] = subsig;
					na.si_fz_sub[i] = SubsigStepStore
						::gen_step_tbl_id(enc_fz,
							ID_ENCODED_SUBSIG);
				}
				na.w_fz[i] = w_fz;
				na.d_fz[i] = f_max - w_fz - one;
				na.w_sp[i] = w_sp;
				na.d_sp[i] = loc - w_sp - one;
			}
		}
	}
}

impl<F: PrimeField + ColEle> StepQueueNeo<F> {
	/// Number of (subsig, step 0..=max_steps) key groups over the
	/// active subsigs; each group adds exactly 2 wrap rows to T_qm.
	pub(crate) fn n_wrap_keys(subsigs: &Vec<F>,
		info: &SubsigStepStore) -> usize {
		subsigs.iter().map(|s| {
			let u = field_to_usize(s);
			info.subsig_to_steps.get(&u).map_or(0,
				|it| it.vec_pm_bounds.len() + 1)
		}).sum()
	}

	/// T_qm row budget: ResLarge real-row budget + 2 wraps per key
	/// group. Aggressive (8_C NEEDS seeding): the wrap budget is
	/// CAPACITY-ONLY -- subsigs*(avg_active+1) keys -- so the shape
	/// is chunk-invariant; n_keys ignored. Non-aggressive keeps the
	/// (run-constant) data n_keys. Exceeding = CapErr, never silent.
	/// Wrap-key budget: explicit capacity.wrap_keys, else derived
	/// subsigs*(avg_active+1).
	pub(crate) fn wrap_budget(capacity: &DischargeAdvCapacity)
	-> usize {
		if capacity.wrap_keys > 0 { capacity.wrap_keys }
		else { capacity.subsigs
			* (capacity.avg_active_pats_per_subsig + 1) }
	}

	pub(crate) fn qm_rows_size(capacity: &DischargeAdvCapacity,
		n_keys: usize) -> usize {
		let (n, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResLarge, capacity);
		let wrap = if capacity.b_aggressive {
			Self::wrap_budget(capacity)
		} else { n_keys };
		n + 2 * wrap
	}

	/// Single-pass T_qm synthesis from the shared-core output. Mode
	/// from capacity.b_aggressive: aggressive = seed-only carry,
	/// classes {C,FP} (BP retagged C); non-aggressive = the full
	/// C.1 partition {C,FP,BP,SP} kept as tagged (witness columns
	/// filled by the fill_nonaggr_cols post-pass). `info` supplies
	/// per-subsig steps/direction; result is padded to the budget.
	/// b_aggr is EXPLICIT (not capacity.b_aggressive): the tier-1
	/// harnesses drive both arms under one small test capacity.
	pub(crate) fn gen_qm_table(&self, info: &SubsigStepStore,
		b_aggr: bool)
	-> Result<QmTable<F>, Error> {
		let max_val: usize = (1 << read_global_config().range2_bit) - 1;
		let (zero, one, f_max) = (F::zero(), F::one(),
			F::from(max_val as u32));
		let mut subsigs = self.subsigs.clone();
		subsigs.sort();
		let mut t = QmTable::default();
		for subsig in &subsigs {
			let u_subsig = field_to_usize(subsig);
			let rec = info.subsig_to_steps.get(&u_subsig).expect(
				&format!("no step info for subsig: {}", subsig));
			let max_steps = rec.vec_pm_bounds.len();
			// backward subsigs: store rows follow the REVERSED
			// (keyword-first) chain; needed only to rebuild the enc
			// of steps M5 trimmed (items carry their own enc).
			let reversed_pm;
			let pm = if rec.is_backward {
				reversed_pm = reverse_pm_bounds(
					&rec.vec_pm_bounds, (0, max_val));
				&reversed_pm
			} else { &rec.vec_pm_bounds };
			let items = self.store_items.get(subsig).expect(
				&format!("no items for subsig: {}", subsig));
			assert!(!items.is_empty()
				&& items[0].base.step == zero
				&& items[0].base.locs == vec![one]); // M5 seed shape
			let f_bwd = if rec.is_backward { one } else { zero };
			let mut enc_prev = zero;
			for s in 0..max_steps + 1 {
				let enc = if s < items.len() { items[s].base.encoded }
				else {
					let (p, (a, b)) = pm[s - 1];
					encode_cols(&vec![vec![*subsig],
						vec![F::from(s as u32)],
						vec![F::from(p as u32)],
						vec![F::from(a as u32)],
						vec![F::from(b as u32)]],
						&vec![0, 1, 2, 3, 4])[0]
				};
				let f_step = F::from(s as u32);
				let (b_last, b_ge1) = (s == max_steps, s >= 1);
				t.push_wrap(enc, zero, zero, f_step, *subsig,
					b_last, b_ge1, f_bwd);
				let n_real = if s < items.len() {
					let it = &items[s];
					let bwd = rec.is_backward && s >= 2;
					for k in 0..it.base.locs.len() {
						t.push_real(it, k, f_step, b_last, bwd,
							enc_prev, f_bwd, max_val, b_aggr);
					}
					it.base.locs.len()
				} else { 0 };
				t.push_wrap(enc, F::from((n_real + 1) as u32), f_max,
					f_step, *subsig, b_last, b_ge1, f_bwd);
				enc_prev = enc;
			}
		}
		// strict-sort diff advice (before padding: pads are separate
		// groups and the circuit binding masks pad/key-change rows)
		let nrows = t.enc.len();
		t.d_sort = vec![zero; nrows];
		for i in 1..nrows {
			if t.enc[i] == t.enc[i - 1] {
				t.d_sort[i] = t.loc[i] - t.loc[i - 1] - one;
			}
		}
		// front pads + CapErr (fixed budget)
		let n_keys = Self::n_wrap_keys(&subsigs, info);
		let n_total = Self::qm_rows_size(&self.capacity, n_keys);
		if t.enc.len() > n_total {
			return Err(Error::CapErr(vec![(format!(
				"neo_qm_table, b_igc: {}", self.b_igc), t.enc.len())]));
		}
		let n_pad = n_total - t.enc.len();
		t.pad_front(n_pad);
		Ok(t)
	}

	/// Merge dictionary D: sorted (pat, cnt) over the FULL store's
	/// pat universe (all subsig chains; constant per fsm -- 8_C
	/// shape invariance) UNION L; cnt counts only the SEEDED
	/// (subsig,step) keys (0 for cold/L-only pats). An L pat outside
	/// the store universe (and not a 0/max sentinel) is CapErr.
	pub(crate) fn gen_merge_dict(subsigs: &Vec<F>,
		info: &SubsigStepStore, hm_loc: &HashMap<F, Vec<(F, F)>>,
		b_igc: bool)
	-> Result<(Vec<F>, Vec<F>), Error> {
		let mut cnt: HashMap<F, u32> = HashMap::new();
		for u in &info.subsig_ids {
			if let Some(rec) = info.subsig_to_steps.get(u) {
				for (p, _) in &rec.vec_pm_bounds {
					cnt.entry(F::from(*p as u32)).or_insert(0);
				}
			}
		}
		for subsig in subsigs {
			if subsig.is_zero() { continue; }
			let u = field_to_usize(subsig);
			let rec = info.subsig_to_steps.get(&u).unwrap();
			for (p, _) in &rec.vec_pm_bounds {
				*cnt.entry(F::from(*p as u32)).or_insert(0) += 1;
			}
		}
		let f_max = F::from(((1u64 << read_global_config()
			.range2_bit) - 1) as u32);
		for p in hm_loc.keys() {
			if !cnt.contains_key(p) && !p.is_zero() && *p != f_max {
				return Err(Error::CapErr(vec![(format!(
					"neo_dict_offstore, b_igc: {}", b_igc),
					hm_loc.len())]));
			}
			cnt.entry(*p).or_insert(0);
		}
		let mut pats = cnt.keys().cloned().collect::<Vec<F>>();
		pats.sort();
		let cnts = pats.iter().map(|p| F::from(cnt[p]))
			.collect::<Vec<F>>();
		Ok((pats, cnts))
	}

	/// Per-L-row multiplicity advice for the counting logup: cnt(pat)
	/// for real L rows, 0 for the 0/max wrap rows.
	pub(crate) fn gen_merge_m_aux(l_pat: &Vec<F>, l_loc: &Vec<F>,
		d_pat: &Vec<F>, d_cnt: &Vec<F>) -> Vec<F> {
		let max_val: usize = (1 << read_global_config().range2_bit) - 1;
		let f_max = F::from(max_val as u32);
		let hm = d_pat.iter().zip(d_cnt.iter())
			.map(|(p, c)| (*p, *c)).collect::<HashMap<F, F>>();
		l_pat.iter().zip(l_loc.iter()).map(|(p, l)| {
			if l.is_zero() || *l == f_max { F::zero() }
			else { *hm.get(p).unwrap_or(&F::zero()) }
		}).collect()
	}

	/// Aggressive verdict feed: acc = LAST_STEP encoded keys having a
	/// C row this chunk (sorted, deduped) + per-entry completeness
	/// m-table. Container names mirror legacy so compute_sig reads it
	/// unchanged.
	pub(crate) fn gen_acc_and_mtbl(t: &QmTable<F>,
		info: &SubsigStepStore) -> (Vec<F>, Vec<F>) {
		let is_term = |i: usize| -> bool {
			if t.cat[i] != F::from(CAT_C) { return false; }
			let u = field_to_usize(&t.subsig[i]);
			let num = info.subsig_to_steps.get(&u).unwrap()
				.vec_pm_bounds.len();
			// 8_A: empty-chain (seed-only) subsigs never "complete" --
			// their step-0 seed is not a terminal. Excluding them
			// matches compute_sig's inp_subsigs filter (empty-chain
			// dropped), keeping the acc membership logup balanced.
			num > 0 && field_to_usize(&t.step[i]) == num
		};
		let mut acc: Vec<F> = vec![];
		for i in t.n_pad..t.enc.len() {
			if is_term(i) && !acc.contains(&t.enc[i]) {
				acc.push(t.enc[i]);
			}
		}
		acc.sort();
		let mtbl = acc.iter().map(|e| {
			let c = (t.n_pad..t.enc.len()).filter(|&i|
				t.enc[i] == *e && is_term(i)).count();
			F::from(c as u32)
		}).collect::<Vec<F>>();
		(acc, mtbl)
	}
}

// ============================================================
//   M6: aggressive {C,FP} cert layer -- circuit side
// ============================================================

/// One in-place batched field inversion (0 -> 0); the fast path for
/// building is_zero witnesses (verify_union_prf precedent).
fn batch_inv<F: PrimeField>(v: &[F]) -> Vec<F> {
	let mut w = v.to_vec();
	batch_inversion(&mut w);
	w
}

/// Build one boolean column: out[i] = (vars[i]==0), 2cs per row.
/// `native` must hold the same values as `vars` (used only for the
/// batched inverse hints; constraints bind vars alone).
fn gen_zero_bits<F: PrimeField + ColEle>(
	cs: &ConstraintSystemRef<F>, native: &[F], vars: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
	let inv = batch_inv(native);
	(0..native.len()).map(|i|
		is_zero_better_adv(&vars[i], &inv[i], cs)).collect()
}

/// FpVar mirror of QmTable's columns (data + si); what constraints
/// act on. Allocated by tests (new_var per cell) or the gadget
/// (Container::rc_from).
pub(crate) struct QmVars<F: PrimeField + ColEle> {
	pub enc: Vec<FpVar<F>>, pub id: Vec<FpVar<F>>,
	pub loc: Vec<FpVar<F>>, pub cat: Vec<FpVar<F>>,
	pub step: Vec<FpVar<F>>, pub subsig: Vec<FpVar<F>>,
	pub prev_id1: Vec<FpVar<F>>, pub prev_loc1: Vec<FpVar<F>>,
	pub prev_loc2: Vec<FpVar<F>>, pub pat: Vec<FpVar<F>>,
	pub rg1: Vec<FpVar<F>>, pub rg2: Vec<FpVar<F>>,
	pub enc_prev: Vec<FpVar<F>>, pub b_bwd: Vec<FpVar<F>>,
	pub d_c1: Vec<FpVar<F>>, pub d_c2: Vec<FpVar<F>>,
	pub d_below_lo: Vec<FpVar<F>>, pub d_below_hi: Vec<FpVar<F>>,
	pub d_above_lo: Vec<FpVar<F>>, pub d_above_hi: Vec<FpVar<F>>,
	pub d_sort: Vec<FpVar<F>>,
	pub si_step: Vec<FpVar<F>>, pub si_subsig: Vec<FpVar<F>>,
	pub si_pat: Vec<FpVar<F>>, pub si_rg1: Vec<FpVar<F>>,
	pub si_rg2: Vec<FpVar<F>>, pub si_enc_prev: Vec<FpVar<F>>,
	pub si_b_bwd: Vec<FpVar<F>>,
	/// non-aggressive witness mirror (empty under aggressive).
	pub nonaggr: QmNonAggrVars<F>,
}

/// Per-row selector bits handed to every downstream cert block.
/// is_wrap is a linear residual (may be non-boolean only on rows
/// other invariants already reject); the rest are forced bits.
/// is_bp/is_sp exist only in the non-aggressive arm (empty in aggr,
/// whose cats are {0, C, FP} after the BP->C retag).
pub(crate) struct NeoSel<F: PrimeField + ColEle> {
	pub is_pad: Vec<FpVar<F>>, pub is_wrap: Vec<FpVar<F>>,
	pub is_c: Vec<FpVar<F>>, pub is_fp: Vec<FpVar<F>>,
	pub is_bp: Vec<FpVar<F>>, pub is_sp: Vec<FpVar<F>>,
	pub is_step0: Vec<FpVar<F>>, pub b_bwd_row: Vec<FpVar<F>>,
	pub is_last: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// Row-classification layer, both arms. Every T_qm row is proven
	/// exactly one of: PAD (enc==0 filler), WRAP (per-group
	/// loc-0/loc-max sentinel), C (reachable match), FP (unreachable
	/// match), and -- non-aggressive only -- BP (scan outran it) or
	/// SP (frozen-step surplus). All later blocks mask their
	/// constraints with these bits, so their soundness rests on the
	/// bits being FORCED, not advice. Also derives is_step0 (seed
	/// rows, exempt from C cert and merge) and b_bwd_row (per-row
	/// window direction).
	/// PARAMS: t = native cols (batched inverse hints ONLY; hints
	/// cannot weaken soundness -- constraints bind vars); v = the
	/// allocated circuit vars; r1 = msg2 challenge (fuses the two
	/// seed pins); b_aggr selects the arm (the aggressive stream is
	/// bit-identical to M6). Also derives is_last (LAST si tag,
	/// shared by the wf run lemma and the acc/BP feeds).
	/// COST: ~19*n aggr / ~24*n non-aggr. PERF 61081.1.
	fn assert_neo_selectors(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, r1: &FpVar<F>, b_aggr: bool,
		job_id: usize,
	) -> Result<NeoSel<F>, SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let max_val: usize = (1 << read_global_config().range2_bit) - 1;
		let (f_c, f_fp) = (F::from(CAT_C), F::from(CAT_FP));
		let c_one = new_const_var(&cs, F::one());
		let c_max = new_const_var(&cs, F::from(max_val as u32));
		// --- Section 1: forced boolean bit columns (2cs each/row) ---
		// is_pad <=> enc==0; is_c/is_fp (and non-aggr is_bp/is_sp)
		// <=> cat; is_step0/1 <=> step. step is trustworthy:
		// si_step is pinned (C5) + outer lookup.
		let is_pad = gen_zero_bits(&cs, &t.enc, &v.enc)?;
		let is_c = gen_zero_bits(&cs,
			&t.cat.iter().map(|c| *c - f_c).collect::<Vec<F>>(),
			&v.cat.iter().map(|c| c - &new_const_var(&cs, f_c))
				.collect::<Vec<_>>())?;
		let is_fp = gen_zero_bits(&cs,
			&t.cat.iter().map(|c| *c - f_fp).collect::<Vec<F>>(),
			&v.cat.iter().map(|c| c - &new_const_var(&cs, f_fp))
				.collect::<Vec<_>>())?;
		let (is_bp, is_sp) = if b_aggr { (vec![], vec![]) } else {
			let (f_bp, f_sp) = (F::from(CAT_BP), F::from(CAT_SP));
			(gen_zero_bits(&cs,
				&t.cat.iter().map(|c| *c - f_bp)
					.collect::<Vec<F>>(),
				&v.cat.iter().map(|c|
					c - &new_const_var(&cs, f_bp))
					.collect::<Vec<_>>())?,
			 gen_zero_bits(&cs,
				&t.cat.iter().map(|c| *c - f_sp)
					.collect::<Vec<F>>(),
				&v.cat.iter().map(|c|
					c - &new_const_var(&cs, f_sp))
					.collect::<Vec<_>>())?)
		};
		let is_step0 = gen_zero_bits(&cs, &t.step, &v.step)?;
		let is_step1 = gen_zero_bits(&cs,
			&t.step.iter().map(|s| *s - F::one()).collect::<Vec<F>>(),
			&v.step.iter().map(|s| s - &c_one).collect::<Vec<_>>())?;
		// is_last <=> si_step carries the LAST tag of THIS enc
		// (si_step pinned in C5 + outer-bound; shared by the wf
		// run-completeness lemma and the acc/BP feeds).
		let f1l = F::from(1u64 << read_global_config().range2_bit);
		let f5l = f1l * f1l * f1l * f1l * f1l;
		let cl_nat = F::from(0x23001101u64) * f5l
			* F::from(1u64 << 32)
			+ F::from(ID_ENCODED_LAST_STEP as u64) * f5l;
		let c_l2 = new_const_var(&cs, cl_nat);
		let tg_nat: Vec<F> = (0..n).map(|i|
			t.si_step[i] - cl_nat - t.enc[i]).collect();
		let tg_var: Vec<FpVar<F>> = (0..n).map(|i|
			&(&v.si_step[i] - &c_l2) - &v.enc[i]).collect();
		let is_last = gen_zero_bits(&cs, &tg_nat, &tg_var)?;
		// --- Section 2: row 0 must be a pad (once) ---
		// the group-start cert reads row i-1; forcing enc[0]==0
		// closes the table-start boundary (pads sort first).
		check_eq(&v.enc[0], &FpVar::<F>::Constant(F::zero()), "neo row0 pad")?;
		let mut sel = NeoSel { is_pad: vec![], is_wrap: vec![],
			is_c: vec![], is_fp: vec![], is_bp: vec![],
			is_sp: vec![], is_step0: vec![], b_bwd_row: vec![],
			is_last: vec![] };
		for i in 0..n {
			// --- Section 3: wrap bit as unity residual (2cs) ---
			// is_wrap := 1 - is_pad - (all cat bits) is a FREE LC,
			// so "one class per row" holds by construction. FORCED
			// part: a residual row must be a sentinel: loc in
			// {0,max}. A mistagged row (cat=7 at a real loc) fails
			// here; the pad-with-cat corner dies via hygiene below.
			let mut is_wrap =
				&c_one - &is_pad[i] - &is_c[i] - &is_fp[i];
			if !b_aggr {
				is_wrap = &is_wrap - &is_bp[i] - &is_sp[i];
			}
			let t1 = &is_wrap * &v.loc[i];
			check_prod_zero(&t1, &(&v.loc[i] - &c_max), lc!(),
				"neo wrap loc in {0,max}")?;
			// --- Section 4: pad hygiene (1cs) ---
			// pads carry no payload: loc + cat == 0.
			check_prod_zero(&is_pad[i], &(&v.loc[i] + &v.cat[i]),
				lc!(), "neo pad hygiene")?;
			// --- Section 5: seed pins, real-gated (2cs) ---
			// Fused via r1: t0*(loc-1)==0 and is_step0*is_fp==0
			// (t0*is_fp==is_step0*is_fp since is_c*is_fp==0).
			// Duplicate honest seeds allowed (harmless).
			// EXAMPLE loc==1: fake seed (step0,loc=500,cat=C) would
			//   let an unreachable a1:505 pass its C cert
			//   (505-500=5 in [1,9]) -> fabricated reachability.
			// EXAMPLE !FP: tagging the seed FP would orphan every
			//   step-1 row, letting the whole chain go FP -> false
			//   discharge. The seed anchors the anti-drop cascade.
			let t0 = (&is_c[i] + &is_fp[i]) * &is_step0[i];
			check_prod_zero(&t0,
				&(&(&v.loc[i] - &c_one) + &(r1 * &is_fp[i])), lc!(),
				"neo seed pins")?;
			// --- Section 5b (non-aggr): seed stays C (1cs) ---
			// A BP/SP-tagged seed would silently drop the anchor
			// from q_c; forcing real step-0 rows to C keeps the
			// carried seed invariant across chunks.
			if !b_aggr {
				check_prod_zero(&is_step0[i],
					&(&is_bp[i] + &is_sp[i]), lc!(),
					"neo seed stays C")?;
			}
			// --- Section 6: per-row window direction (1cs) ---
			// b_bwd = per-subsig flag, DB-bound {0,1} via si_b_bwd.
			// Step 1 is ALWAYS the forward keyword anchor (legacy
			// CU5a/CU6: bit && src_step!=0).
			// EXAMPLE: sig "a1 .{1,9} kw" stored kw-first. kw:50 at
			//   step1: b_bwd_row=0 -> forward gap 50-1=49 from seed.
			//   a1:43 at step2: b_bwd_row=1 -> mirrored gap
			//   50-43=7 in [1,9] (a1 occurs BEFORE the keyword).
			let b_bwd_row = &v.b_bwd[i] * (&c_one - &is_step1[i]);
			sel.is_wrap.push(is_wrap);
			sel.b_bwd_row.push(b_bwd_row);
		}
		sel.is_pad = is_pad; sel.is_c = is_c; sel.is_fp = is_fp;
		sel.is_bp = is_bp; sel.is_sp = is_sp;
		sel.is_step0 = is_step0; sel.is_last = is_last;
		log(job_id, LOG3, &format!(
			"PERF 61081.1: block=selectors cs={} pred={}",
			cs.num_constraints() - n0,
			(if b_aggr { 19 } else { 24 }) * n));
		Ok(sel)
	}

	/// TERMS: a GROUP = all T_qm rows sharing one key enc(subsig,
	/// step); its first row is the 0-WRAP (loc 0 sentinel), its last
	/// the MAX-WRAP (loc max); real rows between them are matches
	/// tagged C or FP. The QR-TARGET is the lookup table of REACHABLE
	/// rows: every wrap/C row keyed pack(enc, rid, loc), where rid
	/// ranks those rows 0,1,2,.. inside their group (FP skipped).
	/// This function proves T_qm has that shape: (a) legacy wf; (b)
	/// group-start cert (pads prefix; first row of a group is its
	/// 0-wrap with id 0); (c) STRICT loc ascent (no duplicates); (d)
	/// group uniqueness vs the expected keys (store rows + one seed
	/// key per subsig) -- no cloned/invented groups; (e) rid chain.
	/// PARAMS: s_enc = bound store rows' enc col; subsigs = stmt
	/// subsig list (seed enc = subsig*2^(4rb)); r1 fuses pairs, r2
	/// fingerprints the key multiset. Returns (grp_start, rid).
	/// SHARED by both arms: rid increments as 1-is_pad-is_fp, which
	/// in the aggressive table (cats {0,C,FP}) is literally the
	/// same linear combination as is_wrap+is_c, and in the
	/// non-aggressive table also counts BP/SP -- the paper's Q_r.
	/// Plus (f) RUN COMPLETENESS: each subsig's contiguous group run
	/// starts at its step-0 seed, steps by +1, and ends only at its
	/// DB-LAST group -- with the seed anchor this forces the FULL
	/// chain of every present subsig (kills the n12 tail-drop).
	/// COST: ~26*n (folds the ~2*(|S|+|subsigs|) term).
	/// PERF 61081.2.
	fn assert_neo_wf(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		s_enc: &[FpVar<F>], subsigs: &[FpVar<F>],
		s_enc_nat: &[F], subsig_nat: &[F],
		r1: &FpVar<F>, r2: &FpVar<F>, job_id: usize,
	) -> Result<(Vec<FpVar<F>>, Vec<FpVar<F>>), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let rb = read_global_config().range2_bit;
		let c_max = new_const_var(&cs,
			F::from(((1u64 << rb) - 1) as u64));
		let c_one = new_const_var(&cs, F::one());
		// --- Section 1: legacy wf skeleton (3cs/row, REUSE) ---
		assert_well_formed_sorted(cs.clone(), &v.enc, &v.id, &v.loc,
			None, None, None, None, r1.clone(), rb)?;
		// --- Section 2: group-start cert (5cs/row) ---
		// b_same[i] = (enc[i]==enc[i-1]); a non-pad key change is a
		// group start and must BE a 0-wrap: id + r1*loc == 0.
		// EXAMPLE: shifting a group's ids to make another row "id 1"
		//   (the old min-inflation trick) dies here.
		let mut d_nat = vec![F::zero(); n];
		for i in 1..n { d_nat[i] = t.enc[i] - t.enc[i - 1]; }
		let d_var = (0..n).map(|i| if i == 0 { FpVar::<F>::Constant(F::zero()) }
			else { &v.enc[i] - &v.enc[i - 1] }).collect::<Vec<_>>();
		let b_same = gen_zero_bits(&cs, &d_nat, &d_var)?;
		let mut grp_start = vec![FpVar::<F>::Constant(F::zero())];
		for i in 1..n {
			check_prod_zero(&(&c_one - &sel.is_pad[i - 1]),
				&sel.is_pad[i], lc!(), "neo pads are a prefix")?;
			let gs = (&c_one - &b_same[i])
				* (&c_one - &sel.is_pad[i]);
			check_prod_zero(&gs, &(&v.id[i] + &(r1 * &v.loc[i])),
				lc!(), "neo group starts at its 0-wrap")?;
			grp_start.push(gs);
		}
		check_prod_zero(&(&c_one - &sel.is_pad[n - 1]),
			&(&v.loc[n - 1] - &c_max), lc!(), "neo last row max")?;
		// --- Section 3: STRICT within-group sort (2cs/row) ---
		// d_sort advice is RANGE2-si'd (>=0 via outer lookup); bind:
		// same-group adjacency => d_sort == loc[i]-loc[i-1]-1.
		// EXAMPLE: duplicated (enc,loc) row => diff-1 = -1, not in
		//   the range table.
		for i in 1..n {
			let same = &b_same[i] * (&c_one - &sel.is_pad[i]);
			check_eq(&v.d_sort[i], &(&same
				* &(&v.loc[i] - &v.loc[i - 1] - &c_one)),
				"neo strict sort bind")?;
		}
		// --- Section 4: group uniqueness (2cs/row + expected) ---
		// grand product over 0-wrap keys (grp_start rows) == product
		// over expected keys. EXAMPLE: an empty clone group of enc_x
		//   (the round-1 false-FP oracle) doubles enc_x's pole.
		let mut lhs = c_one.clone();
		for i in 0..n {
			let term = &grp_start[i] * &(&(&v.enc[i] + r2) - &c_one);
			lhs = &lhs * &(&term + &c_one);
		}
		let f1 = F::from(1u64 << rb);
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
		// 8_C: zero entries are pads (padded store rows / dummy-0
		// subsig slots) -> factor 1, not r2. A real store enc/subsig
		// is never 0, so masking cannot hide a live key.
		let z_se = gen_zero_bits(&cs, s_enc_nat, s_enc)?;
		let z_sg = gen_zero_bits(&cs, subsig_nat, subsigs)?;
		let mut rhs = c_one.clone();
		for (j, e) in s_enc.iter().enumerate() {
			let fj = &c_one + &((&c_one - &z_se[j])
				* &(&(e + r2) - &c_one));
			rhs = &rhs * &fj;
		}
		for (j, s) in subsigs.iter().enumerate() {
			let fj = &c_one + &((&c_one - &z_sg[j])
				* &(&(&(s * &c_sh4) + r2) - &c_one));
			rhs = &rhs * &fj;
		}
		check_eq(&lhs, &rhs, "neo group uniqueness")?;
		// --- Section 5: rid rank chain (1cs/row) ---
		// rid[i] = (1-grp_start)*(rid[i-1] + (1-is_pad-is_fp)): 0
		// at the group start; +1 exactly on the NON-FP rows = the
		// QR target (aggr: wrap/C; non-aggr: wrap/C/BP/SP). FP rows
		// keep the previous rank and are invisible in the target.
		// Increment is provably in {0,1}: the cat bits are forced
		// exclusive zero-bits (negative cases die in C1's
		// wrap-force/hygiene).
		// EXAMPLE a6 [0w,73C,79C,96FP,141C,maxw]: rid 0,1,2,2,3,4.
		let mut rid = vec![FpVar::<F>::Constant(F::zero())];
		for i in 1..n {
			let inc = &(&c_one - &sel.is_pad[i]) - &sel.is_fp[i];
			let r_i = (&c_one - &grp_start[i])
				* &(&rid[i - 1] + &inc);
			rid.push(r_i);
		}
		// --- Section 6: run completeness (8cs/row) ---
		// Sorted encs make each subsig's groups one contiguous RUN.
		// (a) a run ends only at its DB-LAST group (is_last off the
		// pinned si_step); (b) a run starts at its step-0 seed; (c)
		// consecutive groups in a run step by +1. With the seed
		// anchor: any subsig present shows its FULL chain 0..last,
		// so the n12 joint store-drop (tail truncation) leaves an
		// un-endable run -> UNSAT.
		let mut ds_nat = vec![F::zero(); n];
		for i in 1..n { ds_nat[i] = t.subsig[i] - t.subsig[i - 1]; }
		let ds_var = (0..n).map(|i| if i == 0 {
			FpVar::<F>::Constant(F::zero()) }
			else { &v.subsig[i] - &v.subsig[i - 1] })
			.collect::<Vec<_>>();
		let same_sub = gen_zero_bits(&cs, &ds_nat, &ds_var)?;
		for i in 1..n {
			let bnd = &grp_start[i] * &(&c_one - &same_sub[i]);
			let t_end = &bnd * &(&c_one - &sel.is_pad[i - 1]);
			check_prod_zero(&t_end,
				&(&c_one - &sel.is_last[i - 1]), lc!(),
				"neo run ends at LAST")?;
			check_prod_zero(&bnd, &v.step[i], lc!(),
				"neo run starts at seed")?;
			let u = &grp_start[i] * &same_sub[i];
			check_prod_zero(&u,
				&(&(&v.step[i] - &v.step[i - 1]) - &c_one), lc!(),
				"neo run step chain")?;
		}
		check_prod_zero(&(&c_one - &sel.is_pad[n - 1]),
			&(&c_one - &sel.is_last[n - 1]), lc!(),
			"neo final run ends at LAST")?;
		log(job_id, LOG3, &format!(
			"PERF 61081.2: block=wf cs={} pred={}",
			cs.num_constraints() - n0, 26 * n));
		Ok((grp_start, rid))
	}

	/// Pin every si column to its row's claimed tag; the OUTER
	/// foldpot lookup then forces each (si,value) pair to exist in
	/// the DB, so together: value == the DB fact for THIS row's enc.
	/// Tags are linear in enc (gen_step_tbl_id = const_cat + enc).
	///  - si_step: (si-cN-enc)*(si-cL-enc)==0 (NORMAL or LAST of
	///    THIS enc; the DB stores a step under exactly one, so
	///    last/non-last mislabeling dies at the outer lookup).
	///    EXAMPLE: tagging terminal enc_T's row with tag_LAST(enc')
	///    to dodge the acc query fails (neither factor is 0).
	///  - si_subsig mask (1-is_pad)*(1-is_step0); si_pat/rg1/rg2/
	///    enc_prev mask (REAL row)*(1-is_step0), real = is_c+is_fp
	///    in aggressive and additionally +is_bp+is_sp in
	///    non-aggressive (same formula on the aggressive table,
	///    where no BP/SP rows exist); pin: si ==
	///    mask*(const_cat+enc-RANGE2) + RANGE2.
	///  - si_b_bwd == FLAG_BASE + subsig on ALL rows (linear).
	/// COST: ~14*n. MEASURED @ fig-14 n=34: 476 (0% vs
	/// 14n). PERF 61081.5.
	fn assert_neo_si_pins(
		cs: ConstraintSystemRef<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		b_aggr: bool, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = v.enc.len();
		let rb = read_global_config().range2_bit;
		let f1 = F::from(1u64 << rb);
		let f5 = f1 * f1 * f1 * f1 * f1;
		let base = F::from(0x23001101u64) * f5 * F::from(1u64 << 32);
		let cat_c = |cid: u32| base + F::from(cid as u64) * f5;
		let c_n = new_const_var(&cs, cat_c(ID_ENCODED_NORMAL_STEP));
		let c_l = new_const_var(&cs, cat_c(ID_ENCODED_LAST_STEP));
		let c_rg2t = new_const_var(&cs, F::from(RANGE2));
		let c_one = new_const_var(&cs, F::one());
		let c_fbase = new_const_var(&cs,
			F::from(1u64 << 32) * F::from(ID_SUBSIG_IS_BACKWARD));
		let pins: [(u32, fn(&QmVars<F>) -> &Vec<FpVar<F>>); 5] = [
			(ID_ENCODED_SUBSIG, |v| &v.si_subsig),
			(ID_ENCODED_PAT, |v| &v.si_pat),
			(ID_ENCODED_RG_START, |v| &v.si_rg1),
			(ID_ENCODED_RG_END, |v| &v.si_rg2),
			(ID_ENCODED_PREV_ENCODED, |v| &v.si_enc_prev)];
		for i in 0..n {
			check_prod_zero(
				&(&(&v.si_step[i] - &c_n) - &v.enc[i]),
				&(&(&v.si_step[i] - &c_l) - &v.enc[i]), lc!(),
				"neo si_step pin")?;
			let m_sub = (&c_one - &sel.is_pad[i])
				* (&c_one - &sel.is_step0[i]);
			let real = if b_aggr {
				&sel.is_c[i] + &sel.is_fp[i]
			} else {
				&(&sel.is_c[i] + &sel.is_fp[i])
					+ &(&sel.is_bp[i] + &sel.is_sp[i])
			};
			let m_bind = real * (&c_one - &sel.is_step0[i]);
			for (j, (cid, getcol)) in pins.iter().enumerate() {
				let mask = if j == 0 { &m_sub } else { &m_bind };
				let c_cat = new_const_var(&cs, cat_c(*cid));
				let tag = &(&c_cat + &v.enc[i]) - &c_rg2t;
				check_eq(&getcol(v)[i],
					&(&(mask * &tag) + &c_rg2t), "neo si pin")?;
			}
			check_eq(&v.si_b_bwd[i], &(&c_fbase + &v.subsig[i]),
				"neo si_b_bwd pin")?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61081.5: block=si_pins cs={} pred={}",
			cs.num_constraints() - n0, 14 * n));
		Ok(())
	}
}

/// Plain-value (F, not FpVar) bundle of every column the neo core
/// consumes: the T_qm table plus L/D/S/acc side columns and all
/// m-tables. Built by the advice side; inside assert_msg3 it is
/// rebuilt from witness value()s and serves as hint material only
/// (constraints bind the NeoCoreVars mirror alone).
#[derive(Clone, Debug, Default)]
pub(crate) struct NeoCore<F: PrimeField + ColEle> {
	pub t: QmTable<F>,
	pub l_pat: Vec<F>, pub l_loc: Vec<F>,
	pub subsig_nat: Vec<F>,
	pub s_enc: Vec<F>, pub s_pat: Vec<F>,
	pub d_pat: Vec<F>, pub d_cnt: Vec<F>, pub d_diff: Vec<F>,
	pub m_aux: Vec<F>, pub mtbl_qr: Vec<F>, pub mtbl_d: Vec<F>,
	pub acc_out: Vec<F>, pub mtbl_acc: Vec<F>,
	// ---- non-aggressive extension (empty under aggressive) ----
	/// committed q_i (IDX_INP) cols: the carried-in queue Q_i as
	/// serialized by StepQueue::to_container (front-padded).
	pub qi_enc: Vec<F>, pub qi_loc: Vec<F>,
	/// committed q_c (IDX_OUP) cols: the carry set Q_c = the C
	/// projection of Q_m, next chunk's Q_i.
	pub qc_enc: Vec<F>, pub qc_loc: Vec<F>,
	/// m-table of the fused QC-target logup (C-pred + BP-min +
	/// SP-freeze + SP-dom query families). The carry-in logup's
	/// m-table is t.nonaggr.m_carry_in (filled by fill_nonaggr).
	pub mtbl_qc: Vec<F>,
}

/// FpVar mirror of NeoCore (what the circuit constrains).
pub(crate) struct NeoCoreVars<F: PrimeField + ColEle> {
	pub qm: QmVars<F>,
	pub l_pat: Vec<FpVar<F>>, pub l_loc: Vec<FpVar<F>>,
	pub subsigs: Vec<FpVar<F>>,
	pub s_enc: Vec<FpVar<F>>, pub s_pat: Vec<FpVar<F>>,
	pub d_pat: Vec<FpVar<F>>, pub d_cnt: Vec<FpVar<F>>,
	pub d_diff: Vec<FpVar<F>>, pub m_aux: Vec<FpVar<F>>,
	pub mtbl_qr: Vec<FpVar<F>>, pub mtbl_d: Vec<FpVar<F>>,
	pub acc_out: Vec<FpVar<F>>, pub mtbl_acc: Vec<FpVar<F>>,
	// ---- non-aggressive extension (empty under aggressive) ----
	pub qi_enc: Vec<FpVar<F>>, pub qi_loc: Vec<FpVar<F>>,
	pub qc_enc: Vec<FpVar<F>>, pub qc_loc: Vec<FpVar<F>>,
	pub mtbl_qc: Vec<FpVar<F>>,
}

/// FpVar mirror of QmNonAggrCols (loaded only by the non-aggressive
/// arm; every vec row-parallel to QmVars.enc).
pub(crate) struct QmNonAggrVars<F: PrimeField + ColEle> {
	pub b_l: Vec<FpVar<F>>, pub enc_next: Vec<FpVar<F>>,
	pub bp_prev_val: Vec<FpVar<F>>, pub rg2_next: Vec<FpVar<F>>,
	pub w_next: Vec<FpVar<F>>, pub d_bp: Vec<FpVar<F>>,
	pub fz: Vec<FpVar<F>>, pub enc_fz: Vec<FpVar<F>>,
	pub fz_step_val: Vec<FpVar<F>>, pub fz_sub_val: Vec<FpVar<F>>,
	pub w_fz: Vec<FpVar<F>>, pub d_fz: Vec<FpVar<F>>,
	pub w_sp: Vec<FpVar<F>>, pub d_sp: Vec<FpVar<F>>,
	pub m_carry_in: Vec<FpVar<F>>,
	pub si_bp_prev: Vec<FpVar<F>>, pub si_rg2_next: Vec<FpVar<F>>,
	pub si_fz: Vec<FpVar<F>>, pub si_fz_step: Vec<FpVar<F>>,
	pub si_fz_sub: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> QmNonAggrVars<F> {
	/// all-empty mirror for the aggressive loader (never read).
	pub(crate) fn empty() -> Self {
		Self { b_l: vec![], enc_next: vec![], bp_prev_val: vec![],
			rg2_next: vec![], w_next: vec![], d_bp: vec![],
			fz: vec![], enc_fz: vec![], fz_step_val: vec![],
			fz_sub_val: vec![], w_fz: vec![], d_fz: vec![],
			w_sp: vec![], d_sp: vec![], m_carry_in: vec![],
			si_bp_prev: vec![], si_rg2_next: vec![], si_fz: vec![],
			si_fz_step: vec![], si_fz_sub: vec![] }
	}
}

impl<F: PrimeField + ColEle> NeoCore<F> {
	/// Native mirror of the C2 rid chain: rank of the NON-FP rows
	/// (wrap/C/BP/SP) inside their group; FP rows keep the previous
	/// rank; pads stay 0. In the aggressive table cats are {0,C,FP}
	/// so this is exactly the old wrap-or-C rank; in non-aggressive
	/// it matches the circuit increment 1 - is_pad - is_fp.
	pub(crate) fn gen_rid_native(t: &QmTable<F>) -> Vec<F> {
		let n = t.enc.len();
		let mut rid = vec![F::zero(); n];
		for i in 1..n {
			if t.enc[i] != t.enc[i - 1] && !t.enc[i].is_zero() {
				rid[i] = F::zero();
				continue;
			}
			let inc = if t.enc[i].is_zero()
				|| t.cat[i] == F::from(CAT_FP) { F::zero() }
				else { F::one() };
			rid[i] = rid[i - 1] + inc;
		}
		rid
	}

	/// Native mirror of the QC cid chain (NON-AGGRESSIVE): rank of
	/// wrap/C rows inside their group; FP/BP/SP rows keep the
	/// previous rank; pads stay 0. Per group the QC-selected rows
	/// get distinct cids 0..k+1, so (enc, cid=1, loc) resolves to
	/// the least carried loc -- or the max-wrap when none carried.
	/// EXAMPLE a6 group [0w, 73BP, 79BP, 96BP, 141BP, maxw]:
	///   cid = 0,0,0,0,0,1 -> (enc6, 1, max): step carries nothing.
	pub(crate) fn gen_cid_native(t: &QmTable<F>) -> Vec<F> {
		let n = t.enc.len();
		let mut cid = vec![F::zero(); n];
		for i in 1..n {
			if t.enc[i] != t.enc[i - 1] && !t.enc[i].is_zero() {
				cid[i] = F::zero();
				continue;
			}
			let inc = if t.enc[i].is_zero() { F::zero() }
				else if t.cat[i] == F::from(CAT_C)
					|| t.cat[i].is_zero() { F::one() }
				else { F::zero() };
			cid[i] = cid[i - 1] + inc;
		}
		cid
	}

	/// m-table for the fused QR-target logup: per target row (wrap/C
	/// keyed by its (enc,rid,loc) tuple), the number of query hits
	/// across the C-pred, FP-low, FP-high and seed-anchor families.
	/// Tuple counting is challenge-independent.
	pub(crate) fn gen_mtbl_qr(t: &QmTable<F>, rid: &Vec<F>,
		subsig_nat: &Vec<F>) -> Vec<F> {
		let n = t.enc.len();
		let f1 = F::from(1u64 << read_global_config().range2_bit);
		let f_sh4 = f1 * f1 * f1 * f1;
		let mut hm: HashMap<(F, F, F), u32> = HashMap::new();
		for i in 0..n {
			if t.cat[i] == F::from(CAT_C) && !t.step[i].is_zero() {
				*hm.entry((t.enc_prev[i], t.prev_id1[i],
					t.prev_loc1[i])).or_insert(0) += 1;
			}
			if t.cat[i] == F::from(CAT_FP) {
				*hm.entry((t.enc_prev[i], t.prev_id1[i],
					t.prev_loc1[i])).or_insert(0) += 1;
				*hm.entry((t.enc_prev[i],
					t.prev_id1[i] + F::one(),
					t.prev_loc2[i])).or_insert(0) += 1;
			}
		}
		for s in subsig_nat {
			if !s.is_zero() {
				*hm.entry((*s * f_sh4, F::one(), F::one()))
					.or_insert(0) += 1;
			}
		}
		(0..n).map(|i| {
			let b_tgt = !t.enc[i].is_zero()
				&& (t.cat[i].is_zero()
					|| t.cat[i] == F::from(CAT_C));
			if !b_tgt { return F::zero(); }
			F::from(*hm.get(&(t.enc[i], rid[i], t.loc[i]))
				.unwrap_or(&0))
		}).collect()
	}

	/// acc_out with a leading 0 slot (every non-terminal query row
	/// lands there) + the matching completeness m-table.
	pub(crate) fn gen_acc_padded(t: &QmTable<F>,
		info: &SubsigStepStore) -> (Vec<F>, Vec<F>) {
		let (acc, mtbl) = StepQueueNeo::gen_acc_and_mtbl(t, info);
		let n_hit: usize = mtbl.iter()
			.map(|m| field_to_usize(m)).sum();
		let n_zero = t.enc.len() - n_hit;
		let acc_out = [vec![F::zero()], acc].concat();
		let mtbl_acc = [vec![F::from(n_zero as u32)], mtbl].concat();
		(acc_out, mtbl_acc)
	}

	/// m-table for the (pat, m) -> D forcing lookup: per D row, the
	/// number of REAL L rows with that pat (their m == cnt(pat)).
	pub(crate) fn gen_mtbl_d(l_pat: &Vec<F>, l_loc: &Vec<F>,
		d_pat: &Vec<F>) -> Vec<F> {
		let max_val: usize =
			(1 << read_global_config().range2_bit) - 1;
		let f_max = F::from(max_val as u32);
		let mut hm: HashMap<F, u32> = HashMap::new();
		for (p, l) in l_pat.iter().zip(l_loc.iter()) {
			if !l.is_zero() && *l != f_max {
				*hm.entry(*p).or_insert(0) += 1;
			}
		}
		d_pat.iter().map(|p| F::from(*hm.get(p).unwrap_or(&0)))
			.collect()
	}

	/// NON-AGGRESSIVE m-table of the fused QR-target logup. Unlike
	/// the aggressive gen_mtbl_qr, the C-pred family is ABSENT (it
	/// moved to the QC target); only the FP bracket pairs and the
	/// seed anchors query QR. Target rows = non-FP non-pad, keyed
	/// pack(enc, rid, loc).
	pub(crate) fn gen_mtbl_qr_nonaggr(t: &QmTable<F>, rid: &Vec<F>,
		subsig_nat: &Vec<F>) -> Vec<F> {
		let n = t.enc.len();
		let f1 = F::from(1u64 << read_global_config().range2_bit);
		let f_sh4 = f1 * f1 * f1 * f1;
		let mut hm: HashMap<(F, F, F), u32> = HashMap::new();
		for i in 0..n {
			if t.cat[i] == F::from(CAT_FP) {
				*hm.entry((t.enc_prev[i], t.prev_id1[i],
					t.prev_loc1[i])).or_insert(0) += 1;
				*hm.entry((t.enc_prev[i],
					t.prev_id1[i] + F::one(),
					t.prev_loc2[i])).or_insert(0) += 1;
			}
		}
		for s in subsig_nat {
			if !s.is_zero() {
				*hm.entry((*s * f_sh4, F::one(), F::one()))
					.or_insert(0) += 1;
			}
		}
		(0..n).map(|i| {
			let b_tgt = !t.enc[i].is_zero()
				&& t.cat[i] != F::from(CAT_FP);
			if !b_tgt { return F::zero(); }
			F::from(*hm.get(&(t.enc[i], rid[i], t.loc[i]))
				.unwrap_or(&0))
		}).collect()
	}

	/// m-table of the fused QC-target logup (NON-AGGRESSIVE). Four
	/// query families against rows keyed pack(enc, cid, loc), row
	/// selector wrap-or-C:
	///  C (non-seed): (enc_prev, prev_id1, prev_loc1) -- the
	///    re-picked carried predecessor, prev_id1 in QC rank;
	///  BP: (enc_next, 1, w_next) -- least carried loc at step i+1
	///    (or its max-wrap when the step carries nothing);
	///  SP: (enc_fz, 1, w_fz) freeze + (enc, 1, w_sp) min-dom.
	pub(crate) fn gen_mtbl_qc(t: &QmTable<F>, cid: &Vec<F>)
	-> Vec<F> {
		let n = t.enc.len();
		let one = F::one();
		let na = &t.nonaggr;
		let mut hm: HashMap<(F, F, F), u32> = HashMap::new();
		for i in 0..n {
			if t.cat[i] == F::from(CAT_C) && !t.step[i].is_zero() {
				*hm.entry((t.enc_prev[i], t.prev_id1[i],
					t.prev_loc1[i])).or_insert(0) += 1;
			}
			if t.cat[i] == F::from(CAT_BP) {
				*hm.entry((na.enc_next[i], one, na.w_next[i]))
					.or_insert(0) += 1;
			}
			if t.cat[i] == F::from(CAT_SP) {
				*hm.entry((na.enc_fz[i], one, na.w_fz[i]))
					.or_insert(0) += 1;
				*hm.entry((t.enc[i], one, na.w_sp[i]))
					.or_insert(0) += 1;
			}
		}
		(0..n).map(|i| {
			let b_tgt = !t.enc[i].is_zero()
				&& (t.cat[i].is_zero()
					|| t.cat[i] == F::from(CAT_C));
			if !b_tgt { return F::zero(); }
			F::from(*hm.get(&(t.enc[i], cid[i], t.loc[i]))
				.unwrap_or(&0))
		}).collect()
	}

	/// NON-AGGRESSIVE bundle assembler (paper C.1). Builds the
	/// 4-class T_qm + witness cols, the merge dictionary, all
	/// m-tables, and the two COMMITTED transport containers:
	///  q_i (IDX_INP) = the carried-in queue exactly as the fold
	///    binds it, and q_c (IDX_OUP) = the C projection of Q_m
	///    (next chunk's Q_i). acc_out/mtbl_acc stay empty -- the
	///    non-aggressive verdict flows through q_c into
	///    compute_sig, not through failed_acc.
	/// Returns (bundle, ct_qi, ct_qc); can CapErr on the T_qm
	/// budget or the q_c ResSmall carry width.
	pub(crate) fn gen_nonaggr(g: &StepQueueNeo<F>,
		info: &SubsigStepStore, l_pat: Vec<F>, l_loc: Vec<F>,
		hm_loc: &HashMap<F, Vec<(F, F)>>, carried: &StepQueue<F>,
		default_min: F, job_id: usize)
	-> Result<(NeoCore<F>, Arc<Mutex<Container<F>>>,
		Arc<Mutex<Container<F>>>), Error> {
		let mut t = g.gen_qm_table(info, false)?;
		t.fill_nonaggr(info, hm_loc, carried, default_min);
		let rid = Self::gen_rid_native(&t);
		let cid = Self::gen_cid_native(&t);
		let subsig_nat = g.subsigs.clone();
		let (s_enc, s_pat) = Self::gen_store_rows(&subsig_nat,
			info);
		let mut hm_pats: HashMap<F, Vec<(F, F)>> = HashMap::new();
		for p in &l_pat { hm_pats.entry(*p).or_insert(vec![]); }
		let (d_pat, d_cnt) = StepQueueNeo::gen_merge_dict(
			&subsig_nat, info, &hm_pats, g.b_igc)?;
		let mut d_diff = vec![F::zero(); d_pat.len()];
		for j in 1..d_pat.len() {
			d_diff[j] = d_pat[j] - d_pat[j - 1] - F::one();
		}
		let m_aux = StepQueueNeo::gen_merge_m_aux(&l_pat, &l_loc,
			&d_pat, &d_cnt);
		let mtbl_qr = Self::gen_mtbl_qr_nonaggr(&t, &rid,
			&subsig_nat);
		let mtbl_qc = Self::gen_mtbl_qc(&t, &cid);
		let mtbl_d = Self::gen_mtbl_d(&l_pat, &l_loc, &d_pat);
		//committed transport: q_i as handed in; q_c = C projection
		let ct_qi = carried.to_container("q_i", true, false, false,
			false, info)?;
		let qc_sq = g.carry_only();
		let ct_qc = qc_sq.to_container("q_c", false, true, true,
			true, info)?;
		//PERF 61080.2: committed carry saturation (the number the
		//theorem bounds; M12 sizes caps from its run-level peak).
		let (n_qc, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResSmall, &g.capacity);
		let qc_rows: usize = qc_sq.store_items.values().map(|v|
			v.iter().map(|it| it.locs.len()).sum::<usize>()).sum();
		log(job_id, LOG3, &format!(
			"PERF 61080.2 qc_rows={} qc_cap={} sat_pm={}",
			qc_rows, n_qc, qc_rows * 1000 / n_qc.max(1)));
		let col = |ct: &Arc<Mutex<Container<F>>>, name: &str| {
			ct.lock().unwrap().get_container(name).unwrap()
				.lock().unwrap().to_vec()
		};
		let nat = NeoCore {
			qi_enc: col(&ct_qi, "encoded"),
			qi_loc: col(&ct_qi, "locs"),
			qc_enc: col(&ct_qc, "encoded"),
			qc_loc: col(&ct_qc, "locs"),
			t, l_pat, l_loc, subsig_nat, s_enc, s_pat, d_pat,
			d_cnt, d_diff, m_aux, mtbl_qr, mtbl_d,
			acc_out: vec![], mtbl_acc: vec![], mtbl_qc };
		Ok((nat, ct_qi, ct_qc))
	}
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// TERMS: QR-TARGET = the reachable-row lookup table carved from
	/// T_qm: every wrap or C row, keyed pack(enc, rid, loc) with the
	/// C2 rank (pack = challenge combination; collision-free by
	/// Schwartz-Zippel since advice commits before r1 is drawn).
	/// Proves per real row: C -> its claimed predecessor EXISTS in
	/// the target and reaches it (gap in [rg1,rg2], direction per
	/// b_bwd_row); FP -> the two RANK-ADJACENT target rows prev_id1
	/// and prev_id1+1 bracket its predecessor window with no target
	/// row inside (genuinely unreachable); per subsig -> the seed row
	/// (rank 1, loc 1) is in the target (anti-drop anchor). All
	/// query families share ONE fused masked logup (mtbl_qr).
	/// PARAMS: rid = C2 rank col; subsig_nat = native stmt subsigs
	/// (zero-bit hints); mtbl_qr = fused-lookup m-table advice.
	/// COST: ~31*n (folds the fused logup ~2*(3n+
	/// |subsigs|)+3n into the per-row rate). MEASURED @
	/// fig-14 n=34: 1064 (+0.9% vs 31n). PERF 61081.3.
	fn assert_neo_certs_aggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		rid: &[FpVar<F>], subsigs: &[FpVar<F>], subsig_nat: &[F],
		mtbl_qr: &Vec<FpVar<F>>, r1: &FpVar<F>, r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		let c_sh = new_const_var(&cs, F::from(1u64 << rb));
		// --- Section 1: target keys + selector (2 muls/row) ---
		let r1sq = r1 * r1;
		let tgt: Vec<FpVar<F>> = (0..n).map(|i|
			&(&v.enc[i] + &(r1 * &rid[i])) + &(&r1sq * &v.loc[i]))
			.collect();
		let sel_qr: Vec<FpVar<F>> = (0..n).map(|i|
			&sel.is_wrap[i] + &sel.is_c[i]).collect();
		// masks for the FP wrap-sentinel sides
		let z_pl1 = gen_zero_bits(&cs, &t.prev_loc1, &v.prev_loc1)?;
		let m_pl2 = gen_zero_bits(&cs,
			&t.prev_loc2.iter().map(|x| f_max - *x)
				.collect::<Vec<F>>(),
			&v.prev_loc2.iter().map(|x| &c_max - x)
				.collect::<Vec<_>>())?;
		let (mut qry, mut sq) = (vec![], vec![]);
		for i in 0..n {
			// --- Section 2: C reach window (3cs) ---
			// gap = |loc - prev_loc1| oriented by b_bwd_row; d_c1 =
			// gap-rg1 and d_c2 = rg2-gap are RANGE2 advice (>=0);
			// binding them proves rg1 <= gap <= rg2.
			// EXAMPLE fwd: a7:101 from pred 96, rg{1,9}: gap 5,
			//   d_c1=4, d_c2=4. EXAMPLE bwd step2: kw:50, a1:43:
			//   gap 50-43=7.
			let sel_c = &sel.is_c[i] * (&c_one - &sel.is_step0[i]);
			let gap = better_select(&sel.b_bwd_row[i],
				&(&v.prev_loc1[i] - &v.loc[i]),
				&(&v.loc[i] - &v.prev_loc1[i]));
			check_prod_zero(&sel_c,
				&(&(&gap - &v.rg1[i]) - &v.d_c1[i]), lc!(),
				"neo C d1")?;
			check_prod_zero(&sel_c,
				&(&(&v.rg2[i] - &gap) - &v.d_c2[i]), lc!(),
				"neo C d2")?;
			// --- Section 3: FP bracket gaps (6cs) ---
			// below-check: the LOWER neighbor cannot reach this row;
			// masked when prev_loc1 is the 0-wrap (the upper check
			// alone then proves the window sits below every
			// reachable row). above-check symmetric via the
			// max-wrap. Both bound as hi*2^rb + lo, hi boolean (the
			// honest diff can exceed 2^rb).
			// EXAMPLE: FP a7:131 vs 96/141, rg{1,9}:
			//   below 131-96-9-1=25>=0; above 141+1-131-1=10>=0.
			let m_lo = &sel.is_fp[i] * (&c_one - &z_pl1[i]);
			let e_lo = better_select(&sel.b_bwd_row[i],
				&(&(&v.loc[i] + &v.rg1[i]) - &v.prev_loc1[i]
					- &c_one),
				&(&(&v.loc[i] - &v.prev_loc1[i]) - &v.rg2[i]
					- &c_one));
			check_prod_zero(&m_lo, &(&(&e_lo
				- &(&v.d_below_hi[i] * &c_sh)) - &v.d_below_lo[i]),
				lc!(), "neo FP below")?;
			let m_hi = &sel.is_fp[i] * (&c_one - &m_pl2[i]);
			let e_hi = better_select(&sel.b_bwd_row[i],
				&(&(&v.prev_loc2[i] - &v.loc[i]) - &v.rg2[i]
					- &c_one),
				&(&(&v.prev_loc2[i] + &v.rg1[i]) - &v.loc[i]
					- &c_one));
			check_prod_zero(&m_hi, &(&(&e_hi
				- &(&v.d_above_hi[i] * &c_sh)) - &v.d_above_lo[i]),
				lc!(), "neo FP above")?;
			check_prod_zero(&v.d_below_hi[i],
				&(&v.d_below_hi[i] - &c_one), lc!(),
				"neo hi bool")?;
			check_prod_zero(&v.d_above_hi[i],
				&(&v.d_above_hi[i] - &c_one), lc!(),
				"neo hi bool2")?;
			// --- Section 4: fused lookup queries (2 muls/row) ---
			let base = &(&v.enc_prev[i] + &(r1 * &v.prev_id1[i]))
				+ &(&r1sq * &v.prev_loc1[i]);
			qry.push(base.clone()); sq.push(sel_c);
			qry.push(base); sq.push(sel.is_fp[i].clone());
			qry.push(&(&v.enc_prev[i]
				+ &(r1 * &(&v.prev_id1[i] + &c_one)))
				+ &(&r1sq * &v.prev_loc2[i]));
			sq.push(sel.is_fp[i].clone());
		}
		// seed anchors: pack(subsig*2^4rb, 1, 1), sel = subsig != 0.
		// EXAMPLE: dropping subsig 7's seed row leaves the query
		//   pack(7*2^4rb,1,1) unmatched -> UNSAT.
		let f1 = F::from(1u64 << rb);
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
		let z_sub = gen_zero_bits(&cs, subsig_nat, subsigs)?;
		for (j, s) in subsigs.iter().enumerate() {
			qry.push(&(&(s * &c_sh4) + r1) + &r1sq);
			sq.push(&c_one - &z_sub[j]);
		}
		assert_logup_cond(cs.clone(), &qry, &sq, &tgt.to_vec(),
			&sel_qr.to_vec(), mtbl_qr, r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.3: block=certs cs={} pred={}",
			cs.num_constraints() - n0, 31 * n));
		Ok(())
	}
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// MERGE COMPLETENESS + verdict feed (doc terms: L/D/S as in the
	/// design): every match in L must appear in T_qm once per step
	/// that uses its pattern -- omission would hide a potential
	/// signature match. Counting proof: (1) D.pat strict (distinct);
	/// (2) cnt forcing logup(S.pat -> D) pins cnt to the store
	/// fan-out; (3) m forcing: each real L row's advice m pinned by
	/// (pat,m) in D; (4) counting logup: T_qm real non-seed rows
	/// pack(pat,loc) vs L real rows with m_tbl = m => each match
	/// demanded EXACTLY cnt(pat) times (pigeonhole with C2
	/// strictness+uniqueness). ACC: {LAST-step C encs} subset
	/// acc_out via the re-derived LAST tag (legacy pattern + is_c).
	/// PARAMS mirror NeoCore/NeoCoreVars fields; l_nat =
	/// native (l_pat,l_loc) hint slices; r1 packs, r2 logups.
	/// COST: ~14*n + ~7*|L| + ~3*|D| (n-term folds the
	/// logups). MEASURED @ fig-14 n=34: 703 (+2.0% vs the
	/// 689 estimate). PERF 61081.4.
	/// MERGE CORE, shared by both arms: (1) the L real-row selector
	/// (wrap rows are sentinels, not matches); (2) D strictness
	/// (d_diff RANGE2 => pats distinct); (3) cnt forcing
	/// logup(S.pat -> D) pinning cnt to the store fan-out; (4) m
	/// forcing: each real L row's advice m pinned by (pat,m) in D.
	/// Returns sel_l for the arm-specific counting logup.
	/// EMPTY-L degenerate (tier-1 harness only): an empty query
	/// side forces every multiplicity to 0 -- asserted directly
	/// (sum_vec_vars cannot take empty slices).
	fn assert_neo_merge_core(
		cs: ConstraintSystemRef<F>,
		l_pat: &[FpVar<F>], l_loc: &[FpVar<F>], l_nat: (&[F], &[F]),
		m_aux: &Vec<FpVar<F>>, d_pat: &[FpVar<F>],
		d_cnt: &[FpVar<F>], d_diff: &[FpVar<F>], s_pat: &[FpVar<F>],
		mtbl_d: &Vec<FpVar<F>>, r1: &FpVar<F>, r2: &FpVar<F>,
	) -> Result<Vec<FpVar<F>>, SynthesisError> {
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		// --- Section 1: L real-row selector (5cs/L-row) ---
		// L wrap rows (loc 0/max) are sentinels, not matches; they
		// must not satisfy the counting demand.
		let z_l = gen_zero_bits(&cs, l_nat.1, l_loc)?;
		let m_l = gen_zero_bits(&cs,
			&l_nat.1.iter().map(|x| f_max - *x).collect::<Vec<F>>(),
			&l_loc.iter().map(|x| &c_max - x).collect::<Vec<_>>())?;
		let sel_l: Vec<FpVar<F>> = (0..l_pat.len()).map(|j|
			(&c_one - &z_l[j]) * (&c_one - &m_l[j])).collect();
		// --- Section 2: D strictness (1cs/D-row) ---
		// d_diff RANGE2-si'd (>=0): pats strictly ascend => distinct.
		// EXAMPLE: split-cnt forgery {(p,2),(p,3)} needs a duplicate
		//   pat -- dies here.
		for j in 1..d_pat.len() {
			check_eq(&d_diff[j],
				&(&(&d_pat[j] - &d_pat[j - 1]) - &c_one),
				"neo D strict")?;
		}
		// --- Section 3: cnt forcing (1 logup) ---
		// EXAMPLE: pat p on steps s1,s2 -> two S poles at p ->
		//   cnt(p)=2; no other value balances.
		// EMPTY STORE (e.g. an igc gadget for a case-sensitive-only
		// sig set): no S poles / no D dictionary -> vacuous counting
		// logup (assert_logup cannot take an empty query/table side).
		if !s_pat.is_empty() && !d_pat.is_empty() {
			assert_logup(cs.clone(), s_pat, d_pat, d_cnt, r2)?;
		}
		// --- Section 4: m forcing per L row (1 masked logup) ---
		// EXAMPLE: cnt(p)=2 but an L row claims m=1: (p,1) is not a
		//   D row -> unmatched query.
		let c_zero = new_const_var(&cs, F::zero());
		if l_pat.is_empty() {
			for j in 0..d_pat.len() {
				check_eq(&mtbl_d[j], &c_zero, "neo mtbl_d empty-L")?;
			}
		} else {
			let qry_m: Vec<FpVar<F>> = (0..l_pat.len()).map(|j|
				&l_pat[j] + &(r1 * &m_aux[j])).collect();
			let lk_d: Vec<FpVar<F>> = (0..d_pat.len()).map(|j|
				&d_pat[j] + &(r1 * &d_cnt[j])).collect();
			let ones = vec![c_one.clone(); d_pat.len()];
			assert_logup_cond(cs.clone(), &qry_m, &sel_l.to_vec(),
				&lk_d, &ones, mtbl_d, r2)?;
		}
		Ok(sel_l)
	}

	fn assert_neo_merge_acc_aggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		l_pat: &[FpVar<F>], l_loc: &[FpVar<F>], l_nat: (&[F], &[F]),
		m_aux: &Vec<FpVar<F>>, d_pat: &[FpVar<F>],
		d_cnt: &[FpVar<F>], d_diff: &[FpVar<F>], s_pat: &[FpVar<F>],
		mtbl_d: &Vec<FpVar<F>>, acc_out: &[FpVar<F>],
		mtbl_acc: &[FpVar<F>], r1: &FpVar<F>, r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let c_one = new_const_var(&cs, F::one());
		let c_zero = new_const_var(&cs, F::zero());
		// --- Sections 1-4: shared merge core ---
		let sel_l = Self::assert_neo_merge_core(cs.clone(), l_pat,
			l_loc, l_nat, m_aux, d_pat, d_cnt, d_diff, s_pat,
			mtbl_d, r1, r2)?;
		// --- Section 5: the counting logup (1cs/row + logup) ---
		// EXAMPLE: dropping the single row (s2,l) of a cnt=2 pat
		//   leaves hits(p,l)=1 != m=2 -> UNSAT.
		let mut qry_c = vec![]; let mut sel_c = vec![];
		for i in 0..n {
			qry_c.push(&v.pat[i] + &(r1 * &v.loc[i]));
			sel_c.push((&sel.is_c[i] + &sel.is_fp[i])
				* (&c_one - &sel.is_step0[i]));
		}
		if l_pat.is_empty() {
			// no L rows -> no real non-step0 row may exist at all.
			for i in 0..n {
				check_eq(&sel_c[i], &c_zero, "neo merge empty-L")?;
			}
		} else {
			let lk_l: Vec<FpVar<F>> = (0..l_pat.len()).map(|j|
				&l_pat[j] + &(r1 * &l_loc[j])).collect();
			assert_logup_cond(cs.clone(), &qry_c, &sel_c, &lk_l,
				&sel_l.to_vec(), m_aux, r2)?;
		}
		// --- Section 6: verdict feed (2cs/row + 1 logup) ---
		// sel.is_last (LAST si tag, forced in selectors, si_step
		// pinned C5 + outer-bound so steps cannot be mislabeled).
		// qry = enc*is_last*is_c; zero rows hit acc_out's 0 slot.
		// EXAMPLE: full match a1..a8, terminal a8 C row: its enc
		//   must be in acc_out, else UNSAT -> subsig lands in
		//   failed_acc -> compute_sig reports not-discharged.
		// (1-is_step0) mirrors Section 5: seed-only (empty-chain)
		// subsigs' step-0 row is vacuously is_last but must NOT feed
		// acc_out (num>0 filter in gen_acc_and_mtbl). Real terminals
		// sit at step==num>=1, where is_step0=0, so never dropped.
		let qry_a: Vec<FpVar<F>> = (0..n).map(|i|
			&(&(&v.enc[i] * &sel.is_last[i]) * &sel.is_c[i])
				* &(&c_one - &sel.is_step0[i])).collect();
		assert_logup(cs.clone(), &qry_a, acc_out, mtbl_acc, r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.4: block=merge_acc cs={} pred={}",
			cs.num_constraints() - n0,
			13 * n + 7 * l_pat.len() + 3 * d_pat.len()));
		Ok(())
	}

	/// Aggressive-arm circuit entry: composes the five blocks. Order
	/// matters only in that C1 bits and C2 (grp_start, rid) feed the
	/// later blocks; soundness is the conjunction.
	/// COST (R1CS, n = T_qm rows, per-row rates fold logups):
	///   selectors ~19n; wf ~26n (run lemma); si pins ~14n;
	///   certs ~31n; merge+acc ~13n + 7|L| + 3|D|; TOTAL ~103n
	///   + 7|L| + 3|D| -- vs legacy aggressive fwd+acc ~84.5*n1
	///   with quadratic-walk n1; n here is theorem-bounded
	///   (linear; band-locked, test_m6_cost_band).
	///   PERF 61081.9 grand total.
	pub(crate) fn assert_neo_core_aggr(
		cs: ConstraintSystemRef<F>,
		nat: &NeoCore<F>, vars: &NeoCoreVars<F>,
		r1: &FpVar<F>, r2: &FpVar<F>, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let sel = Self::assert_neo_selectors(cs.clone(),
			&nat.t, &vars.qm, r1, true, job_id)?;
		let (_gs, rid) = Self::assert_neo_wf(cs.clone(),
			&nat.t, &vars.qm, &sel, &vars.s_enc, &vars.subsigs,
			&nat.s_enc, &nat.subsig_nat, r1, r2, job_id)?;
		Self::assert_neo_si_pins(cs.clone(), &vars.qm, &sel,
			true, job_id)?;
		Self::assert_neo_certs_aggr(cs.clone(), &nat.t, &vars.qm,
			&sel, &rid, &vars.subsigs, &nat.subsig_nat,
			&vars.mtbl_qr, r1, r2, job_id)?;
		Self::assert_neo_merge_acc_aggr(cs.clone(), &nat.t,
			&vars.qm, &sel, &vars.l_pat, &vars.l_loc,
			(&nat.l_pat, &nat.l_loc), &vars.m_aux, &vars.d_pat,
			&vars.d_cnt, &vars.d_diff, &vars.s_pat, &vars.mtbl_d,
			&vars.acc_out, &vars.mtbl_acc, r1, r2, job_id)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.9: block=TOTAL cs={} rows={}",
			cs.num_constraints() - n0, nat.t.enc.len()));
		Ok(())
	}
}

// ============================================================
//   M7: non-aggressive cert layer (paper C.1, gated !b_aggressive)
// ============================================================

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// QC rank chain (NON-AGGRESSIVE): cid[i] = (1-grp_start) *
	/// (cid[i-1] + is_wrap + is_c). Per group the QC-selected rows
	/// (wrap or C) get distinct cids 0..k+1, so a (enc, cid=1, loc)
	/// query resolves uniquely: the least CARRIED loc of the group,
	/// or the max-wrap when the group carries nothing. BP/SP/FP
	/// rows keep the previous rank and are invisible in the target.
	/// EXAMPLE a2 group [0w, 21C, 111SP, maxw]: cid 0,1,1,2 -- the
	/// (enc2, 1, .) row is 21, the kept minimum.
	/// COST: 1cs/row. PERF folded into 61081.6.
	fn assert_neo_cid_chain(
		grp_start: &[FpVar<F>], sel: &NeoSel<F>,
	) -> Vec<FpVar<F>> {
		let n = grp_start.len();
		let one = FpVar::<F>::Constant(F::one());
		let mut cid = vec![FpVar::<F>::Constant(F::zero())];
		for i in 1..n {
			let c_i = (&one - &grp_start[i])
				* &(&(&cid[i - 1] + &sel.is_wrap[i])
					+ &sel.is_c[i]);
			cid.push(c_i);
		}
		cid
	}

	/// Pins for the NON-AGGRESSIVE si columns and their masked
	/// values (the base columns' pins stay in assert_neo_si_pins).
	/// Per row:
	///  BP (mask is_bp): si_bp_prev/si_rg2_next pinned to
	///    tag(enc_next, PREV_ENCODED/RG_END); bp_prev_val ==
	///    is_bp*enc, so the outer (si,val) pair proves prev of
	///    enc_next IS this row's enc -- and the step chain being a
	///    path makes enc_next THE successor. EXAMPLE: forging
	///    enc_next = enc(step 9 of another subsig) leaves the pair
	///    (tag(enc_next', PREV), enc) absent from the DB.
	///  SP (mask is_sp): si_fz pinned to tag(enc, FZ);
	///    is_fz0 = is_zero(fz) splits enc_fz's authentication:
	///    fz==0 -> structural pin enc_fz == subsig*2^(4rb) (the
	///    seed key: DB has no SUBSIG cat for it); fz>=1 -> 2-tag
	///    step pin (NORMAL|LAST of enc_fz, value fz) + SUBSIG pin
	///    (value subsig).
	/// COST: ~22*n (incl the 1cs/row cid sub-block).
	/// MEASURED @ fig-14 n=34: 748 (0% vs 22n).
	/// PERF 61081.6.
	fn assert_neo_si_pins_nonaggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = v.enc.len();
		let rb = read_global_config().range2_bit;
		let f1 = F::from(1u64 << rb);
		let f5 = f1 * f1 * f1 * f1 * f1;
		let base = F::from(0x23001101u64) * f5 * F::from(1u64 << 32);
		let cat_c = |cid: u32| base + F::from(cid as u64) * f5;
		let c_prev = new_const_var(&cs,
			cat_c(ID_ENCODED_PREV_ENCODED) - F::from(RANGE2));
		let c_rgend = new_const_var(&cs,
			cat_c(ID_ENCODED_RG_END) - F::from(RANGE2));
		let c_fz = new_const_var(&cs,
			cat_c(ID_ENCODED_FZ) - F::from(RANGE2));
		let c_sub = new_const_var(&cs,
			cat_c(ID_ENCODED_SUBSIG) - F::from(RANGE2));
		let c_n = new_const_var(&cs, cat_c(ID_ENCODED_NORMAL_STEP));
		let c_l = new_const_var(&cs, cat_c(ID_ENCODED_LAST_STEP));
		let c_rg2t = new_const_var(&cs, F::from(RANGE2));
		let c_one = new_const_var(&cs, F::one());
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
		let na_t = &t.nonaggr;
		let na_v = &v.nonaggr;
		let is_fz0 = gen_zero_bits(&cs, &na_t.fz, &na_v.fz)?;
		for i in 0..n {
			// --- BP pins (3cs) ---
			let tag_p = &(&c_prev + &na_v.enc_next[i]);
			check_eq(&na_v.si_bp_prev[i],
				&(&(&sel.is_bp[i] * tag_p) + &c_rg2t),
				"neo si_bp_prev pin")?;
			let tag_r = &(&c_rgend + &na_v.enc_next[i]);
			check_eq(&na_v.si_rg2_next[i],
				&(&(&sel.is_bp[i] * tag_r) + &c_rg2t),
				"neo si_rg2_next pin")?;
			check_eq(&na_v.bp_prev_val[i],
				&(&sel.is_bp[i] * &v.enc[i]),
				"neo bp_prev_val bind")?;
			// --- SP pins (8cs) ---
			let tag_f = &(&c_fz + &v.enc[i]);
			check_eq(&na_v.si_fz[i],
				&(&(&sel.is_sp[i] * tag_f) + &c_rg2t),
				"neo si_fz pin")?;
			//m_sp0 = SP row at a singleton step (fz==0): enc_fz is
			//the seed key, pinned structurally.
			let m_sp0 = &sel.is_sp[i] * &is_fz0[i];
			check_prod_zero(&m_sp0,
				&(&na_v.enc_fz[i] - &(&v.subsig[i] * &c_sh4)),
				lc!(), "neo enc_fz seed pin")?;
			//m_spfz = SP row at a tracked step (fz>=1): enc_fz
			//authenticated by its step + subsig DB facts.
			let m_spfz = &sel.is_sp[i] * (&c_one - &is_fz0[i]);
			let t1 = &(&na_v.si_fz_step[i] - &c_n)
				- &na_v.enc_fz[i];
			let t2 = &(&na_v.si_fz_step[i] - &c_l)
				- &na_v.enc_fz[i];
			check_prod_zero(&m_spfz, &(&t1 * &t2), lc!(),
				"neo si_fz_step 2-tag pin")?;
			check_prod_zero(&(&c_one - &m_spfz),
				&(&na_v.si_fz_step[i] - &c_rg2t), lc!(),
				"neo si_fz_step masked")?;
			check_eq(&na_v.fz_step_val[i],
				&(&m_spfz * &na_v.fz[i]),
				"neo fz_step_val bind")?;
			let tag_s = &(&c_sub + &na_v.enc_fz[i]);
			check_eq(&na_v.si_fz_sub[i],
				&(&(&m_spfz * tag_s) + &c_rg2t),
				"neo si_fz_sub pin")?;
			check_eq(&na_v.fz_sub_val[i],
				&(&m_spfz * &v.subsig[i]),
				"neo fz_sub_val bind")?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61081.6: block=si_pins_nonaggr cs={} pred={}",
			cs.num_constraints() - n0, 22 * n));
		Ok(())
	}

	/// NON-AGGRESSIVE certificates. Two fused lookups:
	///  QR target (rank rid over non-FP rows, pack(enc,rid,loc)):
	///    FP bracket pairs + the per-subsig seed anchors -- same
	///    formulas as the aggressive C3, but WITHOUT the C family.
	///  QC target (rank cid over wrap/C rows, pack(enc,cid,loc)):
	///    C-pred (a C row's predecessor must itself be CARRIED --
	///    this is what makes C steps a contiguous prefix, which the
	///    SP freeze lookup relies on), BP min (enc_next, 1, w_next),
	///    SP freeze (enc_fz, 1, w_fz) and SP min-dom (enc, 1, w_sp).
	/// Row constraints: C window (+ the prev_loc1!=0 pin that bans
	/// the 0-wrap as a fake predecessor), FP brackets (verbatim
	/// M6), BP gap bind with the default_min fallback, SP diffs,
	/// and the BP terminal/direction pins.
	/// EXAMPLE BP a6:73 -> w_next=max (step 7 carries nothing) =>
	///   min_eff=default_min=161; d_bp=161-73-9-1=78 (RANGE2).
	/// EXAMPLE SP a2:111 -> (enc_fz=enc5,1,39) proves a5 carries;
	///   (enc2,1,21) proves the kept min; d_sp=89.
	/// COST: ~56*n (folds the 2 fused logups into the
	/// per-row rate). MEASURED @ fig-14 n=34: 1887 (-0.9%
	/// vs 56n). PERF 61081.7.
	fn assert_neo_certs_nonaggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		rid: &[FpVar<F>], cid: &[FpVar<F>], subsigs: &[FpVar<F>],
		subsig_nat: &[F], mtbl_qr: &Vec<FpVar<F>>,
		mtbl_qc: &Vec<FpVar<F>>, default_min: &FpVar<F>,
		r1: &FpVar<F>, r2: &FpVar<F>, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		let c_sh = new_const_var(&cs, F::from(1u64 << rb));
		let na_t = &t.nonaggr;
		let na_v = &v.nonaggr;
		let r1sq = r1 * r1;
		// --- Section 1: target keys + selectors (2 muls/row) ---
		let tgt_qr: Vec<FpVar<F>> = (0..n).map(|i|
			&(&v.enc[i] + &(r1 * &rid[i])) + &(&r1sq * &v.loc[i]))
			.collect();
		let sel_qr: Vec<FpVar<F>> = (0..n).map(|i|
			&(&sel.is_wrap[i] + &sel.is_c[i])
				+ &(&sel.is_bp[i] + &sel.is_sp[i])).collect();
		let tgt_qc: Vec<FpVar<F>> = (0..n).map(|i|
			&(&v.enc[i] + &(r1 * &cid[i])) + &(&r1sq * &v.loc[i]))
			.collect();
		let sel_qc: Vec<FpVar<F>> = (0..n).map(|i|
			&sel.is_wrap[i] + &sel.is_c[i]).collect();
		// masks for the FP wrap-sentinel sides (shared with the C
		// 0-wrap pin below)
		let z_pl1 = gen_zero_bits(&cs, &t.prev_loc1, &v.prev_loc1)?;
		let m_pl2 = gen_zero_bits(&cs,
			&t.prev_loc2.iter().map(|x| f_max - *x)
				.collect::<Vec<F>>(),
			&v.prev_loc2.iter().map(|x| &c_max - x)
				.collect::<Vec<_>>())?;
		// w_next==max bits: the BP "successor carries nothing"
		// branch selecting default_min.
		let z_wmax = gen_zero_bits(&cs,
			&na_t.w_next.iter().map(|x| f_max - *x)
				.collect::<Vec<F>>(),
			&na_v.w_next.iter().map(|x| &c_max - x)
				.collect::<Vec<_>>())?;
		// sel.is_last (LAST si tag, forced in selectors): BP is
		// banned on terminal rows (no step i+1 exists).
		let (mut qry_r, mut sq_r) = (vec![], vec![]);
		let (mut qry_c, mut sq_c) = (vec![], vec![]);
		for i in 0..n {
			// --- Section 2: C reach window (4cs) ---
			// gap = loc - prev_loc1 (non-aggr is forward-only);
			// d_c1 = gap-rg1, d_c2 = rg2-gap RANGE2 advice bound
			// here. Plus the 0-wrap ban: a real C row's pred loc
			// cannot be 0 -- otherwise a fake (enc_prev, 0, 0)
			// query would "reach" any loc <= rg2 and break the
			// C-prefix contiguity the freeze cert relies on.
			let sel_c = &sel.is_c[i] * (&c_one - &sel.is_step0[i]);
			let gap = &v.loc[i] - &v.prev_loc1[i];
			check_prod_zero(&sel_c,
				&(&(&gap - &v.rg1[i]) - &v.d_c1[i]), lc!(),
				"neo C d1")?;
			check_prod_zero(&sel_c,
				&(&(&v.rg2[i] - &gap) - &v.d_c2[i]), lc!(),
				"neo C d2")?;
			check_prod_zero(&sel_c, &z_pl1[i], lc!(),
				"neo C pred not 0-wrap")?;
			// --- Section 3: FP bracket gaps (6cs, M6 verbatim) ---
			let m_lo = &sel.is_fp[i] * (&c_one - &z_pl1[i]);
			let e_lo = better_select(&sel.b_bwd_row[i],
				&(&(&v.loc[i] + &v.rg1[i]) - &v.prev_loc1[i]
					- &c_one),
				&(&(&v.loc[i] - &v.prev_loc1[i]) - &v.rg2[i]
					- &c_one));
			check_prod_zero(&m_lo, &(&(&e_lo
				- &(&v.d_below_hi[i] * &c_sh)) - &v.d_below_lo[i]),
				lc!(), "neo FP below")?;
			let m_hi = &sel.is_fp[i] * (&c_one - &m_pl2[i]);
			let e_hi = better_select(&sel.b_bwd_row[i],
				&(&(&v.prev_loc2[i] - &v.loc[i]) - &v.rg2[i]
					- &c_one),
				&(&(&v.prev_loc2[i] + &v.rg1[i]) - &v.loc[i]
					- &c_one));
			check_prod_zero(&m_hi, &(&(&e_hi
				- &(&v.d_above_hi[i] * &c_sh)) - &v.d_above_lo[i]),
				lc!(), "neo FP above")?;
			check_prod_zero(&v.d_below_hi[i],
				&(&v.d_below_hi[i] - &c_one), lc!(),
				"neo hi bool")?;
			check_prod_zero(&v.d_above_hi[i],
				&(&v.d_above_hi[i] - &c_one), lc!(),
				"neo hi bool2")?;
			// --- Section 4: BP cert (4cs) ---
			// min_eff = w_next, or default_min when the successor
			// group carries nothing (its cid-1 row is the
			// max-wrap). Terminal rows can never be BP, and
			// non-aggressive has no backward subsigs.
			check_prod_zero(&sel.is_bp[i], &sel.is_last[i], lc!(),
				"neo BP not terminal")?;
			check_prod_zero(&sel.is_bp[i], &sel.b_bwd_row[i],
				lc!(), "neo BP fwd-only")?;
			let min_eff = better_select(&z_wmax[i], default_min,
				&na_v.w_next[i]);
			check_prod_zero(&sel.is_bp[i],
				&(&(&(&min_eff - &v.loc[i]) - &na_v.rg2_next[i])
					- &(&na_v.d_bp[i] + &c_one)), lc!(),
				"neo BP gap")?;
			// --- Section 5: SP certs (2cs) ---
			// freeze: w_fz must be a real C loc (< max) at step fz;
			// min-dom: the kept min sits strictly below this row.
			check_prod_zero(&sel.is_sp[i],
				&(&(&(&c_max - &na_v.w_fz[i]) - &c_one)
					- &na_v.d_fz[i]), lc!(), "neo SP freeze")?;
			check_prod_zero(&sel.is_sp[i],
				&(&(&(&v.loc[i] - &na_v.w_sp[i]) - &c_one)
					- &na_v.d_sp[i]), lc!(), "neo SP min-dom")?;
			// --- Section 6: fused lookup queries ---
			// QR: FP bracket pair (2 queries).
			let base_q = &(&v.enc_prev[i] + &(r1 * &v.prev_id1[i]))
				+ &(&r1sq * &v.prev_loc1[i]);
			qry_r.push(base_q.clone());
			sq_r.push(sel.is_fp[i].clone());
			qry_r.push(&(&v.enc_prev[i]
				+ &(r1 * &(&v.prev_id1[i] + &c_one)))
				+ &(&r1sq * &v.prev_loc2[i]));
			sq_r.push(sel.is_fp[i].clone());
			// QC: C-pred + BP min + SP freeze + SP min-dom.
			qry_c.push(base_q); sq_c.push(sel_c);
			qry_c.push(&(&na_v.enc_next[i] + r1)
				+ &(&r1sq * &na_v.w_next[i]));
			sq_c.push(sel.is_bp[i].clone());
			qry_c.push(&(&na_v.enc_fz[i] + r1)
				+ &(&r1sq * &na_v.w_fz[i]));
			sq_c.push(sel.is_sp[i].clone());
			qry_c.push(&(&v.enc[i] + r1)
				+ &(&r1sq * &na_v.w_sp[i]));
			sq_c.push(sel.is_sp[i].clone());
		}
		// seed anchors (QR): pack(subsig*2^4rb, 1, 1) per active
		// subsig -- the anti-drop cascade's ground (M6 unchanged).
		let f1c = F::from(1u64 << rb);
		let c_sh4 = new_const_var(&cs, f1c * f1c * f1c * f1c);
		let z_sub = gen_zero_bits(&cs, subsig_nat, subsigs)?;
		for (j, s) in subsigs.iter().enumerate() {
			qry_r.push(&(&(s * &c_sh4) + r1) + &r1sq);
			sq_r.push(&c_one - &z_sub[j]);
		}
		assert_logup_cond(cs.clone(), &qry_r, &sq_r, &tgt_qr,
			&sel_qr, mtbl_qr, r2)?;
		assert_logup_cond(cs.clone(), &qry_c, &sq_c, &tgt_qc,
			&sel_qc, mtbl_qc, r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.7: block=certs_nonaggr cs={} pred={}",
			cs.num_constraints() - n0, 56 * n));
		Ok(())
	}

	/// NON-AGGRESSIVE merge + carry binding (replaces the acc feed;
	/// the verdict flows through q_c into compute_sig). On top of
	/// the shared merge core:
	///  counting logup gated by b_l -- b_l is boolean, off on
	///    pads/wraps/seed, and self-enforcing (see QmNonAggrCols);
	///  carry-IN logup: every real q_i row exists in Q_m (m =
	///    m_carry_in) -- dropping a carried row = dropping a live
	///    match chain, the load-bearing union direction;
	///  carry-OUT logup: q_c rows <-> Q_m C rows with multiplicity
	///    FORCED to 1 per C row (m = ones, target sel = is_c): an
	///    exact bijection, so the committed carry IS sigma_C(Q_m).
	/// EXAMPLE: omitting C row a3:27 from q_c leaves its pole
	///   unmatched (m=1 demands one hit) -> UNSAT; smuggling BP row
	///   a6:73 into q_c queries a pole no C row provides -> UNSAT.
	/// COST: ~19*n + 7|L| + 3|D| (n-term folds the carry
	/// pins + 3 logups). MEASURED @ fig-14 n=34: 777 (+1.2%
	/// vs the 768 estimate). PERF 61081.8.
	fn assert_neo_merge_nonaggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		vars: &NeoCoreVars<F>, nat: &NeoCore<F>,
		r1: &FpVar<F>, r2: &FpVar<F>, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let c_one = new_const_var(&cs, F::one());
		let c_zero = new_const_var(&cs, F::zero());
		let na_v = &v.nonaggr;
		// --- Sections 1-4: shared merge core ---
		let sel_l = Self::assert_neo_merge_core(cs.clone(),
			&vars.l_pat, &vars.l_loc, (&nat.l_pat, &nat.l_loc),
			&vars.m_aux, &vars.d_pat, &vars.d_cnt, &vars.d_diff,
			&vars.s_pat, &vars.mtbl_d, r1, r2)?;
		// --- Section 5: b_l hygiene (2cs/row) ---
		// boolean + off on pads/wraps/seed (those rows are never
		// L matches; is_wrap is the forced-residual class).
		for i in 0..n {
			check_prod_zero(&na_v.b_l[i],
				&(&na_v.b_l[i] - &c_one), lc!(), "neo b_l bool")?;
			check_prod_zero(&na_v.b_l[i],
				&(&(&sel.is_pad[i] + &sel.is_wrap[i])
					+ &sel.is_step0[i]), lc!(),
				"neo b_l real rows only")?;
		}
		// --- Section 6: counting logup, sel = b_l ---
		// EXAMPLE: a carried-only row (a6:73, not in this chunk's
		// L) sets b_l=0 and demands nothing; turning b_l off on a
		// REAL L row instead shorts that row's cnt(pat) demand.
		let qry_cnt: Vec<FpVar<F>> = (0..n).map(|i|
			&v.pat[i] + &(r1 * &v.loc[i])).collect();
		if vars.l_pat.is_empty() {
			for i in 0..n {
				check_eq(&na_v.b_l[i], &c_zero,
					"neo b_l empty-L")?;
			}
		} else {
			let lk_l: Vec<FpVar<F>> = (0..vars.l_pat.len()).map(|j|
				&vars.l_pat[j] + &(r1 * &vars.l_loc[j])).collect();
			assert_logup_cond(cs.clone(), &qry_cnt,
				&na_v.b_l.to_vec(), &lk_l, &sel_l.to_vec(),
				&vars.m_aux, r2)?;
		}
		// --- Section 7: carry-IN logup (q_i subset-of Q_m) ---
		// query side = the COMMITTED q_i rows (the fold binds them
		// to the previous chunk's q_c), so no carried row can be
		// silently dropped from the merge.
		let sel_real: Vec<FpVar<F>> = (0..n).map(|i|
			&(&sel.is_c[i] + &sel.is_fp[i])
				+ &(&sel.is_bp[i] + &sel.is_sp[i])).collect();
		let tgt_qm: Vec<FpVar<F>> = (0..n).map(|i|
			&v.enc[i] + &(r1 * &v.loc[i])).collect();
		let z_qi = gen_zero_bits(&cs, &nat.qi_enc, &vars.qi_enc)?;
		let qry_qi: Vec<FpVar<F>> = (0..vars.qi_enc.len()).map(|j|
			&vars.qi_enc[j] + &(r1 * &vars.qi_loc[j])).collect();
		let sel_qi: Vec<FpVar<F>> = (0..vars.qi_enc.len()).map(|j|
			&c_one - &z_qi[j]).collect();
		assert_logup_cond(cs.clone(), &qry_qi, &sel_qi, &tgt_qm,
			&sel_real, &na_v.m_carry_in.to_vec(), r2)?;
		// --- Section 8: carry-OUT bijection (q_c == sigma_C) ---
		// m is the CONSTANT 1 on every C row (not advice): each C
		// row must be demanded exactly once by the committed q_c.
		let z_qc = gen_zero_bits(&cs, &nat.qc_enc, &vars.qc_enc)?;
		let qry_qc: Vec<FpVar<F>> = (0..vars.qc_enc.len()).map(|j|
			&vars.qc_enc[j] + &(r1 * &vars.qc_loc[j])).collect();
		let sel_qco: Vec<FpVar<F>> = (0..vars.qc_enc.len()).map(|j|
			&c_one - &z_qc[j]).collect();
		let ones = vec![c_one.clone(); n];
		assert_logup_cond(cs.clone(), &qry_qc, &sel_qco, &tgt_qm,
			&sel.is_c.to_vec(), &ones, r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.8: block=merge_nonaggr cs={} pred={}",
			cs.num_constraints() - n0, 19 * n
				+ 7 * vars.l_pat.len() + 3 * vars.d_pat.len()));
		Ok(())
	}

	/// Non-aggressive circuit entry: the C.1 conjunction --
	/// selectors (6-way) -> wf (+cid chain) -> si pins (base +
	/// non-aggr) -> certs (C/FP/BP/SP, two fused lookups) -> merge
	/// + carry binding. default_min = last_loc + 1 from the fsm
	/// gadget (the legacy backward-prune fallback).
	/// COST: ~151n + 7|L| + 3|D| (per-row rates fold the
	/// logups + carry pins); n is theorem-bounded
	/// (thm:linear-queue) vs the legacy quadratic walk.
	/// MEASURED @ fig-14 n=34: 5277 cs (+0.4% vs 5256
	/// estimate; band-locked, test_nonaggr_circuit_positive).
	/// PERF 61081.9 grand total.
	pub(crate) fn assert_neo_core_nonaggr(
		cs: ConstraintSystemRef<F>,
		nat: &NeoCore<F>, vars: &NeoCoreVars<F>,
		default_min: &FpVar<F>, r1: &FpVar<F>, r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let sel = Self::assert_neo_selectors(cs.clone(),
			&nat.t, &vars.qm, r1, false, job_id)?;
		let (gs, rid) = Self::assert_neo_wf(cs.clone(),
			&nat.t, &vars.qm, &sel, &vars.s_enc, &vars.subsigs,
			&nat.s_enc, &nat.subsig_nat, r1, r2, job_id)?;
		let cid = Self::assert_neo_cid_chain(&gs, &sel);
		Self::assert_neo_si_pins(cs.clone(), &vars.qm, &sel,
			false, job_id)?;
		Self::assert_neo_si_pins_nonaggr(cs.clone(), &nat.t,
			&vars.qm, &sel, job_id)?;
		Self::assert_neo_certs_nonaggr(cs.clone(), &nat.t,
			&vars.qm, &sel, &rid, &cid, &vars.subsigs,
			&nat.subsig_nat, &vars.mtbl_qr, &vars.mtbl_qc,
			default_min, r1, r2, job_id)?;
		Self::assert_neo_merge_nonaggr(cs.clone(), &nat.t,
			&vars.qm, &sel, vars, nat, r1, r2, job_id)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.9: block=TOTAL cs={} rows={}",
			cs.num_constraints() - n0, nat.t.enc.len()));
		Ok(())
	}
}

// ============================================================
//   M6: aggressive statement assembly (N3) + advice + gadget arm
// ============================================================

impl<F: PrimeField + ColEle> NeoCore<F> {
	/// store rows (enc, pat) over the active subsigs' real steps,
	/// direction-aware (backward subsigs use the reversed chain):
	/// the S universe feeding the wf uniqueness product + cnt force.
	pub(crate) fn gen_store_rows(subsigs: &Vec<F>,
		info: &SubsigStepStore) -> (Vec<F>, Vec<F>) {
		let mx = (1usize << read_global_config().range2_bit) - 1;
		let (mut es, mut ps) = (vec![], vec![]);
		for s in subsigs {
			let u = field_to_usize(s);
			let rec = info.subsig_to_steps.get(&u).unwrap();
			let rev;
			let pm = if rec.is_backward {
				rev = reverse_pm_bounds(&rec.vec_pm_bounds,
					(0, mx));
				&rev
			} else { &rec.vec_pm_bounds };
			for (i, (p, (a, b))) in pm.iter().enumerate() {
				es.push(encode_cols(&vec![vec![*s],
					vec![F::from((i + 1) as u32)],
					vec![F::from(*p as u32)],
					vec![F::from(*a as u32)],
					vec![F::from(*b as u32)]],
					&vec![0, 1, 2, 3, 4])[0]);
				ps.push(F::from(*p as u32));
			}
		}
		(es, ps)
	}

	/// assemble the full native bundle from a tagged generator
	/// output + this chunk's L columns (per-pat 0/max wraps kept),
	/// AGGRESSIVE arm (BP->C retag, C-family in mtbl_qr). The merge
	/// dictionary derives its pat universe from the store UNION the
	/// pats appearing in l_pat. Non-aggressive: gen_nonaggr.
	pub(crate) fn gen(g: &StepQueueNeo<F>, info: &SubsigStepStore,
		l_pat: Vec<F>, l_loc: Vec<F>)
	-> Result<NeoCore<F>, Error> {
		let t = g.gen_qm_table(info, true)?;
		let rid = Self::gen_rid_native(&t);
		// 8_C: subsig column = K slots (dummy-0 pad; circuit masks
		// zero slots), store rows padded to the wrap budget; both
		// shapes are capacity-only so every chunk's statement (and
		// the dummy config) is identical. Tier-1 fixtures
		// (capacity.b_aggressive=false) keep exact sizes.
		let mut subsig_nat = g.subsigs.clone();
		let (mut s_enc, mut s_pat) = Self::gen_store_rows(
			&g.subsigs, info);
		if g.capacity.b_aggressive {
			let k_slots = g.capacity.subsigs;
			let s_cap = StepQueueNeo::<F>::wrap_budget(&g.capacity);
			assert!(subsig_nat.len() <= k_slots);
			subsig_nat.resize(k_slots, F::zero());
			if s_enc.len() > s_cap {
				return Err(Error::CapErr(vec![(format!(
					"neo_qm_table, b_igc: {}", g.b_igc),
					s_enc.len())]));
			}
			s_enc.resize(s_cap, F::zero());
			s_pat.resize(s_cap, F::zero());
		}
		let s_pads = s_pat.iter().filter(|p| p.is_zero()).count();
		let mut hm_pats: HashMap<F, Vec<(F, F)>> = HashMap::new();
		for p in &l_pat { hm_pats.entry(*p).or_insert(vec![]); }
		let (d_pat, mut d_cnt) = StepQueueNeo::gen_merge_dict(
			&g.subsigs, info, &hm_pats, g.b_igc)?;
		// cnt-force logup: d_cnt = pole count of s_pat queries, so
		// the zero PADS must be counted in D's 0 entry (real L pat-0
		// rows are loc-wraps, sel_l=0 -> never query (0,m)).
		if s_pads > 0 {
			let j0 = d_pat.iter().position(|p| p.is_zero())
				.ok_or_else(|| Error::CapErr(vec![(format!(
					"neo_dict_zero_slot, b_igc: {}", g.b_igc),
					s_pads)]))?;
			d_cnt[j0] += F::from(s_pads as u32);
		}
		let mut d_diff = vec![F::zero(); d_pat.len()];
		for j in 1..d_pat.len() {
			d_diff[j] = d_pat[j] - d_pat[j - 1] - F::one();
		}
		let m_aux = StepQueueNeo::gen_merge_m_aux(&l_pat, &l_loc,
			&d_pat, &d_cnt);
		let mtbl_qr = Self::gen_mtbl_qr(&t, &rid, &subsig_nat);
		let mtbl_d = Self::gen_mtbl_d(&l_pat, &l_loc, &d_pat);
		let (acc_out, mtbl_acc) = Self::gen_acc_padded(&t, info);
		Ok(NeoCore { t, l_pat, l_loc, subsig_nat, s_enc,
			s_pat, d_pat, d_cnt, d_diff, m_aux, mtbl_qr, mtbl_d,
			acc_out, mtbl_acc,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![] })
	}
}

impl<F: PrimeField + ColEle> StepQueueNeo<F> {
	/// N3 column assembly: the "neo_core" advice container mirroring
	/// NeoCore. si policy (outer lookups): VARIABLE si for the
	/// DB-bound cols (step/subsig/pat/rg1/rg2/enc_prev/b_bwd), const
	/// RANGE2 si for the range-checked diff advice
	/// (d_c1/d_c2/d_below_lo/d_above_lo/d_sort/d_cnt/d_diff/m_aux),
	/// zero si (NOT range-checked) elsewhere -- soundness audit:
	///   enc      group-uniqueness product vs {S encs + seed encs};
	///   id/loc   wf chain + strict d_sort between 0/max sentinels;
	///   cat      unity + hygiene selectors;
	///   prev_*   challenge-packed QR-target lookups (SZ);
	///   *_hi     boolean-checked in-circuit;
	///   l_*      copy of the fsm pat_loc table (binding = M8);
	///   subsigs  compute_sig seed tie (M8);
	///   s_*      S-universe authentication (M8);
	///   d_pat    strict d_diff chain;
	///   mtbl_*   logup multiplicity advice (self-checking).
	fn core_container(nat: &NeoCore<F>)
	-> Arc<Mutex<Container<F>>> {
		let res = Container::<F>::new("neo_core");
		let f_r2 = F::from(RANGE2);
		let t = &nat.t;
		{
			let mut c = res.lock().unwrap();
			let mut var = |v: &Vec<F>, name: &str, si: &Vec<F>| {
				c.add_col(Col::new(v.clone(), name, IDX_DATA));
				c.add_col(Col::new(si.clone(),
					&format!("si_{}", name), IDX_SI_DATA));
			};
			var(&t.step, "step", &t.si_step);
			var(&t.subsig, "subsig", &t.si_subsig);
			var(&t.pat, "pat", &t.si_pat);
			var(&t.rg1, "rg1", &t.si_rg1);
			var(&t.rg2, "rg2", &t.si_rg2);
			var(&t.enc_prev, "enc_prev", &t.si_enc_prev);
			var(&t.b_bwd, "b_bwd", &t.si_b_bwd);
			//non-aggressive witness cols with VARIABLE si (the DB
			//tags carry advice keys enc_next/enc_fz); empty vecs
			//under aggressive => nothing emitted, M6 layout intact.
			if !t.nonaggr.b_l.is_empty() {
				let na = &t.nonaggr;
				var(&na.bp_prev_val, "bp_prev_val",
					&na.si_bp_prev);
				var(&na.rg2_next, "rg2_next", &na.si_rg2_next);
				var(&na.fz, "fz", &na.si_fz);
				var(&na.fz_step_val, "fz_step_val",
					&na.si_fz_step);
				var(&na.fz_sub_val, "fz_sub_val", &na.si_fz_sub);
			}
		}
		if !t.nonaggr.b_l.is_empty() {
			//non-aggressive advice cols with CONST si: lookup
			//witnesses + logup multiplicities zero-si (bound by
			//their logups), diffs RANGE2 (outer range check).
			let mut c = res.lock().unwrap();
			let mut fix = |v: &Vec<F>, name: &str, si_val: F| {
				c.add_col(Col::new(v.clone(), name, IDX_DATA));
				c.add_col(Col::new_const(
					vec![si_val; v.len()],
					&format!("si_{}", name), IDX_SI_DATA));
			};
			let z = F::zero();
			let na = &t.nonaggr;
			fix(&na.b_l, "b_l", z);
			fix(&na.enc_next, "enc_next", z);
			fix(&na.w_next, "w_next", z);
			fix(&na.d_bp, "d_bp", f_r2);
			fix(&na.enc_fz, "enc_fz", z);
			fix(&na.w_fz, "w_fz", z);
			fix(&na.d_fz, "d_fz", f_r2);
			fix(&na.w_sp, "w_sp", z);
			fix(&na.d_sp, "d_sp", f_r2);
			fix(&na.m_carry_in, "m_carry_in", z);
			fix(&nat.mtbl_qc, "mtbl_qc", z);
		}
		{
			let mut c = res.lock().unwrap();
			let mut fix = |v: &Vec<F>, name: &str, si_val: F| {
				c.add_col(Col::new(v.clone(), name, IDX_DATA));
				c.add_col(Col::new_const(
					vec![si_val; v.len()],
					&format!("si_{}", name), IDX_SI_DATA));
			};
			let z = F::zero();
			fix(&t.enc, "enc", z);
			fix(&t.id, "id", z);
			fix(&t.loc, "loc", z);
			fix(&t.cat, "cat", z);
			fix(&t.prev_id1, "prev_id1", z);
			fix(&t.prev_loc1, "prev_loc1", z);
			fix(&t.prev_loc2, "prev_loc2", z);
			fix(&t.d_c1, "d_c1", f_r2);
			fix(&t.d_c2, "d_c2", f_r2);
			fix(&t.d_below_lo, "d_below_lo", f_r2);
			fix(&t.d_below_hi, "d_below_hi", z);
			fix(&t.d_above_lo, "d_above_lo", f_r2);
			fix(&t.d_above_hi, "d_above_hi", z);
			fix(&t.d_sort, "d_sort", f_r2);
			fix(&nat.l_pat, "l_pat", z);
			fix(&nat.l_loc, "l_loc", z);
			fix(&nat.subsig_nat, "subsigs", z);
			fix(&nat.s_enc, "s_enc", z);
			fix(&nat.s_pat, "s_pat", z);
			fix(&nat.d_pat, "d_pat", z);
			fix(&nat.d_cnt, "d_cnt", f_r2);
			fix(&nat.d_diff, "d_diff", f_r2);
			fix(&nat.m_aux, "m_aux", f_r2);
			fix(&nat.mtbl_qr, "mtbl_qr", z);
			fix(&nat.mtbl_d, "mtbl_d", z);
		}
		res
	}

	/// N3: assemble the aggressive statement from the tagged Q_m --
	/// the "neo_core" advice container plus the legacy-named
	/// "failed_acc_combo" verdict feed (FailedSubsigAcc sizing +
	/// completeness m-table, byte-compatible with what compute_sig
	/// reads). Returns both containers and the native bundle with
	/// its acc re-shaped to the container layout.
	pub(crate) fn gen_core_stmt(&self,
		pat_loc: &Arc<Mutex<Container<F>>>, info: &SubsigStepStore)
	-> Result<(Arc<Mutex<Container<F>>>, Arc<Mutex<Container<F>>>,
		NeoCore<F>), Error> {
		let l_pat = pat_loc.lock().unwrap()
			.get_container("sorted_key").unwrap()
			.lock().unwrap().to_vec();
		let l_loc = pat_loc.lock().unwrap()
			.get_container("sorted_val").unwrap()
			.lock().unwrap().to_vec();
		let mut nat = NeoCore::gen(self, info, l_pat,
			l_loc)?;
		let term: Vec<F> = nat.acc_out.iter()
			.filter(|e| !e.is_zero()).cloned().collect();
		let acc = FailedSubsigAcc { acc: term,
			capacity: self.capacity.clone(), b_igc: self.b_igc };
		let ct_acc = acc.to_container("failed_acc")?;
		let acc_vec = ct_acc.lock().unwrap()
			.get_container("acc_encoded").unwrap()
			.lock().unwrap().to_vec();
		let f_c = F::from(CAT_C);
		// !step0 mirrors the circuit acc-feed gate: seed-only
		// (empty-chain) rows are vacuously is_last but never complete
		// (excluded from acc_vec by gen_acc_and_mtbl's num>0 filter),
		// so they must not be counted as nonzero terminal queries here
		// either -- else mtbl_acc's zero slot undercounts by that many.
		let qry_final: Vec<F> = (0..nat.t.enc.len()).map(|i| {
			let last_tag = SubsigStepStore::gen_step_tbl_id(
				nat.t.enc[i], ID_ENCODED_LAST_STEP);
			if nat.t.si_step[i] == last_tag
				&& nat.t.cat[i] == f_c
				&& !nat.t.step[i].is_zero() { nat.t.enc[i] }
			else { F::zero() }
		}).collect();
		let mtbl_complete = gen_m_table(&qry_final, &acc_vec);
		let combo = Container::<F>::new("failed_acc_combo");
		let prf = Container::<F>::new("failed_acc_prf");
		let nc = mtbl_complete.len();
		prf.lock().unwrap().add_col(Col::new(
			mtbl_complete.clone(), "mtbl_complete", IDX_DATA));
		prf.lock().unwrap().add_col(Col::new_const(
			vec![F::zero(); nc], "si_mtbl_complete", IDX_SI_DATA));
		combo.lock().unwrap().add_container(ct_acc);
		combo.lock().unwrap().add_container(prf);
		nat.acc_out = acc_vec;
		nat.mtbl_acc = mtbl_complete;
		let core = Self::core_container(&nat);
		Ok((core, combo, nat))
	}

	/// NON-AGGRESSIVE statement assembly (paper C.1): the "neo_core"
	/// advice container (with the QmNonAggrCols extension) plus the
	/// two COMMITTED transport containers "q_i" (IDX_INP, the
	/// carried-in queue -- the fold binds it to the previous
	/// chunk's q_c) and "q_c" (IDX_OUP, the C projection of Q_m).
	/// No failed_acc: the verdict flows through q_c into
	/// compute_sig (M8 wiring). self = the TAGGED generator output
	/// AFTER apply_sp_pass; carried = the raw Q_i this chunk
	/// received.
	pub(crate) fn gen_core_stmt_nonaggr(&self,
		pat_loc: &Arc<Mutex<Container<F>>>, info: &SubsigStepStore,
		carried: &StepQueue<F>, default_min: F, job_id: usize)
	-> Result<(Arc<Mutex<Container<F>>>, Arc<Mutex<Container<F>>>,
		Arc<Mutex<Container<F>>>, NeoCore<F>), Error> {
		let l_pat = pat_loc.lock().unwrap()
			.get_container("sorted_key").unwrap()
			.lock().unwrap().to_vec();
		let l_loc = pat_loc.lock().unwrap()
			.get_container("sorted_val").unwrap()
			.lock().unwrap().to_vec();
		let hm_loc = StepQueue::<F>::pat_loc_to_hm(pat_loc);
		let (nat, ct_qi, ct_qc) = NeoCore::gen_nonaggr(self, info,
			l_pat, l_loc, &hm_loc, carried, default_min, job_id)?;
		let core = Self::core_container(&nat);
		Ok((core, ct_qi, ct_qc, nat))
	}
}

/// M6 advice for the AGGRESSIVE arm: seed-only universe carry, M5
/// shared core, N3 statement. Mirrors DischargeAdvAdvice::new's
/// aggressive branch; non-aggressive callers keep the legacy advice.
#[derive(Clone, Debug)]
pub struct DischargeAdvNeoAdvice<F: PrimeField + ColEle> {
	pub capacity: DischargeAdvCapacity,
	pub fsm_id: u32,
	pub stmt_container: Arc<Mutex<Container<F>>>,
	pub b_igc: bool,
	pub offset_fsm: usize,
}

impl<F: PrimeField + ColEle> NdAdvice for DischargeAdvNeoAdvice<F> {
	fn as_any(&self) -> &dyn Any { self }
}

impl<F: PrimeField + ColEle> ComponentAdvice<F>
	for DischargeAdvNeoAdvice<F> {
	fn get_container(&self) -> Arc<Mutex<Container<F>>> {
		self.stmt_container.clone()
	}
}

impl<F: PrimeField + ColEle> DischargeAdvNeoAdvice<F> {
	/// mode dispatcher mirroring DischargeAdvAdvice::new's signature
	/// (the sed_mapper swap point in M8): aggressive ignores the
	/// carried queue (seed-only universe), non-aggressive consumes
	/// it as this chunk's Q_i.
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		pat_loc: &Arc<Mutex<Container<F>>>,
		inp_subsigs: &Vec<F>,
		fsm_id: u32,
		subsig_store_info: &SubsigStepStore,
		capacity: &DischargeAdvCapacity,
		inp_step_queue: &StepQueue<F>,
		last_loc: F,
		seg_id: usize,
		job_id: usize,
	) -> Result<Self, Error> {
		if capacity.b_aggressive {
			Self::new_aggr(b_igc, offset_fsm, pat_loc,
				inp_subsigs, fsm_id, subsig_store_info, capacity,
				last_loc, seg_id, job_id)
		} else {
			Self::new_nonaggr(b_igc, offset_fsm, pat_loc, fsm_id,
				subsig_store_info, capacity, inp_step_queue,
				last_loc, job_id)
		}
	}

	/// NON-AGGRESSIVE ctor (paper C.1 prune): Q_i = the carried-in
	/// queue, shared core {C,FP,BP} + apply_sp_pass, then the
	/// statement {neo_core, q_i, q_c}. inp_subsigs is NOT taken:
	/// the active set is the carried queue's (the compute_sig
	/// NEEDS tie is M8's wiring, like aggressive's seed tie).
	pub fn new_nonaggr(
		b_igc: bool,
		offset_fsm: usize,
		pat_loc: &Arc<Mutex<Container<F>>>,
		fsm_id: u32,
		subsig_store_info: &SubsigStepStore,
		capacity: &DischargeAdvCapacity,
		inp_step_queue: &StepQueue<F>,
		last_loc: F,
		job_id: usize,
	) -> Result<Self, Error> {
		assert!(!capacity.b_aggressive);
		let sname = if b_igc { "discharge_adv_stmt_igc" }
			else { "discharge_adv_stmt_cs" };
		let stmt_container = Container::<F>::new(sname);
		// M8b: seed the shared core over the FIXED universe (mirrors
		// new_aggr) so neo_core is fold-invariant; real carry rows
		// overlay the seed. q_i/q_c still carry the real inp_step_queue.
		// Universe = non-empty-chain subsigs only, matching sed_mapper's
		// uni() (empty-chain can never carry a C row and would underflow
		// compute_sig's num==0), so q_c's subsig set == compute_sig's
		// inp_subsigs every chunk.
		let is_uni = |u: usize| subsig_store_info.subsig_to_steps
			.get(&u).map_or(false, |it| !it.vec_pm_bounds.is_empty());
		let seed_subsigs = subsig_store_info.subsig_ids.iter()
			.filter(|u| is_uni(**u))
			.map(|u| F::from(*u as u32)).collect::<Vec<F>>();
		let mut merged = DischargeAdvAdvice::<F>
			::gen_empty_steps_queue_serialized(b_igc, &seed_subsigs,
				subsig_store_info, fsm_id, capacity);
		for (s, items) in inp_step_queue.store_items.iter() {
			if is_uni(field_to_usize(s)) {
				merged.store_items.insert(*s, items.clone());
			}
		}
		let carried = StepQueueNeo::from_stepqueue(merged);
		let mut gen = carried.gen_shared_core_advice(job_id,
			pat_loc, subsig_store_info, last_loc + F::one())?;
		gen.apply_sp_pass(subsig_store_info);
		let (core, ct_qi, ct_qc, _nat) = gen
			.gen_core_stmt_nonaggr(pat_loc, subsig_store_info,
				inp_step_queue, last_loc + F::one(), job_id)?;
		stmt_container.lock().unwrap().add_container(core);
		stmt_container.lock().unwrap().add_container(ct_qi);
		stmt_container.lock().unwrap().add_container(ct_qc);
		Ok(Self { capacity: capacity.clone(), fsm_id,
			stmt_container, b_igc, offset_fsm })
	}

	/// AGGRESSIVE-ONLY ctor (asserts capacity.b_aggressive): seed
	/// THIS CHUNK's NEEDS set (nonzero inp_subsigs, non-empty-chain;
	/// 8_C), run the M5 shared core against this chunk's pat_loc,
	/// and emit the N3 statement under the legacy stmt names. Shape
	/// is chunk-invariant via capacity budgets (qm wrap budget, K
	/// subsig slots, S_cap store pad, constant full-store D).
	pub fn new_aggr(
		b_igc: bool,
		offset_fsm: usize,
		pat_loc: &Arc<Mutex<Container<F>>>,
		inp_subsigs: &Vec<F>,
		fsm_id: u32,
		subsig_store_info: &SubsigStepStore,
		capacity: &DischargeAdvCapacity,
		last_loc: F,
		_seg_id: usize,
		job_id: usize,
	) -> Result<Self, Error> {
		assert!(capacity.b_aggressive);
		let sname = if b_igc { "discharge_adv_stmt_igc" }
			else { "discharge_adv_stmt_cs" };
		let stmt_container = Container::<F>::new(sname);
		// 8_C: seed this chunk's NEEDS set -- nonzero inp_subsigs,
		// filtered to non-empty-chain (mirrors compute_sig's
		// empty-chain drop, so the seed-pin sets stay equal). Cold
		// subsigs are covered by CP-absence (legacy architecture);
		// the wf run lemma forces full chains for every seeded one.
		let is_uni = |u: usize| subsig_store_info.subsig_to_steps
			.get(&u).map_or(false, |it| !it.vec_pm_bounds.is_empty());
		let mut seed_subsigs = inp_subsigs.iter()
			.filter(|s| !s.is_zero())
			.filter(|s| is_uni(field_to_usize(*s)))
			.cloned().collect::<Vec<F>>();
		seed_subsigs.sort();
		seed_subsigs.dedup();
		if seed_subsigs.len() > capacity.subsigs {
			return Err(Error::CapErr(vec![(format!(
				"neo_subsig_slots, b_igc: {}", b_igc),
				seed_subsigs.len())]));
		}
		let seed = DischargeAdvAdvice::<F>
			::gen_empty_steps_queue_serialized(b_igc,
			&seed_subsigs, subsig_store_info, fsm_id, capacity);
		let carried = StepQueueNeo::from_stepqueue(seed);
		let gen = carried.gen_shared_core_advice(job_id, pat_loc,
			subsig_store_info, last_loc + F::one())?;
		let (core, combo, nat) = gen.gen_core_stmt(pat_loc,
			subsig_store_info)?;
		stmt_container.lock().unwrap().add_container(core);
		stmt_container.lock().unwrap().add_container(combo);
		// Publish seed encodings (subsig*2^4rb per SEEDED NEEDS
		// subsig; K+1 slots after the K-pad of subsig_nat) so
		// compute_sig's aggressive seed-pin reads a uniform source.
		// A leading 0 entry is REQUIRED: compute_sig pads inp_subsigs
		// with dummy-0s (enc 0), so the seed table must contain 0 to
		// absorb those zero queries (else the seed-pin logup is
		// unsat); dummy-0 slots just duplicate it (harmless).
		let mut seed_enc: Vec<F> = vec![F::zero()];
		seed_enc.extend(nat.subsig_nat.iter().map(|s|
			encode_cols(&vec![vec![*s], vec![F::zero()],
				vec![F::zero()], vec![F::zero()], vec![F::zero()]],
				&vec![0, 1, 2, 3, 4])[0]));
		let n_seed = seed_enc.len();
		let fwd_seed = Container::<F>::new("fwd_seed");
		fwd_seed.lock().unwrap().add_col(Col::new(seed_enc,
			"encoded", IDX_DATA));
		// companion si col (no outer lookup) keeps data/subtbl_id
		// balanced in the statement assembly (fix/prf pattern).
		fwd_seed.lock().unwrap().add_col(Col::new_const(
			vec![F::zero(); n_seed], "si_encoded", IDX_SI_DATA));
		stmt_container.lock().unwrap().add_container(fwd_seed);
		Ok(Self { capacity: capacity.clone(), fsm_id,
			stmt_container, b_igc, offset_fsm })
	}

	/// aggressive: no cross-chunk carried step-queue (legacy parity
	/// with DischargeAdvAdvice::get_output_steps_queue).
	/// non-aggressive: the committed q_c serialization (encoded ++
	/// locs), which the fold hands to the next chunk as its Q_i.
	pub fn get_output_steps_queue(&self) -> Vec<F> {
		if self.capacity.b_aggressive { return vec![]; }
		let sname = if self.b_igc { "discharge_adv_stmt_igc" }
			else { "discharge_adv_stmt_cs" };
		let res = self.stmt_container.lock().unwrap()
			.search_container(&format!("{} q_c", sname)).unwrap();
		let encoded = res.lock().unwrap().get_container("encoded")
			.unwrap().lock().unwrap().to_vec();
		let locs = res.lock().unwrap().get_container("locs")
			.unwrap().lock().unwrap().to_vec();
		vec![encoded, locs].concat()
	}
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// load one named neo_core column as (vars, native values).
	fn col2(core: &Arc<Mutex<Container<FpVar<F>>>>, name: &str)
	-> Result<(Vec<FpVar<F>>, Vec<F>), SynthesisError> {
		let v = core.lock().unwrap().get_container(name)?
			.lock().unwrap().to_vec();
		let nat = v.iter().map(|x| x.value())
			.collect::<Result<Vec<F>, SynthesisError>>()?;
		Ok((v, nat))
	}

	/// M6 aggressive assert arm: load the neo statement, rebuild the
	/// native bundle from witness values (legacy value()-hint
	/// precedent), and run the five-block aggressive core.
	fn assert_msg3_neo_aggr(&self, i: usize,
		cs: ConstraintSystemRef<F>, wtns: &WitnessSigmaIR1CSVar<F>,
		wtns_cfg: &WitnessSigmaIR1CSConfig)
	-> Result<(), SynthesisError> {
		let cfg = self.inner.get_container_config();
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg,
			wtns, &cfg)?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();
		let core = stmt.get_container("neo_core")?;
		let c2 = |n: &str| Self::col2(&core, n);
		let (enc, enc_n) = c2("enc")?;
		let (id, id_n) = c2("id")?;
		let (loc, loc_n) = c2("loc")?;
		let (cat, cat_n) = c2("cat")?;
		let (step, step_n) = c2("step")?;
		let (subsig, subsig_n) = c2("subsig")?;
		let (prev_id1, prev_id1_n) = c2("prev_id1")?;
		let (prev_loc1, prev_loc1_n) = c2("prev_loc1")?;
		let (prev_loc2, prev_loc2_n) = c2("prev_loc2")?;
		let (pat, pat_n) = c2("pat")?;
		let (rg1, rg1_n) = c2("rg1")?;
		let (rg2, rg2_n) = c2("rg2")?;
		let (enc_prev, enc_prev_n) = c2("enc_prev")?;
		let (b_bwd, b_bwd_n) = c2("b_bwd")?;
		let (d_c1, d_c1_n) = c2("d_c1")?;
		let (d_c2, d_c2_n) = c2("d_c2")?;
		let (d_below_lo, d_below_lo_n) = c2("d_below_lo")?;
		let (d_below_hi, d_below_hi_n) = c2("d_below_hi")?;
		let (d_above_lo, d_above_lo_n) = c2("d_above_lo")?;
		let (d_above_hi, d_above_hi_n) = c2("d_above_hi")?;
		let (d_sort, d_sort_n) = c2("d_sort")?;
		let (si_step, si_step_n) = c2("si_step")?;
		let (si_subsig, si_subsig_n) = c2("si_subsig")?;
		let (si_pat, si_pat_n) = c2("si_pat")?;
		let (si_rg1, si_rg1_n) = c2("si_rg1")?;
		let (si_rg2, si_rg2_n) = c2("si_rg2")?;
		let (si_enc_prev, si_enc_prev_n) = c2("si_enc_prev")?;
		let (si_b_bwd, si_b_bwd_n) = c2("si_b_bwd")?;
		let (l_pat, l_pat_n) = c2("l_pat")?;
		let (l_loc, l_loc_n) = c2("l_loc")?;
		let (subsigs, subsigs_n) = c2("subsigs")?;
		let (s_enc, s_enc_n) = c2("s_enc")?;
		let (s_pat, s_pat_n) = c2("s_pat")?;
		let (d_pat, d_pat_n) = c2("d_pat")?;
		let (d_cnt, d_cnt_n) = c2("d_cnt")?;
		let (d_diff, d_diff_n) = c2("d_diff")?;
		let (m_aux, m_aux_n) = c2("m_aux")?;
		let (mtbl_qr, mtbl_qr_n) = c2("mtbl_qr")?;
		let (mtbl_d, mtbl_d_n) = c2("mtbl_d")?;
		let combo = stmt.get_container("failed_acc_combo")?;
		let facc = combo.lock().unwrap()
			.get_container("failed_acc")?;
		let (acc_out, acc_out_n) = Self::col2(&facc,
			"acc_encoded")?;
		let fprf = combo.lock().unwrap()
			.get_container("failed_acc_prf")?;
		let (mtbl_acc, mtbl_acc_n) = Self::col2(&fprf,
			"mtbl_complete")?;
		let n_pad = enc_n.iter().take_while(|e| e.is_zero())
			.count();
		let t = QmTable { enc: enc_n, id: id_n, loc: loc_n,
			cat: cat_n, step: step_n, subsig: subsig_n,
			prev_id1: prev_id1_n, prev_loc1: prev_loc1_n,
			prev_loc2: prev_loc2_n, pat: pat_n, rg1: rg1_n,
			rg2: rg2_n, enc_prev: enc_prev_n, b_bwd: b_bwd_n,
			d_c1: d_c1_n, d_c2: d_c2_n,
			d_below_lo: d_below_lo_n, d_below_hi: d_below_hi_n,
			d_above_lo: d_above_lo_n, d_above_hi: d_above_hi_n,
			d_sort: d_sort_n, si_step: si_step_n,
			si_subsig: si_subsig_n, si_pat: si_pat_n,
			si_rg1: si_rg1_n, si_rg2: si_rg2_n,
			si_enc_prev: si_enc_prev_n, si_b_bwd: si_b_bwd_n,
			nonaggr: QmNonAggrCols::default(), n_pad };
		let nat = NeoCore { t, l_pat: l_pat_n,
			l_loc: l_loc_n, subsig_nat: subsigs_n,
			s_enc: s_enc_n, s_pat: s_pat_n, d_pat: d_pat_n,
			d_cnt: d_cnt_n, d_diff: d_diff_n, m_aux: m_aux_n,
			mtbl_qr: mtbl_qr_n, mtbl_d: mtbl_d_n,
			acc_out: acc_out_n, mtbl_acc: mtbl_acc_n,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![] };
		let qm = QmVars { enc, id, loc, cat, step, subsig,
			prev_id1, prev_loc1, prev_loc2, pat, rg1, rg2,
			enc_prev, b_bwd, d_c1, d_c2, d_below_lo, d_below_hi,
			d_above_lo, d_above_hi, d_sort, si_step, si_subsig,
			si_pat, si_rg1, si_rg2, si_enc_prev, si_b_bwd,
			nonaggr: QmNonAggrVars::empty() };
		let vars = NeoCoreVars { qm, l_pat, l_loc, subsigs,
			s_enc, s_pat, d_pat, d_cnt, d_diff, m_aux, mtbl_qr,
			mtbl_d, acc_out, mtbl_acc,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![] };
		Self::assert_neo_core_aggr(cs, &nat, &vars, &r1, &r2,
			self.inner.get_job_id())
	}

	/// M7 non-aggressive assert arm: load the neo statement (core +
	/// the QmNonAggrCols extension + the committed q_i/q_c
	/// transport), rebuild the native bundle from witness values
	/// (hints only), derive default_min = last fsm loc + 1 from the
	/// PREVIOUS gadget's statement (legacy assert_msg3 step 2), and
	/// run the C.1 core.
	fn assert_msg3_neo_nonaggr(&self, i: usize,
		cs: ConstraintSystemRef<F>, wtns: &WitnessSigmaIR1CSVar<F>,
		wtns_cfg: &WitnessSigmaIR1CSConfig)
	-> Result<(), SynthesisError> {
		let cfg = self.inner.get_container_config();
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg,
			wtns, &cfg)?;
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();
		//default_min: last fsm-acc loc + 1 (the legacy retrieval;
		//the fsm gadget sits offset_fsm slots earlier).
		let my_name = if self.inner.b_igc
			{ "discharge_adv_stmt_igc" }
			else { "discharge_adv_stmt_cs" };
		let ctx = self.inner.cfgs_context.as_ref()
			.expect("cfgs_context not set");
		let my_idx = ctx.iter().enumerate()
			.filter(|(_i, c)| c.get_name() == my_name)
			.map(|(i, _c)| i).collect::<Vec<_>>()[0];
		let prev_cfg = ctx[my_idx - self.inner.offset_fsm].clone();
		let prev_stmt = Container::<FpVar<F>>::load_from(
			i - self.inner.offset_fsm, wtns_cfg, wtns, &prev_cfg)?;
		let sname_fsm = if self.inner.b_igc { "fsm_adv_stmt_igc" }
			else { "fsm_adv_stmt_cs" };
		let locs = prev_stmt.search_container(&format!(
			"{} fsm_acc locs", sname_fsm))?
			.lock().unwrap().to_vec();
		let default_min = &locs[locs.len() - 1]
			+ &new_const_var(&cs, F::one());
		//load neo_core (base + nonaggr cols)
		let core = stmt.get_container("neo_core")?;
		let c2 = |n: &str| Self::col2(&core, n);
		let (enc, enc_n) = c2("enc")?;
		let (id, id_n) = c2("id")?;
		let (loc, loc_n) = c2("loc")?;
		let (cat, cat_n) = c2("cat")?;
		let (step, step_n) = c2("step")?;
		let (subsig, subsig_n) = c2("subsig")?;
		let (prev_id1, prev_id1_n) = c2("prev_id1")?;
		let (prev_loc1, prev_loc1_n) = c2("prev_loc1")?;
		let (prev_loc2, prev_loc2_n) = c2("prev_loc2")?;
		let (pat, pat_n) = c2("pat")?;
		let (rg1, rg1_n) = c2("rg1")?;
		let (rg2, rg2_n) = c2("rg2")?;
		let (enc_prev, enc_prev_n) = c2("enc_prev")?;
		let (b_bwd, b_bwd_n) = c2("b_bwd")?;
		let (d_c1, d_c1_n) = c2("d_c1")?;
		let (d_c2, d_c2_n) = c2("d_c2")?;
		let (d_below_lo, d_below_lo_n) = c2("d_below_lo")?;
		let (d_below_hi, d_below_hi_n) = c2("d_below_hi")?;
		let (d_above_lo, d_above_lo_n) = c2("d_above_lo")?;
		let (d_above_hi, d_above_hi_n) = c2("d_above_hi")?;
		let (d_sort, d_sort_n) = c2("d_sort")?;
		let (si_step, si_step_n) = c2("si_step")?;
		let (si_subsig, si_subsig_n) = c2("si_subsig")?;
		let (si_pat, si_pat_n) = c2("si_pat")?;
		let (si_rg1, si_rg1_n) = c2("si_rg1")?;
		let (si_rg2, si_rg2_n) = c2("si_rg2")?;
		let (si_enc_prev, si_enc_prev_n) = c2("si_enc_prev")?;
		let (si_b_bwd, si_b_bwd_n) = c2("si_b_bwd")?;
		let (b_l, b_l_n) = c2("b_l")?;
		let (enc_next, enc_next_n) = c2("enc_next")?;
		let (bp_prev_val, bp_prev_val_n) = c2("bp_prev_val")?;
		let (rg2_next, rg2_next_n) = c2("rg2_next")?;
		let (w_next, w_next_n) = c2("w_next")?;
		let (d_bp, d_bp_n) = c2("d_bp")?;
		let (fz, fz_n) = c2("fz")?;
		let (enc_fz, enc_fz_n) = c2("enc_fz")?;
		let (fz_step_val, fz_step_val_n) = c2("fz_step_val")?;
		let (fz_sub_val, fz_sub_val_n) = c2("fz_sub_val")?;
		let (w_fz, w_fz_n) = c2("w_fz")?;
		let (d_fz, d_fz_n) = c2("d_fz")?;
		let (w_sp, w_sp_n) = c2("w_sp")?;
		let (d_sp, d_sp_n) = c2("d_sp")?;
		let (m_carry_in, m_carry_in_n) = c2("m_carry_in")?;
		let (si_bp_prev, si_bp_prev_n) = c2("si_bp_prev_val")?;
		let (si_rg2_next, si_rg2_next_n) = c2("si_rg2_next")?;
		let (si_fz, si_fz_n) = c2("si_fz")?;
		let (si_fz_step, si_fz_step_n) = c2("si_fz_step_val")?;
		let (si_fz_sub, si_fz_sub_n) = c2("si_fz_sub_val")?;
		let (l_pat, l_pat_n) = c2("l_pat")?;
		let (l_loc, l_loc_n) = c2("l_loc")?;
		let (subsigs, subsigs_n) = c2("subsigs")?;
		let (s_enc, s_enc_n) = c2("s_enc")?;
		let (s_pat, s_pat_n) = c2("s_pat")?;
		let (d_pat, d_pat_n) = c2("d_pat")?;
		let (d_cnt, d_cnt_n) = c2("d_cnt")?;
		let (d_diff, d_diff_n) = c2("d_diff")?;
		let (m_aux, m_aux_n) = c2("m_aux")?;
		let (mtbl_qr, mtbl_qr_n) = c2("mtbl_qr")?;
		let (mtbl_d, mtbl_d_n) = c2("mtbl_d")?;
		let (mtbl_qc, mtbl_qc_n) = c2("mtbl_qc")?;
		//committed transport containers
		let ct_qi = stmt.get_container("q_i")?;
		let (qi_enc, qi_enc_n) = Self::col2(&ct_qi, "encoded")?;
		let (qi_loc, qi_loc_n) = Self::col2(&ct_qi, "locs")?;
		let ct_qc = stmt.get_container("q_c")?;
		let (qc_enc, qc_enc_n) = Self::col2(&ct_qc, "encoded")?;
		let (qc_loc, qc_loc_n) = Self::col2(&ct_qc, "locs")?;
		let n_pad = enc_n.iter().take_while(|e| e.is_zero())
			.count();
		let na_t = QmNonAggrCols { b_l: b_l_n,
			enc_next: enc_next_n, bp_prev_val: bp_prev_val_n,
			rg2_next: rg2_next_n, w_next: w_next_n, d_bp: d_bp_n,
			fz: fz_n, enc_fz: enc_fz_n,
			fz_step_val: fz_step_val_n, fz_sub_val: fz_sub_val_n,
			w_fz: w_fz_n, d_fz: d_fz_n, w_sp: w_sp_n,
			d_sp: d_sp_n, m_carry_in: m_carry_in_n,
			si_bp_prev: si_bp_prev_n, si_rg2_next: si_rg2_next_n,
			si_fz: si_fz_n, si_fz_step: si_fz_step_n,
			si_fz_sub: si_fz_sub_n };
		let t = QmTable { enc: enc_n, id: id_n, loc: loc_n,
			cat: cat_n, step: step_n, subsig: subsig_n,
			prev_id1: prev_id1_n, prev_loc1: prev_loc1_n,
			prev_loc2: prev_loc2_n, pat: pat_n, rg1: rg1_n,
			rg2: rg2_n, enc_prev: enc_prev_n, b_bwd: b_bwd_n,
			d_c1: d_c1_n, d_c2: d_c2_n,
			d_below_lo: d_below_lo_n, d_below_hi: d_below_hi_n,
			d_above_lo: d_above_lo_n, d_above_hi: d_above_hi_n,
			d_sort: d_sort_n, si_step: si_step_n,
			si_subsig: si_subsig_n, si_pat: si_pat_n,
			si_rg1: si_rg1_n, si_rg2: si_rg2_n,
			si_enc_prev: si_enc_prev_n, si_b_bwd: si_b_bwd_n,
			nonaggr: na_t, n_pad };
		let nat = NeoCore { t, l_pat: l_pat_n, l_loc: l_loc_n,
			subsig_nat: subsigs_n, s_enc: s_enc_n, s_pat: s_pat_n,
			d_pat: d_pat_n, d_cnt: d_cnt_n, d_diff: d_diff_n,
			m_aux: m_aux_n, mtbl_qr: mtbl_qr_n, mtbl_d: mtbl_d_n,
			acc_out: vec![], mtbl_acc: vec![],
			qi_enc: qi_enc_n, qi_loc: qi_loc_n,
			qc_enc: qc_enc_n, qc_loc: qc_loc_n,
			mtbl_qc: mtbl_qc_n };
		let na_v = QmNonAggrVars { b_l, enc_next, bp_prev_val,
			rg2_next, w_next, d_bp, fz, enc_fz, fz_step_val,
			fz_sub_val, w_fz, d_fz, w_sp, d_sp, m_carry_in,
			si_bp_prev, si_rg2_next, si_fz, si_fz_step,
			si_fz_sub };
		let qm = QmVars { enc, id, loc, cat, step, subsig,
			prev_id1, prev_loc1, prev_loc2, pat, rg1, rg2,
			enc_prev, b_bwd, d_c1, d_c2, d_below_lo, d_below_hi,
			d_above_lo, d_above_hi, d_sort, si_step, si_subsig,
			si_pat, si_rg1, si_rg2, si_enc_prev, si_b_bwd,
			nonaggr: na_v };
		let vars = NeoCoreVars { qm, l_pat, l_loc, subsigs,
			s_enc, s_pat, d_pat, d_cnt, d_diff, m_aux, mtbl_qr,
			mtbl_d, acc_out: vec![], mtbl_acc: vec![],
			qi_enc, qi_loc, qc_enc, qc_loc, mtbl_qc };
		Self::assert_neo_core_nonaggr(cs, &nat, &vars,
			&default_min, &r1, &r2, self.inner.get_job_id())
	}
}

#[cfg(test)]
pub(crate) mod tests_neo_m4 {
	use super::*;
	use ark_bn254::Fr;
	use utils::consts::read_global_config;

	fn f(x: u32) -> Fr { Fr::from(x) }

	pub(crate) fn fixture_capacity() -> DischargeAdvCapacity {
		// non-aggressive: n = subsigs*avg = 16 (>= 13 real rows).
		DischargeAdvCapacity {
			max_nibble_len: 1, subsigs: 1,
			avg_active_pats_per_subsig: 16, basis_pats_in_trace: 1,
			perc_pats_expansion_rate: 100, universe_subsigs: 1,
			b_aggressive: false, prod_pats_expansion: 0,
			wrap_keys: 0,
		}
	}

	// build one neo item; prev_* default 0 (set where the golden certs
	// them); min_next/queue_len filled by build_a1_a8_neo post-pass.
	// rows = [(loc, cat)] sorted by loc.
	fn mk(step: u32, pat: u32, rg1: u32, rg2: Fr, fz: u32,
		rows: &[(u32, u32)]) -> StepQueueItemNeo<Fr> {
		let locs = rows.iter().map(|r| f(r.0)).collect::<Vec<Fr>>();
		let base = StepQueueItem::new(f(1), f(step), f(pat), f(rg1), rg2,
			locs.clone());
		let n = rows.len();
		StepQueueItemNeo {
			cat: rows.iter().map(|r| f(r.1)).collect(),
			prev_id1: vec![f(0); n], prev_loc1: vec![f(0); n],
			prev_loc2: vec![f(0); n],
			min_next: f(0), fz: f(fz), queue_len: f(0), base,
		}
	}

	/// chunk-2 default_min (locs 81..=160): last loc + 1, per legacy
	/// gen_backward_prf empty-successor fallback.
	pub(crate) const A18_DEFAULT_MIN: u32 = 161;

	// a1..a8 worked example from figs/prune_example.tikz: chunk-2 merged
	// Q_m (carried Q_i + PatLoc), DETERMINISTIC golden partition {C,FP,BP}
	// (shared core; SP re-tagging is M7).
	pub(crate) fn build_a1_a8_neo() -> StepQueueNeo<Fr> {
		let inf = f((1u32 << read_global_config().range2_bit) - 1);
		//step-0 seed (undroppable anchor): step=pat=rg=0, loc=1.
		let mut seed = StepQueueItemNeo::from_base(
			StepQueueItem::new(f(1), f(0), f(0), f(0), f(0),
				vec![f(1)]));
		seed.cat[0] = f(CAT_C);
		let mut items = vec![seed,
			mk(1, 1, 1, f(9), 0, &[(6, CAT_C)]),
			mk(2, 2, 0, inf,  5, &[(21, CAT_C), (111, CAT_C)]),
			mk(3, 3, 1, f(9), 5, &[(27, CAT_C)]),
			mk(4, 4, 1, f(9), 5, &[(33, CAT_C)]),
			mk(5, 5, 1, f(9), 0, &[(39, CAT_C), (106, CAT_FP)]),
			mk(6, 6, 1, inf,  8, &[(73, CAT_BP), (79, CAT_BP),
				(96, CAT_BP), (141, CAT_BP)]),
			mk(7, 7, 1, f(9), 8, &[(101, CAT_BP), (131, CAT_FP)]),
		];
		//closure witnesses (Q_r-local prev id + loc) on ALL non-FP
		//rows, incl BP (they sit in Q_r):
		items[1].prev_loc1 = vec![f(1)];          //6 <- seed 1
		items[2].prev_loc1 = vec![f(6), f(6)];    //21,111 <- 6
		items[3].prev_loc1 = vec![f(21)];         //27 <- 21
		items[4].prev_loc1 = vec![f(27)];         //33 <- 27
		//39 <- 33; FP 106 below-only bracket (33+9=42<106; no
		//upper row: loc2=0 sentinel, b_below in cert layer).
		items[5].prev_loc1 = vec![f(33), f(33)];
		items[6].prev_loc1 = vec![f(39); 4];      //BP rows <- 39
		//101 <- 96 (id 2); FP 131 between 96 (id 2) / 141 (id 3).
		items[7].prev_id1  = vec![f(2), f(2)];
		items[7].prev_loc1 = vec![f(96), f(96)];
		items[7].prev_loc2 = vec![f(0), f(141)];
		let mut store_items = HashMap::new();
		store_items.insert(f(1), items);
		let mut neo = StepQueueNeo {
			b_igc: false, subsigs: vec![f(1)], store_items,
			capacity: fixture_capacity(), q_type: StepQueueType::ResLarge,
		};
		// scalars via the existing relations; empty next-C falls back
		// to default_min (legacy map_or semantics).
		let (minr, lenr) = (neo.derive_min(), neo.derive_len());
		let dmin = f(A18_DEFAULT_MIN);
		for its in neo.store_items.values_mut() {
			for it in its.iter_mut() {
				it.min_next = minr.get(it.base.subsig,
					it.base.step + f(1)).unwrap_or(dmin);
				it.queue_len = lenr.get(it.base.subsig)
					.unwrap_or(f(0));
			}
		}
		neo
	}

	#[test]
	fn test_neo_carry_projection_roundtrip() {
		let neo = build_a1_a8_neo();
		let sq = neo.to_stepqueue();
		assert_eq!(
			StepQueueNeo::from_stepqueue(sq.clone()).to_stepqueue(), sq);
		assert_eq!(
			StepQueueNeo::<Fr>::carry_vec_size(&neo.q_type, &neo.capacity),
			StepQueue::<Fr>::vec_size(&neo.q_type, &neo.capacity));
	}

	#[test]
	fn test_neo_full_roundtrip_and_size() {
		let neo = build_a1_a8_neo();
		let v = neo.to_full_vec(&neo.capacity).unwrap();
		assert_eq!(v.len(),
			StepQueueNeo::<Fr>::full_vec_size(&neo.capacity));
		//sizing reconcile: Q_m/Q_r anchored ResLarge, Q_c ResSmall.
		let (nl, _, _) = StepQueue::<Fr>::vec_size(
			&StepQueueType::ResLarge, &neo.capacity);
		let (ns, _, _) = StepQueue::<Fr>::vec_size(
			&StepQueueType::ResSmall, &neo.capacity);
		assert_eq!(v.len(), N_NEO_COLS * nl);
		assert_eq!(
			StepQueueNeo::<Fr>::qc_vec_size(&neo.capacity), 2 * ns);
		let neo2 = StepQueueNeo::parse_full(&v,
			&neo.capacity, neo.b_igc);
		assert_eq!(neo2, neo);
	}

	#[test]
	fn test_neo_min_len_relations() {
		let neo = build_a1_a8_neo();
		let (minr, lenr) = (neo.derive_min(), neo.derive_len());
		let sub = f(1);
		for (s, m) in [(0,1),(1,6),(2,21),(3,27),(4,33),(5,39)] {
			assert_eq!(minr.get(sub, f(s)), Some(f(m)));
		}
		//steps 6/7: F1 end-of-chunk BP cascade, no C rows survive.
		for s in [6u32, 7] {
			assert_eq!(minr.get(sub, f(s)), None);
		}
		assert_eq!(lenr.get(sub), Some(f(5)));
		let dmin = f(A18_DEFAULT_MIN);
		for items in neo.store_items.values() {
			for it in items {
				match minr.get(sub, it.base.step + f(1)) {
					Some(m) => assert_eq!(it.min_next, m),
					None    => assert_eq!(it.min_next, dmin),
				}
				assert_eq!(it.queue_len, f(5));
			}
		}
	}
}

#[cfg(test)]
pub(crate) mod tests_neo_m5 {
	use super::*;
	use super::tests_neo_m4::{build_a1_a8_neo, fixture_capacity,
		A18_DEFAULT_MIN};
	use ark_bn254::Fr;
	use utils::consts::read_global_config;
	use data_processor::type_def::{SubsigStepStore,
		SubsigStepStoreItem};
	use crate::gadgets::traits::{Col, IDX_DATA};

	fn f(x: u32) -> Fr { Fr::from(x) }

	//a1..a8 SDE step store (pats 1..8; max = range2 sentinel).
	pub(crate) fn a18_store() -> SubsigStepStore {
		let mx = (1usize << read_global_config().range2_bit) - 1;
		let pm = vec![(1,(1,9)), (2,(0,mx)), (3,(1,9)), (4,(1,9)),
			(5,(1,9)), (6,(1,mx)), (7,(1,9)), (8,(1,9))];
		let item = SubsigStepStoreItem { subsig_id: 1, igc: false,
			vec_pm_bounds: pm, is_backward: false };
		let mut m = std::collections::HashMap::new();
		m.insert(1usize, item);
		SubsigStepStore { subsig_ids: vec![1], subsig_to_steps: m,
			b_aggressive: false }
	}

	//carried Q_i = Fig-14 chunk-1 output (steps 0..6).
	pub(crate) fn a18_carried() -> StepQueueNeo<Fr> {
		let mx = f((1u32 << read_global_config().range2_bit) - 1);
		let s = |st: u32, pat: u32, a: u32, b: Fr, locs: &[u32]| {
			StepQueueItem::new(f(1), f(st), f(pat), f(a), b,
				locs.iter().map(|x| f(*x)).collect())
		};
		let items = vec![
			s(0, 0, 0, f(0), &[1]),
			s(1, 1, 1, f(9), &[6]),
			s(2, 2, 0, mx,   &[21]),
			s(3, 3, 1, f(9), &[27]),
			s(4, 4, 1, f(9), &[33]),
			s(5, 5, 1, f(9), &[39]),
			s(6, 6, 1, mx,   &[73, 79]),
		];
		let mut m = HashMap::new();
		m.insert(f(1), items);
		StepQueueNeo::from_stepqueue(StepQueue::new(vec![f(1)], m,
			&fixture_capacity(), StepQueueType::ResLarge, false))
	}

	//chunk-2 matches (dummy wrap entries 0/max, ids ascending).
	fn a18_hm() -> HashMap<Fr, Vec<(Fr, Fr)>> {
		let mx = f((1u32 << read_global_config().range2_bit) - 1);
		let wrap = |locs: &[u32]| {
			let mut v = vec![(f(0), f(0))];
			for (i, l) in locs.iter().enumerate() {
				v.push((f((i + 1) as u32), f(*l)));
			}
			v.push((f((locs.len() + 1) as u32), mx));
			v
		};
		let mut m = HashMap::new();
		m.insert(f(2), wrap(&[111]));
		m.insert(f(5), wrap(&[106]));
		m.insert(f(6), wrap(&[96, 141]));
		m.insert(f(7), wrap(&[101, 131]));
		m
	}

	/// golden: generator output == hand-built Fig-14 fixture.
	#[test]
	fn test_m5_shared_core_golden() {
		let qm = a18_carried().gen_shared_core_from_hm(0,
			&a18_hm(), &a18_store(), f(A18_DEFAULT_MIN)).unwrap();
		assert_eq!(qm, build_a1_a8_neo());
	}

	/// table consistency: Q_r filter + tight C carry shapes.
	#[test]
	fn test_m5_qr_and_carry() {
		let qm = a18_carried().gen_shared_core_from_hm(0,
			&a18_hm(), &a18_store(), f(A18_DEFAULT_MIN)).unwrap();
		let n_rows = |q: &StepQueueNeo<Fr>| q.store_items.values()
			.map(|v| v.iter().map(|it| it.base.locs.len())
			.sum::<usize>()).sum::<usize>();
		assert_eq!(n_rows(&qm), 14);
		assert_eq!(n_rows(&qm.to_qr()), 12);   //minus 2 FP
		let qc = qm.carry_only();
		assert!(matches!(qc.q_type, StepQueueType::ResSmall));
		let its = qc.store_items.get(&f(1)).unwrap();
		let want: Vec<Vec<u32>> = vec![vec![1], vec![6],
			vec![21, 111], vec![27], vec![33], vec![39],
			vec![], vec![]];
		assert_eq!(its.len(), want.len());
		for (i, w) in want.iter().enumerate() {
			let got: Vec<Fr> = its[i].locs.clone();
			let exp: Vec<Fr> =
				w.iter().map(|x| f(*x)).collect();
			assert_eq!(got, exp, "step {}", i);
		}
	}

	/// CapErr on deliberate under-capacity (no silent truncation).
	#[test]
	fn test_m5_full_vec_caperr() {
		let qm = a18_carried().gen_shared_core_from_hm(0,
			&a18_hm(), &a18_store(), f(A18_DEFAULT_MIN)).unwrap();
		let mut small = qm.capacity.clone();
		small.avg_active_pats_per_subsig = 4; //n=4 < 14 rows
		assert!(qm.to_full_vec(&small).is_err());
	}

	// ---------------- equivalence oracle (#3) ----------------

	//lcg = Linear Congruential Generator: minimal deterministic
	//PRNG, state x -> a*x + c (mod 2^64) with Knuth MMIX constants,
	//output = top bits (best-mixed). No rand-crate dependency; the
	//same seed always yields the same sequence, so any failing
	//random case is reproducible from its seed alone.
	fn lcg(s: &mut u64) -> u64 {
		*s = s.wrapping_mul(6364136223846793005)
			.wrapping_add(1442695040888963407);
		*s >> 33
	}

	//larger cap so random cases never hit CapErr (n=64 both types).
	fn oracle_capacity() -> DischargeAdvCapacity {
		let mut c = fixture_capacity();
		c.avg_active_pats_per_subsig = 64;
		c
	}

	fn seed_only_queue() -> StepQueue<Fr> {
		let items = vec![StepQueueItem::new(f(1), f(0), f(0),
			f(0), f(0), vec![f(1)])];
		let mut m = HashMap::new();
		m.insert(f(1), items);
		StepQueue::new(vec![f(1)], m, &oracle_capacity(),
			StepQueueType::ResSmall, false)
	}

	//pat_loc container from pat->locs (dummy wraps 0/max, ids asc),
	//mirroring the legacy test_fwd_prf construction.
	pub(crate) fn mk_pat_loc(m: &HashMap<u32, Vec<u32>>)
	-> Arc<Mutex<Container<Fr>>> {
		let mx = (1u32 << read_global_config().range2_bit) - 1;
		let ct = Container::new("pat_loc");
		let (mut ks, mut ids, mut ls) = (vec![], vec![], vec![]);
		let mut pats: Vec<u32> = m.keys().cloned().collect();
		pats.sort();
		for p in pats {
			let locs = &m[&p];
			ks.push(f(p)); ids.push(f(0)); ls.push(f(0));
			for (i, l) in locs.iter().enumerate() {
				ks.push(f(p));
				ids.push(f((i + 1) as u32));
				ls.push(f(*l));
			}
			ks.push(f(p));
			ids.push(f((locs.len() + 1) as u32));
			ls.push(f(mx));
		}
		ct.lock().unwrap().add_col(Col::new(ks, "sorted_key",
			IDX_DATA));
		ct.lock().unwrap().add_col(Col::new(ids, "sorted_id",
			IDX_DATA));
		ct.lock().unwrap().add_col(Col::new(ls, "sorted_val",
			IDX_DATA));
		ct
	}

	//oracle: legacy fwd+bwd carry == neo shared-core carry, byte
	//level (to_vec = the fold contract). Returns legacy result for
	//chunk chaining.
	fn assert_oracle(carried: &StepQueue<Fr>,
		pl: &HashMap<u32, Vec<u32>>, info: &SubsigStepStore,
		dmin: u32, tag: &str) -> StepQueue<Fr> {
		let ct = mk_pat_loc(pl);
		let (_ta, fwd, _fp) = carried.gen_forward_prf(&ct, info);
		let (_td, legacy, _bp) =
			fwd.gen_backward_prf(f(dmin), info);
		let neo = StepQueueNeo::from_stepqueue(carried.clone())
			.gen_shared_core_advice(0, &ct, info, f(dmin))
			.unwrap().carry_only();
		assert_eq!(legacy.to_vec(info).unwrap(),
			neo.to_vec(info).unwrap(), "oracle bytes: {}", tag);
		legacy
	}

	/// equiv oracle (#3): 20 seeded random two-chunk runs over the
	/// a1..a8 SDE; chunk-1 result feeds chunk 2 on both sides.
	#[test]
	fn test_m5_oracle_random() {
		let info = a18_store();
		let rand_pl = |s: &mut u64, lo: u32| {
			let mut pl: HashMap<u32, Vec<u32>> = HashMap::new();
			for p in 1u32..=8 {
				let cnt = (lcg(s) % 4) as usize;
				let mut v: Vec<u32> = (0..cnt).map(|_|
					lo + (lcg(s) % 80) as u32).collect();
				v.sort(); v.dedup();
				if !v.is_empty() { pl.insert(p, v); }
			}
			pl
		};
		for seed0 in 0u64..20 {
			let mut s = seed0
				.wrapping_mul(0x9E3779B97F4A7C15)
				.wrapping_add(1);
			//chunk 1: locs 1..=80, carried = seed-only
			let pl1 = rand_pl(&mut s, 1);
			let mid = assert_oracle(&seed_only_queue(), &pl1,
				&info, 81, &format!("seed {} chunk1", seed0));
			//chunk 2: locs 81..=160, carried = chunk-1 result
			let pl2 = rand_pl(&mut s, 81);
			assert_oracle(&mid, &pl2, &info, 161,
				&format!("seed {} chunk2", seed0));
		}
	}

	//backward 3-step store: keyword-last sig, stored chain gets
	//REVERSED (keyword-first) by reverse_pm_bounds; aggressive-only
	//shape => the oracle runs seed-only single chunks (backward
	//subsigs never carry across chunks).
	fn bwd_store() -> SubsigStepStore {
		let pm = vec![(1, (1, 9)), (2, (1, 9)), (3, (0, 20))];
		let item = SubsigStepStoreItem { subsig_id: 1, igc: false,
			vec_pm_bounds: pm, is_backward: true };
		let mut m = std::collections::HashMap::new();
		m.insert(1usize, item);
		SubsigStepStore { subsig_ids: vec![1], subsig_to_steps: m,
			b_aggressive: true }
	}

	/// M6 amendment to the M5 oracle: BACKWARD-subsig cases. The
	/// reversed keyword-first chain (step-1 forward anchor, i>=2
	/// mirrored [u-b, u-a] windows) must match legacy
	/// gen_forward_prf+gen_backward_prf byte for byte on 20 seeded
	/// random single chunks. Locs floor at 31 = max backward span
	/// (9+20) + 1: the legacy CU1 "M+1 offset" precondition -- a
	/// backward window below it underflows and asserts in legacy.
	#[test]
	fn test_m5_oracle_backward() {
		let info = bwd_store();
		let rand_pl = |s: &mut u64| {
			let mut pl: HashMap<u32, Vec<u32>> = HashMap::new();
			for p in 1u32..=3 {
				let cnt = (lcg(s) % 4) as usize;
				let mut v: Vec<u32> = (0..cnt).map(|_|
					31 + (lcg(s) % 80) as u32).collect();
				v.sort(); v.dedup();
				if !v.is_empty() { pl.insert(p, v); }
			}
			pl
		};
		for seed0 in 100u64..120 {
			let mut s = seed0
				.wrapping_mul(0x9E3779B97F4A7C15)
				.wrapping_add(1);
			let pl = rand_pl(&mut s);
			assert_oracle(&seed_only_queue(), &pl, &info, 161,
				&format!("bwd seed {}", seed0));
		}
	}

	// ---------------- corner cases (#5) ----------------

	//partition snapshot: sorted (step, loc) rows carrying `cat`.
	fn snap(q: &StepQueueNeo<Fr>, cat: u32) -> Vec<(usize, usize)> {
		let fc = f(cat);
		let mut v = vec![];
		for its in q.store_items.values() {
			for it in its {
				for j in 0..it.base.locs.len() {
					if it.cat[j] == fc {
						v.push((field_to_usize(&it.base.step),
							field_to_usize(&it.base.locs[j])));
					}
				}
			}
		}
		v.sort();
		v
	}

	//oracle compare + return neo Q_m for partition asserts.
	fn run_case(carried: &StepQueue<Fr>, pl: &HashMap<u32, Vec<u32>>,
		dmin: u32, tag: &str) -> StepQueueNeo<Fr> {
		let info = a18_store();
		assert_oracle(carried, pl, &info, dmin, tag);
		let ct = mk_pat_loc(pl);
		StepQueueNeo::from_stepqueue(carried.clone())
			.gen_shared_core_advice(0, &ct, &info, f(dmin))
			.unwrap()
	}

	/// (a) EMPTY CHUNK: the scanned chunk contains no matches, so
	/// Q_m is exactly the carried queue. Tests that merge/closure
	/// tolerate an absent match table (no index-0 assumptions) and
	/// that the end-of-chunk backward prune still runs against
	/// default_min=161: carried a6 frontier {73,79} dies (82,88 <
	/// 161) while a5:39 survives via its unbounded {1,inf} window.
	#[test]
	fn test_m5_corner_empty_patloc() {
		let qm = run_case(&a18_carried().to_stepqueue(),
			&HashMap::new(), 161, "empty patloc");
		assert_eq!(snap(&qm, CAT_C),
			vec![(0,1),(1,6),(2,21),(3,27),(4,33),(5,39)]);
		assert_eq!(snap(&qm, CAT_BP), vec![(6,73),(6,79)]);
		assert!(snap(&qm, CAT_FP).is_empty());
	}

	/// (b) MID-CHAIN EMPTIED STEPS: matches chain 6->20->27->33
	/// (steps 1-4), nothing later. The walk empties step 4 (33+9 <
	/// 161), so step 3 must prune against the default_min FALLBACK
	/// (empty successor => min=161), which empties step 3, then
	/// step 2 -- three consecutive map_or(default_min) layers --
	/// until a2's {0,inf} window saves loc 6. Catches empty-min
	/// panics and wrong fallbacks that over/under-prune.
	#[test]
	fn test_m5_corner_midchain_default_min() {
		let mut pl = HashMap::new();
		pl.insert(1, vec![6]); pl.insert(2, vec![20]);
		pl.insert(3, vec![27]); pl.insert(4, vec![33]);
		let qm = run_case(&seed_only_queue(), &pl, 161,
			"midchain default_min");
		assert_eq!(snap(&qm, CAT_C), vec![(0,1),(1,6)]);
		assert_eq!(snap(&qm, CAT_BP),
			vec![(2,20),(3,27),(4,33)]);
		assert!(snap(&qm, CAT_FP).is_empty());
	}

	/// (c) ALL-FP CHUNK: every new match is unreachable (90 outside
	/// a3's window [22,30] from 21; 95 outside a7's [74,82]/[80,88]
	/// from 73/79). Tests that closure seeds ONLY from carried rows
	/// (a bug seeding from PatLoc would make these reachable) and
	/// that FP brackets hold against the carried-only Q_r; carried
	/// rows' C/BP split must equal the empty-chunk case exactly.
	#[test]
	fn test_m5_corner_all_fp() {
		let mut pl = HashMap::new();
		pl.insert(3, vec![90]); pl.insert(7, vec![95]);
		let qm = run_case(&a18_carried().to_stepqueue(), &pl, 161,
			"all fp");
		assert_eq!(snap(&qm, CAT_FP), vec![(3,90),(7,95)]);
		assert_eq!(snap(&qm, CAT_C),
			vec![(0,1),(1,6),(2,21),(3,27),(4,33),(5,39)]);
		assert_eq!(snap(&qm, CAT_BP), vec![(6,73),(6,79)]);
	}

	/// (d) SEED-ONLY: very first chunk, zero matches: Q_m is just
	/// the step-0 seed (loc 1, cat C). Tests the degenerate BP walk
	/// (start=1, loop never runs) and that the undroppable anchor
	/// survives into the carry -- losing it would silently void the
	/// anti-drop soundness argument for every later chunk.
	#[test]
	fn test_m5_corner_seed_only() {
		let qm = run_case(&seed_only_queue(), &HashMap::new(), 81,
			"seed only");
		assert_eq!(snap(&qm, CAT_C), vec![(0,1)]);
		assert!(snap(&qm, CAT_BP).is_empty()
			&& snap(&qm, CAT_FP).is_empty());
		let qc = qm.carry_only();
		let its = qc.store_items.get(&f(1)).unwrap();
		assert!(its.len() == 1 && its[0].locs == vec![f(1)]);
	}

	/// (e) FROZEN-STEP FP + BELOW-FIRST BRACKET: a2:3 lands on a
	/// frozen step (fz=5) and is unreachable BELOW the whole window
	/// [6,max-1] of prev row 6. Tests FP-priority (tagged FP, fz
	/// attr still 5 -- frozen logic never steals the row) and the
	/// below-first sentinel encoding prev_loc1=0 / prev_loc2=first
	/// Q_r row: the exact case needing M6's b_below advice bit.
	#[test]
	fn test_m5_corner_frozen_fp_priority() {
		let mut pl = HashMap::new();
		pl.insert(2, vec![3]);
		let qm = run_case(&a18_carried().to_stepqueue(), &pl, 161,
			"frozen fp");
		assert_eq!(snap(&qm, CAT_FP), vec![(2,3)]);
		let its = qm.store_items.get(&f(1)).unwrap();
		let it2 = &its[2]; //step 2, locs sorted [3, 21]
		assert!(it2.cat[0] == f(CAT_FP)
			&& it2.prev_loc1[0] == f(0)
			&& it2.prev_loc2[0] == f(6)
			&& it2.fz == f(5));
	}

	/// (f) DUPLICATE LOC: carried a6:79 arrives AGAIN as a chunk-2
	/// match (chunk-straddle artifact). Merge must dedup it into
	/// one row with one cat, making the input equivalent to Fig-14
	/// chunk 2 -- asserted by FULL struct equality with the golden
	/// fixture. Catches double-counting that would inflate Q_m or
	/// split a cert across duplicate rows.
	#[test]
	fn test_m5_corner_duplicate_loc() {
		let mut pl = HashMap::new();
		pl.insert(2, vec![111]); pl.insert(5, vec![106]);
		pl.insert(6, vec![79, 96, 141]); //79 = dup of carried
		pl.insert(7, vec![101, 131]);
		let qm = run_case(&a18_carried().to_stepqueue(), &pl, 161,
			"duplicate loc");
		assert_eq!(qm, build_a1_a8_neo());
	}
}

// ============================================================
//   M6 tests: tier-1 direct-cs aggressive core
// ============================================================
#[cfg(test)]
pub(crate) mod tests_neo_m6 {
	use super::*;
	use super::tests_neo_m4::fixture_capacity;
	use ark_bn254::Fr;
	use ark_relations::r1cs::{ConstraintSystem,
		ConstraintSystemRef};
	use crate::gadgets::commons::new_var;
	use data_processor::type_def::{SubsigStepStore,
		SubsigStepStoreItem};

	fn f(x: u32) -> Fr { Fr::from(x) }

	/// flat L columns (pat, loc) with per-pat 0/max wraps, pats
	/// ascending -- the two columns the M6 merge consumes.
	pub(crate) fn hm_to_l_cols(m: &HashMap<u32, Vec<u32>>) -> (Vec<Fr>, Vec<Fr>) {
		let mx = (1u32 << read_global_config().range2_bit) - 1;
		let (mut ps, mut ls) = (vec![], vec![]);
		let mut pats: Vec<u32> = m.keys().cloned().collect();
		pats.sort();
		for p in pats {
			ps.push(f(p)); ls.push(f(0));
			for l in &m[&p] { ps.push(f(p)); ls.push(f(*l)); }
			ps.push(f(p)); ls.push(f(mx));
		}
		(ps, ls)
	}

	/// hm in the generator's (id, loc) wrapped format.
	pub(crate) fn hm_gen(m: &HashMap<u32, Vec<u32>>)
	-> HashMap<Fr, Vec<(Fr, Fr)>> {
		let mx = f((1u32 << read_global_config().range2_bit) - 1);
		let mut out = HashMap::new();
		for (p, locs) in m {
			let mut v = vec![(f(0), f(0))];
			for (i, l) in locs.iter().enumerate() {
				v.push((f((i + 1) as u32), f(*l)));
			}
			v.push((f((locs.len() + 1) as u32), mx));
			out.insert(f(*p), v);
		}
		out
	}

	/// assemble the full native bundle from a generator output
	/// (thin wrapper over NeoCore::gen on hm-derived L cols).
	pub(crate) fn build_core_native(gen: &StepQueueNeo<Fr>,
		info: &SubsigStepStore, hm: &HashMap<u32, Vec<u32>>)
	-> NeoCore<Fr> {
		let (l_pat, l_loc) = hm_to_l_cols(hm);
		NeoCore::gen(gen, info, l_pat, l_loc)
			.expect("core native")
	}

	/// allocate every native column as witness vars.
	pub(crate) fn alloc_vars(cs: &ConstraintSystemRef<Fr>,
		nat: &NeoCore<Fr>) -> NeoCoreVars<Fr> {
		let av = |v: &Vec<Fr>| v.iter().map(|x| new_var(cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		let t = &nat.t;
		let qm = QmVars {
			enc: av(&t.enc), id: av(&t.id), loc: av(&t.loc),
			cat: av(&t.cat), step: av(&t.step),
			subsig: av(&t.subsig), prev_id1: av(&t.prev_id1),
			prev_loc1: av(&t.prev_loc1),
			prev_loc2: av(&t.prev_loc2), pat: av(&t.pat),
			rg1: av(&t.rg1), rg2: av(&t.rg2),
			enc_prev: av(&t.enc_prev), b_bwd: av(&t.b_bwd),
			d_c1: av(&t.d_c1), d_c2: av(&t.d_c2),
			d_below_lo: av(&t.d_below_lo),
			d_below_hi: av(&t.d_below_hi),
			d_above_lo: av(&t.d_above_lo),
			d_above_hi: av(&t.d_above_hi), d_sort: av(&t.d_sort),
			si_step: av(&t.si_step), si_subsig: av(&t.si_subsig),
			si_pat: av(&t.si_pat), si_rg1: av(&t.si_rg1),
			si_rg2: av(&t.si_rg2),
			si_enc_prev: av(&t.si_enc_prev),
			si_b_bwd: av(&t.si_b_bwd),
			nonaggr: alloc_nonaggr_vars(cs, &t.nonaggr),
		};
		NeoCoreVars { qm, l_pat: av(&nat.l_pat),
			l_loc: av(&nat.l_loc), subsigs: av(&nat.subsig_nat),
			s_enc: av(&nat.s_enc), s_pat: av(&nat.s_pat),
			d_pat: av(&nat.d_pat), d_cnt: av(&nat.d_cnt),
			d_diff: av(&nat.d_diff), m_aux: av(&nat.m_aux),
			mtbl_qr: av(&nat.mtbl_qr), mtbl_d: av(&nat.mtbl_d),
			acc_out: av(&nat.acc_out),
			mtbl_acc: av(&nat.mtbl_acc),
			qi_enc: av(&nat.qi_enc), qi_loc: av(&nat.qi_loc),
			qc_enc: av(&nat.qc_enc), qc_loc: av(&nat.qc_loc),
			mtbl_qc: av(&nat.mtbl_qc) }
	}

	/// allocate the non-aggressive witness mirror (empty in aggr).
	pub(crate) fn alloc_nonaggr_vars(cs: &ConstraintSystemRef<Fr>,
		na: &QmNonAggrCols<Fr>) -> QmNonAggrVars<Fr> {
		let av = |v: &Vec<Fr>| v.iter().map(|x| new_var(cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		QmNonAggrVars {
			b_l: av(&na.b_l), enc_next: av(&na.enc_next),
			bp_prev_val: av(&na.bp_prev_val),
			rg2_next: av(&na.rg2_next), w_next: av(&na.w_next),
			d_bp: av(&na.d_bp), fz: av(&na.fz),
			enc_fz: av(&na.enc_fz),
			fz_step_val: av(&na.fz_step_val),
			fz_sub_val: av(&na.fz_sub_val), w_fz: av(&na.w_fz),
			d_fz: av(&na.d_fz), w_sp: av(&na.w_sp),
			d_sp: av(&na.d_sp), m_carry_in: av(&na.m_carry_in),
			si_bp_prev: av(&na.si_bp_prev),
			si_rg2_next: av(&na.si_rg2_next), si_fz: av(&na.si_fz),
			si_fz_step: av(&na.si_fz_step),
			si_fz_sub: av(&na.si_fz_sub) }
	}

	/// run the aggressive core over a (store, hm) input with a
	/// seed-only carry; `tamper` edits the natives pre-allocation
	/// (negative-test hook). Returns (cs, natives).
	pub(crate) fn run_core_aggr(info: &SubsigStepStore,
		hm: &HashMap<u32, Vec<u32>>, default_min: u32,
		tamper: Option<&dyn Fn(&mut NeoCore<Fr>)>)
	-> (ConstraintSystemRef<Fr>, NeoCore<Fr>) {
		let seed = StepQueueItem::new(f(1), f(0), f(0), f(0), f(0),
			vec![f(1)]);
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed]);
		let carried = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m, &fixture_capacity(),
			StepQueueType::ResLarge, false));
		let gen = carried.gen_shared_core_from_hm(0, &hm_gen(hm),
			info, f(default_min)).expect("shared core");
		let mut nat = build_core_native(&gen, info, hm);
		if let Some(tf) = tamper { tf(&mut nat); }
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = alloc_vars(&cs, &nat);
		let r1 = new_var(&cs, Fr::from(12345u32));
		let r2 = new_var(&cs, Fr::from(67890u32));
		DischargeAdvNeoGadget::<Fr>::assert_neo_core_aggr(
			cs.clone(), &nat, &vars, &r1, &r2, 0)
			.expect("assert core");
		(cs, nat)
	}

	fn fig14_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(1, vec![6]);
		m.insert(2, vec![21, 111]);
		m.insert(3, vec![27]);
		m.insert(4, vec![33]);
		m.insert(5, vec![39, 106]);
		m.insert(6, vec![73, 79, 96, 141]);
		m.insert(7, vec![101, 131]);
		m
	}

	/// P1 flagship: whole Fig-14 string as ONE chunk, seed-only.
	/// SAT + partition golden (FP = {5:106, 7:131}, rest C after the
	/// BP->C retag) + acc empty (a8 never matches).
	#[test]
	fn test_m6_fig14_single_chunk() {
		let info = super::tests_neo_m5::a18_store();
		let (cs, nat) = run_core_aggr(&info, &fig14_hm(), 161,
			None);
		assert!(cs.is_satisfied().unwrap());
		let t = &nat.t;
		let mut fp = vec![];
		for i in t.n_pad..t.enc.len() {
			if t.cat[i] == f(CAT_FP) {
				fp.push((field_to_usize(&t.step[i]),
					field_to_usize(&t.loc[i])));
			}
		}
		fp.sort();
		assert_eq!(fp, vec![(5, 106), (7, 131)]);
		assert_eq!(nat.acc_out, vec![f(0)]); // no terminal C
	}

	/// (step, loc) of the real rows tagged `cat`, sorted (pads and
	/// wraps carry cat 0 and never appear for C/FP).
	pub(crate) fn cat_rows(nat: &NeoCore<Fr>, cat: u32)
	-> Vec<(usize, usize)> {
		let t = &nat.t;
		let mut v = vec![];
		for i in t.n_pad..t.enc.len() {
			if t.cat[i] == f(cat) {
				v.push((field_to_usize(&t.step[i]),
					field_to_usize(&t.loc[i])));
			}
		}
		v.sort();
		v
	}

	/// P2a MIDCHAIN: chain a1..a4 then nothing. The M5 walk prunes
	/// steps 2-4 against three consecutive default_min fallback
	/// layers; emission retags them C, so the whole prefix must
	/// re-certify as C, with no FP and an all-zero acc.
	#[test]
	fn test_m6_corner_midchain() {
		let info = super::tests_neo_m5::a18_store();
		let mut hm = HashMap::new();
		hm.insert(1, vec![6]); hm.insert(2, vec![20]);
		hm.insert(3, vec![27]); hm.insert(4, vec![33]);
		let (cs, nat) = run_core_aggr(&info, &hm, 161, None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(cat_rows(&nat, CAT_C),
			vec![(0, 1), (1, 6), (2, 20), (3, 27), (4, 33)]);
		assert!(cat_rows(&nat, CAT_FP).is_empty());
		assert!(nat.acc_out.iter().all(|x| x.is_zero()));
	}

	/// P2b SEED-ONLY / EMPTY-L: zero matches. T_qm = seed row plus
	/// wrap-only groups; L, m_aux and mtbl_d are empty columns and
	/// every merge/cert query is masked. Exercises the empty-lookup
	/// edges of all five blocks end to end.
	#[test]
	fn test_m6_corner_seed_only_empty_l() {
		let info = super::tests_neo_m5::a18_store();
		let (cs, nat) = run_core_aggr(&info, &HashMap::new(), 81,
			None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(cat_rows(&nat, CAT_C), vec![(0, 1)]);
		assert!(cat_rows(&nat, CAT_FP).is_empty());
		assert!(nat.acc_out.iter().all(|x| x.is_zero()));
	}

	/// P2c ALL-FP: both matches unreachable from the bare seed (a3
	/// needs a live a2 row, a7 a live a6 row). FP brackets resolve
	/// against wrap-only predecessor groups: both masks off via the
	/// (0, max) sentinel pair -- the vacuous-bracket edge.
	#[test]
	fn test_m6_corner_all_fp() {
		let info = super::tests_neo_m5::a18_store();
		let mut hm = HashMap::new();
		hm.insert(3, vec![90]); hm.insert(7, vec![95]);
		let (cs, nat) = run_core_aggr(&info, &hm, 161, None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(cat_rows(&nat, CAT_FP), vec![(3, 90), (7, 95)]);
		assert_eq!(cat_rows(&nat, CAT_C), vec![(0, 1)]);
	}

	/// P2d CNT=0 PAT (8_A): an L pat (9) no seeded store step uses
	/// is off-universe -> gen rejects with a neo_dict_offstore
	/// CapErr (shape-drift guard), not a silent cnt=0 dict row.
	#[test]
	fn test_m6_corner_cnt0_pat() {
		let info = super::tests_neo_m5::a18_store();
		let mut hm = fig14_hm();
		hm.insert(9, vec![50]);
		let seed = StepQueueItem::new(f(1), f(0), f(0), f(0),
			f(0), vec![f(1)]);
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed]);
		let carried = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m, &fixture_capacity(),
			StepQueueType::ResLarge, false));
		let gen = carried.gen_shared_core_from_hm(0, &hm_gen(&hm),
			&info, f(161)).expect("shared core");
		let (l_pat, l_loc) = hm_to_l_cols(&hm);
		let res = NeoCore::gen(&gen, &info, l_pat, l_loc);
		let msg = format!("{:?}", res.err()
			.expect("off-store L pat must be rejected"));
		assert!(msg.contains("neo_dict_offstore"), "got {}", msg);
	}

	/// P2e DUPLICATE LOC ACROSS PATS: a3 also matches at loc 33 =
	/// a4's C loc. The rows live in different (subsig, step) groups,
	/// so per-group strict sorting is untouched; a3:33 is FP (no a2
	/// row inside its window [24, 32] -- bracket = (21, 111)).
	#[test]
	fn test_m6_corner_duplicate_loc() {
		let info = super::tests_neo_m5::a18_store();
		let mut hm = fig14_hm();
		hm.insert(3, vec![27, 33]);
		let (cs, nat) = run_core_aggr(&info, &hm, 161, None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(cat_rows(&nat, CAT_FP),
			vec![(3, 33), (5, 106), (7, 131)]);
	}

	/// T3 golden: gen_core_stmt over the hand-built Fig-14 pat_loc.
	/// Asserts (a) the neo_core container mirrors the native bundle
	/// column for column; (b) the si policy (variable DB tags on
	/// real non-step0 rows, RANGE2 on masked/pad rows, subsig-0
	/// dummy step tag on pads); (c) failed_acc has FailedSubsigAcc
	/// sizing with the terminal set and a COMPLETE m-table (every
	/// row queries exactly once); (d) CapErr on an undersized T_qm
	/// budget, never silent truncation.
	#[test]
	fn test_m6_stmt_golden() {
		let info = super::tests_neo_m5::a18_store();
		let ct = super::tests_neo_m5::mk_pat_loc(&fig14_hm());
		let seed = StepQueueItem::new(f(1), f(0), f(0), f(0), f(0),
			vec![f(1)]);
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed]);
		let gen = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m, &fixture_capacity(),
			StepQueueType::ResLarge, false))
			.gen_shared_core_advice(0, &ct, &info, f(161))
			.expect("core");
		let (core, combo, nat) = gen.gen_core_stmt(&ct, &info)
			.expect("stmt");
		// (a) container == native, spot the load-bearing cols
		let get = |n: &str| core.lock().unwrap().get_container(n)
			.unwrap().lock().unwrap().to_vec();
		assert_eq!(get("enc"), nat.t.enc);
		assert_eq!(get("loc"), nat.t.loc);
		assert_eq!(get("cat"), nat.t.cat);
		assert_eq!(get("prev_id1"), nat.t.prev_id1);
		assert_eq!(get("d_sort"), nat.t.d_sort);
		assert_eq!(get("si_step"), nat.t.si_step);
		assert_eq!(get("si_b_bwd"), nat.t.si_b_bwd);
		assert_eq!(get("l_pat"), nat.l_pat);
		assert_eq!(get("l_loc"), nat.l_loc);
		assert_eq!(get("d_pat"), nat.d_pat);
		assert_eq!(get("d_cnt"), nat.d_cnt);
		assert_eq!(get("m_aux"), nat.m_aux);
		assert_eq!(get("mtbl_qr"), nat.mtbl_qr);
		assert_eq!(get("mtbl_d"), nat.mtbl_d);
		// (b) si policy: real non-step0 row = DB tags; pads masked
		let t = &nat.t;
		assert!(t.n_pad >= 1);
		let i3 = (t.n_pad..t.enc.len()).find(|&i|
			t.loc[i] == f(27)).unwrap();
		assert_eq!(t.si_subsig[i3],
			SubsigStepStore::gen_step_tbl_id(t.enc[i3],
				ID_ENCODED_SUBSIG));
		assert_eq!(t.si_step[i3],
			SubsigStepStore::gen_step_tbl_id(t.enc[i3],
				ID_ENCODED_NORMAL_STEP));
		assert_eq!(t.si_subsig[0], f(RANGE2));
		assert_eq!(t.si_step[0],
			SubsigStepStore::gen_step_tbl_id(f(0),
				ID_ENCODED_LAST_STEP));
		// (c) failed_acc: legacy sizing, no terminal C in fig14
		let acc = combo.lock().unwrap()
			.get_container("failed_acc").unwrap()
			.lock().unwrap().get_container("acc_encoded").unwrap()
			.lock().unwrap().to_vec();
		assert_eq!(acc, nat.acc_out);
		assert!(acc.iter().all(|x| x.is_zero()));
		let mtbl = combo.lock().unwrap()
			.get_container("failed_acc_prf").unwrap()
			.lock().unwrap().get_container("mtbl_complete")
			.unwrap().lock().unwrap().to_vec();
		assert_eq!(mtbl, nat.mtbl_acc);
		let tot: usize = mtbl.iter()
			.map(|x| field_to_usize(x)).sum();
		assert_eq!(tot, nat.t.enc.len());
		// (d) CapErr on an undersized row budget
		let mut small = gen.clone();
		small.capacity.avg_active_pats_per_subsig = 8;
		assert!(small.gen_qm_table(&info, true).is_err());
	}

	/// commit-time cost guard: the Fig-14 single-chunk core must
	/// stay inside a +/-25% band of the calibrated 3429 cs over 34
	/// rows -- catches accidental constraint blowup later.
	#[test]
	fn test_m6_cost_band() {
		let info = super::tests_neo_m5::a18_store();
		let (cs, nat) = run_core_aggr(&info, &fig14_hm(), 161,
			None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(nat.t.enc.len(), 34);
		let n = cs.num_constraints();
		assert!(n >= 2572 && n <= 4286,
			"cost drift: {} cs vs calibrated 3429", n);
	}
}

#[cfg(test)]
mod tests_neo_m6_neg {
	use super::*;
	use super::tests_neo_m6::{run_core_aggr, build_core_native};
	use super::tests_neo_m5::a18_store;
	use ark_bn254::Fr;

	fn f(x: u32) -> Fr { Fr::from(x) }

	fn fig14_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(1, vec![6]); m.insert(2, vec![21, 111]);
		m.insert(3, vec![27]); m.insert(4, vec![33]);
		m.insert(5, vec![39, 106]);
		m.insert(6, vec![73, 79, 96, 141]);
		m.insert(7, vec![101, 131]);
		m
	}

	/// P3 verdict: add a8:108 (reachable from a7:101, gap 7) => full
	/// match; SAT and acc_out = [0, enc(a8 step8)] (terminal C row
	/// feeds failed_acc; compute_sig consumes it unchanged). The
	/// terminal anchor also flips the BP walk: min_8=108 keeps
	/// a7:101 (110<108 false), min_7=101 keeps a6:96/141 -- the
	/// whole chain to a8 is C, only a6:73/79 stay BP.
	#[test]
	fn test_m6_full_match_acc() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let (cs, nat) = run_core_aggr(&a18_store(), &hm, 161, None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(nat.acc_out.len(), 2);
		assert!(nat.acc_out[0].is_zero());
		assert!(!nat.acc_out[1].is_zero());
	}

	/// n9 acc omission: same full match, but the prover empties
	/// acc_out -> the completeness logup cannot balance -> UNSAT.
	#[test]
	fn test_m6_neg_acc_omission() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let n_rows = |nat: &NeoCore<Fr>| nat.t.enc.len();
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm, 161,
			Some(&|nat: &mut NeoCore<Fr>| {
				let n = n_rows(nat);
				nat.acc_out = vec![Fr::from(0u32)];
				nat.mtbl_acc = vec![Fr::from(n as u32)];
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n1 omission of a match: generator runs WITHOUT a6:96 (so no
	/// T_qm row demands it) but L still lists it -> the counting
	/// logup demands cnt(6)=1 hits of (6,96) and gets none -> UNSAT.
	#[test]
	fn test_m6_neg_drop_match() {
		let mut hm_red = fig14_hm();
		hm_red.insert(6, vec![73, 79, 141]); // 96 omitted
		let hm_full = fig14_hm();
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm_red, 161,
			Some(&move |nat: &mut NeoCore<Fr>| {
				// restore the FULL L (with 96) + its m columns;
				// T_qm stays the omitting version.
				let (lp, ll) = super::tests_neo_m6::hm_to_l_cols(
					&hm_full);
				nat.m_aux = StepQueueNeo::gen_merge_m_aux(&lp,
					&ll, &nat.d_pat, &nat.d_cnt);
				nat.mtbl_d = NeoCore::gen_mtbl_d(&lp, &ll,
					&nat.d_pat);
				nat.l_pat = lp; nat.l_loc = ll;
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n3 clone group: append an empty [0-wrap, max-wrap] clone of
	/// the step-3 group (the round-1 false-FP oracle) -> the group
	/// uniqueness product sees enc(step3) twice -> UNSAT.
	#[test]
	fn test_m6_neg_clone_group() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				// find the step-3 group's enc + si values
				let i3 = (t.n_pad..t.enc.len()).find(|&i|
					t.step[i] == Fr::from(3u32)).unwrap();
				let (enc, sid, sbw) = (t.enc[i3], t.si_step[i3],
					t.si_b_bwd[i3]);
				let mx = Fr::from(
					(1u32 << read_global_config().range2_bit) - 1);
				for (id, loc) in [(Fr::from(0u32), Fr::from(0u32)),
					(Fr::from(1u32), mx)] {
					t.enc.push(enc); t.id.push(id);
					t.loc.push(loc);
					t.cat.push(Fr::from(0u32));
					t.step.push(Fr::from(3u32));
					t.subsig.push(Fr::from(1u32));
					t.si_step.push(sid); t.si_b_bwd.push(sbw);
					for v in [&mut t.prev_id1, &mut t.prev_loc1,
						&mut t.prev_loc2, &mut t.pat, &mut t.rg1,
						&mut t.rg2, &mut t.enc_prev,
						&mut t.b_bwd, &mut t.d_c1, &mut t.d_c2,
						&mut t.d_below_lo, &mut t.d_below_hi,
						&mut t.d_above_lo, &mut t.d_above_hi,
						&mut t.d_sort] { v.push(Fr::from(0u32)); }
					let rg2t = Fr::from(RANGE2);
					for v in [&mut t.si_subsig, &mut t.si_pat,
						&mut t.si_rg1, &mut t.si_rg2,
						&mut t.si_enc_prev] { v.push(rg2t); }
				}
				// keep the lookup m-table honest for the new rows
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n7 seed pins: (a) seed moved off loc 1 -> fused pin fails;
	/// (b) seed tagged FP -> same pin (r1-fused term) fails.
	#[test]
	fn test_m6_neg_seed_pins() {
		for case in 0..2 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					let t = &mut nat.t;
					let i0 = (t.n_pad..t.enc.len()).find(|&i|
						t.step[i].is_zero()
						&& t.loc[i] == Fr::from(1u32)).unwrap();
					if case == 0 { t.loc[i0] = Fr::from(5u32); }
					else { t.cat[i0] = Fr::from(CAT_FP); }
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"seed pin case {}", case);
		}
	}

	/// n4 unity escape: cat=7 on a real row -> the wrap residual
	/// becomes 1 on a non-sentinel loc -> wrap-force fails.
	#[test]
	fn test_m6_neg_cat7() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(27u32)).unwrap();
				t.cat[i] = Fr::from(7u32);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n8 false FP: retag reachable a7:101 as FP pointing at the
	/// true neighbors (96,141) -> the below-check gap is negative
	/// and no in-range bracket exists -> UNSAT.
	#[test]
	fn test_m6_neg_false_fp() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(101u32)).unwrap();
				t.cat[i] = Fr::from(CAT_FP);
				// bracket claim: (id 3 = 96, id 4 = 141) in the
				// step-6 target coords
				t.prev_id1[i] = Fr::from(3u32);
				t.prev_loc1[i] = Fr::from(96u32);
				t.prev_loc2[i] = Fr::from(141u32);
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n2 hygiene: (a) a pad row given a nonzero loc payload -> the
	/// is_pad*(loc+cat) force fires; (b) row 0 made non-pad -> the
	/// key[0]==0 anchor (plus pad-monotone) fires.
	#[test]
	fn test_m6_neg_pad_hygiene() {
		for case in 0..2 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					assert!(nat.t.n_pad >= 1);
					if case == 0 { nat.t.loc[0] = Fr::from(5u32); }
					else { nat.t.enc[0] = Fr::from(123u32); }
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"pad hygiene case {}", case);
		}
	}

	/// n5 non-adjacent FP pair: the 7:131 bracket skips rank 3 (96)
	/// and claims (79 @ rank 2, 141) -- both true target rows, NOT
	/// rank-adjacent. The numeric gap checks are kept honest (below
	/// diff rewritten to 131-79-9-1=42) so ONLY the (prev_id1+1,
	/// prev_loc2) lookup can fail: rank 3 holds 96, not 141.
	#[test]
	fn test_m6_neg_fp_nonadjacent() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(131u32)).unwrap();
				t.prev_id1[i] = Fr::from(2u32);
				t.prev_loc1[i] = Fr::from(79u32);
				t.d_below_lo[i] = Fr::from(42u32);
				t.d_below_hi[i] = Fr::from(0u32);
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// remove row i from every QmTable column (negative-test tamper).
	fn remove_row(t: &mut QmTable<Fr>, i: usize) {
		let cols: [&mut Vec<Fr>; 28] = [
			&mut t.enc, &mut t.id, &mut t.loc, &mut t.cat,
			&mut t.step, &mut t.subsig, &mut t.prev_id1,
			&mut t.prev_loc1, &mut t.prev_loc2, &mut t.pat,
			&mut t.rg1, &mut t.rg2, &mut t.enc_prev, &mut t.b_bwd,
			&mut t.d_c1, &mut t.d_c2, &mut t.d_below_lo,
			&mut t.d_below_hi, &mut t.d_above_lo,
			&mut t.d_above_hi, &mut t.d_sort, &mut t.si_step,
			&mut t.si_subsig, &mut t.si_pat, &mut t.si_rg1,
			&mut t.si_rg2, &mut t.si_enc_prev, &mut t.si_b_bwd];
		for c in cols { c.remove(i); }
	}

	/// n6 dropped seed -- the anchor's raison d'etre: remove the
	/// seed row, then vacuously FP every real row against its
	/// predecessor group's wrap pair (prev_loc1=0 / prev_loc2=max
	/// turn both bracket masks off). Selectors, wf, sort, merge and
	/// acc all still balance; the ONLY failing family is the
	/// per-subsig seed-anchor query (enc0, 1, 1) -- without it this
	/// forgery would blanket-discharge the whole subsig.
	#[test]
	fn test_m6_neg_drop_seed() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let mx = Fr::from(
					(1u32 << read_global_config().range2_bit) - 1);
				let t = &mut nat.t;
				let i0 = (t.n_pad..t.enc.len()).find(|&i|
					t.step[i].is_zero()
					&& t.loc[i] == Fr::from(1u32)).unwrap();
				remove_row(t, i0);
				// re-close step-0 as a wrap-only group: the
				// max-wrap now follows the 0-wrap directly.
				t.id[i0] = Fr::from(1u32);
				t.d_sort[i0] = mx - Fr::from(1u32);
				for i in t.n_pad..t.enc.len() {
					if t.enc[i].is_zero() || t.loc[i].is_zero()
						|| t.loc[i] == mx { continue; }
					t.cat[i] = Fr::from(CAT_FP);
					t.prev_id1[i] = Fr::from(0u32);
					t.prev_loc1[i] = Fr::from(0u32);
					t.prev_loc2[i] = mx;
					for v in [&mut t.d_c1, &mut t.d_c2,
						&mut t.d_below_lo, &mut t.d_below_hi,
						&mut t.d_above_lo, &mut t.d_above_hi] {
						v[i] = Fr::from(0u32);
					}
				}
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
				let (a, m) = NeoCore::gen_acc_padded(t,
					&a18_store());
				nat.acc_out = a; nat.mtbl_acc = m;
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n10 D forgeries: (a) lied cnt -- pat 3 claims 2 store steps,
	/// the cnt-forcing logup sees one pat-3 pole; (b) m mismatch --
	/// a real L row claims m_aux=0, the (pat, m) -> D forcing has no
	/// (pat, 0) row. (Split-cnt needs a negative d_diff and is
	/// killed by the outer RANGE2 -> tier-2 H-family.)
	#[test]
	fn test_m6_neg_d_family() {
		for case in 0..2 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					if case == 0 {
						let j = nat.d_pat.iter().position(|p|
							*p == Fr::from(3u32)).unwrap();
						nat.d_cnt[j] += Fr::from(1u32);
					} else {
						let mx = Fr::from((1u32 <<
							read_global_config().range2_bit) - 1);
						let j = (0..nat.l_loc.len()).find(|&j|
							!nat.l_loc[j].is_zero()
							&& nat.l_loc[j] != mx).unwrap();
						nat.m_aux[j] = Fr::from(0u32);
					}
				}));
			assert!(!cs.is_satisfied().unwrap(), "D case {}", case);
		}
	}

	/// n11 fake C on an unreachable row: retag FP 5:106 as C with an
	/// in-window (97..105) predecessor claim (rank 1, loc 100). The
	/// gap advice is honest (d_c1=5, d_c2=3), but step-4's target
	/// rows are wraps + 33 only -- the C-pred lookup finds nothing.
	#[test]
	fn test_m6_neg_fake_c() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(106u32)).unwrap();
				t.cat[i] = Fr::from(CAT_C);
				t.prev_id1[i] = Fr::from(1u32);
				t.prev_loc1[i] = Fr::from(100u32);
				t.d_c1[i] = Fr::from(5u32);
				t.d_c2[i] = Fr::from(3u32);
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n12 joint store-drop: full a1..a8 match (n9 base), but the
	/// prover drops the step-8 GROUP and its s_enc row and zeroes
	/// cnt(pat 8) together -- uniqueness/cnt/counting all rebalance
	/// internally, no last-step C remains, the match vanishes.
	/// Must be UNSAT via the run-completeness lemma.
	#[test]
	fn test_m6_neg_joint_store_drop() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm, 161,
			Some(&|nat: &mut NeoCore<Fr>| {
				let f8 = Fr::from(8u32);
				// (1) drop every step-8 row (wraps + the C at 108)
				let t = &mut nat.t;
				for i in (t.n_pad..t.enc.len()).rev() {
					if t.step[i] == f8 { remove_row(t, i); }
				}
				// (2) drop the (subsig, step-8) store row
				let j = nat.s_pat.iter().position(|p| *p == f8)
					.unwrap();
				nat.s_enc.remove(j);
				nat.s_pat.remove(j);
				// (3) cnt(pat 8) -> 0 (pat 8 stays in D via L)
				let k = nat.d_pat.iter().position(|p| *p == f8)
					.unwrap();
				nat.d_cnt[k] = Fr::from(0u32);
				// (4) rebalance every dependent advice table
				let rid = NeoCore::gen_rid_native(&nat.t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(&nat.t, &rid,
					&nat.subsig_nat);
				nat.m_aux = StepQueueNeo::gen_merge_m_aux(
					&nat.l_pat, &nat.l_loc, &nat.d_pat,
					&nat.d_cnt);
				nat.mtbl_d = NeoCore::gen_mtbl_d(&nat.l_pat,
					&nat.l_loc, &nat.d_pat);
				let (a, m) = NeoCore::gen_acc_padded(&nat.t,
					&a18_store());
				nat.acc_out = a;
				nat.mtbl_acc = m;
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n13 tail truncation x3: same joint drop as n12 but for steps
	/// 6..8 -- the run ends at the NORMAL-tagged step-5 group, so
	/// the wf run-completeness lemma (final-run clause) fires.
	#[test]
	fn test_m6_neg_tail_truncation() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm, 161,
			Some(&|nat: &mut NeoCore<Fr>| {
				let dropped = [Fr::from(6u32), Fr::from(7u32),
					Fr::from(8u32)];
				let t = &mut nat.t;
				for i in (t.n_pad..t.enc.len()).rev() {
					if dropped.contains(&t.step[i]) {
						remove_row(t, i);
					}
				}
				for p in &dropped {
					let j = nat.s_pat.iter().position(|x|
						x == p).unwrap();
					nat.s_enc.remove(j);
					nat.s_pat.remove(j);
					let k = nat.d_pat.iter().position(|x|
						x == p).unwrap();
					nat.d_cnt[k] = Fr::from(0u32);
				}
				let rid = NeoCore::gen_rid_native(&nat.t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(&nat.t, &rid,
					&nat.subsig_nat);
				nat.m_aux = StepQueueNeo::gen_merge_m_aux(
					&nat.l_pat, &nat.l_loc, &nat.d_pat,
					&nat.d_cnt);
				nat.mtbl_d = NeoCore::gen_mtbl_d(&nat.l_pat,
					&nat.l_loc, &nat.d_pat);
				let (a, m) = NeoCore::gen_acc_padded(&nat.t,
					&a18_store());
				nat.acc_out = a;
				nat.mtbl_acc = m;
			}));
		assert!(!cs.is_satisfied().unwrap());
	}
}

// ============================================================
//   M6 tier-2 tests: full harness (si / outer lookups live)
// ============================================================
#[cfg(test)]
mod tests_neo_m6_h {
	use super::*;
	use ark_bn254::Fr;
	use crate::gadgets::word_extract::{LEGS,
		tests_word_extract_gadget::test_gadget_adv_ex};
	use crate::gadgets::fsm_adv::{FsmAdvAdvice, FsmAdvCapacity};
	use crate::gadgets::word_extract_adv::WordExtractAdvAdvice;
	use data_processor::clam_db::ClamavDB;
	use data_processor::clamav::default_clamav_cfg;
	use utils::consts::get_global_config;
	use utils::data::{pack_nibbles, pad_word_to_multiple};
	use utils::os::{read_nibbles, proj_root, write_to_file};

	/// One single-cycle aggressive end-to-end case through the REAL
	/// harness (word_extract -> fsm_adv -> neo discharge), with the
	/// si columns and outer DB lookups live. `tamper` (negatives)
	/// mutates the native bundle and rebuilds the statement through
	/// the same N3 column assembly, so ONLY the mutated values
	/// differ from the honest witness.
	fn run_neo_h_case(db: &ClamavDB<Fr>, dir: &str, content: &str,
		b_expect_sat: bool,
		tamper: Option<&dyn Fn(&mut NeoCore<Fr>)>) {
		let b_igc = false;
		let bundle = &db.bundle_subsig;
		let acdfa = &bundle.vec_acdfa[0];
		let store_id = 0;
		let fsm_id = ClamavDB::<Fr>::pm_acdfa_id(store_id, b_igc);
		let steps_store = &bundle.vec_subsig_step_stores[store_id];
		let mut ss: Vec<usize> = steps_store.subsig_ids.iter()
			.cloned().filter(|s| *s != 0).collect();
		ss.sort();
		let input_subsigs: Vec<Fr> = ss.iter()
			.map(|s| Fr::from(*s as u32)).collect();
		//start positions at M+1 so backward windows never underflow
		let m_aggr = db.aggressive_max_span_nibbles;
		let init_loc = if m_aggr > 0 {
			Fr::from((m_aggr + 1) as u32)
		} else { Fr::from(1u32) };
		let wlen = 2usize;
		let (nibble_len, sbits) = (wlen * LEGS,
			acdfa.state_part_bits);
		let cap = FsmAdvCapacity { max_nibble_len: nibble_len,
			acdfa_state_part_bits: sbits, subsigs: 25,
			avg_pats_per_subsig: 4, basis_pats_in_trace: 25 * 100,
			basis_unique_states: 20 * 100,
			basis_acc_states: 15 * 100, halo_nibbles: 0 };
		let cap_disc = DischargeAdvCapacity {
			max_nibble_len: nibble_len, subsigs: cap.subsigs,
			universe_subsigs: cap.subsigs,
			avg_active_pats_per_subsig: 2,
			basis_pats_in_trace: cap.basis_pats_in_trace,
			perc_pats_expansion_rate: 600, b_aggressive: true,
				wrap_keys: 0,
			prod_pats_expansion: 2500 * 600 };
		let path = format!("{}/data/{}/word.txt", proj_root(), dir);
		write_to_file(&path, content);
		let f_nibbles: Vec<Fr> = read_nibbles(&path).iter()
			.map(|x| Fr::from(*x as u32)).collect();
		let all_word = pad_word_to_multiple::<Fr>(
			&pack_nibbles(&f_nibbles), wlen);
		assert!(all_word.len() / wlen == 1, "single-cycle case");
		let word = all_word[0..wlen].to_vec();
		let adv_wea = WordExtractAdvAdvice::new(&word, word.len(),
			false).expect("wea");
		let stmt_wea = adv_wea.stmt_container;
		let cfg_wea = stmt_wea.lock().unwrap().get_cfg();
		let nibbles = stmt_wea.lock().unwrap()
			.get_container("nibbles").unwrap()
			.lock().unwrap().to_vec();
		let adv_faa = FsmAdvAdvice::new(b_igc, 1, &nibbles, &[],
			&acdfa, Fr::from((acdfa.init_state + 1) as u32),
			init_loc, &input_subsigs, &cap, fsm_id,
			&bundle.vec_subsig_stores[store_id], 0).expect("faa");
		let stmt_faa = adv_faa.stmt_container;
		let cfg_faa = stmt_faa.lock().unwrap().get_cfg();
		let pat_loc = stmt_faa.lock().unwrap().search_container(
			"fsm_adv_stmt_cs packed_trace pat_loc sorted_tbl")
			.unwrap();
		let locs = stmt_faa.lock().unwrap().search_container(
			"fsm_adv_stmt_cs fsm_acc locs").unwrap()
			.lock().unwrap().to_vec();
		let last_loc = locs[locs.len() - 1];
		let adv_disc = match tamper {
			None => DischargeAdvNeoAdvice::new_aggr(b_igc, 1,
				&pat_loc, &input_subsigs, fsm_id, steps_store,
				&cap_disc, last_loc, 0, 0).expect("neo adv"),
			Some(tf) => {
				let seed_subsigs: Vec<Fr> = input_subsigs.iter()
					.filter(|s| !s.is_zero()).cloned().collect();
				let seed = DischargeAdvAdvice::<Fr>
					::gen_empty_steps_queue_serialized(b_igc,
					&seed_subsigs, steps_store, fsm_id,
					&cap_disc);
				let gen = StepQueueNeo::from_stepqueue(seed)
					.gen_shared_core_advice(0, &pat_loc,
					steps_store, last_loc + Fr::from(1u32))
					.expect("core");
				let (_c, combo, mut nat) = gen.gen_core_stmt(
					&pat_loc, steps_store).expect("stmt");
				tf(&mut nat);
				let core = StepQueueNeo::core_container(&nat);
				let sc = Container::<Fr>::new(
					"discharge_adv_stmt_cs");
				sc.lock().unwrap().add_container(core);
				sc.lock().unwrap().add_container(combo);
				DischargeAdvNeoAdvice {
					capacity: cap_disc.clone(), fsm_id,
					stmt_container: sc, b_igc, offset_fsm: 1 }
			}
		};
		let stmt_disc = adv_disc.stmt_container;
		let cfg_disc = stmt_disc.lock().unwrap().get_cfg();
		let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa.clone(),
			cfg_disc];
		ContainerConfig::adjust_locations(&mut vec_cfg);
		let cps1 = stmt_wea.lock().unwrap().gen_stmt_components();
		let cps2 = stmt_faa.lock().unwrap().gen_stmt_components();
		let cps3 = stmt_disc.lock().unwrap().gen_stmt_components();
		let cps = cps1.0.into_iter().zip(cps2.0.into_iter())
			.map(|(a, b)| vec![a, b].concat())
			.collect::<Vec<Vec<Fr>>>();
		let cps = cps.into_iter().zip(cps3.0.into_iter())
			.map(|(a, b)| vec![a, b].concat())
			.collect::<Vec<Vec<Fr>>>();
		let mut dcg = DischargeAdvNeoGadget::<Fr>::new(b_igc, 1,
			&cap_disc, fsm_id,
			&vec![cfg_wea.clone(), cfg_faa.clone()],
			&bundle.vec_subsig_step_stores[0]);
		dcg.set_container_cfg(vec_cfg.clone().into(), 2);
		let rg = Arc::new(dcg);
		test_gadget_adv_ex::<Fr>(rg, &word, &cps[0], &cps[1],
			&cps[2], &cps[6], &cps[7],
			&vec![cps[3].clone(), cps[4].clone(),
				cps[5].clone()].concat(),
			4usize, false, Some(vec_cfg), b_expect_sat);
	}

	/// per-test dir: the H tests run in parallel and a shared build
	/// dir races (DB build files + word.txt).
	fn build_fwd_db(dir: &str) -> ClamavDB<Fr> {
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 4; //[ab][ab] -> 4 variant subsigs
		cfg.min_bag_len = 2;
		//aggressive shape: keyword at one END (fwd = first) + a
		//bounded fanned class part -- the DLP proximity shape.
		let sigs = vec![
			"Agg.NeoDisc.fwd;Engine:51-255,Target:0;0;/HELLO.{0,4}[ab][ab]/"
				.to_string()];
		let p = format!("{}/data/{}", proj_root(), dir);
		std::fs::create_dir_all(&p).unwrap();
		ClamavDB::<Fr>::build_test_db(&cfg, dir,
			&sigs, &vec![], &vec![], &vec![]).expect("neo fwd db")
	}

	/// H1 (user-required): FORWARD aggressive subsigs end-to-end.
	/// Variant "ab" matches twice (both in-window => terminal C
	/// rows feed the acc); variants aa/ba/bb keep only the keyword
	/// step => discharged. The neo {C,FP} core + si columns +
	/// outer DB lookups must all hold.
	#[test]
	fn test_m6_h1_aggr_forward_e2e() {
		get_global_config().basis_failed_subsigs = 10000;
		let db = build_fwd_db("debug/sed/neoaggrh1");
		run_neo_h_case(&db, "debug/sed/neoaggrh1",
			"xxHELLOabxxab", true, None);
		get_global_config().basis_failed_subsigs = 0;
	}

	/// H2 (user-required): BACKWARD aggressive subsig end-to-end
	/// (keyword-first reversed chain; step-1 forward anchor, i>=2
	/// mirrored windows). Same fixture family as the legacy
	/// test_m4_discharge_circuit_backward.
	#[test]
	fn test_m6_h2_aggr_backward_e2e() {
		get_global_config().basis_failed_subsigs = 10000;
		let mut cfg = default_clamav_cfg();
		cfg.b_aggressive_sde_for_rep = true;
		cfg.sde_rep_fanout_cap = 4;
		cfg.min_bag_len = 2;
		let sigs = vec![
			"Agg.NeoDisc.bwd;Engine:51-255,Target:0;0;/[ab][ab].{0,4}KEYWORD/"
				.to_string()];
		let p = format!("{}/data/debug/sed/neoaggrbwd",
			proj_root());
		std::fs::create_dir_all(&p).unwrap();
		let db = ClamavDB::<Fr>::build_test_db(&cfg,
			"debug/sed/neoaggrbwd", &sigs, &vec![], &vec![],
			&vec![]).expect("neo bwd db");
		assert!(db.bundle_subsig.vec_subsig_step_stores[0]
			.subsig_to_steps.values()
			.any(|it| it.is_backward && it.vec_pm_bounds.len() >= 2),
			"need a >=2-step backward subsig");
		run_neo_h_case(&db, "debug/sed/neoaggrbwd", "abxxKEYWORD",
			true, None);
		get_global_config().basis_failed_subsigs = 0;
	}

	/// H3 pack-aliasing prev_id1 forgery: shift a C row's prev_id1
	/// far out of rank range. The challenge-packed QR-target lookup
	/// cannot alias (r1 is drawn after the advice commits), so the
	/// query misses -> UNSAT.
	#[test]
	fn test_m6_h3_neg_prev_id1_forgery() {
		get_global_config().basis_failed_subsigs = 10000;
		let db = build_fwd_db("debug/sed/neoaggrh3");
		run_neo_h_case(&db, "debug/sed/neoaggrh3",
			"xxHELLOabxxab", false,
			Some(&|nat: &mut NeoCore<Fr>| {
				let rb = read_global_config().range2_bit;
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.cat[i] == Fr::from(CAT_C)
					&& !t.step[i].is_zero()).unwrap();
				t.prev_id1[i] += Fr::from(1u64 << rb);
			}));
		get_global_config().basis_failed_subsigs = 0;
	}

	/// H4 b_bwd lie: flip the direction bit on a step>=2 C row: the
	/// C-cert gap select flips sign, so the d_c1/d_c2 binds fail ->
	/// UNSAT. (A step-1 flip is b_bwd_row-masked in-circuit and
	/// caught only by the si_b_bwd DB value-lookup, which this
	/// harness leaves to the folding framework's lookup share.)
	#[test]
	fn test_m6_h4_neg_b_bwd_lie() {
		get_global_config().basis_failed_subsigs = 10000;
		let db = build_fwd_db("debug/sed/neoaggrh4");
		run_neo_h_case(&db, "debug/sed/neoaggrh4",
			"xxHELLOabxxab", false,
			Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.cat[i] == Fr::from(CAT_C)
					&& field_to_usize(&t.step[i]) >= 2).unwrap();
				t.b_bwd[i] = Fr::from(1u32) - t.b_bwd[i];
			}));
		get_global_config().basis_failed_subsigs = 0;
	}

	/// H5 strict-sort duplicate: clone the 2nd row of the 2-loc
	/// "ab" group onto the 1st (identical valid row, d_sort=-1
	/// keeps the bind consistent). Killed by the outer RANGE2 on
	/// si_d_sort and the merge counting logup (m_aux pinned to the
	/// per-variant cnt, two hits on one L row).
	#[test]
	fn test_m6_h5_neg_duplicate_loc() {
		get_global_config().basis_failed_subsigs = 10000;
		let db = build_fwd_db("debug/sed/neoaggrh5");
		run_neo_h_case(&db, "debug/sed/neoaggrh5",
			"xxHELLOabxxab", false,
			Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				//find a group with 2 real rows (the WORLD step)
				let i2 = (t.n_pad + 1..t.enc.len()).find(|&i|
					t.enc[i] == t.enc[i - 1]
					&& !t.loc[i - 1].is_zero()
					&& !t.loc[i].is_zero()).unwrap();
				let i1 = i2 - 1;
				t.loc[i2] = t.loc[i1];
				t.cat[i2] = t.cat[i1];
				t.prev_id1[i2] = t.prev_id1[i1];
				t.prev_loc1[i2] = t.prev_loc1[i1];
				t.prev_loc2[i2] = t.prev_loc2[i1];
				t.d_c1[i2] = t.d_c1[i1];
				t.d_c2[i2] = t.d_c2[i1];
				t.d_sort[i2] = -Fr::from(1u32); //loc diff -1 bind
				t.d_sort[i2 + 1] = if t.enc[i2 + 1] == t.enc[i2] {
					t.loc[i2 + 1] - t.loc[i2] - Fr::from(1u32)
				} else { t.d_sort[i2 + 1] };
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		get_global_config().basis_failed_subsigs = 0;
	}
}

#[cfg(test)]
mod tests_neo_nonaggr {
	use super::*;
	use super::tests_neo_m4::{fixture_capacity, A18_DEFAULT_MIN};
	use super::tests_neo_m5::{a18_store, a18_carried, mk_pat_loc};
	use super::tests_neo_m6::{hm_to_l_cols, hm_gen, alloc_vars,
		cat_rows};
	use ark_bn254::Fr;
	use utils::consts::read_global_config;
	use ark_relations::r1cs::{ConstraintSystem,
		ConstraintSystemRef};
	use crate::gadgets::commons::new_var;
	use data_processor::type_def::SubsigStepStore;

	fn f(x: u32) -> Fr { Fr::from(x) }

	/// fig-14 chunk-2 L (the carried-queue worked example).
	fn fig14c2_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(2, vec![111]);
		m.insert(5, vec![106]);
		m.insert(6, vec![96, 141]);
		m.insert(7, vec![101, 131]);
		m
	}

	/// shared-core + SP pass over (carried, hm) -- the advice-side
	/// entry every test drives.
	fn gen_tagged(carried: &StepQueueNeo<Fr>,
		hm: &HashMap<u32, Vec<u32>>, info: &SubsigStepStore,
		dmin: u32) -> StepQueueNeo<Fr> {
		let mut g = carried.gen_shared_core_from_hm(0, &hm_gen(hm),
			info, f(dmin)).expect("shared core");
		g.apply_sp_pass(info);
		g
	}

	/// run the NON-AGGRESSIVE core: advice (core+SP+fill) -> alloc
	/// -> assert_neo_core_nonaggr. `tamper` edits the natives
	/// pre-allocation (negative-test hook). Returns (cs, natives).
	pub(crate) fn run_core_nonaggr(info: &SubsigStepStore,
		carried_sq: &StepQueue<Fr>, hm: &HashMap<u32, Vec<u32>>,
		default_min: u32,
		tamper: Option<&dyn Fn(&mut NeoCore<Fr>)>)
	-> (ConstraintSystemRef<Fr>, NeoCore<Fr>) {
		let carried = StepQueueNeo::from_stepqueue(
			carried_sq.clone());
		let gen = gen_tagged(&carried, hm, info, default_min);
		let (l_pat, l_loc) = hm_to_l_cols(hm);
		let (mut nat, _qi, _qc) = NeoCore::gen_nonaggr(&gen, info,
			l_pat, l_loc, &hm_gen(hm), carried_sq,
			f(default_min), 0).expect("gen_nonaggr");
		if let Some(tf) = tamper { tf(&mut nat); }
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = alloc_vars(&cs, &nat);
		let r1 = new_var(&cs, Fr::from(12345u32));
		let r2 = new_var(&cs, Fr::from(67890u32));
		let dmin = new_var(&cs, f(default_min));
		DischargeAdvNeoGadget::<Fr>::assert_neo_core_nonaggr(
			cs.clone(), &nat, &vars, &dmin, &r1, &r2, 0)
			.expect("assert core nonaggr");
		(cs, nat)
	}

	/// (step, loc) rows of `cat` in a tagged StepQueueNeo, sorted.
	fn snap(q: &StepQueueNeo<Fr>, cat: u32) -> Vec<(u32, u32)> {
		let fc = f(cat);
		let mut v = vec![];
		for its in q.store_items.values() {
			for it in its {
				for j in 0..it.base.locs.len() {
					if it.cat[j] == fc {
						v.push((
							field_to_usize(&it.base.step) as u32,
							field_to_usize(&it.base.locs[j])
								as u32));
					}
				}
			}
		}
		v.sort();
		v
	}

	/// SP GOLDEN (fig-14 chunk 2): the deterministic M5 partition
	/// {C,FP,BP} plus the SP pass. len = 5 (deepest C step); step 2
	/// (fz=5) freezes and demotes 111 keeping min 21; steps 3/4
	/// (single C) and 1/5 (singletons, single C) are no-ops.
	#[test]
	fn test_nonaggr_sp_golden() {
		let info = a18_store();
		let g = gen_tagged(&a18_carried(), &fig14c2_hm(), &info,
			A18_DEFAULT_MIN);
		assert_eq!(snap(&g, CAT_C), vec![(0, 1), (1, 6), (2, 21),
			(3, 27), (4, 33), (5, 39)]);
		assert_eq!(snap(&g, CAT_SP), vec![(2, 111)]);
		assert_eq!(snap(&g, CAT_FP), vec![(5, 106), (7, 131)]);
		assert_eq!(snap(&g, CAT_BP), vec![(6, 73), (6, 79),
			(6, 96), (6, 141), (7, 101)]);
	}

	/// SP corners. (i) singleton-step surplus: fresh chain to a5
	/// with TWO a5 matches -> the non-min demotes even with fz=0
	/// (freeze via the seed group). (ii) len < fz: chain stops at
	/// a4 -> step 2 (fz=5) is NOT frozen, both its C rows stay.
	/// (iii) the kept row is always the step minimum.
	#[test]
	fn test_nonaggr_sp_corners() {
		let info = a18_store();
		let seed = super::tests_neo_m5::a18_carried()
			.store_items[&f(1)][0].clone();
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed.base.clone()]);
		let seed_q = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m, &fixture_capacity(),
			StepQueueType::ResLarge, false));
		//(i) two reachable a5 locs: 39 in [34,42] of 33; 41 too.
		let mut hm = HashMap::new();
		hm.insert(1, vec![6]); hm.insert(2, vec![20]);
		hm.insert(3, vec![27]); hm.insert(4, vec![33]);
		hm.insert(5, vec![39, 41]);
		let g = gen_tagged(&seed_q, &hm, &info, 161);
		assert_eq!(snap(&g, CAT_SP), vec![(5, 41)]);
		assert!(snap(&g, CAT_C).contains(&(5, 39)));
		//(ii) len=4 < fz=5: step 2 keeps both C rows (20 and 24:
		//both reach 27's window? 27 in [21,29] of 20, [25,33] of
		//24 -- both survive BP: 20/24 + rg2_3=9 >= min_3=27).
		let mut hm2 = HashMap::new();
		hm2.insert(1, vec![6]); hm2.insert(2, vec![20, 24]);
		hm2.insert(3, vec![27]); hm2.insert(4, vec![33]);
		//dmin=34 (chunk ends at 33): the tail survives BP; with
		//dmin=161 the unanchored chain would F1-cascade to BP.
		let g2 = gen_tagged(&seed_q, &hm2, &info, 34);
		assert!(snap(&g2, CAT_SP).is_empty());
		assert!(snap(&g2, CAT_C).contains(&(2, 20)));
		assert!(snap(&g2, CAT_C).contains(&(2, 24)));
	}

	/// FILL GOLDEN: the QmNonAggrCols witness values on the fig-14
	/// chunk-2 bundle, hand-checked (see the struct doc example).
	#[test]
	fn test_nonaggr_fill_golden() {
		let info = a18_store();
		let (_cs, nat) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &fig14c2_hm(),
			A18_DEFAULT_MIN, None);
		let t = &nat.t;
		let na = &t.nonaggr;
		let mx = f((1u32 << read_global_config().range2_bit) - 1);
		let row = |loc: u32| (t.n_pad..t.enc.len())
			.find(|&i| t.loc[i] == f(loc) && !t.cat[i].is_zero())
			.unwrap();
		//BP 73: enc_next = step-7 key; step 7 carries nothing =>
		//w_next = max, min_eff = 161, d_bp = 161-73-9-1 = 78.
		let i73 = row(73);
		assert_eq!(t.cat[i73], f(CAT_BP));
		assert_eq!(na.rg2_next[i73], f(9));
		assert_eq!(na.w_next[i73], mx);
		assert_eq!(na.d_bp[i73], f(78));
		assert_eq!(na.bp_prev_val[i73], t.enc[i73]);
		//BP 101 (terminal-1): d_bp = 161-101-9-1 = 50.
		let i101 = row(101);
		assert_eq!(na.d_bp[i101], f(50));
		//SP 111: fz=5, w_fz=39 (a5 carries), w_sp=21 (kept min),
		//d_sp = 111-21-1 = 89, d_fz = max-39-1.
		let i111 = row(111);
		assert_eq!(t.cat[i111], f(CAT_SP));
		assert_eq!(na.fz[i111], f(5));
		assert_eq!(na.w_fz[i111], f(39));
		assert_eq!(na.d_fz[i111], mx - f(40));
		assert_eq!(na.w_sp[i111], f(21));
		assert_eq!(na.d_sp[i111], f(89));
		//merge bits: carried rows m_carry_in=1 & b_l=0; L rows
		//b_l=1 & m_carry_in=0; the seed row is carried.
		for l in [6u32, 21, 27, 33, 39, 73, 79] {
			let i = row(l);
			assert_eq!(na.m_carry_in[i], f(1), "carried {}", l);
			assert_eq!(na.b_l[i], f(0), "carried {}", l);
		}
		for l in [96u32, 141, 101, 106, 111, 131] {
			let i = row(l);
			assert_eq!(na.b_l[i], f(1), "L row {}", l);
			assert_eq!(na.m_carry_in[i], f(0), "L row {}", l);
		}
		let iseed = (t.n_pad..t.enc.len()).find(|&i|
			t.step[i].is_zero() && t.cat[i] == f(CAT_C)).unwrap();
		assert_eq!(na.m_carry_in[iseed], f(1));
		//C re-pick in QC rank: 27's pred is the kept min 21 at
		//rank 1 (111 was demoted to SP and holds no QC rank).
		let i27 = row(27);
		assert_eq!(t.prev_loc1[i27], f(21));
		assert_eq!(t.prev_id1[i27], f(1));
		//q_c natives = the C projection {1,6,21,27,33,39}.
		let mut qc: Vec<u32> = nat.qc_loc.iter()
			.filter(|l| !l.is_zero())
			.map(|l| field_to_usize(l) as u32).collect();
		qc.sort();
		assert_eq!(qc, vec![1, 6, 21, 27, 33, 39]);
	}

	/// STMT GOLDEN: gen_core_stmt_nonaggr container == native
	/// col-for-col on the new columns; q_i mirrors the carried
	/// queue's to_container layout; CapErr on an undersized budget.
	#[test]
	fn test_nonaggr_stmt_golden() {
		let info = a18_store();
		let ct = mk_pat_loc(&fig14c2_hm());
		let carried_sq = a18_carried().to_stepqueue();
		let g = gen_tagged(&a18_carried(), &fig14c2_hm(), &info,
			A18_DEFAULT_MIN);
		let (core, ct_qi, ct_qc, nat) = g.gen_core_stmt_nonaggr(
			&ct, &info, &carried_sq, f(A18_DEFAULT_MIN), 0)
			.expect("stmt");
		let get = |n: &str| core.lock().unwrap().get_container(n)
			.unwrap().lock().unwrap().to_vec();
		assert_eq!(get("b_l"), nat.t.nonaggr.b_l);
		assert_eq!(get("enc_next"), nat.t.nonaggr.enc_next);
		assert_eq!(get("bp_prev_val"), nat.t.nonaggr.bp_prev_val);
		assert_eq!(get("w_next"), nat.t.nonaggr.w_next);
		assert_eq!(get("d_bp"), nat.t.nonaggr.d_bp);
		assert_eq!(get("enc_fz"), nat.t.nonaggr.enc_fz);
		assert_eq!(get("w_fz"), nat.t.nonaggr.w_fz);
		assert_eq!(get("w_sp"), nat.t.nonaggr.w_sp);
		assert_eq!(get("d_sp"), nat.t.nonaggr.d_sp);
		assert_eq!(get("m_carry_in"), nat.t.nonaggr.m_carry_in);
		assert_eq!(get("mtbl_qc"), nat.mtbl_qc);
		assert_eq!(get("si_fz"), nat.t.nonaggr.si_fz);
		assert_eq!(get("si_bp_prev_val"),
			nat.t.nonaggr.si_bp_prev);
		//q_i == the carried queue's own serialization
		let qi_enc = ct_qi.lock().unwrap().get_container("encoded")
			.unwrap().lock().unwrap().to_vec();
		assert_eq!(qi_enc, nat.qi_enc);
		let qc_loc = ct_qc.lock().unwrap().get_container("locs")
			.unwrap().lock().unwrap().to_vec();
		assert_eq!(qc_loc, nat.qc_loc);
		//CapErr on an undersized T_qm budget (never silent).
		let mut small = g.clone();
		small.capacity.avg_active_pats_per_subsig = 8;
		assert!(small.gen_qm_table(&info, false).is_err());
	}

	/// CIRCUIT POSITIVE + COST BAND: the fig-14 chunk-2 core is SAT;
	/// the constraint count stays in a +/-25% band of the calibrated
	/// value (drift guard, like test_m6_cost_band).
	#[test]
	fn test_nonaggr_circuit_positive() {
		let info = a18_store();
		let (cs, nat) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &fig14c2_hm(),
			A18_DEFAULT_MIN, None);
		assert!(cs.is_satisfied().unwrap(), "unsat: {:?}",
			cs.which_is_unsatisfied());
		assert_eq!(cat_rows(&nat, CAT_SP), vec![(2, 111)]);
		let n = cs.num_constraints();
		assert_eq!(nat.t.enc.len(), 34);
		assert!(n >= 3958 && n <= 6596,
			"cost drift: {} cs vs calibrated 5277", n);
	}

	/// CIRCUIT CORNERS: (a) EMPTY-L chunk (carried-only): the BP
	/// cascade prunes a6 {73,79} against default_min, a2..a5 chain
	/// re-certifies, all b_l=0 and the degenerate merge branch
	/// holds. (b) DUP carried+L (79 re-matched): one row with both
	/// b_l=1 and m_carry_in=1 satisfies both logups.
	#[test]
	fn test_nonaggr_circuit_corners() {
		let info = a18_store();
		//(a) empty L
		let (cs, nat) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &HashMap::new(),
			A18_DEFAULT_MIN, None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(cat_rows(&nat, CAT_C), vec![(0, 1), (1, 6),
			(2, 21), (3, 27), (4, 33), (5, 39)]);
		assert_eq!(cat_rows(&nat, CAT_BP), vec![(6, 73), (6, 79)]);
		//(b) duplicate carried + L
		let mut hm = HashMap::new();
		hm.insert(6, vec![79]);
		let (cs2, nat2) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &hm,
			A18_DEFAULT_MIN, None);
		assert!(cs2.is_satisfied().unwrap());
		let t2 = &nat2.t;
		let i79 = (t2.n_pad..t2.enc.len()).find(|&i|
			t2.loc[i] == f(79) && !t2.cat[i].is_zero()).unwrap();
		assert_eq!(t2.nonaggr.b_l[i79], f(1));
		assert_eq!(t2.nonaggr.m_carry_in[i79], f(1));
	}
}

#[cfg(test)]
mod tests_neo_nonaggr_neg {
	use super::*;
	use super::tests_neo_m4::A18_DEFAULT_MIN;
	use super::tests_neo_m5::{a18_store, a18_carried};
	use super::tests_neo_nonaggr::run_core_nonaggr;
	use ark_bn254::Fr;

	fn f(x: u32) -> Fr { Fr::from(x) }

	fn fig14c2_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(2, vec![111]);
		m.insert(5, vec![106]);
		m.insert(6, vec![96, 141]);
		m.insert(7, vec![101, 131]);
		m
	}

	/// run the fig-14 chunk-2 core with `tamper`; expect UNSAT.
	fn expect_unsat(tag: &str,
		tamper: &dyn Fn(&mut NeoCore<Fr>)) {
		let info = a18_store();
		let (cs, _nat) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &fig14c2_hm(),
			A18_DEFAULT_MIN, Some(tamper));
		assert!(!cs.is_satisfied().unwrap(),
			"tamper '{}' still satisfied", tag);
	}

	/// row index of `loc` among real (cat!=0) rows.
	fn row(nat: &NeoCore<Fr>, loc: u32) -> usize {
		let t = &nat.t;
		(t.n_pad..t.enc.len()).find(|&i|
			t.loc[i] == f(loc) && !t.cat[i].is_zero()).unwrap()
	}

	/// regenerate the rank m-tables after a consistent tamper, so
	/// the test pinpoints the intended failing constraint instead
	/// of a trivially stale multiplicity.
	fn regen_mtbls(nat: &mut NeoCore<Fr>) {
		let rid = NeoCore::gen_rid_native(&nat.t);
		let cid = NeoCore::gen_cid_native(&nat.t);
		nat.mtbl_qr = NeoCore::gen_mtbl_qr_nonaggr(&nat.t, &rid,
			&nat.subsig_nat);
		nat.mtbl_qc = NeoCore::gen_mtbl_qc(&nat.t, &cid);
	}

	/// remove row i from every T_qm column (base + nonaggr) and
	/// recompute d_sort + the rank m-tables.
	fn remove_row(nat: &mut NeoCore<Fr>, i: usize) {
		let t = &mut nat.t;
		macro_rules! rm { ($($c:ident),*) => {
			$( t.$c.remove(i); )* } }
		rm!(enc, id, loc, cat, step, subsig, prev_id1, prev_loc1,
			prev_loc2, pat, rg1, rg2, enc_prev, b_bwd, d_c1, d_c2,
			d_below_lo, d_below_hi, d_above_lo, d_above_hi, d_sort,
			si_step, si_subsig, si_pat, si_rg1, si_rg2,
			si_enc_prev, si_b_bwd);
		let na = &mut t.nonaggr;
		macro_rules! rmna { ($($c:ident),*) => {
			$( na.$c.remove(i); )* } }
		rmna!(b_l, enc_next, bp_prev_val, rg2_next, w_next, d_bp,
			fz, enc_fz, fz_step_val, fz_sub_val, w_fz, d_fz, w_sp,
			d_sp, m_carry_in, si_bp_prev, si_rg2_next, si_fz,
			si_fz_step, si_fz_sub);
		//recompute d_sort (a removed row changes an adjacency) and
		//fix ids within the group (ids stay contiguous).
		let n = t.enc.len();
		for j in 1..n {
			t.d_sort[j] = if t.enc[j] == t.enc[j - 1]
				&& !t.enc[j].is_zero()
				{ t.loc[j] - t.loc[j - 1] - Fr::from(1u32) }
				else { Fr::from(0u32) };
		}
		for j in i..n {
			if t.enc[j] == t.enc[i - 1] && !t.id[j].is_zero() {
				t.id[j] = t.id[j] - Fr::from(1u32);
			}
		}
		regen_mtbls(nat);
	}

	/// N1 CARRY-DROP (the union linchpin): silently omit carried BP
	/// row a6:73 from Q_m. Every cert still verifies (73 was
	/// pruned anyway) and both rank m-tables are regenerated -- the
	/// ONLY thing that catches the drop is the carry-in logup: the
	/// committed q_i row (enc6, 73) finds no Q_m row to land on.
	/// This is what forces every carried row to be merged and
	/// classified rather than quietly discarded.
	#[test]
	fn test_nonaggr_neg_carry_drop() {
		expect_unsat("carry drop", &|nat| {
			let i = row(nat, 73);
			remove_row(nat, i);
		});
	}

	/// N2 CARRY-OUT FORGERY, both directions. (a) omit C row 21
	/// from the committed q_c: its forced m=1 pole is unmatched.
	/// (b) smuggle BP row 73 into a q_c pad slot: the query hits no
	/// C-selected target row. Together = q_c is EXACTLY sigma_C.
	#[test]
	fn test_nonaggr_neg_carry_out() {
		expect_unsat("qc omit C row", &|nat| {
			let j = (0..nat.qc_loc.len()).find(|&j|
				nat.qc_loc[j] == f(21)).unwrap();
			nat.qc_enc[j] = f(0);
			nat.qc_loc[j] = f(0);
		});
		expect_unsat("qc smuggle BP row", &|nat| {
			let i = row(nat, 73);
			let (e, l) = (nat.t.enc[i], nat.t.loc[i]);
			assert!(nat.qc_enc[0].is_zero()); //front pad slot
			nat.qc_enc[0] = e;
			nat.qc_loc[0] = l;
		});
	}

	/// N3 b_l LIES, both directions. (a) on a carried-only row
	/// (73): the counting query (pat6, 73) is not an L row. (b) off
	/// on a real L row (96): that row's cnt(pat)=1 demand comes up
	/// short against its forced m_aux.
	#[test]
	fn test_nonaggr_neg_b_l() {
		expect_unsat("b_l on carried-only row", &|nat| {
			let i = row(nat, 73);
			nat.t.nonaggr.b_l[i] = f(1);
		});
		expect_unsat("b_l off on L row", &|nat| {
			let i = row(nat, 96);
			nat.t.nonaggr.b_l[i] = f(0);
		});
	}

	/// N4 FALSE BP MIN: BP row 96 claims min_7 = 150 (consistent
	/// d_bp = 150-96-9-1 = 44), but step 7 carries nothing -- its
	/// cid-1 row is the max-wrap, so (enc7, 1, 150) has no target.
	/// Blocks inflating an empty successor into a fake threshold.
	#[test]
	fn test_nonaggr_neg_bp_min() {
		expect_unsat("bp fake w_next", &|nat| {
			let i = row(nat, 96);
			nat.t.nonaggr.w_next[i] = f(150);
			nat.t.nonaggr.d_bp[i] = f(44);
			regen_mtbls(nat);
		});
	}

	/// N5 C-PRED 0-WRAP BAN: C row 21 (rg {0,inf} from a1) cites
	/// the step-1 0-wrap as predecessor with a CONSISTENT window
	/// (gap 21-0=21, d_c1=21, d_c2=inf-21) and a regenerated
	/// mtbl_qc -- the lookup itself would pass (wraps are QC
	/// targets). Only the prev_loc1!=0 pin rejects it; without the
	/// pin a fabricated 0-predecessor would break the C-prefix
	/// contiguity the SP freeze rests on.
	#[test]
	fn test_nonaggr_neg_c_pred_wrap() {
		expect_unsat("c pred = 0-wrap", &|nat| {
			let mx = f((1u32 <<
				read_global_config().range2_bit) - 1);
			let i = row(nat, 21);
			nat.t.prev_id1[i] = f(0);
			nat.t.prev_loc1[i] = f(0);
			nat.t.d_c1[i] = f(21);
			nat.t.d_c2[i] = mx - f(21);
			regen_mtbls(nat);
		});
	}

	/// N6 SP MIN-DOM FORGERY: SP row 111 claims kept min 105
	/// (consistent d_sp=5); the real cid-1 row of its group is 21,
	/// so (enc2, 1, 105) has no target. The prover cannot invent a
	/// closer "kept" location to justify a drop.
	#[test]
	fn test_nonaggr_neg_sp_min() {
		expect_unsat("sp fake w_sp", &|nat| {
			let i = row(nat, 111);
			nat.t.nonaggr.w_sp[i] = f(105);
			nat.t.nonaggr.d_sp[i] = f(5);
			regen_mtbls(nat);
		});
	}

	/// N7 FAKE FREEZE: SP row 111 claims a5 carries loc 150
	/// (consistent d_fz); the a5 group's cid-1 row is 39, so
	/// (enc5, 1, 150) has no target. Freezing needs the downstream
	/// singleton REALLY carrying.
	#[test]
	fn test_nonaggr_neg_fake_freeze() {
		expect_unsat("sp fake w_fz", &|nat| {
			let mx = f((1u32 <<
				read_global_config().range2_bit) - 1);
			let i = row(nat, 111);
			nat.t.nonaggr.w_fz[i] = f(150);
			nat.t.nonaggr.d_fz[i] = mx - f(151);
			regen_mtbls(nat);
		});
	}

	/// N8 SEED CAT: tagging the seed row SP would drop the anchor
	/// from q_c; the seed-stays-C pin (section 5b) rejects it.
	#[test]
	fn test_nonaggr_neg_seed_cat() {
		expect_unsat("seed tagged SP", &|nat| {
			let t = &mut nat.t;
			let i = (t.n_pad..t.enc.len()).find(|&i|
				t.step[i].is_zero() && t.cat[i] == f(CAT_C))
				.unwrap();
			t.cat[i] = f(CAT_SP);
			regen_mtbls(nat);
		});
	}

	/// N9 MTBL FORGERY: bumping one mtbl_qc entry unbalances the
	/// fused QC logup (multiplicities are checked, not advice).
	#[test]
	fn test_nonaggr_neg_mtbl_qc() {
		expect_unsat("mtbl_qc +1", &|nat| {
			let i = row(nat, 21);
			nat.mtbl_qc[i] = nat.mtbl_qc[i] + f(1);
		});
	}
}

#[cfg(test)]
mod tests_neo_nonaggr_oracle {
	use super::*;
	use super::tests_neo_m5::{a18_store, mk_pat_loc};
	use super::tests_neo_m4::fixture_capacity;
	use ark_bn254::Fr;
	use data_processor::type_def::SubsigStepStore;

	fn f(x: u32) -> Fr { Fr::from(x) }

	fn lcg(s: &mut u64) -> u64 {
		*s = s.wrapping_mul(6364136223846793005)
			.wrapping_add(1442695040888963407);
		*s >> 33
	}

	fn seed_only_queue() -> StepQueue<Fr> {
		let items = vec![StepQueueItem::new(f(1), f(0), f(0),
			f(0), f(0), vec![f(1)])];
		let mut m = HashMap::new();
		m.insert(f(1), items);
		let mut cap = fixture_capacity();
		cap.avg_active_pats_per_subsig = 64;
		StepQueue::new(vec![f(1)], m, &cap,
			StepQueueType::ResSmall, false)
	}

	/// returns (forward pre-prune set, pruned carry).
	fn legacy_chunk(carried: &StepQueue<Fr>,
		pl: &HashMap<u32, Vec<u32>>, info: &SubsigStepStore,
		dmin: u32) -> (StepQueue<Fr>, StepQueue<Fr>) {
		let ct = mk_pat_loc(pl);
		let (_ta, fwd, _fp) = carried.gen_forward_prf(&ct, info);
		let (_td, res, _bp) = fwd.gen_backward_prf(f(dmin), info);
		(fwd, res)
	}

	fn neo_chunk(carried: &StepQueue<Fr>,
		pl: &HashMap<u32, Vec<u32>>, info: &SubsigStepStore,
		dmin: u32) -> StepQueue<Fr> {
		let ct = mk_pat_loc(pl);
		let mut g = StepQueueNeo::from_stepqueue(carried.clone())
			.gen_shared_core_advice(0, &ct, info, f(dmin))
			.expect("neo core");
		g.apply_sp_pass(info);
		g.carry_only()
	}

	/// per-step loc sets of subsig 1 (steps 1..=8).
	fn locs_by_step(q: &StepQueue<Fr>) -> Vec<Vec<u64>> {
		let mut v = vec![vec![]; 9];
		if let Some(items) = q.store_items.get(&f(1)) {
			for it in items {
				let s = field_to_usize(&it.step);
				if s == 0 { continue; }
				for l in &it.locs {
					v[s].push(field_to_usize(l) as u64);
				}
			}
		}
		for s in v.iter_mut() { s.sort(); }
		v
	}

	/// DECISION ORACLE (the user-agreed criterion once SP diverges
	/// from the legacy carried set): per chunk,
	///  (1) neo carry SUBSET-OF the legacy FORWARD (pre-prune) set:
	///      neo never invents a location. Post-prune subset does
	///      NOT hold -- the legacy walk's break-on-first-empty is
	///      input-dependent, so on diverged carries neo may
	///      conservatively KEEP a row legacy pruned (sound: keeping
	///      is always safe);
	///  (2) SINGLETON steps (fz=0: a1, a5, and the terminal a8)
	///      agree on emptiness and on the MIN loc -- the dominating
	///      location the theorem preserves;
	///  (3) terminal-step presence (the discharge decision) equal.
	/// Intermediate tracked steps may legitimately differ: a chain
	/// through an SP-dropped parent is subsumed via the frozen
	/// step's kept min (paper C.1 correctness), so no raw set
	/// equality is asserted there.
	#[test]
	fn test_nonaggr_oracle_decision() {
		let info = a18_store();
		let singleton_steps = [1usize, 5, 8];
		let rand_pl = |s: &mut u64, lo: u32| {
			let mut pl: HashMap<u32, Vec<u32>> = HashMap::new();
			for p in 1u32..=8 {
				let cnt = (lcg(s) % 4) as usize;
				let mut v: Vec<u32> = (0..cnt).map(|_|
					lo + (lcg(s) % 80) as u32).collect();
				v.sort(); v.dedup();
				if !v.is_empty() { pl.insert(p, v); }
			}
			pl
		};
		for seed0 in 0u64..20 {
			let mut s = seed0
				.wrapping_mul(0x9E3779B97F4A7C15)
				.wrapping_add(1);
			let pl1 = rand_pl(&mut s, 1);
			let pl2 = rand_pl(&mut s, 81);
			let (fw1, leg1) = legacy_chunk(&seed_only_queue(),
				&pl1, &info, 81);
			let (fw2, leg2) = legacy_chunk(&leg1, &pl2, &info,
				161);
			let neo1 = neo_chunk(&seed_only_queue(), &pl1,
				&info, 81);
			let neo2 = neo_chunk(&neo1, &pl2, &info, 161);
			for (k, (fw, leg, neo)) in
				[(1, (&fw1, &leg1, &neo1)),
				 (2, (&fw2, &leg2, &neo2))] {
				let fv = locs_by_step(fw);
				let lv = locs_by_step(leg);
				let nv = locs_by_step(neo);
				for st in 1..=8usize {
					//(1) subset vs the pre-prune forward set
					for l in &nv[st] {
						assert!(fv[st].contains(l),
							"seed {} chunk {} step {}: neo loc {} \
							not in legacy fwd", seed0, k, st, l);
					}
					//(2) singleton emptiness + min equality
					if singleton_steps.contains(&st) {
						assert_eq!(lv[st].is_empty(),
							nv[st].is_empty(),
							"seed {} chunk {} singleton step {} \
							emptiness", seed0, k, st);
						if !lv[st].is_empty() {
							assert_eq!(lv[st][0], nv[st][0],
								"seed {} chunk {} singleton \
								step {} min", seed0, k, st);
						}
					}
				}
				//(3) decision: terminal presence equal
				assert_eq!(lv[8].is_empty(), nv[8].is_empty(),
					"seed {} chunk {} terminal", seed0, k);
			}
		}
	}
}

#[cfg(test)]
mod tests_neo_nonaggr_h {
	use super::*;
	use ark_bn254::Fr;
	use crate::gadgets::word_extract::{LEGS,
		tests_word_extract_gadget::test_gadget_adv};
	use crate::gadgets::fsm_adv::{FsmAdvAdvice, FsmAdvCapacity};
	use crate::gadgets::word_extract_adv::WordExtractAdvAdvice;
	use folding_schemes::folding::foldpot::container_config::ContainerConfig;
	use data_processor::clam_db::ClamavDB;
	use data_processor::clamav::{default_clamav_cfg,
		quick_discharge_file_by_crit_bag_pm};
	use utils::data::{pack_nibbles, pad_word_to_multiple};
	use utils::os::{read_nibbles, proj_root, write_to_file};

	/// NON-AGGRESSIVE end-to-end through the REAL harness
	/// (word_extract -> fsm_adv -> neo discharge) with the si
	/// columns and outer DB lookups live, over MULTIPLE cycles so a
	/// carried queue (q_i/q_c) actually crosses fold steps. Mirrors
	/// discharge_test_case's loop but swaps in DischargeAdvNeoAdvice
	/// (non-aggressive arm) + DischargeAdvNeoGadget. Each cycle's
	/// circuit is checked for satisfiability with the honest carry
	/// threaded in (oup_queue -> next inp_steps_queue); this
	/// exercises the C.1 certificates + the q_i/q_c transport under
	/// real lookups. `sig_to_discharge` must fall through CP to SED.
	fn neo_nonaggr_e2e(word_dir: &str, db: &ClamavDB<Fr>,
		file_content: &str, sig_to_discharge: &str) {
		let b_igc = false;
		let cfg = default_clamav_cfg();
		let wlen = 2usize;
		let path = format!("{}/data/{}/word.txt", proj_root(),
			word_dir);
		write_to_file(&path, file_content);
		let nibbles_raw = read_nibbles(&path);
		let f_nibbles: Vec<Fr> = nibbles_raw.iter()
			.map(|x| Fr::from(*x as u32)).collect();
		let wi = quick_discharge_file_by_crit_bag_pm("word.txt",
			&nibbles_raw, &db.vec_sigs,
			&db.vec_sigs_no_critical_pat, &db.map_crit_pat,
			&db.map_crit_pat_igc, &db.dfa_crit,
			&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
			&db.sig_to_id, wlen, wlen).1;
		let infos = wi.vec_sed_sigs_info.iter()
			.filter(|i| i.sig_name == sig_to_discharge)
			.cloned().collect::<Vec<_>>();
		assert_eq!(infos.len(), 1, "sig {} not in SED list",
			sig_to_discharge);
		let info = infos[0].clone();
		let bundle = &db.bundle_subsig;
		let acdfa = &bundle.vec_acdfa[0];
		let sig_id = *db.sig_to_id.get(sig_to_discharge).unwrap();
		let input_subsigs: Vec<Fr> = info.subsig_ids.iter()
			.map(|i| Fr::from(
				acdfa.gen_subsig_id(sig_id, *i + 1) as u32))
			.collect();
		let fsm_id = ClamavDB::<Fr>::pm_acdfa_id(0, b_igc);
		let steps_store = &bundle.vec_subsig_step_stores[0];
		let (nibble_len, sbits) = (wlen * LEGS,
			acdfa.state_part_bits);
		let cap = FsmAdvCapacity { max_nibble_len: nibble_len,
			acdfa_state_part_bits: sbits, subsigs: 4,
			avg_pats_per_subsig: 4, basis_pats_in_trace: 25 * 100,
			basis_unique_states: 20 * 100,
			basis_acc_states: 15 * 100, halo_nibbles: 0 };
		let cap_disc = DischargeAdvCapacity {
			max_nibble_len: nibble_len, subsigs: cap.subsigs,
			universe_subsigs: cap.subsigs,
			avg_active_pats_per_subsig: 1,
			basis_pats_in_trace: cap.basis_pats_in_trace,
			// M8b: universe-seed carries all non-empty-chain subsigs
			// every chunk, so the queue budget must cover them (was 100).
			perc_pats_expansion_rate: 200, b_aggressive: false,
				wrap_keys: 0,
			prod_pats_expansion: 0 };
		let all_word = pad_word_to_multiple::<Fr>(
			&pack_nibbles(&f_nibbles), wlen);
		let n_cycles = all_word.len() / wlen;
		assert!(n_cycles >= 2, "want a multi-cycle carry");
		let mut inp_state = Fr::from((acdfa.init_state + 1) as u32);
		let mut inp_loc = Fr::from(1u32);
		let mut inp_sq = DischargeAdvAdvice::
			gen_empty_steps_queue_serialized(b_igc, &input_subsigs,
			steps_store, fsm_id, &cap_disc);
		for i in 0..n_cycles {
			let word = all_word[wlen * i..wlen * (i + 1)].to_vec();
			let adv_wea = WordExtractAdvAdvice::new(&word,
				word.len(), false).expect("wea");
			let stmt_wea = adv_wea.stmt_container;
			let cfg_wea = stmt_wea.lock().unwrap().get_cfg();
			let nibbles = stmt_wea.lock().unwrap()
				.get_container("nibbles").unwrap()
				.lock().unwrap().to_vec();
			let adv_faa = FsmAdvAdvice::new(b_igc, 1, &nibbles, &[],
				&acdfa, inp_state, inp_loc, &input_subsigs, &cap,
				fsm_id, &bundle.vec_subsig_stores[0], 0)
				.expect("faa");
			let stmt_faa = adv_faa.stmt_container;
			let cfg_faa = stmt_faa.lock().unwrap().get_cfg();
			let pat_loc = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs packed_trace pat_loc sorted_tbl")
				.unwrap();
			let locs = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs fsm_acc locs").unwrap()
				.lock().unwrap().to_vec();
			let last_loc = locs[locs.len() - 1];
			let adv_disc = DischargeAdvNeoAdvice::new(b_igc, 1,
				&pat_loc, &input_subsigs, fsm_id, steps_store,
				&cap_disc, &inp_sq, last_loc, i, 0)
				.expect("neo nonaggr adv");
			let oup_queue = adv_disc.get_output_steps_queue();
			let stmt_disc = adv_disc.stmt_container;
			let cfg_disc = stmt_disc.lock().unwrap().get_cfg();
			let mut vec_cfg = vec![cfg_wea.clone(), cfg_faa.clone(),
				cfg_disc];
			ContainerConfig::adjust_locations(&mut vec_cfg);
			let cps1 = stmt_wea.lock().unwrap().gen_stmt_components();
			let cps2 = stmt_faa.lock().unwrap().gen_stmt_components();
			let cps3 = stmt_disc.lock().unwrap()
				.gen_stmt_components();
			let cps = cps1.0.into_iter().zip(cps2.0.into_iter())
				.map(|(a, b)| vec![a, b].concat())
				.collect::<Vec<Vec<Fr>>>();
			let cps = cps.into_iter().zip(cps3.0.into_iter())
				.map(|(a, b)| vec![a, b].concat())
				.collect::<Vec<Vec<Fr>>>();
			let mut dcg = DischargeAdvNeoGadget::<Fr>::new(b_igc, 1,
				&cap_disc, fsm_id,
				&vec![cfg_wea.clone(), cfg_faa.clone()],
				&bundle.vec_subsig_step_stores[0]);
			dcg.set_container_cfg(vec_cfg.clone().into(), 2);
			let rg = Arc::new(dcg);
			test_gadget_adv::<Fr>(rg, &word, &cps[0], &cps[1],
				&cps[2], &cps[6], &cps[7],
				&vec![cps[3].clone(), cps[4].clone(),
					cps[5].clone()].concat(), 4usize, false,
				Some(vec_cfg));
			let states = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs fsm_acc states").unwrap()
				.lock().unwrap().to_vec();
			inp_state = states[states.len() - 1];
			inp_loc = locs[locs.len() - 1];
			inp_sq = StepQueue::parse_from(&oup_queue,
				StepQueueType::ResSmall, &cap_disc, b_igc);
		}
	}

	/// H1 (non-aggr, user-required): a SED sig discharged across
	/// cycles. sig2's 3rd pattern is absent, so the partial match
	/// carries forward and never completes; the neo non-aggressive
	/// circuit (C/FP/BP/SP certs + q_i/q_c carry) stays satisfiable
	/// with the honest carry, and the outer DB lookups (fz, prev,
	/// rg_end, subsig) all resolve.
	#[test]
	fn test_nonaggr_h1_e2e() {
		let sigs = vec![
			"sig2;Engine:51-255,Target:0;0&1;/def.*234.*567/;/234....def/",
			"sig1;Engine:51-255,Target:0;0&1;/abc..123/;/123....abc/",
		].iter().map(|x| x.to_string()).collect::<Vec<String>>();
		let dir = "debug/sed/neononaggrh1";
		let p = format!("{}/data/{}", proj_root(), dir);
		std::fs::create_dir_all(&p).unwrap();
		let cfg = default_clamav_cfg();
		let db = ClamavDB::<Fr>::build_test_db(&cfg, dir, &sigs,
			&vec![], &vec![], &vec![]).expect("db");
		//long enough to span >=2 cycles; 234 present, 567 absent.
		neo_nonaggr_e2e(dir,
			&db, &format!("def{}234xx56", "x".repeat(90)),
			"sig2");
	}

	/// Per-subsig discharged set from an output queue: discharged iff
	/// last step reached < chain length (compute_sig_adv:460-468 rule).
	/// Same decode for neo q_c and legacy sq_res2 (identical format).
	fn discharged_set(oup: &Vec<Fr>, input_subsigs: &[Fr],
		steps: &data_processor::type_def::SubsigStepStore,
		cap: &DischargeAdvCapacity, b_igc: bool)
		-> std::collections::BTreeSet<usize> {
		let sq = StepQueue::parse_from(oup,
			StepQueueType::ResSmall, cap, b_igc);
		let mut out = std::collections::BTreeSet::new();
		for s in input_subsigs {
			let u = field_to_usize(s);
			let max_step = steps.subsig_to_steps.get(&u)
				.map_or(0, |it| it.vec_pm_bounds.len());
			if max_step == 0 { continue; } //empty-chain: not in universe
			let last = sq.store_items.get(s).map_or(0, |items|
				items.iter().map(|it| field_to_usize(&it.step))
					.max().unwrap_or(0));
			if last < max_step { out.insert(u); }
		}
		out
	}

	/// M8b ground-truth parity: run neo + legacy discharge chains on the
	/// SAME per-cycle input; both final verdicts must equal the non-ZK
	/// ground truth (this fixture discharges every subsig of the sig).
	fn neo_legacy_verdict_parity(word_dir: &str, db: &ClamavDB<Fr>,
		file_content: &str, sig_to_discharge: &str) {
		let b_igc = false;
		let cfg = default_clamav_cfg();
		let wlen = 2usize;
		let path = format!("{}/data/{}/word.txt", proj_root(),
			word_dir);
		write_to_file(&path, file_content);
		let nibbles_raw = read_nibbles(&path);
		let f_nibbles: Vec<Fr> = nibbles_raw.iter()
			.map(|x| Fr::from(*x as u32)).collect();
		let wi = quick_discharge_file_by_crit_bag_pm("word.txt",
			&nibbles_raw, &db.vec_sigs,
			&db.vec_sigs_no_critical_pat, &db.map_crit_pat,
			&db.map_crit_pat_igc, &db.dfa_crit,
			&db.bundle_subsig.vec_acdfa[0], &db.dfa_crit_igc,
			&db.bundle_subsig_igc.vec_acdfa[0], true, &cfg,
			&db.sig_to_id, wlen, wlen).1;
		let infos = wi.vec_sed_sigs_info.iter()
			.filter(|i| i.sig_name == sig_to_discharge)
			.cloned().collect::<Vec<_>>();
		assert_eq!(infos.len(), 1, "sig {} not SED-discharged",
			sig_to_discharge);
		let info = infos[0].clone();
		let bundle = &db.bundle_subsig;
		let acdfa = &bundle.vec_acdfa[0];
		let sig_id = *db.sig_to_id.get(sig_to_discharge).unwrap();
		let input_subsigs: Vec<Fr> = info.subsig_ids.iter()
			.map(|i| Fr::from(
				acdfa.gen_subsig_id(sig_id, *i + 1) as u32))
			.collect();
		let fsm_id = ClamavDB::<Fr>::pm_acdfa_id(0, b_igc);
		let steps_store = &bundle.vec_subsig_step_stores[0];
		let (nibble_len, sbits) = (wlen * LEGS,
			acdfa.state_part_bits);
		let cap = FsmAdvCapacity { max_nibble_len: nibble_len,
			acdfa_state_part_bits: sbits, subsigs: 4,
			avg_pats_per_subsig: 4, basis_pats_in_trace: 25 * 100,
			basis_unique_states: 20 * 100,
			basis_acc_states: 15 * 100, halo_nibbles: 0 };
		let cap_disc = DischargeAdvCapacity {
			max_nibble_len: nibble_len, subsigs: cap.subsigs,
			universe_subsigs: cap.subsigs,
			avg_active_pats_per_subsig: 1,
			basis_pats_in_trace: cap.basis_pats_in_trace,
			perc_pats_expansion_rate: 200, b_aggressive: false,
				wrap_keys: 0,
			prod_pats_expansion: 0 };
		let all_word = pad_word_to_multiple::<Fr>(
			&pack_nibbles(&f_nibbles), wlen);
		let n_cycles = all_word.len() / wlen;
		assert!(n_cycles >= 2, "want a multi-cycle carry");
		let mut inp_state = Fr::from((acdfa.init_state + 1) as u32);
		let mut inp_loc = Fr::from(1u32);
		let seed = || DischargeAdvAdvice::
			gen_empty_steps_queue_serialized(b_igc, &input_subsigs,
			steps_store, fsm_id, &cap_disc);
		let mut inp_sq_neo = seed();
		let mut inp_sq_leg = seed();
		let (mut oup_neo, mut oup_leg) = (vec![], vec![]);
		for i in 0..n_cycles {
			let word = all_word[wlen * i..wlen * (i + 1)].to_vec();
			let adv_wea = WordExtractAdvAdvice::new(&word,
				word.len(), false).expect("wea");
			let nibbles = adv_wea.stmt_container.lock().unwrap()
				.get_container("nibbles").unwrap()
				.lock().unwrap().to_vec();
			let adv_faa = FsmAdvAdvice::new(b_igc, 1, &nibbles, &[],
				&acdfa, inp_state, inp_loc, &input_subsigs, &cap,
				fsm_id, &bundle.vec_subsig_stores[0], 0)
				.expect("faa");
			let stmt_faa = adv_faa.stmt_container;
			let pat_loc = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs packed_trace pat_loc sorted_tbl")
				.unwrap();
			let locs = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs fsm_acc locs").unwrap()
				.lock().unwrap().to_vec();
			let last_loc = locs[locs.len() - 1];
			let adv_neo = DischargeAdvNeoAdvice::new(b_igc, 1,
				&pat_loc, &input_subsigs, fsm_id, steps_store,
				&cap_disc, &inp_sq_neo, last_loc, i, 0)
				.expect("neo adv");
			oup_neo = adv_neo.get_output_steps_queue();
			let adv_leg = DischargeAdvAdvice::new(b_igc, 1,
				&pat_loc, &input_subsigs, fsm_id, steps_store,
				&cap_disc, &inp_sq_leg, last_loc, i, 0)
				.expect("legacy adv");
			oup_leg = adv_leg.get_output_steps_queue();
			let states = stmt_faa.lock().unwrap().search_container(
				"fsm_adv_stmt_cs fsm_acc states").unwrap()
				.lock().unwrap().to_vec();
			inp_state = states[states.len() - 1];
			inp_loc = last_loc;
			inp_sq_neo = StepQueue::parse_from(&oup_neo,
				StepQueueType::ResSmall, &cap_disc, b_igc);
			inp_sq_leg = StepQueue::parse_from(&oup_leg,
				StepQueueType::ResSmall, &cap_disc, b_igc);
		}
		let v_neo = discharged_set(&oup_neo, &input_subsigs,
			steps_store, &cap_disc, b_igc);
		let v_leg = discharged_set(&oup_leg, &input_subsigs,
			steps_store, &cap_disc, b_igc);
		//ground truth: sig SED-discharged => every non-empty-chain
		//subsig of it is discharged (holds for this all-fail fixture).
		let gt: std::collections::BTreeSet<usize> = input_subsigs
			.iter().map(field_to_usize)
			.filter(|u| steps_store.subsig_to_steps.get(u)
				.map_or(false, |it| !it.vec_pm_bounds.is_empty()))
			.collect();
		assert_eq!(v_neo, v_leg, "neo verdict != legacy verdict");
		assert_eq!(v_neo, gt, "neo verdict != ground truth");
		assert_eq!(v_leg, gt, "legacy verdict != ground truth");
		assert!(!gt.is_empty(), "fixture must discharge >=1 subsig");
	}

	/// M8b: neo non-aggr discharge verdict == legacy == non-ZK ground
	/// truth on the H1 no-match fixture (sig2, 567/def-after absent).
	#[test]
	fn test_nonaggr_verdict_parity() {
		let sigs = vec![
			"sig2;Engine:51-255,Target:0;0&1;/def.*234.*567/;/234....def/",
			"sig1;Engine:51-255,Target:0;0&1;/abc..123/;/123....abc/",
		].iter().map(|x| x.to_string()).collect::<Vec<String>>();
		let dir = "debug/sed/neononaggr_parity";
		let p = format!("{}/data/{}", proj_root(), dir);
		std::fs::create_dir_all(&p).unwrap();
		let cfg = default_clamav_cfg();
		let db = ClamavDB::<Fr>::build_test_db(&cfg, dir, &sigs,
			&vec![], &vec![], &vec![]).expect("db");
		neo_legacy_verdict_parity(dir,
			&db, &format!("def{}234xx56", "x".repeat(90)),
			"sig2");
	}
}

// THROWAWAY (M8 measurement): neo-vs-legacy discharge circuit cost on a
// hard non-aggressive scenario. Delete once numbers are captured; the
// official scalability collection is M12. The scenario mirrors the
// data/debug/neo_hard_set sed_hard sig (an nu-step tracked chain) as an
// in-code SubsigStepStore + carried queue + L, so both gadgets can be
// measured without running the DB/fold pipeline.
#[cfg(test)]
mod tests_neo_cost {
	use super::*;
	use ark_bn254::Fr;
	use super::tests_neo_nonaggr::run_core_nonaggr;
	use data_processor::type_def::{SubsigStepStore,
		SubsigStepStoreItem};

	fn f(x: u32) -> Fr { Fr::from(x) }

	// DischargeAdvCapacity sized so T_qm holds n rows (subsigs=1 =>
	// avg_active_pats_per_subsig is the per-subsig row budget).
	fn hard_capacity(cap_n: usize) -> DischargeAdvCapacity {
		DischargeAdvCapacity {
			max_nibble_len: 1, subsigs: 1,
			avg_active_pats_per_subsig: cap_n, basis_pats_in_trace: 1,
			perc_pats_expansion_rate: 100, universe_subsigs: 1,
			b_aggressive: false, prod_pats_expansion: 0,
			wrap_keys: 0,
		}
	}

	// nu-step chain, every step range (1, w) finite (terminal step is a
	// singleton regardless); one subsig id=1.
	fn hard_store(nu: u32, w: u32) -> SubsigStepStore {
		let pm = (1..=nu).map(|i| (i as usize,
			(1usize, w as usize))).collect::<Vec<_>>();
		let item = SubsigStepStoreItem { subsig_id: 1, igc: false,
			vec_pm_bounds: pm, is_backward: false };
		let mut m = std::collections::HashMap::new();
		m.insert(1usize, item);
		SubsigStepStore { subsig_ids: vec![1], subsig_to_steps: m,
			b_aggressive: false }
	}

	// step i (1-indexed) gets `dens` locations [i*s .. i*s+dens), which
	// chain in-range (diffs in [s-dens+1, s+dens-1] subset [1,w]).
	fn step_locs(i: u32, dens: u32, s: u32) -> Vec<u32> {
		(0..dens).map(|k| i * s + k).collect()
	}

	// carried Q_i: seed step0=loc1, steps 1..=nu-1 each `dens` dense
	// chained locations.
	fn hard_carried(nu: u32, dens: u32, s: u32, w: u32,
		cap_n: usize) -> StepQueue<Fr> {
		let mut items = vec![StepQueueItem::new(f(1), f(0), f(0),
			f(0), f(0), vec![f(1)])];
		for i in 1..=(nu - 1) {
			let locs = step_locs(i, dens, s).into_iter().map(f)
				.collect::<Vec<Fr>>();
			items.push(StepQueueItem::new(f(1), f(i), f(i), f(1),
				f(w), locs));
		}
		let mut m = HashMap::new();
		m.insert(f(1), items);
		StepQueue::new(vec![f(1)], m, &hard_capacity(cap_n),
			StepQueueType::ResLarge, false)
	}

	// L = this chunk's raw matches: `dens` dense locations at the
	// terminal step nu (they chain from carried step nu-1 => carry).
	fn hard_hm(nu: u32, dens: u32, s: u32) -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(nu, step_locs(nu, dens, s));
		m
	}

	/// Measure the NEO non-aggressive core cost at a hard scenario.
	/// Adjust nu/dens/s/w/cap_n by hand; read cs + Q_m rows.
	#[test]
	fn neo_cost_probe() {
		let nu = 8u32;
		let dens = 32u32;
		let s = 40u32;
		let w = 200u32;
		let cap_n = 320usize;
		let dmin = nu * s + dens + 100;

		let info = hard_store(nu, w);
		let carried = hard_carried(nu, dens, s, w, cap_n);
		let hm = hard_hm(nu, dens, s);
		let (cs, nat) = run_core_nonaggr(&info, &carried, &hm,
			dmin, None);
		assert!(cs.is_satisfied().unwrap(), "unsat: {:?}",
			cs.which_is_unsatisfied());
		println!("NEO-COST: Q_m rows={} cs={}",
			nat.t.enc.len(), cs.num_constraints());
	}
}
