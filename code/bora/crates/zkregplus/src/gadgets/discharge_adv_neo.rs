// discharge_adv_neo.rs
// Created 2026-07-19.
// Design by the BORA paper author. Code implemented by Claude Opus.
// Code reviewed by the paper author and unit tested.
//
// M3 coexistence stub for the Appendix G.1 constant-queue SDE. This
// stub delegates every SigmaGadget method to DischargeAdvGadget, so the
// neo path is byte-identical to the legacy SDE. The real G.1
// certificates (C/FP/BP/SP over StepQueueNeo) replace the body in M4-M7.

// ============================================================
//  Q_m row-class + lookup-target legend (shared vocabulary)
// ============================================================
// Every T_qm (Q_m) row is exactly one CLASS:
//   pad = enc==0 filler (table tail).
//   0w  = lower wrap sentinel of a group (id 0, loc 0).
//   Mw  = upper wrap sentinel of a group (loc MAX).
//   C   = reachable match, kept (valid predecessor, reaches on).
//   FP  = unreachable match, forward-pruned (no predecessor in
//         the [rg1,rg2] window).
//   BP  = reachable but back-pruned: scan outran it (successor
//         step carries nothing within reach).
//   SP  = reachable but singleton surplus: dominated by a
//         smaller carried loc at a frozen downstream step.
// BP and SP exist ONLY in the non-aggressive arm; the
// aggressive arm retags BP->C and has no SP, so its classes
// are {pad, 0w, C, FP, Mw}.
//
// Two per-chunk LOOKUP TARGETS are carved from Q_m by group:
//   QR = REACHABLE rows: both wraps + C (+ BP,SP non-aggr).
//        Reach cert reads it: C cites a predecessor; FP
//        brackets its window with two rank-adjacent QR rows.
//   QC = CARRIED rows: both wraps + C. Non-aggressive only;
//        the (enc,cid=1,loc) query returns a group's least
//        carried loc (Mw if nothing carries). Aggressive has
//        no QC -- it reseeds each chunk and routes its verdict
//        through failed_acc.
//
// Each target row gets a per-group ORDINAL (0-based address
// within its group, reset at each group start), the middle
// coordinate of the pack(enc, ord, loc) key:
//   rid (QR-id) bumps on every reachable row + both wraps:
//     aggr     0w,C,Mw ;  non-aggr 0w,C,BP,SP,Mw  (FP stalls).
//   cid (QC-id) bumps only on carried rows (non-aggr only):
//     0w,C,Mw  (FP,BP,SP stall -> absent from QC).
// id and id+1 are thus rank-adjacent (the FP bracket).
// EXAMPLE group [0w,21C,55BP,96FP,111SP,Mw]:
//   rid 0,1,2,2,3,4     cid 0,1,1,1,1,2
// ============================================================

use ark_ff::{PrimeField, Zero, Field, batch_inversion};
//DEBUG USE 62070.10: BigInteger::num_bits for the per-column census.
use ark_ff::BigInteger as _;
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
use utils::consts::{read_global_config, B_DEBUG};
use utils::logger::{log, LOG3};
use ark_r1cs_std::R1CSVar;
use folding_schemes::Error;
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget, WitnessSigmaIR1CSVar,
		WitnessSigmaIR1CSConfig, NdAdvice},
	container_config::{ColEle, ContainerConfig},
	circuits_super::field_to_usize,
};
use crate::gadgets::commons::{encode_cols, encode_cols_var,
	is_zero_better_adv, check_eq, check_prod_zero, better_select,
	new_const_var, new_var, gen_m_table_cond, gen_m_table,
	multiset_prod_2col, var_to_lb};
use crate::gadgets::db::{assert_logup, assert_logup_cond,
	assert_well_formed_sorted, gen_union_prf,
	verify_union_prf_vars};
use crate::gadgets::traits::{Container, Col, IDX_DATA, IDX_SI_DATA,
	ComponentAdvice};
use crate::gadgets::discharge_adv::{DischargeAdvGadget,
	DischargeAdvAdvice, DischargeAdvCapacity, FailedSubsigAcc,
	StepQueue, StepQueueItem, StepQueueType, RES_LARGE_COST};

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
		if std::env::var("ZKR_PROBE_COLS").is_ok(){
			let nsub = store_steps.subsig_to_steps.len();
			let need: usize = store_steps.subsig_to_steps.values()
				.map(|it| it.vec_pm_bounds.len() + 1).sum();
			let mx = store_steps.subsig_to_steps.values()
				.map(|it| it.vec_pm_bounds.len()).max().unwrap_or(0);
			println!("DEBUG USE 62050.3: igc={} db_subsigs={} \
maxsteps={} WRAP_KEYS_NEEDED={} have={}",
				b_igc, nsub, mx, need, capacity.wrap_keys);
			crate::gadgets::traits::dump_cfg_col_sizes(
				&inner.dummy_cfg, &format!("neo igc={}", b_igc));
		}
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
		let r1 = wtns.msg2[0].clone();
		let r2 = wtns.msg2[1].clone();
		let job_id = self.inner.get_job_id();
		if self.inner.capacity.b_aggressive {
			let (nat, vars) = self.load_neo_stmt_aggr(i, wtns,
				cfg)?;
			Self::assert_neo_aggr(cs, &nat, &vars, &r1, &r2,
				job_id)
		} else {
			let (nat, vars, default_min) = self
				.load_neo_stmt_nonaggr(i, &cs, wtns, cfg)?;
			Self::assert_neo_nonaggr(cs, &nat, &vars,
				&default_min, &r1, &r2, job_id)
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
				// NO dedup: a carried loc matched again this chunk
				// (halo straddle) keeps BOTH copies, so the union
				// pays one to q_i and one to the join. Cats and
				// certs of the pair are identical; ranks differ.
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
		//PERF 61080: .1 candidate-row DENSITY, .3 busiest-step raw peak
		//(.2 Q_c is logged by the carry consumer in M6). NOT saturation:
		//these are pre-filter {C,FP,BP} rows vs the real-row budget only
		//(no wraps). True T_qm saturation = QM_SAT, see "NEO SAT".
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
			"PERF 61080.1 cand_rows={} real_cap={} dens_pm={}",
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
/// fz=5, enc_fz=enc(step5), w_fz=39 (a5 carries), w_kept=21 (kept
/// min at step 2), d_kept=111-21-1=89.
#[derive(Clone, Debug, PartialEq, Default)]
pub(crate) struct QmNonAggrCols<F: PrimeField + ColEle> {
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
	pub w_kept: Vec<F>,
	/// RANGE2 diff loc - w_kept - 1 (min-domination); underflows
	/// if the prover tries to SP the minimum itself.
	pub d_kept: Vec<F>,
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
	// masked cert diffs: single RANGE2 limbs (chunking keeps
	// loc + rg in range; see assert_fwd_pruning's ASSUMPTION)
	pub d_c1: Vec<F>, pub d_c2: Vec<F>,
	pub d_below_lo: Vec<F>, pub d_above_lo: Vec<F>,
	/// non-strict sort diff advice: loc[i]-loc[i-1] on same-group
	/// adjacencies (RANGE2-si'd), 0 elsewhere; 0 = legal duplicate.
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

/// NONAGGR ONLY -- the materialized JOIN RESULT (temp table,
/// witness-only, never folded across chunks): one block per
/// store row (subsig, step >= 1), holding pat_loc's FULL block
/// for that row's pat -- [loc-0 sentinel, real locs, loc-max
/// sentinel], ids = the pat_loc ranks 0..cnt+1. Pads = all-0
/// rows (prefix by convention; the constraints are
/// position-free). Aggr never builds it: there Q_m itself IS
/// the join result. Shape + membership are verified by
/// assert_join_locations; the rows are linked into Q_m by
/// assert_qm_union over fp = enc||loc (ids stay internal to
/// the join). Built by gen_jr_table.
#[derive(Clone, Debug, PartialEq, Default)]
pub(crate) struct JrTable<F: PrimeField + ColEle> {
	/// owning Q_m group's key (subsig|step|pat|rg1|rg2).
	pub enc: Vec<F>,
	/// that group's pat; bound to enc by the si_pat companion
	/// (else a block could join a foreign pat's locations).
	pub pat: Vec<F>,
	/// pat_loc rank within the block: 0..cnt+1.
	pub id: Vec<F>,
	/// pat_loc loc: 0 sentinel / real locs / max sentinel.
	pub loc: Vec<F>,
	/// tag(enc, PAT) companion for the outer DB lookup: welds
	/// pat = pat(enc) per row (RANGE2 si + val 0 on pads).
	pub si_pat: Vec<F>,
}

/// Chunking-invariant guard: an FP bracket diff must fit ONE
/// RANGE2 cell (chunk length + max window < 2^rb). A violation
/// means the corpus was chunked too coarsely for range2_bit.
fn assert_fp_diff_range2<F: PrimeField + ColEle>(
	d: &F, max_val: usize) {
	assert!(field_to_usize(d) <= max_val,
		"FP bracket diff exceeds RANGE2: chunk too long");
}

impl<F: PrimeField + ColEle> QmTable<F> {
	/// Append one wrap row (loc 0 or max) for group `enc`; cert and
	/// binding cols zeroed with benign si. f_bwd = the subsig's real
	/// backward flag (the (si,val) pair must exist on EVERY row).
	fn push_wrap(&mut self, enc: F, id: F, loc: F, f_step: F,
		subsig: F, pat: F, b_last: bool, b_ge1: bool, f_bwd: F) {
		let (z, rg2t) = (F::zero(), F::from(RANGE2));
		let tag = if b_last { ID_ENCODED_LAST_STEP }
			else { ID_ENCODED_NORMAL_STEP };
		self.enc.push(enc); self.id.push(id); self.loc.push(loc);
		self.cat.push(z); self.step.push(f_step);
		self.subsig.push(subsig); self.b_bwd.push(f_bwd);
		self.pat.push(pat);
		for v in [&mut self.prev_id1, &mut self.prev_loc1,
			&mut self.prev_loc2, &mut self.rg1,
			&mut self.rg2, &mut self.enc_prev, &mut self.d_c1,
			&mut self.d_c2, &mut self.d_below_lo,
			&mut self.d_above_lo] { v.push(z); }
		self.si_step.push(SubsigStepStore::gen_step_tbl_id(enc, tag));
		self.si_subsig.push(if b_ge1 {
			SubsigStepStore::gen_step_tbl_id(enc, ID_ENCODED_SUBSIG)
		} else { rg2t });
		//pat is membership-queried on step>=1 wraps -> DB-bound
		self.si_pat.push(if b_ge1 {
			SubsigStepStore::gen_step_tbl_id(enc, ID_ENCODED_PAT)
		} else { rg2t });
		for v in [&mut self.si_rg1,
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
		// non-aggr never carries backward subsigs; the circuit
		// hard-codes forward formulas on that arm.
		assert!(b_aggr || !bwd,
			"backward subsig in a non-aggressive store");
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
		let (mut dbl, mut dal) = (z, z);
		if !b_seed && b_aggr && cat == F::from(CAT_C) {
			let gap = if bwd { pl1 - loc } else { loc - pl1 };
			dc1 = gap - f_a; dc2 = f_b - gap;
		}
		if cat == F::from(CAT_FP) {
			if !pl1.is_zero() {
				let d = if bwd { loc + f_a - pl1 - one }
					else { loc - pl1 - f_b - one };
				assert_fp_diff_range2(&d, max_val);
				dbl = d;
			}
			if pl2 != f_max {
				let d = if bwd { pl2 - loc - f_b - one }
					else { pl2 + f_a - loc - one };
				assert_fp_diff_range2(&d, max_val);
				dal = d;
			}
		}
		self.d_c1.push(dc1); self.d_c2.push(dc2);
		self.d_below_lo.push(dbl);
		self.d_above_lo.push(dal);
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
			&mut self.d_above_lo, &mut self.d_sort] { pz(v, z); }
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
	/// (run right after gen_qm_table(.., false)). Two jobs:
	///  (1) C rows: RE-PICK the predecessor against the FINAL C
	///      sets and re-rank prev_id1 in QC coordinates. Needed
	///      because apply_sp_pass may demote the closure-time pred:
	///      at a frozen step only the min survives, and the min
	///      always reaches (min-chain lemma), so a C pred exists.
	///      EXAMPLE: a3:27 closure pred was a2:21; had it been 111
	///      (now SP), the re-pick lands on the kept min 21, rank 1.
	///  (2) BP/SP rows: successor/freeze witnesses (see the
	///      QmNonAggrCols field docs for the certificates).
	/// PARAMS: default_min = last_loc + 1 (BP/SP empty-min fallback).
	pub(crate) fn fill_nonaggr(&mut self, info: &SubsigStepStore,
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
			enc_next: vec![z; n],
			bp_prev_val: vec![z; n], rg2_next: vec![z; n],
			w_next: vec![z; n], d_bp: vec![z; n], fz: vec![z; n],
			enc_fz: vec![z; n], fz_step_val: vec![z; n],
			fz_sub_val: vec![z; n], w_fz: vec![z; n],
			d_fz: vec![z; n], w_kept: vec![z; n],
			d_kept: vec![z; n],
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
		//2. per-subsig step metadata (non-aggr = forward-only)
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
		//3. row pass
		for i in self.n_pad..n {
			let cat = self.cat[i];
			if cat.is_zero() { continue; } //wrap sentinel rows
			let (subsig, loc) = (self.subsig[i], self.loc[i]);
			let step = field_to_usize(&self.step[i]);
			if step == 0 { continue; } //seed: no certificate
			let pm = &meta[&subsig];
			//(1) C re-pick: least final-C loc at step-1 inside the
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
			//(2a) BP: successor key + range + carried-min witness
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
			//(2b) SP: freeze (C row at step fz) + min-domination
			if cat == f_sp {
				let max_steps = pm.len();
				let fzv = fz_from_pm_bounds::<F>(pm, max_val)
					[step - 1];
				let fz_us = field_to_usize(&fzv);
				let enc_fz = enc_of[&(subsig, fzv)];
				let w_fz = qc1(&enc_fz);
				let w_kept = qc1(&self.enc[i]);
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
				na.w_kept[i] = w_kept;
				na.d_kept[i] = loc - w_kept - one;
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

	/// Chain lengths (+1 seed group) of the store, sorted
	/// descending: the wrap-key demand per seeded subsig.
	fn chain_keys_desc(info: &SubsigStepStore) -> Vec<usize> {
		let mut v = info.subsig_to_steps.values()
			.map(|it| it.vec_pm_bounds.len() + 1)
			.collect::<Vec<usize>>();
		v.sort_unstable_by(|a, b| b.cmp(a));
		v
	}

	/// Wrap-key budget: explicit capacity.wrap_keys, else the sum
	/// of the capacity.subsigs largest (chain_len+1) in the store
	/// -- the exact worst case for any seeded set of that size.
	pub(crate) fn wrap_budget(capacity: &DischargeAdvCapacity,
		info: &SubsigStepStore) -> usize {
		if capacity.wrap_keys > 0 { return capacity.wrap_keys; }
		Self::chain_keys_desc(info).iter()
			.take(capacity.subsigs).sum()
	}

	/// Invert wrap_budget: the smallest subsig count whose top-K
	/// chain sum covers `demand` keys (CapErr attribution).
	pub(crate) fn wrap_subsigs_for(info: &SubsigStepStore,
		demand: usize) -> usize {
		let (mut acc, mut k) = (0usize, 0usize);
		for l in Self::chain_keys_desc(info) {
			if acc >= demand { break; }
			acc += l; k += 1;
		}
		k.max(1)
	}

	/// T_qm row budget: ResLarge real rows + 2 wraps per budget
	/// key. Capacity-only in BOTH modes -> chunk/fold-invariant
	/// shape (data n_keys ignored).
	pub(crate) fn qm_rows_size(capacity: &DischargeAdvCapacity,
		info: &SubsigStepStore) -> usize {
		let (n, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResLarge, capacity);
		n + 2 * Self::wrap_budget(capacity, info)
	}

	/// Attribute a pooled T_qm overflow to the param over its nominal
	/// share, in that param's own units. total > cap implies at least
	/// one side is over, so the result is never empty.
	pub(crate) fn qm_caperr(capacity: &DischargeAdvCapacity,
		b_igc: bool, info: &SubsigStepStore,
		n_keys: usize, wrap_cap: usize,
		real: usize, real_cap: usize) -> Error {
		let mut v = vec![];
		if n_keys > wrap_cap {
			//derived wrap = top-K chain sum -> bump subsigs to the
			//smallest K covering the demand. "subsigs" in the name
			//routes to p.subsigs (and the aggr_needs_subsigs
			//co-bump) in determine_config.
			v.push((format!("dis_adv::neo_wrap_subsigs, b_igc: {}",
				b_igc), Self::wrap_subsigs_for(info, n_keys)));
		}
		if real > real_cap {
			//invert vec_size's size_trace term for the real rows.
			let d = if capacity.b_aggressive {
				capacity.max_nibble_len * RES_LARGE_COST
			} else { capacity.max_nibble_len
				* capacity.basis_pats_in_trace * RES_LARGE_COST };
			let req = if d == 0 { real }
				else { (real * 100_000_000 + d - 1) / d };
			let nm = if capacity.b_aggressive {
				"dis_adv::prod_pats_expansion"
			} else { "dis_adv::perc_pats_expansion_rate" };
			v.push((format!("{}, b_igc: {}", nm, b_igc), req));
		}
		if v.is_empty() { //defensive: keep the legacy shape
			v.push((format!("neo_qm_table, b_igc: {}", b_igc),
				real + 2 * n_keys));
		}
		Error::CapErr(v)
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
				let f_pat = if s >= 1 {
					F::from(pm[s - 1].0 as u32) } else { zero };
				t.push_wrap(enc, zero, zero, f_step, *subsig,
					f_pat, b_last, b_ge1, f_bwd);
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
					f_step, *subsig, f_pat, b_last, b_ge1, f_bwd);
				enc_prev = enc;
			}
		}
		// sort diff advice, NON-strict (duplicate straddle rows are
		// legal; clones are policed by the union / join instead).
		// Before padding: pads are separate groups and the circuit
		// binding masks pad/key-change rows.
		let nrows = t.enc.len();
		t.d_sort = vec![zero; nrows];
		for i in 1..nrows {
			if t.enc[i] == t.enc[i - 1] {
				t.d_sort[i] = t.loc[i] - t.loc[i - 1];
			}
		}
		// front pads + CapErr (fixed budget)
		let n_keys = Self::n_wrap_keys(&subsigs, info);
		let n_total = Self::qm_rows_size(&self.capacity, info);
		// TRUE T_qm saturation: the two operands CapErr compares. The
		// 61080.1 probe counts pre-filter candidates against the real-row
		// budget alone, so it is a density signal, NOT saturation.
		utils::consts::QM_SAT[self.b_igc as usize]
			.record(t.enc.len(), n_total);
		// SPLIT gauges: QM_SAT cannot separate an oversized wrap
		// budget from oversized real rows, and over-provisioning is
		// silent (only CapErr is loud). See wrap_budget.
		let ig = self.b_igc as usize;
		let (n_real_cap, _, _) = StepQueue::<F>::vec_size(
			&StepQueueType::ResLarge, &self.capacity);
		let wrap_cap = Self::wrap_budget(&self.capacity, info);
		let n_sub = subsigs.iter().filter(|s| !s.is_zero()).count();
		let n_real = t.enc.len().saturating_sub(2 * n_keys);
		utils::consts::QM_WRAP_SAT[ig].record(n_keys, wrap_cap);
		utils::consts::QM_REAL_SAT[ig].record(n_real, n_real_cap);
		utils::consts::QM_SUB_SAT[ig]
			.record(n_sub, self.capacity.subsigs);
		if utils::consts::b_probe_p36() {
			//PER-CHUNK stream: the gauges above fetch_max fill and cap
			//INDEPENDENTLY, so their printed % understates the tightest
			//chunk and cannot show a max-vs-mean spread.
			println!("DEBUG USE 62070.2: qm igc={} rows={}/{} pad={} \
wrap={}/{} real={}/{} sub={}/{}", self.b_igc, t.enc.len(), n_total,
				n_total.saturating_sub(t.enc.len()), n_keys, wrap_cap,
				n_real, n_real_cap, n_sub, self.capacity.subsigs);
			//DEMAND side: why is there anything (or nothing) to do?
			//rows=0 means NO OBLIGATION reached the gadget, which is a
			//fixture/pipeline fact, not an oversized capacity.
			let chains: usize = subsigs.iter()
				.filter(|s| !s.is_zero())
				.map(|s| info.subsig_to_steps
					.get(&field_to_usize(s))
					.map(|r| r.vec_pm_bounds.len()).unwrap_or(0))
				.sum();
			println!("DEBUG USE 62070.7: qm DEMAND igc={} \
subsig_slots={} nonzero_subsigs={} chain_steps={} rows_built={}",
				self.b_igc, subsigs.len(), n_sub, chains,
				t.enc.len());
			//CLASS HISTOGRAM. Sizes the windowed-join idea: an FP row is
			//a trace match that entered Q_m unwindowed and was then
			//labelled unreachable, so FP is exactly what a windowed join
			//would never have materialised. It also sizes the
			//class-gating idea (how many rows pay for C-only advice).
			let f_max = F::from(((1u64 <<
				read_global_config().range2_bit) - 1) as u64);
			let (mut c, mut fp, mut bp, mut sp) = (0, 0, 0, 0);
			let (mut wrap, mut unset) = (0, 0);
			for i in 0..t.enc.len() {
				let k = field_to_usize(&t.cat[i]) as u32;
				let w = t.loc[i].is_zero() || t.loc[i] == f_max;
				if k == CAT_C { c += 1; } else if k == CAT_FP { fp += 1; }
				else if k == CAT_BP { bp += 1; }
				else if k == CAT_SP { sp += 1; }
				else { unset += 1; }
				if w { wrap += 1; }
			}
			let real = t.enc.len() - wrap;
			println!("DEBUG USE 62070.9: qm CLASS igc={} rows={} \
C={} FP={} BP={} SP={} unset={} wrap={} real={} fp_share_of_real={}%",
				self.b_igc, t.enc.len(), c, fp, bp, sp, unset, wrap,
				real, if real > 0 { fp * 100 / real } else { 0 });
		}
		if t.enc.len() > n_total {
			return Err(Self::qm_caperr(&self.capacity, self.b_igc,
				info, n_keys, wrap_cap, n_real, n_real_cap));
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
	#[cfg(any())] // M8_NEW P1: counting block removed
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
	#[cfg(any())] // M8_NEW P1: counting block removed
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

/// Enforce v1 * v2 == v3 in ONE constraint. Building the product
/// as a variable first and then equating costs 2 -- the pin idiom
/// (col == mask * tag + const) pays that on every column.
fn check_prod_eq<F: PrimeField + ColEle>(
	v1: &FpVar<F>, v2: &FpVar<F>, v3: &FpVar<F>, _msg: &str,
) -> Result<(), SynthesisError> {
	let cs = v1.cs();
	if B_DEBUG && v1.value().is_ok() {
		assert!(v1.value()? * v2.value()? == v3.value()?,
			"ERR on check prod eq: {}", _msg);
	}
	cs.enforce_constraint(var_to_lb(v1, F::one()),
		var_to_lb(v2, F::one()), var_to_lb(v3, F::one()))?;
	Ok(())
}

/// DB companion tag of a value column, minus its enc term:
/// gen_step_tbl_id(enc, cid) == si_tag_base(cid) + enc. Callers
/// add the row's own enc, which is what welds tag to row.
fn si_tag_base<F: PrimeField>(cid: u32) -> F {
	let f1 = F::from(1u64 << read_global_config().range2_bit);
	let f5 = f1 * f1 * f1 * f1 * f1;
	F::from(0x23001101u64) * f5 * F::from(1u64 << 32)
		+ F::from(cid as u64) * f5
}

/// Pin one si companion column: si == tag when the mask is on and
/// si == RANGE2 when it is off, with tag = si_tag_base(cid) + key.
/// ONE constraint -- see the comment in assert_neo_si_pins for the
/// two-cases-in-one-line form and why c_tag arrives pre-shifted.
/// INVARIANT: every VARIABLE-si column that core_container
/// registers is pinned through this helper, either in
/// assert_neo_si_pins (base cols) or in assert_neo_si_pins_nonaggr
/// (nonaggr cols + the JR table).
fn check_si_pin<F: PrimeField + ColEle>(
	mask: &FpVar<F>, key: &FpVar<F>, si: &FpVar<F>,
	c_tag: &FpVar<F>, c_rg2: &FpVar<F>, _msg: &str,
) -> Result<(), SynthesisError> {
	check_prod_eq(mask, &(c_tag + key), &(si - c_rg2), _msg)
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

/// Build one GATE-ONLY zero bit per row: out[i] is FORCED to 0
/// when vars[i] != 0 (weld out*var = 0, 1cs); when vars[i] == 0
/// it is free advice (honest value 1). Use ONLY to skip a check
/// at a sentinel -- re-enabling it there only harms the prover.
fn gen_gate_bits<F: PrimeField + ColEle>(
	cs: &ConstraintSystemRef<F>, native: &[F], vars: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
	// NOTE(perf): unlike gen_zero_bits there is NO field inverse
	// here, so batch_inversion has nothing to amortize -- the
	// per-row work is already one witness + one constraint.
	(0..native.len()).map(|i| {
		let b = new_var(cs, if native[i].is_zero() { F::one() }
			else { F::zero() });
		check_prod_zero(&b, &vars[i], lc!(), "gate bit")?;
		Ok(b)
	}).collect()
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
	pub d_below_lo: Vec<FpVar<F>>, pub d_above_lo: Vec<FpVar<F>>,
	pub d_sort: Vec<FpVar<F>>,
	pub si_step: Vec<FpVar<F>>, pub si_subsig: Vec<FpVar<F>>,
	pub si_pat: Vec<FpVar<F>>, pub si_rg1: Vec<FpVar<F>>,
	pub si_rg2: Vec<FpVar<F>>, pub si_enc_prev: Vec<FpVar<F>>,
	pub si_b_bwd: Vec<FpVar<F>>,
	/// non-aggressive witness mirror (empty under aggressive).
	pub nonaggr: QmNonAggrVars<F>,
}

/// NONAGGR ONLY -- circuit-var mirror of JrTable (all vecs empty
/// under aggressive). Allocated by load_neo_stmt_nonaggr.
pub(crate) struct JrVars<F: PrimeField + ColEle> {
	pub enc: Vec<FpVar<F>>, pub pat: Vec<FpVar<F>>,
	pub id: Vec<FpVar<F>>, pub loc: Vec<FpVar<F>>,
	pub si_pat: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> JrVars<F> {
	/// all-empty mirror for the aggressive loader (never read).
	pub(crate) fn empty() -> Self {
		Self { enc: vec![], pat: vec![], id: vec![],
			loc: vec![], si_pat: vec![] }
	}
}

/// Per-row selector bits handed to every downstream cert block.
/// is_wrap is a linear residual (may be non-boolean only on rows
/// other invariants already reject); the rest are forced bits.
/// is_bp/is_sp exist only in the non-aggressive arm (empty in aggr,
/// whose cats are {0, C, FP} after the BP->C retag); b_bwd_row is
/// aggressive-only (EMPTY in non-aggr: no backward subsigs there).
pub(crate) struct NeoSel<F: PrimeField + ColEle> {
	pub is_pad: Vec<FpVar<F>>, pub is_wrap: Vec<FpVar<F>>,
	pub is_c: Vec<FpVar<F>>, pub is_fp: Vec<FpVar<F>>,
	pub is_bp: Vec<FpVar<F>>, pub is_sp: Vec<FpVar<F>>,
	pub is_step0: Vec<FpVar<F>>, pub b_bwd_row: Vec<FpVar<F>>,
	pub is_last: Vec<FpVar<F>>,
	/// (is_c + is_fp) * is_step0: the real seed-row indicator on
	/// any satisfying assignment (the seed pin kills FP seeds),
	/// exported so sel_c = is_c - is_seed is a free combination.
	pub is_seed: Vec<FpVar<F>>,
}

/// Per-row rank counters over the two queried subsets of Q_m:
/// rid = rank within the reachable rows (wrap|C|BP|SP), cid =
/// rank within the carried rows (wrap|C; EMPTY in aggr). Both
/// are in-circuit prefix sums, reset per group, and give lookups
/// their order coordinate ("id 1 = the group's smallest
/// surviving loc").
pub(crate) struct QmRanks<F: PrimeField + ColEle> {
	pub rid: Vec<FpVar<F>>,
	pub cid: Vec<FpVar<F>>,
}

/// Accumulator for queries into Q_m's committed rows. The four
/// certificate functions (assert_carry, assert_fwd_pruning,
/// assert_bwd_pruning, assert_singleton_pruning) PUSH
/// (query, selector) pairs; none of them runs a lookup itself.
/// assert_qm_lookups later checks ALL buffered queries in one
/// shared batch lookup (logup) per buffer -- one multiplicity
/// table and one lookup argument serve every certificate, which
/// is cheaper than each certificate running its own.
/// Queries and targets share the packing enc + r1*id + r1^2*loc.
/// A pair with sel = 0 is vacuous (padding / non-applicable row).
///
/// A buffered query claims "this row exists in a chosen SUBSET
/// of Q_m". Only two subsets are ever queried, and each needs
/// its own instance because one batch lookup has ONE target set:
///
///   REACHABLE instance -- subset Q_r = wrap|C|BP|SP rows (all
///     but FP). Used where the claim is "this row was not
///     forward-pruned": assert_fwd_pruning's two bracketing
///     neighbors of an FP row, and the seed anchors.
///
///   CARRIED instance -- subset = wrap|C rows only. Used where
///     the claim is "this row SURVIVED into the carry":
///     assert_carry's predecessor of a C row, and the
///     group-minimum pins of assert_bwd_pruning /
///     assert_singleton_pruning (a minimum is only meaningful
///     over surviving rows).
///
/// The id inside the packing is the row's rank WITHIN its
/// subset (rid over Q_r, cid over carried), which is what makes
/// "id 1 = the group's smallest surviving loc" pins work.
/// Aggr has no BP/SP rows, so the two subsets coincide: one
/// instance serves every certificate fn.
///
/// CALLERS: only the entry fns assert_neo_{aggr,nonaggr} create
/// instances and call assert_qm_lookups (as their last step,
/// consuming the buffers); certificate fns only push.
pub(crate) struct QmQueryBuf<F: PrimeField + ColEle> {
	pub qry: Vec<FpVar<F>>,
	pub sel: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> QmQueryBuf<F> {
	pub fn new() -> Self { Self { qry: vec![], sel: vec![] } }

	pub fn push(&mut self, qry: FpVar<F>, sel: FpVar<F>) {
		self.qry.push(qry);
		self.sel.push(sel);
	}
}

/// The previous-step row that assert_carry and assert_fwd_pruning
/// both name: packed lookup keys for the (rank, rank+1) neighbor
/// pair, plus the "lower slot is the 0-wrap" bit. Built once per
/// chunk instead of once per consumer.
pub(crate) struct PredView<F: PrimeField + ColEle> {
	/// pack(enc_prev, prev_id1, prev_loc1): C's predecessor and
	/// FP's lower bracket neighbor.
	pub key1: Vec<FpVar<F>>,
	/// pack(enc_prev, prev_id1 + 1, prev_loc2): FP's upper
	/// bracket neighbor, rank-adjacent to key1 by construction.
	pub key2: Vec<FpVar<F>>,
	/// prev_loc1 == 0 bits. NON-AGGR: forced zero bits (the
	/// carry 0-wrap ban needs "loc1 = 0 -> bit = 1"). AGGR:
	/// gate-only bits (only FP's below-skip reads them).
	pub z_loc1: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// Row-classification layer, run in BOTH modes (aggressive and
	/// non-aggressive). Every T_qm row is proven to be exactly one
	/// of: PAD (enc==0 filler), WRAP (the loc-0 / loc-max sentinel
	/// rows that bracket a group), C (reachable match), FP
	/// (unreachable match), and -- non-aggressive only -- BP (the
	/// scan outran it) or SP (frozen-step surplus). Every later
	/// block masks its constraints with these bits, so soundness
	/// rests on the bits being FORCED here, not chosen.
	///
	/// Advice names (per row; all derived here, none committed):
	///   is_pad, is_step0, is_step1, is_last, plus is_bp and is_sp
	///            in non-aggr -- zero-INDICATOR bits: the bit is 1
	///            if and only if the tested column equals its
	///            sentinel. BOTH implications are enforced (col =
	///            sentinel => bit = 1, AND bit = 1 => col =
	///            sentinel); the cheaper 1cs "gate" bit gives only
	///            the second, and every consumer here reads both.
	///   is_c, is_fp  NOT bits at all, but expressions in cat (see
	///            Section 3). An R1CS constraint is written over
	///            linear combinations of variables, so 2*cat -
	///            cat^2 and (cat^2 - cat)/2 can stand wherever a
	///            bit stands, at ZERO extra constraints.
	///   is_wrap  the leftover share, same idea: a wrap row has no
	///            cat of its own (cat = 0, exactly like a pad), so
	///            it is named by elimination, 1 - is_pad - is_c -
	///            is_fp (- is_bp - is_sp), and check (3) then makes
	///            the prover earn it. It lands in {0,1} because
	///            check (4) keeps a pad's cat at 0, so no row is
	///            counted in two shares at once.
	///   is_seed  1 on a subsig's step-0 row -- the artificial
	///            match at loc 1 that every chain starts from.
	///            It is the mask check (5) already multiplies, so
	///            it costs nothing extra; exported because (5)
	///            also bans FP seeds, making it exactly
	///            is_c * is_step0. The two blocks that want "a C
	///            row that is NOT the seed" then write
	///            is_c - is_seed -- a subtraction of columns that
	///            already exist -- instead of one multiplication
	///            per row each.
	///
	/// Checks:
	///  (1) row 0 is a pad (closes the i-1 read at table start);
	///  (2) cat is a class node: cat*(cat-1)*(cat-2) = 0, non-aggr
	///      folding its two extra nodes off cat first;
	///  (3) a wrap row really sits at a sentinel: loc in {0, max};
	///  (4) pad hygiene: a pad carries neither loc nor cat;
	///  (5) seed pins: a real step-0 row sits at loc 1, never FP;
	///  (6) NON-AGGR: a real step-0 row stays C (not BP/SP);
	///  (7) AGGR: b_bwd_row = the row's window direction, forced
	///      forward on step-1 rows (their predecessor is the seed,
	///      an anchor rather than a real location).
	///
	/// EXAMPLE (fig-14) group a1 = [0w, 43C, 131FP, maxw]:
	/// is_wrap 1,0,0,1; is_c 0,1,0,0; is_fp 0,0,1,0.
	///  - CHEAT junk cat at a real loc: cat = 7 is not a node ->
	///    (2) UNSAT; nor can it pose as a wrap, (3) wants loc in
	///    {0,max}.
	///  - CHEAT C and FP at once: cat is ONE node, so no row stalls
	///    its rank (as FP) while passing a C window.
	///  - CHEAT fake seed at loc 500: (5) pins step-0 rows to loc
	///    1, else a1:505 cites it and fabricates reach.
	///  - CHEAT FP seed: orphans every step-1 row and lets a whole
	///    live chain be labeled away; (5) bans it.
	/// PARAMS: t = native cols, batched-inverse HINTS only (hints
	/// cannot weaken soundness -- constraints bind v alone).
	/// COST: ~18*n aggr / ~20*n non-aggr. PERF 61081.1.
	fn assert_neo_selectors(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, b_aggr: bool,
		job_id: usize,
	) -> Result<NeoSel<F>, SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let max_val: usize = (1 << read_global_config().range2_bit) - 1;
		let c_one = new_const_var(&cs, F::one());
		let c_two = new_const_var(&cs, F::from(2u32));
		let c_three = new_const_var(&cs, F::from(3u32));
		let c_four = new_const_var(&cs, F::from(4u32));
		let c_half = new_const_var(&cs,
			F::from(2u32).inverse().unwrap());
		let c_max = new_const_var(&cs, F::from(max_val as u32));
		// the interpolants in Section 3 are tied to this numbering.
		assert!(CAT_C == 1 && CAT_FP == 2 && CAT_BP == 3
			&& CAT_SP == 4, "neo class bits assume nodes 0..4");
		// --- Section 1: forced zero-indicator bits (2cs each) ---
		// gen_zero_bits enforces both implications; a 1cs gate bit
		// would enforce only "bit = 1 => col = sentinel". Both
		// senses are read here, e.g. is_step0 = 0 on a real step-0
		// row would demand DB facts that do not exist for the seed
		// key, while is_step0 = 1 on a step>0 row would skip that
		// row's rg1/rg2 pins outright.
		let zbit = |col: &Vec<F>, var: &Vec<FpVar<F>>, s: F|
		-> Result<Vec<FpVar<F>>, SynthesisError> {
			let c_s = new_const_var(&cs, s);
			gen_zero_bits(&cs,
				&col.iter().map(|x| *x - s).collect::<Vec<F>>(),
				&var.iter().map(|x| x - &c_s).collect::<Vec<_>>())
		};
		let is_pad = gen_zero_bits(&cs, &t.enc, &v.enc)?;
		let is_step0 = gen_zero_bits(&cs, &t.step, &v.step)?;
		// C and FP need no bits (Section 3). BP/SP do: they are the
		// nodes folded OFF cat there, so they must be pinned first.
		let (is_bp, is_sp) = if b_aggr { (vec![], vec![]) } else {
			(zbit(&t.cat, &v.cat, F::from(CAT_BP))?,
			 zbit(&t.cat, &v.cat, F::from(CAT_SP))?)
		};
		// non-aggr has no backward subsigs (asserted at the advice
		// fill), so the whole direction layer is aggr-only. This
		// bit must be a full indicator, not a gate: a backward
		// subsig's step-1 FP row could otherwise claim is_step1 =
		// 0, keep its mirrored window, and discharge a location the
		// seed actually reaches (the mirrored below-test is
		// trivially true and the max-wrap skips the above-test).
		let is_step1 = if b_aggr {
			zbit(&t.step, &v.step, F::one())?
		} else { vec![] };
		// is_last <=> si_step carries the LAST tag of THIS enc, so
		// the bit names a DB fact (si_step is 2-tag pinned by
		// si_pins + bound by the outer lookup). NOTE: pad rows
		// carry the subsig-0 LAST tag, so is_last = 1 on pads;
		// consumers mask by is_pad or by enc.
		let cl_nat = si_tag_base::<F>(ID_ENCODED_LAST_STEP);
		let c_l = new_const_var(&cs, cl_nat);
		let is_last = gen_zero_bits(&cs,
			&(0..n).map(|i| t.si_step[i] - cl_nat - t.enc[i])
				.collect::<Vec<F>>(),
			&(0..n).map(|i| &(&v.si_step[i] - &c_l) - &v.enc[i])
				.collect::<Vec<_>>())?;
		// --- Section 2 / check (1): row 0 is a pad (1cs, once) ---
		// the group-start rule reads row i-1; forcing enc[0] == 0
		// closes the table-start boundary (pads sort first).
		check_eq(&v.enc[0], &FpVar::<F>::Constant(F::zero()),
			"neo row0 pad")?;
		let mut sel = NeoSel { is_pad: vec![], is_wrap: vec![],
			is_c: vec![], is_fp: vec![], is_bp: vec![],
			is_sp: vec![], is_step0: vec![], b_bwd_row: vec![],
			is_last: vec![], is_seed: vec![] };
		for i in 0..n {
			// --- Section 3 / check (2): one cubic pins cat ---
			// cat is committed with si 0 (no outer range check),
			// so nothing yet stops it being an arbitrary field
			// element. Two ways to get class bits out of it:
			//   was: one zero-indicator bit per class, 2cs each
			//        -- 4cs aggressive, 8cs non-aggressive;
			//   now: pin cat to one of 3 nodes with a single
			//        cubic, then READ the classes off cat -- 2cs,
			//        both arms.
			// ce2 is the only witness this costs: ce2 = cat_e^2
			// (1cs). Given ce2, the cubic is one more constraint
			// and the classes are quadratics through the 3 nodes:
			//   cat_e                0 (pad/wrap)  1 (C)  2 (FP)
			//   ce2 = cat_e^2              0         1      4
			//   is_c  = 2*cat_e - ce2      0         1      0
			//   is_fp = (ce2 - cat_e)/2    0         0      1
			// Neither line allocates anything: both are linear in
			// the variables (cat_e, ce2), and R1CS constraints are
			// written over exactly such combinations, so they are
			// free wherever they are used downstream.
			// They are BOOLEAN even though nothing declares them
			// so, and the argument rests on ce2 NOT being free
			// advice: the multiplication above binds ce2 =
			// cat_e^2, and the cubic leaves cat_e three roots, so
			// (is_c, is_fp) can only be (0,0), (1,0) or (0,1).
			// Exclusivity and is_c + is_fp in {0,1} come with it.
			// cat_e ("effective cat") exists only so both arms can
			// share that cubic: non-aggr's cat also takes 3 (BP)
			// and 4 (SP), which alone would need a quartic. Since
			// is_bp/is_sp are already forced bits, subtracting
			// 3*is_bp + 4*is_sp maps those two nodes onto 0 and
			// leaves the other three untouched. A junk cat (7)
			// sets neither bit, so cat_e = 7, no root -> UNSAT.
			// Pinning cat to ONE node is also what makes the
			// classes mutually exclusive, and that is
			// load-bearing: a row tagged C AND FP would stall rid
			// (hiding a reachable row) while still passing its C
			// window, forging a rank-adjacent FP bracket one step
			// later.
			let cat_e = if b_aggr { v.cat[i].clone() } else {
				&(&v.cat[i] - &(&is_bp[i] * &c_three))
					- &(&is_sp[i] * &c_four)
			};
			let ce2 = &cat_e * &cat_e;
			check_prod_zero(&(&ce2 - &cat_e), &(&cat_e - &c_two),
				lc!(), "neo cat is a class node")?;
			let is_c = &(&cat_e * &c_two) - &ce2;
			let is_fp = &(&ce2 - &cat_e) * &c_half;
			// --- Section 4 / check (3): wrap = the residual ---
			// A wrap row carries cat = 0, the same as a pad: there
			// is no "wrap" value to test for. So the class is
			// assigned by elimination, and check (3) then makes
			// the prover earn it -- a wrap must sit at loc 0 or
			// loc max. That is also what stops a real match row
			// from dropping its cat to escape its certificate:
			// the row becomes a wrap and is dragged to a sentinel
			// loc it does not have.
			// The residual is in {0,1} because at most one share
			// on the right is 1: the cat classes are exclusive by
			// Section 3, and check (4) below keeps a pad's cat at
			// 0, so is_pad never overlaps them.
			let res = &(&(&c_one - &is_pad[i]) - &is_c) - &is_fp;
			let is_wrap = if b_aggr { res } else {
				&(&res - &is_bp[i]) - &is_sp[i]
			};
			let t1 = &is_wrap * &v.loc[i];
			check_prod_zero(&t1, &(&v.loc[i] - &c_max), lc!(),
				"neo wrap loc in {0,max}")?;
			// --- Section 5 / check (4): pad hygiene (2cs) ---
			// loc: pads must pack to ZERO for the union multiset.
			// cat: a SEPARATE constraint on purpose -- loc carries
			// si 0 too, so a fused (loc + cat) rule would admit
			// cat = FP with loc = -FP: a pad that DECREMENTS rid
			// and signs the QR target with multiplicity -1. Split,
			// this is what keeps is_pad disjoint from the cat
			// classes, hence is_wrap boolean on every row and
			// every lookup selector non-negative.
			check_prod_zero(&is_pad[i], &v.loc[i], lc!(),
				"neo pad loc")?;
			check_prod_zero(&is_pad[i], &v.cat[i], lc!(),
				"neo pad cat")?;
			// --- Section 6 / check (5): the seed row (3cs) ---
			// A subsig's chain starts at an artificial step-0
			// match placed at loc 1. Pin it: any real (C or FP)
			// step-0 row must be at loc 1, else a step-1 row cites
			// a fabricated seed at loc 500 and claims reach. Ban
			// FP seeds too: an FP seed orphans every step-1 row
			// and lets a whole live chain be labeled away.
			// t0 is that pin's mask, exported as is_seed. With FP
			// seeds banned it equals is_c * is_step0, so consumers
			// get "C but not the seed" as the free subtraction
			// is_c - is_seed (assert_carry, assert_verdict_aggr);
			// without the ban that subtraction could go NEGATIVE
			// on an FP seed row and feed a negative multiplicity.
			let t0 = (&is_c + &is_fp) * &is_step0[i];
			check_prod_zero(&t0, &(&v.loc[i] - &c_one), lc!(),
				"neo seed at loc 1")?;
			check_prod_zero(&is_fp, &is_step0[i], lc!(),
				"neo seed not FP")?;
			sel.is_seed.push(t0);
			// --- Section 6b / check (6): non-aggr seed stays C ---
			// NOT implied by the seed anchor: the non-aggr QR
			// target admits BP/SP rows, so an SP-tagged seed would
			// still answer the anchor query while leaving q_c
			// short by one carried row.
			if !b_aggr {
				check_prod_zero(&is_step0[i],
					&(&is_bp[i] + &is_sp[i]), lc!(),
					"neo seed stays C")?;
			}
			// --- Section 7 / check (7): window direction (1cs,
			//     AGGR only; sel.b_bwd_row stays empty else) ---
			// b_bwd is a DB fact about the row's subsig: its steps
			// are stored in reverse, so the gap to the predecessor
			// is measured the other way round. It cannot apply at
			// step 1, whose predecessor is the seed anchor rather
			// than a real location.
			// EXAMPLE sig "a1 .{1,9} kw", stored kw-first:
			//   kw:50 at step 1 -- pred is the seed at loc 1, so
			//     the gap is read FORWARD, 50 - 1 = 49;
			//   a1:43 at step 2 -- pred is the real row kw:50, so
			//     the MIRRORED gap 50 - 43 = 7 is the one that
			//     must land in [1,9].
			// Hence b_bwd_row = b_bwd everywhere except step 1,
			// where it is forced to 0. Read by assert_carry and
			// assert_fwd_pruning.
			if b_aggr {
				sel.b_bwd_row.push(&v.b_bwd[i]
					* (&c_one - &is_step1[i]));
			}
			sel.is_c.push(is_c);
			sel.is_fp.push(is_fp);
			sel.is_wrap.push(is_wrap);
		}
		sel.is_pad = is_pad; sel.is_bp = is_bp; sel.is_sp = is_sp;
		sel.is_step0 = is_step0; sel.is_last = is_last;
		log(job_id, LOG3, &format!(
			"PERF 61081.1: block=selectors cs={} pred={}",
			cs.num_constraints() - n0,
			(if b_aggr { 18 } else { 20 }) * n));
		Ok(sel)
	}

	/// Proves T_qm has the SHAPE every later certificate assumes.
	/// TERMS: a GROUP is all rows sharing one key enc(subsig, step);
	/// it opens with a 0-WRAP (loc 0) and closes with a MAX-WRAP
	/// (loc max), the group's matches sorted in between. A RUN is
	/// all groups of one subsig, steps 0, 1, 2, ... The QR TARGET
	/// is the lookup image of the reachable rows, addressed by rid,
	/// a per-group rank that skips FP rows.
	///
	/// Advice names:
	///   b_same    zero-indicator bit, enc[i] == enc[i-1]: row i
	///             continues the previous group. Derived once here
	///             and reused by checks (1), (2) and (3);
	///   same_sub  the same bit on the subsig column (run
	///             adjacency);
	///   d_sort    committed column holding, on a row that
	///             continues a group, the gap to the row above:
	///             loc[i] - loc[i-1] (and 0 on any other row). It
	///             carries a RANGE2 si, so the OUTER lookup forces
	///             it non-negative: loc[i] >= loc[i-1] -- the
	///             NON-strict ascent of check (3). Equal neighbors
	///             are legal (halo-straddle duplicates); clones
	///             are policed by the union (nonaggr) / the join
	///             id-chain bijection into L (aggr) instead;
	///   grp_start returned: (1 - b_same) * (1 - is_pad), the reset
	///             signal of both rank chains;
	///   rid       returned: a row's ADDRESS inside the QR target.
	///             It advances on every REACHABLE row -- the two
	///             wraps and C in aggr, plus BP and SP in non-aggr
	///             -- and stalls on FP rows, which therefore have
	///             no address there at all. Reset to 0 at each
	///             grp_start, so the address is per-group.
	///
	/// Checks:
	///  (1) sorted-table skeleton: inside a group id steps by +1,
	///      and a group that ends does so at its max-wrap;
	///  (2) pads form a prefix, and a group's first row IS its
	///      0-wrap (id 0, loc 0);
	///  (3) ascending loc inside a group (duplicates allowed);
	///  (4) the multiset of group keys equals the expected keys --
	///      one per bound store row plus one seed key per statement
	///      subsig -- so no group is cloned or invented;
	///  (5) rid chain (a definition, see Section 6);
	///  (6) run completeness: a run starts at its subsig's step-0
	///      seed, steps by +1, and may end only at a DB-LAST group.
	///
	/// EXAMPLE a6 = [0w, 73C, 79C, 96FP, 141C, maxw] -> rid
	/// 0,1,2,2,3,4 (the FP row stalls the rank).
	///  - CHEAT shift the ids so another row reads "id 1": (2) pins
	///    a group's first row to id 0 AND loc 0.
	///  - CHEAT clone a group of enc_x (the false-FP oracle): (4)
	///    doubles enc_x's factor on one side only -> UNSAT.
	///  - CHEAT repeat an (enc, loc) row: (3) allows it, but the
	///    clone must be PAID -- nonaggr: no q_i/JR partner in the
	///    union; aggr: the id chain slides and the (pat, id, loc)
	///    join query misses L.
	///  - CHEAT drop a subsig's tail groups: (6) leaves that run
	///    unable to end, its last present group not being DB-LAST.
	/// PARAMS: s_enc = enc column of the bound store rows, s_enc_nat
	/// its natives (zero-bit hints); subsigs = statement subsig ids
	/// (seed key = subsig * 2^(4rb)); r2 fingerprints the key
	/// multiset. Returns (grp_start, rid).
	/// COST: ~19*n + ~4*(|s_enc| + |subsigs|). PERF 61081.2.
	fn assert_neo_wf(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		s_enc: &[FpVar<F>], subsigs: &[FpVar<F>],
		s_enc_nat: &[F], subsig_nat: &[F],
		r2: &FpVar<F>, job_id: usize,
	) -> Result<(Vec<FpVar<F>>, Vec<FpVar<F>>), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = t.enc.len();
		let rb = read_global_config().range2_bit;
		let c_max = new_const_var(&cs,
			F::from(((1u64 << rb) - 1) as u64));
		let c_one = new_const_var(&cs, F::one());
		// --- Section 1: group adjacency bit (2cs/row) ---
		// ONE forced indicator feeds the skeleton, the group starts
		// and the loc sort. db::assert_well_formed_sorted builds
		// its own private copy of exactly this bit, which is why
		// its rule is inlined in Section 2 rather than called.
		let mut d_nat = vec![F::zero(); n];
		for i in 1..n { d_nat[i] = t.enc[i] - t.enc[i - 1]; }
		let d_var = (0..n).map(|i| if i == 0 {
			FpVar::<F>::Constant(F::zero()) }
			else { &v.enc[i] - &v.enc[i - 1] }).collect::<Vec<_>>();
		let b_same = gen_zero_bits(&cs, &d_nat, &d_var)?;
		// --- Section 2 / check (1): the skeleton (2cs/row) ---
		// db::assert_well_formed_sorted's rule (no-sort,
		// non-relaxed branch), inlined: a non-pad predecessor
		// forces EITHER "same group and id steps by +1" OR "group
		// changed and the previous row was the max-wrap". The gate
		// (1 - is_pad[i-1]) is that fn's key[i-1] != 0 condition.
		// Two parts of the original are gone: its private
		// adjacency bit (Section 1 now serves it) and its r1 * loc
		// term, which fingerprinted "loc[i] == 0 at a group start"
		// -- Section 3 pins that directly and unconditionally,
		// which is why this block needs no challenge at all.
		// The (J-W) obligation of assert_join_locations (b_ext_wf =
		// true, aggr view) rides on this Section plus Section 3.
		check_eq(&v.id[0], &FpVar::<F>::Constant(F::zero()),
			"neo id0")?;
		for i in 1..n {
			let p1 = &(&v.id[i] - &v.id[i - 1]) - &c_one;
			let p2 = &v.loc[i - 1] - &c_max;
			let res = &(&b_same[i] * &(&p1 - &p2)) + &p2;
			check_prod_zero(&(&c_one - &sel.is_pad[i - 1]), &res,
				lc!(), "neo wf skeleton")?;
		}
		// --- Section 3 / check (2): group starts (4cs/row) ---
		// A non-pad key change opens a group, and that first row
		// must BE the group's 0-wrap. Split into two pins instead
		// of the old r1-fused "id + r1*loc == 0": same cost, holds
		// unconditionally rather than with high probability, and it
		// removes this function's last use of a challenge.
		let mut grp_start = vec![FpVar::<F>::Constant(F::zero())];
		for i in 1..n {
			check_prod_zero(&(&c_one - &sel.is_pad[i - 1]),
				&sel.is_pad[i], lc!(), "neo pads are a prefix")?;
			let gs = (&c_one - &b_same[i])
				* (&c_one - &sel.is_pad[i]);
			check_prod_zero(&gs, &v.id[i], lc!(),
				"neo group starts at id 0")?;
			check_prod_zero(&gs, &v.loc[i], lc!(),
				"neo group starts at loc 0")?;
			grp_start.push(gs);
		}
		check_prod_zero(&(&c_one - &sel.is_pad[n - 1]),
			&(&v.loc[n - 1] - &c_max), lc!(), "neo last row max")?;
		// --- Section 4 / check (3): non-strict sort (1cs/row) ---
		// "row i continues the group" is b_same * (1 - is_pad),
		// which equals (1 - is_pad) - grp_start: a FREE rewrite of
		// two columns Section 3 already paid for. The bind then
		// fits in one constraint. d_sort carries a RANGE2 si, so
		// the outer range table forces loc[i] >= loc[i-1]. Equal
		// neighbors (straddle duplicates) are legal; a cloned row
		// still dies unpaid in the union (nonaggr) or misses its
		// (pat, id, loc) join query (aggr id-chain bijection).
		for i in 1..n {
			let same = &(&c_one - &sel.is_pad[i]) - &grp_start[i];
			check_prod_eq(&same,
				&(&v.loc[i] - &v.loc[i - 1]),
				&v.d_sort[i], "neo sort bind")?;
		}
		// --- Section 5 / check (4): group uniqueness (2cs/row
		//     + ~4 per expected key) ---
		// A grand product over the 0-wrap keys must equal the
		// product over the expected keys. Zero entries are pads
		// (padded store rows, dummy-0 subsig slots) and contribute
		// the neutral factor 1; a real store enc or subsig is never
		// 0, so masking cannot hide a live key.
		let mut lhs = c_one.clone();
		for i in 0..n {
			let term = &grp_start[i] * &(&(&v.enc[i] + r2) - &c_one);
			lhs = &lhs * &(&term + &c_one);
		}
		let f1 = F::from(1u64 << rb);
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
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
		// --- Section 6 / check (5): rid rank chain (1cs/row) ---
		// 0 at a group start, then +1 on exactly the NON-FP rows,
		// which are the QR target (aggr: wraps and C; non-aggr:
		// also BP and SP). FP rows keep the previous rank and so
		// have no address in the target at all.
		// The increment lands in {0,1} rather than going negative
		// because the classes are exclusive and pads are cat-free
		// (selectors Sections 3 and 5).
		let mut rid = vec![FpVar::<F>::Constant(F::zero())];
		for i in 1..n {
			let inc = &(&c_one - &sel.is_pad[i]) - &sel.is_fp[i];
			let r_i = (&c_one - &grp_start[i])
				* &(&rid[i - 1] + &inc);
			rid.push(r_i);
		}
		// --- Section 7 / check (6): run completeness (7cs/row) ---
		// Sorted encs put each subsig's groups in one contiguous
		// run. Ending a run only at a DB-LAST group, together with
		// the seed anchor of assert_seed_anchors, forces any subsig
		// that appears at all to show its FULL chain: a joint store
		// drop leaves a run that cannot be closed.
		let mut ds_nat = vec![F::zero(); n];
		for i in 1..n { ds_nat[i] = t.subsig[i] - t.subsig[i - 1]; }
		let ds_var = (0..n).map(|i| if i == 0 {
			FpVar::<F>::Constant(F::zero()) }
			else { &v.subsig[i] - &v.subsig[i - 1] })
			.collect::<Vec<_>>();
		let same_sub = gen_zero_bits(&cs, &ds_nat, &ds_var)?;
		for i in 1..n {
			let bnd = &grp_start[i] * &(&c_one - &same_sub[i]);
			// a pad predecessor means this is the FIRST run in the
			// table, so there is nothing behind it to end.
			let t_end = &bnd * &(&c_one - &sel.is_pad[i - 1]);
			check_prod_zero(&t_end,
				&(&c_one - &sel.is_last[i - 1]), lc!(),
				"neo run ends at LAST")?;
			check_prod_zero(&bnd, &v.step[i], lc!(),
				"neo run starts at seed")?;
			// "same run, next group" is grp_start * same_sub, which
			// is grp_start - bnd: free, same argument as Section 4.
			let u = &grp_start[i] - &bnd;
			check_prod_zero(&u,
				&(&(&v.step[i] - &v.step[i - 1]) - &c_one), lc!(),
				"neo run step chain")?;
		}
		check_prod_zero(&(&c_one - &sel.is_pad[n - 1]),
			&(&c_one - &sel.is_last[n - 1]), lc!(),
			"neo final run ends at LAST")?;
		log(job_id, LOG3, &format!(
			"PERF 61081.2: block=wf cs={} pred={}",
			cs.num_constraints() - n0, 19 * n));
		Ok((grp_start, rid))
	}

	/// Binds each si companion column of T_qm to the row it sits on.
	/// An si column is the "which DB fact" selector travelling with
	/// a value column: the OUTER foldpot lookup forces every
	/// (si, value) pair to exist in the DB, so once si is pinned to
	/// a tag built from THIS row's enc, the value beside it is a DB
	/// fact about this row instead of prover advice. Tags are linear
	/// in enc -- gen_step_tbl_id(enc, cid) = si_tag_base(cid) + enc
	/// -- so every pin fits in a single constraint.
	///
	/// Advice names: none. Every column touched here is committed
	/// (si_step, si_subsig, si_pat, si_rg1, si_rg2, si_enc_prev,
	/// si_b_bwd); this block only binds them.
	///
	/// Checks, per row:
	///  (1) si_step is the NORMAL tag or the LAST tag of THIS enc;
	///  (2) si_subsig and si_pat are pinned on every non-pad
	///      step >= 1 row, wraps included (a wrap's pat is
	///      join-queried);
	///  (3) si_rg1, si_rg2 and si_enc_prev are pinned on REAL
	///      step >= 1 rows, real = is_c + is_fp, plus is_bp +
	///      is_sp in non-aggr;
	///  (4) si_b_bwd == FLAG_BASE + subsig on every row.
	/// Step-0 rows are masked out of (2) and (3): the seed key is
	/// artificial, so the DB carries no subsig/pat/window fact
	/// under it. A masked-off row takes RANGE2 instead, the neutral
	/// tag that tells the outer lookup "range check only". Those
	/// RANGE2 entries are produced by the ADVICE side -- push_wrap
	/// for wraps, push_real's m() for seed rows, pad_front for pads
	/// -- and are only enforced here.
	///
	/// EXAMPLE: a terminal row tagging si_step with the LAST tag of
	/// a DIFFERENT enc, to dodge the verdict query, fails (1) --
	/// neither factor is zero.
	///  - CHEAT a foreign pat under this enc, to hide the real
	///    pattern's matches: (2) ties pat to enc on every row, so
	///    the row can only carry the pat the DB gives its own enc.
	///  - CHEAT a widened window: rg1/rg2 are DB facts of enc by
	///    (3), not advice, so no row can widen its own reach.
	/// PARAMS: b_aggr only selects whether BP/SP join `real`.
	/// COST: ~9*n. PERF 61081.5.
	fn assert_neo_si_pins(
		cs: ConstraintSystemRef<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		b_aggr: bool, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = v.enc.len();
		let c_n = new_const_var(&cs,
			si_tag_base::<F>(ID_ENCODED_NORMAL_STEP));
		let c_l = new_const_var(&cs,
			si_tag_base::<F>(ID_ENCODED_LAST_STEP));
		let c_rg2t = new_const_var(&cs, F::from(RANGE2));
		let c_one = new_const_var(&cs, F::one());
		let c_fbase = new_const_var(&cs,
			F::from(1u64 << 32) * F::from(ID_SUBSIG_IS_BACKWARD));
		// Every pin has to say two things at once:
		//     mask on  -> si = tag,   tag = si_tag_base(cid) + enc
		//     mask off -> si = RANGE2
		// One line covers both:  si - RANGE2 = mask*(tag - RANGE2).
		//     mask = 1 -> si - RANGE2 = tag - RANGE2 -> si = tag
		//     mask = 0 -> si - RANGE2 = 0            -> si = RANGE2
		// EXAMPLE with si_tag_base(PAT) = 1000 and RANGE2 = 40, on
		// a row with enc = 7: tag = 1007, so a real row must carry
		// si_pat = 1007 and a seed row must carry 40.
		// That shape is ALREADY one R1CS constraint (A = mask,
		// B = tag - RANGE2, C = si - RANGE2), while building the
		// product as a variable and then comparing costs two.
		// tc() bakes the constant part (si_tag_base(cid) - RANGE2)
		// once per category for the whole table; the row's own enc
		// is added into B at the call site.
		let tc = |cid: u32| new_const_var(&cs,
			si_tag_base::<F>(cid) - F::from(RANGE2));
		let pins: [(FpVar<F>, fn(&QmVars<F>) -> &Vec<FpVar<F>>); 5] = [
			(tc(ID_ENCODED_SUBSIG), |v| &v.si_subsig),
			(tc(ID_ENCODED_PAT), |v| &v.si_pat),
			(tc(ID_ENCODED_RG_START), |v| &v.si_rg1),
			(tc(ID_ENCODED_RG_END), |v| &v.si_rg2),
			(tc(ID_ENCODED_PREV_ENCODED), |v| &v.si_enc_prev)];
		for i in 0..n {
			// --- check (1): si_step is a step tag of THIS enc ---
			// The DB stores a step under exactly ONE of the two
			// tags, so a last/non-last mislabel does not die here;
			// it dies at the outer lookup, which finds no such pair.
			check_prod_zero(
				&(&(&v.si_step[i] - &c_n) - &v.enc[i]),
				&(&(&v.si_step[i] - &c_l) - &v.enc[i]), lc!(),
				"neo si_step pin")?;
			// --- masks for checks (2) and (3) ---
			// m_sub: any non-pad row at step >= 1, wraps included.
			// m_bind: real rows only, at step >= 1. `real` is a
			// free sum of exclusive classes; in aggr the BP/SP
			// vectors are empty, which is why the two arms are
			// written out rather than always summing four terms.
			let m_sub = (&c_one - &sel.is_pad[i])
				* (&c_one - &sel.is_step0[i]);
			let real = if b_aggr {
				&sel.is_c[i] + &sel.is_fp[i]
			} else {
				&(&sel.is_c[i] + &sel.is_fp[i])
					+ &(&sel.is_bp[i] + &sel.is_sp[i])
			};
			let m_bind = real * (&c_one - &sel.is_step0[i]);
			// --- checks (2) and (3): one constraint per column ---
			// j = 0, 1 are si_subsig and si_pat (m_sub); j = 2, 3, 4
			// are si_rg1, si_rg2, si_enc_prev (m_bind).
			for (j, (c_tag, getcol)) in pins.iter().enumerate() {
				let mask = if j <= 1 { &m_sub } else { &m_bind };
				check_si_pin(mask, &v.enc[i], &getcol(v)[i],
					c_tag, &c_rg2t, "neo si pin")?;
			}
			// --- check (4): the backward-flag key ---
			// keyed by subsig rather than enc, and linear in it, so
			// no mask and no product: every row, pad included,
			// carries this pair.
			check_eq(&v.si_b_bwd[i], &(&c_fbase + &v.subsig[i]),
				"neo si_b_bwd pin")?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61081.5: block=si_pins cs={} pred={}",
			cs.num_constraints() - n0, 9 * n));
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
	/// committed pat_loc copy (sorted per pat, with the loc-0 and
	/// loc-max sentinel rows): pat, in-pat rank, loc.
	pub l_pat: Vec<F>, pub l_id: Vec<F>, pub l_loc: Vec<F>,
	pub subsig_nat: Vec<F>,
	pub s_enc: Vec<F>,
	pub mtbl_qr: Vec<F>,
	/// m-table of the join membership lookup: hit count per
	/// pat_loc row from Q_m's L-origin rows.
	pub mtbl_tm: Vec<F>,
	/// no-show pats: distinct store pats with zero matches this
	/// chunk (sorted, front-0-padded to s_enc.len()).
	pub ns_pat: Vec<F>,
	/// absence-gap advice per no-show slot (RANGE2-bound):
	/// p-1-g1 and g2-p-1 vs its straddling l_pat pair (g1, g2).
	pub d_ns_lo: Vec<F>, pub d_ns_hi: Vec<F>,
	/// m-table of the gap-pair lookup, len |L|+1: bottom pair
	/// (0, l_pat[0]), adjacent pairs, top (l_pat[last], 2^rb).
	pub mtbl_ns: Vec<F>,
	pub acc_out: Vec<F>, pub mtbl_acc: Vec<F>,
	// ---- non-aggressive extension (empty under aggressive) ----
	/// committed q_i (IDX_INP) cols: the carried-in queue Q_i as
	/// serialized by StepQueue::to_container (front-padded).
	pub qi_enc: Vec<F>, pub qi_loc: Vec<F>,
	/// committed q_c (IDX_OUP) cols: the carry set Q_c = the C
	/// projection of Q_m, next chunk's Q_i.
	pub qc_enc: Vec<F>, pub qc_loc: Vec<F>,
	/// m-table of the shared QC-target lookup (C-pred + BP-min +
	/// SP-freeze + SP-dom query families).
	pub mtbl_qc: Vec<F>,
	/// union proof scalars [b_left_more_zero, diff_zero] for the
	/// Q_m = Q_i u L multiset identity (len 2; empty in aggr).
	pub union_prf: Vec<F>,
	/// JOIN RESULT temp table (all vecs empty in aggr).
	pub jr: JrTable<F>,
}

/// FpVar mirror of NeoCore (what the circuit constrains).
pub(crate) struct NeoCoreVars<F: PrimeField + ColEle> {
	pub qm: QmVars<F>,
	pub l_pat: Vec<FpVar<F>>, pub l_id: Vec<FpVar<F>>,
	pub l_loc: Vec<FpVar<F>>,
	pub subsigs: Vec<FpVar<F>>,
	pub s_enc: Vec<FpVar<F>>,
	pub mtbl_qr: Vec<FpVar<F>>, pub mtbl_tm: Vec<FpVar<F>>,
	pub ns_pat: Vec<FpVar<F>>,
	pub d_ns_lo: Vec<FpVar<F>>, pub d_ns_hi: Vec<FpVar<F>>,
	pub mtbl_ns: Vec<FpVar<F>>,
	pub acc_out: Vec<FpVar<F>>, pub mtbl_acc: Vec<FpVar<F>>,
	// ---- non-aggressive extension (empty under aggressive) ----
	pub qi_enc: Vec<FpVar<F>>, pub qi_loc: Vec<FpVar<F>>,
	pub qc_enc: Vec<FpVar<F>>, pub qc_loc: Vec<FpVar<F>>,
	pub mtbl_qc: Vec<FpVar<F>>,
	pub union_prf: Vec<FpVar<F>>,
	pub jr: JrVars<F>,
}

/// FpVar mirror of QmNonAggrCols (loaded only by the non-aggressive
/// arm; every vec row-parallel to QmVars.enc).
pub(crate) struct QmNonAggrVars<F: PrimeField + ColEle> {
	pub enc_next: Vec<FpVar<F>>,
	pub bp_prev_val: Vec<FpVar<F>>, pub rg2_next: Vec<FpVar<F>>,
	pub w_next: Vec<FpVar<F>>, pub d_bp: Vec<FpVar<F>>,
	pub fz: Vec<FpVar<F>>, pub enc_fz: Vec<FpVar<F>>,
	pub fz_step_val: Vec<FpVar<F>>, pub fz_sub_val: Vec<FpVar<F>>,
	pub w_fz: Vec<FpVar<F>>, pub d_fz: Vec<FpVar<F>>,
	pub w_kept: Vec<FpVar<F>>, pub d_kept: Vec<FpVar<F>>,
	pub si_bp_prev: Vec<FpVar<F>>, pub si_rg2_next: Vec<FpVar<F>>,
	pub si_fz: Vec<FpVar<F>>, pub si_fz_step: Vec<FpVar<F>>,
	pub si_fz_sub: Vec<FpVar<F>>,
}

impl<F: PrimeField + ColEle> QmNonAggrVars<F> {
	/// all-empty mirror for the aggressive loader (never read).
	pub(crate) fn empty() -> Self {
		Self { enc_next: vec![], bp_prev_val: vec![],
			rg2_next: vec![], w_next: vec![], d_bp: vec![],
			fz: vec![], enc_fz: vec![], fz_step_val: vec![],
			fz_sub_val: vec![], w_fz: vec![], d_fz: vec![],
			w_kept: vec![], d_kept: vec![],
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

	/// AGGRESSIVE membership m-table: queries are the step >= 1 rows'
	/// (pat, id, loc); targets are L plus the two derived sentinel
	/// rows of each no-show pat.
	pub(crate) fn gen_mtbl_tm_aggr(t: &QmTable<F>, l_pat: &[F],
		l_id: &[F], l_loc: &[F], ns_pat: &[F]) -> Vec<F> {
		let rb = read_global_config().range2_bit;
		let (f_b, f_sh) = (F::from(1u64 << rb),
			F::from(1u128 << (2 * rb)));
		let f_t2 = F::from((1u64 << rb) + ((1u64 << rb) - 1));
		let one = F::one();
		let qry_tm: Vec<F> = (0..t.enc.len()).map(|i|
			t.pat[i] * f_sh + t.id[i] * f_b + t.loc[i])
			.collect();
		let sel_qry: Vec<F> = t.step.iter().map(|s|
			if s.is_zero() { F::zero() } else { one })
			.collect();
		let mut lk_tm: Vec<F> = (0..l_pat.len()).map(|i|
			l_pat[i] * f_sh + l_id[i] * f_b + l_loc[i])
			.collect();
		let mut sel_lk = vec![one; l_pat.len()];
		let sel_d: Vec<F> = ns_pat.iter().map(|p|
			if p.is_zero() { F::zero() } else { one })
			.collect();
		lk_tm.extend(ns_pat.iter().map(|p| *p * f_sh));
		sel_lk.extend(sel_d.clone());
		lk_tm.extend(ns_pat.iter().map(|p| *p * f_sh + f_t2));
		sel_lk.extend(sel_d);
		gen_m_table_cond(&qry_tm, &sel_qry, &lk_tm, &sel_lk)
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
	#[cfg(any())] // M8_NEW P1: counting block removed
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
				*hm.entry((t.enc[i], one, na.w_kept[i]))
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

	/// NONAGGR ONLY -- build the JOIN RESULT temp table
	///     JR = store JOIN (pat_loc || D),
	/// one block per store row (enc, pat), i.e. per (subsig,
	/// step >= 1) of the statement chains:
	///   pat IN L: pat's FULL L block, ids = L ranks 0..cnt+1
	///     -> [(pat,0,0), (pat,1,l1) .., (pat,cnt+1,max)]
	///   pat NOT in L ("no-show", zero matches this chunk):
	///     -> the sentinel pair [(pat,0,0), (pat,1,max)]. The
	///     pair is absent from L; membership resolves it via
	///     the NeoCore.ns_pat targets (gen_ns_pat), guarded by
	///     assert_ns_gap so a pat that IS in L can never fake
	///     a sentinel-only block and hide its matches.
	/// DECISION: D is per DISTINCT pat, not 2 dummy rows per
	/// step -- chains repeat pats heavily (fan-out copies), so
	/// |D| << store rows. The per-step sentinel pair itself is
	/// unavoidable (Q_m holds a wrap pair per step group whose
	/// union fps JR must pay) but lands in this ~11cs/row temp
	/// table, never in Q_m.
	/// NO Q_m input: gen_qm_table emits wrap groups for EVERY
	/// step of every chain (its trailing pop trims item rows
	/// only), so Q_m's step>=1 group keys are exactly the store
	/// rows -- JR is a pure function of store + L.
	/// Why nonaggr only: nonaggr carries C rows at step>=1, so
	/// Q_m groups interleave carried locs with L locs (ids
	/// re-ranked) -- the join needs this pristine L-block copy.
	/// Aggr carries the seed only: its step>=1 groups ARE the L
	/// blocks, Q_m itself is the join view (a JR would
	/// duplicate every row); aggr shares only the D mechanism.
	///
	/// EXAMPLE (chunk 2). Store: subsig 3 = {step 1: pat 2 (key
	/// E1), step 2: pat 5 (key E2)}; q_i carries E1:101; chunk
	/// L: pat 2 at {517, 525}, pat 5 absent. Q_m groups: E0
	/// seed, E1 = [w0, 101(C), 517, 525, wmax], E2 = [w0,
	/// wmax].
	///   (E1,2,0,0) (E1,2,1,517) (E1,2,2,525) (E1,2,3,max) <-L
	///   (E2,5,0,0) (E2,5,1,max)     <- no-show sentinel pair
	/// Union fps (enc||loc): E1 wraps + 517/525 paid by JR,
	/// E1||101 by q_i, E2 wraps by the D-backed pair. Dropping
	/// the E2 block leaves E2's wraps unpaid -> UNSAT; a
	/// sentinel-only block for E1 needs (2,1,max) in L||D:
	/// absent (L has (2,3,max); adjacency bars 2 from D).
	///
	/// si policy: si_pat = tag(enc, PAT) on EVERY block row,
	/// sentinels too (an unpinned sentinel could borrow a
	/// shorter pat's max row and truncate the block); jr_loc
	/// under the RANGE2 si; jr_enc/jr_id si 0 (union- /
	/// chain-bound). cap: JR row budget (front-pads; CapErr).
	pub(crate) fn gen_jr_table(
		s_enc: &[F],  // store keys (gen_store_rows)
		s_pat: &[F],  // store pats, row-parallel to s_enc
		hm_loc: &HashMap<F, Vec<(F, F)>>, // chunk L: pat ->
		              // [(id, loc)], 0/max-wrapped blocks
		cap: usize,   // JR row budget
	) -> Result<JrTable<F>, Error> {
		let max_val: usize =
			(1 << read_global_config().range2_bit) - 1;
		let (z, one, f_max) = (F::zero(), F::one(),
			F::from(max_val as u32));
		// -- 1. one block per store row; no-show pats get the
		//    sentinel pair --
		let mut jr = JrTable::default();
		let sent = [(z, z), (one, f_max)];
		for (e, p) in s_enc.iter().zip(s_pat.iter()) {
			if e.is_zero() { continue; }
			let si = SubsigStepStore::gen_step_tbl_id(*e,
				ID_ENCODED_PAT);
			let block: &[(F, F)] = match hm_loc.get(p) {
				Some(v) => v.as_slice(),
				None => &sent
			};
			for (id, loc) in block {
				jr.enc.push(*e); jr.pat.push(*p);
				jr.id.push(*id); jr.loc.push(*loc);
				jr.si_pat.push(si);
			}
		}
		// -- 2. capacity pad (pads first, Q_m convention) --
		let used = jr.enc.len();
		if used > cap {
			return Err(Error::CapErr(vec![(
				format!("jr_table"), used)]));
		}
		let rg2t = F::from(RANGE2);
		let pz = |v: &mut Vec<F>, x: F| {
			let mut w = vec![x; cap - used];
			w.append(v); *v = w; };
		pz(&mut jr.enc, z); pz(&mut jr.pat, z);
		pz(&mut jr.id, z); pz(&mut jr.loc, z);
		pz(&mut jr.si_pat, rg2t);
		Ok(jr)
	}

	/// No-show pats: distinct store pats absent from the chunk's
	/// pat_loc pat column (deduped, sorted, front-0-pad to cap).
	pub(crate) fn gen_ns_pat(s_pat: &[F], l_pat: &[F],
		cap: usize) -> Vec<F> {
		let in_l: HashSet<F> = l_pat.iter().cloned().collect();
		let mut ns: Vec<F> = s_pat.iter()
			.filter(|p| !p.is_zero() && !in_l.contains(p))
			.cloned().collect::<HashSet<F>>()
			.into_iter().collect();
		ns.sort_by(|a, b| a.partial_cmp(b).unwrap());
		assert!(ns.len() <= cap, "ns_pat over cap {}", cap);
		let mut res = vec![F::zero(); cap - ns.len()];
		res.extend(ns);
		res
	}

	/// Gap advice for the absence proof: per nonzero no-show
	/// pat, locate the l_pat pair straddling it. Returns
	/// (d_ns_lo, d_ns_hi, mtbl_ns); pair slot k: 0 = bottom
	/// (0, l_pat[0]), 1..n-1 = (l_pat[k-1], l_pat[k]), n = top
	/// (l_pat[n-1], 2^rb).
	fn gen_ns_advice(ns_pat: &[F], l_pat: &[F])
	-> (Vec<F>, Vec<F>, Vec<F>) {
		let n = l_pat.len();
		let (z, one) = (F::zero(), F::one());
		let f_top = F::from(
			1u64 << read_global_config().range2_bit);
		let mut d_lo = vec![z; ns_pat.len()];
		let mut d_hi = vec![z; ns_pat.len()];
		let mut mtbl = vec![z; n + 1];
		let pair = |k: usize| -> (F, F) {
			if k == 0 { (z, l_pat[0]) }
			else if k < n { (l_pat[k - 1], l_pat[k]) }
			else { (l_pat[n - 1], f_top) }
		};
		for (k, p) in ns_pat.iter().enumerate() {
			if p.is_zero() { continue; }
			assert!(n > 0, "no-show pat with empty pat_loc");
			let up = field_to_usize(p);
			let hit = (0..n + 1).find(|i| {
				let (a, b) = pair(*i);
				field_to_usize(&a) < up
					&& up < field_to_usize(&b)
			}).expect("no straddling pair: pat in L?");
			let (a, b) = pair(hit);
			d_lo[k] = *p - one - a;
			d_hi[k] = b - *p - one;
			mtbl[hit] = mtbl[hit] + one;
		}
		(d_lo, d_hi, mtbl)
	}

	/// The two zero-count reconciliation scalars of the multiset
	/// identity Q_m = q_i union JR over pack(enc, loc), which
	/// assert_qm_union checks in-circuit. The WHOLE step-0 group
	/// leaves the identity on both sides: Q_m masks step==0 rows
	/// (wraps AND the per-universe-subsig seed C rows the M8b
	/// reseed synthesizes), q_i masks its seed-enc rows (enc =
	/// subsig*2^4rb, the carried subset). Seed soundness is owned
	/// by the seed anchors + wf, not by transport. JR never holds
	/// a step-0 row (store rows are step>=1); pads pack to 0 and
	/// the identity ignores zeros.
	fn gen_union_scalars(t: &QmTable<F>, jr: &JrTable<F>,
		qi_enc: &[F], qi_loc: &[F], subsig_nat: &[F])
	-> Result<Vec<F>, Error> {
		let base = F::from(1u64
			<< read_global_config().range2_bit);
		let sh4 = base * base * base * base;
		let seed_encs = subsig_nat.iter()
			.filter(|s| !s.is_zero())
			.map(|s| *s * sh4).collect::<HashSet<F>>();
		let pk = |e: &[F], l: &[F]| e.iter().zip(l.iter())
			.map(|(x, y)| *x * base + *y).collect::<Vec<F>>();
		let vec1: Vec<F> = qi_enc.iter().zip(qi_loc.iter())
			.map(|(x, y)| if seed_encs.contains(x) { F::zero() }
				else { *x * base + *y }).collect();
		let vec2 = pk(&jr.enc, &jr.loc);
		let vec3: Vec<F> = (0..t.enc.len()).map(|i|
			if t.step[i].is_zero() { F::zero() }
			else { t.enc[i] * base + t.loc[i] }).collect();
		// prover invariant: every step>=1 Q_m row is paid exactly
		// once -- carried rows by q_i, chunk matches (and the
		// wrap/sentinel borders) by the join. Halo-straddle
		// duplicates are two Q_m rows (no dedup upstream), one
		// paid by each side.
		let nz = |v: &Vec<F>| v.iter()
			.filter(|x| !x.is_zero()).count();
		assert!(nz(&vec1) + nz(&vec2) == nz(&vec3),
			"neo union: q_i {} + jr {} != q_m {} (rows counted \
			twice or dropped)", nz(&vec1), nz(&vec2), nz(&vec3));
		let prf = gen_union_prf(&vec1, &vec2, &vec3,
			"neo_union")?;
		let g = |n: &str| prf.lock().unwrap().get_container(n)
			.unwrap().lock().unwrap().to_vec()[0];
		Ok(vec![g("b_left_more_zero"), g("diff_zero")])
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
		info: &SubsigStepStore, l_pat: Vec<F>, l_id: Vec<F>,
		l_loc: Vec<F>, hm_loc: &HashMap<F, Vec<(F, F)>>,
		carried: &StepQueue<F>, default_min: F, job_id: usize)
	-> Result<(NeoCore<F>, Arc<Mutex<Container<F>>>,
		Arc<Mutex<Container<F>>>), Error> {
		let mut t = g.gen_qm_table(info, false)?;
		t.fill_nonaggr(info, default_min);
		let rid = Self::gen_rid_native(&t);
		let cid = Self::gen_cid_native(&t);
		// NewP3: capacity-only shapes (fold-invariant across files
		// with different obligation sets), mirroring gen's 8_C pad:
		// K dummy-0 subsig slots; s_enc padded to the wrap budget.
		// All consumers mask zero slots.
		let mut subsig_nat = g.subsigs.clone();
		let (mut s_enc, s_pat) = Self::gen_store_rows(&subsig_nat,
			info);
		let k_slots = g.capacity.subsigs;
		let s_cap = StepQueueNeo::<F>::wrap_budget(&g.capacity,
			info);
		//normally CapErr'd upstream (new_nonaggr's seed bound); kept
		//bumpable here so a direct-construction path stays tunable
		//instead of panicking unparseably past determine_config.
		if subsig_nat.len() > k_slots {
			return Err(Error::CapErr(vec![(format!(
				"neo_subsig_slots, b_igc: {}", g.b_igc),
				subsig_nat.len())]));
		}
		subsig_nat.resize(k_slots, F::zero());
		if s_enc.len() > s_cap {
			return Err(Error::CapErr(vec![(format!(
				"dis_adv::neo_wrap_subsigs, b_igc: {}", g.b_igc),
				StepQueueNeo::<F>::wrap_subsigs_for(info,
					s_enc.len()))]));
		}
		s_enc.resize(s_cap, F::zero());
		let mtbl_qr = Self::gen_mtbl_qr_nonaggr(&t, &rid,
			&subsig_nat);
		let mtbl_qc = Self::gen_mtbl_qc(&t, &cid);
		// JOIN RESULT temp table; conservative row budget = the
		// Q_m capacity (strictly larger: each JR block fits in
		// its Q_m group; seed groups are Q_m-only).
		let jr = Self::gen_jr_table(&s_enc, &s_pat, hm_loc,
			t.enc.len())?;
		// no-show pats + absence-gap advice
		let ns_pat = Self::gen_ns_pat(&s_pat, &l_pat,
			s_enc.len());
		let (d_ns_lo, d_ns_hi, mtbl_ns) =
			Self::gen_ns_advice(&ns_pat, &l_pat);
		// membership m-table over the JOIN RESULT view: queries
		// = JR nonzero rows; targets = L ++ no-show sentinel
		// pairs
		let rb = read_global_config().range2_bit;
		let (f_b, f_sh) = (F::from(1u64 << rb),
			F::from(1u128 << (2 * rb)));
		let f_t2 = F::from((1u64 << rb) + ((1u64 << rb) - 1));
		let one = F::one();
		let qry_tm: Vec<F> = (0..jr.enc.len()).map(|i|
			jr.pat[i] * f_sh + jr.id[i] * f_b + jr.loc[i])
			.collect();
		let sel_qry: Vec<F> = jr.enc.iter().map(|e|
			if e.is_zero() { F::zero() } else { one })
			.collect();
		let mut lk_tm: Vec<F> = (0..l_pat.len()).map(|i|
			l_pat[i] * f_sh + l_id[i] * f_b + l_loc[i])
			.collect();
		let mut sel_lk = vec![one; l_pat.len()];
		let sel_d: Vec<F> = ns_pat.iter().map(|p|
			if p.is_zero() { F::zero() } else { one })
			.collect();
		lk_tm.extend(ns_pat.iter().map(|p| *p * f_sh));
		sel_lk.extend(sel_d.clone());
		lk_tm.extend(ns_pat.iter().map(|p| *p * f_sh + f_t2));
		sel_lk.extend(sel_d);
		let mtbl_tm = gen_m_table_cond(&qry_tm, &sel_qry,
			&lk_tm, &sel_lk);
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
		utils::consts::QC_SAT[g.b_igc as usize].record(qc_rows, n_qc);
		let col = |ct: &Arc<Mutex<Container<F>>>, name: &str| {
			ct.lock().unwrap().get_container(name).unwrap()
				.lock().unwrap().to_vec()
		};
		let (qi_enc, qi_loc) = (col(&ct_qi, "encoded"),
			col(&ct_qi, "locs"));
		let union_prf = Self::gen_union_scalars(&t, &jr, &qi_enc,
			&qi_loc, &subsig_nat)?;
		let nat = NeoCore {
			qi_enc, qi_loc,
			qc_enc: col(&ct_qc, "encoded"),
			qc_loc: col(&ct_qc, "locs"),
			t, l_pat, l_id, l_loc, subsig_nat, s_enc, mtbl_qr,
			mtbl_tm, ns_pat, d_ns_lo, d_ns_hi, mtbl_ns,
			acc_out: vec![], mtbl_acc: vec![], mtbl_qc,
			union_prf, jr };
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
	#[cfg(any())] // M8_NEW P1: replaced by assert_carry/
	// assert_fwd_pruning/assert_seed_anchors/assert_qm_lookups
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
	#[cfg(any())] // M8_NEW P1: replaced by assert_join_locations
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

	#[cfg(any())] // M8_NEW P1: replaced by assert_join_locations
	// + assert_verdict_aggr
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
	#[cfg(any())] // M8_NEW P1: replaced by assert_neo_aggr
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
	/// Builds the QC address column: cid gives each CARRIED row its
	/// position inside its group, so a (enc, cid = 1, loc) query
	/// returns that group's least carried loc. NON-AGGRESSIVE only
	/// -- the aggressive arm keeps no carry queue to address.
	///
	/// Advice names: none, cid is derived rather than committed:
	/// cid[i] = (1 - grp_start[i]) * (cid[i-1] + is_wrap + is_c),
	/// so it resets to 0 at each group start and then advances on
	/// the rows the QC target admits, the two wraps and C. FP, BP
	/// and SP rows hold the previous value, and that is what keeps
	/// them out of the target: no query can address them.
	///
	/// Checks: none of its own. The column is sound because of
	/// where its inputs come from -- grp_start is forced by
	/// assert_neo_wf, is_wrap and is_c by assert_neo_selectors,
	/// which also leaves pads cat-free, so the increment stays in
	/// {0, 1} and the chain cannot run backwards.
	///
	/// EXAMPLE group a2 = [0w, 21C, 111SP, maxw] -> cid 0, 1, 1, 2,
	/// so the (enc_a2, 1, .) query lands on 21, the kept minimum.
	///  - CHEAT tag 21 SP as well, to prune the whole group: no row
	///    of a2 is then carried, cid 1 is the max-wrap, and
	///    assert_singleton_pruning's kept-minimum certificate
	///    underflows RANGE2.
	/// COST: 1cs/row, reported inside PERF 61081.6.
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

	/// Binds the si companion columns that exist only in the
	/// non-aggressive arm: the BP and SP witness columns of T_qm,
	/// plus the JOIN-RESULT table's pat. It uses the same
	/// one-constraint pin as assert_neo_si_pins, which owns the
	/// base columns.
	///
	/// Advice names (per row):
	///   is_fz0  zero-indicator bit, fz == 0. It selects which of
	///           the two proofs of enc_fz applies, since step 0 of
	///           a subsig is the artificial seed key and the DB
	///           carries no subsig fact under it;
	///   m_sp0   is_sp * is_fz0, the by-construction branch;
	///   m_spfz  is_sp - m_sp0, the from-the-DB branch -- free,
	///           because the two branches partition the SP rows.
	///
	/// Checks, per T_qm row:
	///  (1) BP rows: si_bp_prev and si_rg2_next carry
	///      tag(enc_next, PREV_ENCODED / RG_END) and bp_prev_val
	///      == enc, so the outer pair states prev(enc_next) = enc;
	///  (2) SP rows: si_fz carries tag(enc, FZ) beside the value
	///      fz, so the frozen step is read out of the DB;
	///  (3) SP rows, frozen step 0: enc_fz == subsig * 2^(4rb),
	///      computed rather than looked up;
	///  (4) SP rows, frozen step >= 1: si_fz_step carries a step
	///      tag of enc_fz beside the value fz, and si_fz_sub
	///      carries tag(enc_fz, SUBSIG) beside the value subsig --
	///      together, enc_fz is the enc of (this subsig, step fz);
	/// and once over the JOIN-RESULT table:
	///  (5) every non-pad JR row: si_pat == tag(enc, PAT), so a
	///      block's pat is the pat the DB gives that block's OWN
	///      enc.
	///
	/// EXAMPLE, why (5) matters. Without it a block for store row
	/// (enc_A, pat_A) may carry pat_B together with si_pat =
	/// tag(enc_B, PAT) for any other store row B: that pair is a
	/// genuine DB fact, so the outer lookup passes. Pick a B whose
	/// pattern has no match in this chunk and the block becomes the
	/// no-show sentinel pair -- subsig A's step looks match-free,
	/// its chain dies, and the file is falsely discharged. The
	/// aggressive arm never had this gap: its join view IS T_qm,
	/// whose pat assert_neo_si_pins pins.
	///  - CHEAT name a step of another subsig as enc_next: (1) then
	///    needs the pair (tag(enc_next, PREV), enc), and the DB
	///    holds no such pair.
	///  - CHEAT freeze a step that never froze: fz comes from the
	///    DB by (2) and enc_fz by (3) or (4), so a row cannot
	///    choose its own freeze point.
	///  - CHEAT claim fz == 0 to skip (4): is_fz0 is forced to 0
	///    whenever fz is nonzero, so the claim needs fz == 0
	///    committed -- and fz is the DB's.
	/// PARAMS: sel_jr = the non-pad bits of the JR table, built by
	/// the caller, which also feeds them to the join's membership
	/// selector, so they are not paid for twice.
	/// COST: ~13*n + |jr|. PERF 61081.6.
	fn assert_neo_si_pins_nonaggr(
		cs: ConstraintSystemRef<F>,
		t: &QmTable<F>, v: &QmVars<F>, sel: &NeoSel<F>,
		jr: &JrVars<F>, sel_jr: &[FpVar<F>],
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = v.enc.len();
		debug_assert!(sel_jr.len() == jr.enc.len(),
			"neo jr selector length");
		let rb = read_global_config().range2_bit;
		let f1 = F::from(1u64 << rb);
		let f_r2 = F::from(RANGE2);
		// tag constants pre-shifted by RANGE2 for check_si_pin
		// (assert_neo_si_pins explains the pin's shape).
		let tc = |cid: u32| new_const_var(&cs,
			si_tag_base::<F>(cid) - f_r2);
		let c_prev = tc(ID_ENCODED_PREV_ENCODED);
		let c_rgend = tc(ID_ENCODED_RG_END);
		let c_fz = tc(ID_ENCODED_FZ);
		let c_sub = tc(ID_ENCODED_SUBSIG);
		let c_pat = tc(ID_ENCODED_PAT);
		// check (4) admits either of two step tags, so it cannot
		// use the single-tag pin and these two stay unshifted.
		let c_n = new_const_var(&cs,
			si_tag_base::<F>(ID_ENCODED_NORMAL_STEP));
		let c_l = new_const_var(&cs,
			si_tag_base::<F>(ID_ENCODED_LAST_STEP));
		let c_rg2t = new_const_var(&cs, f_r2);
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
		let na_t = &t.nonaggr;
		let na_v = &v.nonaggr;
		// STRONG bit, not the 1cs gate: only "is_fz0 = 1 => fz = 0"
		// is needed for soundness, but a gate bit is left
		// unconstrained wherever fz = 0, and then m_sp0 and m_spfz
		// below would no longer be boolean.
		let is_fz0 = gen_zero_bits(&cs, &na_t.fz, &na_v.fz)?;
		for i in 0..n {
			// --- check (1): BP witnesses (3cs) ---
			// A subsig's steps form a chain, so each enc has one
			// predecessor and one successor: the DB pair
			// prev(enc_next) = enc leaves only one enc_next.
			check_si_pin(&sel.is_bp[i], &na_v.enc_next[i],
				&na_v.si_bp_prev[i], &c_prev, &c_rg2t,
				"neo si_bp_prev pin")?;
			check_si_pin(&sel.is_bp[i], &na_v.enc_next[i],
				&na_v.si_rg2_next[i], &c_rgend, &c_rg2t,
				"neo si_rg2_next pin")?;
			check_prod_eq(&sel.is_bp[i], &v.enc[i],
				&na_v.bp_prev_val[i], "neo bp_prev_val bind")?;
			// --- check (2): the frozen step is a DB fact (1cs) ---
			check_si_pin(&sel.is_sp[i], &v.enc[i],
				&na_v.si_fz[i], &c_fz, &c_rg2t, "neo si_fz pin")?;
			// --- checks (3) and (4): identify enc_fz (7cs) ---
			// An SP row claims its group is frozen at step fz, and
			// assert_singleton_pruning proves that by asking what
			// the group of step fz carries. It therefore needs
			// enc_fz, the key of (this subsig, step fz). That
			// column is advice with si 0, so these checks are what
			// tie it down. is_fz0 picks which of the two proofs
			// applies; m_sp0 and m_spfz partition the SP rows, so
			// exactly one runs per row and the second mask is a
			// subtraction rather than a product.
			//  fz == 0: the key is the seed key, so it is COMPUTED
			//    as subsig * 2^(4rb) -- the encoding places subsig
			//    in the top field with step 0 below it. No lookup
			//    is possible in this case: the DB files no subsig
			//    fact under a step-0 key.
			//  fz >= 1: two DB facts about enc_fz are read back --
			//    its step must equal fz, and its subsig must equal
			//    this row's subsig. A (subsig, step) pair has one
			//    key, so the two together leave a single enc_fz.
			//    The step pin accepts either the NORMAL or the
			//    LAST tag (t1 * t2 = 0), since the DB files a step
			//    under exactly one of them.
			// EXAMPLE: an SP row at step 7 of subsig a whose DB
			// freeze point is fz = 5 must give enc_fz = enc(a, 5).
			// Naming enc(b, 5) instead needs the pair
			// (tag(enc(b,5), SUBSIG), a) in the DB, and that fact
			// reads b, not a.
			let m_sp0 = &sel.is_sp[i] * &is_fz0[i];
			check_prod_zero(&m_sp0,
				&(&na_v.enc_fz[i] - &(&v.subsig[i] * &c_sh4)),
				lc!(), "neo enc_fz seed pin")?;
			let m_spfz = &sel.is_sp[i] - &m_sp0;
			let t1 = &(&na_v.si_fz_step[i] - &c_n)
				- &na_v.enc_fz[i];
			let t2 = &(&na_v.si_fz_step[i] - &c_l)
				- &na_v.enc_fz[i];
			check_prod_zero(&m_spfz, &(&t1 * &t2), lc!(),
				"neo si_fz_step 2-tag pin")?;
			check_prod_eq(&m_spfz, &na_v.fz[i],
				&na_v.fz_step_val[i], "neo fz_step_val bind")?;
			check_si_pin(&m_spfz, &na_v.enc_fz[i],
				&na_v.si_fz_sub[i], &c_sub, &c_rg2t,
				"neo si_fz_sub pin")?;
			check_prod_eq(&m_spfz, &v.subsig[i],
				&na_v.fz_sub_val[i], "neo fz_sub_val bind")?;
			// NOTE: off this branch si_fz_step needs no pin. The
			// pair (si_fz_step, fz_step_val) is read by nothing
			// else, the bind above already forces fz_step_val = 0
			// there, and the outer lookup still confines si_fz_step
			// to a pair the DB holds. The advice writes RANGE2.
		}
		// --- check (5): a JR block's pat belongs to its enc ---
		// This arm's join view is the JR table rather than T_qm, so
		// T_qm's own pat pin does not reach it: the constraint
		// below is the only thing tying a block's pat to its enc.
		for k in 0..jr.enc.len() {
			check_si_pin(&sel_jr[k], &jr.enc[k], &jr.si_pat[k],
				&c_pat, &c_rg2t, "neo jr si_pat pin")?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61081.6: block=si_pins_nonaggr cs={} pred={}",
			cs.num_constraints() - n0,
			13 * n + jr.enc.len()));
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
	#[cfg(any())] // M8_NEW P1: replaced by the certificate fns
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
	#[cfg(any())] // M8_NEW P1: replaced by assert_join_locations
	// + assert_qm_union + assert_carry
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
	#[cfg(any())] // M8_NEW P1: replaced by assert_neo_nonaggr
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
//   M8_NEW: redesigned circuit core -- join / union / certs /
//   shared lookups / verdict (approved interfaces; bodies P2)
// ============================================================

/// Union proof advice for assert_qm_union: the two zero-count
/// reconciliation scalars of the multiset identity
/// (verify_union_prf, db.rs).
pub(crate) struct QmUnionAdvice<F: PrimeField + ColEle> {
	pub b_left_more_zero: FpVar<F>,
	pub diff_zero: FpVar<F>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// BOTH modes -- THE join gadget (paper's merge JOIN term,
	/// fig:prune step 1): proves the view (enc, pat, id, loc)
	/// is exactly "queried groups JOIN pat_loc". No
	/// reachability here -- that belongs to the certificates.
	/// CALLERS:
	///   aggr:    view = Q_m itself (no carry: Q_m IS the join
	///            result), sel_q = 1 - is_step0 (pads have
	///            step 0, so one bit masks pads + seed group),
	///            b_ext_wf = true;
	///   nonaggr: view = JrTable (Q_m mixes in carried rows,
	///            so the join lives in a temp table;
	///            assert_qm_union links it into Q_m), sel_q =
	///            1 - is_zero(enc), b_ext_wf = false.
	///
	/// RELATION TO THE PAPER'S TABLE-JOIN GADGETS (Sec 6.2/
	/// 6.3; verify_tbl_left_join / _wide): those prove
	/// "output = tbl1 join tbl2" on a materialized output
	/// table from exactly three obligations -- the same three
	/// here:
	///   (J-W) output well-formed over its compound key: each
	///       key block walks consecutive ids, bracketed by
	///       the loc-0 / loc-max dummy rows. ONE skeleton
	///       call (assert_well_formed_sorted, non-relaxed),
	///       run here iff b_ext_wf = false. The aggr view's
	///       owner is assert_neo_wf S1 -- the IDENTICAL call
	///       on the same three columns (re-running it would
	///       pay 3n twice).
	///   (J-B) key side bound to tbl1 (= store join db): enc
	///       is a store group key (wf S4 uniqueness for Q_m;
	///       the JR view inherits it through assert_qm_union,
	///       whose sentinels must land on a real group's
	///       wraps), and pat is welded to enc per row by an
	///       si_pat companion (Q_m si-pins / JrTable.si_pat).
	///       Without that weld a block could join a FOREIGN
	///       pat's locations under this enc and hide the true
	///       pat's matches.
	///   (J-M) value side bound to tbl2 (= L = pat_loc): THIS
	///       fn's one batch logup -- every selected row's
	///       (pat, id, loc) triple is in pat_loc (fixed-base
	///       encode_cols_var; legal: all three range-bound).
	/// Per block of pat p: no fabrication (each triple exists
	/// in L) and no omission (the border forces the last loc
	/// = max, whose only L row for p has id cnt+1; the +1
	/// chain then covers 0..cnt+1, the FULL block). A pat
	/// shared by several groups needs no bookkeeping: each
	/// block brackets the whole list.
	///
	/// Step-0 rows are EXEMPT: the seed match is artificial,
	/// absent from pat_loc. Unfakeable: step is DB-bound on
	/// every Q_m row (si_step); a step-0 block smuggled into
	/// the JR view dies in assert_qm_union (the whole step-0
	/// group is masked there, so its rows find no partner).
	/// SOUNDNESS DEPENDENCY (aggr view): wraps are queried,
	/// so wrap rows' pat must be DB-bound via si_pat
	/// (push_wrap emits the variable si on step>=1 wraps;
	/// si_pins pins (real+wrap)*(1-is_step0) rows).
	///
	/// EXAMPLE (aggr view). Store: subsig 3 = {step 1: pat 2,
	/// step 2: pat 5}; chunk matches: pat 2 at {17, 25},
	/// pat 5 none. INPUTS:
	///   pat_loc = (l_pat, l_id, l_loc), 6 rows (fsm table
	///   copy; per pat: ids 0..cnt+1, loc-0/loc-max
	///   sentinels):
	///     l_pat = [2,  2,  2,   2,  5,   5]
	///     l_id  = [0,  1,  2,   3,  0,   1]
	///     l_loc = [0, 17, 25, max,  0, max]
	///   m_tm = [1, 1, 1, 1, 1, 1]
	///   view = Q_m cols; sel_q = 1 - is_step0 (E0 = seed
	///   group, E1 = step 1, E2 = step 2):
	///     row grp pat id loc  cat   sel_q  query
	///     r0  E0   0  0    0  wrap    0    --
	///     r1  E0   0  1    1  C       0    --
	///     r2  E0   0  2  max  wrap    0    --
	///     r3  E1   2  0    0  wrap    1    (2,0,0)   in L
	///     r4  E1   2  1   17  C       1    (2,1,17)  in L
	///     r5  E1   2  2   25  FP      1    (2,2,25)  in L
	///     r6  E1   2  3  max  wrap    1    (2,3,max) in L
	///     r7  E2   5  0    0  wrap    1    (5,0,0)   in L
	///     r8  E2   5  1  max  wrap    1    (5,1,max) in L
	/// All queries found -> SAT. E2 = the matchless-pat case.
	/// ATTACKS: drop r5 -> r6 slides to id 2, query (2,2,max)
	/// not in L; fabricate (2,?,30) -> no such L row; retag
	/// E1's wraps to pat 5 to fake it empty -> si_pat pin
	/// fails; relabel r5's step to 0 to dodge the query ->
	/// si_step pair fails; wrong m_tm -> the logup identity
	/// itself fails. (The JR-view example lives on
	/// gen_jr_table.)
	/// NO-SHOW EXTENSION: a store pat with zero matches has a
	/// sentinel-only block; its two queries (p,0,0)/(p,1,max)
	/// hit targets derived FREE from the committed ns_pat col
	/// (p*2^2rb and p*2^2rb + 2^rb + max), eligible only where
	/// sel_ns = 1 -- and assert_ns_gap proves exactly those
	/// pats absent from L, so a matched pat cannot fake an
	/// empty block through them.
	/// COST: (b_ext_wf ? 2 : 5)*n + 3*|L|. PERF 61082.1.
	fn assert_join_locations(
		cs: ConstraintSystemRef<F>,
		view: (&[FpVar<F>], &[FpVar<F>], &[FpVar<F>],
			&[FpVar<F>]), // enc, pat, id, loc
		sel_q: &[FpVar<F>],// membership query mask
		b_ext_wf: bool,    // (J-W) owned by caller's table wf?
		pat_loc: (&[FpVar<F>], &[FpVar<F>], &[FpVar<F>]),
		                   // committed L: l_pat, l_id, l_loc
		ns_pat: &[FpVar<F>],
		                   // no-show pats (sentinel targets)
		sel_ns: &[FpVar<F>],
		                   // (ns_pat != 0) bits, caller-built
		m_tm: &[FpVar<F>], // membership multiplicity advice,
		                   //   len |L| + 2*|ns|
		r1: &FpVar<F>,     // wf skeleton challenge
		r2: &FpVar<F>,     // lookup challenge = wtns.msg2[1]
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let (enc, pat, id, loc) = view;
		// -- 1. (J-W) bracket skeleton, unless the caller's
		//    table wf already runs the identical call --
		if !b_ext_wf {
			assert_well_formed_sorted(cs.clone(),
				&enc.to_vec(), &id.to_vec(), &loc.to_vec(),
				None, None, None, None, r1.clone(),
				read_global_config().range2_bit)?;
		}
		// -- 2. (J-M) membership logup into pat_loc ++ no-show
		//    sentinel targets --
		let (l_pat, l_id, l_loc) = pat_loc;
		if l_pat.is_empty() {
			// empty-L degenerate (empty-store igc): no query
			// and no no-show claim may exist at all.
			let c_zero = new_const_var(&cs, F::zero());
			for s in sel_q.iter().chain(sel_ns.iter()) {
				check_eq(s, &c_zero, "neo join empty-L")?;
			}
			return Ok(());
		}
		let qry = encode_cols_var(&vec![pat.to_vec(),
			id.to_vec(), loc.to_vec()], &vec![0, 1, 2]);
		let mut lk = encode_cols_var(&vec![l_pat.to_vec(),
			l_id.to_vec(), l_loc.to_vec()], &vec![0, 1, 2]);
		let c_one = new_const_var(&cs, F::one());
		let mut tsel = vec![c_one.clone(); l_pat.len()];
		let rb = read_global_config().range2_bit;
		let c_sh = new_const_var(&cs,
			F::from(1u128 << (2 * rb)));
		let c_t2 = new_const_var(&cs,
			F::from((1u64 << rb) + ((1u64 << rb) - 1)));
		for k in 0..ns_pat.len() {
			lk.push(&ns_pat[k] * &c_sh);
			tsel.push(sel_ns[k].clone());
		}
		for k in 0..ns_pat.len() {
			lk.push(&(&ns_pat[k] * &c_sh) + &c_t2);
			tsel.push(sel_ns[k].clone());
		}
		assert_logup_cond(cs.clone(), &qry, &sel_q.to_vec(),
			&lk, &tsel, &m_tm.to_vec(), r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61082.1: block=join ext_wf={} cs={} pred={}",
			b_ext_wf, cs.num_constraints() - n0,
			(if b_ext_wf { 2 } else { 5 }) * enc.len()
				+ 3 * (l_pat.len() + 2 * ns_pat.len())));
		Ok(())
	}

	/// Absence proof for the no-show pats: each nonzero ns_pat
	/// entry p is straddled by an ADJACENT pair (g1, g2) of the
	/// sorted l_pat column -- g1 < p < g2 with nothing between
	/// them -- so p has no match in this chunk. g1 = p-1-d_lo,
	/// g2 = p+1+d_hi (free; RANGE2-bound d_* keep the
	/// inequalities strict in the integers; a wrapped g1 finds
	/// no target). The pair packs with the CHALLENGE
	/// (g1 + r1*g2), NOT fixed-base: g2 is a derived sum
	/// reaching 2^(rb+1), and fixed-base would let
	/// (p-1, p+2^rb) collide with the in-block pair (p, p).
	/// Targets, free from committed l_pat: bottom pair
	/// (0, l_pat[0]), the adjacent pairs, top pair
	/// (l_pat[last], 2^rb). Membership-target eligibility and
	/// this proof share ONE selector (sel_ns), so every usable
	/// sentinel target is absence-proven.
	/// COST: ~4*(|L| + |ns|). PERF 61082.3.
	fn assert_ns_gap(
		cs: ConstraintSystemRef<F>,
		ns_pat: &[FpVar<F>],  // no-show pats (front-0-padded)
		sel_ns: &[FpVar<F>],  // (ns_pat != 0), caller-built
		d_ns_lo: &[FpVar<F>], // gap below, RANGE2-bound advice
		d_ns_hi: &[FpVar<F>], // gap above, RANGE2-bound advice
		l_pat: &[FpVar<F>],   // committed pat_loc pat col
		                      //   (sorted by the fsm-side wf)
		mtbl_ns: &[FpVar<F>], // hit count per pair, len |L|+1
		r1: &FpVar<F>,        // pair-pack challenge
		r2: &FpVar<F>,        // lookup challenge = wtns.msg2[1]
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = l_pat.len();
		let c_zero = new_const_var(&cs, F::zero());
		if n == 0 {
			// empty-store degenerate: no no-show claims.
			for s in sel_ns {
				check_eq(s, &c_zero, "neo ns empty-L")?;
			}
			return Ok(());
		}
		let c_one = new_const_var(&cs, F::one());
		let c_top = new_const_var(&cs,
			F::from(1u64 << read_global_config().range2_bit));
		// queries: g1 + r1*g2 (1 mul each; masked rows carry
		// garbage, gated out by sel_ns)
		let qry: Vec<FpVar<F>> = (0..ns_pat.len()).map(|k| {
			let g1 = &(&ns_pat[k] - &c_one) - &d_ns_lo[k];
			let g2 = &(&ns_pat[k] + &c_one) + &d_ns_hi[k];
			&g1 + &(&g2 * r1)
		}).collect();
		// targets: bottom, adjacent pairs, top (1 mul each)
		let mut tgt: Vec<FpVar<F>> = Vec::with_capacity(n + 1);
		tgt.push(&l_pat[0] * r1);
		for i in 0..n - 1 {
			tgt.push(&l_pat[i] + &(&l_pat[i + 1] * r1));
		}
		tgt.push(&l_pat[n - 1] + &(&c_top * r1));
		let ones = vec![c_one.clone(); tgt.len()];
		assert_logup_cond(cs.clone(), &qry, &sel_ns.to_vec(),
			&tgt, &ones, &mtbl_ns.to_vec(), r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61082.3: block=ns_gap cs={} pred={}",
			cs.num_constraints() - n0,
			4 * (n + ns_pat.len())));
		Ok(())
	}

	/// Build the shared predecessor view: 3 muls/row for the two
	/// keys + the z_loc1 bits (2cs strong / 1cs gate-only).
	fn gen_pred_view(
		cs: &ConstraintSystemRef<F>, t: &QmTable<F>,
		v: &QmVars<F>, b_aggr: bool, r1: &FpVar<F>,
	) -> Result<PredView<F>, SynthesisError> {
		let r1sq = r1 * r1;
		let n = v.enc.len();
		let mut key1 = Vec::with_capacity(n);
		let mut key2 = Vec::with_capacity(n);
		for i in 0..n {
			let t_id = r1 * &v.prev_id1[i];
			let t_p1 = &r1sq * &v.prev_loc1[i];
			let t_p2 = &r1sq * &v.prev_loc2[i];
			key1.push(&(&v.enc_prev[i] + &t_id) + &t_p1);
			key2.push(&(&(&v.enc_prev[i] + &t_id) + r1) + &t_p2);
		}
		let z_loc1 = if b_aggr {
			gen_gate_bits(cs, &t.prev_loc1, &v.prev_loc1)?
		} else {
			gen_zero_bits(cs, &t.prev_loc1, &v.prev_loc1)?
		};
		Ok(PredView { key1, key2, z_loc1 })
	}

	/// Verifies the CARRY labels of Q_m: a row tagged C really
	/// survives, and the committed carry-out wire q_c is exactly
	/// that set of rows. C is the paper's Q_c certificate
	/// (fig:prune step 3) -- some location at the previous step
	/// reaches this one. Step-0 rows (the seed) are carried by
	/// definition, and FP/BP/SP rows are not touched here.
	///
	/// Two checks, both masked to is_c:
	///  (1) reach window: gap = |loc - prev_loc1| lies in
	///      [rg1, rg2] via the RANGE2 advice d_c1/d_c2, and the
	///      named predecessor exists -- that query is buffered
	///      for assert_qm_lookups to discharge against the
	///      carried rows;
	///  (2) projection q_c = sigma_C(Q_m), a permutation check;
	///      NONAGGR only, the aggressive arm commits no carry.
	///
	/// EXAMPLE (fig-14): C row a7:101 with pred a6:96, rg{1,9}
	/// gives gap 5, d_c1 = 4, d_c2 = 4, and q_c holds (a7, 101).
	///
	/// PARAMS: b_aggr selects the arm; pv = shared predecessor
	/// view (in aggr, fwd_pruning's lower-neighbor query rides
	/// this fn's fused key1 push).
	/// CONSUMERS of q_c: the folding driver binds it to the NEXT
	/// chunk's q_i (whose union step rebuilds Q_m from it), and
	/// compute_sig reads the final chunk's q_c for the verdict.
	fn assert_carry(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,  // loc, prev_loc1, rg1, rg2, d_c1, d_c2,
		                 //   enc
		sel: &NeoSel<F>, // is_c, is_fp, is_seed, b_bwd_row
		b_aggr: bool,    // arm: bwd windows + no ban + no q_c
		q_c: (&[FpVar<F>], &[FpVar<F>], &[F]),
		                 // carry-out transport (enc vars, loc
		                 //   vars, enc native); EMPTY in aggr
		pv: &PredView<F>,
		buf: &mut QmQueryBuf<F>,
		                 // CARRIED-target instance
		r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.enc.len();
		let rb = read_global_config().range2_bit;
		let c_one = new_const_var(&cs, F::one());
		let c_base = new_const_var(&cs, F::from(1u64 << rb));
		for i in 0..n {
			// --- (1) reach window (2cs, +1cs non-aggr) ---
			// sel_c = non-seed C rows; free: the seed pin makes
			// is_seed exact (see NeoSel::is_seed).
			let sel_c = &sel.is_c[i] - &sel.is_seed[i];
			// non-aggr is forward-only (no backward subsigs), so
			// the orientation select is an aggressive-arm cost.
			let gap = if b_aggr {
				better_select(&sel.b_bwd_row[i],
					&(&qm.prev_loc1[i] - &qm.loc[i]),
					&(&qm.loc[i] - &qm.prev_loc1[i]))
			} else { &qm.loc[i] - &qm.prev_loc1[i] };
			check_prod_zero(&sel_c,
				&(&(&gap - &qm.rg1[i]) - &qm.d_c1[i]), lc!(),
				"neo C d1")?;
			check_prod_zero(&sel_c,
				&(&(&qm.rg2[i] - &gap) - &qm.d_c2[i]), lc!(),
				"neo C d2")?;
			// NONAGGR: the pred cannot be the previous group's
			// 0-wrap. That wrap is a legal carried target (cid 0),
			// so a fake (enc_prev, 0, 0) pred passes any window
			// with loc <= rg2; the planted low C row then becomes
			// its group's kept minimum and singleton pruning drops
			// the live chain above it. Aggr has no SP layer, and
			// over-claiming C there only feeds acc_out, so it
			// keeps the M6 stream.
			if !b_aggr {
				check_prod_zero(&sel_c, &pv.z_loc1[i], lc!(),
					"neo C pred not 0-wrap")?;
			}
			// aggr: fwd_pruning's lower-neighbor query is the
			// SAME key; one fused slot serves both (exclusive
			// cats keep the fused sel in {0,1}).
			if b_aggr {
				buf.push(pv.key1[i].clone(),
					&sel_c + &sel.is_fp[i]);
			} else {
				buf.push(pv.key1[i].clone(), sel_c);
			}
		}
		// --- (2) projection q_c = sigma_C(Q_m) ---
		// is_c identifies the carry set only INSIDE this circuit;
		// the fold links chunks positionally, so the set must
		// leave as a dense fixed-size container. Multiplicity is
		// pinned at 1 per C row, so a PERMUTATION check does what
		// a lookup would, cheaper: two grand products over
		// pack(loc, enc) = loc + enc*2^rb (free, constant base),
		// masked rows contributing the neutral factor 1.
		// EXAMPLE: dropping C row a3:27 from q_c leaves the left
		//   product one factor richer -> UNSAT; smuggling BP row
		//   a6:73 in adds a factor the C set cannot match.
		if !b_aggr {
			let z_qc = gen_zero_bits(&cs, q_c.2, q_c.0)?;
			let sq: Vec<FpVar<F>> = z_qc.iter()
				.map(|z| &c_one - z).collect();
			let lhs = multiset_prod_2col(cs.clone(), &qm.loc,
				&qm.enc, &sel.is_c, r2, &c_base);
			let rhs = multiset_prod_2col(cs.clone(), q_c.1,
				q_c.0, &sq, r2, &c_base);
			check_eq(&lhs, &rhs, "neo carry-out bijection")?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.4: block=carry cs={} pred={}",
			cs.num_constraints() - n0,
			if b_aggr { 3 * n } else { 5 * n + 4 * q_c.0.len() }));
		Ok(())
	}

	/// Verifies the FWD-PRUNE labels of Q_m: a row tagged FP is
	/// unreachable -- two rank-ADJACENT reachable rows at the
	/// previous step straddle its window (paper fig:prune step 3,
	/// Q_fp certificate: l1 + rg2 < loc < l2 + rg1, fwd form).
	/// Orientation costs one mul, in the aggressive arm only.
	///
	/// Three checks, all masked to is_fp:
	///  (1) below: loc - prev_loc1 - rg2 - 1 >= 0 via the RANGE2
	///      advice d_below_lo; skipped when prev_loc1 is the
	///      0-wrap (nothing reachable lies below);
	///  (2) above: prev_loc2 + rg1 - loc - 1 >= 0 via d_above_lo;
	///      skipped when prev_loc2 is the max-wrap;
	///  (3) the neighbor pair exists rank-adjacent in Q_r:
	///      pv.key1 / pv.key2 go to the REACHABLE buffer.
	///
	/// EXAMPLE (fig-14): FP a7:131 vs neighbors 96/141, rg{1,9}:
	/// below 131-96-9-1 = 25, above 141+1-131-1 = 10, both >= 0.
	///
	/// ASSUMPTION: chunking keeps loc + rg inside RANGE2 (chunk
	/// len + max window < 2^rb; asserted at the advice fill), so
	/// each diff fits ONE RANGE2 cell -- no overflow limb.
	fn assert_fwd_pruning(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,  // loc, rg1, rg2, prev_loc1, prev_loc2,
		                 //   d_below_lo, d_above_lo
		sel: &NeoSel<F>, // is_fp, b_bwd_row
		b_aggr: bool,
		nat_prev_loc2: &[F],
		pv: &PredView<F>,
		buf: &mut QmQueryBuf<F>,
		                 // REACHABLE-target instance
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.enc.len();
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		// gate-only bit: prev_loc2 == max is the "nothing above"
		// sentinel; a dishonest 0 only re-enables the check.
		let z_pl2 = gen_gate_bits(&cs,
			&nat_prev_loc2.iter().map(|x| f_max - *x)
				.collect::<Vec<F>>(),
			&qm.prev_loc2.iter().map(|x| &c_max - x)
				.collect::<Vec<_>>())?;
		for i in 0..n {
			// fwd-form diffs. ONE mul orients both for bwd rows:
			// the two selects M6 paid for swap the same (rg1,rg2)
			// pair, so u = b_bwd_row*(rg1+rg2) converts below and
			// above at once (+u / -u).
			let e_lo = &(&(&qm.loc[i] - &qm.prev_loc1[i])
				- &qm.rg2[i]) - &c_one;
			let e_hi = &(&(&qm.prev_loc2[i] + &qm.rg1[i])
				- &qm.loc[i]) - &c_one;
			let (e_lo, e_hi) = if b_aggr {
				let u = &sel.b_bwd_row[i]
					* &(&qm.rg1[i] + &qm.rg2[i]);
				(&e_lo + &u, &e_hi - &u)
			} else { (e_lo, e_hi) };
			// (1) + (2): each active diff equals its committed
			// RANGE2 cell (single limb by the doc ASSUMPTION).
			let m_lo = &sel.is_fp[i] * (&c_one - &pv.z_loc1[i]);
			check_prod_zero(&m_lo, &(&e_lo - &qm.d_below_lo[i]),
				lc!(), "neo FP below")?;
			let m_hi = &sel.is_fp[i] * (&c_one - &z_pl2[i]);
			check_prod_zero(&m_hi, &(&e_hi - &qm.d_above_lo[i]),
				lc!(), "neo FP above")?;
			// (3): key1 rides assert_carry's fused slot in aggr
			// (same key, exclusive sels).
			if !b_aggr {
				buf.push(pv.key1[i].clone(),
					sel.is_fp[i].clone());
			}
			buf.push(pv.key2[i].clone(), sel.is_fp[i].clone());
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.5: block=fwd_prune cs={} pred={}",
			cs.num_constraints() - n0,
			(if b_aggr { 6 } else { 5 }) * n));
		Ok(())
	}

	/// Verifies the BWD-PRUNE labels of Q_m: a row tagged BP is
	/// a dead end going forward -- even its farthest reach falls
	/// short of the successor step's least surviving location
	/// (paper fig:prune step 3, Q_bp certificate:
	/// loc + rg2_{i+1} < min_{i+1}). NONAGGR ONLY: the
	/// aggressive arm retags BP rows to C at emission.
	///
	/// Two checks, both masked to is_bp:
	///  (1) min pin: the query (enc_next, 1, w_next) goes to the
	///      CARRIED buffer -- cid 1 is the successor group's
	///      first carried row, its least loc (or the max-wrap
	///      when the group carries nothing);
	///  (2) gap cert: min_eff - loc - rg2_next = d_bp + 1 with
	///      d_bp RANGE2-bound, where min_eff = w_next, or
	///      default_min when w_next is the max-wrap.
	///
	/// EXAMPLE (fig-14): BP a6:73, rg2_next 9; step 7 carries
	/// nothing so w_next = max, min_eff = default_min = 161;
	/// d_bp = 161 - 73 - 9 - 1 = 78.
	///
	/// PARAMS: default_min = last_loc + 1, the least loc any
	/// future chunk can add at step i+1.
	fn assert_bwd_pruning(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,  // loc; nonaggr cols: enc_next, w_next,
		                 //   rg2_next, d_bp
		sel: &NeoSel<F>, // is_bp
		nat_w_next: &[F],
		                 // native w_next (zero-bit hints for the
		                 //   empty-successor branch)
		default_min: &FpVar<F>,
		                 // bound when successor carries nothing
		buf_qc: &mut QmQueryBuf<F>,
		                 // CARRIED-target instance
		r1: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.loc.len();
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		let na = &qm.nonaggr;
		let r1sq = r1 * r1;
		// w_next == max bits, STRONG both ways. EXAMPLE (fig-14,
		// default_min = 161): BP a6:73, rg2_next 9, reach 82.
		//  A) step 7 carries {90, 120}: the min pin forces
		//     w_next = 90; bit 0, min_eff = 90, cert 82 < 90.
		//  B) step 7 carries nothing: its cid-1 row is the
		//     max-wrap, so w_next = max (a sentinel, not a
		//     loc); bit 1 swaps in min_eff = default_min = 161,
		//     cert 82 < 161.
		// A gate-only bit is UNSOUND in case B: claiming "not
		// max" keeps min_eff = max, letting a6:200 (reach 209,
		// still live in the next chunk) be pruned. "= max ->
		// bit = 1" is the load-bearing direction here.
		let z_wmax = gen_zero_bits(&cs,
			&nat_w_next.iter().map(|x| f_max - *x)
				.collect::<Vec<F>>(),
			&na.w_next.iter().map(|x| &c_max - x)
				.collect::<Vec<_>>())?;
		// No terminal ban needed: is_bp forces the si_bp_prev DB
		// fact (tag(enc_next, PREV) -> enc, si_pins_nonaggr), and
		// no PREV fact names a LAST step as its value -- a BP tag
		// on a terminal row has no satisfying enc_next. (Step-0
		// rows DO have one; a BP-tagged seed dies at the NEXT
		// chunk's seed anchor instead, as in legacy.)
		for i in 0..n {
			// (2) min_eff - loc - rg2_next >= 1 via RANGE2
			// advice.
			let min_eff = better_select(&z_wmax[i], default_min,
				&na.w_next[i]);
			check_prod_zero(&sel.is_bp[i],
				&(&(&(&min_eff - &qm.loc[i]) - &na.rg2_next[i])
					- &(&na.d_bp[i] + &c_one)), lc!(),
				"neo BP gap")?;
			// (1) against the carried ranks; si_pins_nonaggr
			// authenticated enc_next as THE successor step, so
			// the pin cannot read a foreign group's minimum.
			buf_qc.push(&(&na.enc_next[i] + r1)
				+ &(&r1sq * &na.w_next[i]),
				sel.is_bp[i].clone());
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.6: block=bwd_prune cs={} pred={}",
			cs.num_constraints() - n0, 5 * n));
		Ok(())
	}

	/// Verifies the SINGLETON-PRUNE labels of Q_m: a row tagged SP
	/// is redundant -- its group is FROZEN (the downstream
	/// singleton step fz already holds a location, so only the
	/// group's least loc matters from here on) and this row sits
	/// strictly above that kept minimum (paper fig:prune step 2).
	/// NONAGGR ONLY: the aggressive arm has no SP category.
	///
	/// Advice names (per-row committed columns; a group = all rows
	/// of one (subsig, step), enc = its key, loc = this row's
	/// location):
	///   w_fz   the least loc the fz group CARRIES into the next
	///          chunk (the max-wrap sentinel when it carries
	///          nothing);
	///   d_fz   RANGE2 diff certifying w_fz < max;
	///   w_kept the least loc the OWN group carries -- the "kept
	///          minimum" that makes this row redundant;
	///   d_kept RANGE2 diff certifying w_kept < loc.
	///
	/// Two certs + two min pins, all masked to is_sp:
	///  (1) freeze cert: max - w_fz - 1 = d_fz -> w_fz is a real
	///      loc, so step fz truly carries -> frozen;
	///  (2) min-dom cert: loc - w_kept - 1 = d_kept -> a strictly
	///      smaller loc of this group survives, so dropping this
	///      row loses nothing;
	///  (3) freeze pin (enc_fz, 1, w_fz) into CARRIED -- w_fz IS
	///      the fz group's least carried loc, not invented;
	///  (4) kept pin (enc, 1, w_kept) into CARRIED -- w_kept IS
	///      the own group's least carried loc.
	///
	/// EXAMPLE (fig-14): group (a, step 2) holds {21, 111},
	/// fz = 5, step 5 carries loc 39.
	///  - honest: SP a2:111 with 21 kept -> w_fz = 39,
	///    d_fz = max - 40; w_kept = 21,
	///    d_kept = 111 - 21 - 1 = 89 -> OK, 111 pruned.
	///  - CHEAT prune-the-minimum: SP a2:21 -> 21 is then not
	///    carried, so the pin gives w_kept >= 111 (or max) and
	///    21 - w_kept - 1 underflows RANGE2 -> UNSAT.
	///  - CHEAT prune-everything: carry no a2 row -> cid-1 is the
	///    max-wrap, w_kept = max -> same underflow -> UNSAT.
	///  - CHEAT prune-unfrozen: step 5 carries nothing ->
	///    w_fz = max, d_fz = max - max - 1 = -1 -> UNSAT.
	fn assert_singleton_pruning(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,  // loc, enc; nonaggr cols: enc_fz, w_fz,
		                 //   d_fz, w_kept, d_kept
		sel: &NeoSel<F>, // is_sp
		buf_qc: &mut QmQueryBuf<F>,
		                 // CARRIED-target instance
		r1: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.loc.len();
		let rb = read_global_config().range2_bit;
		let f_max = F::from(((1u64 << rb) - 1) as u64);
		let c_max = new_const_var(&cs, f_max);
		let c_one = new_const_var(&cs, F::one());
		let na = &qm.nonaggr;
		let r1sq = r1 * r1;
		for i in 0..n {
			// (1) w_fz < max: an empty fz group's cid-1 row is
			// the max-wrap; a real loc proves step fz carries ->
			// the chain reached len fz (C-prefix contiguity) ->
			// frozen. fz = 0 pins enc_fz to the seed key
			// (si_pins), whose C row always exists.
			check_prod_zero(&sel.is_sp[i],
				&(&(&(&c_max - &na.w_fz[i]) - &c_one)
					- &na.d_fz[i]), lc!(), "neo SP freeze")?;
			// (2) w_kept < loc: underflows when the prover aims
			// SP at the minimum itself, or when the own group
			// carries nothing (w_kept = max) -- a group can only
			// drop rows ABOVE a minimum it actually keeps.
			check_prod_zero(&sel.is_sp[i],
				&(&(&(&qm.loc[i] - &na.w_kept[i]) - &c_one)
					- &na.d_kept[i]), lc!(), "neo SP min-dom")?;
			// (3)(4) cid 1 = the group's first carried row = its
			// least loc (cid chain + sorted wf). enc_fz is
			// authenticated by si_pins_nonaggr (fz DB fact +
			// step/SUBSIG pins), so the freeze pin cannot read a
			// foreign group's minimum.
			buf_qc.push(&(&na.enc_fz[i] + r1)
				+ &(&r1sq * &na.w_fz[i]),
				sel.is_sp[i].clone());
			buf_qc.push(&(&qm.enc[i] + r1)
				+ &(&r1sq * &na.w_kept[i]),
				sel.is_sp[i].clone());
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.7: block=singleton_prune cs={} pred={}",
			cs.num_constraints() - n0, 4 * n));
		Ok(())
	}

	/// Pushes each statement subsig's SEED ANCHOR query: the
	/// step-0 seed row (the artificial match every subsig starts
	/// with, at loc 1, rank 1 of its group) must exist in Q_m AND
	/// be a reachable (non-FP) row. This is the ground of all
	/// reachability: the seed can never be pruned and reaches
	/// every step-1 row, so no cascade of FP labels can hide a
	/// live match. A LOOKUP, not a wf rule: padding is legal
	/// everywhere in Q_m, so only a statement-side query can bind
	/// "subsig s is in the statement" to "s's seed row is
	/// present". BOTH modes.
	///
	/// Advice names (per statement slot j, s = its subsig id):
	///   z_sub  zero-bit: 1 iff slot j is the pad (s = 0); welded
	///          both ways, so a real subsig cannot pose as pad.
	///
	/// Per slot, one query into the REACHABLE target:
	///  (1) (enc(s, 0), 1, 1) -- s's group key at step 0, rank 1,
	///      loc 1 -- with sel = 1 - z_sub[j].
	///
	/// EXAMPLE (fig-14): statement = [0, a] (slot 0 is pad).
	/// z_sub = [1, 0] -> one live query pack(a*2^4rb, 1, 1).
	///  - honest: row a0:1 sits in Q_m labeled C -> matched.
	///  - CHEAT vacuous all-FP: label a's every row FP (chunk
	///    "discharges" with no work) -> a0:1 is not a QR target
	///    -> query unmatched -> UNSAT.
	///  - CHEAT drop-the-group: pad out a's rows entirely -> no
	///    row keys enc(a, 0) -> unmatched -> UNSAT.
	///  - CHEAT fake-pad: switch slot a's sel off -> z_sub is
	///    welded both ways, z_sub = 1 needs s = 0 -> UNSAT.
	fn assert_seed_anchors(
		cs: ConstraintSystemRef<F>,
		subsigs: (&[FpVar<F>], &[F]),
		                 // statement subsig ids (0 = pad slot)
		                 //   + natives (zero-bit hints)
		buf_qr: &mut QmQueryBuf<F>,
		                 // REACHABLE-target instance
		r1: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let (s_var, s_nat) = subsigs;
		let m = s_var.len();
		let rb = read_global_config().range2_bit;
		let f1 = F::from(1u64 << rb);
		let c_sh4 = new_const_var(&cs, f1 * f1 * f1 * f1);
		let c_one = new_const_var(&cs, F::one());
		let r1sq = r1 * r1;
		// STRONG zero-bits (2cs/slot): sel is a true boolean, so
		// the logup sees only multiplicities 0/1. A gate-bit cut
		// (1cs) would be sound but costs a negative-multiplicity
		// argument for ~m saved constraints -- not worth it.
		let z_sub = gen_zero_bits(&cs, s_nat, s_var)?;
		for (j, s) in s_var.iter().enumerate() {
			// seed key: enc(s, 0) = s * 2^(4*rb); rank 1, loc 1.
			// Reachability is by CONSTRUCTION of the lookup: the
			// QR target side admits no FP row, so a hit row is
			// reachable, not merely present.
			buf_qr.push(&(&(s * &c_sh4) + r1) + &r1sq,
				&c_one - &z_sub[j]);
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.8: block=seed_anchors cs={} pred={}",
			cs.num_constraints() - n0, 2 * m));
		Ok(())
	}

	/// Verifies the merge equation as a multiset identity:
	///     Q_m = Q_i disjoint-union (joined L rows),
	/// i.e. every carried-in row and every joined location
	/// appears in Q_m exactly once, and Q_m holds nothing else.
	/// Dropping a carried row (a live match chain) or smuggling
	/// an extra row is UNSAT. NONAGGR ONLY: aggr has no carry
	/// queue, its Q_m is the join alone.
	///
	/// Elements are packed enc||loc (fixed-base). Pad rows -- of
	/// Q_m, of q_i and of the join table alike -- are all-zero
	/// and pack to ZERO, and the identity ignores zeros
	/// (verify_union_prf, db.rs: non-zero multisets + 2-scalar
	/// zero reconciliation).
	/// The WHOLE step-0 group is outside the identity, on BOTH
	/// sides: the M8b reseed synthesizes one seed C row per
	/// UNIVERSE subsig while q_i carries only the CARRIED
	/// subset's, so seed transport is redundant and seed
	/// soundness is owned by the seed anchors + wf instead. So
	/// vec3 = (1 - is_step0) * pack, and each q_i row gets a
	/// b_seed bit: vec1 = (1 - b_seed) * pack. b_seed = 1 is only
	/// SAT on a row whose enc is a seed key subsig*2^4rb of a
	/// statement subsig (conditional logup; a real step >= 1 enc
	/// has a nonzero step field and can never hit that table),
	/// and b_seed = 0 on a true seed row leaves its pack with no
	/// vec3 partner -- forced honest both ways. Halo-straddle
	/// duplicates are two Q_m rows, one paid by each side.
	fn assert_qm_union(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,  // enc, loc (vec3 side)
		sel: &NeoSel<F>, // is_step0 (masks the seed group)
		q_i: (&[FpVar<F>], &[FpVar<F>]),
		                 // carried-in enc, loc (pad rows = 0)
		l_join: (&[FpVar<F>], &[FpVar<F>]),
		                 // join table enc, loc (pad rows = 0)
		subsigs: (&[FpVar<F>], &[F]),
		                 // statement subsig slots (seed-key table)
		prf: &QmUnionAdvice<F>,
		r1: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.enc.len();
		let rb = read_global_config().range2_bit;
		let c_one = new_const_var(&cs, F::one());
		let c_base = new_const_var(&cs, F::from(1u64 << rb));
		let f1 = F::from(1u64 << rb);
		let sh4 = f1 * f1 * f1 * f1;
		let c_sh4 = new_const_var(&cs, sh4);
		let (s_var, s_nat) = subsigs;
		// b_seed bits (advice witnesses; native rule = enc equals
		// a seed key of a nonzero statement subsig).
		let seed_encs = s_nat.iter().filter(|s| !s.is_zero())
			.map(|s| *s * sh4).collect::<HashSet<F>>();
		let z = F::zero();
		let b_seed: Vec<FpVar<F>> = q_i.0.iter().map(|e| {
			let hit = seed_encs.contains(&e.value().unwrap_or(z));
			new_var(&cs, if hit { F::one() } else { F::zero() })
		}).collect();
		for b in &b_seed {
			check_prod_eq(b, b, b, "neo b_seed boolean")?;
		}
		// conditional logup: b_seed = 1 rows must hit the seed-key
		// table subsig*2^4rb (dummy-0 slots contribute the 0 key,
		// absorbing b_seed = 1 on all-zero q_i pad rows: harmless,
		// their pack is 0 either way).
		let tbl: Vec<FpVar<F>> = s_var.iter()
			.map(|s| s * &c_sh4).collect();
		let sel_tbl = vec![c_one.clone(); tbl.len()];
		let m_nat: Vec<F> = s_nat.iter().map(|s| {
			let key = *s * sh4;
			F::from(q_i.0.iter().filter(|e|
				e.value().unwrap_or(z) == key
				&& (!s.is_zero())).count() as u64)
		}).collect();
		let m_seed: Vec<FpVar<F>> = m_nat.iter().map(|m|
			new_var(&cs, *m)).collect();
		assert_logup_cond(cs.clone(), &q_i.0.to_vec(),
			&b_seed, &tbl, &sel_tbl, &m_seed, r1)?;
		// pack(enc, loc) = enc * 2^rb + loc: a free linear combo,
		// injective (loc < 2^rb), all-zero rows pack to 0.
		let vec1: Vec<FpVar<F>> = q_i.0.iter().zip(q_i.1.iter())
			.enumerate().map(|(j, (x, y))|
				&(&c_one - &b_seed[j])
					* &(&(x * &c_base) + y)).collect();
		let vec2: Vec<FpVar<F>> = l_join.0.iter()
			.zip(l_join.1.iter())
			.map(|(x, y)| &(x * &c_base) + y).collect();
		let vec3: Vec<FpVar<F>> = (0..n).map(|i|
			&(&c_one - &sel.is_step0[i])
				* &(&(&qm.enc[i] * &c_base) + &qm.loc[i]))
			.collect();
		verify_union_prf_vars(cs.clone(), &vec1, &vec2, &vec3,
			&prf.b_left_more_zero, &prf.diff_zero, r1)?;
		log(job_id, LOG3, &format!(
			"PERF 61082.2: block=union cs={} pred={}",
			cs.num_constraints() - n0,
			3 * n + 5 * vec1.len() + vec2.len()
				+ 2 * tbl.len()));
		Ok(())
	}

	/// Discharges every query buffered by the certificate
	/// functions: one batch membership lookup (logup) against
	/// Q_m's REACHABLE rows (buf_qr: FP brackets from
	/// fwd_pruning + seed anchors; in aggr also the C-preds) and
	/// one against its CARRIED rows (buf_qc, nonaggr only:
	/// C-preds from carry, BP mins, SP freeze/kept pins).
	/// Closing the batch here lets ONE m-table and ONE argument
	/// serve every certificate.
	///
	/// Advice names (per Q_m row):
	///   mtbl_qr  hit count: how many buffered QR queries land
	///            on this row (0 on non-target rows);
	///   mtbl_qc  same for the QC batch (EMPTY in aggr).
	///
	/// Checks:
	///  (1) QR batch: every sel=1 query in buf_qr equals some
	///      sel=1 target pack(enc, rid, loc); target sel =
	///      is_wrap + is_c, plus is_bp + is_sp in nonaggr (those
	///      category vecs are EMPTY in aggr);
	///  (2) QC batch (skipped when buf_qc is empty, i.e. aggr):
	///      likewise against pack(enc, cid, loc), target sel =
	///      is_wrap + is_c.
	///
	/// EXAMPLE (fig-14): assert_carry buffered C row a2:21's
	/// predecessor key (enc(a,1), 1, 9); it must hit committed
	/// row a1:9 here.
	///  - honest: a1:9 is carried (C), its cid is 1 -> hit.
	///  - CHEAT phantom parent: cite a loc no committed row
	///    holds -> no target packs to that key -> UNSAT.
	///  - CHEAT wrong subset: cite an FP row as predecessor ->
	///    that row's target sel is 0 -> unmatched -> UNSAT.
	///  - CHEAT mtbl fudge: inflate a row's hit count -> the
	///    logup rational identity fails at random r2 -> UNSAT.
	///
	/// COST: per live batch ~4n + 2|buf| (2n target-key muls +
	/// 2n target inverse+sel + ~2 per buffered query), so aggr
	/// ~4n + 2|buf_qr|, nonaggr ~8n + 2(|buf_qr| + |buf_qc|).
	/// PERF 61082.9.
	fn assert_qm_lookups(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,        // enc, loc (target key parts)
		sel: &NeoSel<F>,       // is_wrap/is_c/is_bp/is_sp
		ranks: &QmRanks<F>,    // rid + cid (cid EMPTY in aggr)
		buf_qr: QmQueryBuf<F>, // consumed: no push after
		buf_qc: QmQueryBuf<F>, // EMPTY in aggr -> skipped
		mtbl_qr: &[FpVar<F>],  // hit-count advice per Q_m row
		mtbl_qc: &[FpVar<F>],  // EMPTY in aggr
		r1: &FpVar<F>, r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.enc.len();
		let r1sq = r1 * r1;
		// categories are mutually exclusive booleans, so the sel
		// sums below stay boolean -- no row is double-counted.
		let tgt_qr: Vec<FpVar<F>> = (0..n).map(|i|
			&(&qm.enc[i] + &(r1 * &ranks.rid[i]))
				+ &(&r1sq * &qm.loc[i])).collect();
		let b_aggr = sel.is_bp.is_empty();
		let sel_qr: Vec<FpVar<F>> = (0..n).map(|i| {
			let s = &sel.is_wrap[i] + &sel.is_c[i];
			if b_aggr { s }
			else { &s + &(&sel.is_bp[i] + &sel.is_sp[i]) }
		}).collect();
		assert_logup_cond(cs.clone(), &buf_qr.qry, &buf_qr.sel,
			&tgt_qr, &sel_qr, &mtbl_qr.to_vec(), r2)?;
		// aggr has no carry queue: its buf_qc arrives empty and
		// the whole QC side (cid, mtbl_qc) is absent -- skipping
		// it saves the 2n key muls and the logup outright.
		if !buf_qc.qry.is_empty() {
			let tgt_qc: Vec<FpVar<F>> = (0..n).map(|i|
				&(&qm.enc[i] + &(r1 * &ranks.cid[i]))
					+ &(&r1sq * &qm.loc[i])).collect();
			let sel_qc: Vec<FpVar<F>> = (0..n).map(|i|
				&sel.is_wrap[i] + &sel.is_c[i]).collect();
			assert_logup_cond(cs.clone(), &buf_qc.qry,
				&buf_qc.sel, &tgt_qc, &sel_qc,
				&mtbl_qc.to_vec(), r2)?;
		}
		log(job_id, LOG3, &format!(
			"PERF 61082.9: block=qm_lookups cs={} pred={}",
			cs.num_constraints() - n0,
			4 * n + 2 * buf_qr.qry.len()
				+ if buf_qc.qry.is_empty() { 0 }
				else { 4 * n + 2 * buf_qc.qry.len() }));
		Ok(())
	}

	/// AGGR MODE ONLY (the nonaggr verdict flows through the q_c
	/// carry into compute_sig instead). Feeds the verdict: every
	/// subsig whose match chain SURVIVED to its terminal step
	/// must be recorded in acc_out, the committed failed-subsig
	/// accumulator that compute_sig reads (a surviving chain =
	/// the file matches that subsig = discharge FAILED for it).
	///
	///
	/// Advice names:
	///   acc_out   committed failed-subsig accumulator slots,
	///             with a LEADING 0 SLOT for masked rows;
	///   mtbl_acc  hit-count advice per acc_out slot.
	///
	/// Check:
	///  (1) per row, qry = enc * is_last * (is_c - is_seed);
	///      one batch lookup (logup) of all queries into
	///      acc_out. Masked rows query 0, landing in the 0 slot.
	///
	/// EXAMPLE: full match a1..a8 -> the terminal a8 C row
	/// queries enc(a, 8), which must sit in acc_out ->
	/// compute_sig sees subsig a as NOT discharged.
	///  - honest no-match: a's chain dies at step 3 -> no a row
	///    is both is_last and C -> all query 0 -> acc_out stays
	///    free of a.
	///  - CHEAT hide-the-match: drop enc(a, 8) from acc_out ->
	///    the terminal row's query matches no slot -> UNSAT.
	///  - CHEAT seed-only pollution: an unmatched subsig's
	///    step-0 row is vacuously is_last, but is_c - is_seed
	///    masks it -> it queries 0 -> an unmatched subsig can
	///    never be smuggled into the failed set.
	///
	/// COST: 2n muls + logup(n + 2|acc_out|). PERF 61082.10.
	fn assert_verdict_aggr(
		cs: ConstraintSystemRef<F>,
		qm: &QmVars<F>,        // enc
		sel: &NeoSel<F>,       // is_last, is_c, is_seed
		acc_out: &[FpVar<F>],  // failed-subsig accumulator,
		                       //   leading 0 slot
		mtbl_acc: &[FpVar<F>], // hit-count advice per slot
		r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		let n = qm.enc.len();
		// sel_c = is_c - is_seed: free combo equal to
		// is_c*(1 - is_step0) on any satisfying assignment (the
		// seed pin kills FP seeds) -- saves the legacy formula's
		// third mul. is_last itself is FORCED in selectors
		// (si_step LAST tag), so the true terminal cannot shed
		// it; relabeling it FP is killed by the fwd bracket cert.
		let qry: Vec<FpVar<F>> = (0..n).map(|i|
			&(&qm.enc[i] * &sel.is_last[i])
				* &(&sel.is_c[i] - &sel.is_seed[i])).collect();
		assert_logup(cs.clone(), &qry, acc_out, mtbl_acc, r2)?;
		log(job_id, LOG3, &format!(
			"PERF 61082.10: block=verdict cs={} pred={}",
			cs.num_constraints() - n0,
			3 * n + 2 * acc_out.len()));
		Ok(())
	}

	/// AGGR entry: thin composer, no constraints of its own.
	/// Interface = the test seam (cs, nat, vars, r1, r2, job_id).
	pub(crate) fn assert_neo_aggr(
		cs: ConstraintSystemRef<F>,
		nat: &NeoCore<F>, vars: &NeoCoreVars<F>,
		r1: &FpVar<F>, r2: &FpVar<F>, job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		// -- 1. derive + bind per-row selector bits
		//    (is_c/is_fp, is_step0, is_last, is_wrap, ...) --
		let sel = Self::assert_neo_selectors(cs.clone(),
			&nat.t, &vars.qm, true, job_id)?;
		// -- 2. well-formedness: row shape vs the S store,
		//    group sort order, wrap/pad structure; returns
		//    group starts + per-row reachable ranks --
		let (_gs, rid) = Self::assert_neo_wf(cs.clone(),
			&nat.t, &vars.qm, &sel, &vars.s_enc, &vars.subsigs,
			&nat.s_enc, &nat.subsig_nat, r2, job_id)?;
		// -- 3. pin each si_* companion column to its base
		//    column (outer-lookup share consistency) --
		Self::assert_neo_si_pins(cs.clone(), &vars.qm, &sel,
			true, job_id)?;
		// -- 4. ranks for the lookup keys; cid empty: aggr
		//    has no carried-rank chain --
		let ranks = QmRanks { rid, cid: vec![] };
		// single buffer: reachable == carried in aggr
		let mut buf = QmQueryBuf::new();
		// -- 5. join: aggr Q_m IS the join result; sel_q =
		//    1 - is_step0 (pads have step 0) masks pads +
		//    seed group, cost-free; (J-W) owned by step 2's
		//    skeleton (b_ext_wf = true) --
		let c_one = new_const_var(&cs, F::one());
		let sel_q: Vec<FpVar<F>> = sel.is_step0.iter()
			.map(|b| &c_one - b).collect();
		// -- 5a. no-show pats: ONE selector shared by the
		//    membership targets and the gap proof --
		let ns_zero = gen_zero_bits(&cs, &nat.ns_pat,
			&vars.ns_pat)?;
		let sel_ns: Vec<FpVar<F>> = ns_zero.iter()
			.map(|z| &c_one - z).collect();
		Self::assert_join_locations(cs.clone(),
			(&vars.qm.enc, &vars.qm.pat, &vars.qm.id,
				&vars.qm.loc),
			&sel_q, true,
			(&vars.l_pat, &vars.l_id, &vars.l_loc),
			&vars.ns_pat, &sel_ns,
			&vars.mtbl_tm, r1, r2, job_id)?;
		// -- 5b. absence proof for the no-show pats --
		Self::assert_ns_gap(cs.clone(), &vars.ns_pat, &sel_ns,
			&vars.d_ns_lo, &vars.d_ns_hi, &vars.l_pat,
			&vars.mtbl_ns, r1, r2, job_id)?;
		// -- 6. carry-out queue q_c (committed empty in
		//    aggr; still shape-checked); pv = the predecessor
		//    view shared with the fwd-pruning block --
		let pv = Self::gen_pred_view(&cs, &nat.t, &vars.qm,
			true, r1)?;
		Self::assert_carry(cs.clone(), &vars.qm, &sel, true,
			(&vars.qc_enc, &vars.qc_loc, &nat.qc_enc), &pv,
			&mut buf, r2, job_id)?;
		// -- 7. fwd pruning: every FP label justified by
		//    querying its parent rows (closure vs Q_r) --
		Self::assert_fwd_pruning(cs.clone(), &vars.qm, &sel,
			true, &nat.t.prev_loc2, &pv, &mut buf, job_id)?;
		// -- 8. each statement subsig's step-0 seed row must
		//    exist reachable in Q_m (anchor of reachability:
		//    blocks the vacuous all-FP labeling) --
		Self::assert_seed_anchors(cs.clone(),
			(&vars.subsigs, &nat.subsig_nat), &mut buf, r1,
			job_id)?;
		// -- 9. close the batch: one logup of all buffered
		//    queries into Q_m; consumes buf by value (qc
		//    side passed empty) --
		Self::assert_qm_lookups(cs.clone(), &vars.qm, &sel,
			&ranks, buf, QmQueryBuf::new(), &vars.mtbl_qr,
			&vars.mtbl_qc, r1, r2, job_id)?;
		// -- 10. verdict: every surviving terminal C row
		//    must be recorded in acc_out (own logup) --
		Self::assert_verdict_aggr(cs.clone(), &vars.qm, &sel,
			&vars.acc_out, &vars.mtbl_acc, r2, job_id)?;
		log(job_id, LOG3, &format!(
			"PERF 61081.9: block=TOTAL cs={} rows={}",
			cs.num_constraints() - n0, nat.t.enc.len()));
		Ok(())
	}

	/// NONAGGR entry: thin composer, no constraints of its own.
	/// Interface = the test seam (cs, nat, vars, default_min,
	/// r1, r2, job_id).
	pub(crate) fn assert_neo_nonaggr(
		cs: ConstraintSystemRef<F>,
		nat: &NeoCore<F>, vars: &NeoCoreVars<F>,
		default_min: &FpVar<F>, r1: &FpVar<F>, r2: &FpVar<F>,
		job_id: usize,
	) -> Result<(), SynthesisError> {
		let n0 = cs.num_constraints();
		// -- 1. derive + bind per-row selector bits
		//    (is_c/is_fp/is_bp/is_sp, is_step0, is_last,
		//    is_wrap, ...) --
		let sel = Self::assert_neo_selectors(cs.clone(),
			&nat.t, &vars.qm, false, job_id)?;
		// -- 2. well-formedness: row shape vs the S store,
		//    group sort order, wrap/pad structure; returns
		//    group starts + per-row reachable ranks --
		let (gs, rid) = Self::assert_neo_wf(cs.clone(),
			&nat.t, &vars.qm, &sel, &vars.s_enc, &vars.subsigs,
			&nat.s_enc, &nat.subsig_nat, r2, job_id)?;
		// -- 3. carried ranks: cid counts only carried rows
		//    (cat in {C,BP,SP}); free linear combo of rid --
		let cid = Self::assert_neo_cid_chain(&gs, &sel);
		// -- 4. pin each si_* companion column to its base
		//    column: core cols, then nonaggr + JR cols. sel_jr
		//    is built here because both the JR pat pin and the
		//    join's membership selector need it --
		let c_one = new_const_var(&cs, F::one());
		let jr_zero = gen_zero_bits(&cs, &nat.jr.enc,
			&vars.jr.enc)?;
		let sel_jr: Vec<FpVar<F>> = jr_zero.iter()
			.map(|z| &c_one - z).collect();
		Self::assert_neo_si_pins(cs.clone(), &vars.qm, &sel,
			false, job_id)?;
		Self::assert_neo_si_pins_nonaggr(cs.clone(), &nat.t,
			&vars.qm, &sel, &vars.jr, &sel_jr, job_id)?;
		// -- 5. both lookup key parts: reachable rank rid +
		//    carried rank cid --
		let ranks = QmRanks { rid, cid };
		// two buffers: reachable and carried are distinct
		// query targets in nonaggr
		let mut buf_qr = QmQueryBuf::new();
		let mut buf_qc = QmQueryBuf::new();
		// -- 6. join: Q_m mixes carried rows in, so the join
		//    result lives in its own table (JR = store rows
		//    JOIN pat_loc); b_ext_wf = false: JR owns its
		//    bracket skeleton. sel_q = the non-pad rows, built
		//    with the si pins in step 4 --
		// -- 6a. no-show pats: ONE selector shared by the
		//    membership targets and the gap proof --
		let ns_zero = gen_zero_bits(&cs, &nat.ns_pat,
			&vars.ns_pat)?;
		let sel_ns: Vec<FpVar<F>> = ns_zero.iter()
			.map(|z| &c_one - z).collect();
		Self::assert_join_locations(cs.clone(),
			(&vars.jr.enc, &vars.jr.pat, &vars.jr.id,
				&vars.jr.loc),
			&sel_jr, false,
			(&vars.l_pat, &vars.l_id, &vars.l_loc),
			&vars.ns_pat, &sel_ns,
			&vars.mtbl_tm, r1, r2, job_id)?;
		// -- 6b. absence proof for the no-show pats --
		Self::assert_ns_gap(cs.clone(), &vars.ns_pat, &sel_ns,
			&vars.d_ns_lo, &vars.d_ns_hi, &vars.l_pat,
			&vars.mtbl_ns, r1, r2, job_id)?;
		// -- 7. multiset identity Q_m = q_i (carried in) union
		//    the join result: no row dropped or smuggled --
		let prf = QmUnionAdvice {
			b_left_more_zero: vars.union_prf[0].clone(),
			diff_zero: vars.union_prf[1].clone() };
		Self::assert_qm_union(cs.clone(), &vars.qm, &sel,
			(&vars.qi_enc, &vars.qi_loc),
			(&vars.jr.enc, &vars.jr.loc),
			(&vars.subsigs, &nat.subsig_nat), &prf, r1,
			job_id)?;
		// -- 8. carry-out queue q_c: the tight carried set
		//    handed to the next chunk (holds the verdict);
		//    pv = the predecessor view shared with fwd --
		let pv = Self::gen_pred_view(&cs, &nat.t, &vars.qm,
			false, r1)?;
		Self::assert_carry(cs.clone(), &vars.qm, &sel, false,
			(&vars.qc_enc, &vars.qc_loc, &nat.qc_enc), &pv,
			&mut buf_qc, r2, job_id)?;
		// -- 9. fwd pruning: every FP label justified by
		//    querying its parent rows (closure vs Q_r) --
		Self::assert_fwd_pruning(cs.clone(), &vars.qm, &sel,
			false, &nat.t.prev_loc2, &pv, &mut buf_qr, job_id)?;
		// -- 10. bwd pruning: every BP label is a fwd dead
		//    end -- farthest reach short of the successor
		//    step's minimum surviving loc --
		Self::assert_bwd_pruning(cs.clone(), &vars.qm, &sel,
			&nat.t.nonaggr.w_next, default_min, &mut buf_qc,
			r1, job_id)?;
		// -- 11. singleton pruning: every SP label redundant
		//    above its frozen group's kept minimum --
		Self::assert_singleton_pruning(cs.clone(), &vars.qm,
			&sel, &mut buf_qc, r1, job_id)?;
		// -- 12. each statement subsig's step-0 seed row must
		//    exist reachable in Q_m (anchor of reachability:
		//    blocks the vacuous all-FP labeling) --
		Self::assert_seed_anchors(cs.clone(),
			(&vars.subsigs, &nat.subsig_nat), &mut buf_qr, r1,
			job_id)?;
		// -- 13. close the batch: one logup per buffer into
		//    Q_m; consumes both buffers by value --
		Self::assert_qm_lookups(cs.clone(), &vars.qm, &sel,
			&ranks, buf_qr, buf_qc, &vars.mtbl_qr,
			&vars.mtbl_qc, r1, r2, job_id)?;
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
		l_pat: Vec<F>, l_id: Vec<F>, l_loc: Vec<F>)
	-> Result<NeoCore<F>, Error> {
		let t = g.gen_qm_table(info, true)?;
		let rid = Self::gen_rid_native(&t);
		// 8_C: subsig column = K slots (dummy-0 pad; circuit masks
		// zero slots), store rows padded to the wrap budget; both
		// shapes are capacity-only so every chunk's statement (and
		// the dummy config) is identical. Tier-1 fixtures
		// (capacity.b_aggressive=false) keep exact sizes.
		let mut subsig_nat = g.subsigs.clone();
		let (mut s_enc, s_pat) = Self::gen_store_rows(
			&g.subsigs, info);
		if g.capacity.b_aggressive {
			let k_slots = g.capacity.subsigs;
			let s_cap = StepQueueNeo::<F>::wrap_budget(
				&g.capacity, info);
			//as in gen_nonaggr: upstream-guarded, kept bumpable.
			if subsig_nat.len() > k_slots {
				return Err(Error::CapErr(vec![(format!(
					"neo_subsig_slots, b_igc: {}", g.b_igc),
					subsig_nat.len())]));
			}
			subsig_nat.resize(k_slots, F::zero());
			if s_enc.len() > s_cap {
				//store rows = Sigma(chain) over NEEDS -> bump subsigs
				return Err(Error::CapErr(vec![(format!(
					"dis_adv::neo_wrap_subsigs, b_igc: {}", g.b_igc),
					StepQueueNeo::<F>::wrap_subsigs_for(info,
						s_enc.len()))]));
			}
			s_enc.resize(s_cap, F::zero());
		}
		let mtbl_qr = Self::gen_mtbl_qr(&t, &rid, &subsig_nat);
		// no-show pats + absence-gap advice
		let ns_pat = Self::gen_ns_pat(&s_pat, &l_pat,
			s_enc.len());
		let (d_ns_lo, d_ns_hi, mtbl_ns) =
			Self::gen_ns_advice(&ns_pat, &l_pat);
		let mtbl_tm = Self::gen_mtbl_tm_aggr(&t, &l_pat, &l_id,
			&l_loc, &ns_pat);
		let (acc_out, mtbl_acc) = Self::gen_acc_padded(&t, info);
		Ok(NeoCore { t, l_pat, l_id, l_loc, subsig_nat, s_enc,
			mtbl_qr, mtbl_tm, ns_pat, d_ns_lo, d_ns_hi, mtbl_ns,
			acc_out, mtbl_acc,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![], union_prf: vec![],
			jr: JrTable::default() })
	}
}

impl<F: PrimeField + ColEle> StepQueueNeo<F> {
	/// N3 column assembly: the "neo_core" advice container mirroring
	/// NeoCore. si policy (outer lookups): VARIABLE si for the
	/// DB-bound cols (step/subsig/pat/rg1/rg2/enc_prev/b_bwd), const
	/// RANGE2 si for the range-checked diff advice
	/// (d_c1/d_c2/d_below_lo/d_above_lo/d_sort),
	/// zero si (NOT range-checked) elsewhere -- soundness audit:
	///   enc      group-uniqueness product vs {S encs + seed encs};
	///   id/loc   wf chain + sorted d_sort between 0/max sentinels;
	///   cat      unity + hygiene selectors;
	///   prev_*   challenge-packed QR-target lookups (SZ);
	///   *_hi     boolean-checked in-circuit;
	///   l_*      copy of the fsm pat_loc table (binding = M8);
	///   subsigs  compute_sig seed tie (M8);
	///   s_enc    S-universe authentication (M8);
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
			if !t.nonaggr.enc_next.is_empty() {
				let na = &t.nonaggr;
				var(&na.bp_prev_val, "bp_prev_val",
					&na.si_bp_prev);
				var(&na.rg2_next, "rg2_next", &na.si_rg2_next);
				var(&na.fz, "fz", &na.si_fz);
				var(&na.fz_step_val, "fz_step_val",
					&na.si_fz_step);
				var(&na.fz_sub_val, "fz_sub_val", &na.si_fz_sub);
			}
			//JOIN RESULT temp table (nonaggr): jr_pat carries
			//the variable tag(enc, PAT) si on every block row.
			if !nat.jr.enc.is_empty() {
				var(&nat.jr.pat, "jr_pat", &nat.jr.si_pat);
			}
		}
		if !t.nonaggr.enc_next.is_empty() {
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
			fix(&na.enc_next, "enc_next", z);
			fix(&na.w_next, "w_next", z);
			fix(&na.d_bp, "d_bp", f_r2);
			fix(&na.enc_fz, "enc_fz", z);
			fix(&na.w_fz, "w_fz", z);
			fix(&na.d_fz, "d_fz", f_r2);
			fix(&na.w_kept, "w_kept", z);
			fix(&na.d_kept, "d_kept", f_r2);
			fix(&nat.mtbl_qc, "mtbl_qc", z);
			fix(&nat.union_prf, "union_prf", z);
			//JR data cols: enc union-bound (si 0), id chain-bound
			//(si 0), loc RANGE2 (packing legality of the
			//membership triple).
			fix(&nat.jr.enc, "jr_enc", z);
			fix(&nat.jr.id, "jr_id", z);
			fix(&nat.jr.loc, "jr_loc", f_r2);
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
			fix(&t.d_above_lo, "d_above_lo", f_r2);
			fix(&t.d_sort, "d_sort", f_r2);
			fix(&nat.l_pat, "l_pat", z);
			fix(&nat.l_id, "l_id", z);
			fix(&nat.l_loc, "l_loc", z);
			fix(&nat.subsig_nat, "subsigs", z);
			fix(&nat.s_enc, "s_enc", z);
			fix(&nat.mtbl_qr, "mtbl_qr", z);
			fix(&nat.mtbl_tm, "mtbl_tm", z);
			fix(&nat.ns_pat, "ns_pat", f_r2);
			fix(&nat.d_ns_lo, "d_ns_lo", f_r2);
			fix(&nat.d_ns_hi, "d_ns_hi", f_r2);
			fix(&nat.mtbl_ns, "mtbl_ns", z);
		}
		res
	}

	/// DEBUG USE 62070.10: per-column census of the emitted statement --
	/// length, live bit-width, and whether the col is const-folded.
	/// Sizes three levers at once: which cols are L-sized (externalise),
	/// which carry a VARIABLE si (the outer-lookup key drivers), and how
	/// many bits each col actually uses (packing headroom).
	fn probe_core_cols(ct: &Container<F>, tag: &str) {
		match ct {
			Container::Complex(v, _, _, _) => {
				for ch in v {
					Self::probe_core_cols(&ch.lock().unwrap(), tag);
				}
			},
			Container::Single(c) => {
				let g = c.lock().unwrap();
				let n = g.data.len();
				if n == 0 { return; }
				let bits = g.data.iter()
					.map(|x| x.into_bigint().num_bits())
					.max().unwrap_or(0);
				let nz = g.data.iter().filter(|x| !x.is_zero()).count();
				let name = match &g.cfg {
					ContainerConfig::Column(_, nm, _, _) => nm.clone(),
					_ => "?".to_string(),
				};
				//b_const cols collapse to ONE witness var, so a wide
				//const si costs 1 while a variable si costs n.
				println!("DEBUG USE 62070.10: col {} name={} len={} \
nonzero={} bits={} const={}", tag, name, n, nz, bits, g.b_const);
			},
		}
	}

	/// DEBUG USE 62070.8: how much of the fsm L (pat_loc) table this
	/// chunk actually filled. All-pad L means the chunk matched no
	/// pattern at all, so an empty Q_m is a FIXTURE fact.
	fn probe_l_occupancy(arm: &str, b_igc: bool, l_pat: &Vec<F>,
		l_loc: &Vec<F>) {
		let n = l_pat.len();
		let nz = l_pat.iter().filter(|p| !p.is_zero()).count();
		let mut pats: Vec<F> = l_pat.iter().filter(|p| !p.is_zero())
			.cloned().collect();
		pats.sort(); pats.dedup();
		let mx = l_loc.iter().max().cloned()
			.unwrap_or_else(F::zero);
		println!("DEBUG USE 62070.8: L {} igc={} len={} nonzero={} \
distinct_pats={} max_loc={}", arm, b_igc, n, nz, pats.len(), mx);
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
		let l_id = pat_loc.lock().unwrap()
			.get_container("sorted_id").unwrap()
			.lock().unwrap().to_vec();
		let l_loc = pat_loc.lock().unwrap()
			.get_container("sorted_val").unwrap()
			.lock().unwrap().to_vec();
		if utils::consts::b_probe_p36() {
			Self::probe_l_occupancy("AGGR", self.b_igc, &l_pat,
				&l_loc);
		}
		let mut nat = NeoCore::gen(self, info, l_pat, l_id,
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
		if utils::consts::b_probe_p36() {
			Self::probe_core_cols(&core.lock().unwrap(), "AGGR");
		}
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
		let l_id = pat_loc.lock().unwrap()
			.get_container("sorted_id").unwrap()
			.lock().unwrap().to_vec();
		let l_loc = pat_loc.lock().unwrap()
			.get_container("sorted_val").unwrap()
			.lock().unwrap().to_vec();
		if utils::consts::b_probe_p36() {
			Self::probe_l_occupancy("NONAGGR", self.b_igc, &l_pat,
				&l_loc);
		}
		let hm_loc = StepQueue::<F>::pat_loc_to_hm(pat_loc);
		let (nat, ct_qi, ct_qc) = NeoCore::gen_nonaggr(self, info,
			l_pat, l_id, l_loc, &hm_loc, carried, default_min,
			job_id)?;
		let core = Self::core_container(&nat);
		if utils::consts::b_probe_p36() {
			Self::probe_core_cols(&core.lock().unwrap(), "NONAGGR");
		}
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
			Self::new_nonaggr(b_igc, offset_fsm, pat_loc,
				inp_subsigs, fsm_id, subsig_store_info, capacity,
				inp_step_queue, last_loc, job_id)
		}
	}

	/// NON-AGGRESSIVE ctor (paper C.1 prune): seed = inp_subsigs
	/// (the SDE obligation set, capacity-bounded), Q_i overlaid,
	/// shared core + apply_sp_pass -> statement {neo_core,q_i,q_c}.
	pub fn new_nonaggr(
		b_igc: bool,
		offset_fsm: usize,
		pat_loc: &Arc<Mutex<Container<F>>>,
		inp_subsigs: &Vec<F>,
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
		// NewP3: seed this fold's SDE obligation set (inp_subsigs =
		// the failed-CP subsigs from DischargeInfo), NOT the DB
		// universe: cost is O(capacity), not O(DB). Mirrors
		// new_aggr's seed; unseeded subsigs are CP-absence covered
		// (legacy architecture). Chunk-0's public q_i anchors the
		// set in-circuit (assert_qm_union's b_seed logup).
		let is_uni = |u: usize| subsig_store_info.subsig_to_steps
			.get(&u).map_or(false, |it| !it.vec_pm_bounds.is_empty());
		// filtered to non-empty-chain (mirrors new_aggr and
		// compute_sig's empty-chain drop, so the seed-pin sets stay
		// equal); empty-chain ids are meta/count-constraint subsigs
		// with no FSM chain to walk, covered by CP-absence instead.
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
		let mut merged = DischargeAdvAdvice::<F>
			::gen_empty_steps_queue_serialized(b_igc, &seed_subsigs,
				subsig_store_info, fsm_id, capacity);
		for (s, items) in inp_step_queue.store_items.iter() {
			assert!(merged.store_items.contains_key(s),
				"carried subsig {} outside the obligation seed", s);
			merged.store_items.insert(*s, items.clone());
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
	/// load one named neo_core column as
	/// (circuit vars, plain F values).
	fn col2(core: &Arc<Mutex<Container<FpVar<F>>>>, name: &str)
	-> Result<(Vec<FpVar<F>>, Vec<F>), SynthesisError> {
		let v = core.lock().unwrap().get_container(name)?
			.lock().unwrap().to_vec();
		let nat = v.iter().map(|x| x.value())
			.collect::<Result<Vec<F>, SynthesisError>>()?;
		Ok((v, nat))
	}

	/// Deserialize chunk i's committed neo statement into the
	/// plain-F-value bundle (NeoCore) + circuit vars (NeoCoreVars).
	/// Pure loading, no constraints. Aggr: no q_i/q_c transport.
	fn load_neo_stmt_aggr(&self, i: usize,
		wtns: &WitnessSigmaIR1CSVar<F>,
		wtns_cfg: &WitnessSigmaIR1CSConfig)
	-> Result<(NeoCore<F>, NeoCoreVars<F>), SynthesisError> {
		let cfg = self.inner.get_container_config();
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg,
			wtns, &cfg)?;
		let core = stmt.get_container("neo_core")?;
		// c2: load one neo_core column by name as
		// (circuit vars, plain F values via value()).
		let c2 = |n: &str| Self::col2(&core, n);
		// -- 1. Q_m table: 20 base columns --
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
		let (d_above_lo, d_above_lo_n) = c2("d_above_lo")?;
		let (d_sort, d_sort_n) = c2("d_sort")?;
		// -- 2. si_* companions (outer-lookup share) --
		let (si_step, si_step_n) = c2("si_step")?;
		let (si_subsig, si_subsig_n) = c2("si_subsig")?;
		let (si_pat, si_pat_n) = c2("si_pat")?;
		let (si_rg1, si_rg1_n) = c2("si_rg1")?;
		let (si_rg2, si_rg2_n) = c2("si_rg2")?;
		let (si_enc_prev, si_enc_prev_n) = c2("si_enc_prev")?;
		let (si_b_bwd, si_b_bwd_n) = c2("si_b_bwd")?;
		// -- 3. side columns: pat_loc triple, statement
		//    subsigs, store rows, multiplicity tables --
		let (l_pat, l_pat_n) = c2("l_pat")?;
		let (l_id, l_id_n) = c2("l_id")?;
		let (l_loc, l_loc_n) = c2("l_loc")?;
		let (subsigs, subsigs_n) = c2("subsigs")?;
		let (s_enc, s_enc_n) = c2("s_enc")?;
		let (mtbl_qr, mtbl_qr_n) = c2("mtbl_qr")?;
		let (mtbl_tm, mtbl_tm_n) = c2("mtbl_tm")?;
		let (ns_pat, ns_pat_n) = c2("ns_pat")?;
		let (d_ns_lo, d_ns_lo_n) = c2("d_ns_lo")?;
		let (d_ns_hi, d_ns_hi_n) = c2("d_ns_hi")?;
		let (mtbl_ns, mtbl_ns_n) = c2("mtbl_ns")?;
		// -- 4. verdict target: failed-subsig accumulator
		//    (legacy container names; compute_sig reads it) --
		let combo = stmt.get_container("failed_acc_combo")?;
		let facc = combo.lock().unwrap()
			.get_container("failed_acc")?;
		let (acc_out, acc_out_n) = Self::col2(&facc,
			"acc_encoded")?;
		let fprf = combo.lock().unwrap()
			.get_container("failed_acc_prf")?;
		let (mtbl_acc, mtbl_acc_n) = Self::col2(&fprf,
			"mtbl_complete")?;
		// -- 5. assemble the F-value bundle (NeoCore) and the
		//    var bundle (NeoCoreVars); n_pad = leading pad rows
		//    (hint only); q_i/q_c/union empty: aggr carries
		//    nothing across chunks --
		let n_pad = enc_n.iter().take_while(|e| e.is_zero())
			.count();
		let t = QmTable { enc: enc_n, id: id_n, loc: loc_n,
			cat: cat_n, step: step_n, subsig: subsig_n,
			prev_id1: prev_id1_n, prev_loc1: prev_loc1_n,
			prev_loc2: prev_loc2_n, pat: pat_n, rg1: rg1_n,
			rg2: rg2_n, enc_prev: enc_prev_n, b_bwd: b_bwd_n,
			d_c1: d_c1_n, d_c2: d_c2_n,
			d_below_lo: d_below_lo_n, d_above_lo: d_above_lo_n,
			d_sort: d_sort_n, si_step: si_step_n,
			si_subsig: si_subsig_n, si_pat: si_pat_n,
			si_rg1: si_rg1_n, si_rg2: si_rg2_n,
			si_enc_prev: si_enc_prev_n, si_b_bwd: si_b_bwd_n,
			nonaggr: QmNonAggrCols::default(), n_pad };
		let nat = NeoCore { t, l_pat: l_pat_n, l_id: l_id_n,
			l_loc: l_loc_n, subsig_nat: subsigs_n,
			s_enc: s_enc_n, mtbl_qr: mtbl_qr_n,
			mtbl_tm: mtbl_tm_n, ns_pat: ns_pat_n,
			d_ns_lo: d_ns_lo_n, d_ns_hi: d_ns_hi_n,
			mtbl_ns: mtbl_ns_n,
			acc_out: acc_out_n, mtbl_acc: mtbl_acc_n,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![], union_prf: vec![],
			jr: JrTable::default() };
		let qm = QmVars { enc, id, loc, cat, step, subsig,
			prev_id1, prev_loc1, prev_loc2, pat, rg1, rg2,
			enc_prev, b_bwd, d_c1, d_c2, d_below_lo,
			d_above_lo, d_sort, si_step, si_subsig,
			si_pat, si_rg1, si_rg2, si_enc_prev, si_b_bwd,
			nonaggr: QmNonAggrVars::empty() };
		let vars = NeoCoreVars { qm, l_pat, l_id, l_loc, subsigs,
			s_enc, mtbl_qr, mtbl_tm, ns_pat, d_ns_lo, d_ns_hi,
			mtbl_ns, acc_out, mtbl_acc,
			qi_enc: vec![], qi_loc: vec![], qc_enc: vec![],
			qc_loc: vec![], mtbl_qc: vec![], union_prf: vec![],
			jr: JrVars::empty() };
		Ok((nat, vars))
	}

	/// Deserialize chunk i's committed neo statement (core + nonaggr
	/// cols + q_i/q_c transport) into the plain-F-value bundle +
	/// circuit vars, plus default_min = last fsm loc + 1.
	fn load_neo_stmt_nonaggr(&self, i: usize,
		cs: &ConstraintSystemRef<F>,
		wtns: &WitnessSigmaIR1CSVar<F>,
		wtns_cfg: &WitnessSigmaIR1CSConfig)
	-> Result<(NeoCore<F>, NeoCoreVars<F>, FpVar<F>),
		SynthesisError> {
		let cfg = self.inner.get_container_config();
		let stmt = Container::<FpVar<F>>::load_from(i, wtns_cfg,
			wtns, &cfg)?;
		// -- 1. default_min = last fsm-acc loc + 1, read from
		//    the fsm gadget's statement (offset_fsm slots
		//    earlier; legacy assert_msg3 retrieval) --
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
			+ &new_const_var(cs, F::one());
		let core = stmt.get_container("neo_core")?;
		// c2: load one neo_core column by name as
		// (circuit vars, plain F values via value()).
		let c2 = |n: &str| Self::col2(&core, n);
		// -- 2. Q_m table: 20 base columns --
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
		let (d_above_lo, d_above_lo_n) = c2("d_above_lo")?;
		let (d_sort, d_sort_n) = c2("d_sort")?;
		// -- 3. si_* companions (outer-lookup share) --
		let (si_step, si_step_n) = c2("si_step")?;
		let (si_subsig, si_subsig_n) = c2("si_subsig")?;
		let (si_pat, si_pat_n) = c2("si_pat")?;
		let (si_rg1, si_rg1_n) = c2("si_rg1")?;
		let (si_rg2, si_rg2_n) = c2("si_rg2")?;
		let (si_enc_prev, si_enc_prev_n) = c2("si_enc_prev")?;
		let (si_b_bwd, si_b_bwd_n) = c2("si_b_bwd")?;
		// -- 4. nonaggr extension columns (BP/SP pruning +
		//    frozen-step advice) + their si_* companions --
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
		let (w_kept, w_kept_n) = c2("w_kept")?;
		let (d_kept, d_kept_n) = c2("d_kept")?;
		let (si_bp_prev, si_bp_prev_n) = c2("si_bp_prev_val")?;
		let (si_rg2_next, si_rg2_next_n) = c2("si_rg2_next")?;
		let (si_fz, si_fz_n) = c2("si_fz")?;
		let (si_fz_step, si_fz_step_n) = c2("si_fz_step_val")?;
		let (si_fz_sub, si_fz_sub_n) = c2("si_fz_sub_val")?;
		// -- 5. side columns: pat_loc triple, statement
		//    subsigs, store rows, multiplicity tables,
		//    union proof scalars --
		let (l_pat, l_pat_n) = c2("l_pat")?;
		let (l_id, l_id_n) = c2("l_id")?;
		let (l_loc, l_loc_n) = c2("l_loc")?;
		let (subsigs, subsigs_n) = c2("subsigs")?;
		let (s_enc, s_enc_n) = c2("s_enc")?;
		let (mtbl_qr, mtbl_qr_n) = c2("mtbl_qr")?;
		let (mtbl_tm, mtbl_tm_n) = c2("mtbl_tm")?;
		let (ns_pat, ns_pat_n) = c2("ns_pat")?;
		let (d_ns_lo, d_ns_lo_n) = c2("d_ns_lo")?;
		let (d_ns_hi, d_ns_hi_n) = c2("d_ns_hi")?;
		let (mtbl_ns, mtbl_ns_n) = c2("mtbl_ns")?;
		let (mtbl_qc, mtbl_qc_n) = c2("mtbl_qc")?;
		let (union_prf, union_prf_n) = c2("union_prf")?;
		// -- 5b. JOIN RESULT temp table (join view + si_pat
		//    companion of the outer-lookup share) --
		let (jr_enc, jr_enc_n) = c2("jr_enc")?;
		let (jr_pat, jr_pat_n) = c2("jr_pat")?;
		let (jr_id, jr_id_n) = c2("jr_id")?;
		let (jr_loc, jr_loc_n) = c2("jr_loc")?;
		let (jr_si_pat, jr_si_pat_n) = c2("si_jr_pat")?;
		// -- 6. committed carry transport: q_i (from previous
		//    chunk) and q_c (to next chunk) --
		let ct_qi = stmt.get_container("q_i")?;
		let (qi_enc, qi_enc_n) = Self::col2(&ct_qi, "encoded")?;
		let (qi_loc, qi_loc_n) = Self::col2(&ct_qi, "locs")?;
		let ct_qc = stmt.get_container("q_c")?;
		let (qc_enc, qc_enc_n) = Self::col2(&ct_qc, "encoded")?;
		let (qc_loc, qc_loc_n) = Self::col2(&ct_qc, "locs")?;
		// -- 7. assemble the F-value bundle (NeoCore) and the
		//    var bundle (NeoCoreVars); n_pad = leading pad rows
		//    (hint only); acc_out/mtbl_acc empty: the nonaggr
		//    verdict flows through the q_c carry instead --
		let n_pad = enc_n.iter().take_while(|e| e.is_zero())
			.count();
		let na_t = QmNonAggrCols {
			enc_next: enc_next_n, bp_prev_val: bp_prev_val_n,
			rg2_next: rg2_next_n, w_next: w_next_n, d_bp: d_bp_n,
			fz: fz_n, enc_fz: enc_fz_n,
			fz_step_val: fz_step_val_n, fz_sub_val: fz_sub_val_n,
			w_fz: w_fz_n, d_fz: d_fz_n, w_kept: w_kept_n,
			d_kept: d_kept_n,
			si_bp_prev: si_bp_prev_n, si_rg2_next: si_rg2_next_n,
			si_fz: si_fz_n, si_fz_step: si_fz_step_n,
			si_fz_sub: si_fz_sub_n };
		let t = QmTable { enc: enc_n, id: id_n, loc: loc_n,
			cat: cat_n, step: step_n, subsig: subsig_n,
			prev_id1: prev_id1_n, prev_loc1: prev_loc1_n,
			prev_loc2: prev_loc2_n, pat: pat_n, rg1: rg1_n,
			rg2: rg2_n, enc_prev: enc_prev_n, b_bwd: b_bwd_n,
			d_c1: d_c1_n, d_c2: d_c2_n,
			d_below_lo: d_below_lo_n, d_above_lo: d_above_lo_n,
			d_sort: d_sort_n, si_step: si_step_n,
			si_subsig: si_subsig_n, si_pat: si_pat_n,
			si_rg1: si_rg1_n, si_rg2: si_rg2_n,
			si_enc_prev: si_enc_prev_n, si_b_bwd: si_b_bwd_n,
			nonaggr: na_t, n_pad };
		let nat = NeoCore { t, l_pat: l_pat_n, l_id: l_id_n,
			l_loc: l_loc_n,
			subsig_nat: subsigs_n, s_enc: s_enc_n,
			mtbl_qr: mtbl_qr_n, mtbl_tm: mtbl_tm_n,
			ns_pat: ns_pat_n, d_ns_lo: d_ns_lo_n,
			d_ns_hi: d_ns_hi_n, mtbl_ns: mtbl_ns_n,
			acc_out: vec![], mtbl_acc: vec![],
			qi_enc: qi_enc_n, qi_loc: qi_loc_n,
			qc_enc: qc_enc_n, qc_loc: qc_loc_n,
			mtbl_qc: mtbl_qc_n, union_prf: union_prf_n,
			jr: JrTable { enc: jr_enc_n, pat: jr_pat_n,
				id: jr_id_n, loc: jr_loc_n,
				si_pat: jr_si_pat_n } };
		let na_v = QmNonAggrVars { enc_next, bp_prev_val,
			rg2_next, w_next, d_bp, fz, enc_fz, fz_step_val,
			fz_sub_val, w_fz, d_fz, w_kept, d_kept,
			si_bp_prev, si_rg2_next, si_fz, si_fz_step,
			si_fz_sub };
		let qm = QmVars { enc, id, loc, cat, step, subsig,
			prev_id1, prev_loc1, prev_loc2, pat, rg1, rg2,
			enc_prev, b_bwd, d_c1, d_c2, d_below_lo,
			d_above_lo, d_sort, si_step, si_subsig,
			si_pat, si_rg1, si_rg2, si_enc_prev, si_b_bwd,
			nonaggr: na_v };
		let vars = NeoCoreVars { qm, l_pat, l_id, l_loc, subsigs,
			s_enc, mtbl_qr, mtbl_tm, ns_pat, d_ns_lo, d_ns_hi,
			mtbl_ns,
			acc_out: vec![], mtbl_acc: vec![],
			qi_enc, qi_loc, qc_enc, qc_loc, mtbl_qc, union_prf,
			jr: JrVars { enc: jr_enc, pat: jr_pat, id: jr_id,
				loc: jr_loc, si_pat: jr_si_pat } };
		Ok((nat, vars, default_min))
	}
}

#[cfg(test)]
mod tests_neo_r0 {
	use super::*;
	use ark_bn254::Fr;
	use ark_relations::r1cs::ConstraintSystem;

	fn f(x: u32) -> Fr { Fr::from(x) }

	/// every piece id an si companion column in this file is keyed
	/// by; si_tag_base has to agree with the DB on all of them.
	fn piece_ids() -> Vec<u32> {
		vec![ID_ENCODED_NORMAL_STEP, ID_ENCODED_LAST_STEP,
			ID_ENCODED_SUBSIG, ID_ENCODED_PAT, ID_ENCODED_RG_START,
			ID_ENCODED_RG_END, ID_ENCODED_PREV_ENCODED,
			ID_ENCODED_FZ]
	}

	/// si_tag_base(cid) + enc must reproduce gen_step_tbl_id, which
	/// is what makes a pinned column land on a real DB pair.
	#[test]
	fn test_r0_si_tag_base_matches_db() {
		for p in piece_ids() {
			for e in [0u32, 1, 7, 12345, 0xffff] {
				let want = SubsigStepStore::gen_step_tbl_id(f(e), p);
				assert_eq!(si_tag_base::<Fr>(p) + f(e), want,
					"si_tag_base mismatch cid={} enc={}", p, e);
			}
		}
	}

	/// distinct piece ids must not collide for any enc in range.
	#[test]
	fn test_r0_si_tag_base_separates_cids() {
		let ids = piece_ids();
		for i in 0..ids.len() {
			for j in (i + 1)..ids.len() {
				assert_ne!(si_tag_base::<Fr>(ids[i]),
					si_tag_base::<Fr>(ids[j]));
			}
		}
	}

	#[test]
	fn test_r0_batch_inv() {
		let v = vec![f(0), f(1), f(7), f(0), f(123456)];
		let w = batch_inv(&v);
		for i in 0..v.len() {
			if v[i].is_zero() { assert_eq!(w[i], f(0)); }
			else { assert_eq!(v[i] * w[i], f(1)); }
		}
	}

	/// B_DEBUG is false, so a wrong product shows up only as an
	/// unsatisfied system -- which is exactly what the negatives
	/// in later rounds rely on.
	#[test]
	fn test_r0_check_prod_eq() {
		let cases = [(3u32, 5u32, 15u32, true), (3, 5, 16, false),
			(0, 9, 0, true), (0, 9, 1, false), (1, 1, 1, true)];
		for (a, b, c, sat) in cases {
			let cs = ConstraintSystem::<Fr>::new_ref();
			let v1 = new_var(&cs, f(a));
			let v2 = new_var(&cs, f(b));
			let v3 = new_var(&cs, f(c));
			check_prod_eq(&v1, &v2, &v3, "r0").expect("prod eq");
			assert_eq!(cs.num_constraints(), 1, "prod eq is 1cs");
			assert_eq!(cs.is_satisfied().unwrap(), sat,
				"prod eq {}*{}=={}", a, b, c);
		}
	}

	/// both sides of the pin, including the RANGE2 pre-shift the
	/// caller bakes into c_tag: mask on -> si = tag_base + key,
	/// mask off -> si = RANGE2, in ONE constraint.
	#[test]
	fn test_r0_check_si_pin() {
		let base = si_tag_base::<Fr>(ID_ENCODED_PAT);
		let key = f(7);
		let rg2 = Fr::from(RANGE2);
		let cases: Vec<(u32, Fr, bool)> = vec![
			(1, base + key, true),
			(1, rg2, false),
			(1, base + key + f(1), false),
			(1, base, false),
			(0, rg2, true),
			(0, base + key, false),
			(0, f(0), false)];
		for (m, si, sat) in cases {
			let cs = ConstraintSystem::<Fr>::new_ref();
			let mask = new_var(&cs, f(m));
			let kv = new_var(&cs, key);
			let sv = new_var(&cs, si);
			let c_tag = new_const_var(&cs, base - rg2);
			let c_rg2 = new_const_var(&cs, rg2);
			check_si_pin(&mask, &kv, &sv, &c_tag, &c_rg2, "r0")
				.expect("si pin");
			assert_eq!(cs.num_constraints(), 1, "si pin is 1cs");
			assert_eq!(cs.is_satisfied().unwrap(), sat,
				"si pin mask={}", m);
		}
	}

	/// gen_zero_bits is forced BOTH ways: x == 0 pins the bit to 1
	/// (x*inv = 1-z), x != 0 pins it to 0 (x*z = 0).
	#[test]
	fn test_r0_gen_zero_bits() {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let nat = vec![f(0), f(5), f(0), f(99)];
		let vars: Vec<FpVar<Fr>> = nat.iter()
			.map(|x| new_var(&cs, *x)).collect();
		let bits = gen_zero_bits(&cs, &nat, &vars).expect("bits");
		let want = [f(1), f(0), f(1), f(0)];
		for i in 0..nat.len() {
			assert_eq!(bits[i].value().unwrap(), want[i], "row {}", i);
		}
		assert!(cs.is_satisfied().unwrap());
	}

	/// the hint slice is prover-controlled; claiming zero for a
	/// non-zero column leaves x*inv = 1 - 0 unsatisfiable.
	#[test]
	fn test_r0_gen_zero_bits_bad_hint_unsat() {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = vec![new_var(&cs, f(5))];
		let _ = gen_zero_bits(&cs, &[f(0)], &vars).expect("bits");
		assert!(!cs.is_satisfied().unwrap());
	}

	/// gen_gate_bits is ONE-SIDED: a bit claimed on a non-zero
	/// column dies at the weld b*x = 0.
	#[test]
	fn test_r0_gen_gate_bits_weld_unsat() {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = vec![new_var(&cs, f(5))];
		let b = gen_gate_bits(&cs, &[f(0)], &vars).expect("gate");
		assert_eq!(b[0].value().unwrap(), f(1));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// the free side, documented rather than defended: on a zero
	/// column a 0 bit also satisfies. Re-enabling a check at a
	/// sentinel only ever costs the prover.
	#[test]
	fn test_r0_gen_gate_bits_free_at_zero() {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let nat = vec![f(3), f(0)];
		let vars: Vec<FpVar<Fr>> = nat.iter()
			.map(|x| new_var(&cs, *x)).collect();
		let b = gen_gate_bits(&cs, &nat, &vars).expect("gate");
		assert_eq!(b[0].value().unwrap(), f(0));
		assert_eq!(b[1].value().unwrap(), f(1));
		assert_eq!(cs.num_constraints(), 2, "gate bit is 1cs");
		assert!(cs.is_satisfied().unwrap());
		let cs2 = ConstraintSystem::<Fr>::new_ref();
		let v2 = vec![new_var(&cs2, f(0))];
		let b2 = gen_gate_bits(&cs2, &[f(9)], &v2).expect("gate");
		assert_eq!(b2[0].value().unwrap(), f(0));
		assert!(cs2.is_satisfied().unwrap());
	}

	#[test]
	fn test_r0_fp_diff_range2_ok() {
		assert_fp_diff_range2(&f(100), 100);
		assert_fp_diff_range2(&f(0), 100);
	}

	#[test]
	#[should_panic(expected = "chunk too long")]
	fn test_r0_fp_diff_range2_over() {
		assert_fp_diff_range2(&f(101), 100);
	}
}

// NOTE_NEW8_ADAPTED (P3 R1): revived as-is -- this module only
// exercises the native StepQueueNeo layer, which New8 left intact.
#[cfg(test)]
pub(crate) mod tests_neo_m4 {
	use super::*;
	use ark_bn254::Fr;
	use utils::consts::read_global_config;

	fn f(x: u32) -> Fr { Fr::from(x) }

	pub(crate) fn fixture_capacity() -> DischargeAdvCapacity {
		// non-aggressive: n = subsigs*avg = 16 (>= 13 real rows).
		DischargeAdvCapacity {
			res_small_cost: DischargeAdvCapacity::default_res_small(),
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

// NOTE_NEW8_ADAPTED (P3 R1): revived as-is -- shared-core generator
// + equivalence oracle, both untouched by New8.
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
	/// match (chunk-straddle artifact). NO dedup (option-1 union
	/// fix): BOTH copies stay, adjacent and same-cat, so the union
	/// pays one to q_i and one to the join. Collapsing the pair
	/// recovers Fig-14 chunk 2 on locs/cats/scalars (reach ranks
	/// in prev_id1 may shift by the extra row).
	#[test]
	fn test_m5_corner_duplicate_loc() {
		let mut pl = HashMap::new();
		pl.insert(2, vec![111]); pl.insert(5, vec![106]);
		pl.insert(6, vec![79, 96, 141]); //79 = dup of carried
		pl.insert(7, vec![101, 131]);
		let qm = run_case(&a18_carried().to_stepqueue(), &pl, 161,
			"duplicate loc");
		let gold = build_a1_a8_neo();
		let s = f(1);
		let its = qm.store_items.get(&s).unwrap();
		let g_its = gold.store_items.get(&s).unwrap();
		assert_eq!(its.len(), g_its.len());
		for (i, (it, g)) in its.iter().zip(g_its.iter())
			.enumerate() {
			let (mut locs, mut cats) =
				(it.base.locs.clone(), it.cat.clone());
			if i == 6 {
				assert_eq!(locs, vec![f(73), f(79), f(79),
					f(96), f(141)]);
				assert_eq!(cats[1], cats[2], "pair same cat");
				locs.remove(2); cats.remove(2);
			}
			assert_eq!(locs, g.base.locs, "locs item {}", i);
			assert_eq!(cats, g.cat, "cats item {}", i);
			assert_eq!(it.min_next, g.min_next, "min item {}", i);
			assert_eq!(it.fz, g.fz, "fz item {}", i);
		}
	}
}

// ============================================================
//   P3 R1: New8 native layer (tables, JR, no-show, m-tables)
// ============================================================
#[cfg(test)]
pub(crate) mod tests_neo_r1 {
	use super::*;
	use super::tests_neo_m4::{fixture_capacity, A18_DEFAULT_MIN};
	use super::tests_neo_m5::{a18_store, a18_carried};
	use ark_bn254::Fr;

	fn f(x: u32) -> Fr { Fr::from(x) }

	fn f_max() -> Fr {
		f((1u32 << read_global_config().range2_bit) - 1)
	}

	/// flat L columns (pat, id, loc) with per-pat 0/max wraps, pats
	/// ascending -- the 3-column pat_loc shape the New8 join reads.
	/// One leading all-zero PAD row, because the real pat_loc is a
	/// committed capacity-sized table: it is never zero-length, and
	/// the no-show gap advice leans on that (an empty column has no
	/// pair to straddle). Nothing queries the pad.
	pub(crate) fn l_cols3(m: &HashMap<u32, Vec<u32>>)
	-> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
		let (mut ps, mut is, mut ls) =
			(vec![f(0)], vec![f(0)], vec![f(0)]);
		let mut pats: Vec<u32> = m.keys().cloned().collect();
		pats.sort();
		for p in pats {
			ps.push(f(p)); is.push(f(0)); ls.push(f(0));
			for (i, l) in m[&p].iter().enumerate() {
				ps.push(f(p)); is.push(f((i + 1) as u32));
				ls.push(f(*l));
			}
			ps.push(f(p)); is.push(f((m[&p].len() + 1) as u32));
			ls.push(f_max());
		}
		(ps, is, ls)
	}

	/// the same L in the generator's pat -> [(id, loc)] form.
	pub(crate) fn hm_gen3(m: &HashMap<u32, Vec<u32>>)
	-> HashMap<Fr, Vec<(Fr, Fr)>> {
		let mut out = HashMap::new();
		for (p, locs) in m {
			let mut v = vec![(f(0), f(0))];
			for (i, l) in locs.iter().enumerate() {
				v.push((f((i + 1) as u32), f(*l)));
			}
			v.push((f((locs.len() + 1) as u32), f_max()));
			out.insert(f(*p), v);
		}
		out
	}

	/// fig-14 chunk-2 matches.
	pub(crate) fn c2_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(2, vec![111]); m.insert(5, vec![106]);
		m.insert(6, vec![96, 141]); m.insert(7, vec![101, 131]);
		m
	}

	/// the shared core BOTH arms accept: classes {C,FP,BP}. The
	/// aggressive table refuses SP by construction, so the SP pass
	/// is a separate fixture.
	fn core_plain() -> (SubsigStepStore, StepQueueNeo<Fr>) {
		let info = a18_store();
		let g = a18_carried().gen_shared_core_from_hm(0,
			&hm_gen3(&c2_hm()), &info, f(A18_DEFAULT_MIN))
			.expect("shared core");
		(info, g)
	}

	/// the same core after the SP pass -- non-aggressive only.
	fn core_sp() -> (SubsigStepStore, StepQueueNeo<Fr>) {
		let (info, mut g) = core_plain();
		g.apply_sp_pass(&info);
		(info, g)
	}

	/// [start, end) row ranges of the non-pad groups, in order.
	fn groups(t: &QmTable<Fr>) -> Vec<(usize, usize)> {
		let mut v: Vec<(usize, usize)> = vec![];
		for i in 0..t.enc.len() {
			if t.enc[i].is_zero() { continue; }
			match v.last_mut() {
				Some(g) if t.enc[i] == t.enc[i - 1] => g.1 = i + 1,
				_ => v.push((i, i + 1)),
			}
		}
		v
	}

	/// top-K wrap budget: sum of the capacity.subsigs largest
	/// (chain+1) in the store; row budget capacity-only BOTH modes.
	#[test]
	fn test_r1_wrap_budget_and_rows_size() {
		let info = a18_store();
		assert_eq!(StepQueueNeo::<Fr>::n_wrap_keys(&vec![f(1)],
			&info), 9); // 8 steps + 1
		let mut cap = fixture_capacity();
		//derived = top-K chain sum (a18 store = one chain of 9)
		assert_eq!(StepQueueNeo::<Fr>::wrap_budget(&cap, &info), 9);
		cap.wrap_keys = 5;
		assert_eq!(StepQueueNeo::<Fr>::wrap_budget(&cap, &info), 5,
			"explicit wrap_keys wins");
		cap.wrap_keys = 0;
		cap.subsigs = 2;
		assert_eq!(StepQueueNeo::<Fr>::wrap_budget(&cap, &info), 9,
			"top-K truncates at the store size");
		cap.subsigs = 1;
		let (n, _, _) = StepQueue::<Fr>::vec_size(
			&StepQueueType::ResLarge, &cap);
		assert_eq!(StepQueueNeo::<Fr>::qm_rows_size(&cap, &info),
			n + 18, "2 wraps per budget key");
		cap.b_aggressive = true;
		assert_eq!(StepQueueNeo::<Fr>::qm_rows_size(&cap, &info),
			n + 18, "capacity-only: mode-independent");
		//inversion: smallest K covering the demand
		assert_eq!(StepQueueNeo::<Fr>::wrap_subsigs_for(&info, 9),
			1);
		assert_eq!(StepQueueNeo::<Fr>::wrap_subsigs_for(&info, 1),
			1);
	}

	/// a pooled T_qm overflow must name the param that is actually
	/// over its nominal share, in that param's own units, so
	/// determine_config can bump it (both sides, and never empty).
	#[test]
	fn test_r1_qm_caperr_attribution() {
		//chains (chain+1) = [9, 5, 3]: top-K inversion material
		let mk = |lens: &[usize]| -> SubsigStepStore {
			let mut m = std::collections::HashMap::new();
			let mut ids = vec![];
			for (i, l) in lens.iter().enumerate() {
				let pm = (0..*l).map(|j| (j + 1, (1, 9)))
					.collect::<Vec<_>>();
				m.insert(i + 1,
					data_processor::type_def::SubsigStepStoreItem {
					subsig_id: i + 1, igc: false,
					vec_pm_bounds: pm, is_backward: false });
				ids.push(i + 1);
			}
			SubsigStepStore { subsig_ids: ids,
				subsig_to_steps: m, b_aggressive: false }
		};
		let info = mk(&[8, 4, 2]);
		let mut cap = fixture_capacity();
		cap.b_aggressive = true;
		cap.max_nibble_len = 1000;
		let names = |e: Error| -> Vec<(String, usize)> {
			match e { Error::CapErr(v) => v, _ => panic!("not CapErr") }
		};
		// wrap over only: 12 keys vs 9 budget -> top-2 (9+5) covers
		let v = names(StepQueueNeo::<Fr>::qm_caperr(
			&cap, false, &info, 12, 9, 0, 100));
		assert_eq!(v.len(), 1);
		assert!(v[0].0.starts_with("dis_adv::neo_wrap_subsigs"));
		assert_eq!(v[0].1, 2, "smallest K with top-K sum >= 12");
		// real over only: 50 rows vs 10 -> prod back-solved
		let v = names(StepQueueNeo::<Fr>::qm_caperr(
			&cap, false, &info, 1, 9, 50, 10));
		assert_eq!(v.len(), 1);
		assert!(v[0].0.starts_with("dis_adv::prod_pats_expansion"));
		assert_eq!(v[0].1, 50 * 100_000_000 / (1000 * 100));
		// both over -> both reported
		let v = names(StepQueueNeo::<Fr>::qm_caperr(
			&cap, true, &info, 12, 9, 50, 10));
		assert_eq!(v.len(), 2);
		assert!(v.iter().all(|x| x.0.contains("b_igc: true")));
		// non-aggressive routes to perc, not prod
		cap.b_aggressive = false;
		let v = names(StepQueueNeo::<Fr>::qm_caperr(
			&cap, false, &info, 1, 9, 50, 10));
		assert!(v[0].0.starts_with("dis_adv::perc_pats_expansion_rate"));
	}

	/// the class universe the P2 cubic now enforces in-circuit:
	/// {0,C,FP} aggressive, {0,C,FP,BP,SP} non-aggressive, and the
	/// aggressive arm reaches it by retagging BP -> C.
	#[test]
	fn test_r1_qm_table_cat_universe() {
		let (info, g) = core_plain();
		let ta = g.gen_qm_table(&info, true).expect("aggr table");
		let tn = g.gen_qm_table(&info, false).expect("nonaggr");
		let ok_a = [f(0), f(CAT_C), f(CAT_FP)];
		assert!(ta.cat.iter().all(|c| ok_a.contains(c)),
			"aggr cat outside {{0,C,FP}}");
		let n_x = |t: &QmTable<Fr>, c0: u32| t.cat.iter()
			.filter(|c| **c == f(c0)).count();
		assert_eq!(n_x(&ta, CAT_C),
			n_x(&tn, CAT_C) + n_x(&tn, CAT_BP),
			"aggr C == nonaggr C + BP (the retag)");
		assert_eq!(n_x(&ta, CAT_FP), n_x(&tn, CAT_FP));
		assert!(n_x(&tn, CAT_BP) > 0, "fixture must exercise BP");
		let (info2, gs) = core_sp();
		let ts = gs.gen_qm_table(&info2, false).expect("sp table");
		let ok_n = [f(0), f(CAT_C), f(CAT_FP), f(CAT_BP), f(CAT_SP)];
		assert!(ts.cat.iter().all(|c| ok_n.contains(c)));
		assert!(n_x(&ts, CAT_SP) > 0, "fixture must exercise SP");
	}

	/// SP is structurally non-aggressive: handing an SP-tagged core
	/// to the aggressive table must abort, not silently retag.
	#[test]
	#[should_panic(expected = "aggr: unexpected cat")]
	fn test_r1_qm_table_aggr_rejects_sp() {
		let (info, g) = core_sp();
		let _ = g.gen_qm_table(&info, true);
	}

	/// every group is bracketed by its two wrap sentinels, and (the
	/// Part E fix) a step >= 1 wrap carries the chain pat, so a
	/// matched pat cannot relabel its wraps onto a no-show pat.
	#[test]
	fn test_r1_qm_table_wrap_pairs() {
		let (info, g) = core_sp();
		let t = g.gen_qm_table(&info, false).expect("table");
		let gs = groups(&t);
		assert_eq!(gs.len(), 9, "one group per (subsig, step)");
		let pm = &info.subsig_to_steps.get(&1usize).unwrap()
			.vec_pm_bounds;
		for (k, (a, b)) in gs.iter().enumerate() {
			assert!(t.id[*a].is_zero() && t.loc[*a].is_zero()
				&& t.cat[*a].is_zero(), "group {} lower wrap", k);
			let e = b - 1;
			assert!(t.loc[e] == f_max() && t.cat[e].is_zero(),
				"group {} upper wrap", k);
			let want = if k == 0 { f(0) }
				else { f(pm[k - 1].0 as u32) };
			assert_eq!(t.pat[*a], want, "lower wrap pat, group {}", k);
			assert_eq!(t.pat[e], want, "upper wrap pat, group {}", k);
		}
		for i in 0..t.enc.len() {
			if !t.enc[i].is_zero() { continue; }
			assert!(t.cat[i].is_zero() && t.loc[i].is_zero(),
				"pad row {} must be inert", i);
		}
	}

	/// rid/cid are ADDRESSES, and the two facts every cert leans on
	/// are: reachable rows get consecutive ranks inside their group
	/// (so id and id+1 really are adjacent), and cid == 1 names the
	/// group's least CARRIED loc -- the max wrap when none carries.
	#[test]
	fn test_r1_rid_cid_contract() {
		let (info, g) = core_sp();
		let t = g.gen_qm_table(&info, false).expect("table");
		let rid = NeoCore::gen_rid_native(&t);
		let cid = NeoCore::gen_cid_native(&t);
		for i in 0..t.enc.len() {
			if t.enc[i].is_zero() {
				assert!(rid[i].is_zero() && cid[i].is_zero(),
					"pad {} must not rank", i);
			}
		}
		for (a, b) in groups(&t) {
			let (mut r, mut c) = (0u32, 0u32);
			let mut least: Option<Fr> = None;
			for i in a..b {
				let cat = t.cat[i];
				if cat != f(CAT_FP) {
					assert_eq!(rid[i], f(r), "rid at row {}", i);
					r += 1;
				} else {
					assert_eq!(rid[i], f(r - 1), "FP stalls rid");
				}
				if cat.is_zero() || cat == f(CAT_C) {
					assert_eq!(cid[i], f(c), "cid at row {}", i);
					if c == 1 { least = Some(t.loc[i]); }
					c += 1;
				} else {
					assert_eq!(cid[i], f(c - 1), "non-carried stalls");
				}
			}
			let want = (a..b).filter(|i| t.cat[*i] == f(CAT_C))
				.map(|i| t.loc[i]).min_by_key(|l| field_to_usize(l))
				.unwrap_or(f_max());
			assert_eq!(least.expect("group has a cid-1 row"), want,
				"cid 1 must be the least carried loc");
		}
	}

	/// JR is a pure store-JOIN-L: one block per store row, a matched
	/// pat contributing its FULL wrapped L block and a no-show pat
	/// exactly the sentinel pair, with si_pat welded to the block's
	/// own enc on every row (the false-discharge hole).
	#[test]
	fn test_r1_gen_jr_table() {
		let info = a18_store();
		let (s_enc, s_pat) = NeoCore::<Fr>::gen_store_rows(
			&vec![f(1)], &info);
		let hm = hm_gen3(&c2_hm());
		let used: usize = s_pat.iter().map(|p|
			hm.get(p).map_or(2, |v| v.len())).sum();
		assert_eq!(used, 22);
		assert!(NeoCore::gen_jr_table(&s_enc, &s_pat, &hm,
			used - 1).is_err(), "JR over cap must CapErr");
		let cap = used + 3;
		let jr = NeoCore::gen_jr_table(&s_enc, &s_pat, &hm, cap)
			.expect("jr");
		assert_eq!(jr.enc.len(), cap);
		for i in 0..cap - used {
			assert!(jr.enc[i].is_zero() && jr.pat[i].is_zero()
				&& jr.loc[i].is_zero()
				&& jr.si_pat[i] == Fr::from(RANGE2),
				"JR pad {} must be inert with a benign si", i);
		}
		let mut at = cap - used;
		for (e, p) in s_enc.iter().zip(s_pat.iter()) {
			let want: Vec<(Fr, Fr)> = match hm.get(p) {
				Some(v) => v.clone(),
				None => vec![(f(0), f(0)), (f(1), f_max())],
			};
			for (id, loc) in &want {
				assert_eq!(jr.enc[at], *e, "row {} enc", at);
				assert_eq!(jr.pat[at], *p, "row {} pat", at);
				assert_eq!((jr.id[at], jr.loc[at]), (*id, *loc));
				assert_eq!(jr.si_pat[at],
					SubsigStepStore::gen_step_tbl_id(*e,
						ID_ENCODED_PAT), "row {} si_pat", at);
				at += 1;
			}
		}
		assert_eq!(at, cap);
	}

	/// no-show pats: DISTINCT store pats absent from L, sorted and
	/// front-padded to the store-row bound.
	#[test]
	fn test_r1_gen_ns_pat() {
		let s_pat = vec![f(1), f(3), f(3), f(5), f(0)];
		let l_pat = vec![f(3), f(3), f(9)];
		assert_eq!(NeoCore::<Fr>::gen_ns_pat(&s_pat, &l_pat, 4),
			vec![f(0), f(0), f(1), f(5)]);
		let (info, g) = core_plain();
		let (_, s2) = NeoCore::<Fr>::gen_store_rows(&vec![f(1)],
			&info);
		let (l_pat2, _, _) = l_cols3(&c2_hm());
		let ns = NeoCore::<Fr>::gen_ns_pat(&s2, &l_pat2, 8);
		assert_eq!(ns, vec![f(0), f(0), f(0), f(0),
			f(1), f(3), f(4), f(8)]);
		let _ = g;
	}

	/// the absence guard's advice: each no-show pat is bracketed by
	/// an ADJACENT pair of the sorted l_pat column, with both gaps
	/// non-negative, and the pair multiplicity table counts exactly
	/// the pats that used each pair.
	#[test]
	fn test_r1_gen_ns_advice() {
		let l_pat = vec![f(3), f(3), f(9)];
		let ns = vec![f(0), f(1), f(5)];
		let (lo, hi, mtbl) =
			NeoCore::<Fr>::gen_ns_advice(&ns, &l_pat);
		assert_eq!(lo, vec![f(0), f(0), f(1)]);
		assert_eq!(hi, vec![f(0), f(1), f(3)]);
		assert_eq!(mtbl, vec![f(1), f(0), f(1), f(0)]);
		let n_q = ns.iter().filter(|p| !p.is_zero()).count();
		assert_eq!(mtbl.iter().map(|m| field_to_usize(m))
			.sum::<usize>(), n_q, "one pair hit per no-show pat");
		let top = Fr::from(1u64 << read_global_config().range2_bit);
		let (lo2, hi2, m2) = NeoCore::<Fr>::gen_ns_advice(
			&vec![f(11)], &l_pat);
		assert_eq!(lo2, vec![f(11) - f(1) - f(9)]);
		assert_eq!(hi2, vec![top - f(11) - f(1)]);
		assert_eq!(m2, vec![f(0), f(0), f(0), f(1)],
			"a pat above every L pat uses the TOP pair");
	}

	/// a pat that IS in L has no straddling pair -- the generator
	/// must refuse rather than emit an advice a verifier accepts.
	#[test]
	#[should_panic(expected = "no straddling pair")]
	fn test_r1_gen_ns_advice_pat_in_l() {
		NeoCore::<Fr>::gen_ns_advice(&vec![f(3)],
			&vec![f(3), f(9)]);
	}

	/// aggressive m-table: multiplicities are counted per TARGET
	/// tuple, so their sum must equal the number of queries the
	/// certificate layer will push (C predecessors + 2 per FP + one
	/// seed anchor per live subsig), and no FP row is ever a target.
	#[test]
	fn test_r1_mtbl_qr_balances() {
		let (info, g) = core_plain();
		let t = g.gen_qm_table(&info, true).expect("table");
		let rid = NeoCore::gen_rid_native(&t);
		let subs = vec![f(1)];
		let m = NeoCore::gen_mtbl_qr(&t, &rid, &subs);
		let n_c = (0..t.enc.len()).filter(|i|
			t.cat[*i] == f(CAT_C) && !t.step[*i].is_zero()).count();
		let n_fp = t.cat.iter().filter(|c| **c == f(CAT_FP)).count();
		assert_eq!(m.iter().map(|x| field_to_usize(x))
			.sum::<usize>(), n_c + 2 * n_fp + 1);
		for i in 0..t.enc.len() {
			if t.cat[i] == f(CAT_FP) || t.enc[i].is_zero() {
				assert!(m[i].is_zero(), "row {} must not be a QR \
					target", i);
			}
		}
	}

	/// non-aggressive split: the C-predecessor family moves to QC,
	/// so QR carries only the FP brackets and the seed anchors while
	/// QC carries C-pred + BP min + the two SP pins.
	#[test]
	fn test_r1_mtbl_qr_qc_nonaggr_balance() {
		let (info, g) = core_sp();
		let t = g.gen_qm_table(&info, false).expect("table");
		let (rid, cid) = (NeoCore::gen_rid_native(&t),
			NeoCore::gen_cid_native(&t));
		let subs = vec![f(1)];
		let qr = NeoCore::gen_mtbl_qr_nonaggr(&t, &rid, &subs);
		let cnt = |c0: u32| t.cat.iter()
			.filter(|c| **c == f(c0)).count();
		let n_c1 = (0..t.enc.len()).filter(|i|
			t.cat[*i] == f(CAT_C) && !t.step[*i].is_zero()).count();
		assert_eq!(qr.iter().map(|x| field_to_usize(x))
			.sum::<usize>(), 2 * cnt(CAT_FP) + 1);
		let mut t2 = g.gen_qm_table(&info, false).expect("table");
		t2.fill_nonaggr(&info, f(A18_DEFAULT_MIN));
		let qc = NeoCore::gen_mtbl_qc(&t2, &cid);
		assert_eq!(qc.iter().map(|x| field_to_usize(x))
			.sum::<usize>(),
			n_c1 + cnt(CAT_BP) + 2 * cnt(CAT_SP));
		for i in 0..t.enc.len() {
			let carried = t.cat[i].is_zero()
				|| t.cat[i] == f(CAT_C);
			if t.enc[i].is_zero() || !carried {
				assert!(qc[i].is_zero(), "row {} not a QC target", i);
			}
		}
	}

	/// the verdict feed: one leading zero slot absorbs every masked
	/// row, so the m-table still accounts for all n rows.
	#[test]
	fn test_r1_gen_acc_padded() {
		let (info, g) = core_plain();
		let t = g.gen_qm_table(&info, true).expect("table");
		let (acc, mtbl) = NeoCore::gen_acc_padded(&t, &info);
		assert_eq!(acc.len(), mtbl.len());
		assert!(acc[0].is_zero(), "leading slot absorbs masked rows");
		assert_eq!(mtbl.iter().map(|m| field_to_usize(m))
			.sum::<usize>(), t.enc.len(),
			"every Q_m row lands in exactly one acc slot");
	}
}

// ============================================================
//   M6 tests: tier-1 direct-cs aggressive core
// ============================================================
// NOTE_NEW8_ADAPTED (P3 R2): harness rebuilt for the New8 column
// set (l_id/mtbl_tm/ns_*/union_prf/JR in, the six counting cols
// out) and repointed at the assert_neo_aggr entry.
#[cfg(test)]
pub(crate) mod tests_neo_m6 {
	use super::*;
	use super::tests_neo_m4::fixture_capacity;
	use super::tests_neo_r1::{l_cols3, hm_gen3};
	use ark_bn254::Fr;
	use ark_relations::r1cs::{ConstraintSystem,
		ConstraintSystemRef};
	use crate::gadgets::commons::new_var;
	use data_processor::type_def::{SubsigStepStore,
		SubsigStepStoreItem};

	fn f(x: u32) -> Fr { Fr::from(x) }

	/// the 3-column pat_loc the New8 join reads (pat, id, loc).
	pub(crate) fn hm_to_l_cols(m: &HashMap<u32, Vec<u32>>)
	-> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
		l_cols3(m)
	}

	/// hm in the generator's (id, loc) wrapped format.
	pub(crate) fn hm_gen(m: &HashMap<u32, Vec<u32>>)
	-> HashMap<Fr, Vec<(Fr, Fr)>> {
		hm_gen3(m)
	}

	/// assemble the full native bundle from a generator output
	/// (thin wrapper over NeoCore::gen on hm-derived L cols).
	pub(crate) fn build_core_native(gen: &StepQueueNeo<Fr>,
		info: &SubsigStepStore, hm: &HashMap<u32, Vec<u32>>)
	-> NeoCore<Fr> {
		let (l_pat, l_id, l_loc) = hm_to_l_cols(hm);
		NeoCore::gen(gen, info, l_pat, l_id, l_loc)
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
			d_above_lo: av(&t.d_above_lo), d_sort: av(&t.d_sort),
			si_step: av(&t.si_step), si_subsig: av(&t.si_subsig),
			si_pat: av(&t.si_pat), si_rg1: av(&t.si_rg1),
			si_rg2: av(&t.si_rg2),
			si_enc_prev: av(&t.si_enc_prev),
			si_b_bwd: av(&t.si_b_bwd),
			nonaggr: alloc_nonaggr_vars(cs, &t.nonaggr),
		};
		NeoCoreVars { qm, l_pat: av(&nat.l_pat),
			l_id: av(&nat.l_id), l_loc: av(&nat.l_loc),
			subsigs: av(&nat.subsig_nat), s_enc: av(&nat.s_enc),
			mtbl_qr: av(&nat.mtbl_qr), mtbl_tm: av(&nat.mtbl_tm),
			ns_pat: av(&nat.ns_pat), d_ns_lo: av(&nat.d_ns_lo),
			d_ns_hi: av(&nat.d_ns_hi), mtbl_ns: av(&nat.mtbl_ns),
			acc_out: av(&nat.acc_out),
			mtbl_acc: av(&nat.mtbl_acc),
			qi_enc: av(&nat.qi_enc), qi_loc: av(&nat.qi_loc),
			qc_enc: av(&nat.qc_enc), qc_loc: av(&nat.qc_loc),
			mtbl_qc: av(&nat.mtbl_qc),
			union_prf: av(&nat.union_prf),
			jr: JrVars { enc: av(&nat.jr.enc),
				pat: av(&nat.jr.pat), id: av(&nat.jr.id),
				loc: av(&nat.jr.loc),
				si_pat: av(&nat.jr.si_pat) } }
	}

	/// allocate the non-aggressive witness mirror (empty in aggr).
	pub(crate) fn alloc_nonaggr_vars(cs: &ConstraintSystemRef<Fr>,
		na: &QmNonAggrCols<Fr>) -> QmNonAggrVars<Fr> {
		let av = |v: &Vec<Fr>| v.iter().map(|x| new_var(cs, *x))
			.collect::<Vec<FpVar<Fr>>>();
		QmNonAggrVars {
			enc_next: av(&na.enc_next),
			bp_prev_val: av(&na.bp_prev_val),
			rg2_next: av(&na.rg2_next), w_next: av(&na.w_next),
			d_bp: av(&na.d_bp), fz: av(&na.fz),
			enc_fz: av(&na.enc_fz),
			fz_step_val: av(&na.fz_step_val),
			fz_sub_val: av(&na.fz_sub_val), w_fz: av(&na.w_fz),
			d_fz: av(&na.d_fz), w_kept: av(&na.w_kept),
			d_kept: av(&na.d_kept),
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
		(run_nat_aggr(&nat), nat)
	}

	/// allocate a (possibly tampered) native bundle and run the
	/// aggressive entry over it.
	pub(crate) fn run_nat_aggr(nat: &NeoCore<Fr>)
	-> ConstraintSystemRef<Fr> {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = alloc_vars(&cs, nat);
		let r1 = new_var(&cs, Fr::from(12345u32));
		let r2 = new_var(&cs, Fr::from(67890u32));
		DischargeAdvNeoGadget::<Fr>::assert_neo_aggr(
			cs.clone(), nat, &vars, &r1, &r2, 0)
			.expect("assert core");
		cs
	}

	/// recompute every derived advice table of the AGGRESSIVE bundle
	/// from its (tampered) T_qm / s_enc / L. A negative test uses
	/// this so the forgery is not caught by some stale multiplicity
	/// it forgot to update -- only the real defence may fire.
	pub(crate) fn regen_aggr_advice(nat: &mut NeoCore<Fr>,
		info: &SubsigStepStore, s_pat: &[Fr]) {
		let rid = NeoCore::gen_rid_native(&nat.t);
		nat.mtbl_qr = NeoCore::gen_mtbl_qr(&nat.t, &rid,
			&nat.subsig_nat);
		nat.ns_pat = NeoCore::gen_ns_pat(s_pat, &nat.l_pat,
			nat.s_enc.len());
		let (lo, hi, mns) = NeoCore::gen_ns_advice(&nat.ns_pat,
			&nat.l_pat);
		nat.d_ns_lo = lo; nat.d_ns_hi = hi; nat.mtbl_ns = mns;
		nat.mtbl_tm = NeoCore::gen_mtbl_tm_aggr(&nat.t, &nat.l_pat,
			&nat.l_id, &nat.l_loc, &nat.ns_pat);
		let (a, m) = NeoCore::gen_acc_padded(&nat.t, info);
		nat.acc_out = a; nat.mtbl_acc = m;
	}

	/// the store pats of a18_store, in s_enc row order.
	pub(crate) fn a18_s_pat() -> Vec<Fr> {
		NeoCore::<Fr>::gen_store_rows(&vec![f(1)],
			&super::tests_neo_m5::a18_store()).1
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

	/// P2d OFF-STORE L PAT: pat 9 matches in the chunk but no store
	/// step uses it. The old counting design had to reject this (a
	/// cnt=0 dictionary row); the New8 join is driven BY THE STORE
	/// ROWS, so an unreferenced L row is simply a lookup target
	/// nobody queries -- it must be accepted, change no Q_m row, and
	/// leave its membership multiplicity at zero.
	#[test]
	fn test_m6_corner_offstore_l_pat() {
		let info = super::tests_neo_m5::a18_store();
		let mut hm = fig14_hm();
		let (cs0, nat0) = run_core_aggr(&info, &hm, 161, None);
		assert!(cs0.is_satisfied().unwrap());
		hm.insert(9, vec![50]);
		let (cs, nat) = run_core_aggr(&info, &hm, 161, None);
		assert!(cs.is_satisfied().unwrap(),
			"an off-store L pat must not break the core");
		assert_eq!(nat.t.cat, nat0.t.cat, "Q_m must be unchanged");
		assert_eq!(nat.t.loc, nat0.t.loc);
		let i9 = (0..nat.l_pat.len())
			.find(|i| nat.l_loc[*i] == f(50)).expect("l row 9");
		assert!(nat.mtbl_tm[i9].is_zero(),
			"nobody queries the off-store row");
	}

	/// P2e DUPLICATE LOC ACROSS PATS: a3 also matches at loc 33 =
	/// a4's C loc. The rows live in different (subsig, step) groups,
	/// so per-group sorting is untouched; a3:33 is FP (no a2
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
		assert_eq!(get("l_id"), nat.l_id);
		assert_eq!(get("l_loc"), nat.l_loc);
		assert_eq!(get("mtbl_qr"), nat.mtbl_qr);
		assert_eq!(get("mtbl_tm"), nat.mtbl_tm);
		assert_eq!(get("ns_pat"), nat.ns_pat);
		assert_eq!(get("d_ns_lo"), nat.d_ns_lo);
		assert_eq!(get("d_ns_hi"), nat.d_ns_hi);
		assert_eq!(get("mtbl_ns"), nat.mtbl_ns);
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
	/// stay inside a +/-25% band of the calibrated 2763 cs over 34
	/// rows -- catches accidental constraint blowup later. Re-banded
	/// in P3 R2 (was 3429 under M6; New8 drops the counting block
	/// and slims the frame). Block split at n = 34:
	///   selectors 613, wf 670, si_pins 306, join 176, ns_gap 114,
	///   carry 102, fwd_prune 204, seed_anchors 3, lookups 314,
	///   verdict 108.
	#[test]
	fn test_m6_cost_band() {
		let info = super::tests_neo_m5::a18_store();
		let (cs, nat) = run_core_aggr(&info, &fig14_hm(), 161,
			None);
		assert!(cs.is_satisfied().unwrap());
		assert_eq!(nat.t.enc.len(), 34);
		let n = cs.num_constraints();
		assert!(n >= 2072 && n <= 3454,
			"cost drift: {} cs vs calibrated 2763", n);
	}
}

// NOTE_NEW8_ADAPTED (P3 R2): forgeries re-aimed at the New8
// defences -- the counting attacks became no-show/membership
// attacks, and every tamper now regenerates its derived advice.
#[cfg(test)]
mod tests_neo_m6_neg {
	use super::*;
	use super::tests_neo_m6::{run_core_aggr, run_nat_aggr,
		regen_aggr_advice, a18_s_pat, hm_to_l_cols};
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

	/// n1 omission of a match: the generator runs WITHOUT a6:96, so
	/// no Q_m row demands it, but the committed pat_loc still lists
	/// it. Under New8 the counting logup is gone; the defence is the
	/// JOIN's membership lookup -- dropping a middle loc renumbers
	/// the survivors, so Q_m's (pat, id, loc) for 141 becomes
	/// (6, 3, 141) while L holds (6, 4, 141): no target, UNSAT.
	#[test]
	fn test_m6_neg_drop_match() {
		let info = a18_store();
		let mut hm_red = fig14_hm();
		hm_red.insert(6, vec![73, 79, 141]); // 96 omitted
		let seed = StepQueueItem::new(f(1), f(0), f(0), f(0), f(0),
			vec![f(1)]);
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed]);
		let carried = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m,
			&super::tests_neo_m4::fixture_capacity(),
			StepQueueType::ResLarge, false));
		let gen = carried.gen_shared_core_from_hm(0,
			&super::tests_neo_m6::hm_gen(&hm_red), &info, f(161))
			.expect("shared core");
		// Q_m from the REDUCED match set, L from the full one
		let (lp, li, ll) = hm_to_l_cols(&fig14_hm());
		let nat = NeoCore::gen(&gen, &info, lp, li, ll)
			.expect("core");
		assert!(!run_nat_aggr(&nat).is_satisfied().unwrap());
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
						&mut t.d_below_lo, &mut t.d_above_lo,
						&mut t.d_sort] { v.push(Fr::from(0u32)); }
					let rg2t = Fr::from(RANGE2);
					for v in [&mut t.si_subsig, &mut t.si_pat,
						&mut t.si_rg1, &mut t.si_rg2,
						&mut t.si_enc_prev] { v.push(rg2t); }
				}
				// keep every derived table honest for the new rows
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
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

	/// n4 unity escape: cat=7 on a real row. Under New8 this dies
	/// EARLIER than it used to -- at the class cubic
	/// cat(cat-1)(cat-2)=0 in assert_neo_selectors, not at the wrap
	/// residual -- because the class bits are now Lagrange
	/// expressions of cat rather than independently welded columns.
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
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n2 hygiene: (a) a pad row given a nonzero loc payload -> the
	/// is_pad*loc force fires; (b) row 0 made non-pad -> the
	/// key[0]==0 anchor (plus pad-monotone) fires; (c) THE SPLIT
	/// DEFECT New8 fixed: a pad carrying cat = CAT_FP and the
	/// compensating loc = -CAT_FP passed the old FUSED force
	/// is_pad*(loc+cat)=0, which sums to zero without either term
	/// being zero. That pad reads as is_wrap = -1: a NEGATIVE logup
	/// multiplicity and a rid decrement. It must now be UNSAT at
	/// is_pad*cat = 0.
	#[test]
	fn test_m6_neg_pad_hygiene() {
		for case in 0..3 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					assert!(nat.t.n_pad >= 1);
					if case == 0 { nat.t.loc[0] = Fr::from(5u32); }
					else if case == 1 {
						nat.t.enc[0] = Fr::from(123u32);
					} else {
						nat.t.cat[0] = Fr::from(CAT_FP);
						nat.t.loc[0] = -Fr::from(CAT_FP);
					}
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"pad hygiene case {}", case);
		}
	}

	/// n14 CLASS EXCLUSIVITY: a junk cat cannot make a row count as
	/// both C and FP at once. The class bits are Lagrange
	/// expressions of cat -- is_c = 2cat - cat^2, is_fp =
	/// (cat^2-cat)/2 -- so is_c + is_fp = 1 has exactly the two
	/// roots 1 and 2; anything else (here cat = 3 on the
	/// aggressive arm, whose universe is {0,1,2}) breaks the cubic.
	/// This matters beyond bookkeeping: assert_logup_cond multiplies
	/// the inverse by the selector, so a non-boolean selector would
	/// count one query twice.
	#[test]
	fn test_m6_neg_cat_exclusivity() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(27u32)).unwrap();
				t.cat[i] = Fr::from(CAT_BP); // 3: nonaggr-only
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
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
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// remove row i from every QmTable column (negative-test tamper).
	fn remove_row(t: &mut QmTable<Fr>, i: usize) {
		let cols: [&mut Vec<Fr>; 26] = [
			&mut t.enc, &mut t.id, &mut t.loc, &mut t.cat,
			&mut t.step, &mut t.subsig, &mut t.prev_id1,
			&mut t.prev_loc1, &mut t.prev_loc2, &mut t.pat,
			&mut t.rg1, &mut t.rg2, &mut t.enc_prev, &mut t.b_bwd,
			&mut t.d_c1, &mut t.d_c2, &mut t.d_below_lo,
			&mut t.d_above_lo, &mut t.d_sort, &mut t.si_step,
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
				t.d_sort[i0] = mx;
				for i in t.n_pad..t.enc.len() {
					if t.enc[i].is_zero() || t.loc[i].is_zero()
						|| t.loc[i] == mx { continue; }
					t.cat[i] = Fr::from(CAT_FP);
					t.prev_id1[i] = Fr::from(0u32);
					t.prev_loc1[i] = Fr::from(0u32);
					t.prev_loc2[i] = mx;
					for v in [&mut t.d_c1, &mut t.d_c2,
						&mut t.d_below_lo, &mut t.d_above_lo] {
						v[i] = Fr::from(0u32);
					}
				}
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n9-dup AGGR DUPLICATE ROW: move a real row onto its group
	/// mate (7:101 -> 131), a clone the non-strict sort accepts
	/// with honest d_sort. The aggr defence is the join id-chain
	/// bijection: the clone's (pat, id, 131) query cites 101's id
	/// with 131's loc -- not an L row -- and 101's own L row goes
	/// unqueried. The join (the union's aggr counterpart) objects
	/// regardless of the regenerated rank/membership advice.
	#[test]
	fn test_m6_neg_duplicate_row() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				let t = &mut nat.t;
				let i = (t.n_pad..t.enc.len()).find(|&i|
					t.loc[i] == Fr::from(101u32)).unwrap();
				assert!(t.enc[i + 1] == t.enc[i]
					&& t.loc[i + 1] == Fr::from(131u32));
				t.loc[i] = Fr::from(131u32);
				let n = t.enc.len();
				for j in 1..n { //honest non-strict rebind
					t.d_sort[j] = if t.enc[j] == t.enc[j - 1]
						&& !t.enc[j].is_zero()
						{ t.loc[j] - t.loc[j - 1] }
						else { Fr::from(0u32) };
				}
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	// NOTE_NEW8_OBSOLETE (P3 R2): the old n10 D-family forgeries
	// (lied cnt, m_aux mismatch) attacked the counting block, which
	// New8 deleted along with d_pat/d_cnt/m_aux/mtbl_d. Its role --
	// "you cannot lie about a pattern's presence" -- is carried by
	// the no-show gap guard, attacked here instead.

	/// n10-prime NO-SHOW FORGERY: pat 3 DOES match in this chunk, but
	/// the prover lists it as a no-show so a sentinel-only block
	/// could hide its matches. assert_ns_gap demands an ADJACENT
	/// pair of the sorted l_pat column straddling the claimed pat;
	/// pat 3 sits IN that column, so no such pair exists and the
	/// gap lookup cannot balance. (a) zero gaps, (b) zero gaps plus
	/// a hand-bumped pair multiplicity.
	#[test]
	fn test_m6_neg_ns_forgery() {
		for case in 0..2 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					let j = nat.ns_pat.iter().position(|p|
						p.is_zero()).expect("a free ns slot");
					nat.ns_pat[j] = Fr::from(3u32);
					nat.d_ns_lo[j] = Fr::from(0u32);
					nat.d_ns_hi[j] = Fr::from(0u32);
					if case == 1 {
						let k = nat.mtbl_ns.len() - 1;
						nat.mtbl_ns[k] += Fr::from(1u32);
					}
					nat.mtbl_tm = NeoCore::gen_mtbl_tm_aggr(&nat.t,
						&nat.l_pat, &nat.l_id, &nat.l_loc,
						&nat.ns_pat);
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"no-show forgery case {}", case);
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
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n12 joint store-drop: full a1..a8 match, but the prover drops
	/// the step-8 GROUP together with its s_enc row, so nothing is
	/// left inconsistent inside the table and the match simply
	/// vanishes. Must be UNSAT via the wf run-completeness lemma:
	/// the surviving final group carries a NORMAL step tag, and a
	/// run has to end on a LAST-tagged one.
	#[test]
	fn test_m6_neg_joint_store_drop() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let mut s_pat = a18_s_pat();
		s_pat.pop(); // step 8 = the last store row
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm, 161,
			Some(&move |nat: &mut NeoCore<Fr>| {
				let f8 = Fr::from(8u32);
				let t = &mut nat.t;
				for i in (t.n_pad..t.enc.len()).rev() {
					if t.step[i] == f8 { remove_row(t, i); }
				}
				nat.s_enc.pop();
				regen_aggr_advice(nat, &a18_store(), &s_pat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

	/// n13 tail truncation x3: the same joint drop for steps 6..8 --
	/// the run now ends at the NORMAL-tagged step-5 group, so the
	/// final-run clause of the same lemma fires.
	#[test]
	fn test_m6_neg_tail_truncation() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		let mut s_pat = a18_s_pat();
		s_pat.truncate(5);
		let (cs, _nat) = run_core_aggr(&a18_store(), &hm, 161,
			Some(&move |nat: &mut NeoCore<Fr>| {
				let dropped = [Fr::from(6u32), Fr::from(7u32),
					Fr::from(8u32)];
				let t = &mut nat.t;
				for i in (t.n_pad..t.enc.len()).rev() {
					if dropped.contains(&t.step[i]) {
						remove_row(t, i);
					}
				}
				nat.s_enc.truncate(5);
				regen_aggr_advice(nat, &a18_store(), &s_pat);
			}));
		assert!(!cs.is_satisfied().unwrap());
	}

}

// ============================================================
//   M6 tier-2 tests: full harness (si / outer lookups live)
// ============================================================
// NOTE_NEW8_ADAPTED (P3 R5: aggressive tier-2 end-to-end through
// the real harness).
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
			res_small_cost: DischargeAdvCapacity::default_res_small(),
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

	/// H5 duplicate-row clone: clone the 2nd row of the 2-loc "ab"
	/// group onto the 1st. The (now non-strict) sort accepts it
	/// with an honest d_sort = 0, but the aggr join's id-chain
	/// bijection kills it: the clone's (pat, id, loc) query cites
	/// id 2 with id 1's loc, which is not an L row (and the
	/// original 2nd loc goes missing from the block).
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
				t.d_sort[i2] = Fr::from(0u32); //honest dup bind
				t.d_sort[i2 + 1] = if t.enc[i2 + 1] == t.enc[i2] {
					t.loc[i2 + 1] - t.loc[i2]
				} else { t.d_sort[i2 + 1] };
				let rid = NeoCore::gen_rid_native(t);
				nat.mtbl_qr = NeoCore::gen_mtbl_qr(t, &rid,
					&nat.subsig_nat);
			}));
		get_global_config().basis_failed_subsigs = 0;
	}
}

// NOTE_NEW8_ADAPTED (P3 R3): repointed at gen_nonaggr's 3-column L
// and the assert_neo_nonaggr entry; the b_l / m_carry_in goldens
// went with the columns New8 deleted.
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
		let (l_pat, l_id, l_loc) = hm_to_l_cols(hm);
		let (mut nat, _qi, _qc) = NeoCore::gen_nonaggr(&gen, info,
			l_pat, l_id, l_loc, &hm_gen(hm), carried_sq,
			f(default_min), 0).expect("gen_nonaggr");
		if let Some(tf) = tamper { tf(&mut nat); }
		(run_nat_nonaggr(&nat, default_min), nat)
	}

	/// allocate a (possibly tampered) native bundle and run the
	/// non-aggressive entry over it.
	pub(crate) fn run_nat_nonaggr(nat: &NeoCore<Fr>,
		default_min: u32) -> ConstraintSystemRef<Fr> {
		let cs = ConstraintSystem::<Fr>::new_ref();
		let vars = alloc_vars(&cs, nat);
		let r1 = new_var(&cs, Fr::from(12345u32));
		let r2 = new_var(&cs, Fr::from(67890u32));
		let dmin = new_var(&cs, f(default_min));
		DischargeAdvNeoGadget::<Fr>::assert_neo_nonaggr(
			cs.clone(), nat, &vars, &dmin, &r1, &r2, 0)
			.expect("assert core nonaggr");
		cs
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
		//SP 111: fz=5, w_fz=39 (a5 carries), w_kept=21 (kept min),
		//d_kept = 111-21-1 = 89, d_fz = max-39-1.
		let i111 = row(111);
		assert_eq!(t.cat[i111], f(CAT_SP));
		assert_eq!(na.fz[i111], f(5));
		assert_eq!(na.w_fz[i111], f(39));
		assert_eq!(na.d_fz[i111], mx - f(40));
		assert_eq!(na.w_kept[i111], f(21));
		assert_eq!(na.d_kept[i111], f(89));
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
		assert_eq!(get("enc_next"), nat.t.nonaggr.enc_next);
		assert_eq!(get("bp_prev_val"), nat.t.nonaggr.bp_prev_val);
		assert_eq!(get("w_next"), nat.t.nonaggr.w_next);
		assert_eq!(get("d_bp"), nat.t.nonaggr.d_bp);
		assert_eq!(get("enc_fz"), nat.t.nonaggr.enc_fz);
		assert_eq!(get("w_fz"), nat.t.nonaggr.w_fz);
		assert_eq!(get("w_kept"), nat.t.nonaggr.w_kept);
		assert_eq!(get("d_kept"), nat.t.nonaggr.d_kept);
		assert_eq!(get("mtbl_qc"), nat.mtbl_qc);
		assert_eq!(get("union_prf"), nat.union_prf);
		assert_eq!(get("jr_enc"), nat.jr.enc);
		assert_eq!(get("jr_pat"), nat.jr.pat);
		assert_eq!(get("jr_id"), nat.jr.id);
		assert_eq!(get("jr_loc"), nat.jr.loc);
		assert_eq!(get("si_jr_pat"), nat.jr.si_pat);
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
		// Re-banded in P3 R3 (was 5277 under M7); union/seed fix
		// added +36 (b_seed bits + seed-key logup). Block split at
		// n = 34: selectors 681, wf 670, si_pins 306 + 476,
		// join 349, union 194, ns_gap 75, carry 233, fwd 170,
		// bwd 171, singleton 137, anchors 3, lookups 763.
		assert!(n >= 3360 && n <= 5600,
			"cost drift: {} cs vs calibrated 4516", n);
	}

	/// CIRCUIT CORNERS: (a) EMPTY-L chunk (carried-only): the BP
	/// cascade prunes a6 {73,79} against default_min and the
	/// a2..a5 chain re-certifies, with every JR block collapsed to
	/// its no-show sentinel pair. (b) FRESH-L chunk: a match at a
	/// location no carried row holds -- the union pairs it through
	/// the join, not the carry.
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
		let n_real = nat.jr.enc.iter()
			.filter(|e| !e.is_zero()).count();
		assert_eq!(n_real, 2 * 8, "8 store rows, sentinel pairs");
		//(b) one fresh match
		let mut hm = HashMap::new();
		hm.insert(6, vec![96]);
		let (cs2, nat2) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &hm,
			A18_DEFAULT_MIN, None);
		assert!(cs2.is_satisfied().unwrap(), "unsat: {:?}",
			cs2.which_is_unsatisfied());
		let t2 = &nat2.t;
		assert!((t2.n_pad..t2.enc.len()).any(|i|
			t2.loc[i] == f(96) && !t2.cat[i].is_zero()),
			"the fresh match must reach Q_m");
	}

	/// CHUNK-STRADDLE DUPLICATE (the option-1 fix): a carried loc
	/// that matches AGAIN in this chunk keeps BOTH copies in Q_m
	/// (no dedup), so the union pays one to q_i and one to the
	/// join, and the non-strict sort accepts the equal neighbors.
	/// Was a should_panic guard test before the union/seed fix.
	#[test]
	fn test_nonaggr_straddle_duplicate() {
		let info = a18_store();
		let mut hm = HashMap::new();
		hm.insert(6, vec![79]); // 79 is already carried
		let (cs, nat) = run_core_nonaggr(&info,
			&a18_carried().to_stepqueue(), &hm,
			A18_DEFAULT_MIN, None);
		assert!(cs.is_satisfied().unwrap(), "unsat: {:?}",
			cs.which_is_unsatisfied());
		let t = &nat.t;
		let dups = (t.n_pad + 1..t.enc.len()).filter(|&i|
			t.enc[i] == t.enc[i - 1] && t.loc[i] == t.loc[i - 1]
			&& t.loc[i] == f(79)).count();
		assert_eq!(dups, 1, "the straddle pair must be in Q_m");
	}
}

// NOTE_NEW8_ADAPTED (P3 R3): the carry-in and b_l attacks became
// union and JR-pin attacks; w_sp/d_sp renamed to w_kept/d_kept.
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
			d_below_lo, d_above_lo, d_sort,
			si_step, si_subsig, si_pat, si_rg1, si_rg2,
			si_enc_prev, si_b_bwd);
		let na = &mut t.nonaggr;
		macro_rules! rmna { ($($c:ident),*) => {
			$( na.$c.remove(i); )* } }
		rmna!(enc_next, bp_prev_val, rg2_next, w_next, d_bp,
			fz, enc_fz, fz_step_val, fz_sub_val, w_fz, d_fz,
			w_kept, d_kept, si_bp_prev, si_rg2_next, si_fz,
			si_fz_step, si_fz_sub);
		//recompute d_sort (a removed row changes an adjacency) and
		//fix ids within the group (ids stay contiguous).
		let n = t.enc.len();
		for j in 1..n {
			t.d_sort[j] = if t.enc[j] == t.enc[j - 1]
				&& !t.enc[j].is_zero()
				{ t.loc[j] - t.loc[j - 1] }
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
	/// row a6:73 from Q_m. Every cert still verifies (73 was pruned
	/// anyway) and both rank m-tables are regenerated -- what
	/// catches the drop is assert_qm_union: the committed q_i row
	/// (enc6, 73) is on the left of Q_m = q_i u JR with nothing on
	/// the right to pair with. This is what forces every carried
	/// row to be merged and classified, not quietly discarded.
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

	// NOTE_NEW8_OBSOLETE (P3 R3): the old N3 attacked the b_l
	// merge bit, a column New8 removed (the union subsumes the
	// routing it encoded). Its successors are N3a and N3b below.

	/// N3a JR si_pat HOLE (the false-discharge case the New8 frame
	/// round found): a JOIN block belonging to store row A carries
	/// si_pat = tag(enc_B, PAT) for a DIFFERENT store row B. The
	/// outer lookup only binds the PAIR (si_pat, jr.pat), so it is
	/// a genuine DB pair and cannot object; if nothing tied si_pat
	/// to the block's OWN enc, A could present B's block -- pick a
	/// no-show B and A looks match-free, killing a live chain.
	/// Check (5) of assert_neo_si_pins_nonaggr is the only defence.
	#[test]
	fn test_nonaggr_neg_jr_si_pat() {
		let info = a18_store();
		let (s_enc, _s_pat) = NeoCore::<Fr>::gen_store_rows(
			&vec![f(1)], &info);
		// B = step 3 (pat 3, no match in chunk 2); the block we
		// relabel belongs to step 2, so the tag really is foreign.
		let enc_b = s_enc[2];
		let tag_b = SubsigStepStore::gen_step_tbl_id(enc_b,
			ID_ENCODED_PAT);
		let enc_a = s_enc[1];
		assert_ne!(enc_a, enc_b);
		expect_unsat("jr si_pat from a foreign store row", &|nat| {
			let jr = &mut nat.jr;
			let mut hit = 0;
			for k in 0..jr.enc.len() {
				if jr.enc[k] == enc_a {
					jr.si_pat[k] = tag_b;
					hit += 1;
				}
			}
			assert!(hit > 0, "no JR block for the chosen store row");
		});
	}

	/// N3b UNION TAMPERS, both sides of Q_m = q_i u JR: (a) blank a
	/// real JR row, so a joined location is no longer paid for;
	/// (b) move a Q_m location, so the right side no longer matches
	/// what the carry and the join together claim; (c) clone by
	/// overwrite -- move 96 onto its group-mate 141, forming a
	/// duplicate pair the (non-strict) sort now ACCEPTS with an
	/// honest d_sort of 0: the second 141 has no q_i/JR partner
	/// and 96 goes unpaid. All three break the multiset identity.
	#[test]
	fn test_nonaggr_neg_union() {
		expect_unsat("drop a JR row", &|nat| {
			let k = (0..nat.jr.enc.len()).find(|&k|
				!nat.jr.enc[k].is_zero()
				&& !nat.jr.loc[k].is_zero()).unwrap();
			nat.jr.enc[k] = f(0); nat.jr.pat[k] = f(0);
			nat.jr.id[k] = f(0); nat.jr.loc[k] = f(0);
			nat.jr.si_pat[k] = f(RANGE2);
		});
		expect_unsat("move a Q_m loc", &|nat| {
			let i = row(nat, 96);
			nat.t.loc[i] = f(97);
			regen_mtbls(nat);
		});
		expect_unsat("clone a Q_m loc", &|nat| {
			let i = row(nat, 96); // a6 group also holds 141
			nat.t.loc[i] = f(141);
			let t = &mut nat.t;
			let n = t.enc.len();
			for j in 1..n { //honest non-strict d_sort rebind
				t.d_sort[j] = if t.enc[j] == t.enc[j - 1]
					&& !t.enc[j].is_zero()
					{ t.loc[j] - t.loc[j - 1] }
					else { f(0) };
			}
			regen_mtbls(nat);
		});
	}

	/// N3c FOREIGN SEED SMUGGLE: a q_i pad slot is overwritten
	/// with the seed key of a subsig OUTSIDE the statement
	/// (7 * 2^4rb). b_seed stays 0 for it (the seed-key logup
	/// admits only statement subsigs), so the row enters the
	/// union's left side with no Q_m partner. Guards the q_i-side
	/// seed mask of the union/seed fix: only true seed rows of
	/// statement subsigs may leave the identity.
	#[test]
	fn test_nonaggr_neg_foreign_seed() {
		let sh4 = {
			let b = f(1u32 << read_global_config().range2_bit);
			b * b * b * b
		};
		expect_unsat("foreign seed enc in q_i", &|nat| {
			let j = (0..nat.qi_enc.len()).find(|&j|
				nat.qi_enc[j].is_zero()).unwrap();
			nat.qi_enc[j] = f(7) * sh4;
			nat.qi_loc[j] = f(1);
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
	/// (consistent d_kept=5); the real cid-1 row of its group is
	/// 21, so (enc2, 1, 105) has no target. The prover cannot
	/// invent a closer "kept" location to justify a drop.
	#[test]
	fn test_nonaggr_neg_sp_min() {
		expect_unsat("sp fake w_kept", &|nat| {
			let i = row(nat, 111);
			nat.t.nonaggr.w_kept[i] = f(105);
			nat.t.nonaggr.d_kept[i] = f(5);
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

// ============================================================
//   P3 R4: the batch closers (assert_qm_lookups, verdict)
// ============================================================
#[cfg(test)]
mod tests_neo_r4 {
	use super::*;
	use super::tests_neo_m4::A18_DEFAULT_MIN;
	use super::tests_neo_m5::{a18_store, a18_carried};
	use super::tests_neo_m6::{run_core_aggr, regen_aggr_advice,
		a18_s_pat};
	use super::tests_neo_nonaggr::run_core_nonaggr;
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

	fn c2_hm() -> HashMap<u32, Vec<u32>> {
		let mut m = HashMap::new();
		m.insert(2, vec![111]); m.insert(5, vec![106]);
		m.insert(6, vec![96, 141]); m.insert(7, vec![101, 131]);
		m
	}

	/// A drain over an EMPTY buffer proves nothing, so every later
	/// negative in this file rests on these two facts: the
	/// reachable buffer is fed on both arms, and the carried buffer
	/// is fed on the non-aggressive one (aggr skips it by design,
	/// which is why its mtbl_qc stays empty).
	#[test]
	fn test_r4_buffers_are_fed() {
		let (_cs, nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, None);
		let hits = |v: &Vec<Fr>| v.iter()
			.filter(|x| !x.is_zero()).count();
		assert!(hits(&nat.mtbl_qr) > 0, "aggr QR drain is vacuous");
		assert!(nat.mtbl_qc.is_empty(),
			"aggr must have no carried target");
		let (_cs2, nat2) = run_core_nonaggr(&a18_store(),
			&a18_carried().to_stepqueue(), &c2_hm(),
			A18_DEFAULT_MIN, None);
		assert!(hits(&nat2.mtbl_qr) > 0, "nonaggr QR vacuous");
		assert!(hits(&nat2.mtbl_qc) > 0, "nonaggr QC vacuous");
		assert!(hits(&nat2.mtbl_tm) > 0, "membership vacuous");
	}

	/// the aggressive QR drain really is a constraint: multiplicity
	/// is checked advice, not a hint. (The QC twin is
	/// test_nonaggr_neg_mtbl_qc.)
	#[test]
	fn test_r4_mtbl_qr_forgery() {
		for case in 0..2 {
			let (cs, _nat) = run_core_aggr(&a18_store(),
				&fig14_hm(), 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					let j = nat.mtbl_qr.iter().position(|m|
						!m.is_zero()).unwrap();
					if case == 0 {
						nat.mtbl_qr[j] += f(1);
					} else {
						nat.mtbl_qr[j] -= f(1);
					}
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"mtbl_qr case {}", case);
		}
	}

	/// the verdict feed must carry exactly the terminal C rows:
	/// (a) rewriting a real acc entry leaves its terminal row's
	/// query with no target, (b) shifting the leading zero slot's
	/// count breaks the masked-row bookkeeping.
	/// HARNESS-LIMITED, deliberately not tested here: APPENDING an
	/// unqueried acc entry (multiplicity 0) is inert for a logup,
	/// so this seam cannot reject it. What rejects a fabricated
	/// failed-subsig is compute_sig consuming the committed acc
	/// container -- an integration-level check (P4), not a
	/// constraint of this gadget.
	#[test]
	fn test_r4_verdict_forgery() {
		let mut hm = fig14_hm();
		hm.insert(8, vec![108]);
		for case in 0..2 {
			let hm2 = hm.clone();
			let (cs, _nat) = run_core_aggr(&a18_store(), &hm2, 161,
				Some(&move |nat: &mut NeoCore<Fr>| {
					if case == 0 {
						let j = nat.acc_out.iter().position(|x|
							!x.is_zero()).expect("a terminal C");
						nat.acc_out[j] = f(999);
					} else {
						nat.mtbl_acc[0] += f(1);
					}
				}));
			assert!(!cs.is_satisfied().unwrap(),
				"verdict case {}", case);
		}
	}

	/// the seed anchor is the ground of reachability: drop the
	/// per-subsig anchor query by zeroing the statement subsig slot
	/// and everything else still balances, so the rest of the
	/// system would accept a vacuously all-FP table. It must not.
	#[test]
	fn test_r4_seed_anchor_drop() {
		let (cs, _nat) = run_core_aggr(&a18_store(), &fig14_hm(),
			161, Some(&|nat: &mut NeoCore<Fr>| {
				nat.subsig_nat[0] = f(0);
				regen_aggr_advice(nat, &a18_store(), &a18_s_pat());
			}));
		assert!(!cs.is_satisfied().unwrap());
	}
}

// NOTE_NEW8_ADAPTED (P3 R3): native-only oracle, revived as-is.
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

// NOTE_NEW8_ADAPTED (P3 R6: non-aggressive tier-2 end-to-end + verdict parity).
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
			res_small_cost: DischargeAdvCapacity::default_res_small(),
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
	// Union/seed fix applied: the whole step-0 group is outside
	// the union on both sides (Q_m masks step==0, q_i masks its
	// seed-enc rows), so the universe-vs-carried seed mismatch
	// this test used to trip no longer exists.
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
			res_small_cost: DischargeAdvCapacity::default_res_small(),
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
	// Union/seed fix applied: see test_nonaggr_h1_e2e's note.
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
// NOTE_NEW8_ADAPTED (P3 R6: cost band vs legacy / old-neo).
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
			res_small_cost: DischargeAdvCapacity::default_res_small(),
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

	/// The aggressive twin of the probe above, on the same hard
	/// scenario: seed-only carry (what the aggressive arm always
	/// has), all matches arriving in this chunk. Reported next to
	/// the non-aggressive figure so the two arms are comparable.
	#[test]
	fn neo_cost_probe_aggr() {
		let (nu, dens, s, w) = (8u32, 32u32, 40u32, 200u32);
		let cap_n = 320usize;
		let info = hard_store(nu, w);
		let mut hm = HashMap::new();
		for i in 1..=nu { hm.insert(i, step_locs(i, dens, s)); }
		let mut cap = hard_capacity(cap_n);
		cap.b_aggressive = false; // exact sizes, as in tier 1
		let seed = StepQueueItem::new(f(1), f(0), f(0), f(0), f(0),
			vec![f(1)]);
		let mut m = HashMap::new();
		m.insert(f(1), vec![seed]);
		let carried = StepQueueNeo::from_stepqueue(StepQueue::new(
			vec![f(1)], m, &cap, StepQueueType::ResLarge, false));
		let dmin = nu * s + dens + 100;
		let gen = carried.gen_shared_core_from_hm(0,
			&super::tests_neo_r1::hm_gen3(&hm), &info, f(dmin))
			.expect("shared core");
		let (l_pat, l_id, l_loc) =
			super::tests_neo_r1::l_cols3(&hm);
		let nat = NeoCore::gen(&gen, &info, l_pat, l_id, l_loc)
			.expect("core");
		let cs = super::tests_neo_m6::run_nat_aggr(&nat);
		assert!(cs.is_satisfied().unwrap(), "unsat: {:?}",
			cs.which_is_unsatisfied());
		println!("NEO-COST-AGGR: Q_m rows={} cs={}",
			nat.t.enc.len(), cs.num_constraints());
	}
}
