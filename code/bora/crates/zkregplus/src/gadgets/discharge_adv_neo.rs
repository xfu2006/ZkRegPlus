// discharge_adv_neo.rs
// Created 2026-07-19.
// Design by the BORA paper author. Code implemented by Claude Opus.
// Code reviewed by the paper author and unit tested.
//
// M3 coexistence stub for the Appendix G.1 constant-queue SDE. This
// stub delegates every SigmaGadget method to DischargeAdvGadget, so the
// neo path is byte-identical to the legacy SDE. The real G.1
// certificates (C/FP/BP/SP over StepQueueNeo) replace the body in M4-M7.

use ark_ff::{PrimeField, Zero};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{SynthesisError, ConstraintSystemRef};
use data_processor::type_def::SubsigStepStore;
use std::collections::HashMap;
use folding_schemes::Error;
use folding_schemes::folding::foldpot::{
	sigma_ir1cs::{SigmaGadget, WitnessSigmaIR1CSVar,
		WitnessSigmaIR1CSConfig},
	container_config::{ColEle, ContainerConfig},
};
use crate::gadgets::discharge_adv::{DischargeAdvGadget,
	DischargeAdvCapacity, StepQueue, StepQueueItem, StepQueueType};

/// M3 stub wrapping the legacy SDE gadget; forwards all trait methods.
#[derive(Clone, Debug)]
pub struct DischargeAdvNeoGadget<F: PrimeField + ColEle> {
	/// delegate target; replaced by native G.1 state in M4+.
	pub inner: DischargeAdvGadget<F>,
}

impl<F: PrimeField + ColEle> DischargeAdvNeoGadget<F> {
	/// mirrors DischargeAdvGadget::new so the sed_mapper swap is 1:1.
	pub fn new(
		b_igc: bool,
		offset_fsm: usize,
		capacity: &DischargeAdvCapacity,
		fsm_id: u32,
		prev_cfgs: &Vec<ContainerConfig>,
		store_steps: &SubsigStepStore,
	) -> Self {
		let inner = DischargeAdvGadget::<F>::new(
			b_igc, offset_fsm, capacity, fsm_id, prev_cfgs,
			store_steps);
		Self { inner }
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
		word_id: FpVar<F>, subsig_id: FpVar<F>)
		-> Result<(), SynthesisError> {
		self.inner.assert_msg3(i, cs, wtns, cfg, word_id,
			subsig_id)
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

	/// (B) length of the full advice vec = N_NEO_COLS * n.
	pub fn full_vec_size(q_type: &StepQueueType,
		capacity: &DischargeAdvCapacity) -> usize {
		let (n, _, _) = Self::carry_vec_size(q_type, capacity);
		N_NEO_COLS * n
	}

	/// (B) serialize base + attrs as N_NEO_COLS columns of length n,
	/// concatenated. Per-item scalars replicated per row; tail padded with
	/// dummy (encoded 0) rows. CapErr if rows exceed n.
	pub fn to_full_vec(&self, q_type: &StepQueueType,
		capacity: &DischargeAdvCapacity) -> Result<Vec<F>, Error> {
		let (n, _, _) = Self::carry_vec_size(q_type, capacity);
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
	pub fn parse_full(vec: &Vec<F>, q_type: StepQueueType,
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
			capacity: capacity.clone(), q_type }
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

#[cfg(test)]
pub(crate) mod tests_neo_m4 {
	use super::*;
	use ark_bn254::Fr;
	use utils::consts::read_global_config;

	fn f(x: u32) -> Fr { Fr::from(x) }

	fn fixture_capacity() -> DischargeAdvCapacity {
		// non-aggressive: n = subsigs*avg = 16 (>= 13 real rows).
		DischargeAdvCapacity {
			max_nibble_len: 1, subsigs: 1,
			avg_active_pats_per_subsig: 16, basis_pats_in_trace: 1,
			perc_pats_expansion_rate: 100, universe_subsigs: 1,
			b_aggressive: false, prod_pats_expansion: 0,
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
		let mut items = vec![
			mk(1, 1, 1, f(9), 0, &[(6, CAT_C)]),
			mk(2, 2, 0, inf,  5, &[(21, CAT_C), (111, CAT_C)]),
			mk(3, 3, 1, f(9), 5, &[(27, CAT_C)]),
			mk(4, 4, 1, f(9), 5, &[(33, CAT_C)]),
			mk(5, 5, 1, f(9), 0, &[(39, CAT_C), (106, CAT_FP)]),
			mk(6, 6, 1, inf,  8, &[(73, CAT_BP), (79, CAT_BP),
				(96, CAT_BP), (141, CAT_BP)]),
			mk(7, 7, 1, f(9), 8, &[(101, CAT_BP), (131, CAT_FP)]),
		];
		// C-chain certs (prev_id1 = id into prev step's rows, all 0
		// here): 21<-6, 111<-6, 27<-21, 33<-27, 39<-33.
		items[1].prev_loc1 = vec![f(6), f(6)];
		items[2].prev_loc1[0] = f(21);
		items[3].prev_loc1[0] = f(27);
		items[4].prev_loc1[0] = f(33);
		// FP 5:106 below-only bracket (33+9=42<106; no upper row:
		// loc2=0 sentinel, b_below bit lands with the cert layer).
		items[4].prev_loc1[1] = f(33);
		// FP 7:131 between 96 (id 2) and 141 (id 3): 105<131<142.
		items[6].prev_id1[1] = f(2);
		items[6].prev_loc1[1] = f(96);
		items[6].prev_loc2[1] = f(141);
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
		let v = neo.to_full_vec(&neo.q_type, &neo.capacity).unwrap();
		let (n, _, _) =
			StepQueueNeo::<Fr>::carry_vec_size(&neo.q_type, &neo.capacity);
		assert_eq!(v.len(),
			StepQueueNeo::<Fr>::full_vec_size(&neo.q_type, &neo.capacity));
		assert_eq!(v.len(), N_NEO_COLS * n);
		let neo2 = StepQueueNeo::parse_full(&v, neo.q_type.clone(),
			&neo.capacity, neo.b_igc);
		assert_eq!(neo2, neo);
	}

	#[test]
	fn test_neo_min_len_relations() {
		let neo = build_a1_a8_neo();
		let (minr, lenr) = (neo.derive_min(), neo.derive_len());
		let sub = f(1);
		for (s, m) in [(1,6),(2,21),(3,27),(4,33),(5,39)] {
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
