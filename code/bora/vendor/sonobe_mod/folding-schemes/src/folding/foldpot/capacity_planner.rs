//! Lightweight capacity probe = Pass-1 planning only (circuit selection +
//! per-word capacity check), copied out of `driver.rs` so it can run WITHOUT
//! the folding keys / crypto. PURE ADDITION: the `Driver` / `pass_all` /
//! `foldpot_main` framework is untouched (non-aggressive folding is
//! byte-identical). Used by `determine_config` to find the confirmed-lowest
//! config via estimate -> probe -> bump-on-CapErr.
//!
//! The 5 planning methods below are verbatim copies of `driver.rs`'s
//! `b_fast=false` path (gen_nd_advice_at_layer, find_working_layer_for_wd,
//! bin_search_best_layer, plan_nd_advice_new, plan_nd_advice), generic-reduced
//! to <C1, FC, LK, GM, H>. The spurious `<CS1E...>::ProverParams: Send+Sync`
//! where-bound on bin_search is dropped (its body never uses CS1E).

use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::fmt::Debug;
use core::marker::PhantomData;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_crypto_primitives::sponge::Absorb;

use crate::Error;
use crate::frontend::FCircuit;
use crate::folding::circuits::CF1;
use crate::folding::foldpot::utils::B_DEBUG;
use crate::folding::foldpot::circuits_super::field_to_usize;
use crate::folding::foldpot::sigma_ir1cs::{
    SigmaIR1CS, LookupTableTwoCol, GadgetMapper, Capacity, NdAdvice, WordInfo,
    CloneDeep};

extern crate utils as logger_crate;
use logger_crate::{logger::{log_perf, LOG2}, timer::Timer as GTimer,
    data::packed_to_nibbles, consts};

macro_rules! lock_unwrap {
    ($mutex:expr) => {
        $mutex.lock().unwrap_or_else(|e|
            panic!("Mutex poisoned at {}:{}: {}", file!(), line!(), e))
    };
}

/// Holds only what the Pass-1 planning needs: the circuit ladder. No keys,
/// no nova_param, no batch processor, no lkup/poseidon (planning uses none).
pub struct CapacityPlanner<C1, FC, LK, GM, const H: bool>
where
    C1: CurveGroup,
    C1::ScalarField: PrimeField + Absorb,
    FC: FCircuit<C1::ScalarField>
        + SigmaIR1CS<H, C1::ScalarField, LK, GM, C = C1>,
    LK: LookupTableTwoCol<C1::ScalarField>,
    GM: GadgetMapper<CF1<C1>, LK> + Clone + Debug,
{
    /// circuit ladder, ordered by preference (descending cost); 1 circ/layer.
    layered_circs: Vec<Vec<FC>>,
    /// flattened circuits (mirrors Driver.circuits)
    circuits: Vec<FC>,
    _p: PhantomData<fn() -> (C1, LK, GM)>,
}

impl<C1, FC, LK, GM, const H: bool> CapacityPlanner<C1, FC, LK, GM, H>
where
    C1: CurveGroup,
    C1::ScalarField: PrimeField + Absorb,
    FC: FCircuit<C1::ScalarField>
        + SigmaIR1CS<H, C1::ScalarField, LK, GM, C = C1>,
    LK: LookupTableTwoCol<C1::ScalarField>,
    GM: GadgetMapper<CF1<C1>, LK> + Clone + Debug,
{
    pub fn new(layered_circs: Vec<Vec<FC>>) -> Self {
        let circuits = layered_circs.concat();
        Self { layered_circs, circuits, _p: PhantomData }
    }

    // ==================================================================
    // M3: the probe entry point.
    // ==================================================================

    /// Run Pass-1 planning over the sample (per word: circuit selection +
    /// capacity check via gen_nd_advice). Ok(total_steps) if every word
    /// plans; else the FIRST word's CapErr list (param_name, required_value).
    /// No folding, no advice kept (b_save_advice=false). Early-abort on the
    /// first CapErr keeps failing probes cheap.
    pub fn capacity_probe(&self, words: &[Vec<CF1<C1>>],
        word_infos: &[WordInfo]) -> Result<usize, Vec<(String, usize)>> {
        let mut total_steps = 0usize;
        for (i, word) in words.iter().enumerate() {
            match self.plan_nd_advice(0, LOG2, false, word,
                    &word_infos[i], &format!("probe_w{}", i)) {
                Ok((steps, _sz, _pci, _cap, _adv)) => total_steps += steps,
                Err(Error::CapErr(v)) => return Err(v),
                Err(e) => return Err(vec![
                    (format!("non-cap error: {:?}", e), 0)]),
            }
        }
        Ok(total_steps)
    }

    /// Parallel capacity probe: process the words across up to `n_threads`
    /// workers, each with its OWN deep-cloned circuit ladder (so the gadget
    /// Mutexes don't contend). Ok(total_steps) if all words plan, else the
    /// first CapErr. `n_threads` bounds peak memory (each worker holds one
    /// ladder clone) -- keep it small for big circuits to avoid OOM.
    pub fn capacity_probe_par(&self, words: &[Vec<CF1<C1>>],
        word_infos: &[WordInfo], n_threads: usize)
        -> Result<usize, Vec<(String, usize)>>
    where FC: CloneDeep + Send + Sync, LK: Send + Sync, GM: Send + Sync {
        use rayon::prelude::*;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(n_threads.max(1)).build().expect("rayon pool");
        let results: Vec<Result<usize, Vec<(String, usize)>>> =
            pool.install(|| {
            (0..words.len()).into_par_iter().map_init(
                // one deep-cloned ladder per worker thread (not per word).
                || CapacityPlanner::<C1, FC, LK, GM, H>::new(
                    self.layered_circs.iter().map(|l|
                        l.iter().map(|c| c.clone_deep_self()).collect())
                        .collect()),
                |planner, i| {
                    let r = std::panic::catch_unwind(
                        std::panic::AssertUnwindSafe(|| {
                        match planner.plan_nd_advice(0, LOG2, false, &words[i],
                                &word_infos[i], "probe") {
                            Ok((steps, ..)) => Ok(steps),
                            Err(Error::CapErr(v)) => Err(v),
                            Err(e) => Err(vec![
                                (format!("non-cap: {:?}", e), 0)]),
                        }
                    }));
                    r.unwrap_or_else(|e| {
                        let msg = e.downcast_ref::<&str>().map(|s| s.to_string())
                            .or_else(|| e.downcast_ref::<String>().cloned())
                            .unwrap_or_else(|| "unknown".to_string());
                        Err(vec![(format!("panic in probe word {}: {}",
                            i, msg), 0)])
                    })
                }
            ).collect()
        });
        let mut total = 0usize;
        for r in results {
            match r { Ok(s) => total += s, Err(v) => return Err(v) }
        }
        Ok(total)
    }

    /// Collect-mode parallel probe: like capacity_probe_par but returns a
    /// PER-WORD result (None = planned ok, Some(errs) = that word's CapErr)
    /// so one sweep yields every failing word's demand instead of aborting
    /// on the first. Drives the seed-then-finalize cap loop.
    pub fn capacity_probe_collect(&self, words: &[Vec<CF1<C1>>],
        word_infos: &[WordInfo], n_threads: usize)
        -> Vec<Option<Vec<(String, usize)>>>
    where FC: CloneDeep + Send + Sync, LK: Send + Sync, GM: Send + Sync {
        use rayon::prelude::*;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(n_threads.max(1)).build().expect("rayon pool");
        pool.install(|| {
            (0..words.len()).into_par_iter().map_init(
                || CapacityPlanner::<C1, FC, LK, GM, H>::new(
                    self.layered_circs.iter().map(|l|
                        l.iter().map(|c| c.clone_deep_self()).collect())
                        .collect()),
                |planner, i| {
                    let r = std::panic::catch_unwind(
                        std::panic::AssertUnwindSafe(|| {
                        match planner.plan_nd_advice(0, LOG2, false, &words[i],
                                &word_infos[i], "probe") {
                            Ok(_) => None,
                            Err(Error::CapErr(v)) => Some(v),
                            Err(e) => Some(vec![
                                (format!("non-cap: {:?}", e), 0)]),
                        }
                    }));
                    r.unwrap_or_else(|e| {
                        let msg = e.downcast_ref::<&str>()
                            .map(|s| s.to_string())
                            .or_else(|| e.downcast_ref::<String>().cloned())
                            .unwrap_or_else(|| "unknown".to_string());
                        Some(vec![(format!("panic in probe word {}: {}",
                            i, msg), 0)])
                    })
                }
            ).collect()
        })
    }

    // ==================================================================
    // M2: copied planning methods (driver.rs b_fast=false path).
    // ==================================================================

    /// Public entry: plan steps for one word. Copy of driver.rs:675.
    pub fn plan_nd_advice(&self, job_id: usize, log_level: usize,
        b_save_advice: bool, word: &Vec<CF1<C1>>, word_info: &WordInfo,
        word_fname: &str)
        -> Result<(usize, Vec<usize>, Vec<usize>,
            Vec<Arc<dyn Capacity + Send + Sync>>,
            Vec<Arc<dyn NdAdvice + Send + Sync>>), Error> {
        self.plan_nd_advice_new(job_id, log_level, b_save_advice, word,
            word_info, word_fname)
    }

    /// Copy of driver.rs:826 with the b_fast=true (par_search) branch removed
    /// so it always uses the sequential find_working_layer + bin_search path.
    pub fn plan_nd_advice_new(&self, job_id: usize, log_level: usize,
        b_save_advice: bool, word: &Vec<CF1<C1>>, word_info: &WordInfo,
        word_fname: &str)
        -> Result<(usize, Vec<usize>, Vec<usize>,
            Vec<Arc<dyn Capacity + Send + Sync>>,
            Vec<Arc<dyn NdAdvice + Send + Sync>>), Error> {
        let mut gt1 = GTimer::new();
        let mut gt2 = GTimer::new();
        log_perf(job_id, log_level, &format!("plan_nd_advice step 0. \
            layers: {}, word.len(): {}, b_save_adivce: {}",
            self.layered_circs.len(), word.len(), b_save_advice), &mut gt1);
        let mwl = lock_unwrap!(self.layered_circs[0][0].get_mapper())
            .max_word_len();
        for i in 0..self.layered_circs.len() {
            assert!(self.layered_circs[i].len() == 1, "only 1 circ per layer!");
            assert!(lock_unwrap!(self.layered_circs[i][0].get_mapper())
                .max_word_len() == mwl);
        }
        // sequential path (b_fast=false): find max working layer, then
        // binary-search the minimum working layer.
        let (max_layer_id, num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)
            = self.find_working_layer_for_wd(job_id, log_level, b_save_advice,
                word, word_info)?;
        let min_layer = 0;
        let (_best_layer, num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) =
            self.bin_search_best_layer(job_id, log_level + 2, b_save_advice,
                word, word_info, min_layer, max_layer_id,
                num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)?;
        let pci = vec_pci[0];
        for x in &vec_pci { assert!(*x == pci); }
        log_perf(job_id, log_level, &format!("PERF 1001: plan_nd_advice for \
            {}, best_layer: {}, pci: {}, word.len in rounded bytes: {}.",
            word_fname, _best_layer, pci, word.len() * 63 / 2), &mut gt2);
        Ok((num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv))
    }

    /// Copy of driver.rs:615. Heuristic guess of a working layer, verified on
    /// the full word; returns Err(CapErr) if even the max layer cannot fit.
    fn find_working_layer_for_wd(&self, job_id: usize, log_level: usize,
        b_save_advice: bool, word: &Vec<CF1<C1>>, word_info: &WordInfo)
        -> Result<(usize, usize, Vec<usize>, Vec<usize>,
            Vec<Arc<dyn Capacity + Send + Sync>>,
            Vec<Arc<dyn NdAdvice + Send + Sync>>), Error> {
        let full_len = word.len();
        let max_wlen = lock_unwrap!(self.layered_circs[0][0].get_mapper())
            .max_word_len();
        let long_bar = 1024 * 1024 / 31 * 4; //4MB of data
        let max_layer_id = self.layered_circs.len() - 1;

        //1. compute guessed_layer
        let guessed_layer = if full_len < 4 * max_wlen || full_len > long_bar {
            max_layer_id
        } else {
            let seg = word[full_len / 2..full_len / 2 + max_wlen].to_vec();
            let min_layer = 0;
            let res = self.gen_nd_advice_at_layer(job_id, max_layer_id,
                log_level, b_save_advice, &seg, word_info)?;
            let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) = res;
            let (best_layer, _num_segs, _vec_seg_size, _vec_pci, _vec_cap,
                _vec_adv) = self.bin_search_best_layer(job_id, log_level,
                    b_save_advice, &seg, word_info, min_layer, max_layer_id,
                    num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)?;
            best_layer
        };

        //2. check if guessed layer works for the full word
        let res = self.gen_nd_advice_at_layer(job_id, guessed_layer,
            log_level, b_save_advice, &word, word_info);
        if res.is_ok() {
            let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)
                = res.unwrap();
            Ok((guessed_layer, num_segs, vec_seg_size, vec_pci, vec_cap,
                vec_adv))
        } else {
            let res2 = self.gen_nd_advice_at_layer(job_id, max_layer_id,
                log_level, b_save_advice, &word, word_info)?;
            let (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv) = res2;
            Ok((max_layer_id, num_segs, vec_seg_size, vec_pci, vec_cap,
                vec_adv))
        }
    }

    /// Copy of driver.rs:702 WITHOUT the spurious `<CS1E...>: Send+Sync`
    /// where-bound (the body only calls gen_nd_advice_at_layer).
    fn bin_search_best_layer(&self, job_id: usize, log_level: usize,
        b_save_advice: bool, word: &Vec<CF1<C1>>, word_info: &WordInfo,
        min_layer: usize, max_layer: usize, max_layer_num_segs: usize,
        max_layer_vec_seg_size: Vec<usize>, max_layer_vec_pci: Vec<usize>,
        max_layer_vec_cap: Vec<Arc<dyn Capacity + Send + Sync>>,
        max_layer_vec_adv: Vec<Arc<dyn NdAdvice + Send + Sync>>)
        -> Result<(usize, usize, Vec<usize>, Vec<usize>,
            Vec<Arc<dyn Capacity + Send + Sync>>,
            Vec<Arc<dyn NdAdvice + Send + Sync>>), Error> {
        let mut gt1 = GTimer::new();
        let mut min_layer_id = min_layer;
        let (mut best_layer, mut max_layer_id) = (max_layer, max_layer);
        let (mut num_segs, mut vec_seg_size, mut vec_pci, mut vec_cap,
            mut vec_adv) = (max_layer_num_segs, max_layer_vec_seg_size,
            max_layer_vec_pci, max_layer_vec_cap, max_layer_vec_adv);
        while min_layer_id <= max_layer_id && max_layer_id > 0 {
            let mid_id = (min_layer_id + max_layer_id) / 2;
            let res = self.gen_nd_advice_at_layer(job_id, mid_id, log_level,
                b_save_advice, word, word_info);
            if res.is_ok() {
                (num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv)
                    = res.unwrap();
                best_layer = mid_id;
                if mid_id == 0 { break; } else { max_layer_id = mid_id - 1; }
            } else {
                min_layer_id = mid_id + 1;
            }
            log_perf(job_id, log_level, &format!("bin_search: min_id: {}, \
                max_id: {}, mid_id: {}.  word.len(): {}.", min_layer_id,
                max_layer_id, mid_id, word.len()), &mut gt1);
        }
        Ok((best_layer, num_segs, vec_seg_size, vec_pci, vec_cap, vec_adv))
    }

    /// Copy of driver.rs:531. Generate advice for the word at `layer_i`,
    /// segment by segment, carrying prev_adv across a word's segments (so the
    /// per-chunk capacity demand that climbs per chunk is exercised). CapErr
    /// from gen_nd_advice propagates via `?`.
    fn gen_nd_advice_at_layer(&self, job_id: usize, layer_i: usize,
        _log_level: usize, b_save_advice: bool, word: &Vec<CF1<C1>>,
        word_info: &WordInfo)
        -> Result<(usize, Vec<usize>, Vec<usize>,
            Vec<Arc<dyn Capacity + Send + Sync>>,
            Vec<Arc<dyn NdAdvice + Send + Sync>>), Error> {
        let mut vec_pci = vec![];
        let mut vec_size = vec![];
        let mut vec_cap = vec![];
        let mut vec_adv: Vec<Arc<dyn NdAdvice + Send + Sync>> = vec![];
        let layer = &self.layered_circs[layer_i];
        let circ = &layer[0];
        let max_wlen = lock_unwrap!(circ.get_mapper()).max_word_len();
        let wlen = word.len();
        let num_segs = if wlen % max_wlen == 0 { wlen / max_wlen }
            else { wlen / max_wlen + 1 };
        let pci = layer_i; //because every layer has only one circ
        let cap = lock_unwrap!(circ.get_mapper()).get_capacity();
        let mut prev_adv = None;
        for i in 0..num_segs {
            if std::env::var("ZKR_PROBE_64008").is_ok() {
                consts::PROBE_CHUNK_ID.store(i, Ordering::Relaxed);
            }
            let start = i * max_wlen;
            let end = if (i + 1) * max_wlen > wlen { wlen }
                else { (i + 1) * max_wlen };
            let seg = word[start..end].to_vec();
            // aggressive forward halo: per-seg look-ahead = successor's first
            // M nibbles as raw u8 (empty for last seg / non-aggr => SED pads).
            let m_halo = cap.halo_nibbles();
            let wi_owned;
            let wi_ref = if m_halo > 0 && end < wlen {
                let n_end = if end + max_wlen > wlen { wlen }
                    else { end + max_wlen };
                let nxt = packed_to_nibbles(&word[end..n_end].to_vec());
                let take = m_halo.min(nxt.len());
                let mut wi = word_info.clone();
                wi.halo_nibbles = nxt[0..take].iter()
                    .map(|f| field_to_usize(f) as u8).collect();
                wi_owned = wi;
                &wi_owned
            } else { word_info };
            let advice = lock_unwrap!(circ.get_mapper())
                .gen_nd_advice(&seg, wi_ref, prev_adv, i, job_id)?;
            vec_pci.push(pci);
            vec_size.push(end - start);
            vec_cap.push(cap.clone());
            prev_adv = Some(advice.clone());
            if b_save_advice { vec_adv.push(advice); }
        }
        Ok((num_segs, vec_size, vec_pci, vec_cap, vec_adv))
    }
}
