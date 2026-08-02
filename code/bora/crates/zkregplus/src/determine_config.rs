//! determine_config: auto capacity tuner. Finds the confirmed-lowest config
//! that discharges a sample set against a DB, by: (1) warm-start from the
//! estimator, (2) build circuits, (3) run Pass-1 capacity probe over the
//! sample, (4) on any CapErr bump the exact param to its required value and
//! retry. Works for both aggressive and non-aggressive. Uses the lightweight
//! CapacityPlanner (no keys/folding) so the foldpot framework is untouched.
//! The driving loop lives in zkp_driver.rs (where the concrete circuit types
//! and build_circs live); this file holds the mode-agnostic scalar logic.

use crate::circs::cp_mapper::CpCapacity;
use crate::circs::sed_mapper::SedCapacity;
use crate::circs::dfa_mapper::DfaCapacity;
use serde::{Serialize, Deserialize};

/// Scalar cap parameters tuned by the loop. Seeded from the estimator output,
/// bumped per CapErr, and turned into CpCapacity/SedCapacity(/DfaCapacity)
/// each iteration (we rebuild rather than poke struct fields, since
/// SedCapacity::new builds internal comp_capacities from these values).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CapParams {
    // CP (critical-pattern) gadget
    pub cp_basis_unique_states: usize,
    pub cp_subsigs: usize,
    pub cp_avg_pats: usize,
    // SED gadget (cs = case-sensitive arm)
    pub subsigs: usize,
    pub avg_pats_per_subsig: usize,
    pub avg_active_pats_per_subsig: usize,
    pub basis_pats_in_trace: usize,
    pub perc_pats_expansion_rate: usize,
    // aggressive: forward-queue cap INFERRED from container_rows (decoupled
    // from basis_pats*perc); sizes the SED step queues in the gadget. perc
    // above is kept cosmetic in aggressive. serde-default for old configs;
    // non-aggressive leaves it 0 (gadget reads basis_pats*perc instead).
    #[serde(default)]
    pub prod_pats_expansion: usize,
    pub sigs_sed: usize,
    pub perc_comp_subsigs: usize,
    pub basis_unique_states: usize,
    pub basis_acc_states: usize,
    // SED igc arm: per-case CapErrs carry "b_igc: true". Tuned in both modes
    // -- non-aggressive sizes the real igc arm; aggressive sizes the tiny
    // 1-subsig sentinel independently from cs (so igc stays cheap).
    pub subsigs_igc: usize,
    pub avg_active_pats_per_subsig_igc: usize,
    pub basis_pats_in_trace_igc: usize,
    pub perc_pats_expansion_rate_igc: usize,
    #[serde(default)]
    pub prod_pats_expansion_igc: usize,
    pub basis_acc_states_igc: usize,
    // aggressive igc sentinel: its own SMALL basis_unique_states (the cs
    // field above is shared cs/igc in non-aggressive). serde-default so
    // configs written before this field deserialize (clamped on use).
    #[serde(default)]
    pub basis_unique_states_igc: usize,
    // DFA gadget (non-aggressive only; 0 in aggressive)
    pub dfa_sigs: usize,
    pub dfa_subsigs: usize,
    // GlobalConfig knob + structural
    pub aggr_needs_subsigs: usize,
    pub max_word_len: usize,
    pub acdfa_state_part_bits: usize,
}

impl CapParams {
    /// Write this config as pretty JSON. The determine_config -> full_dlp
    /// handoff: the Python driver never parses stdout or edits source, it
    /// just sequences runs and lets these files carry the config.
    pub fn save_json(&self, path: &str) -> std::io::Result<()> {
        let s = serde_json::to_string_pretty(self)
            .expect("CapParams serialize");
        std::fs::write(path, s)
    }

    /// Read a config written by save_json. Panics with the path on error so
    /// a missing/garbled handoff fails loudly in the driver.
    pub fn load_json(path: &str) -> CapParams {
        let s = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read config {}: {}", path, e));
        serde_json::from_str(&s)
            .unwrap_or_else(|e| panic!("parse config {}: {}", path, e))
    }
}

/// The per-step run-config the Python driver writes and points at via the
/// ZKR_DLP_RUNCFG env var. Paths are repo-root-relative (resolved like
/// run_db_bundle resolves config_dir). The full_dlp_sample* / full_dlp tests
/// read this instead of hardcoding paths, so fixture<->real is data-only.
#[derive(Clone, Debug, Deserialize)]
pub struct RunCfg {
    pub config_dir: String,
    pub sig_file: String,
    pub cache_dir: String,
    pub fanout_cap: usize,
    pub chunk_len: usize,
    pub range2_bit: usize,
    #[serde(default)] pub scan_file: String,
    #[serde(default)] pub config_out: String,
    #[serde(default)] pub config_c1: String,
    #[serde(default)] pub config_c2: String,
    #[serde(default)] pub report_out: String,
    // M11: aggressive per-chunk ladder. config_ladder = Vec<CapParams> handoff;
    // k_max = rung cap (DP picks <= k_max); n_buckets = log-bucket coarsening.
    #[serde(default)] pub config_ladder: String,
    #[serde(default = "k_max_default")] pub k_max: usize,
    #[serde(default = "n_buckets_default")] pub n_buckets: usize,
    // When k_max>=3, peel rung 0 into a smaller rung 0' sized at this
    // percentile of rung 0's FSM/CP per-chunk demand (FSM-tail bumps to rung0).
    #[serde(default = "peel_pct_default")] pub peel_pct: usize,
    // full_dlp(): deterministic size-balanced split source (config_dir-
    // relative, .tgz ok) and job count; reset forces cache recompute.
    #[serde(default)] pub full_list: String,
    #[serde(default = "num_jobs_default")] pub num_jobs: usize,
    #[serde(default)] pub reset: bool,
}

fn k_max_default() -> usize { 4 }
fn n_buckets_default() -> usize { 2048 }
fn peel_pct_default() -> usize { 90 }
fn num_jobs_default() -> usize { 8 }

impl RunCfg {
    /// Load the run-config the driver pointed ZKR_DLP_RUNCFG at.
    pub fn from_env() -> RunCfg {
        let path = std::env::var("ZKR_DLP_RUNCFG")
            .expect("ZKR_DLP_RUNCFG not set (run via scripts/run_full_dlp.py)");
        Self::from_path(&path)
    }

    /// Load a run-config from a fixed JSON path on disk (no env needed).
    pub fn from_path(path: &str) -> RunCfg {
        let s = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read runcfg {}: {}", path, e));
        serde_json::from_str(&s)
            .unwrap_or_else(|e| panic!("parse runcfg {}: {}", path, e))
    }
}

/// Parse a CapErr out of a panic message. Some gadgets `.expect()` a CapErr
/// during build_circs' container sizing (e.g. discharge_adv.rs:3645) instead of
/// returning it, so the build PANICS when a cap is below a structural floor.
/// determine_config catches that panic and feeds the parsed (param, required)
/// back through apply_caperr_bumps, auto-discovering the floor.
/// Expects the Debug form: ... CapErr([("<name>", <num>), ...]) ...
pub fn parse_caperr_from_panic(msg: &str) -> Option<Vec<(String, usize)>> {
    // Accept both compact "CapErr([..." and pretty {:#?} "CapErr(\n    [...".
    let i = msg.find("CapErr(")?;
    let after = &msg[i + "CapErr(".len()..];
    let lb = after.find('[')?;
    let mut rest = &after[lb + 1..];
    let mut res = vec![];
    loop {
        let Some(q1) = rest.find('"') else { break };
        let after = &rest[q1 + 1..];
        let Some(q2) = after.find('"') else { break };
        let name = after[..q2].to_string();
        let tail = &after[q2 + 1..];
        let digits: String = tail.chars()
            .skip_while(|c| !c.is_ascii_digit())
            .take_while(|c| c.is_ascii_digit()).collect();
        let Ok(num) = digits.parse::<usize>() else { break };
        res.push((name, num));
        match tail.find(')') { Some(c) => rest = &tail[c + 1..], None => break }
    }
    if res.is_empty() { None } else { Some(res) }
}

/// Run one build+probe closure, converting a build-time CapErr-panic into a
/// normal CapErr. Returns Ok(Ok(steps)) on pass, Ok(Err(caperr)) on a (caught
/// or returned) CapErr to bump, or Err(msg) on a non-CapErr panic (fatal).
pub fn probe_catching<T, Fp>(f: Fp)
    -> Result<Result<T, Vec<(String, usize)>>, String>
where Fp: FnOnce() -> Result<T, Vec<(String, usize)>> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => Ok(r),
        Err(panic) => {
            let msg = panic.downcast_ref::<&str>().map(|s| s.to_string())
                .or_else(|| panic.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "unknown panic".to_string());
            match parse_caperr_from_panic(&msg) {
                Some(errs) => Ok(Err(errs)),
                None => Err(format!("non-CapErr panic in build/probe: {}", msg)),
            }
        }
    }
}

/// Apply CapErr bumps to `p`. For each (param_name, required), set the mapped
/// field to max(current, required). Returns (any_changed, unmapped_names).
/// `required` is the gadget's back-solved minimum, so post-loop each binding
/// field sits at its exact minimum => the confirmed-lowest config.
pub fn apply_caperr_bumps(p: &mut CapParams, b_aggr: bool,
    errs: &[(String, usize)]) -> (bool, Vec<String>) {
    let mut changed = false;
    let mut unmapped = vec![];
    let mut up = |cur: &mut usize, req: usize, ch: &mut bool| {
        if req > *cur { *cur = req; *ch = true; }
    };
    for (name, req) in errs {
        let r = *req;
        // igc arm markers: "b_igc: true" on per-case fields, "subsigs_igc"
        // on comp_sig. ("b_igc: false" is the cs arm; note "b_igc" itself
        // contains "_igc" so we must NOT match on a bare "_igc".)
        let igc = name.contains("b_igc: true") || name.contains("subsigs_igc");
        if name.starts_with("dis_adv::prod_pats_expansion") {
            // aggressive forward-queue cap (rung-independent).
            if igc { up(&mut p.prod_pats_expansion_igc, r, &mut changed); }
            else { up(&mut p.prod_pats_expansion, r, &mut changed); }
        } else if name.starts_with("dis_adv::perc_pats_expansion_rate") {
            if igc { up(&mut p.perc_pats_expansion_rate_igc, r, &mut changed); }
            else { up(&mut p.perc_pats_expansion_rate, r, &mut changed); }
        } else if name.starts_with("dis_adv::avg_active_pats_per_subsig") {
            if igc { up(&mut p.avg_active_pats_per_subsig_igc, r, &mut changed); }
            else { up(&mut p.avg_active_pats_per_subsig, r, &mut changed); }
        } else if name.starts_with("comp_sig::perc_comp_subsigs") {
            up(&mut p.perc_comp_subsigs, r, &mut changed); // shared cs/igc
        } else if name.starts_with("comp_sig::sigs") {
            up(&mut p.sigs_sed, r, &mut changed);
        } else if name.starts_with("fsm_adv::basis_acc_states") {
            if igc { up(&mut p.basis_acc_states_igc, r, &mut changed); }
            else { up(&mut p.basis_acc_states, r, &mut changed); }
        } else if name.starts_with("fsm_adv::basis_pats_in_trace") {
            if igc { up(&mut p.basis_pats_in_trace_igc, r, &mut changed); }
            else { up(&mut p.basis_pats_in_trace, r, &mut changed); }
        } else if name.starts_with("dfa_adv::sigs") {
            up(&mut p.dfa_sigs, r, &mut changed);
        } else if name.starts_with("dfa_adv::subsigs") {
            up(&mut p.dfa_subsigs, r, &mut changed);
        } else if name.starts_with("cp::") {
            // CP pack gadget caps (pack.rs) -> the CP-capacity fields. Must
            // precede the generic subsigs/basis branches so cp::subsigs is not
            // mis-routed to the SED subsigs.
            if name.starts_with("cp::subsigs") {
                up(&mut p.cp_subsigs, r, &mut changed);
            } else if name.starts_with("cp::avg_pats") {
                up(&mut p.cp_avg_pats, r, &mut changed);
            } else if name.starts_with("cp::basis_unique_states") {
                up(&mut p.cp_basis_unique_states, r, &mut changed);
            } else {
                unmapped.push(name.clone());
            }
        } else if name.contains("subsigs") {
            // dis_adv::subsigs / comp_sig::subsigs{,_cs,_igc,_N} / fsm_adv::subsigs
            // Also dis_adv::neo_wrap_subsigs: the neo T_qm wrap budget is
            // subsigs*(max_chain+1) and max_chain is DB-exact, so a wrap
            // overflow is always a subsigs shortfall (gadget back-solves
            // the required count, so it lands in these same units).
            if igc { up(&mut p.subsigs_igc, r, &mut changed); }
            else {
                // +1 reserves the comp_sig dummy entry (inp_subsigs[0] must be
                // 0; compute_sig_adv.rs:1103). The universe CapErr reports the
                // raw subsig count, one short of the buffer comp_sig needs.
                up(&mut p.subsigs, r + 1, &mut changed);
                if b_aggr { up(&mut p.aggr_needs_subsigs, r, &mut changed); }
            }
        } else if name.contains("basis_unique_states") {
            // aggressive: igc has its own small sentinel field; cs and the
            // non-aggressive shared arm keep the original field.
            if igc && b_aggr {
                up(&mut p.basis_unique_states_igc, r, &mut changed);
            } else {
                up(&mut p.basis_unique_states, r, &mut changed); // SED/fsm pack
            }
        } else {
            // max_word_len, lkup/pack sizing, etc.
            unmapped.push(name.clone());
        }
    }
    (changed, unmapped)
}

/// Build the aggressive CP+SED capacities from the scalar params (rebuild,
/// not field-poke, since SedCapacity::new derives internal comp_capacities).
/// Returns (cp_cs, sed_cs, cp_igc, sed_igc). The igc CP runs the real igc
/// crit-pattern DFA, so it shares the tunable cp_basis_unique_states; the SED
/// igc is a subsigs=1 sentinel tuned via the _igc params (clamped to floors so
/// any seed -- including 0/serde-default -- yields a valid capacity).
pub fn caps_from_params_aggr(p: &CapParams)
    -> (CpCapacity, SedCapacity, CpCapacity, SedCapacity) {
    let cp = CpCapacity {
        max_word_len: p.max_word_len,
        basis_unique_states: p.cp_basis_unique_states,
        subsigs: p.cp_subsigs,
        avg_pats_per_subsig: p.cp_avg_pats,
    };
    let cp_igc = CpCapacity {
        max_word_len: p.max_word_len,
        basis_unique_states: p.cp_basis_unique_states, // shared with cs CP
        subsigs: 1,                                    // sentinel
        avg_pats_per_subsig: 1,
    };
    let mut sed = SedCapacity::new(
        p.max_word_len, p.acdfa_state_part_bits, p.subsigs,
        p.avg_pats_per_subsig, p.avg_active_pats_per_subsig,
        p.basis_pats_in_trace, p.perc_pats_expansion_rate, p.sigs_sed,
        p.perc_comp_subsigs, p.basis_unique_states, p.basis_acc_states);
    // aggressive: override the forward-queue cap with the inferred prod
    // (no-op when 0 -> keeps the basis_pats*perc default).
    sed.set_prod_pats_expansion(p.prod_pats_expansion);
    let mut sed_igc = SedCapacity::new(
        p.max_word_len, p.acdfa_state_part_bits, 1, 1,
        p.avg_active_pats_per_subsig_igc.max(1),
        p.basis_pats_in_trace_igc.max(8),
        p.perc_pats_expansion_rate_igc.max(64), 1, 1,
        p.basis_unique_states_igc.max(4),
        p.basis_acc_states_igc.max(2));
    sed_igc.set_prod_pats_expansion(p.prod_pats_expansion_igc);
    (cp, sed, cp_igc, sed_igc)
}

/// Build the non-aggressive cs/igc/dfa capacities from scalar params, in the
/// order build_circs_adv wants them. cp_igc reuses the cs CP caps.
pub fn caps_from_params_general(p: &CapParams)
    -> (CpCapacity, SedCapacity, DfaCapacity, CpCapacity, SedCapacity) {
    let cp = |bu, ss, ap| CpCapacity { max_word_len: p.max_word_len,
        basis_unique_states: bu, subsigs: ss, avg_pats_per_subsig: ap };
    let cp_cs = cp(p.cp_basis_unique_states, p.cp_subsigs, p.cp_avg_pats);
    let cp_igc = cp(p.cp_basis_unique_states, p.cp_subsigs, p.cp_avg_pats);
    let sed_cs = SedCapacity::new(p.max_word_len, p.acdfa_state_part_bits,
        p.subsigs, p.avg_pats_per_subsig, p.avg_active_pats_per_subsig,
        p.basis_pats_in_trace, p.perc_pats_expansion_rate, p.sigs_sed,
        p.perc_comp_subsigs, p.basis_unique_states, p.basis_acc_states);
    let sed_igc = SedCapacity::new(p.max_word_len, p.acdfa_state_part_bits,
        p.subsigs_igc, p.avg_pats_per_subsig, p.avg_active_pats_per_subsig_igc,
        p.basis_pats_in_trace_igc, p.perc_pats_expansion_rate_igc, p.sigs_sed,
        p.perc_comp_subsigs, p.basis_unique_states, p.basis_acc_states_igc);
    let dfa = DfaCapacity::new(p.max_word_len, p.dfa_sigs, p.dfa_subsigs);
    (cp_cs, sed_cs, dfa, cp_igc, sed_igc)
}

/// Read the non-aggressive hand caps back into CapParams (cs + igc + dfa).
pub fn capparams_from_caps_general(cp_cs: &CpCapacity, sed_cs: &SedCapacity,
    dfa: &DfaCapacity, sed_igc: &SedCapacity) -> CapParams {
    CapParams {
        cp_basis_unique_states: cp_cs.basis_unique_states,
        cp_subsigs: cp_cs.subsigs,
        cp_avg_pats: cp_cs.avg_pats_per_subsig,
        subsigs: sed_cs.subsigs,
        avg_pats_per_subsig: sed_cs.avg_pats_per_subsig,
        avg_active_pats_per_subsig: sed_cs.avg_active_pats_per_subsig,
        basis_pats_in_trace: sed_cs.basis_pats_in_trace,
        perc_pats_expansion_rate: sed_cs.perc_pats_expansion_rate,
        prod_pats_expansion: 0,        // re-inferred by determine_config_aggr
        sigs_sed: sed_cs.sigs_sed,
        perc_comp_subsigs: sed_cs.perc_comp_subsigs,
        basis_unique_states: sed_cs.basis_unique_states,
        basis_acc_states: sed_cs.basis_acc_states,
        subsigs_igc: sed_igc.subsigs,
        avg_active_pats_per_subsig_igc: sed_igc.avg_active_pats_per_subsig,
        basis_pats_in_trace_igc: sed_igc.basis_pats_in_trace,
        perc_pats_expansion_rate_igc: sed_igc.perc_pats_expansion_rate,
        prod_pats_expansion_igc: 0,
        basis_acc_states_igc: sed_igc.basis_acc_states,
        basis_unique_states_igc: sed_igc.basis_unique_states,
        dfa_sigs: dfa.sigs,
        dfa_subsigs: dfa.subsigs,
        aggr_needs_subsigs: 0,
        max_word_len: sed_cs.max_word_len,
        acdfa_state_part_bits: sed_cs.acdfa_state_part_bits,
    }
}

/// Read a (CpCapacity, SedCapacity) pair back into scalar CapParams (the
/// runner's hand config -> the comparison baseline / warm-start). dfa_* stay 0
/// (aggressive has no DFA gadget).
pub fn capparams_from_caps_aggr(cp: &CpCapacity, sed: &SedCapacity,
    aggr_needs_subsigs: usize) -> CapParams {
    CapParams {
        cp_basis_unique_states: cp.basis_unique_states,
        cp_subsigs: cp.subsigs,
        cp_avg_pats: cp.avg_pats_per_subsig,
        subsigs: sed.subsigs,
        avg_pats_per_subsig: sed.avg_pats_per_subsig,
        avg_active_pats_per_subsig: sed.avg_active_pats_per_subsig,
        basis_pats_in_trace: sed.basis_pats_in_trace,
        perc_pats_expansion_rate: sed.perc_pats_expansion_rate,
        prod_pats_expansion: 0,        // re-inferred by determine_config_aggr
        sigs_sed: sed.sigs_sed,
        perc_comp_subsigs: sed.perc_comp_subsigs,
        basis_unique_states: sed.basis_unique_states,
        basis_acc_states: sed.basis_acc_states,
        // igc sentinel seeds: 0 here, clamped to floors in
        // caps_from_params_aggr and bumped per igc CapErr by the tuner.
        subsigs_igc: 0,
        avg_active_pats_per_subsig_igc: 0,
        basis_pats_in_trace_igc: 0,
        perc_pats_expansion_rate_igc: 0,
        prod_pats_expansion_igc: 0,
        basis_acc_states_igc: 0,
        basis_unique_states_igc: 0,
        dfa_sigs: 0,
        dfa_subsigs: 0,
        aggr_needs_subsigs,
        max_word_len: sed.max_word_len,
        acdfa_state_part_bits: sed.acdfa_state_part_bits,
    }
}

/// Pass iff every field is <= cur (better) or within +10% (not too worse).
/// `new` = determine_config output, `cur` = the runner's current hand config.
pub fn compare_caps(new: &CapParams, cur: &CapParams) -> Result<(), Vec<String>> {
    let mut bad = vec![];
    let mut chk = |name: &str, n: usize, c: usize| {
        if n > c && n * 10 > c * 11 {
            bad.push(format!("{}: new {} > +10% of cur {}", name, n, c));
        }
    };
    chk("perc_pats_expansion_rate", new.perc_pats_expansion_rate,
        cur.perc_pats_expansion_rate);
    chk("avg_active_pats_per_subsig", new.avg_active_pats_per_subsig,
        cur.avg_active_pats_per_subsig);
    chk("subsigs", new.subsigs, cur.subsigs);
    chk("basis_pats_in_trace", new.basis_pats_in_trace,
        cur.basis_pats_in_trace);
    chk("perc_comp_subsigs", new.perc_comp_subsigs, cur.perc_comp_subsigs);
    chk("sigs_sed", new.sigs_sed, cur.sigs_sed);
    chk("basis_unique_states", new.basis_unique_states,
        cur.basis_unique_states);
    chk("basis_acc_states", new.basis_acc_states, cur.basis_acc_states);
    chk("avg_pats_per_subsig", new.avg_pats_per_subsig,
        cur.avg_pats_per_subsig);
    chk("cp_basis_unique_states", new.cp_basis_unique_states,
        cur.cp_basis_unique_states);
    chk("cp_subsigs", new.cp_subsigs, cur.cp_subsigs);
    chk("dfa_sigs", new.dfa_sigs, cur.dfa_sigs);
    chk("dfa_subsigs", new.dfa_subsigs, cur.dfa_subsigs);
    chk("aggr_needs_subsigs", new.aggr_needs_subsigs, cur.aggr_needs_subsigs);
    chk("subsigs_igc", new.subsigs_igc, cur.subsigs_igc);
    chk("avg_active_pats_per_subsig_igc", new.avg_active_pats_per_subsig_igc,
        cur.avg_active_pats_per_subsig_igc);
    chk("basis_pats_in_trace_igc", new.basis_pats_in_trace_igc,
        cur.basis_pats_in_trace_igc);
    chk("perc_pats_expansion_rate_igc", new.perc_pats_expansion_rate_igc,
        cur.perc_pats_expansion_rate_igc);
    chk("basis_acc_states_igc", new.basis_acc_states_igc,
        cur.basis_acc_states_igc);
    if bad.is_empty() { Ok(()) } else { Err(bad) }
}

/// Assemble the rung ladder from P_max + band-DP specs (M11). subsigs gets the
/// +1 comp_sig dummy; aggr_needs is uniform = P_max.subsigs (the forward-queue
/// clamp is per-rung no-op -- gadget clamps it to each rung's own universe).
/// perc_pats/avg_active come from the band (already P_max-anchored); FSM/CP
/// basis caps are ratio-scaled per rung; perc_comp stays P_max.
pub fn assemble_ladder(p_max: &CapParams,
    specs: &[crate::band_dp::RungSpec]) -> Vec<CapParams> {
    // top rung carries the global-max structural rate; ratio-scale P_max's
    // basis caps by rung_rate/top_rate so the top rung == P_max and cheaper
    // rungs shrink to their band's demand. 0 -> no per-chunk data, keep P_max.
    let g_u = specs.last().map_or(0, |s| s.max_unique_acc_pats);
    let g_a = specs.last().map_or(0, |s| s.max_acc_states);
    let g_p = specs.last().map_or(0, |s| s.max_pats_in_trace);
    let g_c = specs.last().map_or(0, |s| s.max_cp_unique_states);
    let scale = |pmax_b: usize, rate: usize, g: usize| -> usize {
        if g == 0 { pmax_b }              // no per-chunk data -> keep P_max
        else { ((pmax_b * rate + g - 1) / g).min(pmax_b).max(2) }
    };
    let n = specs.len();
    specs.iter().enumerate().map(|(i, s)| {
        // Exact path (non-top rung): plan_rungs already de-saturated s.max_*
        // to the rung's own member max, so use it directly (clamped <=P_max).
        // Top rung + legacy path keep the P_max ratio-scale (top retains the
        // estimator margin since it cannot CapErr-bump).
        let exact = i + 1 != n;
        let pick = |pmax_b: usize, rate: usize, g: usize| -> usize {
            // exact non-top: the rung's own max (clamped <=P_max). When there
            // is no per-chunk data for this axis (g==0) keep P_max, mirroring
            // scale()'s no-data fallback.
            if exact { if g == 0 { pmax_b } else { rate.max(2).min(pmax_b) } }
            else { scale(pmax_b, rate, g) }
        };
        let mut c = p_max.clone();
        c.subsigs = s.subsigs + 1;
        c.aggr_needs_subsigs = p_max.subsigs;
        c.perc_pats_expansion_rate = s.perc_pats_expansion_rate;
        // aggressive forward-queue cap (exact per prod-band); igc stays the
        // P_max sentinel (floored for the dummy in determine_config_aggr).
        c.prod_pats_expansion = s.prod_pats_expansion;
        c.avg_active_pats_per_subsig = s.avg_active_pats_per_subsig;
        c.basis_unique_states =
            pick(p_max.basis_unique_states, s.max_unique_acc_pats, g_u);
        c.basis_acc_states =
            pick(p_max.basis_acc_states, s.max_acc_states, g_a);
        c.basis_pats_in_trace =
            pick(p_max.basis_pats_in_trace, s.max_pats_in_trace, g_p);
        c.cp_basis_unique_states =
            pick(p_max.cp_basis_unique_states, s.max_cp_unique_states, g_c);
        // fsm_adv requires basis_acc_states >= basis_pats_in_trace/10.
        c.basis_acc_states =
            c.basis_acc_states.max(c.basis_pats_in_trace / 10 + 1);
        c
    }).collect()
}

/// Save the rung LADDER (Vec<CapParams> JSON handoff; the Python driver
/// sequences runs and lets this file carry the config).
pub fn save_ladder(ladder: &[CapParams], path: &str) -> std::io::Result<()> {
    let s = serde_json::to_string_pretty(ladder).expect("ladder serialize");
    std::fs::write(path, s)
}

/// Load a ladder written by save_ladder. Panics loudly with the path on error.
pub fn load_ladder(path: &str) -> Vec<CapParams> {
    let s = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read ladder {}: {}", path, e));
    serde_json::from_str(&s)
        .unwrap_or_else(|e| panic!("parse ladder {}: {}", path, e))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zero_params() -> CapParams {
        CapParams {
            cp_basis_unique_states: 0, cp_subsigs: 0, cp_avg_pats: 0,
            subsigs: 0, avg_pats_per_subsig: 0, avg_active_pats_per_subsig: 0,
            basis_pats_in_trace: 0, perc_pats_expansion_rate: 0,
            prod_pats_expansion: 0, sigs_sed: 0,
            perc_comp_subsigs: 0, basis_unique_states: 0, basis_acc_states: 0,
            subsigs_igc: 0, avg_active_pats_per_subsig_igc: 0,
            basis_pats_in_trace_igc: 0, perc_pats_expansion_rate_igc: 0,
            prod_pats_expansion_igc: 0,
            basis_acc_states_igc: 0, basis_unique_states_igc: 0,
            dfa_sigs: 0, dfa_subsigs: 0, aggr_needs_subsigs: 0,
            max_word_len: 0, acdfa_state_part_bits: 0,
        }
    }

    #[test]
    fn test_caperr_mapping_each_param() {
        let cases = vec![
            ("dis_adv::perc_pats_expansion_rate, StepFwdPrf b_igc: false", 11000),
            ("dis_adv::avg_active_pats_per_subsig, b_igc: false", 12),
            ("comp_sig::perc_comp_subsigs", 17),
            ("comp_sig::sigs", 9),
            ("fsm_adv::basis_acc_states, b_igc: false", 1000),
            ("fsm_adv::basis_pats_in_trace for loc_state_pat_tbl, b_igc: false", 1400),
            ("dfa_adv::sigs", 6),
            ("dfa_adv::subsigs", 13),
        ];
        for (name, req) in cases {
            let mut p = zero_params();
            let (changed, unmapped) =
                apply_caperr_bumps(&mut p, false, &[(name.to_string(), req)]);
            assert!(changed, "no change for {}", name);
            assert!(unmapped.is_empty(), "unexpected unmapped for {}: {:?}",
                name, unmapped);
        }
    }

    #[test]
    fn test_caperr_values_and_max() {
        let mut p = zero_params();
        p.perc_pats_expansion_rate = 5555; // current > some, < others
        let (changed, _) = apply_caperr_bumps(&mut p, false, &[
            ("dis_adv::perc_pats_expansion_rate, StepFwdPrf b_igc: false"
                .to_string(), 10380)]);
        assert!(changed);
        assert_eq!(p.perc_pats_expansion_rate, 10380, "bumped to required");
        // a smaller required must NOT lower it (max semantics)
        let (changed2, _) = apply_caperr_bumps(&mut p, false, &[
            ("dis_adv::perc_pats_expansion_rate, StepFwdPrf b_igc: false"
                .to_string(), 9000)]);
        assert!(!changed2);
        assert_eq!(p.perc_pats_expansion_rate, 10380, "stays at max");
    }

    #[test]
    fn test_subsigs_aggr_cobump_and_unmapped() {
        // aggressive: a subsigs CapErr co-bumps aggr_needs_subsigs.
        let mut p = zero_params();
        let (changed, _) = apply_caperr_bumps(&mut p, true,
            &[("dis_adv::subsigs".to_string(), 3000)]);
        assert!(changed);
        // +1 reserves the comp_sig dummy entry (inp_subsigs[0] must be 0);
        // aggr_needs_subsigs carries the raw universe count.
        assert_eq!(p.subsigs, 3001);
        assert_eq!(p.aggr_needs_subsigs, 3000, "aggr co-bump");
        // non-aggressive: no co-bump.
        let mut p2 = zero_params();
        apply_caperr_bumps(&mut p2, false,
            &[("comp_sig::subsigs_cs".to_string(), 700)]);
        assert_eq!(p2.subsigs, 701);   // +1 dummy-entry reservation
        assert_eq!(p2.aggr_needs_subsigs, 0, "no aggr co-bump");
        // unknown name surfaces as unmapped.
        let mut p3 = zero_params();
        let (_changed, unmapped) = apply_caperr_bumps(&mut p3, false,
            &[("max_word_len".to_string(), 999),
              ("lkup::target_size".to_string(), 5)]);
        assert_eq!(unmapped.len(), 2, "both unknowns surfaced");
    }

    #[test]
    fn test_parse_caperr_from_panic() {
        let msg = "discharge_adv advice err: CapErr([(\"dis_adv::\
            perc_pats_expansion_rate, StepFwdPrf b_igc: false\", 19)])";
        let v = parse_caperr_from_panic(msg).expect("should parse");
        assert_eq!(v.len(), 1);
        assert!(v[0].0.starts_with("dis_adv::perc_pats_expansion_rate"));
        assert_eq!(v[0].1, 19);
        // multi-pair
        let msg2 = "x CapErr([(\"a::b\", 5), (\"c::d\", 12)]) y";
        let v2 = parse_caperr_from_panic(msg2).unwrap();
        assert_eq!(v2, vec![("a::b".to_string(), 5), ("c::d".to_string(), 12)]);
        // no CapErr -> None
        assert!(parse_caperr_from_panic("some other panic").is_none());
    }

    #[test]
    fn test_caperr_igc_routing() {
        let mut p = zero_params();
        // b_igc: true -> igc field, cs untouched.
        apply_caperr_bumps(&mut p, false, &[(
            "dis_adv::perc_pats_expansion_rate, StepFwdPrf b_igc: true"
                .to_string(), 50)]);
        assert_eq!(p.perc_pats_expansion_rate_igc, 50);
        assert_eq!(p.perc_pats_expansion_rate, 0, "cs untouched by igc");
        // b_igc: false -> cs field, igc untouched.
        apply_caperr_bumps(&mut p, false, &[(
            "dis_adv::avg_active_pats_per_subsig, b_igc: false".to_string(), 7)]);
        assert_eq!(p.avg_active_pats_per_subsig, 7);
        assert_eq!(p.avg_active_pats_per_subsig_igc, 0, "igc untouched by cs");
        // comp_sig::subsigs_igc -> subsigs_igc.
        apply_caperr_bumps(&mut p, false,
            &[("comp_sig::subsigs_igc".to_string(), 99)]);
        assert_eq!(p.subsigs_igc, 99);
        assert_eq!(p.subsigs, 0, "cs subsigs untouched by igc");
    }

    #[test]
    fn test_assemble_ladder() {
        use crate::band_dp::RungSpec;
        let mut p = zero_params();           // stand-in P_max
        p.subsigs = 201; p.perc_pats_expansion_rate = 8000;
        p.avg_active_pats_per_subsig = 12; p.basis_pats_in_trace = 700;
        let z = (0, 0, 0, 0);                // no per-chunk data -> keep P_max
        let specs = vec![
            RungSpec { subsigs: 0, perc_pats_expansion_rate: 125,
                prod_pats_expansion: 0,
                avg_active_pats_per_subsig: 1, max_unique_acc_pats: z.0,
                max_acc_states: z.1, max_pats_in_trace: z.2,
                max_cp_unique_states: z.3 },
            RungSpec { subsigs: 200, perc_pats_expansion_rate: 8000,
                prod_pats_expansion: 0,
                avg_active_pats_per_subsig: 12, max_unique_acc_pats: z.0,
                max_acc_states: z.1, max_pats_in_trace: z.2,
                max_cp_unique_states: z.3 }];
        let l = assemble_ladder(&p, &specs);
        assert_eq!(l.len(), 2);
        assert_eq!(l[0].subsigs, 1);         // 0 + dummy
        assert_eq!(l[0].perc_pats_expansion_rate, 125);
        assert_eq!(l[1].subsigs, 201);
        for c in &l {                        // uniform aggr_needs + structural rides along
            assert_eq!(c.aggr_needs_subsigs, p.subsigs);
            assert_eq!(c.basis_pats_in_trace, 700);
        }
        for w in l.windows(2) { assert!(w[0].subsigs <= w[1].subsigs); }
    }

    #[test]
    fn test_ladder_json_round_trip() {
        let mut a = zero_params(); a.subsigs = 5;
        let mut b = zero_params(); b.subsigs = 50;
        let l = vec![a, b];
        let f = std::env::temp_dir().join("m11_ladder_round_trip.json");
        save_ladder(&l, f.to_str().unwrap()).unwrap();
        assert_eq!(load_ladder(f.to_str().unwrap()), l);
    }
}
