#!/usr/bin/env python3
"""Write a NEW clam ladder.json whose rung 0 is set EXPLICITLY, from the
1,212-word 69908 decline census, under a hard cs1e budget.

READ-ONLY on the input: the source ladder is never modified.  Output is
a separate file, so the original stays usable as-is.

    python3 patch_ladder.py [SRC] [DST]
    default SRC ~/clam_ladder.json   DST ~/clam_ladder_rung0.json

Then run with  ZKR_NEO_LOAD_LADDER=$DST  and compare cs1e/fit.

WHY THIS WORKS WITHOUT A RECOMPILE.  CapParams.levels overrides the
ratio descent wholesale: build_circs_adv (zkp_driver.rs:399-412) calls
next_level() first and, when it yields, rebuilds ALL FIVE capacities via
caps_from_params_general -- decreased_copy(2) and every GlobalConfig
min_* floor are skipped for that rung.
"""
import copy
import json
import os
import sys

# ---- rung-0 targets -------------------------------------------------
# Census (1,212 words, 744 fit / 468 declined) + the neo cost model
# fitted on the two measured production COST blocks.  Budget: neo is
# 3,309,455 cs1e over legacy at 8 jobs (97,247,867 vs 93,938,412);
# cs1e ~ 2.5017 x circ0 R1CS.
#   qm 7644->1000 frees 3,388,265 ; GetSig inversion frees 500,109
#   spend  acc 569/bp, pats 1,706/bp, cp_uniq 1,157/bp = 1,013,565
#   net -2,874,809 cs1e, ~176,000 unspent as model margin.
QM_RUNG0       = 800    # was 7644.  q_m blocks 1 word in 1,212.
ACC_STATES     = 352    # was 268 (floor).  p90 of demand (193/214).
PATS_IN_TRACE  = 400    # was 295 (floor).  See the COUPLING note below.
CP_UNIQ_STATES = 1127   # was 1054 (floor). Max demand 1119 -> 138/138.
# rung 0 inherits the 368 min_subsigs floor while P_max cp_subsigs is
# ~40, so the CHEAP rung's GetSig is 1.77x the BIG rung's (108,616 vs
# 61,398).  The .max(floor) rules have no upper clamp.  Pin to P_max.
FIX_CP_SUBSIGS_INVERSION = True

# COUPLING -- basis_pats_in_trace is NOT independent of basis_acc_states.
# fsm_adv.rs:1301 joins locs_final x states_final (sized by
# basis_acc_states) into packed_trace_size (sized by
# basis_pats_in_trace), so raising acc raises the pats REQUIREMENT.
# fsm_adv.rs:1294-1299 states the intended relation: pats ~ 1.1 * acc,
# hard panic above 10x.  The original floors 295/268 are ratio 1.101 --
# they encoded this rule.  Measured: the all-zero dummy word demands
# pats = acc + 1 (it CapErr'd at 491 when acc was set to 490, which is
# how attempt 2 died at circuit-build time).
PATS_ACC_RATIO_MIN = 1.1

# clam production floors (bora_data_driver.rs CLAM spec).  min_cp_subsigs
# and min_subsigs_igc are unset, so both inherit min_subsigs = 368
# (consts.rs:601-612).
F_SUBSIGS, F_UNIQ, F_ACC, F_PATS = 368, 1054, 268, 295
F_AVGPATS, F_AVGACT, F_PERC, F_SIGSSED, F_COMPSUB = 8, 2, 1, 2, 10
F_DFA_SIGS, F_DFA_SUBSIGS = 3, 3


def dec2(p):
    """decreased_copy(2) + the clam floors, in Python.  Mirrors
    sed_mapper.rs:272-300, cp_mapper.rs:134-152, dfa_mapper.rs:127-143.
    Rust `*9/16` on usize truncates; Python `*9//16` matches for +ints."""
    c = copy.deepcopy(p)
    c["levels"] = []                       # a descended rung descends no further
    # CP (level 2 = /4).  cp_igc reuses these same three fields.
    c["cp_basis_unique_states"] = max(p["cp_basis_unique_states"] // 4, F_UNIQ)
    c["cp_subsigs"] = max(p["cp_subsigs"] // 4, F_SUBSIGS)
    c["cp_avg_pats"] = max(p["cp_avg_pats"] // 4, F_AVGPATS)
    # SED, case-sensitive arm (level 2).
    c["subsigs"] = max(p["subsigs"] * 9 // 16, F_SUBSIGS)
    c["avg_pats_per_subsig"] = max(p["avg_pats_per_subsig"] * 9 // 16, F_AVGPATS)
    c["avg_active_pats_per_subsig"] = max(
        p["avg_active_pats_per_subsig"] * 9 // 16, F_AVGACT)
    c["basis_pats_in_trace"] = max(p["basis_pats_in_trace"] // 16, F_PATS)
    c["perc_pats_expansion_rate"] = max(
        p["perc_pats_expansion_rate"] * 9 // 16, F_PERC)
    c["sigs_sed"] = max(p["sigs_sed"] * 16 // 25, F_SIGSSED)
    c["perc_comp_subsigs"] = max(p["perc_comp_subsigs"] * 9 // 16, F_COMPSUB)
    # shared by BOTH SED arms (caps_from_params_general passes the cs
    # field into sed_igc too) -- so this one axis is charged twice.
    c["basis_unique_states"] = max(p["basis_unique_states"] * 9 // 16, F_UNIQ)
    c["basis_acc_states"] = max(p["basis_acc_states"] // 16, F_ACC)
    # SED ignore-case arm.  NOTE avg_pats_per_subsig, sigs_sed,
    # perc_comp_subsigs and basis_unique_states are taken from the cs
    # fields above; basis_unique_states_igc is NOT read on this path.
    c["subsigs_igc"] = max(p["subsigs_igc"] * 9 // 16, F_SUBSIGS)
    c["avg_active_pats_per_subsig_igc"] = max(
        p["avg_active_pats_per_subsig_igc"] * 9 // 16, F_AVGACT)
    c["basis_pats_in_trace_igc"] = max(p["basis_pats_in_trace_igc"] // 16, F_PATS)
    c["perc_pats_expansion_rate_igc"] = max(
        p["perc_pats_expansion_rate_igc"] * 9 // 16, F_PERC)
    c["basis_acc_states_igc"] = max(p["basis_acc_states_igc"] // 16, F_ACC)
    c["basis_unique_states_igc"] = max(
        p["basis_unique_states_igc"] * 9 // 16, F_UNIQ)
    # DFA (level 2 = /4).
    c["dfa_sigs"] = max(p["dfa_sigs"] // 4, F_DFA_SIGS)
    c["dfa_subsigs"] = max(p["dfa_subsigs"] // 4, F_DFA_SUBSIGS)
    return c


def main(src, dst):
    if os.path.abspath(src) == os.path.abspath(dst):
        sys.exit("refusing to overwrite the source ladder: SRC == DST")
    if os.path.exists(dst):
        sys.exit("%s already exists -- delete it first" % dst)
    lad = json.load(open(src))
    if not isinstance(lad, list) or len(lad) != 1:
        sys.exit("expected a 1-rung clam ladder (P_max only), got %r"
                 % (len(lad) if isinstance(lad, list) else type(lad)))
    lad = copy.deepcopy(lad)               # source object stays pristine
    pmax = lad[0]
    if pmax.get("levels"):
        sys.exit("source ladder already carries levels[]; nothing to do")

    if PATS_IN_TRACE < ACC_STATES * PATS_ACC_RATIO_MIN:
        sys.exit("PATS_IN_TRACE %d < %.1f x ACC_STATES %d -- the joinwide "
                 "table would overflow and the DUMMY word fails at "
                 "circuit build (fsm_adv.rs:1294-1320)"
                 % (PATS_IN_TRACE, PATS_ACC_RATIO_MIN, ACC_STATES))
    if PATS_IN_TRACE > ACC_STATES * 10:
        sys.exit("PATS_IN_TRACE %d > 10 x ACC_STATES %d -- fsm_adv.rs:1298 "
                 "panics" % (PATS_IN_TRACE, ACC_STATES))

    r0 = dec2(pmax)                        # what the run ships TODAY
    before = copy.deepcopy(r0)
    # dec2 carries qm_real_rows verbatim; the live run applies F1's
    # dense-ratio scaling on top (36,400 -> 7,644 at production).  That
    # affects only the "rung0 now" column for qm, not what we install.
    # min(): never RAISE a child above its parent.
    r0["qm_real_rows"] = min(QM_RUNG0, pmax["qm_real_rows"])
    r0["basis_acc_states"] = ACC_STATES
    r0["basis_pats_in_trace"] = PATS_IN_TRACE
    r0["cp_basis_unique_states"] = CP_UNIQ_STATES
    if FIX_CP_SUBSIGS_INVERSION:
        r0["cp_subsigs"] = min(r0["cp_subsigs"], pmax["cp_subsigs"])

    pmax["levels"] = [r0]
    with open(dst, "w") as f:
        json.dump(lad, f, indent=4)

    print("source (unchanged) : %s" % src)
    print("written            : %s" % dst)
    print("%-32s %10s %10s %10s" % ("field", "P_max", "rung0 now", "rung0 new"))
    print("-" * 66)
    for k in sorted(before):
        if k != "levels" and before[k] != r0[k]:
            print("%-32s %10s %10s %10s" % (k, pmax[k], before[k], r0[k]))
    print("\nrung 0 is now EXPLICIT: decreased_copy(2) and every global")
    print("floor are bypassed for it.  P_max is byte-identical.")


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0] if a else os.path.expanduser("~/clam_ladder.json"),
         a[1] if len(a) > 1 else os.path.expanduser("~/clam_ladder_rung0.json"))
