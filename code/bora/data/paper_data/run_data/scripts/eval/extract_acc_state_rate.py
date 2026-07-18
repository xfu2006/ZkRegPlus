#!/usr/bin/env python3
# ----------------------------------
# Designed by the paper author; function implementation by Claude Code 4.8.
# Code reviewed and audited by the author; the number was manually verified
# by the paper author.
# ----------------------------------
"""Extract the AC-DFA accepting-state density rho (perc_acc) per dataset.

rho(w) = (# AC-DFA accepting-state hits while walking w) / |w|  in [0,1]
is the density that appears as the "sparse match locations" claim in the
§6.4 Complexity remark.

Reads (first that exists, or an explicit path as argv[1]):
  <paper_root>/data/raw_data/any_server/dump_acc_state_ratio.txt  -- preferred:
      the dump from report_acc_state_rate() (full ClamAV corpus, full_clam DB
      cache "full_data"), whose print_discharge_stats block carries the
      aggregate rho line.
  <paper_root>/data/raw_data/any_server/eval_effective.txt  -- fallback: the
      older tier dump; carries per-record fields but only the SAMPLED subset
      of files, so rho is recomputed from records and flagged as a sample.

Generation (on the data laptop, from the crate dir):
  cd .../new_zkregplus/zkregplus
  cargo test --lib --release -- test_acc_state_rate --show-output --nocapture 2>&1 \
      | tee <paper_root>/data/raw_data/any_server/dump_acc_state_ratio.txt
  report_acc_state_rate() calls run_db_bundle -> print_discharge_stats, whose
  line "acc_states/path_len: avg: X%, max: Y%" is rho (avg/max over words).

Prints a per-dataset summary; makes no files. Run with no args.
"""
from __future__ import annotations

import re
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import any_server_file  # noqa: E402

# banner emitted by collect_assess_tier_data() before each dataset's stats
BANNER = re.compile(r"ACC-STATE-RATE:\s*(\w+)")
# aggregate line from print_discharge_stats (stats_helper.rs:278-280)
AVG_MAX = re.compile(r"acc_states/path_len:\s*avg:\s*([\d.]+)%,\s*max:\s*([\d.]+)%")
# pooled multiplicity line (stats_helper.rs:277)
POOLED_MULT = re.compile(
    r"accepted states.*?/acc_path:\s*([\d.]+)%,\s*accepted_states:\s*(\d+),"
    r"\s*accpath_len:\s*(\d+)")
# pooled dedup line, position counted once (stats_helper.rs:276)
POOLED_DEDUP = re.compile(
    r"hs_len.*?/acc_path:\s*([\d.]+)%,\s*hs_len:\s*(\d+),"
    r"\s*accpath_len:\s*(\d+)")
# per-record fields (data_processor discharge_proof::FailDischargeRecord)
REC = re.compile(
    r"total_acc_path_len:\s*(\d+).*?total_hs_size:\s*(\d+).*?total_accepted:\s*(\d+)",
    re.S)
# SED/ISED stats block: steps (pattern words) per signature (stats_helper.rs).
# The SED line is the SDE tier that nu multiplies in the complexity bound.
# NOTE: the dump reports avg_steps only; there is no per-sig max in the dump,
# so this yields the AVERAGE steps/sig, not the theorem's nu = max steps/sig.
SED_STATS = re.compile(
    r"===\s*(I?SED)\s*Stats\s*=+\s*\n"
    r".*?sigs:\s*(\d+),\s*subsigs:\s*(\d+),"
    r"\s*total_steps:\s*(\d+),\s*avg_steps:\s*(\d+)")


def from_sed_stats(text: str) -> dict[str, dict] | None:
    """Pull steps-per-signature from the SED/ISED Stats blocks.

    Returns {"SED": {...}, "ISED": {...}} with sigs, subsigs, total_steps,
    avg_steps. nu in the complexity bound is the SDE tier -> use "SED".
    Returns None if no such block is present.
    """
    out: dict[str, dict] = {}
    for tier, sigs, subsigs, total, avg in SED_STATS.findall(text):
        out[tier] = {"sigs": int(sigs), "subsigs": int(subsigs),
                     "total_steps": int(total), "avg_steps": int(avg)}
    return out or None


def pct(x: float) -> str:
    return f"{x * 100:.3f}%"


def from_aggregate(text: str) -> dict[str, dict]:
    """Pull the print_discharge_stats aggregate lines, keyed by dataset.

    Datasets are delimited by the ACC-STATE-RATE banner; the first aggregate
    line seen after a banner belongs to that dataset (later size-bucket blocks
    are ignored -- they carry no banner).
    """
    out: dict[str, dict] = {}
    cur = None
    for line in text.splitlines():
        b = BANNER.search(line)
        if b:
            cur = b.group(1)
            out.setdefault(cur, {})
            continue
        # single-dataset run (report_acc_state_rate) has no per-dataset
        # banner -> bucket its aggregate lines under "clamav".
        d = out.setdefault(cur if cur is not None else "clamav", {})
        m = AVG_MAX.search(line)
        if m and "avg" not in d:
            d["avg"], d["max"] = float(m.group(1)) / 100, float(m.group(2)) / 100
        m = POOLED_MULT.search(line)
        if m and "pooled" not in d:
            d["pooled"] = float(m.group(1)) / 100
        m = POOLED_DEDUP.search(line)
        if m and "pooled_dedup" not in d:
            d["pooled_dedup"] = float(m.group(1)) / 100
    return {k: v for k, v in out.items() if v}


def from_records(text: str) -> dict | None:
    """Fallback: recompute rho from per-record fields (whole file, one bucket).

    Returns None if no records present. rho is reported both with per-sig
    multiplicity (total_accepted) and deduped (total_hs_size).
    """
    recs = REC.findall(text)
    rows = [(int(p), int(hs), int(a)) for p, hs, a in recs if int(p) > 0]
    if not rows:
        return None
    rho = [a / p for p, _, a in rows]
    rho_dd = [hs / p for p, hs, _ in rows]
    sp = sum(p for p, _, _ in rows)
    sa = sum(a for _, _, a in rows)
    shs = sum(hs for _, hs, _ in rows)
    return {
        "n": len(rows),
        "avg": statistics.fmean(rho), "median": statistics.median(rho),
        "max": max(rho), "min": min(rho), "pooled": sa / sp,
        "avg_dedup": statistics.fmean(rho_dd), "pooled_dedup": shs / sp,
    }


def main() -> None:
    if len(sys.argv) > 1:
        path = Path(sys.argv[1])
    else:
        for name in ("dump_acc_state_ratio.txt", "acc_state_rate.txt",
                     "eval_effective.txt"):
            path = any_server_file(name)
            if path.exists():
                break
    if not path.exists():
        sys.exit(f"no dump found: {path}")
    text = path.read_text(errors="replace")
    print(f"# source: {path}")

    agg = from_aggregate(text)
    if agg:
        print("# per-word rho = acc_states/path_len (AC-DFA accepting-state "
              "density):")
        for ds, d in agg.items():
            if "avg" in d:
                print(f"  {ds:8s} per-word avg = {pct(d['avg'])}   "
                      f"per-word max = {pct(d['max'])}")
        sed = from_sed_stats(text)
        if sed:
            print("# nu = steps (pattern words) per signature; SED = SDE tier "
                  "(dump has AVG only, not the theorem's max):")
            for tier in ("SED", "ISED"):
                if tier in sed:
                    d = sed[tier]
                    print(f"  {tier:8s} avg_steps = {d['avg_steps']}   "
                          f"(sigs = {d['sigs']}, total_steps = "
                          f"{d['total_steps']})")
        return

    rec = from_records(text)
    if rec is None:
        sys.exit("no aggregate blocks and no records found -- wrong dump?")
    print(f"# no aggregate blocks; recomputed from {rec['n']} records "
          f"(WARNING: eval_effective.txt is a SAMPLED subset, not the full corpus)")
    print(f"  per-word rho  avg = {pct(rec['avg'])}")
    print(f"  per-word rho  max = {pct(rec['max'])}")


if __name__ == "__main__":
    main()
