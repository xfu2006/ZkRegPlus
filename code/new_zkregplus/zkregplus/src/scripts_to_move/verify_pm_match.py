#!/usr/bin/env python3
"""verify_pm_match.py -- offline analyzer for the 69200.* probe family.

Reads the probes_69200.txt produced by full_debug_watch.py inside a
bundle directory (extracted from the .tgz returned by the server) and
classifies the host-vs-circuit disagreement that triggers the panic at
compute_sig_adv.rs:1296 ("subsig_id ... res:3 is not false").

Usage:
    python3 verify_pm_match.py <bundle_dir> [--file <scanned_file>]

What it does:
  1. Parses the 69200.* probe lines into structured records.
  2. Reconciles host_chain (word strings) vs circ_chain (pat_ids
     resolved via 69200.c.patmap) -- they MUST be identical when
     translated through the patmap.
  3. Compares per-step witness counts: host arr_cur.n (from hs) vs
     circuit avail.n minus dummy bounds (which is the AC-DFA-tagged
     pat_loc table).
  4. If --file is supplied, treats the file as the *nibble-packed*
     scan target and grep-counts each chain word both as raw bytes
     (lowercase) and as a hex-nibble string (which is what the
     ACDFA/hs runs over). The latter is the relevant ground truth.
  5. Emits a verdict per (sig, subsig, step) classifying into one
     of four outcomes (see bottom of file).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from collections import defaultdict
from typing import Any, Dict, List, Optional, Tuple

# --- probe line parsers ---------------------------------------------------

# Each pattern is anchored at "DEBUG USE 69200.x:" and the rest is parsed
# with a few simple key=value extractors. The bundle prefixes each line
# with "[<source>] ", which we strip up front.

SRC_PREFIX = re.compile(r"^\[[^\]]+\]\s+")


def _strip(line: str) -> str:
    m = SRC_PREFIX.match(line)
    return line[m.end():] if m else line


# Helpers to pull key=val tokens out of free-form probe payloads. Values
# may be ints, debug-formatted Rust types like TriVal::False, vectors of
# tuples, or quoted strings. We capture the textual span and let the
# caller decide how to coerce.

# Match a key followed by '=' and then a "value" that is either:
#   - a quoted string  "..."
#   - a [...] vector
#   - any non-space, non-comma run
# We can't use a single regex elegantly because vectors contain spaces.
# Approach: split the payload into top-level (key=value) chunks by
# scanning brackets.

def _kv_pairs(payload: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    i = 0
    n = len(payload)
    while i < n:
        # skip whitespace and commas
        while i < n and payload[i] in " ,\t":
            i += 1
        # consume key
        j = i
        while j < n and payload[j] not in "= ":
            j += 1
        if j >= n or payload[j] != "=":
            break
        key = payload[i:j]
        # consume value
        j += 1
        v_start = j
        # value may be quoted, bracketed, or barewords until next " key="
        if j < n and payload[j] == '"':
            j += 1
            while j < n and payload[j] != '"':
                if payload[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                j += 1
            j += 1
        else:
            depth_paren = 0
            depth_brack = 0
            while j < n:
                c = payload[j]
                if c == "(":
                    depth_paren += 1
                elif c == ")":
                    depth_paren -= 1
                elif c == "[":
                    depth_brack += 1
                elif c == "]":
                    depth_brack -= 1
                elif (c in " ,"
                      and depth_paren <= 0
                      and depth_brack <= 0):
                    # peek: is this followed by another key=?
                    k = j + 1
                    while k < n and payload[k] in " ,\t":
                        k += 1
                    m = re.match(r"[A-Za-z_][\w.]*=", payload[k:])
                    if m:
                        break
                j += 1
        out[key] = payload[v_start:j]
        i = j
    return out


def _parse_int(s: str) -> int:
    return int(s.strip())


def _parse_str(s: str) -> str:
    s = s.strip()
    if s.startswith('"') and s.endswith('"') and len(s) >= 2:
        return s[1:-1]
    return s


def _parse_int_list(s: str) -> List[int]:
    s = s.strip()
    if s.startswith("[") and s.endswith("]"):
        body = s[1:-1].strip()
    else:
        body = s
    if not body:
        return []
    return [int(x.strip()) for x in body.split(",") if x.strip()]


def _parse_int_pair_list(s: str) -> List[Tuple[int, int]]:
    s = s.strip()
    if s.startswith("[") and s.endswith("]"):
        body = s[1:-1].strip()
    else:
        body = s
    if not body:
        return []
    pairs = re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", body)
    return [(int(a), int(b)) for a, b in pairs]


def _parse_bounds_chain(s: str) -> List[Tuple[Any, int, int]]:
    """Parse a Rust Debug of Vec<(String,(usize,usize))> or
    Vec<(usize,(usize,usize))>. Returns list of (key,a,b) where key is
    a string or int.
    """
    s = s.strip()
    if s.startswith("[") and s.endswith("]"):
        body = s[1:-1]
    else:
        body = s
    # Match either ("word", (a,b)) or (pat_id, (a,b))
    items: List[Tuple[Any, int, int]] = []
    # quoted-key form
    for m in re.finditer(
        r'\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*\(\s*(\d+)\s*,'
        r"\s*(\d+)\s*\)\s*\)",
        body,
    ):
        items.append((m.group(1), int(m.group(2)), int(m.group(3))))
    if items:
        return items
    # int-key form
    for m in re.finditer(
        r"\(\s*(\d+)\s*,\s*\(\s*(\d+)\s*,\s*(\d+)\s*\)\s*\)", body
    ):
        items.append((int(m.group(1)), int(m.group(2)),
                      int(m.group(3))))
    return items


# --- record types ---------------------------------------------------------

class HostBounds:
    __slots__ = ("sig", "ssid", "pat_len", "chain")

    def __init__(self, d: Dict[str, str]):
        self.sig = _parse_str(d["sig"])
        self.ssid = _parse_int(d["ssid"])
        self.pat_len = _parse_int(d["pat_len"])
        self.chain = _parse_bounds_chain(d["pm_bounds"])


class HostStep:
    __slots__ = ("sig", "ssid", "step", "word", "rg",
                 "prev_n", "cur_n", "cur_head", "next_n",
                 "next_head")

    def __init__(self, d: Dict[str, str]):
        self.sig = _parse_str(d["sig"])
        self.ssid = _parse_int(d["ssid"])
        self.step = _parse_int(d["step"])
        self.word = _parse_str(d["word"])
        rg = re.findall(r"\d+", d["rg"])
        self.rg = (int(rg[0]), int(rg[1]))
        self.prev_n = _parse_int(d["prev.n"])
        self.cur_n = _parse_int(d["cur.n"])
        self.cur_head = _parse_int_list(d["cur.head"])
        self.next_n = _parse_int(d["next.n"])
        self.next_head = _parse_int_list(d["next.head"])


class HostFinal:
    __slots__ = ("sig", "ssid", "arr_pos_n", "cost", "cost2", "res")

    def __init__(self, d: Dict[str, str]):
        self.sig = _parse_str(d["sig"])
        self.ssid = _parse_int(d["ssid"])
        self.arr_pos_n = _parse_int(d["arr_pos.n"])
        self.cost = _parse_int(d["cost"])
        self.cost2 = _parse_int(d["cost2"])
        self.res = d["res"].strip()


class HostSed:
    __slots__ = ("sig", "subsig_ids")

    def __init__(self, d: Dict[str, str]):
        self.sig = _parse_str(d["sig"])
        self.subsig_ids = _parse_int_list(d["subsig_ids"])


class CircPatMap:
    __slots__ = ("sig_id", "ss_idx", "subsig_id", "igc",
                 "chain_idx", "pat_id_circ", "word", "orig_rg")

    def __init__(self, d: Dict[str, str]):
        self.sig_id = _parse_int(d["sig_id"])
        self.ss_idx = _parse_int(d["subsig_idx"])
        self.subsig_id = _parse_int(d["subsig_id"])
        self.igc = d["igc"].strip() == "true"
        self.chain_idx = _parse_int(d["chain_idx"])
        self.pat_id_circ = _parse_int(d["pat_id_circ"])
        self.word = _parse_str(d["word"])
        rg = re.findall(r"\d+", d["orig_rg"])
        self.orig_rg = (int(rg[0]), int(rg[1]))


class CircBounds:
    __slots__ = ("subsig", "sig_id", "ss_idx", "igc",
                 "max_steps", "items_len", "chain")

    def __init__(self, d: Dict[str, str]):
        self.subsig = _parse_int(d["subsig"])
        self.sig_id = _parse_int(d["sig_id"])
        self.ss_idx = _parse_int(d["ss_idx"])
        self.igc = d["igc"].strip() == "true"
        self.max_steps = _parse_int(d["max_steps"])
        self.items_len = _parse_int(d["items.len"])
        self.chain = _parse_bounds_chain(d["pm_bounds"])


class CircStep:
    __slots__ = ("subsig", "step", "dst_pat", "rg",
                 "prev_n", "avail_n", "avail_head",
                 "added", "next_n", "next_head")

    def __init__(self, d: Dict[str, str]):
        self.subsig = _parse_int(d["subsig"])
        self.step = _parse_int(d["step"])
        self.dst_pat = _parse_int(d["dst_pat"])
        rg = re.findall(r"\d+", d["rg"])
        self.rg = (int(rg[0]), int(rg[1]))
        self.prev_n = _parse_int(d["prev.n"])
        self.avail_n = _parse_int(d["avail.n"])
        self.avail_head = _parse_int_pair_list(d["avail.head"])
        self.added = _parse_int(d["added"])
        self.next_n = _parse_int(d["next.n"])
        self.next_head = _parse_int_list(d["next.head"])


class CircRawRes:
    __slots__ = ("sid", "sig_id", "ss_idx",
                 "gen_regex_res", "raw_res", "count_res")

    def __init__(self, d: Dict[str, str]):
        self.sid = _parse_int(d["sid"])
        self.sig_id = _parse_int(d["sig_id"])
        self.ss_idx = _parse_int(d["ss_idx"])
        self.gen_regex_res = d["gen_regex_res"].strip()
        self.raw_res = d["raw_res"].strip()
        self.count_res = d["count_res"].strip()


# --- load probes ----------------------------------------------------------

TAG_RE = re.compile(r"^DEBUG USE 69200\.([\w.]+):\s*(.*)$")


def load_probes(probes_file: Path):
    host_bounds: Dict[Tuple[str, int], HostBounds] = {}
    host_steps: Dict[Tuple[str, int, int], HostStep] = {}
    host_final: Dict[Tuple[str, int], HostFinal] = {}
    host_sed: List[HostSed] = []
    circ_patmap: List[CircPatMap] = []
    circ_bounds: Dict[int, CircBounds] = {}
    circ_steps: Dict[Tuple[int, int], CircStep] = {}
    circ_raw_res: List[CircRawRes] = []

    lost = 0
    for raw in probes_file.read_text(errors="replace").splitlines():
        line = _strip(raw)
        m = TAG_RE.match(line)
        if not m:
            continue
        tag, payload = m.group(1), m.group(2)
        d = _kv_pairs(payload)
        try:
            if tag == "h.bounds":
                hb = HostBounds(d)
                host_bounds[(hb.sig, hb.ssid)] = hb
            elif tag == "h.step":
                hs = HostStep(d)
                host_steps[(hs.sig, hs.ssid, hs.step)] = hs
            elif tag == "h.final":
                hf = HostFinal(d)
                host_final[(hf.sig, hf.ssid)] = hf
            elif tag.startswith("h.sed"):
                host_sed.append(HostSed(d))
            elif tag == "c.patmap":
                circ_patmap.append(CircPatMap(d))
            elif tag == "c.bounds":
                cb = CircBounds(d)
                circ_bounds[cb.subsig] = cb
            elif tag == "c.step":
                cs = CircStep(d)
                circ_steps[(cs.subsig, cs.step)] = cs
            elif tag == "c.raw_res":
                circ_raw_res.append(CircRawRes(d))
            # c.break is informational only.
        except (KeyError, ValueError, IndexError):
            lost += 1
            continue
    return {
        "host_bounds": host_bounds,
        "host_steps": host_steps,
        "host_final": host_final,
        "host_sed": host_sed,
        "circ_patmap": circ_patmap,
        "circ_bounds": circ_bounds,
        "circ_steps": circ_steps,
        "circ_raw_res": circ_raw_res,
        "lost": lost,
    }


# --- file ground truth ----------------------------------------------------

# The on-disk scanned file is byte-oriented; the AC-DFA / hs run over
# nibble-hex (lowercase). For host words like ".js", look up raw bytes;
# for circuit pat strings (which may be the same word or a hex form
# depending on the subsig type), try both.

def count_substring(blob: bytes, needle: bytes) -> int:
    if not needle:
        return 0
    count = 0
    pos = 0
    while True:
        i = blob.find(needle, pos)
        if i < 0:
            return count
        count += 1
        pos = i + 1


def file_hits(path: Path, word: str) -> Dict[str, int]:
    blob = path.read_bytes()
    nibble_hex = blob.hex().encode()
    out = {}
    try:
        out["raw_bytes"] = count_substring(blob, word.encode())
    except Exception:
        out["raw_bytes"] = -1
    try:
        out["nibble_hex"] = count_substring(
            nibble_hex, word.lower().encode())
    except Exception:
        out["nibble_hex"] = -1
    return out


# --- analysis -------------------------------------------------------------

TARGET_SIGS = {
    34555: "Email.Phishing.VOF1-6295244-1",
    35355: "Win.Virus.Hematite-6232506-0",
    # which subsig (0-based) is the one that hits the panic:
    # 34555 -> 2 ;  35355 -> 0
}
TARGET_SUBSIG = {34555: 2, 35355: 0}


def analyze(probes: Dict, scanned_file: Optional[Path]) -> None:
    print(f"lost lines: {probes['lost']}")
    print()
    for sig_id, sig_name in TARGET_SIGS.items():
        target_ss = TARGET_SUBSIG[sig_id]
        print("=" * 78)
        print(f"sig_id={sig_id}  name={sig_name}  "
              f"target_subsig_idx={target_ss}")

        # --- host side ----------------------------------------------------
        hb = probes["host_bounds"].get((sig_name, target_ss))
        hf = probes["host_final"].get((sig_name, target_ss))
        host_chain = hb.chain if hb else None
        sed_seen = any(s.sig == sig_name
                       for s in probes["host_sed"])

        if hb:
            print(f"  HOST chain (word, rg) len={hb.pat_len}:")
            for w, a, b in host_chain:
                print(f"    word={w!r}  rg=({a},{b})")
        else:
            print("  HOST chain: <no 69200.h.bounds for this "
                  "(sig,subsig)>")

        if hf:
            print(f"  HOST final: arr_pos.n={hf.arr_pos_n} "
                  f"cost={hf.cost} cost2={hf.cost2} res={hf.res}")
        if sed_seen:
            print("  HOST SED: confirmed in vec_sed_sigs_info "
                  "(host says False).")

        # --- circuit side -------------------------------------------------
        # Find the encoded subsig_id matching this (sig_id, target_ss)
        # via the patmap. Multiple patmap rows per (sig_id, ss_idx) are
        # possible (different chain entries); take any.
        rows = [r for r in probes["circ_patmap"]
                if r.sig_id == sig_id and r.ss_idx == target_ss]
        encoded = rows[0].subsig_id if rows else None
        if rows:
            # Build (chain_idx -> (word, pat_id_circ, orig_rg))
            chain_idx_to = {}
            for r in rows:
                chain_idx_to[r.chain_idx] = (
                    r.word, r.pat_id_circ, r.orig_rg)
            print(f"  CIRC patmap rows: {len(rows)}, "
                  f"encoded_subsig={encoded}")
            for k in sorted(chain_idx_to):
                w, pid, rg = chain_idx_to[k]
                print(f"    chain[{k}] word={w!r} "
                      f"pat_id_circ={pid}  orig_rg={rg}")
        else:
            print("  CIRC patmap rows: 0 (no 69200.c.patmap for "
                  "this sig)")
            chain_idx_to = {}

        cb = (probes["circ_bounds"].get(encoded)
              if encoded is not None else None)
        if cb:
            print(f"  CIRC bounds: max_steps={cb.max_steps} "
                  f"items.len={cb.items_len} chain={cb.chain}")
        else:
            print("  CIRC bounds: <no 69200.c.bounds>")

        # --- chain equality check ----------------------------------------
        if host_chain and cb and chain_idx_to:
            # circ chain is [(pat_id_circ, (a,b)), ...]
            mismatches = []
            for i, (cpid, ca, cb2) in enumerate(cb.chain):
                hword, ha, hb2 = host_chain[i]
                expect_pid = chain_idx_to.get(i, (None, None, None))[1]
                if expect_pid != cpid:
                    mismatches.append(
                        f"step{i}: patmap_pid={expect_pid} "
                        f"vs circ_chain_pid={cpid}")
            if mismatches:
                print("  !! CHAIN MISMATCH:")
                for m in mismatches:
                    print(f"    {m}")
            else:
                print("  chain equality: HOST chain words ≡ "
                      "CIRC chain pat_ids (via patmap). OK.")

        # --- per-step verdict --------------------------------------------
        print("  -- per-step --")
        max_step = 0
        if hb:
            max_step = max(max_step, hb.pat_len)
        if cb:
            max_step = max(max_step, cb.max_steps)
        for s in range(max_step):
            hs = probes["host_steps"].get(
                (sig_name, target_ss, s))
            cs = (probes["circ_steps"].get((encoded, s + 1))
                  if encoded is not None else None)
            host_cur_n = hs.cur_n if hs else "?"
            host_next_n = hs.next_n if hs else "?"
            # Subtract the 2 dummy bounding entries circuit always
            # inserts when hm_loc.get returns None. If avail_n == 2
            # AND avail_head == [(0,0),(1,max)] -> 0 real positions.
            if cs:
                avail_real = cs.avail_n
                # Heuristic: count entries with start>=1 and
                # start<=max-1 as "real". The dummies have start==0
                # or start==1 with end==max.
                avail_real_heur = sum(
                    1 for (a, b) in cs.avail_head
                    if not (a == 0 and b == 0)
                    and not (a == 1 and b >= (1 << 24))
                )
                avail_str = (f"{cs.avail_n}"
                             f"(real~{avail_real_heur})")
                added_str = str(cs.added)
            else:
                avail_str = "?"
                added_str = "?"
            # Ground truth via file
            gt = "?"
            if scanned_file and hs:
                hits = file_hits(scanned_file, hs.word)
                gt = (f"raw={hits['raw_bytes']} "
                      f"nib={hits['nibble_hex']}")
            print(f"    step={s:>2}  host(cur.n={host_cur_n}, "
                  f"next.n={host_next_n})  "
                  f"circ(avail={avail_str}, added={added_str})"
                  f"   gt={{ {gt} }}")

        # --- circuit raw_res ---------------------------------------------
        rr_rows = [r for r in probes["circ_raw_res"]
                   if r.sig_id == sig_id]
        if rr_rows:
            print(f"  CIRC raw_res samples ({len(rr_rows)} total):")
            for r in rr_rows[:4]:
                print(f"    sid={r.sid} ss_idx={r.ss_idx} "
                      f"gen_regex_res={r.gen_regex_res} "
                      f"raw_res={r.raw_res} "
                      f"count_res={r.count_res}")

        # --- verdict ------------------------------------------------------
        print("  VERDICT:")
        verdict = classify(probes, sig_id, target_ss, sig_name,
                           scanned_file)
        print(f"    -> {verdict}")
        print()

    # Bottom-line summary
    print("=" * 78)
    print("Outcome legend:")
    print("  A) host=False, circ=Maybe, gt=absent")
    print("     -> definitional mismatch (host returns False for")
    print("        'no occurrences', circuit refuses without")
    print("        positions). Fix: tighten host to return Maybe")
    print("        when cost2==0.")
    print("  B) host=False, circ=Maybe, gt=present")
    print("     -> witness builder dropped real occurrences from")
    print("        pat_loc table. Investigate hm_loc build.")
    print("  C) host=Maybe AND not in vec_sed_sigs_info")
    print("     -> would not have panicked; sanity rule-out.")
    print("  D) host_chain != circ_chain")
    print("     -> two pm-bound constructions diverged "
          "(separate bug).")


def classify(probes, sig_id, target_ss, sig_name,
             scanned_file) -> str:
    hb = probes["host_bounds"].get((sig_name, target_ss))
    hf = probes["host_final"].get((sig_name, target_ss))
    sed_seen = any(s.sig == sig_name for s in probes["host_sed"])
    rows = [r for r in probes["circ_patmap"]
            if r.sig_id == sig_id and r.ss_idx == target_ss]
    encoded = rows[0].subsig_id if rows else None
    cb = (probes["circ_bounds"].get(encoded)
          if encoded is not None else None)
    # Chain equality
    if hb and cb and rows:
        chain_idx_to = {r.chain_idx: r.pat_id_circ for r in rows}
        chain_ok = (len(cb.chain) == len(hb.chain)
                    and all(chain_idx_to.get(i) == cb.chain[i][0]
                            for i in range(len(cb.chain))))
        if not chain_ok:
            return ("D) host_chain != circ_chain "
                    "(two pm-bound constructions diverged)")

    if hf and "Maybe" in hf.res and not sed_seen:
        return "C) host returned Maybe; subsig not discharged"

    if hf and "False" in hf.res:
        # Decide host evidence: was there ANY occurrence?
        host_had_any = False
        if hb:
            for s in range(hb.pat_len):
                hs = probes["host_steps"].get(
                    (sig_name, target_ss, s))
                if hs and hs.cur_n > 0:
                    host_had_any = True
                    break
        # Decide ground truth via file lookup
        gt_present = None
        if scanned_file and hb:
            for w, _, _ in hb.chain:
                hits = file_hits(scanned_file, w)
                if (hits["raw_bytes"] > 0
                        or hits["nibble_hex"] > 0):
                    gt_present = True
                    break
            if gt_present is None:
                gt_present = False
        if host_had_any:
            return ("host=False but some chain links had hits "
                    "(filter collapsed mid-chain — "
                    "check 'allowed_pos' math)")
        if gt_present is True:
            return ("B) host=False, circ=Maybe, gt=present "
                    "-> witness builder dropped real "
                    "occurrences")
        return ("A) host=False, circ=Maybe, gt=absent "
                "-> definitional mismatch (host's vacuous-False "
                "branch); fix is host-side (return Maybe when "
                "cost2==0)")
    return "INCONCLUSIVE (missing probes — check bundle)"


# --- main -----------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("bundle_dir", type=Path)
    ap.add_argument("--file", type=Path,
                    help="path to the scanned file (for "
                         "ground-truth lookup)")
    args = ap.parse_args()

    probes_file = args.bundle_dir / "probes_69200.txt"
    if not probes_file.exists():
        print(f"ERROR: {probes_file} not found", file=sys.stderr)
        return 2
    probes = load_probes(probes_file)
    analyze(probes, args.file)
    return 0


if __name__ == "__main__":
    sys.exit(main())
