#!/usr/bin/env python3
"""FAST NUMA / memory-bandwidth attribution probe for full_dlp().

WHY THIS EXISTS
  full_dlp() Phase-1 (the folding/MSM pass) is ~36/27 (~1.33x) slower on
  gcpm1 than the jetstream2-512GB baseline; on the 128-cpu/1TB box the same
  effect is ~2.6x. The team already MEASURED the cause (see run_full_dlp.py
  docstring): 8 jobs confined to ONE socket = ~0.89x the 512GB baseline, but
  16 jobs across BOTH sockets saturates memory bandwidth = ~2.5x slower. So
  the regression is NUMA / cross-socket DRAM bandwidth on the shared MSM base
  arrays (veccom lagkeys / pedersen generators, one Arc first-touched on one
  node), NOT the GlobalConfig RwLock. This script CONFIRMS that on whatever
  box you run it, FAST, and tells you the best numactl policy there.

HOW IT STAYS FAST (no 8-hour run, no Rust change)
  Per-step fold time is the INVARIANT. A full run is ~27-36 min only because
  it folds thousands of words; each step's MSM cost is identical whether you
  fold 30 words or 30000. We cap the fold with ZKR_WORD_CAP_PER_JOB (an
  existing env knob, driver.rs:2666) so full_dlp does a handful of real
  folding steps and exits in minutes, then we read the per-step fold ms that
  the prover already logs ("prove_step cost: ... circ_id: N ... W ms"). We
  run that capped fold under each numactl policy and compare per-step ms.
  Everything is driven by EXISTING env vars + numactl -- zero Rust edits.

TIERS (run fastest-first)
  Tier A  test_msm proxy   : BN254 G1 MSM (the veccom.rs:315 kernel) under a
                             numactl matrix. No data, no cache, ~minutes.
                             Reproduces the NUMA penalty in isolation.
  Tier B  capped full_dlp  : the REAL folding path, ZKR_WORD_CAP_PER_JOB
                             small, under a numactl matrix. Per-step fold ms.
                             Needs the full_dlp cache warm (one-time ~0.5hr;
                             reused across all policy runs).
  Tier C  perf c2c (opt)   : attach perf c2c to an UNcapped full_dlp to name
                             the contended cache line (proves it's the SRS
                             array, not GLOBAL_CONFIG). Needs perf privilege.

USAGE (run ON the box under test, e.g. gcpm1)
  python3 numa_probe.py                      # Tier A + Tier B, default cap=40
  python3 numa_probe.py --dry-run            # print plan + commands, run none
  python3 numa_probe.py --msm-only           # Tier A only (instant signal)
  python3 numa_probe.py --skip-msm           # Tier B only
  python3 numa_probe.py --word-cap 80 --jobs 8
  python3 numa_probe.py --policies socket,interleave,off,local0,remote
  python3 numa_probe.py --c2c                # also Tier C (uncapped, perf)
  python3 numa_probe.py --skip-warm          # cache already warm

Stdlib only. Mirrors run_full_dlp.py conventions (runcfg, numa_prefix, env).
"""

import argparse
import datetime
import glob
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import time


HERE = os.path.dirname(os.path.abspath(__file__))          # zkregplus/src
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))     # new_zkregplus
ZKREG = os.path.join(REPO, "zkregplus")                    # crate w/ example
CFG_DIR = os.path.join(REPO, "data/paper_data/dlp/cfg/config")
LOGS_DIR = os.path.join(REPO, "data/cache/logs")
# Durable history of probe runs (data/cache is gitignored but persists on the
# box, and survives a git branch switch -- so baseline vs arcswap vs
# replicate-keys results all live here for --compare).
HIST_DIR = os.path.join(REPO, "data/cache/numa_probe")

# MEASURED reference points from run_full_dlp.py (jetstream2):
#   socket-confined 8 jobs ~ 0.89x the 512GB baseline (FASTER)
#   16 jobs both sockets   ~ 2.5x slower (bandwidth-saturated)
REF_SOCKET = 0.89
REF_BOTH = 2.5


# ----------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------
def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def have(tool):
    return shutil.which(tool) is not None


def read_file(p, d=""):
    try:
        with open(p) as f:
            return f.read()
    except Exception:
        return d


def banner(t):
    print("\n" + "=" * 70 + "\n" + t + "\n" + "=" * 70)


# ----------------------------------------------------------------------
# topology / tools
# ----------------------------------------------------------------------
def detect():
    info = {"nnodes": 1, "node_cpus": {}, "node_mem_mb": {},
            "total_cpus": os.cpu_count() or 1}
    if have("numactl"):
        h = run(["numactl", "-H"]).stdout
        info["numactl_H"] = h
        m = re.search(r"available:\s+(\d+)\s+nodes", h)
        if m:
            info["nnodes"] = int(m.group(1))
        for nid, cpus in re.findall(r"node (\d+) cpus:\s*([0-9 ]*)", h):
            info["node_cpus"][int(nid)] = cpus.split()
        for nid, sz in re.findall(r"node (\d+) size:\s*(\d+)\s*MB", h):
            info["node_mem_mb"][int(nid)] = int(sz)
    else:
        info["nnodes"] = max(
            len(glob.glob("/sys/devices/system/node/node[0-9]*")), 1)
    try:
        info["paranoid"] = int(read_file(
            "/proc/sys/kernel/perf_event_paranoid", "99").strip())
    except Exception:
        info["paranoid"] = 99
    info["is_root"] = (os.geteuid() == 0)
    info["have_perf"] = have("perf")
    info["have_numactl"] = have("numactl")
    info["have_numastat"] = have("numastat")
    info["perf_stat_ok"] = info["have_perf"] and (
        info["is_root"] or info["paranoid"] <= 1)
    info["perf_c2c_ok"] = info["have_perf"] and (
        info["is_root"] or info["paranoid"] <= 0)
    return info


def print_env(info):
    banner("ENVIRONMENT / TOPOLOGY")
    print("repo          : %s" % REPO)
    print("logical cpus  : %d" % info["total_cpus"])
    print("NUMA nodes    : %d" % info["nnodes"])
    for nid in sorted(info["node_cpus"]):
        print("  node %d      : %d cpus, %d MB" % (
            nid, len(info["node_cpus"][nid]), info["node_mem_mb"].get(nid, 0)))
    print("tools         : numactl=%s numastat=%s perf=%s" % (
        info["have_numactl"], info["have_numastat"], info["have_perf"]))
    print("perf          : paranoid=%s root=%s stat_ok=%s c2c_ok=%s" % (
        info["paranoid"], info["is_root"],
        info["perf_stat_ok"], info["perf_c2c_ok"]))
    if info["nnodes"] <= 1:
        print("\nNOTE: single NUMA node -> cross-node policies are no-ops here.")
        print("      The 2.6x is a 2-socket effect; a 1-node box cannot show")
        print("      it. Tier A still measures bandwidth saturation under load.")


# ----------------------------------------------------------------------
# numactl policy -> argv prefix (mirrors run_full_dlp.numa_prefix + extras)
# ----------------------------------------------------------------------
def numa_prefix(policy, info):
    nn = info["nnodes"]
    if policy in ("off", "none", "perjob"):
        return []
    if not info["have_numactl"] or nn <= 1:
        return []
    if policy == "interleave":
        return ["numactl", "--interleave=all"]
    if policy == "socket":
        half = max(1, nn // 2)
        return ["numactl", "--cpunodebind=0-%d" % (half - 1)]
    if policy == "local0":
        return ["numactl", "--cpunodebind=0", "--membind=0"]
    if policy == "remote":
        return ["numactl", "--cpunodebind=0", "--membind=%d" % (nn - 1)]
    return []


def policy_note(policy, info):
    return {
        "off": "no numactl (OS first-touch) -- baseline",
        "socket": "confine cpus to first socket's nodes (team default/best)",
        "interleave": "stripe pages over all nodes (run_full_clam default)",
        "local0": "node-0 cpus + node-0 memory (all-local contrast)",
        "remote": "node-0 cpus + far-node memory (FORCED REMOTE, worst case)",
        "perjob": "Rust foldpot::numa per-job pinning (ZKR_NUMA=perjob)",
    }.get(policy, policy)


def default_policies(info):
    base = ["off", "socket", "interleave"]
    if info["nnodes"] >= 2:
        base += ["local0", "remote"]
    return base


# ----------------------------------------------------------------------
# RUSTFLAGS
# ----------------------------------------------------------------------
def rustflags(override):
    if override is not None:
        return override
    env = os.environ.get("RUSTFLAGS")
    if env is not None:
        return env
    if have("ld.lld") or have("lld"):
        return "-C link-args=-fuse-ld=lld -Awarnings"
    return "-Awarnings"


# ----------------------------------------------------------------------
# Tier A: test_msm proxy
# ----------------------------------------------------------------------
MSM_LINE = re.compile(
    r"N=(\d+):\s*msm_med_ms=([\d.]+),\s*norm=([\d.]+)x,"
    r"\s*dram_per_thread=([\d.]+)\s*GB/s,\s*total=([\d.]+)\s*GB/s")


def build_test_msm(rf, dry):
    cmd = ["cargo", "build", "--release", "--example", "test_msm"]
    print("[build] cd %s ; RUSTFLAGS=%r ; %s" % (ZKREG, rf, " ".join(cmd)))
    if dry:
        return True
    r = subprocess.run(cmd, cwd=ZKREG, env=dict(os.environ, RUSTFLAGS=rf))
    if r.returncode != 0:
        print("[build] FAILED. Try --rustflags '-Awarnings' or --skip-msm.")
        return False
    return True


def run_msm_tier(info, rf, outdir, policies, dry):
    banner("TIER A: test_msm proxy (BN254 G1 MSM under numactl matrix)")
    binp = os.path.join(ZKREG, "target/release/examples/test_msm")
    results = {}
    for pol in policies:
        pre = numa_prefix(pol, info)
        argv = pre + [binp]
        print("\n[msm:%s] %s  (%s)" % (pol, " ".join(argv), policy_note(pol, info)))
        if dry:
            continue
        r = subprocess.run(argv, cwd=ZKREG,
                           env=dict(os.environ, RUSTFLAGS=rf),
                           capture_output=True, text=True)
        with open(os.path.join(outdir, "msm_%s.log" % pol), "w") as f:
            f.write(r.stdout + "\n--stderr--\n" + r.stderr)
        parsed = {int(n): {"ms": float(ms), "norm": float(nm),
                           "per_thread": float(pt), "total": float(tt)}
                  for n, ms, nm, pt, tt in MSM_LINE.findall(r.stdout)}
        results[pol] = parsed
        if 8 in parsed:
            print("[msm:%s] N=8 msm=%.1fms  per-thread=%.2f GB/s  total=%.1f GB/s"
                  % (pol, parsed[8]["ms"], parsed[8]["per_thread"],
                     parsed[8]["total"]))
    return results


# ----------------------------------------------------------------------
# Tier B: capped full_dlp under numactl matrix
# ----------------------------------------------------------------------
# prover logs: "prove_step cost: i: .. circ_id: N .. stmt_len: S .. wtns size: W X ms"
STEP_RE = re.compile(
    r"circ_id: (\d+).*stmt_len: (\d+).*wtns size: (\d+) (\d+) ms")


def parse_steps(logpath):
    """Aggregate per-circuit fold steps: {circ: [count, sum_ms, stmt, wtns]}."""
    agg = {}
    for l in open(logpath, errors="replace"):
        if "prove_step cost: i:" not in l:
            continue
        m = STEP_RE.search(l)
        if not m:
            continue
        c = int(m.group(1))
        d = agg.setdefault(c, [0, 0, 0, 0])
        d[0] += 1
        d[1] += int(m.group(4))
        d[2] = int(m.group(2))
        d[3] = int(m.group(3))
    return agg


def effective_runcfg(runcfg_arg, jobs, reset, outdir, dry=False):
    name = runcfg_arg or "runcfg_full.json"
    path = name if os.path.isabs(name) else os.path.join(CFG_DIR, name)
    if dry:
        # resolve only; never load/write in dry-run (file may be absent here)
        if not os.path.isfile(path):
            print("[dry-run] note: runcfg %s not present on this box" % path)
        return path, {}
    if not os.path.isfile(path):
        sys.exit("ERROR: runcfg not found: %s" % path)
    rc = json.load(open(path))
    rc["num_jobs"] = jobs
    if reset:
        rc["reset"] = True
    eff = os.path.join(outdir, "runcfg_effective_j%d.json" % jobs)
    json.dump(rc, open(eff, "w"), indent=2)
    return eff, rc


def full_dlp_cmd(policy, info):
    return numa_prefix(policy, info) + [
        "cargo", "test", "-p", "zkregplus", "--release", "--",
        "zkp_driver::tests_zkp_driver::full_dlp", "--exact", "--nocapture"]


def full_dlp_env(eff, word_cap, policy, rf):
    env = dict(os.environ)
    env["RUSTFLAGS"] = rf
    env["ZKR_DLP_RUNCFG"] = eff
    env["ZKR_NUMA"] = "perjob" if policy == "perjob" else "off"
    env.setdefault("ZKR_DC_THREADS", "8")
    if word_cap > 0:
        env["ZKR_WORD_CAP_PER_JOB"] = str(word_cap)
    return env


def run_full_dlp(tag, policy, eff, word_cap, info, rf, outdir, dry):
    logp = os.path.join(outdir, "full_dlp_%s.log" % tag)
    cmd = full_dlp_cmd(policy, info)
    env = full_dlp_env(eff, word_cap, policy, rf)
    print("\n[dlp:%s] policy=%s cap=%s  (%s)" % (
        tag, policy, word_cap or "none", policy_note(policy, info)))
    print("[dlp:%s] %s" % (tag, " ".join(cmd)))
    if dry:
        return None
    t0 = time.time()
    with open(logp, "w") as lf:
        lf.write("# policy=%s cap=%s cmd=%s\n\n" % (
            policy, word_cap, " ".join(cmd)))
        lf.flush()
        p = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        for line in p.stdout:
            lf.write(line)
            lf.flush()
            if any(k in line for k in ("PROGRESS fold", "PERF WORKFLOW",
                                       "panicked", "PREFLIGHT", "Killed",
                                       "CapErr", "test result")):
                sys.stdout.write("    " + line)
        p.wait()
    wall = time.time() - t0
    agg = parse_steps(logp)
    # overall weighted avg per-step ms + dominant circuit (most total ms)
    tot_ms = sum(d[1] for d in agg.values())
    tot_n = sum(d[0] for d in agg.values())
    overall = tot_ms / tot_n if tot_n else 0.0
    dom = max(agg.items(), key=lambda kv: kv[1][1], default=(None, [0, 0, 0, 0]))
    dom_avg = dom[1][1] / dom[1][0] if dom[1][0] else 0.0
    print("[dlp:%s] wall=%.0fs steps=%d overall_avg=%.0fms/step  dom circ%s "
          "avg=%.0fms (n=%d)" % (tag, wall, tot_n, overall, dom[0],
                                 dom_avg, dom[1][0]))
    return {"wall": wall, "steps": tot_n, "overall_ms": overall,
            "dom_circ": dom[0], "dom_avg_ms": dom_avg, "agg": agg}


def run_dlp_tier(info, rf, outdir, policies, runcfg, jobs, word_cap,
                 skip_warm, dry):
    banner("TIER B: capped full_dlp (real folding path) under numactl matrix")
    eff, rc = effective_runcfg(runcfg, jobs, False, outdir, dry)
    print("runcfg=%s  num_jobs=%s  word_cap=%s  cache_dir=%s" % (
        eff, rc.get("num_jobs", jobs), word_cap, rc.get("cache_dir")))

    if not skip_warm:
        print("\n[warm] first full_dlp run builds the discharge/ladder cache")
        print("       (~0.5hr if cold; instant if already cached). All policy")
        print("       runs below reuse it. Use --skip-warm to skip.")
        run_full_dlp("warm", "socket", eff, word_cap, info, rf, outdir, dry)

    results = {}
    for pol in policies:
        results[pol] = run_full_dlp(pol, pol, eff, word_cap, info, rf,
                                    outdir, dry)
    return results


# ----------------------------------------------------------------------
# Tier B-stress: reproduce the placement x concurrency cliff directly
# ----------------------------------------------------------------------
def confined_policy(info):
    """Best-locality corner for THIS topology: 1 node on a 4+-node box, the
    first socket (half the nodes) on 2-3 nodes, and just 'off' on 1 node."""
    nn = info["nnodes"]
    if nn >= 4:
        return "local0"      # pin to node 0: sharpest locality
    if nn >= 2:
        return "socket"      # first half of the nodes
    return "off"


def run_stress_tier(info, rf, outdir, runcfg, jobs_confined, jobs_spread,
                    word_cap, dry):
    """Two contrasting corners (capped fold, per-step ms):
      confined : few jobs, fewest nodes, all-local  -> low-contention floor
      spread   : 2x jobs across ALL nodes           -> max-contention ceiling
    cliff = spread/confined per-step ms: how much the cross-node bandwidth +
    oversubscription tax costs when you light up the whole box. NOTE the two
    corners differ in core count too (confined uses one node's cpus), so the
    cliff blends NUMA + concurrency; the PURE per-node NUMA penalty at fixed
    cores is the Tier B local0-vs-remote pair. On 1 node the corners coincide."""
    nn = info["nnodes"]
    cpol = confined_policy(info)
    n0 = len(info["node_cpus"].get(0, [])) or info["total_cpus"]
    banner("TIER B-STRESS: confined (%s) vs spread (all %d node(s))" % (
        cpol, max(nn, 1)))
    if nn < 2:
        print("single NUMA node: confined and spread coincide; the cliff needs")
        print(">=2 nodes. Running both anyway for completeness.")
    eff_c, _ = effective_runcfg(runcfg, jobs_confined, False, outdir, dry)
    eff_s, _ = effective_runcfg(runcfg, jobs_spread, False, outdir, dry)
    print("confined: jobs=%d policy=%-9s (node 0, %d cpu, all-local floor)"
          % (jobs_confined, cpol, n0))
    print("spread  : jobs=%d policy=off       (all %d nodes, contention ceiling)"
          % (jobs_spread, nn))
    total_gb = sum(info["node_mem_mb"].values()) / 1024.0
    if total_gb and jobs_spread > info["total_cpus"] // 8:
        print("  RAM note: spread runs %d jobs; each allocates full per-job "
              "SRS/keys." % jobs_spread)
        print("            box has ~%.0f GB. If you hit OOM / PREFLIGHT ABORT,"
              % total_gb)
        print("            lower --stress-spread-jobs (or skip --stress here).")
    confined = run_full_dlp("stress_confined", cpol, eff_c, word_cap,
                            info, rf, outdir, dry)
    spread = run_full_dlp("stress_spread", "off", eff_s, word_cap,
                          info, rf, outdir, dry)
    if confined and spread and confined.get("dom_avg_ms"):
        ratio = spread["dom_avg_ms"] / confined["dom_avg_ms"]
        print("\n[stress] per-step fold ms  confined=%.0f  spread=%.0f  "
              "-> spread/confined = %.2fx" % (
                  confined["dom_avg_ms"], spread["dom_avg_ms"], ratio))
    return {"confined": confined, "spread": spread,
            "jobs_confined": jobs_confined, "jobs_spread": jobs_spread,
            "confined_policy": cpol, "nnodes": nn}


# ----------------------------------------------------------------------
# Tier C: perf c2c attribution on an UNcapped full_dlp
# ----------------------------------------------------------------------
def run_c2c_tier(info, rf, outdir, runcfg, jobs, window, dry):
    banner("TIER C: perf c2c attribution (uncapped full_dlp)")
    if not info["perf_c2c_ok"]:
        print("perf c2c needs paranoid<=0 or root. Enable with:")
        print("  sudo sysctl kernel.perf_event_paranoid=-1")
        print("Skipping Tier C.")
        return
    eff, _ = effective_runcfg(runcfg, jobs, False, outdir, dry)
    cmd = full_dlp_cmd("socket", info)
    env = full_dlp_env(eff, 0, "socket", rf)   # uncapped: real working set
    print("[c2c] launch: %s" % " ".join(cmd))
    if dry:
        return
    p = subprocess.Popen(cmd, cwd=REPO, env=env,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print("[c2c] pid=%d warming 60s before recording..." % p.pid)
    time.sleep(60)
    if p.poll() is not None:
        print("[c2c] prover exited early; nothing to record.")
        return
    if info["have_numastat"]:
        with open(os.path.join(outdir, "numastat_c2c.txt"), "w") as f:
            f.write(run(["numastat", "-p", str(p.pid)]).stdout)
    data = os.path.join(outdir, "perf_c2c.data")
    print("[c2c] perf c2c record -p %d for %ds..." % (p.pid, window))
    run(["perf", "c2c", "record", "-p", str(p.pid), "-o", data,
         "--", "sleep", str(window)])
    rep = run(["perf", "c2c", "report", "-NN", "--stdio", "-i", data])
    with open(os.path.join(outdir, "perf_c2c_report.txt"), "w") as f:
        f.write(rep.stdout + "\n" + rep.stderr)
    print("[c2c] report -> %s/perf_c2c_report.txt" % outdir)
    print("      Read 'Shared Data Cache Line Table': the top HITM line is the")
    print("      contended array. Expect veccom/pedersen SRS, NOT GLOBAL_CONFIG.")
    print("[c2c] prover still running (pid=%d); kill when done: kill %d"
          % (p.pid, p.pid))


# ----------------------------------------------------------------------
# verdict
# ----------------------------------------------------------------------
def verdict(info, msm, dlp, outdir):
    banner("VERDICT")
    out = []

    def emit(s):
        print(s)
        out.append(s)

    # Tier A: bandwidth saturation + cross-node penalty on the MSM kernel
    if msm:
        d = msm.get("off") or next(iter(msm.values()), None)
        if d and 1 in d and 8 in d:
            r = d[8]["per_thread"] / d[1]["per_thread"] if d[1]["per_thread"] else 0
            emit("[A msm] per-thread DRAM GB/s N=1->N=8: %.2f->%.2f (%.0f%% kept)"
                 % (d[1]["per_thread"], d[8]["per_thread"], 100 * r))
            if r < 0.6:
                emit("        => MEMORY-BANDWIDTH BOUND: more concurrency does")
                emit("           not speed MSM up. This is the regression core.")
        loc = msm.get("local0", {}).get(8)
        rem = msm.get("remote", {}).get(8)
        if loc and rem and loc["ms"]:
            emit("[A msm] MSM @N=8 local=%.1fms remote=%.1fms -> %.2fx remote "
                 "penalty" % (loc["ms"], rem["ms"], rem["ms"] / loc["ms"]))

    # Tier B: per-step fold ms across policies (the authoritative signal)
    valid = {k: v for k, v in (dlp or {}).items()
             if v and v.get("dom_avg_ms")}
    if valid:
        best = min(valid.values(), key=lambda v: v["dom_avg_ms"])
        bestk = [k for k, v in valid.items() if v is best][0]
        emit("[B dlp] dominant-circuit avg fold ms/step by policy "
             "(lower=better):")
        for k in sorted(valid, key=lambda k: valid[k]["dom_avg_ms"]):
            v = valid[k]
            rel = v["dom_avg_ms"] / best["dom_avg_ms"]
            emit("        %-11s %7.0f ms/step   %.2fx vs best (%s)"
                 % (k, v["dom_avg_ms"], rel, bestk))
        worst = max(valid.values(), key=lambda v: v["dom_avg_ms"])
        spread = worst["dom_avg_ms"] / best["dom_avg_ms"]
        emit("        spread best->worst = %.2fx" % spread)
        if spread >= 1.25:
            emit("        => NUMA / placement CONFIRMED on this box: policy")
            emit("           alone moves per-step fold cost %.2fx. Best policy" % spread)
            emit("           here is '%s'. This matches the team's jetstream" % bestk)
            emit("           measurement (socket ~0.89x baseline, both-sockets")
            emit("           ~2.5x). The 36/27 full_dlp slowdown is the same")
            emit("           cross-socket bandwidth effect -- run with the best")
            emit("           policy above; ArcSwap on GlobalConfig is irrelevant.")
        else:
            emit("        => policy spread small here; if this box is 1-node or")
            emit("           the cap is too low to reach the heavy circuit, the")
            emit("           NUMA effect may be understated. Raise --word-cap.")

    emit("")
    emit("Reference (team, jetstream2): socket-confined ~%.2fx baseline; "
         "both-sockets ~%.1fx." % (REF_SOCKET, REF_BOTH))
    emit("Raw logs: %s" % outdir)
    with open(os.path.join(outdir, "summary.txt"), "w") as f:
        f.write("\n".join(out) + "\n")


# ----------------------------------------------------------------------
# durable record + cross-run comparison
# ----------------------------------------------------------------------
def git_head():
    r = run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO)
    return r.stdout.strip() if r.returncode == 0 else "nogit"


def _step(v):
    """Pull the comparable per-step fields out of a run dict (or {})."""
    if not v:
        return {}
    return {"dom_avg_ms_per_step": v["dom_avg_ms"], "dom_circ": v["dom_circ"],
            "overall_ms_per_step": v["overall_ms"], "steps": v["steps"],
            "wall_s": v["wall"]}


def collect_metrics(info, msm, dlp, stress, label, word_cap, jobs):
    """Flatten the run into a JSON-able dict for results.json / --compare."""
    st = {}
    if stress:
        c = stress.get("confined")
        s = stress.get("spread")
        st = {"jobs_confined": stress.get("jobs_confined"),
              "jobs_spread": stress.get("jobs_spread"),
              "confined_policy": stress.get("confined_policy"),
              "confined": _step(c), "spread": _step(s),
              "ratio": (s["dom_avg_ms"] / c["dom_avg_ms"]
                        if c and s and c.get("dom_avg_ms") else None)}
    return {
        "stress": st,
        "label": label,
        "git": git_head(),
        "ts": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "host": platform.node(),
        "nnodes": info["nnodes"],
        "total_cpus": info["total_cpus"],
        "word_cap": word_cap,
        "jobs": jobs,
        "msm": {pol: ({"n8_ms": d[8]["ms"],
                       "n8_per_thread_gbps": d[8]["per_thread"],
                       "n8_total_gbps": d[8]["total"],
                       "n1_per_thread_gbps": d.get(1, {}).get("per_thread")}
                      if 8 in d else {})
                for pol, d in (msm or {}).items()},
        "dlp": {pol: ({"overall_ms_per_step": v["overall_ms"],
                       "dom_circ": v["dom_circ"],
                       "dom_avg_ms_per_step": v["dom_avg_ms"],
                       "steps": v["steps"], "wall_s": v["wall"]}
                      if v else {})
                for pol, v in (dlp or {}).items()},
    }


def write_results(metrics, outdir):
    path = os.path.join(outdir, "results.json")
    json.dump(metrics, open(path, "w"), indent=2)
    print("\n[record] results.json -> %s" % path)
    print("[record] label=%s git=%s  (compare later with: "
          "python3 numa_probe.py --compare <dir>...)"
          % (metrics["label"], metrics["git"]))
    return path


def pack_outdir(outdir):
    """Tar the whole results dir into /tmp for one-shot download (like
    run_full_dlp.py). Returns the tarball path."""
    tgz = os.path.join("/tmp", "numa_probe_%s.tgz" % os.path.basename(outdir))
    with tarfile.open(tgz, "w:gz") as t:
        t.add(outdir, arcname=os.path.basename(outdir))
    print("[pack] %s  <- download this (results.json + summary.txt + logs)"
          % tgz)
    return tgz


def load_results(p):
    """Accept a results.json path, or a dir containing one."""
    if os.path.isdir(p):
        p = os.path.join(p, "results.json")
    return json.load(open(p))


def do_compare(paths):
    """Print a side-by-side delta table across labeled runs. The first run is
    the baseline; later runs show x-vs-baseline per policy."""
    # expand dirs/globs
    expanded = []
    for p in paths:
        hits = glob.glob(p)
        expanded.extend(hits if hits else [p])
    runs = []
    for p in expanded:
        try:
            runs.append(load_results(p))
        except Exception as e:
            print("[compare] skip %s (%s)" % (p, e))
    if not runs:
        sys.exit("[compare] no results.json found in: %s" % ", ".join(paths))

    banner("COMPARE: %d runs" % len(runs))
    for i, r in enumerate(runs):
        tag = "BASE" if i == 0 else "  vs"
        print("  [%s] %-16s git=%-10s nodes=%s cap=%s jobs=%s  (%s)" % (
            tag, r.get("label"), r.get("git"), r.get("nnodes"),
            r.get("word_cap"), r.get("jobs"), r.get("ts")))

    # --- Tier B: per-step fold ms (dominant circuit), the key metric ---
    pols = []
    for r in runs:
        for pol in r.get("dlp", {}):
            if pol not in pols and r["dlp"][pol].get("dom_avg_ms_per_step"):
                pols.append(pol)
    if pols:
        print("\n-- full_dlp dominant-circuit fold ms/step "
              "(x = vs BASE same policy; lower better) --")
        hdr = "%-12s" % "policy" + "".join(
            "%18s" % (r.get("label") or ("run%d" % i))
            for i, r in enumerate(runs))
        print(hdr)
        for pol in pols:
            row = "%-12s" % pol
            base = runs[0].get("dlp", {}).get(pol, {}).get(
                "dom_avg_ms_per_step")
            for r in runs:
                v = r.get("dlp", {}).get(pol, {}).get("dom_avg_ms_per_step")
                if not v:
                    row += "%18s" % "-"
                elif base:
                    row += "%12.0f(%.2fx)" % (v, v / base)
                else:
                    row += "%18.0f" % v
            print(row)

    # --- Tier A: MSM N=8 ms ---
    mpols = []
    for r in runs:
        for pol in r.get("msm", {}):
            if pol not in mpols and r["msm"][pol].get("n8_ms"):
                mpols.append(pol)
    if mpols:
        print("\n-- test_msm N=8 MSM ms (x = vs BASE same policy) --")
        print("%-12s" % "policy" + "".join(
            "%18s" % (r.get("label") or ("run%d" % i))
            for i, r in enumerate(runs)))
        for pol in mpols:
            row = "%-12s" % pol
            base = runs[0].get("msm", {}).get(pol, {}).get("n8_ms")
            for r in runs:
                v = r.get("msm", {}).get(pol, {}).get("n8_ms")
                if not v:
                    row += "%18s" % "-"
                elif base:
                    row += "%12.1f(%.2fx)" % (v, v / base)
                else:
                    row += "%18.1f" % v
            print(row)
    # --- stress: confined vs spread per-step ms + the cliff ratio ---
    if any(r.get("stress", {}).get("ratio") for r in runs):
        print("\n-- stress: per-step fold ms (lower better) + spread/confined "
              "cliff --")
        print("%-16s%14s%14s%12s" % (
            "label", "confined", "spread", "cliff"))
        for r in runs:
            s = r.get("stress", {})
            c_ms = s.get("confined", {}).get("dom_avg_ms_per_step")
            s_ms = s.get("spread", {}).get("dom_avg_ms_per_step")
            ratio = s.get("ratio")
            print("%-16s%14s%14s%12s" % (
                r.get("label"),
                "%.0f" % c_ms if c_ms else "-",
                "%.0f" % s_ms if s_ms else "-",
                "%.2fx" % ratio if ratio else "-"))
        print("(cliff = spread/confined; a real fix SHRINKS it, ArcSwap "
              "should not.)")

    print("\n(BASE = first run. <1.00x = the change made that policy FASTER.)")


# ----------------------------------------------------------------------
# main
# ----------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--msm-only", action="store_true",
                    help="Tier A only (instant, no cache)")
    ap.add_argument("--skip-msm", action="store_true",
                    help="skip Tier A, run Tier B only")
    ap.add_argument("--skip-build", action="store_true",
                    help="reuse an already-built test_msm")
    ap.add_argument("--skip-warm", action="store_true",
                    help="full_dlp cache already warm; skip warmup run")
    ap.add_argument("--c2c", action="store_true",
                    help="also run Tier C perf c2c (uncapped, needs perf priv)")
    ap.add_argument("--stress", action="store_true",
                    help="add the confined-vs-spread cliff (jobs x placement)")
    ap.add_argument("--all", action="store_true",
                    help="Tier A + Tier B + stress (NOT c2c -- add --c2c)")
    ap.add_argument("--stress-spread-jobs", type=int, default=None,
                    help="job count for the spread corner (default 2x --jobs)")
    ap.add_argument("--runcfg", default=None,
                    help="full_dlp runcfg (default runcfg_full.json)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--word-cap", type=int, default=40,
                    help="ZKR_WORD_CAP_PER_JOB for the capped fold (0=full)")
    ap.add_argument("--window", type=int, default=45,
                    help="perf c2c sampling seconds (Tier C)")
    ap.add_argument("--policies", default=None,
                    help="comma list: off,socket,interleave,local0,remote,perjob")
    ap.add_argument("--rustflags", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--label", default="run",
                    help="tag for this run (e.g. baseline, arcswap, "
                         "replicate-keys); recorded in results.json")
    ap.add_argument("--compare", nargs="+", default=None,
                    help="compare prior runs: dirs/globs/paths to results.json; "
                         "first is the baseline. Runs nothing else.")
    args = ap.parse_args()

    if args.compare:
        do_compare(args.compare)
        return

    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    outdir = args.out or os.path.join(HIST_DIR, "%s_%s" % (ts, args.label))
    if not args.dry_run:
        os.makedirs(outdir, exist_ok=True)

    info = detect()
    print_env(info)
    if info.get("numactl_H") and not args.dry_run:
        with open(os.path.join(outdir, "numactl_H.txt"), "w") as f:
            f.write(info["numactl_H"])

    rf = rustflags(args.rustflags)
    policies = (args.policies.split(",") if args.policies
                else default_policies(info))

    do_stress = (args.stress or args.all) and not args.msm_only
    spread_jobs = args.stress_spread_jobs or (2 * args.jobs)

    banner("PLAN")
    print("label         : %s  (git %s)" % (args.label, git_head()))
    print("out dir       : %s" % outdir)
    print("policies      : %s" % ", ".join(policies))
    print("tier A msm    : %s" % ("skip" if args.skip_msm else "yes"))
    print("tier B dlp    : %s (cap=%d jobs=%d)" % (
        "no" if args.msm_only else "yes", args.word_cap, args.jobs))
    print("tier B stress : %s%s" % (
        "yes" if do_stress else "no",
        " (confined j%d vs spread j%d)" % (args.jobs, spread_jobs)
        if do_stress else ""))
    print("tier C c2c    : %s" % ("yes" if args.c2c else "no"))

    msm = {}
    if not args.skip_msm:
        if args.skip_build or build_test_msm(rf, args.dry_run):
            msm = run_msm_tier(info, rf, outdir, policies, args.dry_run)

    dlp = {}
    if not args.msm_only:
        dlp = run_dlp_tier(info, rf, outdir, policies, args.runcfg,
                           args.jobs, args.word_cap, args.skip_warm,
                           args.dry_run)

    stress = {}
    if do_stress:
        stress = run_stress_tier(info, rf, outdir, args.runcfg, args.jobs,
                                 spread_jobs, args.word_cap, args.dry_run)

    if args.c2c and not args.msm_only:
        run_c2c_tier(info, rf, outdir, args.runcfg, args.jobs,
                     args.window, args.dry_run)

    if not args.dry_run:
        verdict(info, msm, dlp, outdir)
        metrics = collect_metrics(info, msm, dlp, stress, args.label,
                                  args.word_cap, args.jobs)
        write_results(metrics, outdir)
        pack_outdir(outdir)
    else:
        print("\n[dry-run] nothing executed.")


if __name__ == "__main__":
    main()
