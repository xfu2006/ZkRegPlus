# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code.
# Purpose: DLP_T1001 same-sample Zombie run. Wraps run_zombie.py (unedited)
#          and proves the fixed FX e-mails with real witnesses on every unit
#          whose sweep base timed ok at a sample size, packed under per-key
#          gates, with resume, stop, scale calibration and a start check.
# -------------------------------------------

import os
import re
import sys
import errno
import json
import math
import time
import uuid
import shutil
import signal
import socket
import hashlib
import argparse
import statistics
import threading
import traceback
import subprocess
import warnings
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_zombie as rz  # noqa: E402
import dry_run_zombie as dz  # noqa: E402

# ALL_T1009: test-only redirect of every Zombie /tmp path (unset in real runs)
TMP_ROOT_ENV = "ZKR_ZOMBIE_TMP_ROOT"
TMP_ROOT = os.environ.get(TMP_ROOT_ENV)
if TMP_ROOT:
    TMP_ROOT = os.path.abspath(TMP_ROOT)
    rz.PARTIAL_DIR = os.path.join(TMP_ROOT, "run")
    rz.PARTIAL = os.path.join(rz.PARTIAL_DIR, "run_zombie.partial.jsonl")
    rz.BUILD_ROOT = os.path.join(TMP_ROOT, "circ")
    rz.CIRC_BUILD = os.path.join(rz.BUILD_ROOT, "circ")
    rz.BUILD_RS = os.path.join(rz.CIRC_BUILD, "src", "zkmb.rs")
    rz.BUILD_RS_ORIG = rz.BUILD_RS + ".orig"
    rz.ZKMB_DIR = os.path.join(rz.CIRC_BUILD, "zkmb")
    rz.KEYS_DIR = os.path.join(rz.CIRC_BUILD, "keys")
    rz.CIRC_BIN = os.path.join(rz.CIRC_BUILD, "target", "release",
                               "circ_executable")
    rz.PAR_ROOT = os.path.join(TMP_ROOT, "par")
    rz._pick_scratch_base = lambda: rz.PAR_ROOT

# --- paths (DLP_T1001: module globals so tests can redirect them) ----------
MS_DLP = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(os.path.dirname(MS_DLP)))
DOCS = os.path.join(MS_DLP, "docs")
FX_REL = "data/src_sig/ms_dlp/docs/zombie_bugs/emails/fixture"
FX = os.path.join(REPO, FX_REL)
RAW_DATA_ROOT = os.path.join(REPO, "data", "paper_data", "run_data", "data",
                             "raw_data")
ZOMBIE_TREE = os.path.join(MS_DLP, "zombie")
CLONE_SCRATCH = os.path.join(MS_DLP, "bora_zombie_scratch")  # ALL_T1013 K13
SELF_PATH = os.path.abspath(__file__)
RZ_PATH = os.path.abspath(rz.__file__)
LIST_TIMING = ["data/src_sig/ms_dlp/scripts/run_zombie.py",
               "data/src_sig/ms_dlp/scripts/download_zombie.py",
               "data/src_sig/ms_dlp/regex_zombie_international/",
               FX_REL + "/"]

# --- constants -------------------------------------------------------------
# DLP_T1001: copy of PAPER_DATA.FAIL_RE, pinned by the selftest
FAIL_LIKE = re.compile(
    r"panicked|SIGABRT|Killed|out of memory|cannot allocate|"
    r"CapErr|FATAL|error\[|VERIFICATION FAILED|SPLIT VERIFY: FAIL")
GIB = 2 ** 30
CAP_DEFAULT = 16           # DLP_T1001: gate widening cap, physical cores
SAMPLE_TIMEOUT_MIN = 600
SAMPLE_TIMEOUT_X = 10
AS_FACTOR = 4.0            # DLP_T1001: prlimit AS = cap x this [U, T3 measures]
K_SLACK = 1.25
GATE_D3 = 0.05             # DLP_T1001: d above this adds a 3rd serial replicate
GATE_TAU = 1.13            # DLP_T1001: gate PASS iff packed/serial g <= 1.13 (owner)
POLL_S = 0.1
WATCHDOG_S = 2.0
MEM_WAIT_LOG_S = 600       # DLP_T1001: idle memory-wait log interval
MEM_WAIT_MAX_S = 7200      # DLP_T1001: idle memory wait before a resource stop
LAUNCH_RETRIES = 3
LAUNCH_SWITCH = 3
TAIL_RESOURCE = 2
ALLOC_RE = re.compile(r"memory allocation of|Cannot allocate memory|"
                      r"os error 12|failed to spawn thread")
SDRUN_ERR_RE = re.compile(r"Failed to (start|connect|create|set|parse|find)|"
                          r"Unknown assignment|Transport endpoint|"
                          r"Access denied|Unit name .* is not valid")
VERIFY_RE = re.compile(r"zreal verify_ok (true|false)")
TSV_COLS = ["unit", "size", "email_id", "attempt", "mode", "accepted",
            "expected_reject", "width", "threads", "cpus", "node",
            "cons_bucket", "launcher", "launch_sig", "MemoryMax", "K_f",
            "concurrency", "MemAvailable", "wall_s", "utime_s", "stime_s",
            "maxrss_kB", "prove_ms", "verify_ms", "cons", "verify_ok", "rc",
            "sig", "Result", "class", "base_uuid", "gate_id"]
SCAL_COLS = ["w", "slots", "copies", "g", "s", "tau", "verdict", "w0",
             "overall", "kind", "commit", "dirty", "head_moved", "host",
             "fingerprint", "mode", "t_leaf_start", "rc",
             "zombie_inputs_sha256", "launch_sig"]

# DLP_T1001: the real-witness arm template (fn, then the arm line)
ARM_T = r'''// >>> same_zombie zreal arm (DLP_T1001, do not edit)
fn zreal_one_circuit<const N: usize>(circuit: &str) {
    println!("zreal start");
    let path = env::var("ZREAL_EMAIL").expect("ZREAL_EMAIL unset");
    let b = fs::read(&path).expect("read e-mail");
    if b.len() != N {
        println!("zreal length {} != {}", b.len(), N);
        std::process::exit(4);
    }
    let pw = RegexProverWitness::<N> { t: b.iter().map(|c| c.to_string()).collect(), tu: b.clone() };
    let vw = RegexVerifierWitness::<N> { t: b.iter().map(|c| c.to_string()).collect(), tu: b.clone() };
    let inst_path = CString::new(format!("./keys/{}_inst", circuit)).expect("failed").into_raw();
    let gens_path = CString::new(format!("./keys/{}_gens", circuit)).expect("failed").into_raw();
    let input_names_path = CString::new(format!("./keys/{}_input_names", circuit)).expect("failed").into_raw();
    let term_arr_path = CString::new(format!("./keys/{}_term_arr", circuit)).expect("failed").into_raw();
    let input_idxes_path = CString::new(format!("./keys/{}_input_idxes", circuit)).expect("failed").into_raw();
    let var_idxes_path = CString::new(format!("./keys/{}_var_idxes", circuit)).expect("failed").into_raw();
    let prover_p = zkmb_get_prover(inst_path, gens_path, term_arr_path, input_idxes_path, var_idxes_path);
    let prover = unsafe { &mut *prover_p };
    println!("{} circuit constraints cons {} inputs {} vars {}", circuit, prover.inst.inst.get_num_cons(), prover.inst.inst.get_num_inputs(), prover.inst.inst.get_num_vars());
    let timer = Instant::now();
    let proof = prover.prove(vec![pw]);
    println!("prove takes {}", timer.elapsed().as_millis());
    let data = bincode::serialize(&proof).unwrap();
    println!("proof size is {} bytes", data.len());
    if env::var("ZREAL_NO_VERIFY").is_ok() {
        println!("zreal verify_ok skipped");
        return;
    }
    // ALL_T1013 S1: verifier from the prover's loaded inst and gens (one load)
    let pb = unsafe { Box::from_raw(prover_p) };
    let SpartanProver { inst, gens, term_arr, input_idxes, var_idxes, val_arr } = *pb;
    drop((term_arr, input_idxes, var_idxes, val_arr));
    let verifier = SpartanVerifier::new(inst, gens, read_from_path(input_names_path));
    let verifier = &verifier;
    let timer = Instant::now();
    let ok = verifier.verify(&proof, &vec![vw]);
    println!("verify takes {}", timer.elapsed().as_millis());
    println!("zreal verify_ok {}", ok);
    if !ok {
        std::process::exit(3);
    }
}
// <<< same_zombie zreal arm
//@@ARM
        "policy_real_{n}" => zreal_one_circuit::<{n}>("policy{n}"),
        "policy_keys_{n}" => compile_one_circuit("policy{n}"),'''
ZK_ANCHOR = "fn zk_test() {\n"
ZREAL_BEGIN = "        // >>> same_zombie zreal arms (do not edit)"
ZREAL_END = "        // <<< same_zombie zreal arms"

# --- process state ---------------------------------------------------------
STOP = threading.Event()
ARGS = None
LOG_FH = None
_ORIG = {}
S = {}          # DLP_T1001: run state (see init_state)


# ===========================================================================
# output
# ===========================================================================
def say(msg, caveat=False):
    """The only print path. A FAIL_RE-like line gets the CAVEAT prefix."""
    lines = str(msg).splitlines() or [""]
    out = []
    for ln in lines:
        if caveat or FAIL_LIKE.search(ln):
            ln = "CAVEAT: " + ln
        out.append(ln)
    text = "\n".join(out) + "\n"
    try:
        sys.stdout.write(text)
        sys.stdout.flush()
    except (OSError, ValueError):
        pass
    if LOG_FH is not None:
        try:
            LOG_FH.write(text)
            LOG_FH.flush()
        except (OSError, ValueError):
            pass


def _stamp():
    return time.strftime("%m-%d %H:%M:%S")


def _rz_print(*a, **k):
    # DLP_T1001: RZ's own prints go through say()
    if k.get("file") not in (None, sys.stdout):
        return print(*a, **k)
    text, st = k.get("sep", " ").join(str(x) for x in a), _stamp()
    say("\n".join("[%s] %s" % (st, ln) if ln.strip() else ln
                   for ln in text.split("\n")))   # ALL_T1009: stamp lines


def _excepthook(t, v, tb):
    say("".join(traceback.format_exception(t, v, tb)), caveat=True)


def _thread_excepthook(a):
    if a.exc_type is SystemExit:
        return
    say("".join(traceback.format_exception(a.exc_type, a.exc_value,
                                           a.exc_traceback)), caveat=True)


def _showwarning(message, category, filename, lineno, file=None, line=None):
    say(warnings.formatwarning(message, category, filename, lineno, line),
        caveat=True)


def install_output_hooks():
    sys.excepthook = _excepthook
    threading.excepthook = _thread_excepthook
    warnings.showwarning = _showwarning
    rz.print = _rz_print


# ===========================================================================
# small helpers
# ===========================================================================
def up2(x):
    x = max(1, int(math.ceil(x)))
    return 1 << (x - 1).bit_length()


def down2(x):
    x = int(math.floor(x))
    if x < 1:
        return 1
    return 1 << (x.bit_length() - 1)


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def meminfo(key):
    try:
        with open("/proc/meminfo") as f:
            for ln in f:
                if ln.startswith(key + ":"):
                    return int(ln.split()[1]) * 1024
    except OSError:
        pass
    return 0


def memavail():
    return meminfo("MemAvailable")


def fingerprint():
    model = "unknown"
    try:
        with open("/proc/cpuinfo") as f:
            for ln in f:
                if ln.startswith("model name"):
                    model = ln.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    return "%s|%s|%d|%d" % (socket.gethostname(), model, os.cpu_count() or 0,
                            meminfo("MemTotal") // 1024 // 2 ** 20)


def git_version():
    try:
        out = subprocess.run(["git", "--version"], capture_output=True,
                             text=True, timeout=30).stdout
        return tuple(int(x) for x in re.findall(r"(\d+)\.(\d+)", out)[0])
    except (OSError, subprocess.TimeoutExpired, IndexError, ValueError):
        return (0, 0)


GIT_SAFE_OK = git_version() >= (2, 38)  # ALL_T1009: -c safe.directory needs it


def git_safe_args():
    return ["-c", "safe.directory=" + REPO] if GIT_SAFE_OK else []


def git(*a):
    try:
        r = subprocess.run(["git"] + git_safe_args() + ["-C", REPO] + list(a),
                           capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return r


def git_head():
    r = git("rev-parse", "HEAD")
    return r.stdout.strip() if r is not None and r.returncode == 0 else None


def git_status(paths):
    r = git("status", "--porcelain", "--untracked-files=all", "--", *paths)
    if r is None or r.returncode != 0:
        return None
    return r.stdout.strip()


def zombie_inputs_sha256():
    """sha256 over sorted (path, content) of zombie/circ and zombie/regex."""
    if "zin" in S:
        return S["zin"]
    items = []
    for sub in ("circ", "regex"):
        root = os.path.join(ZOMBIE_TREE, sub)
        for dp, dns, fns in os.walk(root):
            # DLP_T1001: skip only the top-level build dir and .git (src/target is source)
            dns[:] = sorted(d for d in dns if not (
                dp == root and d in ("target", ".git")))
            for fn in fns:
                if fn.endswith(".o"):
                    continue
                items.append(os.path.relpath(os.path.join(dp, fn), ZOMBIE_TREE))
    h = hashlib.sha256()
    for rel in sorted(items):
        p = os.path.join(ZOMBIE_TREE, rel)
        h.update(rel.encode() + b"\0")
        if os.path.islink(p):
            h.update(b"L" + os.readlink(p).encode())
        else:
            h.update(b"F" + bytes.fromhex(sha256_file(p)))
    S["zin"] = h.hexdigest()
    return S["zin"]


def launch_sig(tpc, a):
    """DLP_T1001 R1: sha256 of same_zombie.py, run_zombie.py, inputs, knobs."""
    h = hashlib.sha256()
    for p in (SELF_PATH, RZ_PATH):
        with open(p, "rb") as f:
            h.update(f.read())
        h.update(b"\0")
    h.update(zombie_inputs_sha256().encode())
    h.update(("|%d|%d|%d|%d|%s" % (tpc, a.keep_free, a.slot_cores,
                                   a.reserve_floor, a.launcher)).encode())
    return h.hexdigest()


# ===========================================================================
# fixture
# ===========================================================================
def read_ids():
    rows = []
    with open(os.path.join(FX, "ids.tsv")) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for ln in f:
            if ln.strip():
                rows.append(dict(zip(hdr, ln.rstrip("\n").split("\t"))))
    return rows


def read_expected_reject():
    p = os.path.join(FX, "zombie_expected_reject.tsv")
    out = set()
    with open(p) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for ln in f:
            if ln.strip():
                d = dict(zip(hdr, ln.rstrip("\n").split("\t")))
                out.add((d["unit"], d["email_id"], int(d["size"])))
    return out


def sample_emails(size, n):
    rows = sorted((r for r in read_ids() if int(r["arm"]) == size),
                  key=lambda r: r["id"])[:n]
    return [(r["id"], os.path.join(FX, "emails", "padded", r["id"] + ".eml"),
             r["sha256_padded"]) for r in rows]


def fx_check(sizes, n):
    """Every used e-mail: n per size, length == arm, sha256 == col 6."""
    for size in sizes:
        em = sample_emails(size, n)
        if len(em) != n:
            return "FX has %d e-mails at %d, need %d" % (len(em), size, n)
        for eid, p, sha in em:
            if not os.path.isfile(p) or os.path.getsize(p) != size:
                return "FX e-mail %s missing or not %d bytes" % (eid, size)
            if sha256_file(p) != sha:
                return "FX e-mail %s sha256 differs from ids.tsv" % eid
    return None


# ===========================================================================
# topology
# ===========================================================================
def _read(p, default=""):
    try:
        with open(p) as f:
            return f.read().strip()
    except OSError:
        return default


def _cpulist(s):
    out = []
    for part in s.split(","):
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-")
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return out


def topology(keep_free):
    """Nodes -> slot cores (each core = its logical cpus) after keep-free."""
    aff = sorted(os.sched_getaffinity(0))
    node_of = {}
    base = "/sys/devices/system/node"
    if os.path.isdir(base):
        for nd in sorted(os.listdir(base)):
            if re.match(r"node\d+$", nd):
                for c in _cpulist(_read(os.path.join(base, nd, "cpulist"))):
                    node_of[c] = int(nd[4:])
    cores = {}
    for c in aff:
        t = "/sys/devices/system/cpu/cpu%d/topology/" % c
        key = (_read(t + "physical_package_id", "0"), _read(t + "core_id",
                                                             str(c)))
        cores.setdefault((node_of.get(c, 0), key), []).append(c)
    nodes = {}
    for (nd, _), cpus in cores.items():
        nodes.setdefault(nd, []).append(sorted(cpus))
    return topo_from(nodes, keep_free)


def topo_from(nodes, keep_free):
    """Slot cores per node after spreading keep-free (m6)."""
    nodes = {nd: sorted(cs) for nd, cs in nodes.items()}
    tpc = max(len(c) for cs in nodes.values() for c in cs)
    order = sorted(nodes)
    keep = {nd: keep_free // len(order) for nd in order}
    for nd in order[:keep_free % len(order)]:
        keep[nd] += 1
    slot_cores = {nd: nodes[nd][keep[nd]:] for nd in order}
    return {"nodes": slot_cores, "tpc": tpc,
            "c_cores": sum(len(v) for v in slot_cores.values())}


def node_slot_cores(topo):
    return max([len(v) for v in topo["nodes"].values()] or [1])


def make_slots(topo, w):
    """Slots of w whole cores inside one node, dealt round robin per node."""
    per = {}
    for nd, cs in topo["nodes"].items():
        per[nd] = [(nd, sum(cs[i:i + w], [])) for i in range(0, len(cs) - w + 1,
                                                             w)]
    out = []
    while any(per.values()):
        for nd in sorted(per):
            if per[nd]:
                out.append(per[nd].pop(0))
    return out


def cpus_str(cpus):
    return ",".join(str(c) for c in cpus)


# ===========================================================================
# partial pairs (R2)
# ===========================================================================
def _ends_nl(p):
    """ALL_T1013 FI1: the file's last byte is a newline (or it is empty)."""
    try:
        with open(p, "rb") as f:
            f.seek(-1, os.SEEK_END)
            return f.read(1) == b"\n"
    except OSError:
        return True


class Pair(object):
    """A partial: /tmp primary plus docs mirror, appended in lockstep."""

    def __init__(self, tmp, docs):
        self.tmp, self.docs = tmp, docs

    @staticmethod
    def _nonempty(p):
        return os.path.isfile(p) and os.path.getsize(p) > 0

    def present(self, hold=False):
        """Either copy non-empty; hold=True also counts P's .hold park."""
        ps = (self.tmp, self.docs)
        if hold:
            ps += (self.tmp + ".hold", self.docs + ".hold")
        return any(self._nonempty(p) for p in ps)

    def src(self):
        return self.tmp if self._nonempty(self.tmp) else self.docs

    def load(self):
        """Rows of the preferred copy; a torn last line is skipped. ALL_T1013
        FI1: a bad middle line is skipped and counted when the other copy is
        there to vouch for the rest (a short write tears only one copy)."""
        src, rows, bad = self.src(), [], 0
        other = self.docs if src == self.tmp else self.tmp
        if os.path.isfile(src):
            with open(src) as f:
                lines = [ln for ln in f if ln.strip()]
            for i, ln in enumerate(lines):
                try:
                    rows.append(json.loads(ln))
                except ValueError:
                    if i == len(lines) - 1:
                        say("SAME note: torn last line in %s skipped" % src)
                    elif other != src and self._nonempty(other):
                        bad += 1
                    else:
                        raise
        if bad:
            say("SAME note: %d bad middle line(s) in %s skipped" % (bad, src))
        return rows

    @staticmethod
    def _valid_rows(p):
        """ALL_T1013 FI5: parseable rows of one copy (0 when absent)."""
        n = 0
        try:
            with open(p) as f:
                for ln in f:
                    try:
                        json.loads(ln)
                        n += 1
                    except ValueError:
                        pass
        except OSError:
            pass
        return n

    def repair_tail(self):
        """Drop unparsable lines from both copies before any append: a torn
        last line, and (ALL_T1013 F11) any torn line in the middle. The unit
        of a dropped row is redone (V12)."""
        for p in (self.tmp, self.docs):
            if not self._nonempty(p):
                continue
            with open(p) as f:
                text = f.read()
            lines = text.splitlines(True)
            while lines and not lines[-1].strip():
                lines.pop()
            if not lines:                     # whitespace only: nothing to do
                continue
            bad = []
            for i, ln in enumerate(lines):
                if not ln.strip():
                    continue
                try:
                    json.loads(ln)
                except ValueError:
                    bad.append(i)
            if not bad:
                if not text.endswith("\n"):   # cut before the newline
                    with open(p, "a") as f:
                        f.write("\n")
                    say("SAME note: newline restored at the end of %s" % p)
                continue
            keep = [ln if ln.endswith("\n") else ln + "\n"
                    for i, ln in enumerate(lines) if i not in bad]
            with open(p + ".repair", "w") as f:
                f.writelines(keep)
            os.replace(p + ".repair", p)
            for i in bad:
                redo_from_line(lines[i])
            if bad == [len(lines) - 1]:
                say("SAME note: torn last line removed from %s" % p)
            else:
                say("SAME note: %d unparsable line(s) removed from %s (lines "
                    "%s)" % (len(bad), p, ",".join(str(i + 1) for i in bad)))

    def restore(self):
        """Copy docs to /tmp when /tmp is absent or empty (reboot), or
        (ALL_T1013 FI5) when docs holds more valid rows than /tmp."""
        if self._nonempty(self.docs) and (
                not self._nonempty(self.tmp) or self._valid_rows(self.docs)
                > self._valid_rows(self.tmp)):
            os.makedirs(os.path.dirname(self.tmp), exist_ok=True)
            shutil.copyfile(self.docs, self.tmp + ".restore")
            os.replace(self.tmp + ".restore", self.tmp)
            say("SAME restored %s from %s" % (self.tmp, self.docs))

    def append(self, rows):
        if STOP.is_set():
            return
        text = "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows)
        for p in (self.tmp, self.docs):
            os.makedirs(os.path.dirname(os.path.abspath(p)), exist_ok=True)
            with open(p, "a") as f:
                if f.tell() and not _ends_nl(p):  # ALL_T1013 FI1: no merge
                    f.write("\n")                 # into a torn fragment
                f.write(text)

    def delete(self):
        for p in (self.tmp, self.docs):
            if os.path.exists(p):
                os.remove(p)


_REDO_U = re.compile(r'"(?:unit|regex_name)": "((?:[^"\\]|\\.)*)"')
_REDO_S = re.compile(r'"(?:size|str_len)": (\d+)')


def redo_from_line(ln):
    """ALL_T1013 V12: a dropped row that names its unit and size makes that
    unit redo the size (keygen, base, sample)."""
    u, s = _REDO_U.search(ln), _REDO_S.search(ln)
    if u and s:
        S.setdefault("force_redo", set()).add((u.group(1), int(s.group(1))))
    else:
        say("SAME note: a dropped partial line names no unit and size")


def ruleset():
    return rz.RULESETS[0]


def pair_names(a):
    """(RZ sweep pair or None for the default, sample pair)."""
    dry = "_dry" if a.dry is not None else ""
    tdir = rz.PARTIAL_DIR
    if a.only_same:
        rzn = "same_only_%s%s.partial.jsonl" % (a.server, dry)
        smn = "same_zombie_only_%s%s.partial.jsonl" % (a.server, dry)
        sweep = Pair(os.path.join(tdir, rzn), os.path.join(DOCS, rzn))
    else:
        rzn = "run_zombie_%s.partial.jsonl" % ruleset()
        smn = "same_zombie_%s%s.partial.jsonl" % (ruleset(), dry)
        sweep = Pair(os.path.join(tdir, rzn), os.path.join(DOCS, rzn))
    return sweep, Pair(os.path.join(tdir, smn), os.path.join(DOCS, smn))


def out_paths():
    """Docs TSV and log; dry wears .dry before the suffix (DLP_T1001)."""
    rs = ruleset()
    dry = ".dry" if ARGS is not None and ARGS.dry is not None else ""
    return (os.path.join(DOCS, "same_zombie_%s%s.tsv" % (rs, dry)),
            os.path.join(DOCS, "same_zombie_%s%s.log" % (rs, dry)))


# ===========================================================================
# rows, acceptance, resume rules
# ===========================================================================
def stamp():
    return {"ids_sha": S["ids_sha"], "list_sha": S["list_sha"],
            "zok_gen": rz.ZOK_GEN, "fp": S["fp"], "commit": S["commit"],
            "launch_sig": S["sig"]}


def put(kind, **kw):
    r = stamp()
    r.update(kw)
    r["kind"] = kind
    r["t"] = round(time.time(), 3)
    if S.get("in_scal"):
        r["scal"] = 1                         # kept out of the sample TSV
    S["rows"].append(r)
    S["pair"].append([r])
    return r


def gate_key(r):
    return (r.get("size"), r.get("width"), r.get("cons_bucket"),
            r.get("launcher"), r.get("launch_sig"))


def index_rows(rows):
    """Latest base_uuid per (unit, size) and gate rows by id."""
    base, gates = {}, {}
    for r in rows:
        if r["kind"] == "base":
            base[(r["unit"], r["size"])] = r["base_uuid"]
        elif r["kind"] == "gate":
            gates[r["gate_id"]] = r
    return base, gates


def is_accepted(r, base, gates):
    if r.get("kind") != "prove" or r.get("expected_reject"):
        return False
    if r.get("class") != "ok":
        return False
    if base.get((r["unit"], r["size"])) != r.get("base_uuid"):
        return False
    if r.get("mode") in ("tail", "serial"):
        return True
    if r.get("mode") != "packed":
        return False
    g = gates.get(r.get("gate_id"))
    return bool(g and g.get("verdict") == "pass" and gate_key(g) == gate_key(r)
                and g.get("K_gate", 0) >= r.get("K_f", 0))


def complete_units(rows, size, n, er):
    """Units whose every unlisted e-mail of size has an accepted row."""
    base, gates = index_rows(rows)
    need = [e[0] for e in sample_emails(size, n)]
    got = {}
    for r in rows:
        if r.get("size") == size and is_accepted(r, base, gates):
            got.setdefault(r["unit"], set()).add(r["email_id"])
    out = set()
    for (u, sz) in base:
        if sz != size:
            continue
        want = {e for e in need if (u, e, size) not in er}
        if want <= got.get(u, set()):
            out.add(u)
    return out


def check_rule1(rows, pair):
    for r in rows:
        bad = [k for k, v in (("ids_sha", S["ids_sha"]),
                              ("list_sha", S["list_sha"]),
                              ("zok_gen", rz.ZOK_GEN)) if r.get(k) != v]
        if bad:
            say("SAME abort: %s holds rows with another %s; delete %s and %s "
                "to re-measure." % (pair.src(), "/".join(bad), pair.tmp,
                                    pair.docs))
            raise SystemExit(6)


def state_from_rows(rows, sig, fp):
    """w_state, pass gates, STOP rows under the current launch_sig (rule 4)."""
    w_state, gates, stops = {}, {}, {}
    last = {}
    for r in rows:
        if r.get("launch_sig") != sig:
            continue
        sz = r.get("size")
        if r["kind"] == "width":
            w_state[sz] = max(w_state.get(sz, 0), r["width"])
        elif r["kind"] == "gate" and r.get("fp") == fp:
            if r.get("verdict") == "pass":
                gates.setdefault(gate_key(r), []).append(r)
                last[sz] = ("pass", r)
        elif r["kind"] == "stop":
            last[sz] = ("stop", r)
    for sz, (k, r) in last.items():
        if k == "stop":
            stops[sz] = r
    return w_state, gates, stops


def rule2(sweep, sample):
    """Amended rule 2: both sweep copies absent and the sample present."""
    return not sweep.present(hold=True) and sample.present()


def load_sample(a):
    """Read-only load of the sample rows, rule 2 applied as 'ignored'."""
    sweep, sample = pair_names(a)
    if rule2(sweep, sample):
        say("SAME sweep partial absent, sample partial ignored (rule 2)")
        return []
    rows = sample.load()
    check_rule1(rows, sample)
    return rows


# ===========================================================================
# stamps (zombie_timing)
# ===========================================================================
def scalecal_name(dry):
    return "same_zombie_scalecal%s.tsv" % (".dry" if dry else "")


def scalecal_path(server, dry=False):
    return os.path.join(RAW_DATA_ROOT, server, scalecal_name(dry))


def read_scalecal(server, dry=False):
    p = scalecal_path(server, dry)
    if not os.path.isfile(p):
        return None
    with open(p) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        rows = [dict(zip(hdr, ln.rstrip("\n").split("\t"))) for ln in f
                if ln.strip()]
    return rows[0] if rows else None


def valid_timing(st):
    """valid(stamp, 'zombie_timing'): (ok, reason)."""
    if st is None:
        return False, "no scalecal stamp"
    if st.get("kind") != "zombie_timing":
        return False, "stamp kind %s" % st.get("kind")
    if st.get("host") != socket.gethostname() or st.get("fingerprint") != S["fp"]:
        return False, "stamp from another host or fingerprint"
    if st.get("dirty") != "false":
        return False, "stamp tree was dirty"
    if st.get("head_moved") != "false":
        return False, "HEAD moved during the scalecal"
    c = st.get("commit") or ""
    r = git("merge-base", "--is-ancestor", c, "HEAD")
    if not c or r is None or r.returncode != 0:
        return False, "stamp commit %s is not an ancestor of HEAD" % c[:12]
    r = git("diff", "--name-only", c, "HEAD", "--", *LIST_TIMING)
    if r is None or r.returncode != 0 or r.stdout.strip():
        return False, "committed change since the stamp: %s" % (
            (r.stdout.split() if r is not None else ["git failed"])[:5])
    stt = git_status(LIST_TIMING)
    if stt is None or stt:
        return False, "uncommitted change under the timing list: %s" % (
            (stt or "git failed").split("\n")[:5])
    if st.get("zombie_inputs_sha256") != zombie_inputs_sha256():
        return False, "zombie inputs hash changed"
    if st.get("launch_sig") != S["sig"]:
        return False, "launch_sig changed"
    if st.get("overall") != "PASS":
        return False, "scalecal verdict %s" % st.get("overall")
    return True, None


def best_scalecal(server):
    """Full-run record first, then the dry one: (stamp, ok, reason)."""
    first = None
    for dry in (False, True):
        st = read_scalecal(server, dry)
        ok, why = valid_timing(st)
        if ok:
            return st, ok, why
        if first is None or (first[0] is None and st is not None):
            first = (st, ok, why)
    return first


def print_stamp_view(c):
    r = git("diff", "--stat", c)
    say("SAME stamp commit %s; diff --stat:\n%s" % (
        c[:12], r.stdout.rstrip() if r is not None else "(git failed)"))
    say("SAME status: %s" % (git_status(LIST_TIMING) or "(clean)"))


# ===========================================================================
# start check (full mode)
# ===========================================================================
def start_check(a, rows, pending=False):
    """Per-size start check plus the STOP-row rule. Returns refusal or None
    and sets S['w_state'] / S['serial']. pending: the full run will run the
    speed check itself, so a missing PASS decides nothing yet (DLP_T1001)."""
    cap = S["cap"]
    sig, fp = S["sig"], S["fp"]
    w_state, gates, stops = state_from_rows(rows, sig, fp)
    S["w_state"] = dict(w_state)
    S["serial"] = set()
    S["refused"], S["refused_prior"] = {}, set()
    st, sc_ok, sc_why = best_scalecal(a.server)
    if st is not None:
        print_stamp_view(st.get("commit") or "HEAD")
    sc_w0 = int(st["w0"]) if sc_ok and st.get("w0", "").isdigit() else None
    enforce = S["topo"]["c_cores"] >= a.start_check_min_cores
    if not enforce:
        say("SAME start check skipped C_cores=%d" % S["topo"]["c_cores"])
    for size in a.sizes:
        gw = [k[1] for k in gates if k[0] == size]
        w0 = max([sc_w0 or 0] + gw) or None
        valid_pass = sc_w0 is not None or bool(gw)
        if enforce and not valid_pass and pending:
            say("SAME start check %d: no valid PASS yet (%s); the full run "
                "runs the speed check first" % (size, sc_why))
        elif enforce:
            if not valid_pass and size == 1000:
                S["serial"].add(1000)
                say("SERIAL MODE 1 KB from the start: no valid PASS (%s)"
                    % sc_why)
            elif not valid_pass and cap != 0:
                why = ("the full run already tried the speed check "
                       "(SCALECAL)" if S.get("scal_tried") else
                       "the speed check needs C_cores >= %d"
                       % a.scalecal_min_cores)
                S["refused"][size] = (
                    "no valid PASS for %d (%s); %s. Set "
                    "ZKR_SAME_MAX_WIDTH_CORES=0 to allow serial mode"
                    % (size, sc_why, why))
            elif valid_pass:
                S["w_state"][size] = max(S["w_state"].get(size, 0), w0)
        stop = stops.get(size)
        if stop is not None:
            cause = stop.get("cause")
            if cause in ("error", "mem", "ref") and sum(  # ALL_T1013: once
                    1 for r in rows if r.get("kind") == "stop"
                    and r.get("size") == size and r.get("cause") == cause
                    and (cause != "error" or stop_etype(r) == stop_etype(stop))
                    and r.get("launch_sig") == sig) < 2:
                say("SAME STOP row at %d lifted: %s (%s)" % (
                    size, "an error stop is retried once per exception type"
                    if cause == "error" else "a %s stop is retried once" % (
                        "memory" if cause == "mem" else "gate reference"),
                    stop.get("reason")))
            elif size == 1000 or cap == 0:
                S["serial"].add(size)
                say("SAME STOP row at %d: serial mode for %d" % (size, size))
            elif cap > stop.get("cap", 0):
                L = ladder(S["topo"], cap)            # ALL_T1013 S5
                S["w_state"][size] = max(S["w_state"].get(size, 0),
                                         next_rung(L, stop.get("width", 1))
                                         or L[-1])
                say("SAME STOP row at %d: cap raised, re-gate at %d cores"
                    % (size, S["w_state"][size]))
            elif stop.get("cause") == "nopass" and valid_pass:
                say("SAME STOP row at %d lifted: a valid PASS exists now"
                    % size)
            else:                             # gate, nopass, mem: size only
                S["refused"].setdefault(size, "earlier STOP kept (cap "
                                        "unchanged): %s" % stop.get("reason"))
                S["refused_prior"].add(size)
    return None


def stop_etype(r):
    """Exception type of an error STOP row (older rows: from the reason)."""
    if r.get("etype"):
        return r["etype"]
    m = re.match(r"exception in flush: (\w+):", r.get("reason") or "")
    return m.group(1) if m else ""


# ===========================================================================
# launcher, probes, preflight (6a)
# ===========================================================================
def plog(name):
    return os.path.join(S["logdir"], name)


def run_logged(cmd, name, timeout=60, **kw):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout, **kw)
    except (OSError, subprocess.TimeoutExpired) as e:
        with open(plog(name), "a") as f:
            f.write("$ %s\n%s\n" % (" ".join(cmd), e))
        return None
    with open(plog(name), "a") as f:
        f.write("$ %s\nrc=%d\n%s%s\n" % (" ".join(cmd), r.returncode,
                                          r.stdout, r.stderr))
    return r


def sctl(*a, **kw):
    return run_logged(["systemctl", "--user"] + list(a), "probes.log", **kw)


def unit_cgroup(unit):
    r = sctl("show", "-p", "ControlGroup", "--value", unit)
    if r is None or r.returncode != 0 or not r.stdout.strip():
        return None
    return "/sys/fs/cgroup" + r.stdout.strip()


def has_omit(cg):
    try:
        os.getxattr(cg, "user.oomd_omit")
        return True
    except OSError:
        return False


def _run_ro(cmd):
    """Unlogged read-only command (no S['logdir'] needed)."""
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None


def oomd_active(log=True):
    cmd = ["systemctl", "is-active", "systemd-oomd"]
    r = run_logged(cmd, "probes.log") if log else _run_ro(cmd)
    return r is not None and r.stdout.strip() == "active"


def oomd_paths(log=True):
    r = run_logged(["oomctl"], "probes.log") if log else _run_ro(["oomctl"])
    if r is None or r.returncode != 0:
        return []
    out, on = [], False
    for ln in r.stdout.splitlines():
        if not ln.startswith("\t") and not ln.startswith(" "):
            on = ln.strip().startswith("Memory Pressure Monitored CGroups")
            continue
        m = re.match(r"\s+Path: (\S+)", ln)
        if on and m:
            out.append(m.group(1))
    return out


def probe_scope(extra, props, cmd, tag):
    """Probe scope in bora-same.slice with extra + props; returns (proc,
    unit, accepted props). extra (the probe's MemoryMax) is never returned."""
    unit = "same-probe-%s-%d-%d" % (tag, os.getpid(), int(time.time()))
    while True:
        full = (["systemd-run", "--user", "--scope", "--quiet",
                 "--unit=" + unit, "--slice=bora-same.slice"] +
                sum((["-p", p] for p in extra + props), []) + ["--"] + cmd)
        with open(plog("probes.log"), "a") as f:
            f.write("$ %s\n" % " ".join(full))
        with open(plog("probe_%s.out" % tag), "w") as f:
            p = subprocess.Popen(full, stdout=f, stderr=subprocess.PIPE,
                                 text=True)
        time.sleep(0.5)
        if p.poll() is not None and p.returncode != 0:
            err = p.stderr.read()
            with open(plog("probes.log"), "a") as f:
                f.write(err)
            bad = [q for q in props if q.split("=")[0] in err]
            if bad and SDRUN_ERR_RE.search(err):
                props = [q for q in props if q not in bad]
                say("SAME probe %s: property %s rejected, re-run without it"
                    % (tag, bad[0].split("=")[0]))
                unit += "r"
                continue
        return p, unit, props


OUTER_SCOPE = ("Outer-scope requirement: when systemd-oomd monitors memory "
               "pressure on an ancestor of the cgroup PAPER_DATA.py runs in "
               "(on Ubuntu, user@<uid>.service), that cgroup must carry "
               "user.oomd_omit, because keygens run inside it. Launch with: "
               "systemd-run --user --scope -p ManagedOOMPreference=omit "
               "[-p MemoryMax=...] python3 scripts/PAPER_DATA.py ...")


def oomd_check(repair=True):
    """6a step 7 on our own cgroup; refusal text or None (DLP_T1001 fix6).
    repair=False is read only: no set-property, no log, no S['logdir']."""
    if not oomd_active(log=repair):
        return None
    mine = _read("/proc/self/cgroup").split("::", 1)[-1].strip()
    for path in oomd_paths(log=repair):
        if not mine.startswith(path.rstrip("/") + "/"):
            continue
        cg = "/sys/fs/cgroup" + mine
        if repair and not has_omit(cg):
            sctl("set-property", "--runtime", os.path.basename(mine),
                 "ManagedOOMPreference=omit")
        if not has_omit(cg):
            return ("our cgroup %s is pressure-monitored by oomd (%s) without "
                    "user.oomd_omit. %s" % (mine, path, OUTER_SCOPE))
    return None


def preflight():
    """6a: oomd check (refuses), then steps 1-6 (launcher, props, note)."""
    why = oomd_check()
    if why:
        say("SAME refuse: %s" % why)
        raise SystemExit(6)
    return launcher_probe()


def launcher_probe():
    """6a steps 1-6. Returns (launcher, props, note)."""
    st = {}
    try:
        return _launcher_probe(st)
    finally:
        if st.get("slice"):                   # ALL_T1009: never leave it capped
            sctl("set-property", "--runtime", "bora-same.slice",
                 "MemoryMax=infinity")


def _launcher_probe(st):
    uid = os.getuid()
    props = ["MemorySwapMax=0", "OOMPolicy=kill", "ManagedOOMPreference=omit"]
    r = sctl("show", "-p", "Version")
    if r is None or r.returncode != 0:
        return "prlimit", props, "systemctl --user unavailable"
    r = run_logged(["loginctl", "show-user", str(uid), "-p", "Linger"],
                   "probes.log")
    if r is None or "Linger=yes" not in r.stdout:
        return "prlimit", props, "linger off"
    ub = "/sys/fs/cgroup/user.slice/user-%d.slice/user@%d.service/" % (uid, uid)
    if ("memory" not in _read(ub + "cgroup.controllers").split()
            or "memory" not in _read(ub + "cgroup.subtree_control").split()):
        return "prlimit", props, "memory controller not delegated"
    oomd = oomd_active()
    # probe A: properties read back, slice live set-property
    # DLP_T1001 fix1: the probe MemoryMax stays out of the prove props
    p, unit, props = probe_scope(["MemoryMax=64M"], props, ["sleep", "20"],
                                 "a")
    try:
        if p.poll() is not None:
            return "prlimit", props, "probe A scope did not start"
        r = sctl("show", "-p", "MemoryMax", "-p", "MemorySwapMax", unit +
                 ".scope")
        txt = r.stdout if r is not None else ""
        if ("MemoryMax=67108864" not in txt
                or ("MemorySwapMax=0" not in txt
                    and "MemorySwapMax=0" in props)):
            return "prlimit", props, "probe A read-back failed"
        cg = unit_cgroup(unit + ".scope")
        if oomd and "ManagedOOMPreference=omit" in props and (
                cg is None or not has_omit(cg)):
            return "prlimit", props, "probe A: no user.oomd_omit"
        st["slice"] = True                    # ALL_T1009: restore in finally
        sctl("set-property", "--runtime", "bora-same.slice",
             "MemoryMax=1073741824")
        scg = unit_cgroup("bora-same.slice")
        if scg is None or _read(scg + "/memory.max") != "1073741824":
            return "prlimit", props, "probe A: slice live set-property failed"
    finally:
        _kill_quiet(p)
    # probe B: oom-kill seen as rc -9 and Result oom-kill
    touch = [sys.executable, "-c", "b=bytearray(128<<20)\n"
             "for i in range(0,len(b),4096): b[i]=1\nimport time; time.sleep(5)"]
    p, unit, _ = probe_scope(["MemoryMax=64M"], props, touch, "b")
    try:
        p.wait(timeout=30)
    except subprocess.TimeoutExpired:
        pass
    _kill_quiet(p)                            # ALL_T1009: also closes stderr
    res = bus_result(unit + ".scope")
    if p.returncode != -9 or res != "oom-kill":
        return "prlimit", props, "probe B rc=%s Result=%s" % (p.returncode, res)
    # probe C: idle slice cap reaches a new scope's parent
    note = ""
    sctl("set-property", "--runtime", "bora-same.slice", "MemoryMax=2G")
    pc = ("cat /sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/../memory.max")
    p, unit, _ = probe_scope([], props, ["sh", "-c", pc], "c")
    try:
        p.wait(timeout=30)
    except subprocess.TimeoutExpired:
        pass
    _kill_quiet(p)                            # ALL_T1009: also closes stderr
    if _read(plog("probe_c.out")) != "2147483648":
        note = "slice cap off"
    return "systemd", props, note


def _kill_quiet(p):
    try:
        p.kill()
        p.wait(timeout=5)
    except Exception:
        pass
    try:
        if p.stderr is not None:              # ALL_T1009: no ResourceWarning
            p.stderr.close()
    except Exception:
        pass


def bus_result(unit):
    """Poll ActiveState until inactive, failed or gone (2 s); Result."""
    res, t0 = "", time.time()
    while True:
        r = sctl("show", "-p", "ActiveState", "-p", "Result", "-p",
                 "LoadState", unit, timeout=10)
        txt = r.stdout if r is not None else ""
        d = dict(ln.split("=", 1) for ln in txt.splitlines() if "=" in ln)
        res = d.get("Result", "")
        if (d.get("ActiveState") in ("inactive", "failed")
                or d.get("LoadState") == "not-found" or time.time() - t0 > 2):
            break
        time.sleep(0.1)
    sctl("reset-failed", unit, timeout=10)
    return res


def systemd_startup():
    sctl("stop", "bora-same.slice", "bora-tail.slice", timeout=120)
    sctl("reset-failed", "same-*", timeout=60)
    me = os.getuid()
    for pid in _pids():
        try:
            if os.stat("/proc/%d" % pid).st_uid != me:
                continue
            cmd = open("/proc/%d/cmdline" % pid, "rb").read()
        except OSError:
            continue
        if b"policy_real_" in cmd and pid != os.getpid():
            _sigkill(pid)


# ===========================================================================
# process tree (SIGTERM)
# ===========================================================================
def _pids():
    return [int(d) for d in os.listdir("/proc") if d.isdigit()]


# ALL_T1009 A1: one driver per box (abstract socket lock + hand-run scan)
DRIVER_LOCK = "bora_zombie_driver_%d" % os.getuid()
_REAL_DRIVER_LOCK = DRIVER_LOCK
LOCK_POLL_S = 10
LOCK_LOG_S = 300                 # ALL_T1009: at most 6 wait lines per run
LOCK_WAIT_RUN_S = 1800
CHECK_LOCK_WAIT_S = 120          # ALL_T1009: a quick PD restart is not refused
SCAN_DRIVERS = ("run_zombie.py", "dry_run_zombie.py")
_LOCK = {}


def driver_lock_held(name):
    """ALL_T1009: read only: is @name bound (/proc/net/unix)?"""
    try:
        with open("/proc/net/unix") as f:
            return any(ln.split()[-1] == "@" + name for ln in f
                       if len(ln.split()) >= 8)
    except OSError:
        return False


def lock_holders(name):
    """ALL_T1009: pids of this user holding the socket @name."""
    ino = set()
    try:
        with open("/proc/net/unix") as f:
            for ln in f:
                p = ln.split()
                if len(p) >= 8 and p[-1] == "@" + name:
                    ino.add("socket:[%s]" % p[6])
    except OSError:
        return []
    out = []
    for pid in _pids():
        if pid == os.getpid() or not _owned(pid):
            continue
        try:
            fds = os.listdir("/proc/%d/fd" % pid)
        except OSError:
            continue
        for fd in fds:
            try:
                if os.readlink("/proc/%d/fd/%s" % (pid, fd)) in ino:
                    out.append(pid)
                    break
            except OSError:
                continue
    return out


def _script_of(argv):
    """ALL_T1009: the script a python argv runs (None for -c, -m)."""
    i = 1
    while i < len(argv):
        x = argv[i]
        if x in (b"-c", b"-m"):
            return None
        i += 2 if x in (b"-W", b"-X", b"-Q") else 1
        if not x.startswith(b"-"):
            return x
    return None


def other_zombie_pids(names=None):
    """ALL_T1009: this user's python processes whose script is in names."""
    names, out = names or SCAN_DRIVERS, []
    for pid in _pids():
        if pid == os.getpid() or not _owned(pid):
            continue
        try:
            argv = open("/proc/%d/cmdline" % pid, "rb").read().split(b"\0")
        except OSError:
            continue
        if not os.path.basename(argv[0]).startswith(b"python"):
            continue
        sc = _script_of([x for x in argv if x])
        if sc and os.path.basename(sc).decode(errors="replace") in names:
            out.append(pid)
    return out


def driver_lock(wait_s):
    """ALL_T1009: take the box-wide driver lock; None or a refusal."""
    if _LOCK.get("sock") is not None:
        return None
    t0 = t_log = time.time()
    while True:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
        try:
            s.bind("\0" + DRIVER_LOCK)
            _LOCK["sock"] = s
            return None
        except OSError:
            s.close()
        now = time.time()
        if now - t0 >= wait_s:
            return ("another Zombie driver holds the driver lock @%s (pids %s)"
                    % (DRIVER_LOCK, lock_holders(DRIVER_LOCK) or "unknown"))
        if now - t0 >= LOCK_POLL_S and now - t_log >= LOCK_LOG_S:
            t_log = now
            print("SAME wait lock @%s, %.0f s of %d s" % (
                DRIVER_LOCK, now - t0, wait_s), flush=True)
        time.sleep(max(0.0, min(LOCK_POLL_S, wait_s - (now - t0))))


def driver_guard(wait_s):
    """ALL_T1009: the lock, then hand runs of RZ / dry RZ; None or why."""
    why = driver_lock(wait_s)
    if why:
        return why
    pids = other_zombie_pids()
    if pids:
        return ("a hand run of run_zombie.py or dry_run_zombie.py is active "
                "(pids %s); stop it first" % pids)
    return None


# ALL_T1009 A3: circ_executable left by a dead driver
ZOMBIE_DIRS = ("bora_zombie_scratch", "bora_zombie_par")


def _stat_of(pid):
    """(state, ppid) from /proc/PID/stat, or None."""
    try:
        with open("/proc/%d/stat" % pid) as f:
            f2 = f.read().rsplit(")", 1)[1].split()
        return f2[0], int(f2[1])
    except (OSError, IndexError, ValueError):
        return None


def _exe_base(pid):
    """ALL_T1009: basename of /proc/PID/exe, else of argv[0]."""
    try:
        p = os.readlink("/proc/%d/exe" % pid)
        return os.path.basename(p[:-10] if p.endswith(" (deleted)") else p)
    except OSError:
        try:
            a0 = open("/proc/%d/cmdline" % pid, "rb").read().split(b"\0")[0]
            return os.path.basename(a0.decode(errors="replace"))
        except OSError:
            return ""


def _live_python_ancestor(pid):
    st, seen = _stat_of(pid), set()
    p = st[1] if st else 0
    while p > 1 and p not in seen:
        seen.add(p)
        st = _stat_of(p)
        if st is None:
            return True                       # ALL_T1009: unsure, so spare it
        if st[0] != "Z" and _exe_base(p).startswith("python"):
            return True
        p = st[1]
    return False


def _owned(pid):
    try:
        return os.stat("/proc/%d" % pid).st_uid == os.getuid()
    except OSError:
        return False


def _cwd_of(pid):
    try:
        return os.readlink("/proc/%d/cwd" % pid)
    except OSError:
        return ""


def _zombie_cwd(cwd):
    if cwd.endswith(" (deleted)"):
        cwd = cwd[:-10]
    root = os.path.abspath(rz.PAR_ROOT)
    return (any(x in ZOMBIE_DIRS for x in cwd.split("/")) or cwd == root
            or cwd.startswith(root + "/"))


def orphan_circ(kill, pids=None):
    """ALL_T1009: [(pid, cwd)] of orphan circ_executable; kill=True kills."""
    out = []
    for pid in (sorted(pids) if pids is not None else _pids()):
        if pid == os.getpid() or not _owned(pid):
            continue
        if _exe_base(pid) != "circ_executable":
            continue
        cwd = _cwd_of(pid)
        if not cwd or not _zombie_cwd(cwd) or _live_python_ancestor(pid):
            continue
        out.append((pid, cwd))
        if kill:
            _sigkill(pid)
            say("SAME note: killed orphan circ_executable pid %d (cwd %s)"
                % (pid, cwd))
    return out


def _alive(pid):
    st = _stat_of(pid)
    return st is not None and st[0] != "Z"


def orphan_text(orph):
    return ("orphan circ_executable of a dead driver: %s. Kill them first: "
            "kill -9 %s" % ("; ".join("pid %d cwd %s" % o for o in orph),
                            " ".join(str(p) for p, _ in orph)))


# ALL_T1009 A4: die with PAPER_DATA
def bind_parent():
    """ALL_T1009: SIGTERM us when ZKR_SAME_PARENT (PAPER_DATA) dies."""
    want = os.environ.pop("ZKR_SAME_PARENT", None)
    if not want:
        return
    import ctypes
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, signal.SIGTERM, 0, 0, 0) != 0:   # ALL_T1009: PDEATHSIG
        say("SAME note: PR_SET_PDEATHSIG failed errno %d" % ctypes.get_errno())
    try:
        gone = os.getppid() != int(want)
    except ValueError:
        gone = False
    if gone:
        say("SAME refuse: parent %s already gone" % want)
        raise SystemExit(143)


def descendants(root):
    kids = {}
    for pid in _pids():
        try:
            with open("/proc/%d/stat" % pid) as f:
                ppid = int(f.read().rsplit(")", 1)[1].split()[1])
        except (OSError, IndexError, ValueError):
            continue
        kids.setdefault(ppid, []).append(pid)
    out, todo = [], [root]
    while todo:
        for c in kids.get(todo.pop(), []):
            out.append(c)
            todo.append(c)
    return out


def _sigkill(pid):
    try:
        os.kill(pid, signal.SIGKILL)
    except OSError:
        pass


def _kill_loop():
    while True:
        for pid in descendants(os.getpid()):
            _sigkill(pid)
        time.sleep(1.0)


def on_sigterm(signum, frame):
    # DLP_T1001 m9: stop writers, kill descendants every 1 s, exit 143
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    STOP.set()
    for pid in descendants(os.getpid()):      # ALL_T1013 F3: one pass now
        _sigkill(pid)
    threading.Thread(target=_kill_loop, daemon=True).start()
    raise SystemExit(143)


# ===========================================================================
# proves: launch, reap, classify (6a, 6d)
# ===========================================================================
class Task(object):
    def __init__(self, unit, size, eid, epath, d, base, er):
        self.unit, self.size, self.eid, self.epath = unit, size, eid, epath
        self.dir, self.base, self.er = d, base, er
        self.launch_fail = 0
        self.watchdog = 0                     # ALL_T1013 F14
        self.cls = []

    @property
    def rss(self):
        return self.base["rss_c"] or 0

    @property
    def cap(self):
        return int(max(1.5 * self.rss, self.rss + 4 * GIB))

    @property
    def timeout(self):
        return max(SAMPLE_TIMEOUT_MIN, SAMPLE_TIMEOUT_X *
                   (self.base["wall_s"] or 0))


def next_attempt(t):
    k = (t.unit, t.size, t.eid, t.base["base_uuid"])
    S["attempts"][k] = S["attempts"].get(k, 0) + 1
    return S["attempts"][k]


def launch(t, mode, slot=None, w=0, gid="", K_f=0, bucket=None, conc=0,
           tmult=1):
    """Start one real-witness prove; returns its running record."""
    circ = os.path.abspath(S["binp"])
    core = [circ, "policy_real_%d" % t.size, "false", "prover_verifier"]
    env = dict(os.environ)
    env["ZREAL_EMAIL"] = t.epath
    packed = mode in ("packed", "scalecal")
    cpus, node = ("", "")
    if packed:
        node, cl = slot
        cpus = cpus_str(cl)
        env["RAYON_NUM_THREADS"] = str(len(cl))
        core = ["taskset", "-c", cpus] + core
    else:
        env.pop("RAYON_NUM_THREADS", None)
    env.pop("ZREAL_NO_VERIFY", None)
    if mode == "gate_serial":                 # ALL_T1013 S2: prove_ms only
        env["ZREAL_NO_VERIFY"] = "1"
    S["k"] += 1
    unit = ""
    if S["launcher"] == "systemd":
        unit = "same-%d-%d-%d" % (os.getpid(), int(time.time()), S["k"])
        slc = "bora-same.slice" if packed else "bora-tail.slice"
        props = list(S["props"])
        if packed:
            props = ["MemoryMax=%d" % t.cap] + props
        else:                                 # serial: AS guard as prlimit
            core = rz._limited(core, S["full_mem"])
        cmd = (["systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
                "--slice=" + slc] + sum((["-p", q] for q in props), []) +
               ["--"] + core)
    else:
        cmd = rz._limited(core, int(t.cap * AS_FACTOR) if packed
                          else S["full_mem"])
    att = next_attempt(t)
    tag = "%s_%d_%s_a%d" % (re.sub(r"[^A-Za-z0-9]+", "_", t.unit), t.size,
                            t.eid, att)
    outp = os.path.join(S["logdir"], tag + ".out")
    errp = os.path.join(S["logdir"], tag + ".err")
    ma = memavail()
    with open(outp, "w") as fo, open(errp, "w") as fe:
        p = subprocess.Popen(cmd, cwd=t.dir, env=env, stdout=fo, stderr=fe)
    return {"t": t, "p": p, "pid": p.pid, "t0": time.time(), "slot": slot,
            "unit": unit, "mode": mode, "w": w, "cpus": cpus, "node": node,
            "threads": env.get("RAYON_NUM_THREADS", ""), "gid": gid,
            "K_f": K_f, "bucket": bucket, "conc": conc, "memavail": ma,
            "out": outp, "err": errp, "killed": None, "attempt": att,
            "timeout": t.timeout * tmult, "launcher": S["launcher"],
            "memmax": t.cap if packed and S["launcher"] == "systemd" else ""}


def reap(r, block=False):
    """wait4 the prove; returns (status, rusage) or None while running."""
    while True:
        try:
            pid, status, ru = os.wait4(r["pid"], 0 if block else os.WNOHANG)
        except ChildProcessError:
            return 0, None
        except InterruptedError:
            continue
        if pid == 0:
            return None
        r["p"].returncode = os.waitstatus_to_exitcode(status)
        return status, ru


def kill_proc(r, why):
    r["killed"] = why
    _sigkill(r["pid"])
    for c in descendants(r["pid"]):
        _sigkill(c)


def classify(rc, out, err, result, killed, er, timed_out, base_cons, cons):
    """6d death classes."""
    started = "zreal start" in out
    if er:
        return "expected_reject"
    if killed == "watchdog":
        return "watchdog"
    if rc != 0 and not started and SDRUN_ERR_RE.search(err):
        return "launcher"
    if timed_out:
        return "resource"
    vm = VERIFY_RE.search(out)
    if rc == 0:
        if rz._parse_metrics(out) is None or vm is None:
            return "resource"
        if vm.group(1) != "true":
            return "verify_false"
        return "ok" if cons == base_cons else "cons_mismatch"
    if rc == 3:
        return "verify_false"
    if result == "oom-kill" or ALLOC_RE.search(err):
        return "resource"
    if rc < 0 and -rc in (9, 15):
        return "resource"
    return "crash_suspect"


SKIP_LINE = "zreal verify_ok skipped"


def skip_view(out, mode):
    """ALL_T1013 S2: a gate serial reference that skipped its verify reads
    as verified for classify; its row keeps verify_ms and verify_ok empty."""
    if mode == "gate_serial" and SKIP_LINE in out:
        return out + "\nverify takes 0\nzreal verify_ok true\n", True
    return out, False


def needs_bus(r):
    """A systemd prove without a clean exit needs its scope Result."""
    out = skip_view(_read(r["out"]), r["mode"])[0]
    return r["launcher"] == "systemd" and not (
        r["p"].returncode == 0 and rz._parse_metrics(out) and
        VERIFY_RE.search(out))


def finish(r, status, ru, result=None):
    """Build, classify and persist the prove row of a reaped process."""
    t = r["t"]
    rc = r["p"].returncode if r["p"].returncode is not None else -9
    out, skipped = skip_view(_read(r["out"]), r["mode"])   # ALL_T1013 S2
    err = _read(r["err"])
    m = rz._parse_metrics(out) or {}
    vm = VERIFY_RE.search(out)
    if skipped:
        m["verify_ms"], vm = None, None
    if result is None:
        result = bus_result(r["unit"] + ".scope") if needs_bus(r) else ""
    cls = classify(rc, out, err, result, r["killed"], t.er,
                   r["killed"] == "timeout", t.base["cons"], m.get("r1cs_cons"))
    row = put("prove", unit=t.unit, size=t.size, email_id=t.eid,
              attempt=r["attempt"], mode=r["mode"], expected_reject=int(t.er),
              width=r["w"], threads=r["threads"], cpus=r["cpus"],
              node=r["node"], cons_bucket=r["bucket"], launcher=r["launcher"],
              MemoryMax=r["memmax"], K_f=r["K_f"], concurrency=r["conc"],
              MemAvailable=r["memavail"],
              wall_s=round(time.time() - r["t0"], 3),
              utime_s=round(ru.ru_utime, 3) if ru else None,
              stime_s=round(ru.ru_stime, 3) if ru else None,
              maxrss_kB=ru.ru_maxrss if ru else None,
              prove_ms=m.get("prove_ms"), verify_ms=m.get("verify_ms"),
              cons=m.get("r1cs_cons"),
              verify_ok=(vm.group(1) == "true") if vm else None, rc=rc,
              sig=-rc if rc < 0 else 0, Result=result, **{"class": cls},
              base_uuid=t.base["base_uuid"], gate_id=r["gid"])
    t.cls.append(cls)
    if cls == "launcher":
        S["launch_consec"] += 1
        if S["launch_consec"] >= LAUNCH_SWITCH and S["launcher"] == "systemd":
            S["launcher"] = "prlimit"
            say("SAME launcher: %d consecutive launcher failures, switching "
                "to prlimit (new coverage key)" % S["launch_consec"])
    else:
        S["launch_consec"] = 0
    if cls not in ("ok", "expected_reject"):
        say("SAME prove %s size=%d %s attempt %d mode %s: class %s rc=%d "
            "sig=%d" % (t.unit, t.size, t.eid, r["attempt"], r["mode"], cls,
                        rc, -rc if rc < 0 else 0))
    return cls, row


def run_one_serial(t, mode, tmult=1):
    """One serial prove on the idle box (tail, serial, gate_serial)."""
    r = launch(t, mode, tmult=tmult)
    while True:
        got = reap(r)
        if got is not None:
            return finish(r, *got)
        if time.time() - r["t0"] > r["timeout"]:
            kill_proc(r, "timeout")
        time.sleep(POLL_S)


def serial_until_done(t, mode, tmult=1):
    """Serial attempts per 6d: resource 2, crash 1 (+repro), verify 1."""
    n_res = 0
    while True:
        cls, row = run_one_serial(t, mode, tmult)
        if cls == "ok":
            if "crash_suspect" in t.cls[:-1]:
                S["notes"].append("transient crash %s %s %d" % (
                    t.unit, t.eid, t.size))
            return cls
        if cls == "launcher":
            t.launch_fail += 1
            if t.launch_fail <= LAUNCH_RETRIES:
                continue
            return cls
        if cls == "resource":
            n_res += 1
            if n_res < TAIL_RESOURCE:
                continue
            S["notes"].append("incomplete %s %s %d" % (t.unit, t.eid, t.size))
            return cls
        if cls == "crash_suspect":
            if t.cls.count("crash_suspect") < 2:   # one reproduce attempt
                continue
            S["fails"].append("reproduced crash %s %s %d" % (t.unit, t.eid,
                                                             t.size))
        if cls in ("verify_false", "cons_mismatch"):
            S["fails"].append("%s %s %s %d" % (cls, t.unit, t.eid, t.size))
        return cls


def run_tail(tasks):
    for t in tasks:
        first = t.cls[-1] if t.cls else "resource"
        if first == "verify_false":
            S["fails"].append("verify_false %s %s %d" % (t.unit, t.eid, t.size))
        serial_until_done(t, "tail", tmult=2)


# ===========================================================================
# scheduler: width, admission, gate (6b)
# ===========================================================================
def ffd_count(tasks, nslots, B, used=0):
    k = 0
    for t in sorted(tasks, key=lambda x: -x.rss):
        if k < nslots and used + t.cap <= B:
            used += t.cap
            k += 1
    return k


def ladder(topo, cap):
    """ALL_T1013 S5: width rungs by slot count. A candidate is the widest
    width for its slots per node (C // w); 1, 2, 4 and the top min(cap, C)
    stay, any other rung needs at most 1/1.4 of the last kept rung's slots."""
    C = node_slot_cores(topo)
    top = max(1, min(cap, C) if cap else C)
    out = []
    for w in range(1, top + 1):
        if not (w == top or C // (w + 1) < C // w):
            continue
        if (not out or w in (2, 4, top)
                or C // w <= (C // out[-1]) / 1.4):
            out.append(w)
    return out


def snap_up(rungs, x):
    """ALL_T1013 R6: smallest rung >= x, else the top rung."""
    return next((r for r in rungs if r >= x), rungs[-1])


def snap_down(rungs, x):
    return max([r for r in rungs if r <= x] or [rungs[0]])


def next_rung(rungs, w):
    """ALL_T1013 R6: smallest rung above w (w need not be a rung)."""
    return next((r for r in rungs if r > w), None)


def widen_next(g_hist, s, w):
    """ALL_T1013 S5: the next rung, or None to give up: no rung above w,
    or two rungs together improved g by at most the serial spread s."""
    nxt = next_rung(ladder(S["topo"], S["cap"]), w) if S["cap"] else None
    if nxt is None or (len(g_hist) >= 3 and g_hist[-3] - g_hist[-1] <= s):
        return None
    return nxt


def width_for(size, tasks, B):
    topo = S["topo"]
    w_cpu = max([int(math.ceil(1.5 * (t.base["u_c"] or 0) / topo["tpc"]))
                 for t in tasks] + [ARGS.slot_cores])
    k_mem = max(1, ffd_count(tasks, len(tasks), B))
    w_mem = topo["c_cores"] // max(1, min(k_mem, len(tasks)))
    L = ladder(topo, S["cap"])                # ALL_T1013 S5: cap and node top
    w = max(S["w_state"].get(size, ARGS.slot_cores), snap_up(L, w_cpu),
            snap_down(L, w_mem))
    return snap_up(L, w)


def best_gate(key):
    g = S["gates"].get(key) or []
    return max(g, key=lambda r: r["K_gate"]) if g else None


def gate_pairs(tasks):
    """Circuits 0 and n//2 by cons desc, first 2 unlisted e-mails each."""
    units = sorted({t.unit: t.base["cons"] for t in tasks}.items(),
                   key=lambda x: (-x[1], x[0]))
    pick = [units[0][0]] if len(units) == 1 else [units[0][0],
                                                   units[len(units) // 2][0]]
    out = []
    for u in pick:
        mine = [t for t in tasks if t.unit == u and not t.er]
        out.extend(sorted(mine, key=lambda t: t.eid)[:2])
    return out


def ref_serial(t):
    """ALL_T1013 FI2/FI4: one gate reference prove; a resource death
    (OOM, kill, timeout) is retried once, as serial_until_done does."""
    cls, row = run_one_serial(t, "gate_serial")
    if cls == "resource":
        say("SAME note: gate reference %s %s size=%d was a resource death; "
            "retried once" % (t.unit, t.eid, t.size))
        cls, row = run_one_serial(t, "gate_serial")
    return cls, row


def serial_reference(pairs):
    """2 serial proves per pair, a 3rd when d > 0.05; ref median, s."""
    ref, ds = {}, []
    for t in pairs:
        ms, cls = [], "ok"
        for _ in range(2):
            cls, row = ref_serial(t)
            if cls != "ok":
                break
            ms.append(row["prove_ms"])
        if cls == "verify_false":             # a reject, not a gate failure
            note_vf(t)
            continue
        if cls != "ok":
            return None, None
        d = abs(ms[0] - ms[1]) / max(1e-9, statistics.mean(ms))
        if d > GATE_D3:
            cls, row = ref_serial(t)
            if cls != "ok":
                return None, None
            ms.append(row["prove_ms"])
        ref[id(t)] = max(1, statistics.median(ms))
        ds.append(d)
    if not ref:
        return {}, None                       # every pair verify_false
    return ref, statistics.median(ds)


def note_vf(t):
    msg = "verify_false %s %s %d (gate pair)" % (t.unit, t.eid, t.size)
    if msg not in S["fails"]:
        S["fails"].append(msg)
        say("SAME gate pair %s %s size=%d is verify_false: recorded as a "
            "failing pair, not used for the gate" % (t.unit, t.eid, t.size))


def judge(pair_ms, ref, s):
    ratios = [pair_ms[k] / ref[k] for k in ref]
    g = math.exp(sum(math.log(max(x, 1e-9)) for x in ratios) / len(ratios))
    return g, GATE_TAU, g <= GATE_TAU


class Packed(object):
    """One packed pass at width w; launches under K_f, B and slots."""

    def __init__(self, size, b, w, B, K_f, gid, pairs, mode="packed"):
        self.size, self.b, self.w, self.B = size, b, w, B
        self.K_f, self.gid, self.pairs = K_f, gid, pairs
        self.mode = mode
        self.slots = make_slots(S["topo"], w)
        self.free = list(range(len(self.slots)))
        self.running, self.tail, self.done_ok = [], [], []
        self.finishing = []
        self.pair_ms, self.committed = {}, 0
        self.draining = False
        self.on_pairs = None
        self.launcher0 = S["launcher"]
        self.wait_t0 = self.wait_log = None

    @property
    def switched(self):
        return S["launcher"] != self.launcher0

    def can(self, t):
        R = S["R"]
        lim = self.K_f if self.K_f else len(self.slots)
        return (self.free and len(self.running) < lim
                and self.committed + t.cap <= self.B
                and memavail() - R >= t.cap and not self.paused)

    def start(self, t):
        self.wait_t0 = None                   # a launch ends a memory wait
        si = self.free.pop(0)
        r = launch(t, self.mode, self.slots[si], self.w, self.gid,
                   self.K_f or 0, self.b, len(self.running) + 1)
        r["si"] = si
        self.committed += t.cap
        self.running.append(r)
        S["running"].append(r)

    def run(self, queue):
        self.paused = False
        if S["launcher"] == "systemd":        # slice cap = B for every pass
            sctl("set-property", "--runtime", "bora-same.slice",
                 "MemoryMax=%d" % max(self.B, 1), "MemorySwapMax=0")
        while True:                           # first round, FFD by rss_c
            for t in list(queue):
                if self.can(t):
                    self.start(t)
                    queue.remove(t)
            if self.running or not self.idle_wait(queue):
                break
        if not self.K_f:
            self.K_f = len(self.running)
            for r in self.running:
                r["K_f"] = self.K_f
        if not self.running:
            return
        last_wd = time.time()
        while self.running or self.finishing or (queue and not self.draining):
            for r, got, fut in list(self.finishing):
                if fut.done():                # DLP_T1001: bus off the loop
                    self.finishing.remove((r, got, fut))
                    cls, row = finish(r, *got, result=fut.result())
                    self.after(r["t"], cls, row, queue)
            for r in list(self.running):
                got = reap(r)
                if got is None:
                    if time.time() - r["t0"] > r["timeout"] and not r["killed"]:
                        kill_proc(r, "timeout")
                    continue
                self.running.remove(r)
                S["running"].remove(r)
                self.free.append(r["si"])
                self.free.sort()
                self.committed -= r["t"].cap
                if S.get("bus") is not None and needs_bus(r):
                    self.finishing.append((r, got, S["bus"].submit(
                        bus_result, r["unit"] + ".scope")))
                    continue
                cls, row = finish(r, *got)
                self.after(r["t"], cls, row, queue)
            if time.time() - last_wd >= WATCHDOG_S:
                last_wd = time.time()
                ma = memavail()
                self.paused = ma < S["R"]
                if ma < S["R"] / 2 and self.running:
                    y = max(self.running, key=lambda r: r["t0"])
                    kill_proc(y, "watchdog")
            if self.switched:
                self.draining = True
            while queue and not self.draining:
                nxt = next((t for t in queue if self.can(t)), None)
                if nxt is None:
                    break
                queue.remove(nxt)
                self.start(nxt)
            if (queue and not self.running and not self.finishing
                    and not self.draining):
                self.idle_wait(queue)         # DLP_T1001 R3: no dump on pause
            time.sleep(POLL_S)

    def idle_wait(self, queue):
        """Idle box, nothing launched: tasks whose cap can never fit (cap
        > B) go to the tail; the rest wait for memory. True: keep waiting."""
        never = [t for t in queue if t.cap > self.B]
        self.tail.extend(never)
        queue[:] = [t for t in queue if t not in never]
        if not queue:
            return False
        ma, now = memavail(), time.time()
        self.paused = ma < S["R"]
        if self.wait_t0 is None:
            self.wait_t0 = self.wait_log = now - MEM_WAIT_LOG_S
        if now - self.wait_log >= MEM_WAIT_LOG_S:
            self.wait_log = now
            say("SAME WAIT memory: avail %.0f GiB < reserve %.0f GiB, %d tasks "
                "queued" % (ma / GIB, S["R"] / GIB, len(queue)))
        if now - self.wait_t0 >= MEM_WAIT_MAX_S + MEM_WAIT_LOG_S:
            raise MemStop("idle memory wait over %d s at %d (avail %.0f GiB "
                          "< reserve %.0f GiB)" % (MEM_WAIT_MAX_S, self.size,
                                                   ma / GIB, S["R"] / GIB))
        time.sleep(POLL_S)
        return True

    def after(self, t, cls, row, queue):
        if cls == "watchdog":
            t.watchdog += 1
            if t.watchdog < 3:                # ALL_T1013 F14: bounded
                queue.insert(0, t)
                return
            self.tail.append(t)
        if cls == "launcher":
            t.launch_fail += 1
            if t.launch_fail <= LAUNCH_RETRIES:
                queue.insert(0, t)
                return
            self.tail.append(t)
        elif cls in ("resource", "crash_suspect", "verify_false"):
            self.tail.append(t)
        elif cls == "cons_mismatch":
            S["fails"].append("cons_mismatch %s %s %d" % (t.unit, t.eid,
                                                          t.size))
        elif cls == "ok":
            self.done_ok.append(t)
        if self.pairs is not None and t in self.pairs and t not in self.pair_ms:
            self.pair_ms[t] = (row["prove_ms"] if cls == "ok" else
                               "verify_false" if cls == "verify_false"
                               else None)
            if len(self.pair_ms) == len(self.pairs) and self.on_pairs:
                self.on_pairs(self)


def give_up(size, reason, tasks, w, cause="gate"):
    """Gate cannot pass: SERIAL MODE 1 KB, cap-0 serial, or SAME STOP."""
    if size == 1000 or S["cap"] == 0:
        if size not in S["serial"]:
            say("=" * 64)
            say("SERIAL MODE %s: %s" % ("1 KB" if size == 1000 else
                                        "%d" % size, reason))
            say("=" * 64)
        S["serial"].add(size)
        for t in tasks:
            serial_until_done(t, "serial")
        return
    raise StopFlush(reason, w, cause)


class MemStop(Exception):
    """Idle memory wait timed out (DLP_T1001)."""


class StopFlush(Exception):
    def __init__(self, reason, width=None, cause="gate"):
        Exception.__init__(self, reason)
        self.width = width
        self.cause = cause                    # ALL_T1013 FI2: "ref" lifts once


def run_subflush(size, b, tasks):
    """6b sub-flush: width, coverage, gate event, widen/serial/stop."""
    if size in S["serial"]:
        for t in tasks:
            serial_until_done(t, "serial")
        return []
    B = memavail() - S["R"]
    tail = [t for t in tasks if t.cap > B]
    queue = sorted([t for t in tasks if t.cap <= B], key=lambda t: -t.rss)
    w = width_for(size, queue or tasks, B)
    ref = s = pairs = None
    g_hist = []                               # ALL_T1013 S5: this event's g
    while queue:
        key = (size, w, b, S["launcher"], S["sig"])
        K0 = ffd_count(queue, len(make_slots(S["topo"], w)), B)
        gate = best_gate(key)
        if gate and gate["K_gate"] >= K0:
            pk = Packed(size, b, w, B, K0, gate["gate_id"], None)
        elif gate and K0 <= K_SLACK * gate["K_gate"]:
            pk = Packed(size, b, w, B, gate["K_gate"], gate["gate_id"], None)
        else:
            pk = None
        if pk is not None:
            pk.run(queue)
            tail.extend(pk.tail)
            if pk.switched and queue:
                continue
            break
        if pairs is None:
            pairs = gate_pairs(queue)
        if ref is None:
            ref, s = serial_reference(pairs)
            if not ref:
                give_up(size, "verify_false on every gate pair at %d" % size
                        if ref == {} else
                        "gate reference prove failed at %d" % size, queue, w,
                        cause="gate" if ref == {} else "ref")   # ALL_T1013
                return tail
            pairs = [t for t in pairs if id(t) in ref]
        tail[:] = [t for t in tail if t not in pairs]
        gid = uuid.uuid4().hex[:12]
        queue[:] = pairs + [t for t in queue if t not in pairs]
        pk = Packed(size, b, w, B, 0, gid, pairs)
        verdict = {}

        def on_pairs(p, verdict=verdict, gid=gid, key=key, w=w):
            for t, v in p.pair_ms.items():
                if v == "verify_false":
                    note_vf(t)
            good = {id(t): v for t, v in p.pair_ms.items()
                    if v not in (None, "verify_false")}
            if any(v is None for v in p.pair_ms.values()) or not good:
                verdict.update(g=float("inf"), tau=0, ok=False,
                               vf=not good and None not in p.pair_ms.values())
            else:
                g, tau, ok = judge(good, {k: ref[k] for k in good}, s)
                verdict.update(g=g, tau=tau, ok=ok)
            put("gate", gate_id=gid, size=size, width=w, cons_bucket=b,
                launcher=key[3], K_gate=p.K_f,
                g=round(verdict["g"], 4) if verdict["g"] != float("inf")
                else None, s=round(s, 4), tau=round(verdict["tau"], 4),
                verdict="pass" if verdict["ok"] else "fail",
                pairs=["%s|%s" % (t.unit, t.eid) for t in p.pairs])
            say("SAME gate %s size=%d w=%d b=%d K_gate=%d g=%s tau=%.3f s=%.3f"
                " -> %s" % (gid, size, w, b, p.K_f, verdict["g"],
                            verdict["tau"], s,
                            "pass" if verdict["ok"] else "fail"))
            if not verdict["ok"]:
                p.draining = True
        pk.on_pairs = on_pairs
        pk.run(queue)
        tail.extend(pk.tail)
        if not verdict:
            if pk.switched:                   # key changed mid-event
                queue[:] = list(dict.fromkeys(pairs + pk.done_ok + queue))
                tail[:] = [t for t in tail if t not in pairs]
                continue
            # DLP_T1001 fix4: serial at 1 KB, STOP only at 2 and 4 KB
            give_up(size, "gate pairs never completed at %d" % size,
                    list(dict.fromkeys(pairs + pk.done_ok + queue)), w)
            tail[:] = [t for t in tail if t not in pairs]
            return tail
        if verdict["ok"]:
            gr = [r for r in S["rows"] if r.get("gate_id") == gid
                  and r["kind"] == "gate"][-1]
            S["gates"].setdefault(key, []).append(gr)
            if queue:                         # drained by a launcher switch:
                pairs = ref = None            # new pairs, never re-proved
                g_hist = []
                continue
            break
        if verdict.get("vf"):
            give_up(size, "verify_false on every gate pair at %d" % size,
                    list(dict.fromkeys(pk.done_ok + queue)), w)
            return tail
        pairs = [t for t in pairs if pk.pair_ms.get(t) != "verify_false"]
        rejected = list(dict.fromkeys(pairs + pk.done_ok + queue))
        tail[:] = [t for t in tail if t not in pairs]
        g = verdict["g"]
        g_hist.append(g)
        nxt = widen_next(g_hist, s, w)        # ALL_T1013 S5: two-rung stop
        if nxt is None:
            give_up(size, "gate cannot pass at %d (w=%d g=%s)" % (size, w, g),
                    rejected, w)
            return tail
        say("SAME widen size=%d w %d -> %d (g=%.3f)" % (size, w, nxt, g))
        w = nxt
        S["w_state"][size] = w
        put("width", size=size, width=w)
        queue[:] = rejected
    return tail


# ===========================================================================
# flush, proxy, pipeline hooks
# ===========================================================================
def build_tasks(items, n=None):
    er = S["er"]
    tasks = []
    for it in items:
        for eid, p, _sha in sample_emails(it["size"], n or ARGS.n):
            tasks.append(Task(it["unit"], it["size"], eid, p, it["dir"],
                              it["base"], (it["unit"], eid, it["size"]) in er))
    return tasks


def flush():
    """Sample work for the deferred dirs of the last batch (DLP_T1001)."""
    items = S["pending"][:]
    del S["pending"][:]
    if not items:
        return
    size = items[0]["size"]
    try:
        tasks = build_tasks(items)
        listed = [t for t in tasks if t.er]
        work = [t for t in tasks if not t.er]
        buckets = {}
        for t in work:
            buckets.setdefault(int(math.log2(max(2, t.base["cons"] or 2))),
                               []).append(t)
        tail = []
        say("SAME flush size=%d units=%d tasks=%d buckets=%s" % (
            size, len(items), len(tasks), sorted(buckets, reverse=True)))
        for b in sorted(buckets, reverse=True):
            tail.extend(run_subflush(size, b, buckets[b]))
        if listed:                            # proved once, never retried
            pk = Packed(size, -1, ARGS.slot_cores, memavail() - S["R"], 0, "",
                        None)
            pk.run(list(listed))
            for t in pk.tail:                 # never launched (cap > B)
                if not t.cls:
                    run_one_serial(t, "tail")
        run_tail(tail)
    except MemStop as e:
        mem_stop(size, str(e), tasks)
    except StopFlush as e:
        stop_path(size, str(e), items, e.width, cause=e.cause)
        return                                # dirs gone: never re-kept
    except Exception as e:
        with open(plog("tracebacks.log"), "a") as f:
            f.write(traceback.format_exc())
        stop_path(size, "exception in flush: %s: %s" % (type(e).__name__, e),
                  items, cause="error", etype=type(e).__name__)
        return                                # DLP_T1001 M1
    for it in items:
        if ARGS.scalecal and size == 1000:
            S["keep"].append(it)
        else:
            _ORIG["rmtree"](it["dir"], ignore_errors=True)


def mem_stop(size, reason, tasks):
    """Resource stop: serial at 1 KB if a serial prove fits, else this
    size's sample is refused (R1 path) and the sweep goes on."""
    for r in list(S["running"]):
        kill_proc(r, "stop")
        reap(r, block=True)
    del S["running"][:]
    base, gates = index_rows(S["rows"])
    done = {(r["unit"], r["email_id"]) for r in S["rows"]
            if r.get("size") == size and is_accepted(r, base, gates)}
    left = [t for t in tasks if not t.er and (t.unit, t.eid) not in done]
    if ((size == 1000 or S["cap"] == 0)
            and memavail() >= max([t.cap for t in left] or [0])):
        give_up(size, reason, left, 0)
        return
    S.setdefault("refused", {})[size] = "resource stop: %s" % reason
    put("stop", size=size, reason="resource stop: %s" % reason, cap=S["cap"],
        width=S["w_state"].get(size, ARGS.slot_cores), cause="mem")
    if size in ARGS.sizes:
        ARGS.sizes.remove(size)
    say("SAME sample at %d refused: %s. The sweep goes on." % (size, reason))


def stop_path(size, reason, items, width=None, cause="gate", etype=None):
    """Kill and reap running proves, persist the STOP row, refuse this
    size's sample (R1 rule): the sweep and the other sizes go on."""
    for r in list(S["running"]):
        kill_proc(r, "stop")
        reap(r, block=True)
    del S["running"][:]
    put("stop", size=size, reason=reason, cap=S["cap"],
        width=width or S["w_state"].get(size, ARGS.slot_cores), cause=cause,
        **({"etype": etype} if etype else {}))
    for it in items + S["keep"]:
        _ORIG["rmtree"](it["dir"], ignore_errors=True)
    del S["keep"][:]
    S.setdefault("refused", {})[size] = reason
    if size in ARGS.sizes:
        ARGS.sizes.remove(size)
    say("SAME sample at %d stopped: %s. The sweep and the other sizes go on; "
        "the leaf ends with SAME STOP." % (size, reason))


class ShutilProxy(object):
    """rz.shutil: defers sample dirs, flushes at disk_usage (RZ:970)."""

    def __getattr__(self, name):
        return getattr(shutil, name)

    def rmtree(self, path, *a, **k):
        if path in S["defer"]:
            S["pending"].append(S["defer"].pop(path))
            return None
        return _ORIG["rmtree"](path, *a, **k)

    def disk_usage(self, path):
        flush()
        return shutil.disk_usage(path)


def time_one(binp, built, str_len, mem_bytes=None, timeout=rz.PROVE_TIMEOUT):
    """RZ _time_one with wait4; a sample-size ok base is recorded/deferred."""
    rec, base = base_time(binp, built, str_len, mem_bytes, timeout)
    if rec.get("status") == "oom_or_killed" and S.get("last_batch_n") == 1:
        # ALL_T1013 FI3: RZ never retries a serial batch's killed base prove;
        # rerun it once, alone, on the same keys, argv, cap and timeout
        say("SAME note: base prove of %s at %d was killed in a serial batch; "
            "rerun once alone" % (built["name"], str_len))
        rec, base = base_time(binp, built, str_len, mem_bytes, timeout)
    if base is not None and str_len in ARGS.sizes:
        d = built["dir"]
        put("base", unit=built["name"], size=str_len, **base)
        S["defer"][d] = {"unit": built["name"], "size": str_len, "dir": d,
                         "base": base}
    return rec


def base_time(binp, built, str_len, mem_bytes=None, timeout=rz.PROVE_TIMEOUT):
    """RZ _time_one (RZ:874-893): same argv, cwd, env, timeout; (rec, base)."""
    name, prox, d = built["name"], built["prox"], built["dir"]
    pat, kws, _ = rz.extract_parts(rz._read(os.path.join(
        rz.FULL_DIR, name + ".regex")).strip())
    cmd = rz._limited([os.path.abspath(binp), "policy_%d" % str_len, "false",
                       "prover_verifier"], mem_bytes)
    outp = os.path.join(S["logdir"], "base_%s_%d.out" % (
        re.sub(r"[^A-Za-z0-9]+", "_", name), str_len))
    errp = outp[:-4] + ".err"
    t0 = time.time()
    with open(outp, "w") as fo, open(errp, "w") as fe:
        p = subprocess.Popen(cmd, cwd=d, stdout=fo, stderr=fe, text=True)
    r = {"p": p, "pid": p.pid}
    while True:
        got = reap(r)
        if got is not None:
            break
        if time.time() - t0 > timeout:
            _sigkill(p.pid)
            reap(r, block=True)
            return rz._rec(name, str_len, pat, kws, prox,
                           status="prove_timeout"), None
        time.sleep(POLL_S)
    wall = time.time() - t0
    _, ru = got
    out, err = _read(outp), _read(errp)
    if p.returncode != 0:
        st = "oom_or_killed" if p.returncode < 0 else "prove_fail"
        return rz._rec(name, str_len, pat, kws, prox, status=st,
                       err=(err or "")[-300:]), None
    m = rz._parse_metrics(out)
    if m is None:
        return rz._rec(name, str_len, pat, kws, prox, status="prove_fail",
                       err="no metrics"), None
    rec = rz._rec(name, str_len, pat, kws, prox, status="ok", **m)
    if ru is None:
        return rec, None
    cpu = ru.ru_utime + ru.ru_stime
    return rec, {"base_uuid": uuid.uuid4().hex[:12],
                 "rss_c": ru.ru_maxrss * 1024, "wall_s": round(wall, 3),
                 "u_c": cpu / max(wall, 1e-6), "cons": m["r1cs_cons"],
                 "prove_ms": m["prove_ms"], "utime": round(ru.ru_utime, 3),
                 "stime": round(ru.ru_stime, 3)}


def load_partial_wrapped():
    """RZ _load_partial plus R2 restore, rule 2 and rule 3."""
    a = ARGS
    sweep = Pair(rz.PARTIAL, rz.PARTIAL_DOCS)
    sample = pair_names(a)[1]
    if not S.get("rule2_done") and rule2(sweep, sample):   # ALL_T1009: once
        say("SAME rule 2: sweep partial absent, deleting %s and %s"
            % (sample.tmp, sample.docs))
        sample.delete()
        S["rows"] = []
    sweep.restore()
    sample.restore()
    done = _ORIG["load"]()
    retry_once(done, sweep)                   # ALL_T1013 F7
    for u, size in sorted(S.get("force_redo", ())):   # ALL_T1013 V12
        if done.pop("%s|%d" % (u, size), None) is not None:
            say("SAME note: %s %d redone (a dropped partial line named it)"
                % (u, size))
    sigs = {r.get("launch_sig") for r in done.values()}   # ALL_T1013 F12
    if len(sigs) > 1 or sigs - {S.get("sig")}:
        say("SAME note: kept sweep rows carry %d launch_sig value(s) (%s); "
            "this run is %s" % (len(sigs), ", ".join(
                (x or "none")[:12] for x in sorted(sigs, key=str)),
                (S.get("sig") or "")[:12]))
    for size in a.sizes:
        comp = complete_units(S["rows"], size, a.n, S["er"])
        for k in list(done):
            u, sz = k.rsplit("|", 1)
            if (int(sz) == size and done[k].get("status") == "ok"
                    and u not in comp):
                del done[k]
    return done


def append_partial_wrapped(rec):
    if STOP.is_set():                         # DLP_T1001 m9: no GIVEN UP rows
        return
    rec["launch_sig"] = S.get("sig")          # ALL_T1013 F12
    return _ORIG["append"](rec)


def render_wrapped(orig, sizes):
    """RZ render plus the zreal fn and policy_real_<N> arms."""
    text = _ORIG["render"](orig, sizes)
    fn, arm = ARM_T.split("\n//@@ARM\n")
    if text.count(ZK_ANCHOR) != 1:
        raise SystemExit("zkmb.rs: expected one %r" % ZK_ANCHOR.strip())
    text = text.replace(ZK_ANCHOR, fn + "\n\n" + ZK_ANCHOR)
    block = (ZREAL_BEGIN + "\n" + "\n".join(arm.replace("{n}", str(n))
                                            for n in sizes) + "\n" +
             ZREAL_END + "\n")
    return text.replace(rz.ARM_ANCHOR, block + rz.ARM_ANCHOR)


def run_pipeline_wrapped(binp, str_len, names, done):
    S["binp"] = binp
    S["cur_size"] = str_len                   # ALL_T1009: for batch lines
    res = _ORIG["pipeline"](binp, str_len, names, done)
    flush()
    try:
        size_notes(str_len, res, done)        # ALL_T1017 b/c
    except Exception as e:
        say("SAME note: size notes skipped: %s" % e)
    if ARGS.scalecal and str_len == 1000:
        try:
            scalecal()
        finally:
            for it in S["keep"]:
                _ORIG["rmtree"](it["dir"], ignore_errors=True)
            del S["keep"][:]
    return res


def size_notes(str_len, res, done):
    """ALL_T1017 b/c: calib per constraint count, growth factor, the not-fit
    list, and after the second-largest size the largest-size prediction.
    res holds resumed rows, so every launch prints them. A later launch that
    only KEEPs the leaf copies no note; the docs log still shows not_fit."""
    by = {}
    for r in res:
        if _okv(r, "peak_rss") and r.get("r1cs_cons"):
            by.setdefault(r["r1cs_cons"], []).append(r["peak_rss"])
    for c, v in sorted(by.items()):
        say("SAME note: calib size=%d cons=%d units=%d rss median/max=%s/%s"
            % (str_len, c, len(v), _gib(statistics.median(v)), _gib(max(v))))
    say("SAME note: growth factor at %d B is %.3f over %d rows"
        % ((str_len,) + growth_factor(done, str_len)))
    nf = sorted(r["regex_name"] for r in res if r.get("status") == "not_fit")
    if nf:
        say("SAME note: units over the address-space cap at %d B: %s"
            % (str_len, ", ".join(nf)))
    vs = sorted(rz.VEC_SIZE)
    if len(vs) > 1 and str_len == vs[-2] and S.get("full_mem"):
        predict_next(vs[-1], [r["regex_name"] for r in res], done)


def predict_next(L, names, done):
    """ALL_T1017 b: keygen RSS prediction at the largest size L."""
    full = S["full_mem"]
    slope = rz._calib_slope(done, "peak_rss", rz.EST_SLOPE_BYTES_PER_CONS)
    est = sorted(((rz._estimate(n, L, done, slope, "peak_rss", 0), n)
                  for n in names), reverse=True)
    if not est:
        return
    over = ["%s %s" % (n, _gib(v)) for v, n in est if v > full]
    say("SAME note: %d B keygen prediction: largest %s %s; %d unit(s) above "
        "the %s address-space cap" % (L, est[0][1], _gib(est[0][0]),
                                      len(over), _gib(full)))
    if over:
        say("SAME WARNING: %d B keygen predicted above the %s address-space "
            "cap: %s" % (L, _gib(full), ", ".join(over)), caveat=True)


# ALL_T1009 N1/O2: rayon thread arena + stack room in the keygen AS cap
AS_THREAD_B = 66 * 2 ** 20     # ALL_T1009: 8.2 GiB at 128 threads [M laptop]
AS_THREAD_MAX = 4 * AS_THREAD_B


def arena_room():
    return len(os.sched_getaffinity(0)) * S.get("arena_b", AS_THREAD_B)


def as_cap_wrapped(est_rss, full_mem):
    """ALL_T1009 N1: RZ's keygen cap plus the arena room of its prove."""
    cap = _ORIG["as_cap"](est_rss, full_mem)
    if not cap:
        return cap
    S["cap_room"] = room = arena_room()       # ALL_T1009: room used at cap time
    return int(min(full_mem, cap + room))


def sync_scratch():
    """ALL_T1013 F9/V13: syncfs the scratch fs, and the partial and log fs
    when they are other mounts; os.sync only as a fallback."""
    try:
        import ctypes
        libc = ctypes.CDLL(None, use_errno=True)
        devs = []
        for p in (rz.PAR_ROOT, rz.PARTIAL_DIR, S.get("logdir")):
            if not p or not os.path.isdir(p):
                continue
            dev = os.stat(p).st_dev
            if dev in devs:
                continue
            fd = os.open(p, os.O_RDONLY)
            try:
                if libc.syncfs(fd) != 0:
                    raise OSError(ctypes.get_errno(), "syncfs %s" % p)
            finally:
                os.close(fd)
            devs.append(dev)
        if not devs:
            raise OSError(errno.ENOENT, "no fs to sync")
        return "syncfs=%d" % len(devs)
    except Exception:
        os.sync()
        return "sync"


class BatchTPE(ThreadPoolExecutor):
    """ALL_T1009 N2: rz.ThreadPoolExecutor that records the batch size."""

    def __init__(self, *args, **kw):
        n = kw.get("max_workers", args[0] if args else None)
        S["batch_n"] = S["last_batch_n"] = n   # ALL_T1013 FI3: kept for timing
        S["batch_seq"] = S.get("batch_seq", 0) + 1
        try:
            say("SAME batch t=%s size=%s jobs=%s" % (
                _stamp(), S.get("cur_size", "-"), n))
        except Exception:
            pass
        super().__init__(*args, **kw)

    def __exit__(self, *exc):
        S.pop("batch_n", None)
        r = super().__exit__(*exc)            # ALL_T1009: all keygens returned
        if exc[0] is None:                    # ALL_T1009 A4: sync before timing
            t0 = time.time()
            how = sync_scratch()
            say("SAME sync t=%s wall=%.1fs %s" % (_stamp(), time.time() - t0,
                                                  how))
        return r


# ALL_T1009: rayon pool-build failure texts inside RZ's err[-300:] tail
_ARENA_SIG = ("ThreadPoolBuildError", "Resource temporarily unavailable")
_ARENA_LOCK = threading.Lock()


def arena_failure(err):
    """ALL_T1009: a rayon pool failure, not a plain large allocation."""
    return "rayon-core" in err and any(x in err for x in _ARENA_SIG)


def tasks_short():
    """ALL_T1009: free tasks below twice a full batch of keygen threads."""
    av = tasks_free()
    jobs = S.get("batch_n") or 1
    return av is not None and av < 2 * jobs * (len(os.sched_getaffinity(0)) + 4)


def _gib(v):
    return "%.1fGiB" % (v / GIB) if v else "-"


def _est_txt(mem, room, lone):
    """ALL_T1009: the RAM reservation read back from RZ's cap rule."""
    if not mem or lone:
        return "-"
    if mem >= (S.get("full_mem") or float("inf")):
        return "full"
    part = mem - room
    if part <= 8 * GIB:
        return "<=%.1fGiB" % (8 / rz.EST_AS_MARGIN)
    return _gib(part / rz.EST_AS_MARGIN)


def _after_build(b, name, str_len, mem, lone, room, wall):
    """ALL_T1009 B1/O2/m4: log one keygen, learn the arena room."""
    st, err = b.get("status"), b.get("err") or ""
    est, fit = _est_txt(mem, room, lone), ""
    tried = S.setdefault("tried", set())      # ALL_T1017 b: first attempt only
    if (st == "built" and (name, str_len) not in tried and est[:1].isdigit()
            and b.get("peak_rss")):
        part = (mem - room) / rz.EST_AS_MARGIN
        fit = " est=%s err=%+.0f%%" % (_gib(part),
                                       100.0 * (b["peak_rss"] / part - 1))
    tried.add((name, str_len))
    say("SAME build t=%s size=%d %s -> %s wall=%.0fs rss=%s res=%s cap=%s%s%s"
        % (_stamp(), str_len, name, st, wall, _gib(b.get("peak_rss")),
           est, _gib(mem), " lone" if lone else "",
           fit if st == "built" else " err=" + err[-80:].replace("\n", " ")))
    if not mem or lone or b.get("as_cap") != mem or st == "built":
        return
    rss_part = max(1, mem - room)
    rss = b.get("peak_rss")
    if arena_failure(err) and rss and rss < rss_part and not tasks_short():
        with _ARENA_LOCK:                     # ALL_T1009: once per batch
            old = S.get("arena_b", AS_THREAD_B)
            if S.get("arena_seq") != S.get("batch_seq") and old < AS_THREAD_MAX:
                S["arena_b"], S["arena_seq"] = min(AS_THREAD_MAX, 2 * old), \
                    S.get("batch_seq")
                say("SAME note: arena room raised to %d MiB per thread"
                    % (S["arena_b"] >> 20))
    b["as_cap"] = rss_part      # ALL_T1009: RZ's retry backs off from RSS only


KEY_PARTS = ("inst", "gens", "input_names", "term_arr", "input_idxes",
             "var_idxes")
KILL_WAIT_S = 120                 # ALL_T1017 d: wait for killed keygen pids
NOT_FIT_RE = re.compile(r"memory allocation of (\d+) bytes failed")


def _not_fit(b, name, str_len, mem, lone, room):
    """ALL_T1017 c: a lone keygen's own allocation failure near the full
    address-space cap is deterministic, so not_fit, never retried. A bare
    signal death (kernel OOM, cgroup, operator) keeps oom_or_killed."""
    m = NOT_FIT_RE.search(b.get("err") or "")
    if not (lone and m and mem and b.get("status") in ("oom_or_killed",
                                                       "build_fail")):
        return
    n = int(m.group(1))
    if n > meminfo("MemTotal") or (b.get("peak_rss") or 0) + n < 0.8 * (
            mem - room):
        return
    pre = "exceeds the %s address-space cap (0.9 x MemTotal); " % _gib(mem)
    b["status"] = "not_fit"
    b["err"] = pre + (b.get("err") or "")[-(300 - len(pre)):]
    say("SAME FAIL-FAST: %s at %d B exceeds the %s address-space cap "
        "(0.9 x MemTotal); the rest of this size goes on"
        % (name, str_len, _gib(mem)), caveat=True)


def _kill_cwd(d):
    """ALL_T1013 F1: kill our circ_executable left running in work dir d."""
    out, gone = [], []
    for pid in _pids():
        if pid == os.getpid() or not _owned(pid):
            continue
        if _exe_base(pid) != "circ_executable" or _cwd_of(pid) != d:
            continue
        for c in descendants(pid):
            _sigkill(c)
            gone.append(c)
        _sigkill(pid)
        out.append(pid)
    t_end = time.time() + KILL_WAIT_S         # ALL_T1017 d: no overlap after
    while any(_alive(p) for p in out + gone) and time.time() < t_end:
        time.sleep(POLL_S)
    return out


def _keys_missing(d, str_len):
    """ALL_T1013 R1: RZ's keys dir exists but a key file is absent or empty."""
    kd = os.path.join(d, "keys")
    if not os.path.isdir(kd):
        return False
    for part in KEY_PARTS:
        try:
            if os.path.getsize(os.path.join(kd, "policy%d_%s" % (
                    str_len, part))) == 0:
                return True
        except OSError:
            return True
    return False


def _post_build(b, str_len):
    """ALL_T1013 F1/R1: no keygen outlives its timeout; no keyless build."""
    st, d = b.get("status"), b.get("dir")
    if st == "build_timeout" and d:
        for pid in _kill_cwd(os.path.realpath(d)):
            say("SAME note: killed timed-out keygen pid %d (cwd %s)" % (pid, d))
    elif st == "built" and d and _keys_missing(d, str_len):
        b["status"] = "build_fail"
        b["err"] = "keygen wrote no keys (arm missing?)"


def run_keygen_wrapped(cmd, cwd, timeout=rz.PROVE_TIMEOUT):
    """ALL_T1013 S3: keys only; RZ never read the zero-witness prove that
    followed them. Same zkmb_generate_keys call, paths and .zok."""
    cmd = list(cmd)
    i = len(cmd) - 3
    if (i >= 0 and re.match(r"policy_\d+$", cmd[i])
            and cmd[i + 1:] == ["true", "prover"]):
        cmd[i] = "policy_keys_" + cmd[i][len("policy_"):]
    return _ORIG["run_keygen"](cmd, cwd, timeout)


def build_one_wrapped(binp, idx, name, str_len, mem_bytes=None,
                      timeout=rz.PROVE_TIMEOUT):
    """ALL_T1009 B1/N2: full headroom when alone, then log the keygen."""
    lone = S.get("batch_n") == 1 and bool(S.get("full_mem"))
    if lone:
        mem_bytes = S["full_mem"]
    room, t0 = S.get("cap_room", arena_room()), time.time()
    try:
        b = _ORIG["build"](binp, idx, name, str_len, mem_bytes, timeout)
    except OSError as e:                      # ALL_T1013 F8: RZ retries it
        b = {"name": name, "prox": None,
             "dir": os.path.join(rz.PAR_ROOT, "c%05d" % idx),
             "status": ("disk_full" if e.errno in (errno.ENOSPC, errno.EDQUOT)
                        else "build_fail"),
             "err": ("%s: %s" % (type(e).__name__, e))[-300:]}
    try:
        _post_build(b, str_len)
    except Exception as e:                    # ALL_T1013: never end the batch
        say("SAME note: post-build check failed: %s" % e)
    try:
        _not_fit(b, name, str_len, mem_bytes, lone, room)    # ALL_T1017 c
    except Exception as e:
        say("SAME note: not_fit check failed: %s" % e)
    try:
        _after_build(b, name, str_len, mem_bytes, lone, room, time.time() - t0)
    except Exception:
        pass
    return b


# ALL_T1009 B2/N3/B3: growth-aware keygen estimates and job count
GROWTH_K_DEFAULT = math.log2(5.0)  # ALL_T1009: top laptop 1->2 KB RSS ratio [M]
K_MIN, K_MAX = 1.0, 3.0            # ALL_T1009: 2x to 8x per doubling


def _okv(r, vkey):
    return bool(r) and r.get("status") == "ok" and bool(r.get(vkey))


def _pooled_k(done, vkey, s, L):
    """ALL_T1009: exponent k in v(L)/v(s) = (L/s)**k over measured units."""
    key = (id(done), vkey, s, L, len(done))
    memo = S.setdefault("k_memo", {})
    if key in memo:
        return memo[key]

    def ks(a, b):
        out = []
        for r in list(done.values()):
            q = done.get("%s|%d" % (r.get("regex_name"), a))
            if r.get("str_len") == b and _okv(r, vkey) and _okv(q, vkey):
                out.append(math.log(r[vkey] / q[vkey]) / math.log(b / a))
        return out
    k = ks(s, L)
    if len(k) < 3:
        vs = sorted(rz.VEC_SIZE)
        k = [x for a, b in zip(vs, vs[1:]) for x in ks(a, b)]
    if len(k) < 3:
        v = GROWTH_K_DEFAULT if vkey == "peak_rss" else 1.0
    elif vkey == "peak_rss":                  # ALL_T1009: max(median, p75)
        sk = sorted(k)
        v = max(statistics.median(sk), sk[int(math.ceil(0.75 * len(sk))) - 1])
    else:
        v = statistics.median(k)
    memo[key] = v = min(K_MAX, max(K_MIN, v))
    return v


def estimate_wrapped(name, str_len, done, slope, vkey, floor):
    """ALL_T1009 B2: raise RZ's estimate by own or pooled growth, never lower."""
    e = _ORIG["estimate"](name, str_len, done, slope, vkey, floor)
    r = done.get("%s|%d" % (name, str_len))
    if r and r.get(vkey):
        return e
    if (vkey == "peak_rss" and e == floor and _ORIG.get(
            "median_at", rz._median_at)(done, str_len, vkey) is None):
        e = max(e, rz_cold())                 # ALL_T1009 A5: RZ's own cold
    v = own_growth(name, str_len, done, vkey)[0]
    if v is None:
        return e
    if vkey == "peak_rss":                    # ALL_T1017 a: F1 factor
        v = int(v * growth_factor(done, str_len)[0])
    return max(e, v)


def own_growth(name, str_len, done, vkey):
    """ALL_T1009 B2 loop: (value, own) grown from the nearest smaller size;
    own is True when the exponent is the unit's own (ALL_T1017 a)."""
    smaller = sorted((x for x in rz.VEC_SIZE if x < str_len), reverse=True)
    for i, s in enumerate(smaller):
        rr = done.get("%s|%d" % (name, s))
        if not (rr and rr.get(vkey)):
            continue
        k = None
        if i + 1 < len(smaller):
            q = done.get("%s|%d" % (name, smaller[i + 1]))
            if _okv(rr, vkey) and _okv(q, vkey):
                k = min(K_MAX, max(K_MIN, math.log(rr[vkey] / q[vkey])
                                   / math.log(s / smaller[i + 1])))
        own = k is not None
        if k is None:
            k = _pooled_k(done, vkey, s, str_len)
        return int(rr[vkey] * (str_len / s) ** k), own
    return None, False


GF_MIN_ROWS, GF_FLOOR_ROWS = 3, 6  # ALL_T1017 F1: rows to fit, rows to go <1
GF_FLOOR, GF_MAX = 0.95, 2.0


def growth_factor(done, str_len):
    """ALL_T1017 a: (p75 of measured / own-grown keygen RSS over ok rows at
    str_len with an own exponent, rows); 1.0 below 3 rows, >= 0.95 only from
    6 rows, else >= 1.0; at most 2.0."""
    key = (id(done), str_len, len(done))
    memo = S.setdefault("gf_memo", {})
    if key not in memo:
        q = []
        for r in list(done.values()):
            if r.get("str_len") == str_len and _okv(r, "peak_rss"):
                v, own = own_growth(r.get("regex_name"), str_len, done,
                                    "peak_rss")
                if own and v:
                    q.append(r["peak_rss"] / v)
        q.sort()
        f = q[int(math.ceil(0.75 * len(q))) - 1] if len(q) >= GF_MIN_ROWS \
            else 1.0
        lo = GF_FLOOR if len(q) >= GF_FLOOR_ROWS else 1.0
        memo[key] = (min(GF_MAX, max(lo, f)), len(q))
    return memo[key]


def median_at_wrapped(done, str_len, vkey):
    """ALL_T1009 N3: nearest-rank p90 of the measured keygen RSS."""
    if vkey != "peak_rss":
        return _ORIG["median_at"](done, str_len, vkey)
    vals = sorted(r[vkey] for r in list(done.values())
                  if r.get("str_len") == str_len and r.get(vkey))
    return vals[int(math.ceil(0.9 * len(vals))) - 1] if vals else None


def cpu_max_jobs():
    """ALL_T1009 B3: one keygen per 2 cpus of our affinity, task-capped."""
    n = max(1, len(os.sched_getaffinity(0)) // rz.MIN_CPUS_PER_CIRC)
    cap = S.get("jobs_cap")
    return max(1, min(n, cap)) if cap else n


_RZ_CPU_MAX_JOBS = rz._cpu_max_jobs     # ALL_T1009: RZ's own, before overrides
_RZ_MIN_CPUS = rz.MIN_CPUS_PER_CIRC      # ALL_T1009: RZ's own 4 cpus per job


def rz_cold():
    """ALL_T1009 A5: RZ's own cold reservation (budget / (cpu_count // 4))."""
    jobs = max(1, (os.cpu_count() or _RZ_MIN_CPUS) // _RZ_MIN_CPUS)
    return max(int((rz._ram_budget_bytes() or 0) / jobs),
               rz.COLD_RAM_FLOOR_BYTES)


def _hook(name, key, wrapper):
    """ALL_T1009: wrap rz.<name>; a second install keeps the first original."""
    if getattr(rz, name) is not wrapper:
        _ORIG[key] = getattr(rz, name)
    setattr(rz, name, wrapper)


def install_rz_hooks():
    _ORIG.update(rmtree=shutil.rmtree)
    rz.shutil = ShutilProxy()
    rz._time_one = time_one
    # ALL_T1009: identity-guarded, so a second install never recurses
    _hook("_load_partial", "load", load_partial_wrapped)
    _hook("_append_partial", "append", append_partial_wrapped)
    _hook("_render_zkmb", "render", render_wrapped)
    _hook("run_pipeline", "pipeline", run_pipeline_wrapped)
    _hook("_as_cap", "as_cap", as_cap_wrapped)          # ALL_T1009 N1
    _hook("_build_one", "build", build_one_wrapped)     # ALL_T1009 B1/N2
    _hook("_run_keygen", "run_keygen", run_keygen_wrapped)  # ALL_T1013 S3
    rz.ThreadPoolExecutor = BatchTPE                    # ALL_T1009 N2
    _hook("_estimate", "estimate", estimate_wrapped)    # ALL_T1009 B2
    _hook("_median_at", "median_at", median_at_wrapped)  # ALL_T1009 N3
    rz.MIN_CPUS_PER_CIRC = 2                  # ALL_T1009 B3: 1-thread keygen
    if rz._cpu_max_jobs is _RZ_CPU_MAX_JOBS:  # ALL_T1009: override wins
        rz._cpu_max_jobs = cpu_max_jobs


# ===========================================================================
# scalecal (dry, 1 KB)
# ===========================================================================
def in_run_scalecal():
    """Full run without a valid PASS: key one 1 KB pool unit (median .regex
    size of the dry pool) and run scalecal on it (DLP_T1001 round 4)."""
    rs = ruleset()
    rz.FULL_DIR = rs
    names = dz.evenly_spaced_subset(dz.under_size_cap(
        rs, rz.list_policy_names(rs), dz.DRY_MAX_REGEX_BYTES), 4)
    if not names:
        say("SCALECAL SKIP no pool unit")
        return
    name = sorted(names, key=lambda n: (dz.regex_bytes(rs, n), n))[
        (len(names) - 1) // 2]
    old, root = rz.PAR_ROOT, os.path.join(rz._pick_scratch_base(),
                                          "same_scalecal_%d" % os.getpid())
    rz.PAR_ROOT = root
    os.makedirs(root, exist_ok=True)
    try:
        b = rz._build_one(S["binp"], 0, name, 1000, rz._mem_cap_bytes(1))
        base = None
        if b["status"] == "built":
            base = base_time(S["binp"], b, 1000, rz._mem_cap_bytes(1))[1]
        if base is None:
            say("SCALECAL SKIP keygen or base of %s: %s" % (name, b["status"]))
            return
        S["keep"] = [{"unit": name, "size": 1000, "dir": b["dir"],
                      "base": base}]
        scalecal()
    finally:
        rz.PAR_ROOT = old
        _ORIG["rmtree"](root, ignore_errors=True)
        S["keep"] = []
        S["exit6"] = None                     # a FAIL here is not exit 6


def full_start(a, rows):
    """Full-mode start: run scalecal first when no valid PASS exists and the
    box is big enough, then the start check (DLP_T1001 round 4)."""
    _st, ok, why = best_scalecal(a.server)
    if not ok and S["topo"]["c_cores"] >= a.scalecal_min_cores:
        say("SCALECAL in full run: no valid PASS (%s)" % why)
        t0 = time.time()
        try:
            in_run_scalecal()
        except Exception as e:                # a crash is a scalecal FAIL
            say("SCALECAL FAIL (crash in the full-run speed check: %s: %s)\n%s"
                % (type(e).__name__, e, traceback.format_exc()), caveat=True)
            for r in list(S["running"]):      # DLP_T1001 M3: none outlive it
                kill_proc(r, "stop")
                reap(r, block=True)
            del S["running"][:]
        S["scal_tried"] = True
        say("SCALECAL in full run took %.0f s" % (time.time() - t0))
    return start_check(a, rows)


def scalecal_widths(topo, cap):
    """ALL_T1013 S5: the full-run ladder up to the cap; cap 0 keeps the old
    ladder up to 4 (DLP_T1001)."""
    if not cap:
        return [w for w in (1, 2, 4) if w <= min(4, node_slot_cores(topo))]
    return ladder(topo, cap)


def scalecal():
    a = ARGS
    topo = S["topo"]
    if topo["c_cores"] < a.scalecal_min_cores:
        say("SCALECAL SKIP C_cores=%d" % topo["c_cores"])
        return
    commit0 = git_head()
    dirty0 = git_status(LIST_TIMING)
    t0 = S["t_start"]
    pool = [it for it in S["keep"] if it["size"] == 1000]
    if not pool:
        say("SCALECAL SKIP no 1 KB pool unit")
        return
    pool.sort(key=lambda it: (it["base"]["cons"], it["unit"]))
    it = pool[(len(pool) - 1) // 2]
    S["in_scal"] = True
    try:
        _scalecal_body(a, topo, commit0, dirty0, t0, it)
    finally:
        S["in_scal"] = False


def _scalecal_body(a, topo, commit0, dirty0, t0, it):
    """scalecal() after the pool pick; its rows carry scal=1."""
    # DLP_T1001: the first 4 unlisted 1 KB e-mails, whatever --n is
    tasks = [t for t in build_tasks([it], n=len(read_ids())) if not t.er]
    tasks = sorted(tasks, key=lambda t: t.eid)[:4]
    why = fx_check([1000], max(4, a.n))
    if why or len(tasks) < 4:
        say("SCALECAL SKIP %s" % (why or "fewer than 4 unlisted e-mails"))
        return
    ref, s = serial_reference(tasks)
    if ref:
        tasks = [t for t in tasks if id(t) in ref]
    else:
        ref = None
    rows, w0 = [], None
    for w in scalecal_widths(topo, S["cap"]):
        n = len(make_slots(topo, w))
        B = memavail() - S["R"]
        n = min(n, max(1, int(B // max(1, tasks[0].cap))))
        copies = [Task(t.unit, t.size, t.eid, t.epath, t.dir, t.base, False)
                  for i in range(n) for t in [tasks[i % len(tasks)]]]
        idx = {id(c): id(tasks[i % len(tasks)]) for i, c in enumerate(copies)}
        if ref is None:
            g, tau, ok = float("inf"), 0.0, False
        else:
            pk = Packed(1000, -1, w, B, n, "scalecal", copies, mode="scalecal")
            try:
                pk.run(list(copies))
            except MemStop as e:              # a width that cannot launch
                say("SCALECAL w=%d: %s" % (w, e))
            ms = [(v, ref[idx[id(c)]]) for c, v in pk.pair_ms.items()]
            if len(ms) < n or any(not isinstance(v, int)   # ALL_T1013 F16
                                  for v, _ in ms):
                g, tau, ok = float("inf"), 0.0, False
            else:
                g = math.exp(sum(math.log(v / rf) for v, rf in ms) / len(ms))
                tau = GATE_TAU
                ok = g <= tau
        if ok and w0 is None:
            w0 = w
        rows.append({"w": w, "slots": len(make_slots(topo, w)), "copies": n,
                     "g": "%.4f" % g if g != float("inf") else "inf",
                     "s": "%.4f" % (s or 0), "tau": "%.4f" % tau,
                     "verdict": "PASS" if ok else "FAIL"})
        say("SCALECAL w=%d copies=%d g=%s tau=%.3f -> %s" % (
            w, n, rows[-1]["g"], tau, rows[-1]["verdict"]))
    overall = "PASS" if w0 is not None else "FAIL"
    head = git_head()
    st = {"w0": w0 or "", "overall": overall, "kind": "zombie_timing",
          "commit": commit0 or "", "dirty": "false" if dirty0 == "" else "true",
          "head_moved": "false" if head == commit0 else "true",
          "host": socket.gethostname(), "fingerprint": S["fp"],
          "mode": "dry" if a.dry is not None else "full",
          "t_leaf_start": "%.3f" % t0, "rc": 0 if w0 else 6,
          "zombie_inputs_sha256": zombie_inputs_sha256(),
          "launch_sig": S["sig"]}
    text = "\t".join(SCAL_COLS) + "\n" + "".join(
        "\t".join(str(dict(r, **st).get(c, "")) for c in SCAL_COLS) + "\n"
        for r in rows)
    dry = a.dry is not None                   # DLP_T1001: dry never hits full
    for p in (scalecal_path(a.server, dry),
              os.path.join(DOCS, scalecal_name(dry))):
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p + ".tmp", "w") as f:
            f.write(text)
        os.replace(p + ".tmp", p)
    if w0 is not None:
        say("SCALECAL PASS w0=%d" % w0)
    else:
        say("SCALECAL FAIL")
        S["exit6"] = "SCALECAL FAIL"


# ===========================================================================
# TSV
# ===========================================================================
def write_tsv():
    """Rebuild the TSV from the sample partial (every exit)."""
    tsv = out_paths()[0]
    rows = pair_names(ARGS)[1].load()
    base, gates = index_rows(rows)
    lines = ["\t".join(TSV_COLS)]
    for r in rows:
        if r.get("kind") != "prove" or r.get("scal"):
            continue
        d = dict(r, accepted=int(is_accepted(r, base, gates)))
        lines.append("\t".join("" if d.get(c) is None else str(d.get(c))
                               for c in TSV_COLS))
    os.makedirs(os.path.dirname(tsv), exist_ok=True)
    with open(tsv + ".tmp", "w") as f:
        f.write("\n".join(lines) + "\n")
    os.replace(tsv + ".tmp", tsv)


def summary():
    rows = S["rows"]
    for size in ARGS.sizes:
        comp = complete_units(rows, size, ARGS.n, S["er"])
        units = {r["unit"] for r in rows if r["kind"] == "base"
                 and r["size"] == size}
        say("SAME summary size=%d units=%d complete=%d%s" % (
            size, len(units), len(comp & units),
            " serial" if size in S["serial"] else ""))
    n_er = sum(1 for r in rows if r["kind"] == "prove"
               and r.get("expected_reject"))
    say("SAME expected-reject pairs %d, prover-confirmed %d" % (
        len(S["er"]), n_er))
    for n in S["notes"]:
        say("SAME note: %s" % n)
    for f in S["fails"]:
        say("SAME failing pair: %s" % f)


# ===========================================================================
# main
# ===========================================================================
def parse_args(argv):
    ap = argparse.ArgumentParser(
        description="DLP_T1001 same-sample Zombie",
        epilog="Gate: packed/serial prove-time ratio g must be <= %.2f. "
        "ZKR_SAME_MAX_WIDTH_CORES: gate widening cap in physical "
        "cores, default %d; 0 = serial allowed at every size. %s"
        % (GATE_TAU, CAP_DEFAULT, OUTER_SCOPE))
    ap.add_argument("--sizes", default="1000,2000,4000")
    ap.add_argument("--n", type=int, default=32)
    ap.add_argument("--server", default="jet1tb")
    ap.add_argument("--dry", type=int, default=None)
    ap.add_argument("--only-same", action="store_true")
    ap.add_argument("--scalecal", action="store_true")
    ap.add_argument("--scalecal-min-cores", type=int, default=32)
    ap.add_argument("--start-check-min-cores", type=int, default=32)
    ap.add_argument("--check-start", action="store_true")
    ap.add_argument("--slot-cores", type=int, default=1)
    ap.add_argument("--keep-free", type=int, default=4)
    ap.add_argument("--reserve-floor", type=int, default=64)
    ap.add_argument("--launcher", choices=("auto", "prlimit"), default="auto")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--build-only", action="store_true")   # ALL_T1013 S9
    a = ap.parse_args(argv)
    a.sizes = [int(x) for x in a.sizes.split(",") if x]
    return a


def parse_cap():
    v = os.environ.get("ZKR_SAME_MAX_WIDTH_CORES", str(CAP_DEFAULT))
    if not re.match(r"^\d+$", v.strip()):
        return None
    return int(v)


def init_state(a):
    S.clear()
    S.update(rows=[], pending=[], defer={}, keep=[], running=[], attempts={},
             notes=[], fails=[], serial=set(), w_state={}, gates={}, k=0,
             launch_consec=0, launcher="prlimit", props=[], exit6=None,
             t_start=time.time(), binp=None, refused={},
             refused_prior=set())
    S["topo"] = topology(a.keep_free)
    S["fp"] = fingerprint()
    S["commit"] = git_head() or ""
    S["ids_sha"] = sha256_file(os.path.join(FX, "ids.tsv"))
    S["list_sha"] = sha256_file(os.path.join(FX, "zombie_expected_reject.tsv"))
    S["er"] = read_expected_reject()
    S["sig"] = launch_sig(S["topo"]["tpc"], a)
    S["cap"] = parse_cap()
    S["R"] = max(a.reserve_floor * GIB, meminfo("MemTotal") // 10)
    S["full_mem"] = rz._mem_cap_bytes(1)


def clone_check():
    """RZ builds a copy of zombie/circ in rz.BUILD_ROOT; both need the
    source module circ/src/target/ (DLP_T1001 fix5)."""
    mod = os.path.join("src", "target", "mod.rs")
    if not os.path.isfile(os.path.join(MS_DLP, rz.CLONE_CIRC, mod)):
        return ("zombie clone incomplete (%s/%s missing): run "
                "scripts/download_zombie.py" % (rz.CLONE_CIRC, mod))
    if os.path.isdir(rz.CIRC_BUILD) and not os.path.isfile(
            os.path.join(rz.CIRC_BUILD, mod)):
        return ("stale circ build copy %s lacks %s: delete %s so run_zombie "
                "re-copies it" % (rz.CIRC_BUILD, mod, rz.BUILD_ROOT))
    return None


def same_units_running():
    r = sctl("list-units", "--plain", "--no-legend", "--state=running",
             "same-*")
    return bool(r is not None and r.stdout.strip())


# ALL_T1009 A6: hour-0 host checks (refuse or adapt there, never at hour 107)
SCRATCH_REFUSE_GIB = rz.SCRATCH_MIN_FREE_GB  # ALL_T1009: 10x a 4 KB key set [M]
SCRATCH_WARN_GIB = 250       # ALL_T1009: a full 4 KB batch writes 80-110 GiB [E]
PIDS_SLACK = 2000                # ALL_T1009: d3 value


def cores_refusal():
    if S["topo"]["c_cores"] < 1 and S["cap"] != 0:
        return ("no slot cores left after keep-free %d (C_cores 0); set "
                "ZKR_SAME_MAX_WIDTH_CORES=0 for serial mode" % ARGS.keep_free)
    return None


def circ_rebuild_needed(a):
    """ALL_T1009: RZ's own rebuild rule (RZ:565-571), read only."""
    sizes = dz.DRY_VEC_SIZE if a.dry is not None else rz.VEC_SIZE
    if not (os.path.isfile(rz.CIRC_BIN) and os.path.isfile(rz.BUILD_RS_ORIG)):
        return True
    if rz._render_zkmb is not render_wrapped:
        _ORIG["render"] = rz._render_zkmb
    try:
        return rz._read(rz.BUILD_RS) != render_wrapped(
            rz._read(rz.BUILD_RS_ORIG), sizes)
    except (OSError, SystemExit):
        return True


def nightly_refusal(a):
    from download_zombie import have_rust_nightly
    ok, why = have_rust_nightly()
    if ok:
        return None
    if not circ_rebuild_needed(a):            # ALL_T1009: no build at the leaf
        say("CAVEAT: SAME check-start WARNING: the pinned Rust nightly is "
            "missing (%s), but circ_executable needs no rebuild" % why)
        return None
    return ("the pinned Rust nightly for circ is missing (%s) and circ needs a "
            "rebuild: run python3 scripts/INSTALL.py --data zombie" % why)


def selftest_refusal():
    try:
        selftest()
    except AssertionError as e:
        return "selftest failed: %s" % e
    return None


def sweep_refusal(a):
    """ALL_T1009: RZ's hour-107 resume load, read only, on PD's .hold view."""
    sweep = pair_names(a)[0]
    for p in (sweep.tmp, sweep.docs):
        src = p + ".hold" if os.path.exists(p + ".hold") else p
        if not os.path.isfile(src) or os.path.getsize(src) == 0:
            continue
        try:
            rows = Pair(src, src).load()
        except ValueError as e:
            return "sweep partial %s has a bad line (%s): repair or delete it" % (
                src, e)
        bad = [r for r in rows if not isinstance(r, dict)
               or "regex_name" not in r or "str_len" not in r
               or r.get("zok_gen") != rz.ZOK_GEN]
        if bad:
            return ("sweep partial %s holds %d rows run_zombie cannot resume "
                    "(no regex_name/str_len, or zok_gen not %s): delete %s and "
                    "%s to re-measure" % (src, len(bad), rz.ZOK_GEN, sweep.tmp,
                                          sweep.docs))
    return None


def _fs_dev(p):
    try:
        return os.stat(p).st_dev
    except OSError:
        return None


def pick_scratch():
    """ALL_T1013 K13: RZ's scratch rule (writable local fs with the most
    free space, at least SCRATCH_MIN_FREE_GB) over RZ's mount roots plus the
    clone's own fs at <ms_dlp>/bora_zombie_scratch. One candidate per fs: the
    clone dir first, so a K14 bind mount (/tmp/bora, /tmp/bora_zombie_par) of
    the clone's fs never stands in for it. Under the C1 redirect only
    rz.PAR_ROOT."""
    if TMP_ROOT:
        return rz.PAR_ROOT
    best, best_free, seen = None, -1.0, set()
    for mp, base in ([(MS_DLP, CLONE_SCRATCH)]   # ALL_T1013 K15: clone first
                     + [(m, os.path.join(m, "bora_zombie_scratch"))
                        for m in rz._candidate_mounts()]):
        dev = _fs_dev(mp)
        if dev is None or dev in seen:
            continue
        free = rz._writable_free_gb(mp)
        if free is None:                      # e.g. a root-owned mount root
            continue
        seen.add(dev)
        if free > best_free:
            best, best_free = base, free
    if best is None or best_free < rz.SCRATCH_MIN_FREE_GB:
        say("[scratch] no local drive with >= %d GiB free; using %s"
            % (rz.SCRATCH_MIN_FREE_GB, rz.PAR_ROOT))
        return rz.PAR_ROOT
    say("[scratch] using %s (%.0f GiB free) for per-job key work dirs%s"
        % (best, best_free, " (the clone's fs)" if best == CLONE_SCRATCH
           else ""))
    return best


if not TMP_ROOT:                              # ALL_T1013 K13: at import, so
    rz._pick_scratch_base = pick_scratch      # check-start sees it too


def scratch_src(base):
    return ("clone" if base == CLONE_SCRATCH else "fallback"
            if base == rz.PAR_ROOT else "mount")


def scratch_free_gib():
    base = rz._pick_scratch_base()
    p = base
    while p and not os.path.isdir(p):
        p = os.path.dirname(p)
    return shutil.disk_usage(p or "/").free / GIB, base


def pids_avail():
    """ALL_T1009: least pids.max - pids.current on our cgroup path."""
    rel = _read("/proc/self/cgroup").split("::", 1)[-1].strip()
    p, best = os.path.normpath("/sys/fs/cgroup" + rel), None
    while p.startswith("/sys/fs/cgroup"):
        mx = _read(os.path.join(p, "pids.max"))
        cur = _read(os.path.join(p, "pids.current"))
        if mx.isdigit() and cur.isdigit():
            v = int(mx) - int(cur)
            best = v if best is None else min(best, v)
        if p == "/sys/fs/cgroup":
            break
        p = os.path.dirname(p)
    return best


def nproc_avail():
    """ALL_T1009: RLIMIT_NPROC soft limit minus this uid's threads."""
    import resource
    soft = resource.getrlimit(resource.RLIMIT_NPROC)[0]
    if soft == resource.RLIM_INFINITY:
        return None
    n = 0
    for pid in _pids():
        st = _read("/proc/%d/status" % pid)
        uid = re.search(r"^Uid:\s+(\d+)", st, re.M)
        thr = re.search(r"^Threads:\s+(\d+)", st, re.M)
        if uid and thr and int(uid.group(1)) == os.getuid():
            n += int(thr.group(1))
    return soft - n


def tasks_free():
    """ALL_T1009: the tighter of the cgroup and the ulimit -u headroom."""
    vals = [v for v in (pids_avail(), nproc_avail()) if v is not None]
    return min(vals) if vals else None


def jobs_fit():
    """(keygen jobs that fit the task limits, B3 jobs, free tasks)."""
    ncpu = len(os.sched_getaffinity(0))
    want = max(1, ncpu // 2)
    av = tasks_free()
    if av is None:
        return want, want, None
    return max(0, min(want, (av - PIDS_SLACK) // (ncpu + 4))), want, av


def leftover_gib(base):
    """ALL_T1013 F5: GiB of a killed run's work dirs, which the leaf frees."""
    return rz._dir_bytes(base) / GIB if os.path.isdir(base) else 0.0


def reclaim_scratch():
    """ALL_T1013 F5: under the lock, remove the work dirs a killed run left
    (only rz.PAR_ROOT while the test redirect is set, V10)."""
    roots = [rz.PAR_ROOT]
    if not TMP_ROOT:
        roots += [os.path.join(mp, "bora_zombie_scratch")
                  for mp in rz._candidate_mounts()] + [CLONE_SCRATCH]
    for p in dict.fromkeys(os.path.abspath(r) for r in roots):
        try:
            if (not os.path.isdir(p) or os.path.islink(p)
                    or os.stat(p).st_uid != os.getuid()):
                continue
        except OSError:
            continue
        n = rz._dir_bytes(p)
        shutil.rmtree(p, ignore_errors=True)
        say("SAME note: removed leftover %s (%.1f GiB)" % (p, n / GIB))


RETRY_ONCE = tuple(rz.RESOURCE_FAIL)          # ALL_T1013 F7 + FI3


def retry_once(done, sweep):
    """ALL_T1013 F7 (owner): a sweep row given up for a resource is retried
    once per unit and size; a second give-up stays."""
    try:
        rows = sweep.load()
    except ValueError:
        return
    n = {}
    for r in rows:
        if isinstance(r, dict) and r.get("status") in RETRY_ONCE:
            k = "%s|%s" % (r.get("regex_name"), r.get("str_len"))
            n[k] = n.get(k, 0) + 1
    for k in sorted(done):
        st = done[k].get("status")
        if st not in RETRY_ONCE:
            continue
        u, sz_ = k.rsplit("|", 1)
        if n.get(k, 0) <= 1:
            del done[k]
            say("SAME note: retry once %s %s (%s)" % (u, sz_, st))
        else:
            say("SAME note: %s %s given up %d times, kept" % (u, sz_, n[k]))


def host_views(a):
    """ALL_T1009: (text, refusal) for the scratch drive and task limit."""
    free, base = scratch_free_gib()
    lg = leftover_gib(base)                   # ALL_T1013 F5: freed at the leaf
    free += lg
    n, want, av = jobs_fit()
    full = a.dry is None
    txt = "scratch=%.0fGiB(%s,%s) tasks_free=%s keygen_jobs=%d" % (
        free, base, scratch_src(base), "max" if av is None else av,
        max(n, 0))
    if n < 1:
        return txt, ("the task limits (pids.max, ulimit -u) leave %s free "
                     "tasks, too few for one keygen of %d threads"
                     % (av, len(os.sched_getaffinity(0)) + 4))
    left = (" This counts %.0f GiB of leftover work dirs in %s, which the "
            "leaf removes." % (lg, base) if lg else "")
    if full and free < SCRATCH_REFUSE_GIB:
        return txt, ("the scratch drive for %s has %.0f GiB free, below run_"
                     "zombie's own %d GiB rule.%s" % (base, free,
                                                      SCRATCH_REFUSE_GIB, left))
    if free < (SCRATCH_WARN_GIB if full else SCRATCH_REFUSE_GIB):
        say("CAVEAT: SAME check-start WARNING: the scratch drive for %s has "
            "only %.0f GiB free; a full 4 KB batch writes 80 to 110 GiB of "
            "keys, so batches will shrink.%s" % (base, free, left))
    if n < want:
        say("SAME check-start WARNING: the task limit lowers keygen jobs from "
            "%d to %d" % (want, n))
    return txt, None


def check_start_main(a):
    """--check-start: cap, clone, oomd and launcher probes, rule 2, start
    check, STOP rule. No build, no keygen."""
    why = driver_guard(CHECK_LOCK_WAIT_S)     # ALL_T1009: bounded wait
    orph = [] if why else orphan_circ(kill=True)   # ALL_T1013 F4: lock held
    if orph:
        time.sleep(0.5)
        orph = [o for o in orph if _alive(o[0])]
    if why or orph:
        say("SAME check-start REFUSE: %s" % (why or orphan_text(orph)))
        return 6
    if S["cap"] is None:
        say("SAME check-start REFUSE: ZKR_SAME_MAX_WIDTH_CORES must be a "
            "non-negative integer")
        return 6
    why = (clone_check() or fx_check(a.sizes, a.n) or cores_refusal()
           or nightly_refusal(a) or selftest_refusal())   # ALL_T1009: hour 0
    if why:
        say("SAME check-start REFUSE: %s" % why)
        return 6
    S["logdir"] = os.path.join(rz.PARTIAL_DIR, "same_logs", "check_%s_%d" % (
        time.strftime("%Y%m%d_%H%M%S"), os.getpid()))
    os.makedirs(S["logdir"], exist_ok=True)
    why = oomd_check(repair=False)            # ALL_T1009: never edit caller
    if why:
        say("SAME check-start REFUSE: %s" % why)
        return 6
    if a.launcher == "auto":
        if same_units_running():
            say("SAME check-start: same-* scopes running, launcher probes "
                "skipped")
        else:
            lch, _props, note = launcher_probe()
            say("SAME check-start launcher %s%s" % (lch, (" (%s)" % note)
                                                    if note else ""))
    hv, why = host_views(a)                   # ALL_T1009: scratch, tasks
    if why:
        say("SAME check-start REFUSE: %s" % why)
        return 6
    hv += " circ=%s" % ("rebuild-at-leaf" if circ_rebuild_needed(a)  # S9
                        else "prebuilt")
    if a.dry is not None:
        say("SAME check-start PASS (dry: no start check) %s" % hv)
        return 0
    why = sweep_refusal(a)                    # ALL_T1009: RZ resume at hour 0
    if why:
        say("SAME check-start REFUSE: %s" % why)
        return 6
    rows = load_sample(a)
    pending = (not best_scalecal(a.server)[1]
               and S["topo"]["c_cores"] >= a.scalecal_min_cores)
    if pending:                               # an in-run stamp must be clean
        stt = git_status(LIST_TIMING)
        need = S["cap"] != 0 and any(x != 1000 for x in a.sizes)
        if stt is None and need:              # ALL_T1009: certain, so refuse
            say("SAME check-start REFUSE: git status failed on the timing "
                "list, so the in-run speed-check stamp would be invalid and "
                "2 and 4 KB would be refused at the leaf. If git reports "
                "dubious ownership, run: git config --global --add "
                "safe.directory %s" % REPO)
            return 6
        elif stt is None:
            say("CAVEAT: SAME check-start WARNING: git status failed on the "
                "timing list (dubious ownership?); the in-run stamp will be "
                "invalid, so 2 and 4 KB samples will be refused at the leaf")
        elif stt and need:
            say("SAME check-start REFUSE: the full run will make its own "
                "speed-check stamp, but the timing list has uncommitted or "
                "untracked files, so that stamp would be dirty: %s. Commit "
                "them first." % stt.split("\n")[:5])
            return 6
        elif stt:
            say("SAME check-start WARNING: the timing list is dirty (%s); "
                "this run needs no stamp (1 KB only or cap 0)"
                % stt.split("\n")[:5])
    why = start_check(a, rows, pending=pending)
    for size in sorted(S["refused_prior"]):
        say("SAME check-start WARNING: %s; the sweep still runs"
            % S["refused"].pop(size))
    why = why or next(iter(S["refused"].values()), None)
    if why:
        say("SAME check-start REFUSE: %s" % why)
        return 6
    say("SAME check-start PASS sizes=%s serial=%s %s" % (
        ",".join(map(str, a.sizes)), sorted(S["serial"]) or "none", hv))
    return 0


PD_RUN_LOCK = "/tmp/bora/PAPER_DATA.lock"
BUILD_REDIRECT_ENV = "ZKR_T1013_BUILD_REDIRECT"   # ALL_T1013: test-only


def pd_lock_held():
    """ALL_T1013 R4: a PAPER_DATA run holds its flock (read-only probe)."""
    import fcntl
    try:
        fd = os.open(PD_RUN_LOCK, os.O_RDONLY)
    except OSError:
        return False
    try:
        fcntl.flock(fd, fcntl.LOCK_SH | fcntl.LOCK_NB)
        fcntl.flock(fd, fcntl.LOCK_UN)
        return False
    except OSError:
        return True
    finally:
        os.close(fd)


def build_only_main(a):
    """ALL_T1013 S9: build circ_executable as the full leaf would (same
    VEC_SIZE, same render hooks); never refuses, rc 7 on a build failure."""
    if TMP_ROOT and os.environ.get(BUILD_REDIRECT_ENV) != "1":
        say("SAME note: test redirect active, circ build left to the leaf")
        return 0
    if pd_lock_held():
        say("SAME note: a PAPER_DATA run holds %s; circ build left to the "
            "leaf" % PD_RUN_LOCK)
        return 0
    why = driver_lock(0)
    if why:
        say("SAME note: %s; circ build left to the leaf" % why)
        return 0
    try:
        install_rz_hooks()
        binp = rz.ensure_zombie_built(rz.VEC_SIZE)
        say("SAME build-only OK %s zkmb.rs %s" % (binp, sha256_file(
            rz.BUILD_RS)[:16]))
        return 0
    except (Exception, SystemExit) as e:
        say("SAME build-only FAIL: %s: %s" % (type(e).__name__, e))
        return 7


def only_same_main():
    """--only-same: RZ main (RZ:1098-1132) at 1000 for RULESETS[0]."""
    rs = ruleset()
    rz.FULL_DIR = rs
    os.chdir(MS_DLP)
    os.makedirs(rz.DOCS_DIR, exist_ok=True)
    os.makedirs(rz.PARTIAL_DIR, exist_ok=True)
    sweep = pair_names(ARGS)[0]
    rz.PARTIAL, rz.PARTIAL_DOCS = sweep.tmp, sweep.docs
    binp = rz.ensure_zombie_built(rz.VEC_SIZE)
    rz.PAR_ROOT = rz._pick_scratch_base()
    os.makedirs(rz.PAR_ROOT, exist_ok=True)
    try:
        done = rz._load_partial()
        rz.run_pipeline(binp, 1000, rz.list_policy_names(rs), done)
    finally:
        rz.shutil.rmtree(rz.PAR_ROOT, ignore_errors=True)


def topology_line():
    """Full 64-hex launch_sig, as in every row (DLP_T1001 fix2)."""
    return "SAME topology C_cores=%d tpc=%d nodes=%d launch_sig=%s cap=%d" % (
        S["topo"]["c_cores"], S["topo"]["tpc"], len(S["topo"]["nodes"]),
        S["sig"], S["cap"])


def post_build(binp, a):
    """Re-hash the Zombie inputs after this run's fixes and make, so the
    scalecal stamp and launch_sig hold the built tree (DLP_T1001 fix3)."""
    S["binp"] = binp
    S.pop("zin", None)
    S["sig"] = launch_sig(S["topo"]["tpc"], a)


def run_main(a):
    global LOG_FH
    sweep, sample = pair_names(a)
    if a.dry is not None:
        for p in (pair_names(a)[1],) + ((sweep,) if a.only_same else ()):
            p.delete()
    S["pair"] = sample
    for p in (sweep, sample):                 # DLP_T1001 R2: before any put
        p.repair_tail()
    if rule2(sweep, sample):
        say("SAME rule 2: sweep partial absent, deleting %s and %s"
            % (sample.tmp, sample.docs))
        sample.delete()
    S["rule2_done"] = True                    # ALL_T1009: RZ load skips it
    sweep.restore()
    sample.restore()
    if S["cap"] is None:
        say("SAME refuse: ZKR_SAME_MAX_WIDTH_CORES must be a non-negative "
            "integer")
        return 6
    bad = [x for x in a.sizes if x not in rz.VEC_SIZE] if a.dry is None else \
        [x for x in a.sizes if x not in dz.DRY_VEC_SIZE]
    if bad or (a.only_same and a.sizes != [1000]):
        say("SAME refuse: sizes %s not in the sweep" % a.sizes)
        return 6
    why = fx_check(a.sizes, a.n) or clone_check() or cores_refusal()
    if why:
        say("SAME refuse: %s" % why)
        return 6
    reclaim_scratch()                         # ALL_T1013 F5: lock held
    n, want, av = jobs_fit()                  # ALL_T1009: adapt, never refuse
    S["jobs_cap"] = max(1, n)
    free, base = scratch_free_gib()
    say("SAME note: host scratch %.0f GiB free (%s), tasks free %s, keygen "
        "jobs %d of %d" % (free, base, "max" if av is None else av,
                           S["jobs_cap"], want))
    if a.launcher == "auto":
        S["launcher"], S["props"], note = preflight()
        say("SAME launcher %s%s" % (S["launcher"], (" (%s)" % note)
                                    if note else ""))
    if a.dry is not None:
        rz.VEC_SIZE = dz.DRY_VEC_SIZE
        rz.list_policy_names = dz._make_dry_list_policy_names(
            a.dry, rz.list_policy_names)
    install_rz_hooks()
    post_build(rz.ensure_zombie_built(rz.VEC_SIZE), a)
    rows = S["rows"] = load_sample(a)
    S["bus"] = ThreadPoolExecutor(max_workers=4)
    if a.dry is None:
        why = full_start(a, rows)
        if why:
            say("SAME refuse at start: %s" % why)
            return 6
        for size, msg in sorted(S["refused"].items()):   # DLP_T1001 R1
            if size not in S["refused_prior"]:
                put("stop", size=size, reason=msg, cap=S["cap"],
                    width=S["w_state"].get(size, ARGS.slot_cores),
                    cause="nopass")
            say("SAME sample at %d refused: %s. The sweep and the other "
                "sizes still run. A resume keeps %d refused, with no "
                "re-keygen, until a valid PASS exists or the cap is raised."
                % (size, msg, size))
        a.sizes = [x for x in a.sizes if x not in S["refused"]]
    w_state, S["gates"], _ = state_from_rows(rows, S["sig"], S["fp"])
    if a.dry is not None:                     # full: start_check set it
        S["w_state"] = w_state
    if S["launcher"] == "systemd":
        systemd_startup()
    say(topology_line())
    if a.only_same:
        only_same_main()
    else:
        rz.main()
    summary()
    for size, msg in sorted(S.get("refused", {}).items()):
        say("SAME STOP at %d: %s" % (size, msg))
    if S["exit6"] or S.get("refused"):
        return 6
    return 0


def main(argv=None):
    global ARGS, LOG_FH
    a = ARGS = parse_args(sys.argv[1:] if argv is None else argv)
    install_output_hooks()
    if a.selftest:
        return selftest()
    os.chdir(MS_DLP)
    if TMP_ROOT:                              # ALL_T1009: never silent
        say("SAME note: test redirect active, root %s" % TMP_ROOT)
    init_state(a)
    if a.check_start:
        return check_start_main(a)
    if a.build_only:                          # ALL_T1013 S9: INSTALL calls it
        return build_only_main(a)
    why = driver_guard(LOCK_WAIT_RUN_S)      # ALL_T1009: before any file
    if why:
        say("SAME refuse: %s" % why)
        return 6
    signal.signal(signal.SIGTERM, on_sigterm)
    bind_parent()
    S["logdir"] = os.path.join(rz.PARTIAL_DIR, "same_logs",
                               time.strftime("%Y%m%d_%H%M%S") +
                               "_%d" % os.getpid())
    os.makedirs(S["logdir"], exist_ok=True)
    LOG_FH = open(out_paths()[1], "w" if a.dry is not None else "a")
    say("SAME log start %s pid %d" % (time.strftime("%Y-%m-%d %H:%M:%S"),
                                      os.getpid()))   # ALL_T1009: full appends
    orphan_circ(kill=True)                    # ALL_T1009: lock held, so ours
    rc = 1
    try:
        rc = run_main(a)
    except SystemExit as e:
        if isinstance(e.code, str):
            say(e.code)
            rc = 1
        else:
            rc = e.code if e.code is not None else 0
    finally:
        try:
            write_tsv()
        except Exception as e:
            say("SAME TSV rebuild failed: %s" % e, caveat=True)
        if a.dry is not None and not STOP.is_set():
            for p in (pair_names(a)[1],) + ((pair_names(a)[0],)
                                            if a.only_same else ()):
                p.delete()
        if S.get("launcher") == "systemd":    # ALL_T1009: uncap the slice
            try:
                sctl("set-property", "--runtime", "bora-same.slice",
                     "MemoryMax=infinity")
            except Exception:
                pass
        say("SAME exit %d" % rc)
        LOG_FH.close()
        LOG_FH = None
    return rc


# ===========================================================================
# selftest (pins)
# ===========================================================================
RZ_PINS = ("e = _estimate(n, str_len, done, slope",
           "dk = _estimate(pending[i]", "max_jobs = _cpu_max_jobs()",
           "ex.submit(_build_one, binp",
           "caps = {idx: _as_cap(est_ram(n), full_mem)",
           "with ThreadPoolExecutor(max_workers=len(batch))",
           'default = _median_at(done, str_len, "peak_rss")',
           "serial = len(batch) == 1", "// MIN_CPUS_PER_CIRC)",
           "rc, _out, errtxt, rss = _run_keygen(",        # ALL_T1013 S3
           '"true", "prover"], mem_bytes), d, timeout)')


S1_PINS = ("let timer = Instant::now();\n    let proof = prover.prove(vec![pw]);"
           "\n    println!(\"prove takes {}\", timer.elapsed().as_millis());",
           "let verifier = &verifier;\n    let timer = Instant::now();\n    let ok"
           " = verifier.verify(&proof, &vec![vw]);\n    println!(\"verify takes"
           " {}\", timer.elapsed().as_millis());")


def selftest():
    import inspect
    src = inspect.getsource(_ORIG.get("pipeline", rz.run_pipeline))
    i_du = src.find("shutil.disk_usage(PAR_ROOT)")
    i_ex = src.find("ThreadPoolExecutor(")
    i_to = src.find("_time_one(binp, b, str_len")
    i_rm = src.find('shutil.rmtree(b["dir"]')
    assert -1 not in (i_du, i_ex, i_to, i_rm), "RZ pipeline anchors moved"
    assert i_du < i_ex < i_to < i_rm, "RZ pipeline order changed"
    assert "widx, fin = {}, {}, [0], [0]" in src, "RZ widx no longer per call"
    msrc = inspect.getsource(rz.main)
    assert "finally:\n        shutil.rmtree(PAR_ROOT" in msrc, "RZ main finally"
    tsrc = open(RZ_PATH).read()            # RZ _time_one, unhooked text
    assert '"policy_%d" % str_len, "false",' in tsrc, "RZ base argv moved"
    for pin in RZ_PINS:                    # ALL_T1009: hook anchors, file text
        assert pin in tsrc, "RZ hook anchor moved: %s" % pin
    pd = os.path.join(REPO, "scripts", "PAPER_DATA.py")
    if os.path.isfile(pd):
        m = re.search(r'FAIL_RE = re\.compile\(\s*r"([^"]*)"\s*r"([^"]*)"\)',
                      open(pd).read())
        assert m and m.group(1) + m.group(2) == FAIL_LIKE.pattern, \
            "FAIL_LIKE differs from PAPER_DATA.FAIL_RE"
    zk = os.path.join(ZOMBIE_TREE, "circ", "src", "zkmb.rs")
    if os.path.isfile(zk):
        orig = open(zk).read()
        _ORIG.setdefault("render", rz._render_zkmb)
        a1 = render_wrapped(orig, [1000, 2000, 4000])
        a2 = render_wrapped(orig, [1000, 2000, 4000])
        assert a1 == a2 and a1.count("fn zreal_one_circuit") == 1
        assert a1.index("fn zreal_one_circuit") < a1.index(ZK_ANCHOR)
        assert '"policy_real_4000" => zreal_one_circuit::<4000>("policy4000")' \
            in a1
        assert "fn compile_one_circuit(circuit: &str)" in orig   # ALL_T1013 S3
        zfn = a1[a1.index("fn zreal_one_circuit"):a1.index(
            "// <<< same_zombie zreal arm")]
        for pin in S1_PINS:                   # ALL_T1013 S1: timers unchanged
            assert zfn.count(pin) == 1, "S1 timer pin: %s" % pin
        assert [zfn.index(p) for p in S1_PINS] == sorted(
            zfn.index(p) for p in S1_PINS), "S1 timer order"
        assert "zkmb_get_verifier" not in zfn, "S1: second key load"
        for fld in ("pub inst: Instance,", "    gens: NIZKGens,",
                    "    val_arr: Vec<Option<Value>>,",
                    "pub fn new(inst: Instance, gens: NIZKGens, "
                    "input_names: Vec<String>)"):
            assert fld in orig, "S1 upstream anchor moved: %s" % fld
        assert ('"policy_keys_4000" => compile_one_circuit("policy4000")'
                in a1), "S3 keys arm missing"
        blk = a1[a1.index(ZREAL_BEGIN):a1.index(ZREAL_END) + len(ZREAL_END) + 1]
        bare = a1.replace(ARM_T.split("\n//@@ARM\n")[0] + "\n\n", "", 1)
        assert bare.replace(blk, "", 1) == _ORIG["render"](
            orig, [1000, 2000, 4000]), "render differs outside the zreal parts"
    assert up2(3) == 4 and down2(3) == 2 and up2(1) == 1 and down2(0) == 1
    m = NOT_FIT_RE.search("memory allocation of 34359738368 bytes failed\n")
    assert m and m.group(1) == "34359738368", "ALL_T1017: NOT_FIT_RE"
    assert "not_fit" not in rz.RESOURCE_FAIL + RETRY_ONCE, "T1017: retried"
    assert not FAIL_LIKE.search("SAME note: units over the address-space "
                                "cap at 4000 B: u"), "T1017: note is a FAIL"
    say("[same_zombie selftest] OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
