# Tests for compress_regex.compress_combos.
#
# Two oracles:
#  - greenery (FSM language algebra): for each family the union of the emitted
#    outputs must EQUAL (precise) or strictly CONTAIN (approx) the union of the
#    sources, and never MISS one (UNSOUND = the discharge-soundness invariant).
#    greenery is a TEST-ONLY dependency; absent -> those tests skip.
#  - sim_fanout (in compress_regex, no extra dep): mirrors BORA's leg selection
#    so we can assert every emitted regex actually fans out (>=1 mandatory
#    anchor) and none is a dead disjunction (the BORA pm>=2 assertion guard).
import random
import pytest

from compress_regex import (compress_combos, sim_fanout, _fan_status,
                            PRECISE, APPROX, KEEP)

try:
    from greenery import parse
    _HAVE_GREENERY = True
except ImportError:
    _HAVE_GREENERY = False

needs_greenery = pytest.mark.skipif(
    not _HAVE_GREENERY, reason="pip install greenery (test-only oracle)")

_SPECIAL = set(".^$*+?()[]{}|\\")


def _to_greenery(p):
    """Translate the Zombie/BORA dialect to greenery syntax. Outside a class,
    \\xHH -> its char (escaped if a greenery metachar). Inside a class, keep
    \\xHH (lowercased) verbatim -- greenery accepts hex escapes in classes but
    not e.g. a bare '[- ]'."""
    out, i, n, incls = [], 0, len(p), False
    while i < n:
        c = p[i]
        if c == "[":
            incls = True; out.append(c); i += 1; continue
        if c == "]":
            incls = False; out.append(c); i += 1; continue
        if c == "\\" and p[i + 1:i + 2] == "x":
            if incls:
                out.append("\\x" + p[i + 2:i + 4].lower()); i += 4; continue
            ch = chr(int(p[i + 2:i + 4], 16)); i += 4
            out.append("\\" + ch if ch in _SPECIAL else ch); continue
        out.append(c); i += 1
    return "".join(out)


def _fsm(s):
    return parse(_to_greenery(s)).to_fsm()


def _union(rxs):
    return "(" + "|".join(rxs) + ")"


def verify(originals, outputs):
    """'precise' (union == union) | 'approx' (sound strict superset) |
    'UNSOUND' (the outputs miss some source string)."""
    U = _fsm(_union(originals))
    M = _fsm(_union(outputs))
    if U.equivalent(M):
        return "precise"
    if (U - M).empty():
        return "approx"
    return "UNSOUND"


def fp_bound(originals, outputs, upto=14):
    """(shortest extra string, count of extra strings up to `upto` bytes).
    Informational; tolerant of greenery API differences in strings()."""
    extra = _fsm(_union(outputs)) - _fsm(_union(originals))
    try:
        gen = extra.strings("?")
    except TypeError:
        gen = extra.strings()
    try:
        strs = [s for _, s in zip(range(5000), gen)
                if len("".join(s) if isinstance(s, list) else s) <= upto]
    except Exception:
        return (None, -1)
    return (strs[0] if strs else None, len(strs))


# --- fixtures: real DLP alternation families (combos built from spec) --------
def _itin():
    g = (list(range(50, 66)) + list(range(70, 89))
         + list(range(90, 93)) + list(range(94, 100)))
    return ([r"9[0-9]{2}%d[0-9]{4}" % v for v in g]
            + [r"9[0-9]{2}[\x2D\x20]?%d[\x2D\x20]?[0-9]{4}" % v for v in g])

def _aba():
    p = list(range(0, 13)) + list(range(21, 33)) + list(range(61, 73)) + [80]
    return [r"%02d[0-9]{2}\x2D?[0-9]{4}\x2D?[0-9]" % v for v in p]

def _ecuador():
    p = list(range(1, 31)) + [90, 99]
    return [r"%02d[0-9]{8}" % v for v in p]

# the un-factorable (KEEP) families -- these used to emit a DEAD disjunction;
# the new algorithm must split each into fannable concatenations.
AUSTRALIA_DL = [
    r"[0-9]{2}[\x2D\x20]?[0-9]{2}[\x2D\x20]?[0-9]{4}",
    r"[0-9]{3}[\x2D\x20]?[0-9]{3}[\x2D\x20]?[0-9]{3,4}",
    r"[0-9][\x2D\x20]?[0-9]{3}[\x2D\x20]?[0-9]{3}[\x2D\x20]?[0-9]{3}",
    r"[0-9]{7}", r"[A-Za-z][0-9]{5}", r"[A-Za-z]{2}[0-9]{4}",
    r"[0-9]{4}[A-Za-z]{2}"]
CANADA_DL = [
    r"[0-9]{6}\x2D[0-9]{3}", r"[0-9]{5,9}", r"[0-9]{7}",
    r"[A-Za-z]{2}\x2D?[A-Za-z]{2}\x2D?[A-Za-z]{2}\x2D?[A-Za-z][0-9]{3}[A-Za-z]{2}",
    r"[0-9]{5,7}", r"[A-Za-z][0-9]{9}",
    r"[A-Za-z]{5}\x2D?[0123][0-9][01][0-9]{6}",
    r"[A-Za-z][0-9]{4}\x2D?[0-9]{5}\x2D?[0-9][0156][0-9][0123][0-9]",
    r"[0-9]{5,6}", r"[A-Za-z][0-9]{12}", r"[0-9]{8}"]

FAMILIES = {
    "itin": _itin(),
    "aba": _aba(),
    "ecuador": _ecuador(),
    "korea": [r"[A-Za-z][0-9]{3}[A-Za-z][0-9]{4}", r"[A-Za-z][0-9]{8}"],
    "spain": [r"[0-9]{8}[A-Za-z]", r"[A-Za-z][0-9]{7}[A-Za-z]"],
    "latvia": [r"[0-9]{2}[0-9]{9}", r"[0-9]{6}\x2D[0-9][0-9]{4}"],
    "france": [r"[0-9]{13}\x20[0-9]{2}", r"[0-9]{15}"],
    "czech": [r"[0-9]{6}\x2F?[0-9]{3}", r"[0-9]{6}\x2F?[0-9]{4}"],
    "japan": [r"[0-9]{4}\x2D?[0-9]{6}", r"[0-9]{7,12}"],
    "malta": [r"[0-9]{7}[A-Za-z]", r"[0-9]{9}"],
    "canada_bank": [r"0[0-9]{8}", r"[0-9]{5}\x2D[0-9]{3}"],
    "brazil": [r"[0-9]{11}", r"[0-9]{3}\x2E[0-9]{3}\x2E[0-9]{3}\x2D[0-9]{2}"],
    "israel": [r"[0-9]{13}", r"[0-9]{2}\x2D[0-9]{3}\x2D[0-9]{8}"],
    "australia_dl": AUSTRALIA_DL,
    "canada_dl": CANADA_DL,
}

# families whose collapse MUST be lossless (the NEEDS drivers + equal-length)
PRECISE_DRIVERS = ["itin", "aba", "ecuador", "korea", "spain"]


@needs_greenery
@pytest.mark.parametrize("name", PRECISE_DRIVERS)
def test_precise_drivers(name):
    combos = FAMILIES[name]
    r = compress_combos(combos)
    assert r.kind == PRECISE, (name, r.kind, r.outputs)
    assert verify(combos, r.outputs) == "precise", (name, r.outputs)


@needs_greenery
@pytest.mark.parametrize("name", list(FAMILIES))
def test_never_unsound(name):
    """Load-bearing: the union of outputs must accept everything the sources do
    (a superset), for EVERY family, regardless of precise/approx labeling."""
    combos = FAMILIES[name]
    r = compress_combos(combos)
    v = verify(combos, r.outputs)
    assert v != "UNSOUND", (name, r.kind, r.outputs)
    if r.kind == PRECISE:
        assert v == "precise", (name, r.outputs)
    if r.kind == APPROX:
        assert v == "approx", (name, r.outputs)


def test_every_output_is_fan_safe():
    """The BORA guarantee (no greenery needed): EVERY emitted regex, for EVERY
    family, must fan out to a real anchor ('anchor') OR not be fanned at all
    ('none') -- NEVER 'fanned_no_anchor' (a dead disjunction that would panic
    the pm>=2 assertion). The KEEP families in particular must all fan."""
    for name, combos in FAMILIES.items():
        r = compress_combos(combos)
        for o in r.outputs:
            st = _fan_status(o)
            assert st != "fanned_no_anchor", (name, o, st)
        # un-factorable families are split into concatenations that all fan
        if name in ("australia_dl", "canada_dl"):
            assert all(sim_fanout(o) for o in r.outputs), (name, r.outputs)
            assert len(r.outputs) > 1, (name, r.outputs)


def test_sim_fanout_calibration():
    """sim_fanout / _fan_status mirror BORA's select_slots (SINGLE_FANOUT_MAX=26,
    mandatory legs first)."""
    assert _fan_status(r"[0-9]{4}") == "anchor"            # digit run pins
    assert _fan_status(r"[0-9]{2}[\x2D\x20]?[0-9]{4}") == "anchor"
    # a top-level disjunction: only optional legs -> fanned, no anchor
    assert _fan_status(r"([0-9]{7}|[A-Za-z][0-9]{9})") == "fanned_no_anchor"
    # all legs over card 26 (combined letters) -> never pinned, not fanned
    assert _fan_status(r"[A-Za-z]{5}") == "none"
    assert sim_fanout(r"[0-9]{4}") and not sim_fanout(r"[A-Za-z]{5}")


@needs_greenery
def test_report_kinds(capsys):
    """Informational: each family's kind, source->output count, and (for approx)
    the FP bound."""
    with capsys.disabled():
        print()
        for name, combos in FAMILIES.items():
            r = compress_combos(combos)
            fan = all(sim_fanout(o) or _fan_status(o) == "none"
                      for o in r.outputs)
            print("  %-13s %-8s %3d->%d  fan=%s  %s"
                  % (name, r.kind, r.stats.get("before", len(combos)),
                     len(r.outputs), fan,
                     " | ".join(o[:40] for o in r.outputs[:3])))


def _rand_combo(rng):
    bases = ["[0-9]", "[A-Za-z]", "[A-Za-z0-9]", r"\x2D", "5", "A", "9"]
    out = []
    for _ in range(rng.randint(2, 5)):
        b = rng.choice(bases)
        q = rng.choice(["", "", "{2}", "{1,3}", "?"])
        out.append(b + q)
    return "".join(out)


@needs_greenery
def test_fuzz_soundness():
    """Random small alternation sets must NEVER produce an unsound merge, and
    no emitted output may be a dead disjunction."""
    rng = random.Random(12345)
    for _ in range(400):
        k = rng.randint(2, 6)
        combos = list({_rand_combo(rng) for _ in range(k)})
        if len(combos) < 2:
            continue
        r = compress_combos(combos)
        assert verify(combos, r.outputs) != "UNSOUND", (combos, r.outputs)
        for o in r.outputs:
            assert _fan_status(o) != "fanned_no_anchor", (combos, o)


def test_compress_runs_without_greenery():
    """compress_combos / sim_fanout have NO runtime dependency on greenery."""
    r = compress_combos([r"9[0-9]{2}50[0-9]{4}", r"9[0-9]{2}51[0-9]{4}"])
    assert r.outputs and r.kind in (PRECISE, APPROX, KEEP)
    assert sim_fanout(r.outputs[0])
