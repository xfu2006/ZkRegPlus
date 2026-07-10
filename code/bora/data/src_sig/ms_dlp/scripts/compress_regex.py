# -------------------------------------------
# Compress a collection of alternation-free regex "combos" (the output of
# gen_zombie_regex.expand_pat) back into ONE regex that serves as the common
# basis for BOTH BORA and Zombie. The builder only ever WIDENS, so the merged
# regex's language is always a superset-or-equal of the union of the combos
# (the discharge-soundness guarantee). kind reports PRECISE (==union) vs APPROX
# (strict superset, sound) vs KEEP (left as an alternation).
#
# Dialect (a strict subset of Python re): literal bytes, \xHH, [classes] (with
# ranges and \xHH), fixed {n} / range {m,n} reps, ? , top-level (a|b). The PAT
# combos carry NO top-level proximity .{0,N} (already stripped upstream).
#
# Verification of soundness + precise/approx lives in test_compress_regex.py
# (greenery FSM oracle); this module self-declares kind by construction.
# -------------------------------------------
import re
try:                                  # stdlib regex parser (sim_fanout)
    from re import _parser as _sre
except ImportError:                   # py < 3.11
    import sre_parse as _sre

PRECISE, APPROX, KEEP = "PRECISE", "APPROX", "KEEP"


class Result:
    """Compression outcome. `outputs` is the list of emitted regexes (1 for a
    clean factoring, several when an un-factorable disjunction is split into
    fannable concatenations). `merged` = outputs[0] for the common single case."""
    def __init__(self, outputs, kind, stats=None):
        self.outputs = outputs if isinstance(outputs, list) else [outputs]
        self.kind = kind
        self.stats = stats or {}

    @property
    def merged(self):
        return self.outputs[0]

    def __repr__(self):
        return "Result(%r, %s, %r)" % (self.outputs, self.kind, self.stats)


# --- piece 1: atomizer + prefix/suffix factor ------------------------------
_QUANT = re.compile(r"\{\d+(?:,\d+)?\}|\?")
_FIXED = re.compile(r"\{(\d+)\}\Z")


def atomize(combo):
    """Flat (alternation-free) dialect regex -> list of atoms. Atom = one base
    unit (literal byte | \\xHH | [class]) + any trailing quantifier; joining the
    atoms reproduces `combo`. Raises on a top-level '|' or '(' (must be flat)."""
    atoms, i, n = [], 0, len(combo)
    while i < n:
        c = combo[i]
        if c in "|(":
            raise ValueError("non-flat combo (top-level %r) at %d: %r"
                             % (c, i, combo))
        if c == "\\" and combo[i + 1:i + 2] == "x":
            base, i = combo[i:i + 4], i + 4
        elif c == "[":
            j = combo.find("]", i)
            if j < 0:
                raise ValueError("unterminated class at %d: %r" % (i, combo))
            base, i = combo[i:j + 1], j + 1
        else:
            base, i = c, i + 1
        m = _QUANT.match(combo, i)
        if m:
            base += m.group(0)
            i = m.end()
        atoms.append(base)
    return atoms


def _split_quant(atom):
    m = _QUANT.search(atom)
    return (atom[:m.start()], atom[m.start():]) if m else (atom, "")


def _common_run(seqs):
    """Number of leading elements identical across all seqs (stops at shortest)."""
    k = 0
    for col in zip(*seqs):
        if len(set(col)) == 1:
            k += 1
        else:
            break
    return k


def factor(combos):
    """(prefix_atoms, middles, suffix_atoms): common atom prefix+suffix shared by
    ALL combos (non-overlapping), and each combo's residual middle atom-list."""
    seqs = [atomize(c) for c in combos]
    p = _common_run(seqs)
    shortest = min(len(s) for s in seqs)
    s = 0
    for col in zip(*[seq[::-1] for seq in seqs]):
        if p + s >= shortest:
            break
        if len(set(col)) == 1:
            s += 1
        else:
            break
    prefix = seqs[0][:p]
    suffix = seqs[0][len(seqs[0]) - s:] if s else []
    middles = [seq[p: len(seq) - s] for seq in seqs]
    return prefix, middles, suffix


# --- symbols (single matched position) -------------------------------------
def _sym_members(sym):
    """Set of byte values a single-position symbol matches (literal | \\xHH |
    [class]); None if `sym` is not single-position (carries a quantifier)."""
    base, q = _split_quant(sym)
    if q:
        return None
    if base.startswith("[") and base.endswith("]"):
        return _class_members(base[1:-1])
    if base.startswith("\\x"):
        return {int(base[2:4], 16)}
    if len(base) == 1:
        return {ord(base)}
    return None


def _class_members(body):
    """Parse a class body (e.g. '0-9', '\\x2D\\x20', 'A-Za-z0-9', '0-24-9',
    'NEDFACUX') into a set of byte values."""
    units, i, n = [], 0, len(body)
    while i < n:
        if body[i] == "\\" and body[i + 1:i + 2] == "x":
            units.append(int(body[i + 2:i + 4], 16)); i += 4
        else:
            units.append(ord(body[i])); i += 1
    out, k = set(), 0
    while k < len(units):
        if k + 2 < len(units) and units[k + 1] == ord("-"):
            out.update(range(units[k], units[k + 2] + 1)); k += 3
        else:
            out.add(units[k]); k += 1
    return out


def _render_byte(v):
    """Render a byte value: alnum as itself, everything else as \\xHH."""
    c = chr(v)
    return c if c.isalnum() else "\\x%02X" % v


def _render_class(members):
    """Fold a set of byte values into the tightest class string; a singleton is
    rendered bare (no brackets)."""
    vs = sorted(members)
    if len(vs) == 1:
        return _render_byte(vs[0])
    parts, i = [], 0
    while i < len(vs):
        j = i
        while j + 1 < len(vs) and vs[j + 1] == vs[j] + 1:
            j += 1
        if j - i >= 2:
            parts.append(_render_byte(vs[i]) + "-" + _render_byte(vs[j]))
        else:
            parts.extend(_render_byte(vs[k]) for k in range(i, j + 1))
        i = j + 1
    return "[" + "".join(parts) + "]"


def _union_class(syms):
    """Union single-position symbols into one class (exact set union -> precise)."""
    members = set()
    for s in syms:
        m = _sym_members(s)
        if m is None:
            # not single-position: fall back to a bare alternation
            return "(" + "|".join(dict.fromkeys(syms)) + ")"
        members |= m
    return _render_class(members)


def _slots(atoms):
    """Atom-list -> fixed single-byte slot symbols, or None if any atom is
    VARIABLE length (?, {m,n} m!=n)."""
    out = []
    for a in atoms:
        base, q = _split_quant(a)
        if q == "":
            out.append(base)
        else:
            m = _FIXED.fullmatch(q)
            if not m:
                return None
            out += [base] * int(m.group(1))
    return out


def _coalesce(symlist):
    """Render a symbol list to a string, folding runs of an identical symbol
    into sym{n} (cosmetic, language-preserving)."""
    out, i = [], 0
    while i < len(symlist):
        j = i
        while j < len(symlist) and symlist[j] == symlist[i]:
            j += 1
        run = j - i
        out.append(symlist[i] + ("{%d}" % run if run > 1 else ""))
        i = j
    return "".join(out)


# --- piece 3: precise core (trie_merge) ------------------------------------
def trie_merge(seqs):
    """Minimal PRECISE factoring of symbol-sequences (each symbol = one matched
    position). Language == exact union. Recursive: factor common prefix+suffix,
    fold single-symbol leaves into a class, else group by first symbol."""
    seqs = [list(s) for s in dict.fromkeys(tuple(s) for s in seqs)]
    if len(seqs) == 1:
        return _coalesce(seqs[0])
    p = _common_run(seqs)
    shortest = min(len(s) for s in seqs)
    q = 0
    for col in zip(*[s[::-1] for s in seqs]):
        if p + q >= shortest:
            break
        if len(set(col)) == 1:
            q += 1
        else:
            break
    pre = _coalesce(seqs[0][:p])
    suf = _coalesce(seqs[0][len(seqs[0]) - q:]) if q else ""
    mids = [s[p: len(s) - q] for s in seqs]
    empties = any(len(m) == 0 for m in mids)
    nonempty = [m for m in mids if len(m) > 0]
    if not nonempty:
        return pre + suf
    if not empties and all(len(m) == 1 for m in nonempty):
        return pre + _union_class([m[0] for m in nonempty]) + suf
    groups = {}
    for m in nonempty:
        groups.setdefault(m[0], []).append(m[1:])
    branches = [k + trie_merge(g) for k, g in groups.items()]
    body = branches[0] if len(branches) == 1 else "(" + "|".join(branches) + ")"
    if empties:                       # some branch is just prefix+suffix -> opt
        body = "(" + body + ")?" if len(body) > 1 else body + "?"
    return pre + body + suf


# --- skeleton grouping (variable-atom middles, e.g. optional separators) ----
def _skeleton(atoms):
    """Atom structure with single-byte LITERAL atoms wildcarded to 'LIT'
    (classes / \\xHH / quantified atoms kept verbatim)."""
    out = []
    for a in atoms:
        base, q = _split_quant(a)
        is_lit = (q == "" and not base.startswith("[")
                  and not base.startswith("\\x") and len(base) == 1)
        out.append("LIT" if is_lit else a)
    return tuple(out)


def group_by_skeleton(middles):
    groups = {}
    for m in middles:
        groups.setdefault(_skeleton(m), []).append(m)
    return list(groups.values())


def compress_group(group):
    """Members share a skeleton (same structure, differ only in LIT positions).
    Constant atoms pass through; each maximal run of varying positions is
    trie-merged. PRECISE."""
    cols = list(zip(*group))
    out, i, n = [], 0, len(cols)
    while i < n:
        if len(set(cols[i])) == 1:
            out.append(cols[i][0]); i += 1
        else:
            j = i
            while j < n and len(set(cols[j])) > 1:
                j += 1
            seqs = [[m[k] for k in range(i, j)] for m in group]
            out.append(trie_merge(seqs)); i = j
    return "".join(out)


def _is_optional_atom(a):
    return a.endswith("?") or re.search(r"\{0,\d+\}\Z", a) is not None


def _strip_optionals(atoms):
    """Atom-list with optional atoms removed = its 'all optionals absent'
    instance (one concrete string in its language)."""
    return tuple(a for a in atoms if not _is_optional_atom(a))


def drop_subsumed(groups):
    """Drop group A iff some group B has optional atoms and B's 'all-optionals-
    absent' member set literally COVERS A's members -- then A's language sits
    inside B's (sound). Compares actual members (literal values), not just
    skeletons, so it never drops a group B doesn't truly contain."""
    members = [set(tuple(m) for m in g) for g in groups]
    stripped = [set(_strip_optionals(m) for m in g) for g in groups]
    has_opt = [any(_strip_optionals(m) != tuple(m) for m in g) for g in groups]
    keep = []
    for a in range(len(groups)):
        subsumed = any(b != a and has_opt[b] and members[a] <= stripped[b]
                       for b in range(len(groups)))
        if not subsumed:
            keep.append(groups[a])
    return keep


# --- piece 4: approx wideners (B: on by default) ---------------------------
def _widen_optional(parts):
    """Two branches A and AB where one is the other plus a leading/trailing run
    -> A(extra)? . APPROX. (best-effort; returns None if not this shape)."""
    if len(parts) != 2:
        return None
    a, b = sorted(parts, key=len)
    if b.startswith(a):
        return a + "(" + b[len(a):] + ")?"
    if b.endswith(a):
        return "(" + b[:len(b) - len(a)] + ")?" + a
    return None


def _widen_trailing_len(parts):
    """Branches sharing a prefix and ending in a run of the SAME repeated class
    of differing length -> prefix CLASS{min,max}. APPROX. Covers japan/malta-ish
    tails. Best-effort: returns None if not cleanly this shape."""
    if len(parts) < 2:
        return None
    # decompose each into (prefix_str, tail_class, lo, hi)
    decs = []
    for p in parts:
        m = re.fullmatch(r"(.*?)(\[[^\]]*\]|\\x..|[A-Za-z0-9])\{(\d+)(?:,(\d+))?\}",
                         p)
        if not m:
            # a bare single tail symbol counts as {1,1}
            m2 = re.fullmatch(r"(.*?)(\[[^\]]*\]|\\x..|[A-Za-z0-9])", p)
            if not m2:
                return None
            decs.append((m2.group(1), m2.group(2), 1, 1))
        else:
            lo = int(m.group(3)); hi = int(m.group(4)) if m.group(4) else lo
            decs.append((m.group(1), m.group(2), lo, hi))
    pref = decs[0][0]
    if any(d[0] != pref for d in decs):
        return None
    # union the tail classes; span the lengths
    cls = _union_class([d[1] for d in decs])
    lo = min(d[2] for d in decs); hi = max(d[3] for d in decs)
    span = "{%d}" % lo if lo == hi else "{%d,%d}" % (lo, hi)
    return pref + cls + span


def widen(parts):
    """Try the wideners; return (regex, APPROX) for the first sound, not-too-
    loose hit, else None (-> keep precise alternation)."""
    for w in (_widen_optional, _widen_trailing_len):
        r = w(parts)
        if r is not None:
            return r
    return None


# --- positional class-union concatenation (cluster member merge) -----------
def _base_members(base):
    """Byte set of a single base unit: [class] / \\xHH / literal char."""
    if base.startswith("[") and base.endswith("]"):
        return _class_members(base[1:-1])
    if base.startswith("\\x"):
        return {int(base[2:4], 16)}
    return {ord(base)}


def _slot_seq(combo):
    """Flat combo -> list of (byte-set, optional) single-position slots. {n}->n
    mandatory; {m,n}->m mandatory + (n-m) optional; ?->1 optional. Raises (via
    atomize) on a non-flat combo."""
    slots = []
    for a in atomize(combo):
        base, q = _split_quant(a)
        mem = frozenset(_base_members(base))
        if q == "":
            slots.append((mem, False))
        elif q == "?":
            slots.append((mem, True))
        else:
            m = re.fullmatch(r"\{(\d+)(?:,(\d+))?\}", q)
            lo = int(m.group(1)); hi = int(m.group(2)) if m.group(2) else lo
            slots += [(mem, False)] * lo + [(mem, True)] * (hi - lo)
    return slots


def _rep_suffix(lo, hi):
    if lo == hi:
        return "" if lo == 1 else "{%d}" % lo
    if lo == 0:
        return "?" if hi == 1 else "{0,%d}" % hi
    return "{%d,%d}" % (lo, hi)


def concat_merge(combos):
    """Merge same-structure combos into ONE concatenation (positional class-union
    with length ranges). Left-aligned; a shorter combo makes trailing positions
    optional. A sound SUPERSET of the union that stays a concatenation, so a
    guaranteed column remains a fan-out anchor (a disjunction has none)."""
    seqs = [_slot_seq(c) for c in combos]
    L = max(len(s) for s in seqs)
    cols = []
    for j in range(L):
        mem, opt = set(), False
        for s in seqs:
            if j < len(s):
                mem |= s[j][0]; opt = opt or s[j][1]
            else:
                opt = True
        cols.append((frozenset(mem), opt))
    out, i = [], 0
    while i < len(cols):
        mem = cols[i][0]; j = i; nman = nopt = 0
        while j < len(cols) and cols[j][0] == mem:
            if cols[j][1]:
                nopt += 1
            else:
                nman += 1
            j += 1
        out.append(_render_class(mem) + _rep_suffix(nman, nman + nopt))
        i = j
    return "".join(out)


_DIGITS = set(range(48, 58))
_LETTERS = set(range(65, 91)) | set(range(97, 123))


def _skeleton_kinds(combo):
    """Structural skeleton: the sequence of block KINDs (d=digits, L=letters,
    s=other) ignoring counts and optional separators. Same skeleton => combos
    align cleanly under concat_merge (a narrow column stays mandatory)."""
    sig = []
    for a in atomize(combo):
        base, q = _split_quant(a)
        if q == "?" or re.fullmatch(r"\{0,\d+\}", q):
            continue
        mem = _base_members(base)
        sig.append("d" if mem <= _DIGITS
                   else ("L" if mem <= _LETTERS else "s"))
    return tuple(sig)


_GRP1 = re.compile(r"\((\[[^\]]*\]|\\x..|[A-Za-z0-9])\)"
                   r"(\?|\{\d+(?:,\d+)?\}|[*+])?")


def _normalize_groups(combo):
    """Unwrap a group holding a single base unit: ([0-9])? -> [0-9]? . Lets the
    flat-combo machinery handle combos expand_pat left with quantified groups."""
    prev = None
    while prev != combo:
        prev = combo
        combo = _GRP1.sub(lambda m: m.group(1) + (m.group(2) or ""), combo)
    return combo


def cluster_concat(combos):
    """Replace an un-factorable disjunction with a SHORT list of fannable
    concatenations: normalize, cluster by skeleton, concat_merge each cluster,
    keep the merge only if it fans (sim_fanout) else keep that cluster's combos
    separate (each flat combo already fans). Returns (outputs, kind)."""
    norm = [_normalize_groups(c) for c in combos]
    groups = {}
    for c in norm:
        try:
            groups.setdefault(_skeleton_kinds(c), []).append(c)
        except Exception:
            groups.setdefault(("_raw_", c), []).append(c)
    outputs, approx = [], False
    for members in groups.values():
        try:
            cm = concat_merge(members)
        except Exception:
            outputs.extend(members); continue        # keep separate
        if sim_fanout(cm):
            if len(members) > 1:
                approx = True
            outputs.append(cm)
        else:
            outputs.extend(members)                   # keep separate (each fans)
    outputs = list(dict.fromkeys(outputs))
    return outputs, (APPROX if approx else PRECISE)


# --- BORA fan-out simulator (find_class_runs + select_slots, faithful) ------
_SINGLE_FANOUT_MAX = 26       # legs with folded card > this are never pinned


def _class_card(av):
    """Byte count of an sre IN token (a class); 256 for a negated class."""
    s = set()
    for t in av:
        if t[0] == _sre.LITERAL:
            s.add(t[1])
        elif t[0] == _sre.RANGE:
            s.update(range(t[1][0], t[1][1] + 1))
        elif t[0] == _sre.NEGATE:
            return 256
    return len(s)


def _collect_legs(node, in_opt, legs):
    """Mirror data_processor::find_class_runs: gather class legs as (card,
    optional). Alternation branches mark their legs optional; a {0,N} rep
    contributes no guaranteed leg."""
    for op, av in node:
        if op == _sre.IN:
            legs.append((_class_card(av), in_opt))
        elif op in (_sre.MAX_REPEAT, _sre.MIN_REPEAT):
            mn, _mx, sub = av
            if len(sub) == 1 and sub[0][0] == _sre.IN:
                if mn >= 1:
                    legs.append((_class_card(sub[0][1]), in_opt))
            else:
                _collect_legs(sub, in_opt or mn == 0, legs)
        elif op == _sre.BRANCH:
            for alt in av[1]:
                _collect_legs(alt, True, legs)
        elif op == _sre.SUBPATTERN:
            _collect_legs(av[-1], in_opt, legs)
        # LITERAL / others: not a class leg


def _fan_status(regex, budget=100):
    """Predict BORA's aggressive fan-out for `regex` (mirrors select_slots):
      'anchor'           -- pins >=1 GUARANTEED (mandatory) leg => real SED
                            anchor (pm.len() >= 2 with the keyword). GOOD.
      'fanned_no_anchor' -- pins only optional legs (e.g. a top-level
                            disjunction) => fan-out fires but yields no anchor
                            => the BORA pm.len() >= 2 assertion would PANIC. BAD.
      'none'             -- no pinnable leg (all card > SINGLE_FANOUT_MAX) => not
                            fanned at all => no assertion. SAFE.
    Legs over SINGLE_FANOUT_MAX are skipped; mandatory legs are funded first."""
    try:
        legs = []
        _collect_legs(_sre.parse(regex), False, legs)
    except Exception:
        return "none"
    prod, chosen, mandatory = 1, 0, 0
    for want_opt in (False, True):
        for card, opt in legs:
            if opt != want_opt or card > _SINGLE_FANOUT_MAX:
                continue
            if prod * card <= budget:
                prod *= card
                chosen += 1
                if not opt:
                    mandatory += 1
    if chosen == 0:
        return "none"
    return "anchor" if mandatory > 0 else "fanned_no_anchor"


def sim_fanout(regex, budget=100):
    """True iff the fan-out yields a real SED anchor (a mandatory pinned leg)."""
    return _fan_status(regex, budget) == "anchor"


# --- shape-split disjunction guard -----------------------------------------
def _top_split(s, sep="|"):
    """Split `s` on top-level `sep`, honoring [] classes, () groups, \\ escapes."""
    parts, depth, incls, cur, i = [], 0, False, [], 0
    while i < len(s):
        c = s[i]
        if c == "\\":
            cur.append(s[i:i + 2]); i += 2; continue
        if incls:
            cur.append(c); incls = (c != "]"); i += 1; continue
        if c == "[":
            incls = True; cur.append(c); i += 1; continue
        if c == "(":
            depth += 1; cur.append(c); i += 1; continue
        if c == ")":
            depth -= 1; cur.append(c); i += 1; continue
        if c == sep and depth == 0:
            parts.append("".join(cur)); cur = []; i += 1; continue
        cur.append(c); i += 1
    parts.append("".join(cur))
    return parts


def _group_contents(regex):
    """Inner text of every parenthesized group (top-level and nested)."""
    res, starts, incls, i = [], [], False, 0
    while i < len(regex):
        c = regex[i]
        if c == "\\":
            i += 2; continue
        if incls:
            incls = (c != "]"); i += 1; continue
        if c == "[":
            incls = True; i += 1; continue
        if c == "(":
            starts.append(i + 1); i += 1; continue
        if c == ")":
            if starts:
                res.append(regex[starts.pop():i])
            i += 1; continue
        i += 1
    return res


def _has_shape_split_disjunction(regex):
    """True iff some group is a disjunction whose branches differ in skeleton
    shape (length or per-position kind d/L/s). Such a disjunction renders to a
    top-level alternation that collapses the leading SED anchor (the keyword and
    digit borrow both vanish in the forward arm), so it must be split into
    separate concatenations. A same-shape disjunction (pure value-set
    refinement, e.g. ITIN's `(5[0-9]|6[0-5]|..)`) stays a local node and is kept."""
    for content in _group_contents(regex):
        branches = _top_split(content)
        if len(branches) < 2:
            continue
        sigs = set()
        for b in branches:
            try:
                sigs.add(_skeleton_kinds(b))
            except Exception:
                sigs.add(("_raw_", b))
        if len(sigs) > 1:
            return True
    return False


# --- orchestration ---------------------------------------------------------
def _join(atoms):
    return "".join(atoms)


def compress_combos(combos):
    """Compress alternation-free combos into one regex (common BORA+Zombie
    basis). Returns Result(merged, kind, stats). Builder only widens, so
    L(merged) >= union always (soundness)."""
    combos = list(dict.fromkeys(combos))
    n_before = len(combos)
    if n_before == 1:
        return Result([combos[0]], PRECISE, {"before": 1, "after": 1})
    stats = {"before": n_before}
    # Structured collapse needs flat combos. When clean factoring fails, split
    # the would-be disjunction into fannable concatenations (cluster_concat)
    # rather than one dead alternation -- the builder only widens, so every
    # output is a sound superset of its sources.
    try:
        prefix, middles, suffix = factor(combos)
        slotted = [_slots(m) for m in middles]
        if all(s is not None for s in slotted):
            outputs = [_join(prefix) + trie_merge(slotted) + _join(suffix)]
            kind = PRECISE
        else:
            groups = group_by_skeleton(middles)
            groups = drop_subsumed(groups)
            parts = list(dict.fromkeys(compress_group(g) for g in groups))
            if len(parts) == 1:
                outputs = [_join(prefix) + parts[0] + _join(suffix)]
                kind = PRECISE
            else:
                w = widen(parts)
                if w is not None:
                    outputs = [_join(prefix) + w + _join(suffix)]
                    kind = APPROX
                else:
                    outputs, kind = cluster_concat(combos)
    except Exception as e:
        outputs, kind = cluster_concat(combos)
        stats["fallback"] = str(e)
    # Fan-safety: reroute through cluster_concat (fannable concatenations) when
    # an output is either (a) a top-level disjunction with no guaranteed leg
    # (fanned without an anchor), or (b) a disjunction with mixed-shape branches
    # (renders to a top-level alternation that collapses the SED anchor). Both
    # would trip the BORA pm>=2 assertion; the split keeps each branch a clean
    # concatenation. Same-shape value-set disjunctions (the drivers) are kept.
    if any(_fan_status(o) == "fanned_no_anchor"
           or _has_shape_split_disjunction(o) for o in outputs):
        outputs, kind = cluster_concat(combos)
        stats["rerouted"] = True
    stats["after"] = len(outputs)
    stats["kind"] = kind
    return Result(outputs, kind, stats)
