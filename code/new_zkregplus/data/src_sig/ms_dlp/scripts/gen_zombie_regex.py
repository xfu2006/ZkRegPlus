# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code; reviewed by BORA author.
# Date: 06/06/2026
# Purpose: translate each accepted Microsoft SIT record (raw_data_records/*.txt)
#          into the restricted regex dialect accepted by Zombie's
#          regex/bin/TestRegex, emitting TWO files per SIT:
#
#            regex_pat_zombie/<slug>.regex  -- the "pure" pattern regex (PAT),
#                                              the Pattern section only.
#            regex_zombie/<slug>.regex      -- the full proximity policy as a
#                                              single regex, with the window
#                                              baked in both orders:
#                                                (PAT.{0,N}KWS)|(KWS.{0,N}PAT)
#                                              where KWS = (kw1|kw2|...) and
#                                              N = the SIT's proximity.
#
#        Dialect notes (regex/regex.cf, Interpreter.C): bare chars are letters
#        and digits only; '.' is the wildcard; '-' and '^' are legal only inside
#        [...]; every other literal (space, '=', '/', '+', '.', ...) must be a
#        hex byte \xHH; classes support ranges [A-Z] and negation [^...];
#        quantifiers are * + ? {n} {n,m}. There is no /i flag, so
#        case-insensitivity is expanded into classes.
#
#        Each SIT is classified exact / approx / untranslatable. 'approx' means
#        a regex is emitted but a constraint regex cannot express was dropped
#        (checksum, date validity, broad "any combination" blobs); the loss is
#        recorded as a warning. 'untranslatable' SITs are skipped (no file).
#  Results manually sampled and audited by BORA author. Tests in two ways
#  (1) ALL regex are tested (accepted) by Zombie
#  (2) An LLM assisted query is to retrieve samples from web for each
#       rule (e.g., driver license of NY). Then, these samples are 
#       tested against the regex generated. If non-match, it means
#       regexes generated are incorrect and they are removed (mostly
#       because inaccurate specification in the original SIT or
#       too ambiguous translation).
#  ALL regexes generated are verified to accept the web crawled samples
#   in regex_pat_samples/ 
# -------------------------------------------

import os
import re
import sys
import shutil
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import gen_report_header, get_ms_dlp_dir  # noqa: E402

# --- configuration ---------------------------------------------------------
DOCS_DIR    = "docs"
TESTREGEX   = os.path.join("zombie", "regex", "bin", "TestRegex")
VERIFY_TIMEOUT = 8                    # seconds; "Parse Successful!" prints first,
                                      # so a short cap is plenty to capture it

# Two passes run from the SAME pipeline (only the I/O dirs differ): the English
# batch and the international SUPERSET (English + foreign rules with non-English
# keywords stripped; see retrieve_ms_dlp.py). Each Pass names its input records,
# its per-combo pattern + full-policy output dirs, its positive-sample dir, and
# its log. PER-COMBO LAYOUT: a SIT with C>1 expanded combinations (see expand_pat)
# writes <slug>/comb<MM>.regex; a single-combination SIT writes the flat
# <slug>.regex (no churn for the 78% of SITs with no alternation).
class Pass:
    def __init__(self, records, pat_dir, full_dir, sample_dir, log_file):
        self.records, self.pat_dir, self.full_dir = records, pat_dir, full_dir
        self.sample_dir, self.log_file = sample_dir, log_file

PASS_ENGLISH = Pass(
    "raw_data_records", "regex_pat_zombie", "regex_zombie",
    "regex_pat_samples", os.path.join(DOCS_DIR, "gen_zombie_regex.log"))
PASS_INTL = Pass(
    "raw_data_records_international", "regex_pat_zombie_international",
    "regex_zombie_international", "regex_pat_samples_international",
    os.path.join(DOCS_DIR, "gen_zombie_regex_international.log"))
ALL_PASSES = [PASS_ENGLISH, PASS_INTL]

# LIMIT_LOG referenced by the limit-fitting warnings below.
LIMIT_LOG   = os.path.join(DOCS_DIR, "verify_zombie_limit.log")

# --- low-level helpers -----------------------------------------------------
_WORDNUM = {"zero": 0, "a": 1, "an": 1, "one": 1, "two": 2, "three": 3,
            "four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9,
            "ten": 10, "eleven": 11, "twelve": 12}

# parenthesized single-char literals, e.g. "an equal sign (=)" -> '='
_RE_PARENCH = re.compile(r"\(([^()])\)")
# named symbol words -> the literal character they denote
_SYMWORD = {"hyphen": "-", "dash": "-", "space": "_SP_", "comma": ",",
            "dot": ".", "period": ".", "slash": "/", "colon": ":",
            "semicolon": ";", "underscore": "_", "apostrophe": "'",
            "quotation": '"'}


def _count(word):
    """'seven' -> 7; '11' -> 11; otherwise None."""
    w = word.strip().lower()
    if w in _WORDNUM:
        return _WORDNUM[w]
    if w.isdigit():
        return int(w)
    return None


def _esc(s):
    """Render a literal string into the dialect: alphanumerics bare, every other
    byte (space, '.', '/', '=', '+', ...) as \\xHH. '.' -> \\x2E so it is a
    literal dot, not the wildcard."""
    out = []
    for ch in s:
        if ch.isascii() and ch.isalnum():
            out.append(ch)
        else:
            out.append("\\x%02X" % ord(ch))
    return "".join(out)


def _norm(s):
    """Normalize smart quotes / dashes and collapse whitespace."""
    s = (s.replace("‘", "'").replace("’", "'")
          .replace("“", '"').replace("”", '"')
          .replace("–", "-").replace("—", "-"))
    return re.sub(r"\s+", " ", s).strip()


def _cls(chars):
    """Build a character class from literal chars (single char -> bare unit)."""
    uniq = []
    for c in chars:
        if c not in uniq:
            uniq.append(c)
    if len(uniq) == 1:
        return _esc(uniq[0])
    return "[" + "".join(_esc(c) for c in uniq) + "]"


def _rep(unit, lo, hi=None):
    """Apply a quantifier to a single unit (class / escaped byte / group)."""
    if hi is None:
        return unit if lo == 1 else "%s{%d}" % (unit, lo)
    return "%s{%d,%d}" % (unit, lo, hi)


def _letters_excluding(excluded):
    """Class of A-Z/a-z minus the excluded letters (an explicit allow-list, not
    [^...], so digits/symbols are not accidentally admitted)."""
    ex = set(c.upper() for c in excluded)
    up = "".join(c for c in "ABCDEFGHIJKLMNOPQRSTUVWXYZ" if c not in ex)
    return "[" + up + up.lower() + "]"


# --- record parsing --------------------------------------------------------
def parse_sit(path):
    """Read one raw_data_records/<slug>.txt into
    {slug, proximity:int, pattern:str (raw block, 'OR' lines kept), keywords:[]}."""
    slug = os.path.basename(path)[:-4]
    proximity = 300
    pat_lines, keywords, sect = [], [], None
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            s = line.strip()
            if s.startswith("proximity:"):
                m = re.search(r"(\d+)", s)
                if m:
                    proximity = int(m.group(1))
            elif s.startswith("--- pattern ---"):
                sect = "pat"
            elif s.startswith("--- keywords"):
                sect = "kw"
            elif sect == "pat":
                pat_lines.append(line)
            elif sect == "kw" and s:
                keywords.append(s)
    return {"slug": slug, "proximity": proximity,
            "pattern": "\n".join(pat_lines), "keywords": keywords}


# --- pattern -> regex ------------------------------------------------------
def _split_alternatives(block):
    """Recover top-level alternatives. Groups are separated by lone 'OR' lines
    (the capture from retrieve_ms_dlp.py); within a group a line that ends in a
    trailing 'or'/'OR' closes one alternative. Returns a list of alternatives,
    each a list of element phrases (still to be tokenized)."""
    groups = [[]]
    for raw in block.splitlines():
        line = _norm(raw)
        if not line:
            continue
        if line.upper() == "OR":
            groups.append([])
            continue
        # skip negative-example prose, e.g. "... ddddddddd won't match"
        if re.search(r"(wo\s*n'?t|will not|does\s*n'?t|do not)\s+match", line, re.I):
            continue
        groups[-1].append(line)

    alts = []
    for g in groups:
        cur = []
        for line in g:
            if re.search(r"\bor\s*$", line, re.I):
                head = re.sub(r"\s*\bor\s*$", "", line, flags=re.I).strip()
                if head:
                    cur.append(head)
                alts.append(cur)
                cur = []
            else:
                cur.append(re.sub(r"\.\s*$", "", line).strip())
        if cur:
            alts.append(cur)
    return [a for a in alts if a]


def _tokenize(line):
    """Split one element line into atomic elements on 'followed by', stripping a
    leading 'followed by'/'followed either'/'followed'."""
    line = re.sub(r"^followed (by |either )?", "", line, flags=re.I).strip()
    parts = re.split(r"\bfollowed by\b", line, flags=re.I)
    return [p.strip() for p in parts if p.strip()]


_UNIT = r"(?:digit|letter|character|number|alphanumeric)"


def _parse_count(pl):
    """Pull the repetition count out of a phrase. Counts are anchored to the
    unit word (digit/letter/...) so an unrelated value range elsewhere -- e.g.
    the '01 to 12' in 'six digits ... valid MM value of 01 to 12' -- is not
    mistaken for a repetition range. Returns (lo, hi|None) or None."""
    # "between 1-200 <unit>" / "between 1 and 200"
    m = re.search(r"between\s+(\d+)\s*(?:-|and)\s*(\d+)", pl)
    if m:
        return int(m.group(1)), int(m.group(2))
    # "X to Y <unit>" / "X or Y <unit>" (range count directly before the unit)
    m = re.search(r"\b(\w+)\s+(?:to|or)\s+(\w+)\s+" + _UNIT, pl)
    if m and _count(m.group(1)) is not None and _count(m.group(2)) is not None:
        return _count(m.group(1)), _count(m.group(2))
    # "N-M [consecutive] <unit>" e.g. '1-4 numbers', '6-17 consecutive digits'
    m = re.search(r"\b(\d+)\s*-\s*(\d+)\s+(?:consecutive\s+)?" + _UNIT, pl)
    if m:
        return int(m.group(1)), int(m.group(2))
    # hyphenated word range, e.g. 'two-three digits', 'three-four digits'
    # (must precede the single-leading-count match, which would take only 'two')
    m = re.match(r"(\w+)-(\w+)\b", pl)
    if m and _count(m.group(1)) is not None and _count(m.group(2)) is not None:
        return _count(m.group(1)), _count(m.group(2))
    # single leading count (also handles hyphenated 'two-digit', 'one-digit')
    m = re.match(r"(\w+)\b", pl)
    if m and _count(m.group(1)) is not None:
        return _count(m.group(1)), None
    m = re.search(r"of\s+(\d+)\b", pl)
    if m:
        return int(m.group(1)), None
    return None


def _expand_num_ranges(text):
    """Expand 'ranges' prose like 00-12, 21-32, or 80 (and ITIN's '50' to '65')
    into a zero-padded literal alternation. Returns a regex group or None."""
    toks = []
    width = 1
    # endpoints may be quoted on either side, e.g. ITIN's '50' to '65'
    rng = r"['\"]?(\d+)['\"]?\s*(?:-|to)\s*['\"]?(\d+)['\"]?"
    for a, b in re.findall(rng, text):
        width = max(width, len(a), len(b))
        for v in range(int(a), int(b) + 1):
            toks.append((v, max(len(a), len(b))))
    # standalone singletons introduced by 'or'/'and', e.g. '... or 80'
    cleaned = re.sub(rng, " ", text)
    for s in re.findall(r"\b(\d+)\b", cleaned):
        toks.append((int(s), len(s)))
        width = max(width, len(s))
    if not toks:
        return None
    lits = sorted({str(v).zfill(width) for v, _ in toks})
    return "(" + "|".join(lits) + ")"


def _translate_element(phrase):
    """Translate one atomic element phrase to (fragment, kind) where
    kind in {'exact','approx'}, or None if no rule matches (-> untranslatable)."""
    p = _norm(phrase)
    pl = p.lower()
    parens = _RE_PARENCH.findall(p)

    # --- explicit "ddd ddd ddd" digit mask (e.g. US DL "formatted like ...") --
    # space-separated runs of 'd' -> [0-9]{k} groups joined by a literal space.
    # Must precede the plain-digit rule, which would otherwise see "nine digits".
    m = re.search(r"\bd{2,}(?:\s+d{2,})+", p)
    if m and "digit" in pl:
        groups = m.group(0).split()
        return "\\x20".join("[0-9]{%d}" % len(g) for g in groups), "exact"

    # --- numeric value sets / ranges on digits ---------------------------
    # "two digits in the ranges 00-12, 21-32, 61-72, or 80"
    # "two digits '50' to '65', '70' to '88' ... for the fourth and fifth digit"
    # Only a literal value-SET: the word "ranges", quoted values ('50' to '65'),
    # or multi-digit endpoints (00-12). Single-digit "between 0-9" is a per-digit
    # range with a count, handled below -- not a value set.
    if re.search(r"\bdigits?\b", pl) and (
            "range" in pl
            or re.search(r"['\"]\d+['\"]\s*(?:-|to)", pl)):
        grp = _expand_num_ranges(p)
        if grp is not None:
            return grp, "exact"

    # "one digit; any of 0, 1, 2 or 3"  /  "a digit, either 2 or 3"
    m = re.search(r"\bdigit\b.*?(?:any of|either)\s+([0-9 ,or]+)", pl)
    if m:
        ds = re.findall(r"\d", m.group(1))
        if ds:
            return "[" + "".join(ds) + "]", "exact"
    # "one digit zero or one"
    if re.search(r"\bdigit\b.*\bzero or one\b", pl):
        return "[01]", "exact"
    # "(N|any) digit(s) between X-Y" / "... 1 to 9" -> [X-Y] repeated N times
    # (Indonesia DL: 'any nine digits between 0-9'; Medicare: '1 to 9')
    m = re.search(r"(\w+)\s+digits?\s+between\s+(\d)\s*(?:-|to)\s*(\d)", pl)
    if m:
        n = _count(m.group(1)) or 1
        return _rep("[%s-%s]" % (m.group(2), m.group(3)), n), "exact"
    m = re.search(r"digit between\s+(\d)\s*(?:-|to)\s*(\d)", pl)
    if m:
        return "[%s-%s]" % (m.group(1), m.group(2)), "exact"
    # "first digit is in the range 2-6"
    m = re.search(r"digit is in the range\s+(\d)\s*-\s*(\d)", pl)
    if m:
        return "[%s-%s]" % (m.group(1), m.group(2)), "approx"
    # "the digit '9'"  /  "a zero '0'"
    m = re.search(r"the digit\s*['\"]?(\d)['\"]?", pl)
    if m and "or" not in pl:
        return m.group(1), "exact"
    if re.match(r"a zero", pl):
        return "0", "exact"
    # "the digit '8' or '9'"
    m = re.findall(r"['\"]?(\d)['\"]?(?:\s+or\s+)['\"]?(\d)['\"]?", pl)
    if m and "digit" in pl:
        a, b = m[0]
        return "[%s%s]" % (a, b), "exact"
    # bare digit alternation with no "digit" word, e.g. "0 or 1" (Indonesia DL)
    if re.fullmatch(r"\d(?:\s+or\s+\d)+", pl):
        return "[" + "".join(re.findall(r"\d", pl)) + "]", "exact"
    # "either 'A', 'B', 'C', or 'D' (...)" -- quoted letter set (UK NINO suffix)
    if "either" in pl:
        qs = re.findall(r"['\"]([A-Za-z])['\"]", p)
        if qs:
            body = "".join(qs)
            if "not case-sensitive" in pl:
                body = body.upper() + body.lower()
            approx = bool(re.search(r"only certain|allowed|valid", pl))
            return "[" + body + "]", ("approx" if approx else "exact")

    # --- "the string ..." literals ---------------------------------------
    if pl.startswith("the string") or pl.startswith("a string"):
        rest = re.sub(r"^(the|a) string\s+", "", p, flags=re.I)
        # drop trailing semantic clauses ("where pwd isn't preceded ...")
        approx = False
        if " where " in rest:
            rest = rest.split(" where ")[0]
            approx = True
        # split into the alternative literals: on ' or ' and commas
        opts = re.split(r"\s+or\s+|,", rest)
        opts = [o.strip().strip('"').strip("'").strip() for o in opts]
        # remove scraper stray-space-after-dot inside domain-ish literals
        opts = [re.sub(r"\.\s+", ".", o) for o in opts if o]
        if not opts:
            return None
        frag = (_esc(opts[0]) if len(opts) == 1
                else "(" + "|".join(_esc(o) for o in opts) + ")")
        return frag, ("approx" if approx else "exact")

    # --- "any combination of ..." ----------------------------------------
    if "any combination" in pl or pl.startswith("any character"):
        cr = _parse_count(pl)
        # charset: specific (letters/digits + / +) vs broad (symbols/spaces)
        if re.search(r"symbols|special characters|spaces", pl):
            unit, kind = ".", "approx"            # wildcard, over-matches
        elif "aren't" in pl or "not a" in pl or "isn't" in pl:
            excl = parens or re.findall(r"['\"](.)['\"]", p)
            unit = "[^" + "".join(_esc(c) for c in excl) + "]"
            kind = "exact"
        else:
            chars = []
            if "letter" in pl:
                chars += ["A-Z", "a-z"]
            if "digit" in pl:
                chars += ["0-9"]
            if "forward slash" in pl or "/" in parens:
                chars += ["\\x2F"]
            if "plus" in pl or "+" in parens:
                chars += ["\\x2B"]
            unit = "[" + "".join(chars) + "]" if chars else "."
            kind = "exact" if chars else "approx"
        if cr is None:
            cr = (1, None)
        return _rep(unit, cr[0], cr[1]), kind

    # --- "characters that aren't ..." / single excluded char -------------
    if "aren't" in pl or "isn't" in pl or re.search(r"that is not", pl):
        excl = parens or re.findall(r"['\"](.)['\"]", p)
        if excl:
            unit = "[^" + "".join(_esc(c) for c in excl) + "]"
            if "one or more" in pl:
                return unit + "+", "exact"
            cr = _parse_count(pl)
            if cr:
                return _rep(unit, cr[0], cr[1]), "exact"
            return unit, "exact"

    # --- whitespace ------------------------------------------------------
    m = re.search(r"(\w+)\s+to\s+(\w+)\s+whitespace", pl)
    if m:
        lo, hi = _count(m.group(1)), _count(m.group(2))
        if lo is not None and hi is not None:
            return "[\\x20\\x09]{%d,%d}" % (lo, hi), "exact"

    # --- single-letter alternations / case folds -------------------------
    # "A or a", "T or t", "a letter D or d", "I or i"
    m = re.search(r"\b([A-Za-z])\s+or\s+([A-Za-z])\b", p)
    if m and "digit" not in pl and "letter" in pl + " letter":
        a, b = m.group(1), m.group(2)
        if a.lower() == b.lower():
            return "[%s%s]" % (a.upper(), a.lower()), "exact"
        return "[%s%s]" % (a, b), "exact"
    if re.fullmatch(r"[A-Za-z]\s+or\s+[A-Za-z]", p):
        a, b = p.split(" or ")
        a, b = a.strip(), b.strip()
        if a.lower() == b.lower():
            return "[%s%s]" % (a.upper(), a.lower()), "exact"
        return "[%s%s]" % (a, b), "exact"

    # --- letters with enumerated sets ------------------------------------
    # "one letter (N, E, D, F, A, C, U, X)"  -> [NEDFACUX]
    # "Two letters (PA, PB, PC, ...)"        -> (PA|PB|...)
    # "A letter in C, P, H, F, A, T, B, L, J, G" -> [CPHFATBLJG]
    if "letter" in pl:
        cr = _parse_count(pl) or (1, None)
        # enumerated set in parentheses
        mset = re.search(r"\(([A-Za-z][A-Za-z,\s/]*)\)", p)
        inset = re.search(r"letters?\s+in\s+([A-Za-z][A-Za-z,\s]*)", p)
        excl = re.search(r"exclud(?:ing|e)\s+([A-Za-z,\s'\"and]+)", pl)
        excpt = re.search(r"except\s+([A-Za-z,\s'\"and]+)", pl)
        ci = "not case-sensitive" in pl or "case-sensitive" in pl
        # quoted literal after "the letter(s)", e.g. the letters "ET" -> ET
        mlit = re.search(r"letters?\s+['\"]([A-Za-z]{2,})['\"]", p)
        if mlit:
            lit = mlit.group(1)
            if ci:
                return "".join("[%s%s]" % (c.upper(), c.lower())
                               for c in lit), "exact"
            return _esc(lit), "exact"
        if mset:
            toks = [t.strip() for t in re.split(r"[,/]", mset.group(1)) if t.strip()]
            if all(len(t) == 1 for t in toks):
                base = "[" + "".join(toks).upper() + "".join(toks).lower() + "]" \
                    if ci else "[" + "".join(toks) + "]"
                return _rep(base, cr[0], cr[1]), "exact"
            grp = "(" + "|".join(_esc(t) for t in toks) + ")"
            return grp, "exact"
        if inset:
            toks = [t.strip() for t in re.split(r"[,/]", inset.group(1)) if len(t.strip()) == 1]
            if toks:
                base = "[" + "".join(toks).upper() + "".join(toks).lower() + "]"
                return _rep(base, cr[0], cr[1]), "exact"
        if excl or excpt:
            g = (excl or excpt).group(1)
            # only quoted single letters, or standalone single-letter tokens --
            # never letters embedded in a word like "and"
            quoted = re.findall(r"['\"]([A-Za-z])['\"]", g)
            letters = quoted or re.findall(r"(?<![A-Za-z])[A-Za-z](?![A-Za-z])", g)
            base = _letters_excluding(letters)
            return _rep(base, cr[0], cr[1]), "exact"
        # "five letters ... or the digit '9' in place of a letter"
        if "or the digit" in pl or "digit" in pl:
            return _rep("[A-Za-z0-9]", cr[0], cr[1]), "exact"
        return _rep("[A-Za-z]", cr[0], cr[1]), "exact"

    # --- alphanumeric ----------------------------------------------------
    if "alphanumeric" in pl or re.search(r"letters?\s+or\s+digits?|digits?\s+or\s+letters?", pl):
        cr = _parse_count(pl) or (1, None)
        return _rep("[A-Za-z0-9]", cr[0], cr[1]), "exact"

    # --- generic "<n> characters [representing ...]" (cross-refs, loose) --
    m = re.match(r"(\w+)\s+characters?\b", pl)
    if m and _count(m.group(1)) is not None:
        return _rep("[A-Za-z0-9]", _count(m.group(1))), "approx"

    # --- plain digits / "numbers" (with possible dropped semantics) ------
    if re.search(r"\b(?:digits?|numbers?)\b", pl):
        cr = _parse_count(pl) or (1, None)
        approx = bool(re.search(r"check\s*digit|checksum|parity|date|birth|"
                                r"DDMMYY|YYMMDD|MMDDY|gender|century|serial|"
                                r"county|citizenship|indicator|issue|individual",
                                pl, re.I))
        frag = _rep("[0-9]", cr[0], cr[1])
        if "option" in pl:   # matches optional / options (a spec typo) / (optional)
            frag = "(" + frag + ")?"
        return frag, ("approx" if approx else "exact")

    # --- bare check/parity digit phrases ---------------------------------
    if re.search(r"check digit|parity digit|checksum", pl):
        return "[0-9]", "approx"

    # --- pure separators / literal symbols -------------------------------
    sep = _try_separator(p)
    if sep is not None:
        return sep

    return None


def _try_separator(p):
    """Translate a separator / literal-symbol phrase (no digit/letter/string/
    combination content) into a class or escaped byte, honoring 'optional' and
    'two equal signs'. Returns (fragment, 'exact') or None."""
    pl = p.lower()
    if any(w in pl for w in ("digit", "letter", "combination", "the string",
                             "alphanumeric", "character")):
        # 'whitespace characters' handled earlier; everything else here is not
        # a plain separator.
        if "whitespace" not in pl:
            return None
    chars = list(_RE_PARENCH.findall(p))
    # quoted single-char literals, e.g. delimiter of "-" or "+"  (Sweden ID)
    chars += re.findall(r"['\"]([^A-Za-z0-9 ])['\"]", p)
    for word, ch in _SYMWORD.items():
        if re.search(r"\b" + word + r"\b", pl):
            chars.append(" " if ch == "_SP_" else ch)
    if "equal" in pl and "=" not in chars:
        chars.append("=")
    if "greater than" in pl and ">" not in chars:
        chars.append(">")
    if re.search(r"\bplus\b", pl) and "+" not in chars:
        chars.append("+")
    if re.search(r"\bminus\b", pl) and "-" not in chars:
        chars.append("-")
    if "whitespace" in pl and not chars:
        chars = [" "]
    if not chars:
        return None

    # "two equal signs (=)" -> repeated literal
    m = re.search(r"(\w+)\s+equal signs", pl)
    if m and _count(m.group(1)):
        frag = _esc("=") * _count(m.group(1))
    else:
        frag = _cls(chars)

    if "option" in pl:   # matches optional / options (a spec typo) / (optional)
        frag = frag + "?" if (frag.startswith("[") or "\\x" in frag
                              and len(frag) <= 4 or len(frag) == 1) else "(" + frag + ")?"
    return frag, "exact"


def patterns_to_regex(pattern_str):
    """Translate the Pattern block to (regex, status, warnings).
    status in {'exact','approx','untranslatable'}."""
    alts = _split_alternatives(pattern_str)
    if not alts:
        return None, "untranslatable", ["empty pattern"]
    warnings = []
    worst = "exact"
    branch_regexes = []
    for alt in alts:
        frags = []
        for line in alt:
            for elem in _tokenize(line):
                res = _translate_element(elem)
                if res is None:
                    return None, "untranslatable", ["no rule for: %r" % elem]
                frag, kind = res
                frags.append(frag)
                if kind == "approx":
                    worst = "approx"
                    warnings.append("approx element: %r" % elem)
        branch_regexes.append("".join(frags))
    if len(branch_regexes) == 1:
        regex = branch_regexes[0]
    else:
        regex = "(" + "|".join(branch_regexes) + ")"
    return regex, worst, warnings


# Per-SIT relaxations: for a few SITs the spec-faithful translation diverges from
# the real-world format (the spec says e.g. "hyphen"/"check digit", but real
# values differ -- verified via web-crawled samples, docs/reg_pat_samples.log).
# A general rule can't fix these without breaking faithful SITs, so we bend just
# these regexes toward reality via literal (old -> new) substring tweaks. Each
# `old` is a unique substring of that SIT's generated regex. Logged as warnings.
REGEX_RELAXATIONS = {
    "sit-defn-poland-regon-number": [
        (r"[0-9]{9}\x2D[0-9]{5}", r"[0-9]{9}\x2D?[0-9]{5}",
         "real 14-digit REGON has no hyphen -> hyphen optional")],
    "sit-defn-india-gst-number": [
        (r"[\x2D\x20]?[0-9]", r"[\x2D\x20]?[A-Za-z0-9]",
         "real GSTIN check char is alphanumeric, not a digit")],
    "sit-defn-germany-tax-identification-number": [
        (r"[0-9]{2}[0-9]", r"[0-9]{2}\x20?[0-9]",
         "allow optional space before the check digit (real grouping)")],
    "sit-defn-canada-drivers-license-number": [
        (r"[0-9]{5}[0-9][0156]", r"[0-9]{5}\x2D?[0-9][0156]",
         "Quebec format separator before the date-encoded tail")],
}


def _relax(slug, regex, warnings):
    """Apply this SIT's real-world relaxations to its generated regex."""
    for old, new, note in REGEX_RELAXATIONS.get(slug, []):
        if old in regex:
            regex = regex.replace(old, new)
            warnings.append("relaxed to real-world: " + note)
        else:
            warnings.append("relaxation not applied (pattern absent): " + note)
    return regex


# Microsoft's Purview pages mix descriptive PROSE into the keyword list of some
# SITs -- e.g. "The regular expression ... finds content ...", "for example AB",
# "Any combination of ...", "Equal sign (=)" -- and a few leak an example secret
# VALUE as a keyword (e.g. an 86-char base64 storage key). These are not keywords;
# they bloat (and, for >=33-byte tokens, break) the proximity regex KWS. Drop them.
# Real keywords -- including long German compounds and multi-word phrases like
# "Driver's License" / "Permis de Conduire" -- carry none of these markers.
_PROSE_MARKERS = (
    "for example", "any combination of", "followed by", "-or-",
    "the regular expression", "the function", "a keyword from",
    "finds content", "find content", "is found", "matches the pattern",
    "sign (", "symbol (", "whitespace character", "isn't preceded",
)
_RE_SECRET_VALUE = re.compile(r"^[A-Za-z0-9/+]{40,}={0,2}$")  # leaked base64 secret

# A keyword line longer than this is a descriptive SENTENCE, not a keyword (the
# marker list above catches the common ones; this is the backstop for sentences
# that carry no marker). Real keywords -- even long German compounds
# ("Identifikationsnummer", ~21) and multi-word phrases ("Permis de Conduire",
# ~17) -- stay well under it; only prose like "Any combination of 1-200
# characters that are upper- or lowercase letters, digits, ..." exceeds it.
MAX_KEYWORD_LEN = 50


def _is_prose_keyword(kw):
    """True if a 'keyword' line is actually descriptive prose, a leaked example
    value, or an over-long sentence rather than a real keyword."""
    low = kw.lower()
    if any(m in low for m in _PROSE_MARKERS):
        return True
    if len(kw.strip()) > MAX_KEYWORD_LEN:        # very long sentence, not a keyword
        return True
    return bool(_RE_SECRET_VALUE.match(kw))


def _filter_keywords(keywords):
    """Split keywords into (kept, dropped); dropped are prose/leaked values."""
    kept, dropped = [], []
    for k in keywords:
        (dropped if _is_prose_keyword(k) else kept).append(k)
    return kept, dropped


# Minimum keyword length (trimmed; internal spaces between words are KEPT).
# Short acronyms like "id"/"ids"/"dl" are real Purview keywords but, as standalone
# tokens, they pervade ordinary business email ("Request ID: 12345", "User DL"),
# so even whitespace-delimited they flood the proximity policy with false hits
# (Canada-DL flagged 39% of the corpus on "id" alone). Dropping sub-threshold
# keywords trades a little recall for a large precision gain (Canada-DL -> ~4%).
MIN_KEYWORD_LEN = 4


def _filter_short_keywords(keywords):
    """Drop keywords whose trimmed length is below MIN_KEYWORD_LEN (leading/
    trailing whitespace stripped first; spaces between words preserved). Returns
    (kept, dropped)."""
    kept, dropped = [], []
    for k in keywords:
        (kept if len(k.strip()) >= MIN_KEYWORD_LEN else dropped).append(k)
    return kept, dropped


# ===========================================================================
# Zombie compiler-limit approximation  (see docs/verify_zombie_limit.log)
# ===========================================================================
# Zombie's regex->circuit compiler has three hard limits (empirically established,
# verified case-by-case in docs/verify_zombie_limit.log):
#   (1) ceiling: a contiguous FIXED-length match segment is packed base-256 into
#       one BN254 field element, so it must be <=32 bytes. A run/segment >=33 B
#       overflows the 256-bit integer (panic) or emits a malformed expression
#       (parse error). A "segment" = adjacent literals + fixed-count reps
#       (lit{n}, [..]{n}); a variable operator (?, {lo,hi}, *, +) or | splits it.
#   (2) zerolb: ANY zero-lower-bound rep {0,N} (literal or wildcard, every N) is
#       miscompiled to an empty coefficient and rejected. The top-level proximity
#       .{0,N} is exempt -- run_zombie.py strips it and enforces it natively.
#   (3) litgap: a wildcard rep .{m,N}/.*/.+ is safe ONLY when it LEADS its
#       sequence; the moment a literal OR class precedes it, codegen tiles the
#       preceding bytes with the wildcard span into an over-32 B run -> ceiling,
#       for EVERY width (even .{1,5}). This -- NOT "a bounded gap is uncompilable
#       at any width" -- is the real rule (verified G7 in the limit log): e.g.
#       `User Id .{1,200} Password=value` fails because "User Id" sits in FRONT
#       of the gap, whereas a LEADING `.{1,200}B` compiles.
#
# We approximate the generated regex to fit, ALWAYS over-approximating (widening
# the match set) so the non-membership claim stays SOUND (we never clear a doc
# that the exact regex would flag; the cost is extra false positives). Every
# change is recorded as a "zombie-limit[...]" warning citing the limit log.
ZOMBIE_SEG_LIMIT = 32        # max bytes in one packed fixed-length segment

# NOTE: the connection-string SITs used to be rebuilt here from a hand-written
# CONNSTRING_SYNTAX table (a value-only PAT + context-anchor keywords). That was
# the ONLY place the pipeline NARROWED the match set (precision-oriented, not a
# sound non-membership superset) AND it discarded the SITs' real keywords. It is
# gone: connection-string SITs have prose patterns that are untranslatable and an
# intra-pattern literal-preceded gap that Zombie cannot compile (limit (3) above),
# so they now fall through to the GENERAL discard (reason=untranslatable-pattern /
# uncompilable-pat). Every SIT the pipeline emits is therefore a sound
# over-approximation, with real keywords.


def _atoms(s):
    """Split a regex literal string into matched-byte atoms (a bare char, or a
    \\xHH escape = one byte)."""
    out, i = [], 0
    while i < len(s):
        if s[i] == "\\" and s[i + 1:i + 2] == "x":
            out.append(s[i:i + 4]); i += 4
        else:
            out.append(s[i]); i += 1
    return out


def _cap_reps(pat):
    """Cap every {n}/{lo,hi} quantifier count to <=ZOMBIE_SEG_LIMIT so a single
    fixed-count rep cannot overflow the packed segment (e.g. [..]{86} -> {32}).
    Per-rep, not segment-wide: a rep adjacent to long literals is handled by the
    connection-string collapse, the only place that occurs."""
    notes = []

    def repl(m):
        lo, hi = m.group(1), m.group(3)
        if hi is None:
            if int(lo) > ZOMBIE_SEG_LIMIT:
                notes.append("zombie-limit[ceiling]: rep {%s} > %dB packed-run "
                             "limit -> {%d} (see %s)"
                             % (lo, ZOMBIE_SEG_LIMIT, ZOMBIE_SEG_LIMIT, LIMIT_LOG))
                return "{%d}" % ZOMBIE_SEG_LIMIT
            return m.group(0)
        nlo, nhi = min(int(lo), ZOMBIE_SEG_LIMIT), min(int(hi), ZOMBIE_SEG_LIMIT)
        if (nlo, nhi) != (int(lo), int(hi)):
            notes.append("zombie-limit[ceiling]: rep {%s,%s} > %dB -> {%d,%d} "
                         "(see %s)" % (lo, hi, ZOMBIE_SEG_LIMIT, nlo, nhi, LIMIT_LOG))
            return "{%d,%d}" % (nlo, nhi)
        return m.group(0)

    return re.sub(r"\{(\d+)(,(\d+))?\}", repl, pat), notes


def _chop_pat_literals(pat):
    """Chop any contiguous literal run in PAT (outside classes/quantifiers) that
    exceeds ZOMBIE_SEG_LIMIT to its prefix. A prefix matches a superset -> sound."""
    out, run, notes, i = [], [], [], 0

    def flush():
        if len(run) > ZOMBIE_SEG_LIMIT:
            notes.append("zombie-limit[ceiling]: PAT literal run of %dB > %dB "
                         "packed-run limit -> chopped to its %dB prefix (a prefix "
                         "matches a superset -> sound) (see %s)"
                         % (len(run), ZOMBIE_SEG_LIMIT, ZOMBIE_SEG_LIMIT, LIMIT_LOG))
            out.extend(run[:ZOMBIE_SEG_LIMIT])
        else:
            out.extend(run)
        run.clear()

    while i < len(pat):
        c = pat[i]
        if c == "\\" and pat[i + 1:i + 2] == "x":
            run.append(pat[i:i + 4]); i += 4; continue
        if c.isalnum():
            run.append(c); i += 1; continue
        flush()
        if c in "[{":                       # copy class / quantifier block verbatim
            close = "]" if c == "[" else "}"
            j = pat.find(close, i)
            j = j + 1 if j >= 0 else len(pat)
            out.append(pat[i:j]); i = j; continue
        out.append(c); i += 1
    flush()
    return "".join(out), notes


# a VARIABLE-width wildcard rep: .* / .+ / .{m,n} (range). A FIXED .{n} is not
# flagged (it does not trigger the litgap overflow in our corpus).
_RE_VARWILD = re.compile(r"\.(?:\*|\+|\{\d*,\d*\})")


def _uncompilable_reason(pat):
    """Return a reason string if PAT cannot be compiled by Zombie even after the
    sound wideners (cap/chop), else None. The verified killer the wideners cannot
    fix is a VARIABLE wildcard rep (.* / .+ / .{m,n}) PRECEDED by fixed content (a
    literal or class) at the same concatenation level: codegen tiles the preceding
    bytes with the wildcard span into an over-32 B run -> ceiling at EVERY width
    (limit (3) 'litgap'; verified G7 in verify_zombie_limit.log). A LEADING
    wildcard rep compiles, so it is allowed. Paren-level aware: a closed group is
    fixed content in its parent; '|' starts a fresh alternative."""
    stack = [False]                       # seen-fixed-content flag per paren level
    i, n = 0, len(pat)
    while i < n:
        c = pat[i]
        if c == "\\" and i + 1 < n:
            stack[-1] = True; i += 2; continue
        if c == "(":
            stack.append(False); i += 1; continue
        if c == ")":
            if len(stack) > 1:
                stack.pop()
            stack[-1] = True              # the closed group is fixed content here
            i += 1; continue
        if c == "|":
            stack[-1] = False; i += 1; continue
        if c == "[":                      # a class matches a (fixed) byte
            j = pat.find("]", i)
            j = j + 1 if j >= 0 else n
            stack[-1] = True; i = j; continue
        if c == ".":
            m = _RE_VARWILD.match(pat, i)
            if m and stack[-1]:
                return ("not Zombie-compilable: variable wildcard gap %r preceded "
                        "by fixed content (litgap, limit (3); see %s)"
                        % (m.group(0), LIMIT_LOG))
            i = m.end() if m else i + 1   # leading var-wild / bare '.' -> no fixed
            continue
        if not c.isspace():
            stack[-1] = True
        i += 1
    return None


def _approx_keywords(keywords):
    """Chop any keyword longer than ZOMBIE_SEG_LIMIT to a 32-byte prefix."""
    out, notes = [], []
    for k in keywords:
        if len(_atoms(k)) > ZOMBIE_SEG_LIMIT:
            short = "".join(_atoms(k)[:ZOMBIE_SEG_LIMIT])
            notes.append("zombie-limit[ceiling]: keyword %r (%dB) > %dB packed-run "
                         "limit -> chopped to 32B prefix %r (a prefix matches a "
                         "superset -> sound) (see %s)"
                         % (k, len(_atoms(k)), ZOMBIE_SEG_LIMIT, short, LIMIT_LOG))
            k = short
        out.append(k)
    return out, notes


# --- Zombie KWS buildability: the cross-keyword 32 B packed-run limit ---------
# Zombie compiles the WHOLE keyword OR-group KWS=(kw1|kw2|...) into ONE circuit;
# its codegen packs ADJACENT keyword character-runs into 32-byte isZero() terms,
# so two long adjacent keywords overflow -> a malformed .zok (a dangling "+ )")
# that circ rejects (rc 101). Real example (canada-bank): "canada savings bonds"
# and "canada revenue agency" pack into one 41-byte run. Per-keyword chopping to
# <=32 (_approx_keywords) does NOT fix it because the overflow is ACROSS adjacent
# keywords. We prefix-chop every keyword to the largest cap K at which the KWS
# circuit builds. BORA never hits this (one keyword per sig, and it runs as PCRE),
# but to keep BORA and Zombie on a BYTE-IDENTICAL keyword set we chop HERE, in the
# shared pipeline, so both inherit the SAME chopped keywords -- BORA's keywords are
# DRIVEN BY ZOMBIE's limit. Prefix = superset -> sound.
KW_CHOP_LADDER = (24, 18, 15, 12, 10, 8)   # descending caps tried until KWS builds


def _zombie_kws_builds(pat, keywords):
    """True if the Zombie KWS codegen for (pat, KWS(keywords)) is well-formed (no
    >32 B cross-keyword packed-run overflow). Uses TestRegex F (codegen only, no
    circuit build -> fast). Returns True when the binary is unavailable (cannot
    check, so do not chop). The KWS is rendered EXACTLY as sit_to_regex builds it."""
    if not os.path.isfile(TESTREGEX) or not keywords:
        return True
    ws = "[\\x20\\x09\\x0A\\x0D]"
    kws = "(" + "|".join(ws + _esc(k) + ws for k in keywords) + ")"
    try:
        z = subprocess.run([TESTREGEX, "F", "0", "1"],
                           input=pat + " & " + kws + "\n",
                           capture_output=True, text=True, timeout=VERIFY_TIMEOUT)
    except (subprocess.TimeoutExpired, OSError):
        return True
    if "Parse Successful!" not in z.stdout:
        return False                       # codegen itself failed -> not buildable
    return "+ )" not in z.stdout           # dangling '+' = malformed packed run


def _dedupe(seq):
    seen, out = set(), []
    for x in seq:
        if x not in seen:
            seen.add(x); out.append(x)
    return out


def fit_kws_for_zombie(pat, keywords):
    """Prefix-chop the keyword set (only if the full KWS won't build in Zombie) to
    the largest cap K from KW_CHOP_LADDER at which the KWS circuit builds. Returns
    (keywords', notes). The SAME chopped set is returned to BOTH generators."""
    if _zombie_kws_builds(pat, keywords):
        return keywords, []
    for K in KW_CHOP_LADDER:
        chopped = _dedupe(["".join(_atoms(k)[:K]) for k in keywords])
        if _zombie_kws_builds(pat, chopped):
            return chopped, ["zombie-kws-chop[K=%d]: keyword OR-group overflowed "
                             "Zombie's 32B packed-run limit (cross-keyword packing); "
                             "every keyword chopped to its %dB prefix so the KWS "
                             "circuit builds. Prefix = superset -> sound. Applied to "
                             "BORA too for a byte-identical keyword set (see %s)."
                             % (K, K, LIMIT_LOG)]
    K = KW_CHOP_LADDER[-1]
    chopped = _dedupe(["".join(_atoms(k)[:K]) for k in keywords])
    return chopped, ["zombie-kws-chop[K=%d, STILL malformed]: KWS may not build in "
                     "Zombie even at the smallest cap -> FLAGGED (see %s)."
                     % (K, LIMIT_LOG)]


def fit_pat_to_limits(pat):
    """Apply Zombie's SOUND compiler-limit wideners to PAT and report whether it
    can compile. Returns (pat', notes, uncompilable_reason). Wideners (each WIDENS
    the match set -> sound non-membership): cap every {n}/{lo,hi} to <=32; chop any
    >32 B literal run to its 32 B prefix. If after that PAT still cannot build (a
    litgap the wideners cannot remove), uncompilable_reason is a string and the SIT
    must be discarded; otherwise None. Keyword length-capping is separate
    (_approx_keywords), applied by process_sit."""
    notes = []
    pat, n = _cap_reps(pat);          notes += n
    pat, n = _chop_pat_literals(pat); notes += n
    return pat, notes, _uncompilable_reason(pat)


# ===========================================================================
# Alternation expansion  (shared by gen_zombie_regex AND gen_regex_bora)
# ===========================================================================
# A PAT is a sequence of STEPS; a step that is a top-level alternation group
# contributes its branches, everything else is one fixed choice. expand_pat emits
# the full Cartesian product as alternation-free concatenation strings ("combos"),
# RECURSIVELY (nested alternations are expanded too). Both Zombie and BORA build
# from this SAME combo list so their regex sets are structurally identical; Zombie
# bakes one (combo.{0,N}KWS)|(KWS.{0,N}combo) circuit per combo, BORA one
# (keyword,direction) sig per combo. The product is capped at MAX_COMBINATIONS;
# beyond it we TRUNCATE (keep the first N, drop the rest -> a coverage gap, logged
# as combos-truncated). A QUANTIFIED group `(...){n}` is NOT distributed (the
# quantifier is repetition, not a pick) -- it stays an atom.
MAX_COMBINATIONS = 128


def strip_outer_group(s):
    """If `s` is a single group enclosing the WHOLE pattern, return (inner, True);
    else (s, False). Dialect-aware: [..] classes are atomic, \\-escapes are a
    2-char unit, so a `)` inside a class or after an escape is ignored."""
    if not s.startswith("("):
        return s, False
    depth, in_class, i = 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            i += 2; continue
        if in_class:
            if c == "]":
                in_class = False
            i += 1; continue
        if c == "[":
            in_class = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return (s[1:-1], True) if i == len(s) - 1 else (s, False)
        i += 1
    return s, False


def top_level_split(s, sep="|"):
    """Split `s` on `sep` at paren-depth 0 only, treating [..] classes as atomic
    and \\-escapes as a 2-char unit. Nested alternations stay intact."""
    parts, buf, depth, in_class, i = [], [], 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            buf.append(s[i:i + 2]); i += 2; continue
        if in_class:
            buf.append(c)
            if c == "]":
                in_class = False
            i += 1; continue
        if c == "[":
            in_class = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == sep and depth == 0:
            parts.append("".join(buf)); buf = []; i += 1; continue
        buf.append(c); i += 1
    parts.append("".join(buf))
    return parts


def _segments(s):
    """Split a single (alternation-free at top level) sequence into segments:
    ('group', inner) for an UNQUANTIFIED top-level (...) group (expandable), or
    ('atom', text) for any other run (literals, classes, quantified groups). A
    group immediately followed by a quantifier is kept as an atom (parens+quant)."""
    segs, atom, i, n = [], [], 0, len(s)

    def flush():
        if atom:
            segs.append(("atom", "".join(atom))); atom.clear()

    while i < n:
        c = s[i]
        if c == "\\" and i + 1 < n:
            atom.append(s[i:i + 2]); i += 2; continue
        if c == "[":
            j = s.find("]", i); j = j + 1 if j >= 0 else n
            atom.append(s[i:j]); i = j; continue
        if c == "(":
            depth, j = 1, i + 1
            while j < n and depth:
                if s[j] == "\\":
                    j += 2; continue
                if s[j] == "(":
                    depth += 1
                elif s[j] == ")":
                    depth -= 1
                j += 1
            inner = s[i + 1:j - 1]
            k, quant = j, ""
            if k < n and s[k] in "*+?":
                quant = s[k]; k += 1
            elif k < n and s[k] == "{":
                e = s.find("}", k); e = e + 1 if e >= 0 else n
                quant = s[k:e]; k = e
            if quant:                       # quantified group -> atom (not a pick)
                atom.append(s[i:k]); i = k; continue
            flush()
            segs.append(("group", inner)); i = j; continue
        atom.append(c); i += 1
    flush()
    return segs


def _count_combos(s):
    """Number of fully-expanded combinations of `s` (recursive product-of-sums)."""
    parts = top_level_split(s)
    if len(parts) > 1:
        return sum(_count_combos(p) for p in parts)
    prod = 1
    for kind, text in _segments(s):
        if kind == "group":
            prod *= _count_combos(text)
    return prod


def _gen_combos(s, cap):
    """Materialize up to `cap` fully-expanded combinations of `s`, in deterministic
    order (first branch first). Recursive cross-product; alternation eliminated."""
    parts = top_level_split(s)
    if len(parts) > 1:
        out = []
        for p in parts:
            for c in _gen_combos(p, cap):
                out.append(c)
                if len(out) >= cap:
                    return out
        return out
    results = [""]
    for kind, text in _segments(s):
        subs = _gen_combos(text, cap) if kind == "group" else [text]
        new = []
        for pre in results:
            for sub in subs:
                new.append(pre + sub)
                if len(new) >= cap:
                    break
            if len(new) >= cap:
                break
        results = new
    return results


def expand_pat(pat):
    """Expand PAT's alternations into the full Cartesian product of alternation-
    free combos. Returns (combos, n_total, truncated): n_total is the FULL product
    count; combos is its first min(n_total, MAX_COMBINATIONS) members (deduped,
    order preserved); truncated is True when n_total exceeds the cap."""
    n_total = _count_combos(pat)
    raw = _gen_combos(pat, MAX_COMBINATIONS)
    seen, combos = set(), []
    for c in raw:
        if c not in seen:
            seen.add(c); combos.append(c)
    return combos, n_total, n_total > MAX_COMBINATIONS


def sit_to_regex(proximity, pat, keywords, ws_delimit=True):
    """Build the full proximity policy regex (PAT.{0,N}KWS)|(KWS.{0,N}PAT) from a
    PRECOMPUTED (and possibly relaxed) pure pattern. Returns the full regex, or
    None if there are no keywords.

    ws_delimit=True (default): each keyword is flanked by whitespace so a short
    keyword (id, dl, ...) matches a standalone token but NOT a substring of a
    larger word ("consider") or a hyphen/colon-joined token ("Message-ID:"). The
    flanking class is consumed; scanners should pad the document with whitespace
    so a keyword at the very start/end of the text still matches. We use an
    explicit hex class (the Zombie dialect has no \\s; cf. the [\\x20\\x09] usage
    above) and keep the wrappers INSIDE the outer (...) group so the structure --
    and run_zombie's extract_parts round-trip -- is preserved.

    ws_delimit=False: keywords are matched as bare substrings. Used for the
    connection-string SITs, whose context anchors sit inside hostnames/syntax
    ("...redis.cache.windows.net:6380", "User Id=") and would never be
    whitespace-flanked."""
    if not keywords:
        return None
    if ws_delimit:
        ws = "[\\x20\\x09\\x0A\\x0D]"      # space, tab, LF, CR
        kws = "(" + "|".join(ws + _esc(k) + ws for k in keywords) + ")"
    else:
        kws = "(" + "|".join(_esc(k) for k in keywords) + ")"
    n = str(proximity)
    return "({p}.{{0,{n}}}{k})|({k}.{{0,{n}}}{p})".format(p=pat, k=kws, n=n)


# --- I/O + verification ----------------------------------------------------
def reset_dir(path):
    """Create the directory; if it exists, remove ALL of its contents first."""
    if os.path.isdir(path):
        shutil.rmtree(path)
    os.makedirs(path)


def _combo_path(directory, slug, idx, n_combos):
    """Per-combo output path: <dir>/<slug>.regex when C==1 (no churn for the 78%
    of SITs with no alternation), else <dir>/<slug>/comb<MM>.regex."""
    if n_combos == 1:
        return os.path.join(directory, slug + ".regex")
    sub = os.path.join(directory, slug)
    os.makedirs(sub, exist_ok=True)
    return os.path.join(sub, "comb%02d.regex" % idx)


def write_zombie_sit(p, res):
    """Write this SIT's per-combo pure-pattern (p.pat_dir) and full-policy
    (p.full_dir) regexes; return the list of full proximity regexes (one per combo,
    each (combo.{0,N}KWS)|(KWS.{0,N}combo)) for parse verification."""
    slug, combos, kws = res["slug"], res["combos"], res["keywords"]
    n = len(combos)
    fulls = []
    for idx, combo in enumerate(combos):
        full = sit_to_regex(res["proximity"], combo, kws)
        with open(_combo_path(p.pat_dir, slug, idx, n), "w") as f:
            f.write(combo + "\n")
        with open(_combo_path(p.full_dir, slug, idx, n), "w") as f:
            f.write(full + "\n")
        fulls.append(full)
    return fulls


def verify_by_run_zombie(regex):
    """Lightweight syntax check, always run as part of the workflow: feed the
    regex to TestRegex in estimate mode (setting A) and report whether it
    parsed. We only care that 'Parse Successful!' is printed; the analysis that
    follows is irrelevant, so a timeout after a successful parse still counts as
    OK. Returns True/False, or None if the binary is unavailable."""
    if not os.path.isfile(TESTREGEX):
        return None
    cmd = ["stdbuf", "-oL", TESTREGEX, "A"]
    try:
        r = subprocess.run(cmd, input=regex + "\n", capture_output=True,
                           text=True, timeout=VERIFY_TIMEOUT)
        return "Parse Successful!" in r.stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        return "Parse Successful!" in out
    except FileNotFoundError:
        # stdbuf missing; retry without it
        try:
            r = subprocess.run([TESTREGEX, "A"], input=regex + "\n",
                               capture_output=True, text=True,
                               timeout=VERIFY_TIMEOUT)
            return "Parse Successful!" in r.stdout
        except Exception:
            return None


# --- positive self-test samples -------------------------------------------
# Samples live in <sample_dir>/<slug>.txt, generated per-SIT by web-verified
# agents (see docs/reg_pat_samples.log). Positive-only by design. Our dialect is
# a strict subset of Python regex, so re is a faithful oracle with no translation.
# A sample passes if it matches ANY of the expanded combos (their union is the
# original PAT's language, modulo truncation -- see expand_pat). fullmatch for
# identifier SITs. SUBSTRING_SITS (search instead of fullmatch) was only ever the
# connection-string SITs, which are now discarded -> the set is empty, but kept so
# a future substring-detector SIT can opt in.
SUBSTRING_SITS = set()


def _load_samples(slug, sample_dir):
    path = os.path.join(sample_dir, slug + ".txt")
    if not os.path.isfile(path):
        return None
    with open(path) as f:
        lines = [ln.strip() for ln in f if ln.strip()]
    return lines or None


def test_samples(slug, combos, sample_dir):
    """Positive self-test: does some expanded combo accept every web-verified
    sample for this SIT? Returns (n_pass, n_total, [unmatched]) or None (no
    samples). A sample matches the SIT iff ANY combo matches it."""
    samples = _load_samples(slug, sample_dir)
    if not samples:
        return None
    rxs = []
    for c in combos:
        try:
            rxs.append(re.compile(c))
        except re.error:
            pass
    if not rxs:
        return 0, len(samples), list(samples)
    use_search = slug in SUBSTRING_SITS
    def ok(s):
        return any((rx.search(s) if use_search else rx.fullmatch(s)) for rx in rxs)
    miss = [s for s in samples if not ok(s)]
    return len(samples) - len(miss), len(samples), miss


# --- shared per-SIT pipeline ----------------------------------------------
# Itemized reason vocabulary, emitted here so BOTH gen_zombie_regex and
# gen_regex_bora (which calls process_sit) log identical reasons.
DISCARD_REASONS = ("untranslatable-pattern", "no-keywords", "uncompilable-pat",
                   "samples-failed")
APPROX_TAGS = (("approx-translation", "approx element"),
               ("real-world-relax", "relaxed to real-world"),
               ("limit-widen", "zombie-limit["),
               ("combos-truncated", "combos-truncated"))


def _skip(slug, reason, detail, warnings):
    return {"status": "SKIP", "slug": slug, "reason": reason, "detail": detail,
            "warnings": list(warnings)}


def process_sit(rec, sample_dir):
    """The shared translate -> relax -> keyword-filter -> empty-gate -> fit/discard
    -> expand pipeline. Identical for Zombie and BORA; only final assembly differs.
    Returns a SKIP dict {status,slug,reason,detail,warnings} OR an emit dict
    {status(OK|APPROX),slug,proximity,combos,keywords,warnings,n_total,truncated,
    samples}. samples = test_samples(slug, combos, sample_dir)."""
    slug = rec["slug"]
    warnings = []
    pat, status, warns = patterns_to_regex(rec["pattern"])
    warnings += warns
    if status == "untranslatable":
        return _skip(slug, "untranslatable-pattern",
                     warns[0] if warns else "no usable pattern prose", warnings)
    pat = _relax(slug, pat, warnings)

    kept, dropped = _filter_keywords(rec["keywords"])
    for d in dropped:
        warnings.append("dropped non-keyword line (prose/sentence/leak): %r" % d)
    kept, short = _filter_short_keywords(kept)
    for d in short:
        warnings.append("dropped short keyword (trimmed len < %d): %r"
                        % (MIN_KEYWORD_LEN, d))
    if not kept:
        return _skip(slug, "no-keywords",
                     "no keyword survived filtering (prose / len<%d / len>%d / "
                     "non-English all removed)" % (MIN_KEYWORD_LEN, MAX_KEYWORD_LEN),
                     warnings)

    pat, znotes, reason = fit_pat_to_limits(pat)
    warnings += znotes
    if reason:
        return _skip(slug, "uncompilable-pat", reason, warnings)
    if znotes and status == "exact":
        status = "approx"
    kept, knotes = _approx_keywords(kept)
    warnings += knotes
    if knotes and status == "exact":
        status = "approx"
    # chop the keyword set to fit Zombie's KWS packed-run limit (cross-keyword
    # packing); the SAME chopped set feeds Zombie's KWS AND BORA's per-keyword KW.
    kept, kbnotes = fit_kws_for_zombie(pat, kept)
    warnings += kbnotes
    if kbnotes and status == "exact":
        status = "approx"

    combos, n_total, truncated = expand_pat(pat)
    if truncated:
        warnings.append("combos-truncated: %d combos > %d -> kept %d, dropped %d "
                        "paths NOT covered (coverage gap) (see expand_pat)"
                        % (n_total, MAX_COMBINATIONS, len(combos),
                           n_total - len(combos)))
        status = "approx"
    return {"status": "OK" if status == "exact" else "APPROX", "slug": slug,
            "proximity": rec["proximity"], "combos": combos, "keywords": kept,
            "warnings": warnings, "n_total": n_total, "truncated": truncated,
            "samples": test_samples(slug, combos, sample_dir)}


def write_log(p, rows):
    """Write the itemized per-SIT log for one pass. Every dropped/altered rule
    carries a greppable reason=<code> plus a human detail line, and the bottom
    tallies discards and approximations by reason."""
    counts = {"OK": 0, "APPROX": 0, "SKIP": 0}
    for r in rows:
        counts[r["status"]] += 1
    with open(p.log_file, "w") as f:
        f.write(gen_report_header("ms_dlp pattern->Zombie regex generation log"))
        f.write("\n\n")
        f.write("input:   %s/\n" % p.records)
        f.write("outputs: %s/  (per-combo pure pattern: <slug>.regex or <slug>/comb<MM>.regex)\n"
                % p.pat_dir)
        f.write("         %s/  (per-combo full proximity policy, same layout)\n\n"
                % p.full_dir)
        f.write("note: PAT alternations are expanded into the cross-product of\n")
        f.write("  alternation-free combos (cap %d, then TRUNCATE); each combo is\n"
                % MAX_COMBINATIONS)
        f.write("  one Zombie circuit. 'zombie-limit[...]' warnings widen the match\n")
        f.write("  set (sound). Discard reasons: %s. Limits: %s\n\n"
                % (", ".join(DISCARD_REASONS), LIMIT_LOG))
        f.write("== PER-SIT RESULTS ==\n")
        for r in rows:
            if r["status"] == "SKIP":
                f.write("[SKIP  ] %s  reason=%s\n" % (r["slug"], r["reason"]))
                f.write("           - %s\n" % r["detail"])
                for w in r["warnings"]:
                    f.write("           - %s\n" % w)
                continue
            vtag = {True: "parse=OK", False: "parse=FAIL",
                    None: "parse=?"}[r["verify"]]
            samp = r.get("samples")
            stag = "  samples=%d/%d" % (samp[0], samp[1]) if samp else ""
            ctag = "  combos=%d" % len(r["combos"])
            if r["truncated"]:
                ctag += "/%d(trunc)" % r["n_total"]
            f.write("[%-6s] %s  keywords=%d%s  files=%d  %s%s\n"
                    % (r["status"], r["slug"], len(r["keywords"]), ctag,
                       r["n_files"], vtag, stag))
            for w in r["warnings"]:
                f.write("           - %s\n" % w)
            if samp:
                for s in samp[2]:
                    f.write("           ! sample not matched: %r\n" % s)
        # tallies
        s_pass = sum(r["samples"][0] for r in rows if r.get("samples"))
        s_tot = sum(r["samples"][1] for r in rows if r.get("samples"))
        n_combo = sum(len(r["combos"]) for r in rows if r["status"] != "SKIP")
        max_combo = max([len(r["combos"]) for r in rows if r["status"] != "SKIP"],
                        default=0)
        f.write("\n== DISCARDED BY REASON ==\n")
        for code in DISCARD_REASONS:
            n = sum(1 for r in rows if r["status"] == "SKIP" and r["reason"] == code)
            f.write("  %-22s %d\n" % (code, n))
        f.write("\n== APPROXIMATED BY REASON ==\n")
        for code, mark in APPROX_TAGS:
            n = sum(1 for r in rows if r["status"] != "SKIP"
                    and any(mark in w for w in r.get("warnings", [])))
            f.write("  %-22s %d\n" % (code, n))
        f.write("\n== SUMMARY ==\n")
        f.write("total SITs: %d\n" % len(rows))
        f.write("OK:         %d\n" % counts["OK"])
        f.write("APPROX:     %d\n" % counts["APPROX"])
        f.write("SKIP:       %d\n" % counts["SKIP"])
        f.write("combos:     %d total  (max %d per SIT; one Zombie circuit each)\n"
                % (n_combo, max_combo))
        f.write("samples:    %d/%d positive matches\n" % (s_pass, s_tot))
    return counts, s_pass, s_tot, n_combo


def run_pass(p, discard_on_sample_miss):
    """Run one pass: read p.records, run gz.process_sit per SIT, write per-combo
    Zombie regexes, verify, log. discard_on_sample_miss=True (international)
    converts a sample-miss into reason=samples-failed; False (English) keeps the
    rule and records the miss (a miss there is a regression -> caught at review)."""
    reset_dir(p.pat_dir)
    reset_dir(p.full_dir)
    if not os.path.isdir(p.records):
        print("[gen] %s : records dir %s absent -- skipping pass" % (p.log_file, p.records))
        return
    rows = []
    for fname in sorted(os.listdir(p.records)):
        if not fname.endswith(".txt"):
            continue
        rec = parse_sit(os.path.join(p.records, fname))
        res = process_sit(rec, p.sample_dir)
        if res["status"] == "SKIP":
            rows.append(res)
            continue
        samp = res.get("samples")
        if discard_on_sample_miss and samp and samp[0] < samp[1]:
            rows.append(_skip(res["slug"], "samples-failed",
                              "pattern matched only %d/%d web-verified samples -> "
                              "discarded (international auto-discard policy)"
                              % (samp[0], samp[1]), res["warnings"]))
            continue
        fulls = write_zombie_sit(p, res)
        res["n_files"] = len(fulls)
        res["verify"] = (all(verify_by_run_zombie(fr) for fr in fulls)
                         if fulls else None)
        rows.append(res)
    counts, s_pass, s_tot, n_combo = write_log(p, rows)
    print("[gen] %s : SITs=%d OK=%d APPROX=%d SKIP=%d  combos=%d  samples=%d/%d"
          % (p.log_file, len(rows), counts["OK"], counts["APPROX"],
             counts["SKIP"], n_combo, s_pass, s_tot))


# -------------------------------------------
# MAIN
# -------------------------------------------
def main():
    # resolve all relative paths against the ms_dlp dir (never cwd / hardcoded).
    os.chdir(get_ms_dlp_dir())
    os.makedirs(DOCS_DIR, exist_ok=True)
    run_pass(PASS_ENGLISH, discard_on_sample_miss=False)
    run_pass(PASS_INTL, discard_on_sample_miss=True)


if __name__ == "__main__":
    main()
