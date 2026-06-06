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
# -------------------------------------------

import os
import re
import sys
import shutil
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import gen_report_header  # noqa: E402

# --- configuration ---------------------------------------------------------
RECORDS_DIR = "raw_data_records"      # input : per-SIT specs
PAT_DIR     = "regex_pat_zombie"      # output: pure pattern regex
FULL_DIR    = "regex_zombie"          # output: full proximity policy
DOCS_DIR    = "docs"
LOG_FILE    = os.path.join(DOCS_DIR, "gen_zombie_regex.log")
TESTREGEX   = os.path.join("zombie", "regex", "bin", "TestRegex")
VERIFY_TIMEOUT = 8                    # seconds; "Parse Successful!" prints first,
                                      # so a short cap is plenty to capture it

# --- low-level helpers -----------------------------------------------------
_WORDNUM = {"a": 1, "an": 1, "one": 1, "two": 2, "three": 3, "four": 4,
            "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9,
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
    for a, b in re.findall(r"(\d+)\s*(?:-|to)\s*['\"]?(\d+)", text):
        width = max(width, len(a), len(b))
        for v in range(int(a), int(b) + 1):
            toks.append((v, max(len(a), len(b))))
    # standalone singletons introduced by 'or'/'and', e.g. '... or 80'
    cleaned = re.sub(r"(\d+)\s*(?:-|to)\s*['\"]?\d+", " ", text)
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
            letters = re.findall(r"[A-Za-z]", (excl or excpt).group(1))
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
        if "optional" in pl:
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

    if "optional" in pl:
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


def sit_to_regex(proximity, pattern_str, keywords):
    """Build the full proximity policy regex (PAT.{0,N}KWS)|(KWS.{0,N}PAT).
    Returns (full_regex, status, warnings); reuses patterns_to_regex for PAT."""
    pat, status, warns = patterns_to_regex(pattern_str)
    if pat is None:
        return None, status, warns
    if not keywords:
        return None, "untranslatable", ["no keywords"]
    kws = "(" + "|".join(_esc(k) for k in keywords) + ")"
    n = str(proximity)
    full = "({p}.{{0,{n}}}{k})|({k}.{{0,{n}}}{p})".format(p=pat, k=kws, n=n)
    return full, status, warns


# --- I/O + verification ----------------------------------------------------
def reset_dir(path):
    """Create the directory; if it exists, remove ALL of its contents first."""
    if os.path.isdir(path):
        shutil.rmtree(path)
    os.makedirs(path)


def write_one(directory, slug, regex):
    with open(os.path.join(directory, slug + ".regex"), "w") as f:
        f.write(regex + "\n")


def verify(regex):
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
# Realistic instances of each SIT, written by hand from general knowledge of the
# identifier (NOT derived from the generated regex and NOT copied from the MS
# spec), so a too-strict translation shows up as a non-match. Value-constrained
# fields use valid in-range instances. Positive-only by design. Connection-string
# / secret-key SITs are intentionally absent (the pattern detects a substring of
# a longer string, so fullmatch is not the right oracle) and report n/a.
SAMPLES = {
    "sit-defn-aba-routing": ["021000021", "111000025"],
    "sit-defn-australia-bank-account-number": ["062-000", "013-006"],
    "sit-defn-australia-business-number": ["51 824 753 556", "83 914 571 673"],
    "sit-defn-australia-drivers-license-number": ["12345678", "1234AB"],
    "sit-defn-australia-medical-account-number": ["2123456701", "4987654328"],
    "sit-defn-australia-passport-number": ["N1234567", "PA1234567"],
    "sit-defn-australia-tax-file-number": ["123 456 789", "123456782"],
    "sit-defn-austria-social-security-number": ["1234010170", "9876311285"],
    "sit-defn-austria-value-added-tax": ["ATU12345678", "atu12345678"],
    "sit-defn-canada-bank-account-number": ["12345-678", "012345678"],
    "sit-defn-canada-drivers-license-number": ["123456-789", "1234567"],
    "sit-defn-denmark-personal-identification-number": ["010170-1234", "0101701234"],
    "sit-defn-drug-enforcement-agency-number": ["AB1234563", "FS9876543"],
    "sit-defn-estonia-drivers-license-number": ["ET123456", "et654321"],
    "sit-defn-estonia-passport-number": ["A1234567", "K7654321"],
    "sit-defn-estonia-personal-identification-code": ["37605030299", "49001012333"],
    "sit-defn-finland-passport-number": ["AB1234567", "XY7654321"],
    "sit-defn-germany-tax-identification-number": ["12 345 678 901", "12345678901"],
    "sit-defn-germany-value-added-tax-number": ["DE123456789", "de 123 456 789"],
    "sit-defn-india-drivers-license-number": ["MH12 2013 1234567", "DL0120151234567"],
    "sit-defn-india-gst-number": ["27AAPFU0939F1ZV", "29ABCDE1234F2Z5"],
    "sit-defn-india-permanent-account-number": ["AAPFU0939F", "ABCDE1234F"],
    "sit-defn-india-voter-id-card": ["ABC1234567", "XYZ7654321"],
    "sit-defn-indonesia-drivers-license-number": ["401234567890", "1234-5678-901234"],
    "sit-defn-indonesia-identity-card-number": ["3201011503900001", "3174052208850002"],
    "sit-defn-indonesia-passport-number": ["A1234567", "AB123456"],
    "sit-defn-italy-drivers-license-number": ["MV1234567X", "RA7654321B"],
    "sit-defn-italy-fiscal-code": ["RSSMRA85T10A562S", "VRDLGI70A01F205X"],
    "sit-defn-italy-value-added-tax-number": ["IT12345678901", "it12345678901"],
    "sit-defn-lithuania-passport-number": ["12345678", "ABCD5678"],
    "sit-defn-malaysia-identification-card-number": ["900101-14-5678", "880520145678"],
    "sit-defn-malaysia-passport-number": ["A12345678", "H87654321"],
    "sit-defn-medicare-beneficiary-identifier-card": ["1EG4-TE5-MK73", "1EG4TE5MK73"],
    "sit-defn-netherlands-citizens-service-number": ["123 456 782", "123456782"],
    "sit-defn-netherlands-passport-number": ["AB1234567", "123456789"],
    "sit-defn-new-zealand-bank-account-number": ["01 0902 0068389 00", "12-3456-7890123-01"],
    "sit-defn-new-zealand-drivers-license-number": ["AB123456", "XY654321"],
    "sit-defn-new-zealand-inland-revenue-number": ["12-345-678", "123 456 789"],
    "sit-defn-new-zealand-ministry-of-health-number": ["ABC1234", "XYZ4321"],
    "sit-defn-new-zealand-social-welfare-number": ["123-456-789", "123456789"],
    "sit-defn-philippines-national-identification-number": ["1234-5678-9012", "123456789012"],
    "sit-defn-philippines-passport-number": ["A123456", "EB1234567"],
    "sit-defn-philippines-unified-multi-purpose-identification-number": ["1234-5678901-2", "0011-1234567-8"],
    "sit-defn-poland-drivers-license-number": ["12345/67/8901", "00001/01/2015"],
    "sit-defn-poland-regon-number": ["123456785", "123456789-12345"],
    "sit-defn-qatari-id-card-number": ["28412345678", "30198765432"],
    "sit-defn-romania-drivers-license-number": ["B12345678", "912345678"],
    "sit-defn-romania-passport-number": ["12345678", "123456789"],
    "sit-defn-south-africa-identification-number": ["8001015009087", "9202204720082"],
    "sit-defn-sweden-national-id": ["19900101-1234", "900101-1234"],
    "sit-defn-sweden-tax-identification-number": ["900101-1234", "19900101+1234"],
    "sit-defn-uk-drivers-license-number": ["MORGA657054SM9IJ", "SMITH712161S99AB"],
    "sit-defn-uk-electoral-roll-number": ["AB1234", "XY12"],
    "sit-defn-uk-national-health-service-number": ["123 456 7890", "1234567881"],
    "sit-defn-uk-national-insurance-number": ["AB123456C", "QQ 12 34 56 C"],
    "sit-defn-us-bank-account-number": ["12345678", "123456789012"],
    "sit-defn-us-drivers-license-number": ["123 456 789"],
    "sit-defn-us-individual-taxpayer-identification-number": ["955-70-1234", "955701234"],
    "sit-defn-us-uk-passport-number": ["A12345678", "912345678"],
}


def test_samples(slug, regex):
    """Positive self-test: does the pure pattern regex fullmatch every known
    sample for this SIT? Returns (n_pass, n_total, [unmatched]) or None if no
    samples are registered. Our dialect is a strict subset of Python regex, so
    re.fullmatch is a faithful oracle with no translation needed."""
    samples = SAMPLES.get(slug)
    if not samples:
        return None
    try:
        rx = re.compile(regex)
    except re.error:
        return 0, len(samples), list(samples)
    miss = [s for s in samples if not rx.fullmatch(s)]
    return len(samples) - len(miss), len(samples), miss


def write_log(rows):
    counts = {"OK": 0, "APPROX": 0, "SKIP": 0}
    for r in rows:
        counts[r["status"]] += 1
    with open(LOG_FILE, "w") as f:
        f.write(gen_report_header("ms_dlp pattern->regex generation log"))
        f.write("\n\n")
        f.write("outputs:\n")
        f.write("  %s/  (pure pattern regex)\n" % PAT_DIR)
        f.write("  %s/  (full proximity policy)\n\n" % FULL_DIR)
        f.write("== PER-SIT RESULTS ==\n")
        for r in rows:
            vtag = ""
            if r["status"] != "SKIP":
                vtag = {True: "  parse=OK", False: "  parse=FAIL",
                        None: "  parse=?"}[r["verify"]]
            samp = r.get("samples")
            stag = "  samples=%d/%d" % (samp[0], samp[1]) if samp else ""
            f.write("[%-6s] %s%s%s\n" % (r["status"], r["slug"], vtag, stag))
            for w in r["warnings"]:
                f.write("           - %s\n" % w)
            if samp:
                for s in samp[2]:
                    f.write("           ! sample not matched: %r\n" % s)
        s_pass = sum(r["samples"][0] for r in rows if r.get("samples"))
        s_tot = sum(r["samples"][1] for r in rows if r.get("samples"))
        f.write("\n== SUMMARY ==\n")
        f.write("total:   %d\n" % len(rows))
        f.write("OK:      %d\n" % counts["OK"])
        f.write("APPROX:  %d\n" % counts["APPROX"])
        f.write("SKIP:    %d\n" % counts["SKIP"])
        f.write("samples: %d/%d positive matches\n" % (s_pass, s_tot))
    return counts, s_pass, s_tot


# -------------------------------------------
# MAIN
# -------------------------------------------
def main():
    # this script lives in scripts/, one level below ms_dlp/.
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir))
    os.makedirs(DOCS_DIR, exist_ok=True)
    reset_dir(PAT_DIR)
    reset_dir(FULL_DIR)

    rows = []
    for fname in sorted(os.listdir(RECORDS_DIR)):
        if not fname.endswith(".txt"):
            continue
        rec = parse_sit(os.path.join(RECORDS_DIR, fname))
        pat, status, warns = patterns_to_regex(rec["pattern"])
        if status == "untranslatable":
            rows.append({"slug": rec["slug"], "status": "SKIP",
                         "warnings": warns, "verify": None})
            continue
        full, _, _ = sit_to_regex(rec["proximity"], rec["pattern"],
                                  rec["keywords"])
        if full is None:
            rows.append({"slug": rec["slug"], "status": "SKIP",
                         "warnings": ["no keywords"], "verify": None})
            continue
        write_one(PAT_DIR, rec["slug"], pat)
        write_one(FULL_DIR, rec["slug"], full)
        rows.append({"slug": rec["slug"],
                     "status": "OK" if status == "exact" else "APPROX",
                     "warnings": warns, "verify": verify(full),
                     "samples": test_samples(rec["slug"], pat)})

    counts, s_pass, s_tot = write_log(rows)
    print("[gen] %s : total=%d OK=%d APPROX=%d SKIP=%d  samples=%d/%d"
          % (LOG_FILE, len(rows), counts["OK"], counts["APPROX"],
             counts["SKIP"], s_pass, s_tot))


if __name__ == "__main__":
    main()
