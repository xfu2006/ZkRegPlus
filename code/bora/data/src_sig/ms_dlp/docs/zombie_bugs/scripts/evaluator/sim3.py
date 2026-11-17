# sim2 corrected to the generated .zok: only the final tapes that the .zok adds to
# accum count, plus an exact procCheck. Tape roles read from each unit's .zok.
import os, re, sys
try: import re._parser as sp
except ImportError: import sre_parse as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rules import zombie_units
ZDIR = os.path.expanduser('~/tmp/same_sample_work/zok')
UNITS = []
for nm, full, pat, kws, prox in zombie_units():
    z = open(os.path.join(ZDIR, nm.replace('/', '__') + '.zok')).read()
    fa, fb = re.search(r'assert\(procCheck\((f_\d+), (f_\d+)\)\)', z).groups()
    acc = set(re.findall(r'accum = accum \+ (f_\d+)\[i\]', z))
    PD = int(re.search(r'const u32 PROXY_DIST = (\d+)', z).group(1))
    rp, rk = re.compile(pat.encode()), re.compile(kws.encode())
    UNITS.append(dict(nm=nm, rp=rp, rk=rk, wp=sp.parse(pat).getwidth(), wk=sp.parse(kws).getwidth(),
                      pacc=fa in acc, kacc=fb in acc, PD=PD))
def body0(buf):
    s = buf.find(b'\r\n\r\n'); return None if s < 0 else s + 5
def all_ends(buf, rx, w, b0):
    lo, hi = w; n = len(buf); out = set()
    for s in range(b0, n):
        for e in range(s + max(lo, 1), min(n, s + hi) + 1):
            if rx.fullmatch(buf, s, e): out.add(e - 1)
    return out
def unit_rejects(buf, u):
    L = len(buf); b0 = body0(buf)
    if b0 is None: return False          # start tape all 0: no tape fires
    ph = u['rp'].search(buf, b0) is not None
    kh = u['rk'].search(buf, b0) is not None
    if (u['pacc'] and ph) or (u['kacc'] and kh): return True
    if not (ph and kh): return False      # one tape all 0: procCheck holds
    el = all_ends(buf, u['rp'], u['wp'], b0); er = all_ends(buf, u['rk'], u['wk'], b0)
    PD = u['PD']
    return any(PD <= i < L - PD and any(i - PD <= j < i + PD for j in el) for i in er)
def rejects(buf):
    return [u['nm'] for u in UNITS if unit_rejects(buf, u)]
