# Direct evaluator of a generated Zombie .zok (the subset TestRegex emits).
# Translates ZoKrates to Python, field = curve25519 scalar (Spartan). Records every assert.
import re, os
P = 2**252 + 27742317777372353535851937790883648493
ZDIR = os.path.expanduser('~/tmp/same_sample_work/zok')
class G(list):  # bounds guard: ZoKrates would reject a negative or out-of-range index
    def __getitem__(self, k):
        if not (0 <= k < len(self)): raise IndexError(k)
        return list.__getitem__(self, k)
def translate(src, L, guard=False):
    src = src.replace('const u32 STR_LENGTH = 1000', 'const u32 STR_LENGTH = %d' % L, 1)
    out = []
    for ln in src.split('\n'):
        ind = re.match(r'^\s*', ln).group(0); s = ln.strip()
        if not s: continue
        m = re.match(r'^const u32 (\w+) = (\d+)$', s)
        if m: out.append('%s = %s' % m.groups()); continue
        m = re.match(r'^def (\w+)\((.*)\) -> .*:$', s)
        if m:
            args = [a.split()[-1] for a in m.group(2).split(',')]
            out.append(ind + 'def %s(%s):' % (m.group(1), ', '.join(args))); continue
        m = re.match(r'^for u32 (\w+) in (.+)\.\.(.+) do$', s)
        if m: out.append(ind + 'for %s in range(%s, %s):' % m.groups()); continue
        if s == 'endfor': out.append(ind + 'pass'); continue
        m = re.match(r'^field y = if (.+) then (\d+) else (\d+) fi$', s)
        if m:
            c = m.group(1)
            c = {'x == 0': 'x % P == 0', 'x != 0': 'x % P != 0'}.get(c, c).replace('&&', 'and')
            out.append(ind + 'y = %s if (%s) else %s' % (m.group(2), c, m.group(3))); continue
        m = re.match(r'^field\[STR_LENGTH\] (\w+) = \[0; ?STR_LENGTH\]$', s)
        if m: out.append(ind + '%s = %s([0]*STR_LENGTH)' % (m.group(1), 'G' if guard else '')); continue
        m = re.match(r'^field(?:\[STR_LENGTH\])? (\w+) = (.+)$', s)
        if m: out.append(ind + '%s = %s' % m.groups()); continue
        if s == 'assert(ls[i] * r[i] == 0)': out.append(ind + '_chk("proc", (ls[i] * r[i]) % P == 0)'); continue
        if s == 'assert(accum == 0)': out.append(ind + '_chk("accum", accum % P == 0)'); continue
        m = re.match(r'^assert\((procCheck\(\w+, \w+\))\)$', s)
        if m: out.append(ind + m.group(1)); continue
        if s in ('return true', 'return false'): out.append(ind + s.replace('true', 'True').replace('false', 'False')); continue
        if re.match(r'^return \w+$', s) or re.match(r'^[\w\[\]\- ]+ = .+$', s):
            assert '==' not in s and 'assert' not in s and '&&' not in s, s
            out.append(ind + s); continue
        raise ValueError('untranslated: ' + s)
    return '\n'.join(out) + '\n'
_cache = {}
def load(name, L, guard=False):
    k = (name, L, guard)
    if k not in _cache:
        src = open(os.path.join(ZDIR, name.replace('/', '__') + '.zok')).read()
        _cache[k] = compile(translate(src, L, guard), name, 'exec')
    return _cache[k]
def run(name, buf, guard=False):
    """Return (accepted, fails) for padded bytes buf; len(buf) is STR_LENGTH."""
    L = len(buf); fails = set()
    def _chk(tag, ok):
        if not ok: fails.add(tag)
    g = {'P': P, '_chk': _chk, 'G': G}
    exec(load(name, L, guard), g)
    t = (G if guard else list)(buf)
    g['main'](t, t)
    return (not fails), sorted(fails)
