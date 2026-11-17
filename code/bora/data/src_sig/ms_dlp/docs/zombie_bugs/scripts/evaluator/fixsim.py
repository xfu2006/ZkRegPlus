# Evaluate Zombie units with fix 1 (accum skips finals in proximity pairs) and fix 1+2 (single-class tape not complemented).
import sys, os, re, json, glob
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
W = os.path.expanduser('~/tmp/same_sample_work')
def fix(src, f2):
    pf = set(x for m in re.finditer(r'procCheck\(f_(\d+), f_(\d+)\)', src) for x in m.groups())
    src = '\n'.join(l for l in src.split('\n') if not (re.match(r'^\s*accum = accum \+ f_(\d+)\[i\]$', l) and re.match(r'^\s*accum = accum \+ f_(\d+)', l).group(1) in pf))
    if f2: src = re.sub(r'(p_\d+\[i\] = )1 - (t_\d+\[i\])$', r'\1\2', src, flags=re.M)
    return src
def mk():
    for tag, f2 in (('zok_fix1', False), ('zok_fix12', True)):
        os.makedirs(W + '/' + tag, exist_ok=True)
        for p in glob.glob(W + '/zok/*.zok'):
            open(W + '/' + tag + '/' + os.path.basename(p), 'w').write(fix(open(p).read(), f2))
def job(a):
    tag, key, buf, nm = a
    import zokeval
    zokeval.ZDIR = W + '/' + tag
    ok, _ = zokeval.run(nm, buf, False)
    return tag, key, nm, ok
if __name__ == '__main__':
    mk()
    from draw import units, R
    d = json.load(open(W + '/draw.json')); U = units()
    jobs = []
    for i in d['drawn'] + d['val']:
        r = d['meta'][i]; o = open(R + r['path'], 'rb').read(); p = o + b'\n' * (r['arm'] - len(o))
        for tag in ('zok_fix1', 'zok_fix12'):
            jobs += [(tag, i, p, nm) for nm in U]
    with Pool(16) as pool: out = pool.map(job, jobs, chunksize=4)
    rej = {}
    for tag, key, nm, ok in out:
        if not ok: rej.setdefault(tag, {}).setdefault(key, []).append(nm)
    json.dump(rej, open(W + '/fixsim.json', 'w'))
    for tag in ('zok_fix1', 'zok_fix12'):
        for grp, ids in (('drawn', d['drawn']), ('val', d['val'])):
            for a in (1000, 2000, 4000):
                ia = [i for i in ids if d['meta'][i]['arm'] == a]
                nr = sum(1 for i in ia if i in rej.get(tag, {}))
                print(tag, grp, a, 'rejected', nr, 'of', len(ia))
        from collections import Counter
        c = Counter(nm for v in rej.get(tag, {}).values() for nm in v); print(tag, 'top units', c.most_common(6))
