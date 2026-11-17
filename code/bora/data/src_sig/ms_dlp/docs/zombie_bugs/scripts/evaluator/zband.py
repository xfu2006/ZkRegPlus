# Exact Zombie acceptance (the .zok evaluator) for every band candidate, with early exit:
# units ordered by rejection frequency on the 396 fully evaluated e-mails.
import sys, os, json
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from draw import units, eligible, R, W
def init():
    global ORDER
    J = json.load(open(W + '/draw.json')); cnt = {}
    for i, d in J['zrej'].items():
        for nm in d: cnt[nm] = cnt.get(nm, 0) + 1
    ORDER = sorted(units(), key=lambda n: (-cnt.get(n, 0), n))
def one(r):
    import zokeval
    o = open(R + r['path'], 'rb').read(); p = o + b'\n' * (r['arm'] - len(o))
    for nm in ORDER:
        ok, fails = zokeval.run(nm, p)
        if not ok: return r['path'], r['arm'], nm
    return r['path'], r['arm'], None
if __name__ == '__main__':
    rows = [r for r in json.load(open(W + '/cands.json'))['rows'] if eligible(r)]
    with Pool(16, initializer=init) as pool: out = pool.map(one, rows, chunksize=16)
    json.dump(out, open(W + '/zband.json', 'w'))
    from collections import Counter
    print('done', len(out), 'accepted per arm', Counter(a for _, a, x in out if x is None))
    print('first rejecting unit', Counter(x for _, _, x in out).most_common(6))
