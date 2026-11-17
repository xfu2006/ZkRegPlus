# Run the .zok evaluator on every candidate the sim3 model accepts (exact count of Zombie-accepted).
import sys, os, json
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from draw import zjob, units, eligible, R, W
if __name__ == '__main__':
    rows = json.load(open(W + '/cands.json'))['rows']
    acc = [r for r in rows if eligible(r) and not r['sim3_rej']]
    U = units(); jobs = []
    for r in acc:
        o = open(R + r['path'], 'rb').read(); p = o + b'\n' * (r['arm'] - len(o))
        jobs += [(r['path'], p, nm, False) for nm in U]
    with Pool(16) as pool: out = pool.map(zjob, jobs, chunksize=8)
    rej = {}
    for key, nm, ok, fails in out:
        if not ok: rej.setdefault(key, {})[nm] = fails
    json.dump(dict(n=len(acc), arms={r['path']: r['arm'] for r in acc}, rej=rej), open(W + '/val2.json', 'w'))
    print('done', len(acc), 'zok-rejected among sim3-accepted:', len(rej))
