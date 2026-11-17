# Rerun of fixsim with one circuit variant per process (zokeval caches compiled circuits by unit name only).
import sys, os, json
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
W = os.path.expanduser('~/tmp/same_sample_work')
TAG = sys.argv[1]; ARMS = [int(a) for a in sys.argv[2].split(',')]
def init():
    import zokeval; zokeval.ZDIR = W + '/' + TAG
def job(a):
    key, buf, nm = a
    import zokeval
    assert zokeval.ZDIR.endswith(TAG)
    return key, nm, zokeval.run(nm, buf, False)[0]
if __name__ == '__main__':
    from draw import units, R
    d = json.load(open(W + '/draw.json')); U = units(); jobs = []
    for i in d['drawn']:
        r = d['meta'][i]
        if r['arm'] not in ARMS: continue
        o = open(R + r['path'], 'rb').read(); p = o + b'\n' * (r['arm'] - len(o))
        jobs += [(i, p, nm) for nm in U]
    with Pool(4, initializer=init) as pool: out = pool.map(job, jobs, chunksize=4)
    rej = {}
    for k, nm, ok in out:
        if not ok: rej.setdefault(k, []).append(nm)
    print(TAG, ARMS, 'e-mails', len({j[0] for j in jobs}), 'pairs', len(jobs), 'rejected e-mails', len(rej), json.dumps(rej)[:500])
