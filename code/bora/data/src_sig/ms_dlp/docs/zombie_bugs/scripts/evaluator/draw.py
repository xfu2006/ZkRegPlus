# Stage 3: draw 32 per arm, write fixture, run the .zok evaluator on drawn + validation set.
import sys, os, json, random, hashlib
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
R = '/home/xiang/Desktop/NewResearch/Projects/ZkregPlusAll/ZkregPlus/code/bora/'
W = os.path.expanduser('~/tmp/same_sample_work')
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FX = D + '/fixture'
SEED = 20261116; VSEED = 7; NV = 100
def eligible(r):
    return r['sep'] and not any(r[k] for k in r if k.startswith('gt'))
def units():
    from rules import zombie_units
    return [u[0] for u in zombie_units()]
def zjob(a):
    import zokeval
    key, buf, nm, guard = a
    ok, fails = zokeval.run(nm, buf, guard)
    return key, nm, ok, fails
if __name__ == '__main__':
    J = json.load(open(W + '/cands.json')); rows = J['rows']
    by = {a: sorted([r for r in rows if r['arm'] == a and eligible(r)], key=lambda r: r['path']) for a in (1000, 2000, 4000)}
    rng = random.Random(SEED); drawn = []
    for a in (1000, 2000, 4000):
        for k, r in enumerate(rng.sample(by[a], 32)): drawn.append(('%d_%02d' % (a, k + 1), r))
    vr = random.Random(VSEED); dp = {r['path'] for _, r in drawn}; val = []
    for a in (1000, 2000, 4000):
        rest = [r for r in by[a] if r['path'] not in dp]
        for k, r in enumerate(vr.sample(rest, min(NV, len(rest)))): val.append(('v%d_%03d' % (a, k), r))
    os.makedirs(FX + '/emails/orig', exist_ok=True); os.makedirs(FX + '/emails/padded', exist_ok=True)
    tsv = ['id\tsource_path\torig_bytes\tarm\tsha256_orig\tsha256_padded']; bufs = {}
    for i, r in drawn:
        o = open(R + r['path'], 'rb').read(); p = o + b'\n' * (r['arm'] - len(o))
        assert len(o) == r['n'] and len(p) == r['arm'] and p[:len(o)] == o and set(p[len(o):]) <= {10}
        open(FX + '/emails/orig/%s.eml' % i, 'wb').write(o); open(FX + '/emails/padded/%s.eml' % i, 'wb').write(p)
        tsv.append('\t'.join([i, r['path'], str(len(o)), str(r['arm']), hashlib.sha256(o).hexdigest(), hashlib.sha256(p).hexdigest()]))
        bufs[i] = p
    open(FX + '/ids.tsv', 'w').write('\n'.join(tsv) + '\n')
    for i, r in val:
        o = open(R + r['path'], 'rb').read(); bufs[i] = o + b'\n' * (r['arm'] - len(o))
    U = units(); firsts = {'1000_01', '2000_01', '4000_01'}
    jobs = [(i, bufs[i], nm, i in firsts) for i, _ in drawn + val for nm in U]
    with Pool(16) as pool: out = pool.map(zjob, jobs, chunksize=4)
    zrej = {}
    for key, nm, ok, fails in out:
        if not ok: zrej.setdefault(key, {})[nm] = fails
    meta = {i: r for i, r in drawn + val}
    json.dump(dict(seed=SEED, vseed=VSEED, drawn=[i for i, _ in drawn], val=[i for i, _ in val],
                   meta=meta, zrej=zrej, eligible={a: len(v) for a, v in by.items()}), open(W + '/draw.json', 'w'))
    print('done', len(jobs))
