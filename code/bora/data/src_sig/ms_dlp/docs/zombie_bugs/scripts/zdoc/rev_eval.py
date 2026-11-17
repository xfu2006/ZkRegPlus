# review: evaluator vs real-prover agreement over summary.tsv + 40G Czech logs
import sys, os, re, glob
from multiprocessing import Pool
S = sys.argv[1]; sys.path.insert(0, S + '/same_sample/scripts')
DIRS = {'old': 'zok', 'fix1': 'zok_fix1', 'fix12': 'zok_fix12'}
E = S + '/same_sample/fixture/emails/padded'
def path(e): return S + '/zreal/viol2/nz_near.eml' if e == 'nz_near' else '%s/%s.eml' % (E, e)
def job(a):
    v, u, e = a
    import zokeval as Z
    Z.ZDIR = os.path.expanduser('~/tmp/same_sample_work/' + DIRS[v]); Z._cache.clear()
    ok, f = Z.run(u, open(path(e), 'rb').read())
    return v, u, e, ok, f
rows = []
for l in open(S + '/zdoc/runs/summary.tsv'):
    p = l.rstrip('\n').split('\t')
    if len(p) < 6: continue
    rows.append((p[0], p[1], p[2], p[5].split('=')[1]))
for f in glob.glob(S + '/zdoc/runs/old_czech_*_40G.log'):
    e = re.search(r'old_czech_(\d+_\d+)_40G', f).group(1)
    r = re.findall(r'verify result (\w+)', open(f, errors='replace').read())
    rows.append(('old', 'sit-defn-czech-drivers-license-number', e, r[0] if r else 'NONE'))
with Pool(4) as p: res = p.map(job, [(v, u, e) for v, u, e, _ in rows])
agree = dis = none = 0
for (v, u, e, real), (_, _, _, ok, f) in zip(rows, res):
    if real == 'NONE': none += 1; print('NO-REAL', v, u, e, 'eval', ok, f); continue
    if (real == 'true') == ok: agree += 1
    else: dis += 1; print('DISAGREE', v, u, e, real, ok, f)
    if not ok: print('reject', v, u, e, real, f)
print('agree', agree, 'disagree', dis, 'no real result', none)
