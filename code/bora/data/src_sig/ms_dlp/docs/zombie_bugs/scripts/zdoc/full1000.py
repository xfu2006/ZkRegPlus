# zdoc: evaluator over 32 drawn 1 KB e-mails x 194 units x 3 variants; count rejections and fail tags
import sys, os, collections
from multiprocessing import Pool
S = sys.argv[1]; sys.path.insert(0, S + '/same_sample/scripts'); import zokeval as Z
W = os.path.expanduser('~/tmp/same_sample_work')
U = sorted(f[:-4] for f in os.listdir(W + '/zok'))
E = sorted(f[:-4] for f in os.listdir(S + '/same_sample/fixture/emails/padded') if f.startswith('1000_'))
def job(a):
    v, u, e = a
    if Z.ZDIR != W + '/' + v: Z.ZDIR = W + '/' + v; Z._cache.clear()  # cache key lacks ZDIR
    ok, fails = Z.run(u.replace('__', '/'), open(S + '/same_sample/fixture/emails/padded/%s.eml' % e, 'rb').read())
    return v, u, e, ok, tuple(fails)
if __name__ == '__main__':
    with Pool(4) as p: res = p.map(job, [(v, u, e) for v in ('zok', 'zok_fix1', 'zok_fix12') for u in U for e in E], chunksize=8)
    for v in ('zok', 'zok_fix1', 'zok_fix12'):
        r = [x for x in res if x[0] == v and not x[3]]
        print(v, 'emails', len(E), 'units', len(U), 'rejections', len(r), 'fail tags', collections.Counter(x[4] for x in r), 'emails hit', len(set(x[2] for x in r)))
