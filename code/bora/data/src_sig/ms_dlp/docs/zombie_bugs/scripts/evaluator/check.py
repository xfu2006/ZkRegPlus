# Stage 1+2: candidate pool per size band, then per-candidate checks.
# Output: ~/tmp/same_sample_work/cands.tsv
import sys, os, re, json
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
R = '/home/xiang/Desktop/NewResearch/Projects/ZkregPlusAll/ZkregPlus/code/bora/'
W = os.path.expanduser('~/tmp/same_sample_work')
BANDS = {1000: (900, 1000), 2000: (1900, 2000), 4000: (3800, 4000)}
PREFIX = 'data/samples/email/src/maildir/'
def lines(p): return [l.strip() for l in open(p) if l.strip()]
def build_pool():
    pc = lines(R + 'data/src_sig/ms_dlp/docs/enron_list/pass_clean_enron_list.txt')
    passed = set(lines(W + '/lists/passed_clean_email.txt'))
    final = set(lines(W + '/lists/final_enron_list.txt'))
    st = dict(pass_clean_lines=len(pc))
    pc = [p for p in pc if p.startswith(PREFIX)]; st['pass_clean_raw_email'] = len(pc)
    pc = [p for p in pc if p in passed]; st['and_passed_1113'] = len(pc)
    pc = [p for p in pc if p in final]; st['and_final_list'] = len(pc)
    cands = []
    for p in pc:
        n = os.path.getsize(R + p)
        for arm, (lo, hi) in BANDS.items():
            if lo <= n <= hi: cands.append((p, n, arm))
    return st, cands
# --- per-worker state
def init():
    global ZU, ZRX, BRX, sim2, Z3
    import re2
    from rules import zombie_units, bora_rules, rz
    o = re2.Options(); o.case_sensitive = False; o.dot_nl = True
    o.max_mem = 1 << 28; o.log_errors = False; o.encoding = re2.Options.Encoding.LATIN1
    ZU = zombie_units()
    ZRX = []
    for nm, full, pat, kws, prox in ZU:
        a = rz.assemble_parts(pat, kws, prox); assert a == full, nm
        ZRX.append((nm, re2.compile(a.encode(), o)))
    b, _ = bora_rules()
    BRX = [(n, re2.compile(p.encode(), o)) for n, p in b]
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../pad_r1/sim2.py')).read()
    sim2 = {}; exec(src.split("if sys.argv[1]=='adv'")[0], sim2)   # the existing model, unchanged
    import sim3; Z3 = sim3
def gt(buf):
    z = [nm for nm, rx in ZRX if rx.search(buf)]
    b = [nm for nm, rx in BRX if rx.search(buf)]
    return z, b
def work(c):
    p, n, arm = c
    buf = open(R + p, 'rb').read(); assert len(buf) == n
    pad = buf + b'\n' * (arm - n)
    r = dict(path=p, n=n, arm=arm, sep=buf.find(b'\r\n\r\n') >= 0)
    for tag, x in (('orig', buf), ('pad', pad), ('wrap', b' ' + buf + b' ')):
        z, b = gt(x); r['gtz_' + tag] = z; r['gtb_' + tag] = b
    # sim2 as given: reject if pattern or keyword in body, or its proximity predicate
    rj2 = [u[0] for u in sim2['units'] if any(sim2['zomb'](pad, u, arm, u[5]))]
    r['sim2_rej'] = rj2
    r['sim3_rej'] = Z3.rejects(pad)
    return r
if __name__ == '__main__':
    st, cands = build_pool()
    from collections import Counter
    st['band_cands'] = dict(Counter(a for _, _, a in cands))
    print(json.dumps(st))
    with Pool(12, initializer=init, maxtasksperchild=40) as pool:
        res = pool.map(work, cands, chunksize=1)
    json.dump(dict(stats=st, rows=res), open(W + '/cands.json', 'w'))
    print('done', len(res))
