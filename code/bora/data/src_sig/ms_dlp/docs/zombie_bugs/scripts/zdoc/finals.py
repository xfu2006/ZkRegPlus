# zdoc: list positions where final tapes are nonzero, per circuit variant (evaluator)
import sys, os, re
sys.path.insert(0, sys.argv[1]); import zokeval as Z
unit, email = sys.argv[2], sys.argv[3]
buf = open(email, 'rb').read()
for v in ('zok', 'zok_fix1', 'zok_fix12'):
    src = open(os.path.expanduser('~/tmp/same_sample_work/%s/%s.zok' % (v, unit.replace('/', '__')))).read()
    fins = sorted(set(re.findall(r'field\[STR_LENGTH\] (f_\d+) =', src)))
    py = Z.translate(src, len(buf)).replace('\n\treturn False', '\n\t_cap.update({k: v for k, v in locals().items() if k.startswith("f_")})\n\treturn False')
    fails = set(); cap = {}
    g = {'P': Z.P, '_chk': lambda t, ok: ok or fails.add(t), 'G': Z.G, '_cap': cap}
    exec(compile(py, unit, 'exec'), g); g['main'](list(buf), list(buf))
    print('==', v, 'fails:', sorted(fails) or 'none')
    for f in fins:
        pos = [i for i, x in enumerate(cap[f]) if x % Z.P]
        print('  ', f, 'nonzero at', len(pos), 'positions', [(i, buf[max(0, i - 14):i + 1].decode('latin-1')) for i in pos[:4]])
