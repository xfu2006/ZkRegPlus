# zdoc: build markdown tables from runs/summary.tsv
import sys, collections
S = sys.argv[1]
rows = [l.rstrip('\n').split('\t') for l in open(S + '/zdoc/runs/summary.tsv') if '\t' in l]
R = {}; C = {}
for v, u, e, kg, rc, vr, cs in rows:
    R[(v, u, e)] = (rc.split('=')[1], vr.split('=')[1]); c = cs.split('=')[1]
    if c: C[(v, u)] = c
U = [l.split()[1:] for l in open(S + '/zdoc/runs/draw_seed1.txt') if l.startswith('units')][0]
E = [l.split()[1:] for l in open(S + '/zdoc/runs/draw_seed1.txt') if l.startswith('emails')][0]
def cell(v, u, e):
    rc, vr = R.get((v, u, e), ('-', 'missing'))
    return vr if rc == '0' else 'rc %s (%s)' % (rc, vr)
print('| unit (constraints old / fixed) | ' + ' | '.join(E) + ' |')
print('|---|' + '---|' * len(E))
fail = collections.Counter()
for u in U:
    for v in ('old', 'fix12'):
        print('| %s, %s (%s) | ' % (u, 'old' if v == 'old' else 'fix 1+2', C.get((v, u), '?')) + ' | '.join(cell(v, u, e) for e in E) + ' |')
for e in E:
    print(e, 'old rejected by', [u for u in U if R.get(('old', u, e), ('', ''))[1] != 'true'], 'fix12 rejected by', [u for u in U if R.get(('fix12', u, e), ('', ''))[1] != 'true'])
for k in sorted(C): print(k, C[k])
