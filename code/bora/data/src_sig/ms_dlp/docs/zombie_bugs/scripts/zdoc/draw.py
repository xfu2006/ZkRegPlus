# zdoc: draw 5 units of 194 and 8 of the 32 drawn 1 KB e-mails; seed from argv
import random, os, sys, csv
S = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
units = sorted(f[:-4].replace('__', '/') for f in os.listdir(os.path.expanduser('~/tmp/same_sample_work/zok')))
rows = {r['id']: r for r in csv.DictReader(open(S + '/same_sample/fixture/zombie_check.tsv'), delimiter='\t')}
ids = sorted(i for i in rows if i.startswith('1000_'))
assert len(units) == 194 and len(ids) == 32
seed = int(sys.argv[1]); rng = random.Random(seed)
U = rng.sample(units, 5); E = rng.sample(ids, 8)
print('seed', seed); print('units', ' '.join(U)); print('emails', ' '.join(E))
x = 0
for e in E:
    rej = [u for u in U if u in rows[e]['rejecting_units'].split(',')]
    x += bool(rej); print(e, 'rejecting_among_drawn:', ','.join(rej) or '-')
print('predicted XXX (evaluator, old circuits) =', x, 'of 8')
