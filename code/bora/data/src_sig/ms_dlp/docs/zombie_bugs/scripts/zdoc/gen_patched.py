# zdoc: regenerate all 194 .zok with a (patched) TestRegex copy; argv: TestRegex path, out dir
import sys, os
from multiprocessing import Pool
D = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../..'))
sys.path.insert(0, D + '/scripts'); import run_zombie as rz
rz.FULL_DIR = D + '/regex_zombie_international'; rz.TESTREGEX = sys.argv[1]; OUT = sys.argv[2]
def one(nm):
    zok, prox, st = rz._codegen_zok(nm, 1000)
    if zok: open(os.path.join(OUT, nm.replace('/', '__') + '.zok'), 'w').write(zok)
    return st
if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    names = rz.list_policy_names(D + '/regex_zombie_international')
    with Pool(4) as p: res = p.map(one, names)
    from collections import Counter; print(len(names), Counter(res))
