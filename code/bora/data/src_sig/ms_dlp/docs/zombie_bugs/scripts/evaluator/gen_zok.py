# Codegen every Zombie unit's .zok (STR_LENGTH 1000) via run_zombie._codegen_zok (stdout only).
import sys, os
from multiprocessing import Pool
S=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../..'))
sys.path.insert(0, S+'/scripts'); import run_zombie as rz
rz.FULL_DIR = S+'/regex_zombie_international'
rz.TESTREGEX = S+'/zombie/regex/bin/TestRegex'
OUT=os.path.expanduser('~/tmp/same_sample_work/zok')
def one(nm):
    zok, prox, st = rz._codegen_zok(nm, 1000)
    if zok: open(os.path.join(OUT, nm.replace('/','__')+'.zok'),'w').write(zok)
    return nm, prox, st
if __name__=='__main__':
    names = rz.list_policy_names(S+'/regex_zombie_international')
    with Pool(16) as p: res = p.map(one, names)
    from collections import Counter
    print(len(names), Counter(r[2] for r in res), Counter(r[1] for r in res))
    for r in res:
        if r[2]!='ok': print(r)
