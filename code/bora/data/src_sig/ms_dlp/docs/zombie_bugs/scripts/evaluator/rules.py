# Load ground-truth rule sets: Zombie units (combined regex + parts) and BORA PCRE subsigs.
import sys, re
S='/home/xiang/Desktop/NewResearch/Projects/ZkregPlusAll/ZkregPlus/code/bora/data/src_sig/ms_dlp'
sys.path.insert(0, S+'/scripts'); import run_zombie as rz
rz.FULL_DIR = S+'/regex_zombie_international'
def zombie_units():
    out=[]
    for nm in rz.list_policy_names(rz.FULL_DIR):
        full=open(rz.FULL_DIR+'/'+nm+'.regex').read().strip()
        pat,kws,prox=rz.extract_parts(full)
        out.append((nm,full,pat,kws,prox))
    return out
def bora_rules(path=S+'/regex_bora_international/main_full.dat'):
    out=[]; skipped=[]
    for line in open(path):
        f=line.rstrip('\n').split(';')
        for sub in f[3:]:
            m=re.match(r'^/(.*)/([a-z]*)$',sub,re.S)
            if m: out.append((f[0],m.group(1)))
            else: skipped.append((f[0],sub[:40]))
    return out, skipped
