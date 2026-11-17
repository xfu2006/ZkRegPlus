# C timing, 2 KB counts, jet1tb comparison.
import re, os, glob, statistics, sys
L='/home/xiang/tmp/same_sample_work/zfix_run/logs'; OUT=sys.argv[1]
def g(t,p,cast=int):
    m=re.search(p,t); return cast(m.group(1)) if m else None
CU=['sit-defn-canada-drivers-license-number__comb07','sit-defn-sweden-national-id','sit-defn-malta-tax-identification-number__comb00','sit-defn-norway-identification-number','sit-defn-thai-population-identification-code','sit-defn-japan-my-number-corporate','sit-defn-france-national-id-card','sit-defn-lithuania-passport-number','sit-defn-australia-drivers-license-number__comb15','sit-defn-sweden-passport-number']
w=open(os.path.join(OUT,'prove_verify_1k.tsv'),'w')
w.write('unit\torig_inst_cons\tfixed_inst_cons\torig_prove_ms_median3\tfixed_prove_ms_median3\tprove_ratio\torig_verify_ms_median3\tfixed_verify_ms_median3\tverify_ratio\torig_prove_reps\tfixed_prove_reps\torig_verify_reps\tfixed_verify_reps\torig_ok\tfixed_ok\n')
pr=[];vr=[]; so=sx=vo=vx=0
for u in CU:
    d={}
    for v in ('orig','fixed'):
        P=[];V=[];ok=[];inst=None
        for r in (1,2,3):
            f=f'{L}/C/{v}.{u}.rep{r}.log'
            if not os.path.exists(f): continue
            t=open(f,errors='replace').read(); P.append(g(t,r'prove takes (\d+)')); V.append(g(t,r'verify takes (\d+)')); ok.append(g(t,r'verify result (\w+)',str)); inst=g(t,r'circuit constraints cons (\d+)')
        d[v]=(P,V,ok,inst)
    (oP,oV,ook,oi),(xP,xV,xok,xi)=d['orig'],d['fixed']
    if None in oP+xP or not oP or not xP: w.write(u+'\tincomplete\n'); continue
    mo,mx=statistics.median(oP),statistics.median(xP); vo_,vx_=statistics.median(oV),statistics.median(xV)
    pr.append(mx/mo); vr.append(vx_/vo_); so+=mo; sx+=mx; vo+=vo_; vx+=vx_
    w.write('\t'.join(map(str,[u,oi,xi,mo,mx,'%.3f'%(mx/mo),vo_,vx_,'%.3f'%(vx_/vo_),oP,xP,oV,xV,ook,xok]))+'\n')
w.close()
if pr: print(f'C: n={len(pr)} prove total orig {so} ms fixed {sx} ms ratio {sx/so:.3f}; per-unit prove ratio median {statistics.median(pr):.3f} mean {statistics.mean(pr):.3f} min {min(pr):.3f} max {max(pr):.3f}; verify total orig {vo} fixed {vx} ratio {vx/vo:.3f}, per-unit median {statistics.median(vr):.3f}')
# 2 KB
w=open(os.path.join(OUT,'constraints_2k.tsv'),'w'); w.write('unit\torig_cons_after_reduce\tfixed_cons_after_reduce\tratio\torig_num_vars\tfixed_num_vars\tvars_ratio\torig_inst\tfixed_inst\tjet1tb_inst_2k\torig_prove_ms\tfixed_prove_ms\torig_rc\tfixed_rc\n')
j2={l.split('\t')[0]:l.split('\t')[1] for l in open(os.path.join(OUT,'jet1tb_2k.tsv'))}
rc={}
if os.path.exists(f'{L}/k2/rc.txt'):
    for l in open(f'{L}/k2/rc.txt'):
        p=l.split()
        if len(p)==4: rc[(p[1],p[2])]=p[3]
for u in open('/home/xiang/tmp/same_sample_work/zfix_run/units_2k.txt').read().split():
    m={}
    for v in ('orig','fixed'):
        f=f'{L}/k2/{v}.{u}.log'; t=open(f,errors='replace').read() if os.path.exists(f) else ''
        m[v]=(g(t,r'after reduce linearity (\d+)'),g(t,r'Num Variables (\d+)'),g(t,r'circuit constraints cons (\d+)'),g(t,r'prove takes (\d+)'))
    o,x=m['orig'],m['fixed']; rr=lambda a,b:'%.4f'%(b/a) if a and b else ''
    w.write('\t'.join(map(str,[u,o[0],x[0],rr(o[0],x[0]),o[1],x[1],rr(o[1],x[1]),o[2],x[2],j2.get(u),o[3],x[3],rc.get(('orig',u)),rc.get(('fixed',u))]))+'\n')
w.close()
# jet1tb comparison at 1 KB: orig Spartan inst cons vs jet1tb r1cs_cons
j1={l.split('\t')[0]:l.split('\t')[1:] for l in open(os.path.join(OUT,'jet1tb_1k.tsv'))}
eq=ne=0; nes=[]
for l in open(os.path.join(OUT,'constraints_1k.tsv')).read().splitlines()[1:]:
    p=l.split('\t'); u,oi,xi=p[0],p[7],p[8]
    if oi=='None': continue
    if oi==j1[u][0]: eq+=1
    else: ne+=1; nes.append((u,oi,j1[u][0]))
print(f'jet1tb 1 KB: orig Spartan instance cons equal to jet1tb r1cs_cons for {eq} units, different for {ne}: {nes[:10]}')
fx=[(u,p) for u,p in []]
