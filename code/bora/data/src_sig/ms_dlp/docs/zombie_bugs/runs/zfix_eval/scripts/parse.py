# Parse zfix_run logs into per-unit TSVs (constraint counts, verify results) and summary stats.
import re, os, glob, statistics, sys
R='/home/xiang/tmp/same_sample_work/zfix_run/logs'; OUT=sys.argv[1]
def g(t,p,cast=int):
    m=re.search(p,t); return cast(m.group(1)) if m else None
def parse(f):
    t=open(f,errors='replace').read()
    return dict(cons=g(t,r'r1cs cons after reduce linearity (\d+)'), vars=g(t,r'Num Variables (\d+)'),
        pre=g(t,r'r1cs cons before reduce linearity (\d+)'), inst=g(t,r'circuit constraints cons (\d+)'),
        keygen=g(t,r'61427\.3: keygen takes (\d+)'), prove=g(t,r'prove takes (\d+)'), verify_ms=g(t,r'verify takes (\d+)'),
        sat=g(t,r'61427\.1: is_sat (\w+)',str), ok=g(t,r'61427\.4: verify result (\w+)',str),
        rss=g(t,r'Maximum resident set size \(kbytes\): (\d+)'), exit=g(t,r'Exit status: (\d+)'))
units=sorted(os.path.basename(d) for d in glob.glob('/home/xiang/tmp/same_sample_work/zfix_run/fixed/sit-*'))
rows=[]; 
with open(os.path.join(OUT,'constraints_1k.tsv'),'w') as w:
    w.write('unit\torig_cons_after_reduce\tfixed_cons_after_reduce\tcons_ratio_fixed_over_orig\torig_num_vars\tfixed_num_vars\tvars_ratio\torig_spartan_inst_cons\tfixed_spartan_inst_cons\torig_keygen_ms\tfixed_keygen_ms\torig_peak_rss_kB\tfixed_peak_rss_kB\torig_verify_1000_01\tfixed_verify_1000_01\n')
    for u in units:
        o=parse(f'{R}/orig/{u}.1000_01.true.log') if os.path.exists(f'{R}/orig/{u}.1000_01.true.log') else {}
        x=parse(f'{R}/fixed/{u}.1000_01.true.log') if os.path.exists(f'{R}/fixed/{u}.1000_01.true.log') else {}
        rc=lambda a,b: '%.4f'%(b/a) if a and b else ''
        w.write('\t'.join(str(v) for v in [u,o.get('cons'),x.get('cons'),rc(o.get('cons'),x.get('cons')),o.get('vars'),x.get('vars'),rc(o.get('vars'),x.get('vars')),
            o.get('inst'),x.get('inst'),o.get('keygen'),x.get('keygen'),o.get('rss'),x.get('rss'),o.get('ok'),x.get('ok')])+'\n')
        rows.append((u,o,x))
for k in ('cons','vars','inst'):
    good=[(u,o,x) for u,o,x in rows if o.get(k) and x.get(k)]
    so=sum(o[k] for _,o,_ in good); sx=sum(x[k] for _,_,x in good); r=[x[k]/o[k] for _,o,x in good]
    print(f'{k}: n={len(good)} units with both; total orig {so} fixed {sx} total ratio {sx/so:.4f}; mean per-unit orig {so/len(good):.1f} fixed {sx/len(good):.1f}; per-unit ratio mean {statistics.mean(r):.4f} median {statistics.median(r):.4f} min {min(r):.4f} max {max(r):.4f}')
    print(f'{k}: missing orig {[u for u,o,x in rows if not o.get(k)]}')
# D: verify results for fixed on 4 e-mails
with open(os.path.join(OUT,'acceptance_fixed_1k.tsv'),'w') as w:
    w.write('unit\t1000_01\t1000_02\t1000_03\t1000_04\n'); bad=[]; n=0
    for u in units:
        vals=[]
        for i,e in enumerate(['1000_01','1000_02','1000_03','1000_04']):
            f=f'{R}/fixed/{u}.{e}.{"true" if i==0 else "false"}.log'
            v=parse(f)['ok'] if os.path.exists(f) else 'missing'; vals.append(str(v))
            if v=='true': n+=1
            else: bad.append((u,e,v))
        w.write(u+'\t'+'\t'.join(vals)+'\n')
print('D fixed verify true:',n,'of',4*len(units)); print('D non-true not missing:',[b for b in bad if b[2] not in ('missing',None)]); print('D missing/None count:',sum(1 for b in bad if b[2] in ('missing',None)))
ob=[(u,o.get('ok')) for u,o,_ in rows if o.get('ok')!='true']; print('orig on 1000_01 false:',[u for u,v in ob if v=='false']); print('orig on 1000_01 no result:',len([1 for u,v in ob if v is None]))
