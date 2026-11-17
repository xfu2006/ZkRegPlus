# Build near/far violation e-mails (1000 bytes, 0x0A pad) for 3 units; check the true regex with Python re on the body.
import re, os, sys, json
Z=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../../..')) + '/regex_zombie_international/'
OUT=sys.argv[1]
H=(b"Message-ID: <100001.1075800000000.JavaMail.evans@thyme>\r\nDate: Mon, 3 Jul 2000 09:00:00 -0700 (PDT)\r\n"
   b"From: a.b@enron.com\r\nTo: c.d@enron.com\r\nSubject: follow up\r\n\r\n")
F=b"ok see you at noon. "
units={'malta':('sit-defn-malta-drivers-license-number',b'AB123456',b' driver license '),
       'ausdl12':('sit-defn-australia-drivers-license-number/comb12',b'1234 567 890',b' Driver Licence '),
       'austria':('sit-defn-austria-passport-number',b'P1234567',b' passport number ')}
def fill(n): return (F*100)[:n]
def put(segs):
    # segs: list of (end_offset_wanted, bytes); filler between
    out=bytearray(H)
    for end,b in segs:
        st=end-len(b); assert st>=len(out), (st,len(out)); out+=fill(st-len(out)); out+=b
    assert len(out)<=1000; return bytes(out)
res={}
for k,(u,idb,kw) in units.items():
    full=open(Z+u+'.regex').read().strip()
    rx=re.compile(full.encode('latin1'), re.S)
    # near: ID ends at byte 430, keyword (final char) ends at byte 520 -> keyword final pos 519 in [300,700], gap ~76 bytes
    near=put([(430,idb),(520,kw)])
    # far: keyword ends at byte 350, ID ends at byte 900 -> distance ~550 bytes > 300
    far=put([(350,kw),(900,idb)])
    for tag,m in (('near',near),('far',far)):
        body=m[m.index(b'\r\n\r\n')+4:]
        hit=rx.search(body); hitall=rx.search(m)
        pad=m+b'\n'*(1000-len(m)); open(os.path.join(OUT,'%s_%s.eml'%(k,tag)),'wb').write(pad)
        res['%s_%s'%(k,tag)]=dict(unit=u,len=len(m),kw_end=m.index(kw)+len(kw), id_end=m.index(idb)+len(idb),
              body_match=bool(hit), body_match_span=(hit.span() if hit else None), match_whole_padded=bool(rx.search(pad)))
print(json.dumps(res,indent=1))
