"""Ancillary checks of locked constants, root counterexample and source identities."""
import sys, json, hashlib, re, zlib
from pathlib import Path
task=Path('/task')
cand=Path(sys.argv[1] if len(sys.argv)>1 else '/work/reviewcand')
papers=Path('/corpus/originals')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
idx=json.loads((task/'CANDIDATE_INDEX.json').read_text())
for a in idx['candidate_files']:
    assert sha(cand/a['original_name'])==sha(task/a['packet_name'])==a['sha256']
print('Restored candidate and packet: matched',len(idx['candidate_files']),'SHA256 digests')
for row in json.loads((task/'SOURCE_INDEX.json').read_text())['sources']:
    for k in ['pdf','text']:
        assert sha(papers/row[k])==row[k+'_sha256']
        print(row[k],row[k+'_sha256'])
sys.path.insert(0,str(cand))
from verify import I,D,dense
from count import primepi
n=38358837682;m=14111427770
a,b=primepi(n),primepi(m); e=I(1).exp()
x=I('38358837682.1')
assert (a,b)==(1644673232,632207037)
assert (I(n)/e).a>m and (I(n+1)/e).b<m+1
assert (I('36.54').exp()).b<D('1.15e16')
assert (I('39.326').exp()).b<D('1.2e17')
assert n+1==2521*15215723
q=I(10**11)/e
assert int(q.a)==int(q.b)==36787944117
print('Exact real counterexample coordinate, R enclosure:',x,e*x/x.log()*b-a*a)
assert (e*x/x.log()*b-a*a).b<0
assert dense(I(200),True).b<D('.019')
# Fixed mesh conversions in legacy code.
for a,b,k in [(36.98,37.5,100),(37.5,39.32,100),(39.1,39.32,100),
               (39.32,39.5,200),(39.5,40,100),(40,42.8,100),(42.8,43,200),
               (43,60,100),(46,77,25),(47,67,25),(60,163,10),(60,269,10)]:
    assert all(int(D(str(t))*k)==D(str(t))*k for t in (a,b))
    assert k in (10,25,100,200)
# Original PDF content-stream checkpoints (not a general PDF text extractor).
def content(name,page):
    b=(papers/(name+'.pdf')).read_bytes()
    objs={int(i):v for i,v in re.findall(rb'(\d+) 0 obj\s*(.*?)\s*endobj',b,re.S)}
    pages=[(i,v) for i,v in objs.items() if re.search(rb'/Type\s*/Page\b',v)]
    pid,v=pages[page-1]
    cid=int(re.search(rb'/Contents\s*(?:\[\s*)?(\d+) 0 R',v)[1])
    v=objs[cid]
    return pid,cid,zlib.decompress(v.split(b'stream',1)[1].lstrip(b'\r\n'))
for f,p,keywords in [
    ('FKS',7,[b'Theorem',b'Corollary']),('FKS',8,[b'Theorem',b'2.091']),
    ('FKS',26,[b'7.7979',b'0.3089']),('CH2',3,[b'coth',b'113.67']),
    ('CH2',36,[b'9.4']),('PlattTrudgianFiniteRH',4,[b'2.169'])]:
    pid,cid,s=content(f,p)
    glyph=b''.join(re.findall(rb'\(((?:\\.|[^\\()])*)\)',s))
    for kw in keywords:
        hit=glyph.find(kw)
        print(f,p,'page/content object',pid,cid,'stream',hashlib.sha256(s).hexdigest(),
              kw,'glyph context',glyph[max(0,hit-40):hit+65] if hit>=0 else '(not contiguous)')
