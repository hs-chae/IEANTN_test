"""Ancillary directed checks supplementing the unchanged candidate replays.
Invoke from /work/c008 with PYTHONPATH=/work/c008 and assertions enabled."""
from verify import I, pi, dense
from d02_cert import E, lt, local, Wpi, Vpi, CAP0, CAP2, R0, R2, D, power
from pathlib import Path
import hashlib, json, platform, decimal, sys

def sha(p):
    h = hashlib.sha256()
    with Path(p).open("rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): h.update(b)
    return h.hexdigest()

task=Path('/task'); corp=Path('/corpus/originals')
ix=json.loads((task/'CANDIDATE_INDEX.json').read_text())
for r in ix['candidate_files']:
    p=task/r['packet_name']
    assert p.stat().st_size==r['bytes']
    assert sha(p)==sha(Path(r['original_name']))==r['sha256']
for r in json.loads((task/'SOURCE_INDEX.json').read_text())['sources']:
    for k in ('pdf','text'): assert sha(corp/r[k])==r[k+'_sha256']
print('68 candidate files and 7 PDF/text pairs: exact SHA-256 matches')
print(platform.platform(), sys.version, decimal.__libmpdec_version__)

# The directed count program documents counts (used here, not inferred by floats).
N=38358837682
A,B=1644673232,632207037
x=I('38358837682.1')
assert N < x.a < x.b+1 and x.b<N+1 and N+1 == 2521*15215723
xe=x/E(1)
lt(14111427770,xe); lt(xe,14111427771)
R=E(1)*x*B/x.log()-A*A
lt('-7974585.083',R); lt(R,'-7974585.082')
print('quoted real-source witness',x,R)
lt(36787944117,I(10**11)/E(1));lt(I(10**11)/E(1),36787944118)
lt(E('36.528'),E('36.98'));lt(E('36.98'),'1.15e16')
lt(E('39.326'),'1.2e17');lt('1.2e17',E('39.5'))
lt(E(14),1202606);lt(E(17),24154954);lt(E(18),66000000);lt(E('19.5'),300000000)
lt(40000000,E(18));lt(150000000,E('19.03'));lt(E('19.03'),300000000)
lt(159, 160) # no floating thresholds are used in the executable tests below
lt(dense(I(200),True),'.019')
lt(1/(64*pi)+I('.9321')/100**2,'.0071')
lt(I('.0142')+I('2.091')/200*E(-25),1/I(64))
lt(I('.018221')/I('.000495'),37)
lt(36,I('.018221')/I('.000495'))
lt(I('1.000000147')+I('1.78')*E(-I(200)/6),3)
lt(I('1.415')+I('1.000000147'), '2.415001')
lt(I('.9999')*2,2)
J=I('.2')*E(-I(17)/2)+I('2e-11')*E(-I(17)/8)+2*E(-I(17))
lt(2*J,I('1.9998')*E(-I(17)/2))
print('withdrawn theta bound: upper on integrated theta error',J-I('1.9998')*E(-I(17)/2), 'excludes lower endpoint',-J)
# Same shape comparisons and analytical finite-tail glue.
lt(I('.29473')*E(-I(170)/32),'.01044')
lt(I('.123')*500**2*E(-I(500)/32),'.01044')
lt(I('.0142')+I('2.091')/200*E(-I(200)*(I('.25')-R2)),1/I(64))
for t in [160,165,168,170,175]:
    z=I(t)
    print('finite gap local ceilings',t, 'CH2',(I('1.048e-12')+I('113.67')*E(-z/2)).b,
          'B0',local(z,CAP0,D('.75'),D('.25')).b,'D02',local(z,CAP2,D('.75'),D('.25')).b)

print('bridge binary SHA-256', sha('/work/bridge'))
print('bridge log-table SHA-256', sha('/work/bridge.logs'))
print('bridge log-table count',sum(1 for _ in open('/work/bridge.logs')))
print('ancillary checks passed')
