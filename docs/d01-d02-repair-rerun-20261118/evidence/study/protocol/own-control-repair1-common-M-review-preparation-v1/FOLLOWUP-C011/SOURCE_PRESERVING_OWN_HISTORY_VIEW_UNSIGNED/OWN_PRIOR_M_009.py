"""Unchanged candidate cell/anchor tests with literal-original pi allowances.
Only ancillary verification, no parameter or endpoint search."""
import sys
from pathlib import Path
sys.path.insert(0,sys.argv[1])
import certificate as c
import refine as r
from intervals import I,F,PI,log,exp
e=c.e
# PT PNT p.8: (1.95+3.9/v+19.5/v^2)*sqrt(x)/v.
# Include +2/x even if source's unshifted convention was intended.
# After multiplying by exp(v/2), the resulting bound decreases.
assert e(F(43)).lt(10**19)
u=F(24)
assert ((F('1.95')+F('3.9')/u+F('19.5')/u**2)/u+2*e(-u/2)).lt(u/(8*PI))
original=c.fRH
def frh(v):
    assert 24<=v<=58
    return original(v) if v<43 else original(v)*v
c.fRH=frh
# refine imports CH, whose globals resolve the same certificate module.
from certificate import *
def safe_finite(a,z,*args,**kw):
    # Keep the v=43 replacement cutoff at an explicit cell
    # boundary for BOTH v=L and v=L-1.
    a,z=F(a),F(z)
    ends=[a]+[F(b) for b in (43,44) if a<b<z]+[z]
    for l,h in zip(ends,ends[1:]):
        out=finite(l,h,*args,**kw)
        if out is not None:return out
    return None
def check(name, f):
    print(name, f(), flush=True)
check('T, anchor, Li polynomial',anchors)
check('B0/B1 F0 fallback',fallback)
check('analytic sign join',lambda:safe_finite('36.95','37.2',b0,margin=F(0),step=F('.001')))
for a,z,t,step in [('37.2','39.3','.06','0.03125'),('39.3',42,'0','0.03125'),
                   ('39.5',50,'.05','0.03125'),(40,50,'.25','0.03125'),
                   (41,50,'.6','0.03125'),(42,50,'.84','0.03125'),
                   ('37.2',43,'.005','.001'),('39.4',43,'.05','.01'),
                   ('39.9',43,'.25','.01'),('40.9',43,'.6','.01'),
                   ('41.9',43,'.84','.01')]:
    check(('finite constant',a,z,t,step),lambda:safe_finite(a,z,b0,margin=F(t),step=F(step)))
for b,j,a,z,step in [(b0,0,'42.8',60,'.02'),(b0,0,43,60,F(1,16)),
                     (b0,1,'47.5',48,'.02'),(b0,2,53,120,'0.125'),
                     (b0,3,58,91,'0.125'),(b0,4,64,'71.5','0.125'),
                     (b0,1,48,170,'0.125'),(b1,1,48,180,'0.125')]:
    check(('finite profile',str(b),j,a,z,step),lambda:safe_finite(a,z,b,j=j,step=F(step)))
for b, aa in [(b0,[280,192,223,256,290,325,360,396,432,468,504,540,576,613,649,685,722]),
              (b1,[280,180,190,214,240,266,292,318,345,372,399,426,453,480,507,535,562])]:
    check(('uniform tail',str(b)),lambda:[(v,tail(b,j,v)[0]) for j,v in enumerate(aa)])
for b, aa in [(b0,[190,222,255,289,324,359,395,431,467,503,539,575,612,648,684,721]),
              (b1,[170,188,212,238,264,290,316,343,370,397,424,451,478,506,533,560])]:
    def loss(l,h):
        return h**(j+6)*(pick([CH(l-1),r.rp(b,l-1)])+F('2.07')*pick([CH(l),r.rp(b,l)]))
    check(('refined tail',str(b)),lambda:[(v,(F(v)**(j+6)*(r.rp(b,F(v-1))+F('2.07')*r.rp(b,F(v)))).lt(slack(j,F(v)))) for j,v in enumerate(aa,1)])
    if b==b0:
        j=1
        check('refined F1 join fails on these cells',lambda:[q for q in range(170*8,190*8) if not loss(F(q,8),F(q+1,8)).lt(slack(j,F(q,8),F(q+1,8)))])
for j,z0,z1 in [(1,312,227),(2,347,254),(4,421,309),(8,570,421)]:
    check(('no density',j),lambda:[(z,(F(z)**(j+6)*(g(F(z-1))+F('2.07')*g(F(z)))).lt(slack(j,F(z)))) for z,g in [(z0,no_density),(z1,direct_pi)]])
l=F(170)
for d,a in [(F(0),F('1.04e-12')), (F(1,8),F('.0039'))]:
    assert (l*r.rp(b1,l)*e(d*l)).lt(F('.99')*a)
# PT (6), for v>=2000: compare to .0039 exp(-v/8)/v.
v=F(2000)
assert (log(F('.0039'))-v/8).lt(log(235)+F('1.52')*log(v)-F('.8')*exp(log(v)/2))
assert (F('.4')/exp(log(v)/2)).lt(F(1,8))
# Certify the literal old real-wording counterexample.
from endpoint import primepi
n=38358837682; A,B=632207037,1644673232
v=n+F(1,10)
assert (e(F(1))*v*A/log(v)-B**2).lt(0)
print('Dominance tests with corrected anchor and old real wording counterexample passed')
