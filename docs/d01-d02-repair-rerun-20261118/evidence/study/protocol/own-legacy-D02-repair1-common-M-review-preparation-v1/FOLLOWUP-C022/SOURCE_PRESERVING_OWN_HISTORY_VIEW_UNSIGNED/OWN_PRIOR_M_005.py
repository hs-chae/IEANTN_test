"""Same locked parameters/tests, with the FKS conditional panel disabled; no optimization."""
import sys
from fractions import Fraction as F
import d02screen as ds
import d02ram as r
import d02m as m
I,e,b,a=ds.I,ds.e,ds.b,ds.a
T=F("167.656")
def report(label,v,target,lower=False):
    z=I(target)
    print(label,v,(">" if lower else "<"),target,v>z if lower else v<z,flush=True)
ds.prelim()
for L in (155,168,175,180,200,535):
    v=ds.screen(F(L),c=F(7,20))
    print("C at",L,v,flush=True)
    if L==168:report("CH2 handoff, psi at 168",e(-a*I(L))*v,ds.A0)
    if L==200:report("D02.md C200",v,".213")
for L,C,g,target in [(168,'.249','.499','.000999'),(180,'.232384','.465','.00023'),(200,'.212654','.426','.00069')]:
    t=I(L); v=ds.screen(F(L),c=F(7,20))+3*e(-(F(1,2)-a)*t)
    report(f"theta cap at {L}",v,C)
    report(f"interval allowance with actual checked screen at {L}",I(g)-v*(2+b*I(g)*e(-a*t)),target,True)
for l,al,q,c in [('59.5',0,2,'5.30e-8'),('60.98',0,2,'2.944e-8'),('59.5',0,3,'4.935e-6'),('59.5',0,4,'.0008274'),('59.5',0,5,'.13872'),('59.5',0,6,'23.257'),('59.5',F(1,8),0,'.001323'),('59.5',F(9,64),0,'.018165'),('59.5',a,0,'.249412')]:
    report(f'M convex bridge: {l} {al} {q}',ds.maxI(m.convexbridge(F(l),T,al,q),m.combined(T)*I(T)**q*e((al-a)*I(T))),c)
for L,c in [(168,'.248838'),(170,'.245767'),(175,'.238698'),(180,'.232384'),(190,'.221577'),(200,'.212654'),(225,'.195899'),(250,'.184171'),(300,'.168790'),(400,'.152502'),(600,'.138777'),(1000,'.129304'),(175,'.239')]:
    report(f'M power {L}',m.combined(F(L)),c)
for L,c in [(168,'.261492'),(175,'.249146'),(180,'.241556'),(200,'.218341'),(250,'.186256')]:
    report(f'M Dusart only {L}',m.spec(F(L),dusart_only=True),c)
try:
    m.elementary_comparison()
except AssertionError:
    print('comparison function stopped on tighter failed assertion; test primorial separately')
def jr(y):
    x=I(y); J,J2=m.smooth(y)
    return ((1+1/x)*J+2*(1/x+2/x**2)*J2+I('2.000000294')*e(-(F(1,2)-a)*x)+I('2.67')*e(-(F(2,3)-a)*x)+x*e(-b*x))
def flat(y):
    return 2*e(a*I(y))*(ds.A0+117*e(-I(y)/2))**2
report('primorial theta cap after T',ds.screen(T,c=F(7,20))+3*e(-(F(1,2)-a)*I(T)),'.25')
z=ds.maxI(ds.maxI(flat(155),flat(T))+jr(155), I('.125')*e(-a*I(T))+jr(T))
report('primorial converted magnitude',z/(1-z*e(-155*a)/155),'6e-13')
for L,K in [(172,83),('169.2',90),(173,110),(178,130),(183,140),('185.5',145)]:
    report(f'R tail {L} K={K}',r.strengthened_tail(F(L),6,17,K),0,True)
for L,c in [(175,'.24'),(180,'.24'),(535,'.144')]:
    report(f'R scaled count at {L}',r.spi(F(L))*e(a*I(L)),c)
report('shifted single-check reserve',r.reserve(F(172),6,shifted=68),1,True)
for l,u,st,k in [(49,'49.5','.025',65),('49.5',58,'.025',83),(58,154,'.25',83),(154,167,'.025',83),(167,172,'.02',83)]:
    report(f'R cover [{l},{u}]',r.cover(l,u,st,6)[0],k,True)
for l,u,st in [(58,154,'.25'),(154,167,'.025'),(167,172,'.02')]:
    report(f'R shift [{l},{u}]',r.cover(l,u,st,6,shifted=68)[0],1,True)
from pathlib import Path
for row in Path('d02ram_results.txt').read_text().splitlines():
    if 'fraction of next coefficient left:' not in row: continue
    k,N,aa,bb=map(int,row.split()[:4]);n=k+4
    report(f'R k={k} D02 onset {aa}',r.strengthened_tail(F(aa),n,N),0,True)
    report(f'R k={k} B0 onset {bb}',r.strengthened_tail(F(bb),n,N,B=F(7,8)),0,True)
    report(f'R k={k} B0 predecessor {bb-1}',r.strengthened_tail(F(bb-1),n,N,B=F(7,8)),0)
    report(f'R k={k} B0 with compact alternatives at D02 onset {aa}',r.polyr(aa,n,N)-r.loss(aa,aa,n,N,F(7,8))-r.qerr(aa,aa,n,N),0)
print("Done.")
