"""Directed endpoint certificates for spectral_repair.md."""
from verify import I,D,pi,c,dense,H
E=lambda t:I(t).exp()
def lt(x,y):
    assert I(x).b<I(y).a,(x,y)
def R(t):
    return I('.137')*t.log()+I('.443')*t.log().log()+I('1.588')
def z2(y):
    y=I(y); v=y.log()
    return ((y/(2*pi)).log()+1)/(2*pi*y)+(2*R(y)+(I('.137')+I('.443')/v)/2)/y**2
lt(2*(I('.5922435112')/14+z2(100)),'.1')
lt(2*z2(H),'4e-12')
print('ordinates: all',2*(I('.5922435112')/14+z2(100)),'high',2*z2(H))
def J(t):
    return I('.1')*E(-I(t)/2)+I('4e-12')*E(-I(t)/8)+2*E(-I(t))
def jscaled(a,b):
    return (1+I(1)/a)*(I('.1')+I('4e-12')*E(3*I(b)/8)+2*E(-I(a)/2))
def vb(L):
    # scale out exp(-L/2)
    return 1+7*E(-I(L)/4)+3*(c+114*E(-I('14.5')))+I('3.8')*E(-I(L)/6)
lt(E(29),10**13)
lt(I('1.415')+I('1.000000147')+I('1.78')*E(-I(7)/6),3)
lt(1+I('.791')*E(-I(7)/3),'1.08')
lt(1+c+117*E(-I('14.5')),'1.08')
lt(2*I('1.08')+3*I('1.08')/2/(1-E(-I(14)/3)),'3.8')
eta=I('1.0001')
rows=[(14,17,'2.61'),(17,29,'2.25'),(29,58,'1.25')]
for a,b,m in rows:
    f=I(m)
    print('band',a,b,'reserve',vb(a)+jscaled(a,b))
    if b<=29:
        lt(vb(a)+jscaled(a,b)+I('.791'),f)
        lt(I('1.415')+jscaled(a,b),f)
    else:
        lt(vb(a)+jscaled(a,b),f)
        f+=I(a)**2/(8*pi)
    lt(E(f*E(-I(a)/2)/a),I('1.0002') if a==14 else eta)
split=I('189.24')
lt(I('113.67')+vb(58)+(1+I(1)/58)*(I('.1')+2*E(-29)),115)
lt((1+I(1)/58)*I('4e-12'),'4.1e-12')
def end_scaled(a):
    f=1+I(1)/a
    return dense(I(a),True)+(vb(a)+I('.1')*f)*E(-3*I(a)/8)+I('4e-12')*f+2*f*E(-7*I(a)/8)
lim=end_scaled(split)
lt(E(lim*E(-I(split)/8)/split),eta)
Wc=c+115*E(-I(58)/2)+I('4.1e-12')*E(-I(58)/8)
lt(E(Wc/58),eta)
def mid_scaled(a):
    return c*E(I(a)/8)+115*E(-3*I(58)/8)+I('4.1e-12')
def polynomial_after(a,k):
    lt(eta*I('2.25')*I(a)**2*E(-I(a)/2),k)
    lt(eta*(I(29)**4/(8*pi)+I('1.25')*29**2)*E(-I(29)/2),k)
    lt(eta*(c*split**2+115*58**2*E(-29)+I('4.1e-12')*58**2*E(-I(58)/8)),k)
    lt(eta*lim*split**2*E(-I(split)/8),k)
polynomial_after(17,'.133')
polynomial_after('17.3','.120')
polynomial_after(18,'.091')
lt(E('17.3'),66000000)
powers=(I('1.0002')*I('2.61')*E(-3*I(14)/8),eta*I('2.25')*E(-3*I(17)/8),
      eta*(I(29)**2/(8*pi)+I('1.25'))*E(-3*I(29)/8),eta*mid_scaled(split),lim*E(lim*E(-split/8)/split))
for v in powers: lt(v,'.019675')
print('power band bounds',powers)
for L,K in [(200,'.018857'),(300,'.015169'),(500,'.013103'),(1000,'.011821'),(3000,'.010979'),(30000,'.010514'),(1000000,'.010453')]:
    u=end_scaled(L)
    lt(u*E(u*E(-I(L)/8)/L),K)
    print('power',L,K,u*E(u*E(-I(L)/8)/L))
def bridge_power(a,b,coeff,K):
    assert I(a).b<=I(b).a and I(b).b<=16
    lt(I(coeff)*E(I(a)/8)/I(a)**2,K)

bridge_power(I(100000).log(),14,'.597','.019675')
bridge_power(I(500000).log(),14,'.372','.019675')
polynomial_after('17.16','.12722')
lt(E('17.16'),66000000)
for file,goal in [('smallprod.log','.120'),('weighted.log','.12722')]:
    from pathlib import Path
    (row,)=tuple(line for line in Path(file).read_text().splitlines()
                 if line.split()[:4]==['extended','scaled','upper','10000000']
                 or line.split()[:4]==['weighted','scaled','upper','10000000'])
    for v in row.split()[4:]: lt(v,goal)
# Scope audit: lower prime-power tail dwarfs the original symmetric psi tail.
L=17
oldJ=I('.2')*E(-I(L)/2)+I('2e-11')*E(-I(L)/8)+2*E(-I(L))
lt(2*oldJ,I('1.9998')*E(-I(L)/2))
# Density-free redundancy: remainder from the FKS truncation after scaling.
lt(I('.0142')+I('2.091')/200*E(-25),I(1)/64)

# Unique comparison with the original polynomial branches after their onsets.
def newpower(L): return I('.019675')*I(L)**2*E(-I(L)/8)
for y,q,lo,hi in [(2278382,'.2',40,41),(2278383,'.2',40,41),(912560,'.3',35,36)]:
    z=I(y).log()
    lt(z,16); lt(q,newpower(z)); lt(q,newpower(lo)); lt(newpower(hi),q)
print('new power crossovers: (40,41) at .2; (35,36) at .3')

# No FKS Cor.2.9: retain strong polynomial bounds via a later switch.
y=I(230)
lt(eta*(c*y**2+115*58**2*E(-29)+I('4.1e-12')*58**2*E(-I(58)/8)),'.091')
nd=I('.0142')*y**2*E(-y/8)+I('2.091')*y*E(-y/4)+(1+1/y)*J(y)+vb(y)*E(-y/2)
lt(E(nd/y),eta)
lt(eta*y**2*nd,'.091')
print('polynomial tail without FKS Corollary 2.9')
