
from certify import F, H, ex, j0, j1, fac
from functools import lru_cache
@lru_cache(maxsize=50000)
def en(x):
    x=F(x)
    if x<=100:return ex(x)
    a,b=en(x/2)
    return a*a,b*b
def E(x):return en(x)[1]
def EL(x):return en(x)[0]
C1=list(map(F,'7.798 8.162 8.538 8.928 9.331 9.747 10.177 10.621 11.077'.split()))
C2=list(map(F,'4.101 3.693 3.613 3.533 3.453 3.373 3.293 3.213 3.133'.split()))
ROWS=list(zip([F('.75')]+[F(i,100) for i in range(80,88)],C1,C2))
def coeff(s,c1,c2):
    d=1-F(8,3)*(1-s); r=5-2*s
    return 2*(c1*E(d*j0)*j1**4*E((4-r)*F('3.3579'))/(d-r/j0)
              +c2/H*j1*j1/(1-2/j0))
def sharpcoeff(s,c1,c2):
    d=1-F(8,3)*(1-s);r=5-2*s
    term=F(1);a=term
    for k in range(4):
        term*= (r-k)/(d*j0);a+=term
    return 2*(c1*E(d*j0)*j1**4*E((4-r)*F('3.3579'))/d*a
              +c2/H*(j1*j1+2*j1+2))

assert EL(F("1.098613"))*3<1
def rcoeff(s):
    return F('4.9')/EL(F(8,3)*(1-s)*F("1.098613"))
@lru_cache(None)
def discrete(cap,s=F('.75'),step=F(1,1000)):
    seg=[s];p=s
    while p<cap:
        p=min(cap,p+step);seg.append(p)
    assert len(seg)>1
    dd=(cap-seg[-2])/4
    seg=seg[:-1]+[cap-dd/4**n for n in range(7)]+[cap]
    b=[]
    for k,a in enumerate(seg[:-1]):
        i=max(i for i,(t,y,z) in enumerate(ROWS) if t<=a)
        y,z=ROWS[i][1:]
        b.append(ceil(min(sharpcoeff(a,y,z),sharpcoeff(a,rcoeff(a),F("51.5"))),10**10))
        if k:b[k]=min(b[k-1],b[k])
    b.append(F(0))
    return ((F('.036'),2,1-s,0),(F('2.091'),1,KT,0))+tuple(
        (b[i]-b[i+1],0,1-c,0) for i,c in enumerate(seg[1:]) if b[i]>b[i+1])
def slope(s):
    d=1-F(8,3)*(1-s);r=5-2*s
    return F(8,3)*j1+2*F('3.36')+(F(8,3)+2/j0)/(d-r/j0)
def ceil(x,N):return F((N*x).__ceil__(),N)
def row(s,b):
    a1=max(y for t,y,z in ROWS if t<=b)
    a2=max(z for t,y,z in ROWS if t>=s or (t==F('.75') if s<F('.80') else t==F((100*s).__floor__(),100)))
    return ceil(coeff(b,a1,a2),10**8),ceil(slope(s),100)
B0=F(7,8); B2=F(27,32)
KT=F('.47')
def choices(cap):
    for s in map(F,['.75','.80','.81','.82','.83','.84']):
        if not s<cap:continue
        yield (s,cap)
        mids=tuple(t for t,c1,c2 in ROWS if s<t<cap)
        if mids:yield (s,*mids,cap)
    for s in map(F,['.75','.80']):
        for t in map(F,['.80','.81','.82','.83','.84','.85','.86','.87']):
            if s<t<cap:yield (s,t,cap)
@lru_cache(None)
def terms(cuts,k=KT):
    s=cuts[0]
    assert k<=KT
    return ((F('.036'),2,1-s,0),(F('2.091'),1,k,0))+tuple(
        (b,0,1-r,M) for l,r in zip(cuts,cuts[1:]) for b,M in [row(l,r)])
P=((F('1.000001'),0,F(1,2),0),(F('1.78'),0,F(2,3),0))
CH=((F('1.048e-12'),0,0,0),(F('113.67'),0,F(1,2),0))
def val(u,Q):
    return sum(b*u**m*E(c*u)*(u/(u-M) if M else 1) for b,m,c,M in Q)
def perron_valid(u,k=KT):
    assert u>=40 and k*u>=1 and EL(k*u)*max(51,u)<1
    assert 5*E((F(1,2)-k)*u)+2*E(u/2)<1
perron_valid(F(100))
assert KT**2/F('6.25')+F('1.8642')/100**2 < F('.036')
assert F(8,3)*j1+2*F('3.36') > 80
def opts(cap):
    for cs in choices(cap):
        T=terms(cs)
        j=ceil(max(M for b,m,c,M in T)+2,1)
        yield j,T
def minv(u,cap):
    return min([val(u,CH)]+[val(u,Q) for j,Q in opts(cap) if u>=j and u>=100]
        +([u*u*E(5*u/32)/64] if cap==B2 and u>=200 else []))
if __name__=='__main__':
    for cap in (B0,B2):
        for s in ('0.75','0.80','0.81','0.82','0.83','0.84'):
            print(cap,s,row(F(s),cap))
        for u in (100,130,150,160,170,180,190,200,250,400):
            a=minv(F(u),cap)
            print(cap,u,'psi',float(a),'scaled',float(a/EL((1-cap)*u)))
