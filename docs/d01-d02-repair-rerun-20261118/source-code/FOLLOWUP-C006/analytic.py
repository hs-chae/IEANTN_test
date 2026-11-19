from certlib import *
from fractions import Fraction as F
from math import comb
def up(s): return I(s)
def ex(x):return cv(x).exp()
H=3*10**12
b='0.000000000001048'
def dval(s,c1,c2):
    h=I(H).log()
    a=1-F(8,3)*(1-s)
    q=5-2*s
    z=(a-q/h)
    return 2*(c1*power(h,q)*ex(-a*h)/z+c2*(h*h+2*h+2)/H)
bands = [
('0.80','8.17','3.70','0.82','6.42'),
('0.82','8.94','3.54','0.84','1.15'),
('0.84','9.75','3.38','0.85','0.209'),
('0.85','10.18','3.30','0.86','0.089'),
('0.86','10.62','3.22','0.87','0.039'),
('0.87','11.08','3.14','0.874','0.0165'),
('0.874','11.08','3.14','0.875','0.012'),
]
HIG = [(F(c),1-F(t)) for s,_,__,t,c in bands]
def spec(L):  # positive power components, x=e^L, L>=100
    return (I('0.04')*L**2*ex(-L/5)+I(13)*L*ex(-L/2)
            +sum(c*ex(-a*L) for c,a in HIG))
def thetaCH(L):
    return I(b)+116*ex(-L/2)+I('1.78')*ex(-2*L/3)
def thetaSpec(L):
    return spec(L)+I('1.000000147')*ex(-L/2)+I('1.78')*ex(-2*L/3)

def basics():
    for s,c1,c2,t,d in bands:
        v=dval(F(s),I(c1),I(c2))
        print('density',s,v,'<',d)
        assert low(I(d),v)
    assert low(I(b),PI/H)
    assert low(I('0.1'),spec(I(200))*ex(I(25)))
    # FKS zero-sum c slope from Lemma 2.1: U=10^6, Rosser choice.
    u=10**6; l=I(u).log()
    c=1/(2*PI)+(I('.137')*l+I('.443'))/(u*l*(l-(2*PI).log()))
    r=I('.137')*l+I('.443')*l.log()+I('1.588')
    assert low(I('.32'),2*c)
    assert low(I(23),2*(I('11.3993199147')+2*r/u))
    # For L>=100, 23 < .001 L²? no: use coefficient slack from 1/(2pi).
    # Actual log(V/U)*log(sqrt(VU)/2pi) < log(V)^2/2.
    assert low(I('.16'),c)
    # Its negative linear-in-log(V) term more than absorbs 23 for L>=100.
    # With v=log V<=L/2, use algebra v²/2-v*log(2pi)- l²/2+l*log(2pi).
    assert low(c*(l*l/2-l*(2*PI).log()+I(50)*(2*PI).log()),I(23)/2)
    assert low(I(100)/2,(I(10**6)).log())
    assert low(I(1)/160,I(23)/200**2+I('.16')*(I(1)/8+I(10).log()/200)**2+I('2.091')/800)
    # N(t) <= t log(t)/5, t>=100 (check at 100 and monotonic ratios).
    t=I(100); v=t.log()
    R=I('.137')*v+I('.443')*v.log()+I('1.588')
    assert low((I('0.2')-1/(2*PI))*t*v,I('.875')+R)
    # tighter square-zero tail from t>=100: integrate main upper
    assert low(I(1)/160,I(23)/200**2+I('.16')*(I(1)/8+I(10).log()/200)**2+I('2.091')/800)
    # N(t)<=t(log(t)-log(2*pi)-1)/(2*pi)+R(t)+7/8.
    # R(t)+7/8 <= 2*log(t) for t>=100.
    assert low(2*v,R+I('.875'))
    assert low(I('.12'),2*I('.5922435112')/14+2*(v-(2*PI).log())/(PI*t)+8*(v/2+I('.25'))/t**2)
    assert low(I('0.000000000008'),F(4,5)*(I(H).log()+1)/H)

if __name__=='__main__':basics()


# Positive-layer density refinement, including nested counts exactly once.
starts=[F(j,1000) for j in range(800,875)]+[F(j,10000) for j in range(8741,8750)]+[F(7,8)]
cs=[('8.17','3.70'),('8.55','3.62'),('8.94','3.54'),('9.34','3.46'),
    ('9.75','3.38'),('10.18','3.30'),('10.62','3.22'),('11.08','3.14')]
LS=[]
ds=[]
for a in starts[:-1]:
    c1,c2=cs[(100*a-80)//1]
    ds.append(dval(a,I(c1),I(c2)))
for i,z in enumerate(starts[1:]):
    c=ds[i]-(ds[i+1] if i+1<len(ds) else 0)
    assert c.lo>=0
    LS.append((c,1-z,F(0)))
def layer(L,c,g,h):
    assert not h
    return c*ex(-g*L)
def refined(L):
    return I('.04')*L**2*ex(-L/5)+13*L*ex(-L/2)+sum(layer(L,*m) for m in LS)

def optimized_ch(L, fixed=False, ratio=F(1,2)):
    # For 30<=L<=58.  T=10^7 is also useful below 34;
    # T=e^(L/2)/2 is valid on [34,58].
    T=I(10**7) if fixed else ex(L/2)*ratio
    h=(T/(2*PI)).log()
    return PI/(T-1)+PI**2/(3*T**2)+(h*h/(2*PI)-h/(6*PI))*ex(-L/2)

