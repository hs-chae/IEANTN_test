"""Exact real-ray Ramanujan certificates (uses cert.py)."""
from cert import F, exp_bounds, ln_bounds, rup
from math import factorial, comb
from functools import lru_cache

@lru_cache(maxsize=None)
def eu(t):
    """Upper e**t, t<=0, by range reduction and directed squaring."""
    assert t<=0
    scale=10**85
    k=1
    while k< -t:k*=2
    # exp(a)> its Taylor polynomial with 50 terms for a>=0.
    a=-t/k
    term=s=F(1)
    for j in range(1,41):
        term*=a/j
        s+=term
    n=(s*scale).__floor__()
    while k>1:
        n=n*n//scale
        k//=2
    return rup(F(scale,n),scale)

D=F('1.048e-12')
P=F('.01955')

def S(t):
    return sum(F(factorial(k))/t**(k+1) for k in range(13))

def Bpower(u):
    return (10000*eu(-u)+(2*D+348*eu(F(-95)))/190**2*eu(190-u)
                    +P*(1+2/u)*eu(-u/8)/u+3*factorial(13)/u**14)

def B(u,v):
    rem=3*factorial(13)/u**14
    vals=[10000*eu(-u)+(D*(1+2/u)+116*(1+3/u)*eu(-u/2))/u+rem]
    if v<=F('43.7'):
        vals.append((F('1.95')+F('3.9')/u+F('19.5')/u**2)*eu(-u/2)/u+
                    8*eu(-u)+4*factorial(13)/u**14)
    if v<=58:
        vals.append(10000*eu(-u)+(u+2)*eu(-u/2)/25+rem) # 8*pi>25
    if u>=190:
        vals.append(Bpower(u))
    return min(vals)

c=[sum(factorial(k)*comb(j,k) for k in range(min(j,12)+1))
  -sum(factorial(k)*factorial(j-k) for k in range(max(0,j-12),min(j,12)+1))
  for j in range(25)]
assert c[:8]==[0,0,0,0,1,14,145,1412] and min(c[:19])==0
assert c[19]+sum(min(0,c[j])/F("30.5")**(j-19) for j in range(20,25))>0

def dm(t,start=4):
    return sum(c[j]/t**(j-start) for j in range(start,19))

def loss(a,b):
    V=B(a,b);W=B(a-1,b-1)
    return b**5*W + b**6*(2*S(a)+V)*V

def anchor():
    lm,lp=ln_bounds(2)
    lm,lp=-rup(-lm,10**26),rup(lp,10**26)
    # ln(20/ln2), and the positive exp series integrated on [ln2,20].
    a,b=ln_bounds(20/lp)[0],ln_bounds(20/lm)[1]
    a+=sum((20**j-lp**j)/F(j*factorial(j)) for j in range(1,81))
    b+=sum((20**j-lm**j)/F(j*factorial(j)) for j in range(1,81))
    b+= F(20**81,81*factorial(81))*F(4,3)
    y,z=exp_bounds(20)
    assert 0<a-z*S(F(20))<b-y*S(F(20))<6
    # Anchor at exp(22) differs by integral of derivative discrepancy.
    # Its difference >0 and <6 + (e^22-e^20)*13!/20^14 < 50.
    assert 6+exp_bounds(22)[1]*factorial(13)/20**14<50
    assert exp_bounds(11)[1]/F('12.5')<5000
    assert exp_bounds(F('43.7'))[1]<10**19

def certify():
    anchor()
    # Pure-power bound for theta (with prime powers); same global delta envelope.
    assert P*eu(F(-190,8))<D
    assert F('.019535')+(F('1.000000147')+F('1.78')*eu(F(-190,6)))*eu(F(-190*3,8))<P
    # .019535 from cert.py; PNT-derived tail is no worse than global bound.
    a=F('30.5')
    for stop,step,target in [(31,F(1,400),F('.04')),
                             (32,F(1,200),F('.30')),(F('33.2'),F(1,50),F('.70')),
                             (48,F(1,50),F(1)),(191,F(1,50),'refined')]:
        worst=F(10000)
        while a<stop:
            b=min(a+step,F(stop))
            eps=loss(a,b)
            if target=='refined':
                margin=dm(b,6)-b*b*eps-2
            else:
                margin=dm(b)-eps-target
            assert margin>0, (float(a),float(b),float(margin))
            worst=min(worst,margin)
            a=b
        print("checked through",stop,"margin",float(worst))
    # On [191,infinity) the scaled error L^2*eps is decreasing termwise.
    def eps(L):
        a,b=Bpower(L),Bpower(L-1)
        return L**5*b+ L**6*(2*S(L)+a)*a
    assert F(191)**2*eps(F(191))<143
    for q,L in [(3,223),(4,257),(5,292),(6,327),(7,363),(8,408)]:
        assert F(L)**q*eps(F(L))<c[4+q]

if __name__=='__main__':certify()
