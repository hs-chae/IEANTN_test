"""Exact outward-rounded verification of Mertens comparisons."""
from portfolio_check import *
from rigor import hull
from math import factorial

a=I('1.000000147'); g=I('1.78'); m=I('.9999')
def mp(l,r,mode):
    """Upper bounds in units u=e^(-L/2); other scales applied below."""
    L=hull(l,r)
    if mode==0:
        return I('.751'),I('.791')
    j=L**2/(8*PI)
    if mode==1:
        # Recover a much stronger Chebyshev comparison from the reported finite pi bound.
        gL=I('1.95')+I('3.9')/L+I('19.5')/L**2
        return gL-m+(7*L+2)*e(-L/2),a+g*e(-L/6)
    if mode==2:
        j=minimum(j,((L-2*log(L/(PI*e(1))))**2-4)/(8*PI))
    if mode==3:
        j=minimum(j,a0*e(L/2)+I('113.67'))
    if mode==4:
        j=a0*e(L/2)+I('113.67')
    return j,j

def scale(lo,hi,mode,plain=False):
    x=hull(lo,hi); u=e(-x/2); y=e(-x/6)
    off=I('7e-12')*e(x/2 if plain else 3*x/8)
    j=I('.04620')+2*u+off
    j2=I('.04620')/14+2*u+off/H
    k=(1+1/x)*j+2*(1/x+2/x**2)*j2
    d1=2*a-m+F(3,2)*g*y
    d0=a*(2-2/x+8/x**2)-m+F(3,2)*g*y
    em,ep=mp(lo,hi,mode)
    z=I(max((em+k+x*u).lo,(ep+k+d0).lo),max((em+k+x*u).hi,(ep+k+d0).hi))
    # omitted prime-product tail <= 1/x(actual), and multiplying e^-L/2 * L
    v=maximum(em+j,ep+j+d1)
    return maximum(v,z/(1-z*u/x))*u

def maximum(x,y): return I(max(x.lo,y.lo),max(x.hi,y.hi))
def coverM(a,b,h0,coef,exponent=0,plain=False):
    x=F(a); b=F(b)
    worst=I(0)
    count=0
    while x<b:
        y=min(b,x+F(h0))
        mode=(0 if y<=F('29.9') else 1 if y<=F('43.7') else 2 if y<=F('59.5') else 4)
        # boundaries are split manually by caller
        assert not any(x<t<y for t in [F('29.9'),F('43.7'),F('59.5')])
        v=scale(x,y,mode,plain)*(e(I(y)/8) if exponent else I(y)**2)
        assert v<I(coef),(x,y,exponent,v,coef)
        worst=maximum(worst,v);count+=1
        x=y
    print("M cells, first/last, power scale, cap:",count,a,b,exponent,worst,flush=True)

def spectralM(b,C,target):
    x=I(b)
    # Adding all tiny normalized corrections conservatively, including conversion.
    ua=e(-3*x/8); va=e(-7*x/8)
    jb=I('.04620')*ua+2*va+I('7e-12')
    j2b=I('.04620')/14*ua+2*va+I('7e-12')/H
    z=I(C)+(1+1/x)*jb+2*(1/x+2/x**2)*j2b+2*ua+x*va
    v=I(C)+jb+2*ua
    assert maximum(v,z/(1-z*e(-x/8)/x))<I(target)
    return maximum(v,z/(1-z*e(-x/8)/x))

def bridgeM(b,c,coef,exponent=0):
    x,y=I(b),I(c)
    fac=e(y/8) if exponent else y**2
    f=e(-3*x/8) if exponent else x**2*e(-x/2)
    j=I('.04620')*f+2*x**2*e(-x)+(I('7e-12') if exponent else I('7e-12')*x**2*e(-x/8))
    # Both kernels and both power allowances fit inside this conservative guard.
    guard=(a0*fac+118*f+3*j)*(1+I('1e-9'))
    assert guard<I(coef), (b,c,guard,coef)
    print("M CH2 bridge:",b,c,exponent,guard,flush=True)

def main():
    pi_check()
    assert e(F('18.42'))<10**8 and e(F('23.7'))<2*10**10
    assert e(F('29.9'))<10**13
    for l in (34,F('59.5')):
        T=2*PI**2*e(I(l)/2)/l
        assert I(10**7)<T<I(3000175332800)
    # a conservative q(L) square root threshold extends beyond L=58.
    assert I('1.751000147')+g*e(-I('18.42')/6)<I('1.84')
    assert I('1.84')*e(-I('18.42')/2)<I(1)/5000
    assert e(F('29.9'))>10**9
    # admissible D_0 and D_1 upper allowances < 2 u/L and 2u.
    x=I('18.42')
    assert 2*a-m+F(3,2)*g*e(-x/6)<2
    assert x>4
    for lo0,b0,step,c in [
            ('18.42','29.9',F(1,100),'.0671'),
            ('18.8','29.9',F(1,100),'.061'),
            ('23.7','29.9',F(1,100),'.0077'),
            (26,'29.9',F(1,100),'.0029'),
            (28,'29.9',F(1,100),'.00124'),
            (47,'59.5',F(1,100),'.000012'),
            ('29.9','43.7',F(1,100),'.00061'),
            ('43.7','59.5',F(1,50),'.000042')]:
        coverM(lo0,b0,step,c,plain=True)
    bridgeM(F('59.5'),180,'2e-7')
    v=spectralM(180,'.01361','.01362')
    assert v*180**2*e(-I(180)/8)<I('2e-7')
    for x,y in [('18.42','29.9'),('29.9','43.7'),('43.7','59.5')]:
        coverM(x,y,F(1,25),'.013163',1)
    bridgeM(F('59.5'),F('186.03'),'.013163',1)
    for L,t,c in [('186.03','.0131652','.013166') if DUSART_ONLY else ('186.03','.0131624','.013163'),
                  (190,'.012904','.012905') if DUSART_ONLY else (190,'.012902','.012903'),
                  (200,'.0123291','.01233') if DUSART_ONLY else (200,'.012329','.01233'),
                  (250,'.0105496','.01055'),(300,'.0096255','.009626'),
                  (400,'.0086767','.008677'),(1000,'.0073709','.007371')]:
        L=F(L)
        assert spectral(L)<I(t)
        print("M power from L",L,":",spectralM(L,t,c),flush=True)
    # Prove power envelope down to 300000 independently of the fine tape.
    # e^(log x /8)/(log x)^2 is decreasing to L=16, increasing afterwards.
    rows=[ln for ln in open("finite26.txt") if ln.startswith("[")]
    for line in rows:
        ls,rs=line[1:].split("] : ")
        aa,zz=map(int,ls.split(","))
        if aa>=10**8: break
        cc=max(map(int,rs.split()))
        for n in (aa,zz):
            x=log(n)
            assert I(cc)/10**9*e(x/8)/x**2<I('.0149')
            if aa>=500000: assert I(cc)/10**9*e(x/8)/x**2<I('.013163')
    # No-QRH version of the coefficient profiles through .00124.
    z=I('59.5'); y=I(3000)
    J=I('.04620')*z**2*e(-z/2)+2*z**2*e(-z)+I('7e-12')*y**2
    assert (a0*y**2+118*z**2*e(-z/2)+3*J)*(1+I('1e-9'))<I('.00021')
    # Beyond L=3000 use the FKS direct theta branch in ray_check.py
    # and its integral: its checks reduce to the inequality below.
    assert I('.0003')*(1/y+I('.5')*(1+1/y))+I('1e-6')<I('.00021')
    print("M comparisons and joins passed")

if __name__=='__main__': main()
