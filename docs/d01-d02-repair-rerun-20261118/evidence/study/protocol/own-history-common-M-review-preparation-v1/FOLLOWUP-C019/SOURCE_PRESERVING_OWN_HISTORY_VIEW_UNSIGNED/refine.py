"""Additional exact interval certificates. Uses rigor.py + analytic_check.py."""
from analytic_check import *
b=F(379,2)
grid2=[F(i,10000) for i in range(7700,8751)]

def W2(s,z):
    z=I(z); lam=(8*I(s)-5)/3; q=5-2*I(s); r=q-3
    c,d=params(s)
    k=lam*z
    f=sum(comb(3,j)*(I(fac(j))/k**j+r*fac(j+1)/k**(j+1)) for j in range(4))
    return 2*(c*e(-lam*z+q*log(z))/lam*f+d*e(-z)*(z*z+2*z+2))

def test_W2():
    w=[]
    for s in grid2[:-1]:
        t=W2(s,h)
        if w: t=I(min(t.lo,w[-1].lo),min(t.hi,w[-1].hi))
        w.append(t)
    w.append(I(0))
    L=I(b);v=L/3+1
    j=I('2.1')*L*e(-L*(F(1,3)-F(1,8)))+(v*v/6+3)*e(-L*F(3,8))
    j+=(v*v/12+1)*e(-L*F(21,200))+W2(s0,L/3)
    z=sum((x-y)*e(-L*(sm-s)) for x,y,s in zip(w,w[1:],grid2[1:]))
    assert j+z<I('.021')
    assert w[-2]<I('.01055')
    print('refined density scaled at b:',j+z,'asymptotic coefficient:',w[-2])

def Dstar(L):
    L=I(L);bb=I(b)
    return I('.021')*e(-L/8)*(1+1/(L*(I(F(7,8))-2/bb)))+3*e(-L/2)*(1+1/(L*(I('.5')-2/bb)))+I('7e-15')*(L/bb)*e(bb-L)
def Dmin(L):
    d=Dc(L)
    if L<b:return d
    f=Dstar(L)
    return I(min(d.lo,f.lo),min(d.hi,f.hi))
def test_R():
    bb=I(b)
    assert (a0/(I('.9')*bb)+117*e(-bb/2)/(I('.4')*bb)+40*bb*e(10-bb)/(8*PI))<I('7e-15')
    assert maincmp(58)*58**2<I('.001')
    for a,z,cap in [(58,180,125),(180,188,143)]:
        A=I(a);Z=I(z)
        # Normalized flat component at left, scaled at right.
        m=2*upper(A)+Dc(A)+A/(A-1)
        flat=a0*(1+1/(I('.9')*(A-1)))
        tails=117*e(-(A-1)/2)*(1+1/(I('.4')*(A-1)))+40*(A-1)*e(11-A)/(8*PI)
        assert m*(Z**6*flat+A**6*tails)<cap
    # Relative proof for the transition: use decreasing factors at l,
    # the scaling power at u, and positive factorial coefficients at u.
    K=[Acoef(k) for k in range(6,18)]
    assert all(k>0 for k in K)
    assert E_scaled(F(383,2),Dstar)*F(383,2)**2<I('141')
    for i in range(188000,191500):
        a=F(i,1000);z=a+F(1,1000);A=I(a);Z=I(z)
        d=Dmin(a);d1=Dmin(a-1)
        err=(d*(2*upper(A)+d)+A/(A-1)*d1)*Z**6
        main=sum(I(k)/Z**j for j,k in enumerate(K))
        assert main-err>I('4.251'), (a,main-err)
    for L,d,k in [(225,3,1412),(260,4,13985),(330,5,145450),(400,6,1610021)]:
        assert (E_scaled(L,Dstar)+maincmp(L))*I(L)**d < k
    # Extra loss for replacing pi(x/e) by pi(x/e*(1-(1+12/L)/L^4)).
    u=I('1.001')
    A,Z=I(58),I(191)
    am=A-u
    fac=2*A/(A-u)
    flat=a0*(1+1/(I('.9')*am))
    tail=117*e(-am/2)*(1+1/(I('.4')*am))+40*am*e(10-am)/(8*PI)
    assert fac*(Z**5*flat+A**5*tail)<I('.65')
    assert 2*Z**6/(Z-u)*Dstar(Z-u)<I('.65')
    assert (12+u)/(1-u/58)<I('13.25')
    assert (1+I(12)/58)/I(58)**4<1-e(I('-.001'))
    print('refined R transition certified: 3500 closed cells')

def test_M():
    n=1000
    Hn=sum(I(1)/k for k in range(1,n+1))
    gg=Hn-log(n)-I(1)/(2*n)+hull(0,F(1,n*n))
    assert 2+gg-log(4*PI)<I('.04620')
    for m,coef in [(24,'.088'),(26,'.044')]:
        L=I(m)
        j0=I('.11')*e(-L/2)+2*e(-L)+I('7e-12')*e(-L/8)
        d0=(Df(L)+2*(1+1/L)*j0+(I('1.41')+I('2.4')/L)*e(-L/2))/L
        assert d0/(1-d0)*L**3<I(coef)
        assert (Df(L)+j0+I('1.41')*e(-L/2))*L**2<I(coef)
    assert e(I(24))<26489122130
    L=I(26)
    j=I('.04620')*e(-L/2)+2*e(-L)+I('7e-12')*e(-L/8)
    d=(Df(L)+2*(1+1/L)*j+I('1.41')*e(-L/2))/L
    assert d/(1-d)*L**3<I('.044')
    assert (Df(L)+j+I('1.41')*e(-L/2))*L**2<I('.044')
    assert e(L)>195729609428 and e(L)<195729609429
    st=I(b)
    assert 3*e(-st*F(3,8))<I('.00001')
    assert I('.0212')*(1+I('.0212')*e(-st/8))<I('.0213')
    assert (I('.021')+2*(1+1/st)*(I('.04620')*e(-st*F(3,8))+2*e(-st*F(7,8))+I('7e-12'))+
            I('1.41')*e(-st*F(3,8)))<I('.02101')
    assert e(-I(190)/8)<I('.001')
    assert I('.02101')/(1-I('.02101')*e(-st/8)/st)<I('.0211')
    assert I('.0212')-I('.02101')*(1+I('.0212')*I('.001'))>0
    assert I('.0212')/(1-I('.0212')*I('.001'))<I('.02121')
    assert 1/(1-I('.0212')*I('.001'))<I('1.0001')
    assert I('.0211')*I('1.0001')+I('.02121')<I('.0424')
    assert I('.0424')*I(190)**2*e(-I(190)/8)<I('.2')
    assert I('.0421')-I('.02101')*(2+I('.0421')*I('.001'))>I('.00007')
    assert I('.0421')*I(190)**2*e(-I(190)/8)<I(F(1,5000))
    print('gamma for small-zero weight:',gg)

def test_short():
    L=I(100000)
    assert 3*L/8-14*log(L)+log(3)>L/3
    assert 3*L/8+log(3)<I('.4')*L
    assert sum(I(fac(j)*comb(4,j))*F(9,8)**j for j in range(5))<100
    assert sum(I(fac(j)*comb(4,j))*(9/L)**j for j in range(5))<2
    assert 3*144*F(8,125)*e(1)/4<20
    assert 3*900*F(8,125)*e(1)/4<120
    assert 20*e(-log(L)*F(5,12))+120*e(-log(L)*F(23,6))<I('.166')
    # Scaled exponential terms at L0 are negligible; avoid underflow
    # by bounding all e^(-kL) (k>=1/40) by a single e^-70.
    assert 3*L*(L*L+2*L+2)*e(-70)<I('.001')
    err=(I('8.4')*(L+1)*e(-70)+4*((L+1)**2/6+3)*e(-70)
         +4*e(1)*((L+1)**2/12+1)+6*e(-70))/L**14
    assert err<I('.001')
    print('short-interval error: < 0.335 times length')

if __name__=='__main__':
    pi_check();test_W2();test_R();test_M();test_short()
