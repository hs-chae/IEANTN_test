"""Exact arithmetic checks for inequalities in candidate.md."""
from rigor import *
from math import factorial as fac, comb

def e(x): return exp(x)
H=I(3*10**12); h=log(H); a0=PI/H
s0=F(77,100); sm=F(7,8)
grid=[F(i,1000) for i in range(770,876)]
# Upper roundings of Table 8, using either listed interval at a shared endpoint.
density=[(750,'7.798','4.101'),(800,'8.162','3.693'),(810,'8.538','3.613'),
         (820,'8.928','3.533'),(830,'9.331','3.453'),(840,'9.747','3.373'),
         (850,'10.177','3.293'),(860,'10.621','3.213'),(870,'11.077','3.133')]
def params(s):
    _,c,d=next(t for t in reversed(density) if F(t[0],1000)<=s)
    return I(c),I(d)
def W(s,z):
    z=I(z); lam=(8*I(s)-5)/3; q=5-2*I(s)
    c,d=params(s)
    return 2*(c*e(-lam*z+q*log(z))/(lam-q/z)+d*e(-z)*z*z/(1-2/z))
def test_density():
    w=[W(s,h) for s in grid[:-1]]+[I(0)]
    assert all(a>b for a,b in zip(w,w[1:]))
    L=I(190);v=L/3+1
    j=I('2.1')*L*e(-L*(F(1,3)-F(1,8)))+(v*v/6+3)*e(-L*F(3,8))
    j+=(v*v/12+1)*e(-L*F(21,200))+W(s0,L/3)
    b=sum((x-y)*e(-L*(sm-s)) for x,y,s in zip(w,w[1:],grid[1:]))
    assert j+b<I('.022')
    assert W(sm,h)<I('.011')
    for U in (I(100),H):
        l=log(U)
        r=I('.137')*l+I('.443')*log(l)+I('1.588')
        c=1/(2*PI)+(I('.137')*l+I('.443'))/(U*l*log(U/(2*PI)))
        assert c<I(F(1,6)) and 2*r/U<I('.1')
    assert e(1)>I('2.45') and e(L/3)>2*L and e(L/2)/5-1>e(L/3)
    print('density scaled at 190:',j+b,'W(7/8):',W(sm,h))

def P(L):
    L=I(L)
    return sum(I(fac(k))/L**k for k in range(18))
def lower(L):
    L=I(L)
    return P(L)-36*e(1-L)
def upper(L):
    L=I(L)
    return P(L)+4*L*e(-L)+I(fac(18))/L**17
def Df(L):
    L=I(L); return L**2*e(-L/2)/(8*PI)
def Dc(L):
    L=I(L)
    return a0*(1+1/(L*I('.9')))+117*e(-L/2)*(1+1/(L*I('.4')))+40*L*e(10-L)/(8*PI)
def Dd(L):
    L=I(L)
    return I('.023')*e(-L/8)*(1+1/(L*(I(F(7,8))-I(2)/190)))+3*e(-L/2)*(1+1/(L*(I('.5')-I(2)/190)))+I('2.12e-12')*(L/190)*e(190-L)
def Dh(L):
    L=I(L)
    return (L*L+L/I(F(7,8)))*e(-L/8)/64+3*e(-L/2)*(1+1/(L*(I('.5')-I(2)/200)))+I('2.12e-12')*(L/200)*e(200-L)
def Acoef(k):
    return sum(fac(j)*comb(k,j) for j in range(k+1))-sum(fac(j)*fac(k-j) for j in range(k+1))
def maincmp(a):
    # Upper bound for omitted square coefficients, upper truncation error,
    # and the lower approximation error at L-1, all multiplied by L^4.
    L=I(a)
    tail=sum(I(fac(j)*fac(k))/L**(j+k-4) for j in range(18) for k in range(18) if j+k>=18)
    d=4*L*e(-L)+I(fac(18))/L**17
    return tail+L**4*((2*P(L)+d)*d+36*L/(L-1)*e(2-L))
def E_scaled(L,d,prev=None,one=False):
    L=I(L);u=upper(L); z=d(L)
    if prev is None: prev=d
    return L**4*(L/(L-1)*prev(L-1)+(0 if one else z*(2*u+z)))
def poly4(L):
    L=I(L)
    return sum(I(Acoef(k))/L**(k-4) for k in range(4,18))
def test_main():
    assert [Acoef(k) for k in range(7)]==[0,0,0,0,1,14,145]
    assert all(Acoef(k)>0 for k in range(4,18))
    assert log(I('1.2e17'))>39 and log(I('2.169e25'))>58
    assert I(18)/(1-I(17)/36)<36
    assert maincmp(37)<I('.0001') and upper(37)<I('1.04')
    for a,b in [(37,F(371,10)),(F(371,10),38),(38,39),(40,41)]:
        lhs=E_scaled(a,Df,one=a<39)
        assert lhs+I('.0001')<poly4(b), (a,b,lhs,poly4(b))
    assert E_scaled(41,Df)<I('.91')
    assert E_scaled(58,Dc)<I('.002')
    # On [58,191], bound growing constant component at right and two
    # decaying tails at the left by bounding their scaled contribution.
    def flat(L):
        L=I(L);return a0*(1+1/(I('.9')*57))
    def tail(L):
        L=I(L);return 117*e(-L/2)*(1+1/(L*I('.4')))+40*L*e(10-L)/(8*PI)
    assert Dc(57)<I('.00001')
    assert ((I('2.081')+I(58)/57)*I(191)**4*flat(191)+
           (I('2.081')+I(58)/57)*I(58)**4*tail(57)<I('.01'))
    assert E_scaled(191,Dd)<I('.01')
    assert (Dc(190)+a0+117*e(-I(190)/2))<I('2.12e-12')
    assert (Dc(200)+a0+117*e(-I(200)/2))<I('2.12e-12')
    # Independent route using only the given PsiMajorant (no density).
    assert ((I('2.081')+I(58)/57)*I(271)**4*flat(271)+
           (I('2.081')+I(58)/57)*I(58)**4*tail(57)<I('.03'))
    assert E_scaled(271,Dh)<I('.038')
    print('main omitted-term loss at L=37:',maincmp(37))
    print('scaled losses at 40/41/191/271:',*[E_scaled(k,d) for k,d in ((40,Df),(41,Df),(191,Dd),(271,Dh))])

def test_mertens():
    assert e(I(21)/2)>32321
    assert log(2)>I('.69')
    L=I(21)
    a=I(20)
    assert 2*e(-a/6)+2*e(-a/4)+2*a/log(2)*e(-a*F(3,10))<1
    assert 80/L**3+2*e(-L/6)+2*e(-L/4)+2*L/log(2)*e(-L*F(3,10))<I('.2')
    assert 80/L**3<I('.01')
    assert 2*(I('.5922435112')/14+(log(100/(2*PI))+1)/(PI*100))<I('.11')
    assert 2*(log(H/(2*PI))+1)/(PI*H)<I('7e-12')
    assert log(2*PI)<2 and log(2*PI)>1
    def j(L):return I('.11')*e(-L/2)+2*e(-L)+I('7e-12')*e(-L/8)
    def b0(L,B):
        return (B+2*(1+1/L)*j(L)+(I('1.41')+I('2.4')/L)*e(-L/2))/L
    def b1(L,B):
        return B+j(L)+I('1.41')*e(-L/2)
    for l,b,coef in [(22,Df,'0.170'),(21,Df,'0.235'),(58,lambda L:a0+I('113.67')*e(-L/2),'0.001')]:
        L=I(l)
        if l!=21:
            d=b0(L,b(L))
            assert d/(1-d)*L**3<I(coef)
        assert b1(L,b(L))*L**2<I(coef)
    L=I(190); d=b0(L,I('.023')*e(-L/8))
    assert d/(1-d)*L**3<I('.001') and b1(L,I('.023')*e(-L/8))*L**2<I('.001')
    assert a0*I(190)**2<I('4e-8')
    print('Mertens at log x=22:', b0(I(22),Df(22))*I(22)**3)

if __name__=='__main__':
    pi_check()
    test_density();test_main();test_mertens()
