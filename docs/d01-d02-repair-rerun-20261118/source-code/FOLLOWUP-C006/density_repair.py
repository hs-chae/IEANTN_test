"""Tighter majorant for the FKS high-zero mass; no D01."""
from analytic import *
from math import factorial

# Exact printed upper constants of FKS Cor. 2.9, Table 8.
table=[
    ('8.1610','3.6926'),('8.5373','3.6126'),('8.9269','3.5326'),('9.3298','3.4526'),
    ('9.7461','3.3725'),('10.1759','3.2924'),('10.6191','3.2123'),('11.0755','3.1321')]
def major(s):
    c1,c2=map(I,table[(100*s-80)//1])
    h=I(H).log()
    a=1-F(8,3)*(1-s)
    q=5-2*s
    assert 3<q<4 and a>0
    t=I(1)/a
    plus=t
    for j in range(4):
        t=t*(q-j)/(a*h)
        plus+=t
    return 2*(c1*power(h,q)*ex(-a*h)*plus+c2*(h*h+2*h+2)/H)
grid=starts[:-1]+[F(j,10**5) for j in range(87491,87500)]+[F(7,8)]
mass=[]
for s in grid[:-1]:
    v=major(s).hi
    mass.append(min(v,mass[-1]) if mass else v)
mass.append(0)   # terminal algebraic padding, not a zero count on beta=7/8
layers=[(I.raw(a-b,a-b),1-s) for (a,b),s in zip(zip(mass,mass[1:]),grid[1:])]
def sc(L):
    # Scaled pointwise psi envelope, only claim monotonicity for L>=200.
    return (I('.011')*L**2*ex(-F(3,40)*L)+I('2.091')*L*ex(-L/8)
            +sum(c*ex(-(g-F(1,8))*L) for c,g in layers))
def tail(B,C):
    L=I(B)
    assert B>=180 and low(ex(L/2),767135587)
    r=ex(-3*L/8); s=ex(-(F(2,3)-F(1,8))*L)
    j=I('.12')*r+I('.000000000008')
    assert low(I('.001'),I('.5')/(L/2)**3) # same Dusart power-tail guard
    a=sc(L)+(1+1/L)*j+I('1.84')*ex(-7*L/8)+I('1.002')*r+I('2.67')*s
    assert low(I(C),a/(1-a*ex(-L/8)/L))
    print('refined all-ray Mertens',B,C,'rescaled majorant at onset',a)
def boot_height():
    T=ex(I(25)); V=ex(I(26))
    assert low(T,100) and low((ex(I(50))-2)/5,T)
    assert low(V,I('2.45')*T) and low(V,10**6)
    u=I(10**6).log(); p=(2*PI).log()
    c=1/(2*PI)+(I('.137')*u+I('.443'))/(10**6*u*(u-p))
    assert low(I('.16'),c)
    assert low(c*(26*p+u*u/2-u*p),I(23)/2)
    assert F('.16')*F('.26')**2<F('.011')
if __name__=='__main__':
    boot_height()
    for B,C in [
        (193,'.0196'),(197,'.0196'),(200,'.01896'),(215,'.018'),(218,'.018'),(225,'.01744'),(237,'.017'),(240,'.017'),(250,'.01643'),(300,'.01513'),
        (350,'.01432'),(420,'.01358'),(600,'.01259'),(1000,'.01172'),
        (2000,'.01106'),(5000,'.01067'),(10000,'.01056'),(20000,'.01051'),
        (100000,'.01046'),(1000000,'.010454')]:
        tail(B,C)
    for B in [200,225,250,300,350,420,600,1000,2000,5000,10000,20000,100000]:
        print('diagnostic refined psi',B,sc(I(B)))
    print('diagnostic limiting coefficient plus J cost',layers[-1][0]+I('.000000000008'))
