#!/usr/bin/python3.10
from bounds import *

def sqrt(x): return (I(x).ln()/2).exp()
def shape(L):
    z=sqrt(L)
    return 2*L*z*(-I('.8476836')*z).exp()
def fks():
    L0,L1=LN2,I(3).ln()
    assertlt(shape(L0),1-LN2/2)
    assertlt(shape(I('2.1').ln()),1-LN2/I('2.1'))
    c=I('.8476836')
    assertlt(LN2/2,sqrt(L0)*(-c*sqrt(L1)).exp()*(3-c*sqrt(L1)))
    for z,sgn in [('2.29012',-1),('2.29014',1)]:
        x=I(z); v=shape(x.ln())-(1-LN2/x)
        print('FKS onset bracket',z,v)
        assertlt(0,sgn*v)
    for u in (L1,I(40)): assertlt(Q('.77'),shape(u))
    assertlt(3,c*sqrt(40))
    assertlt(Q('1.93378e-8'),shape(I(1000)))
    assertlt(Q('1.94751e-12'),shape(I(2100)))
    assertlt(Q('.77'),Q('9.22022')/2*shape(L0))

def pt():
    x=I('2.9')
    assertlt(1-LN2/2,1-LN2/x)
    delta=1-LN2/3
    t=LN2; p=2; ps=[2]
    for n in range(3,600):
        if any(n%r==0 for r in ps if r*r<=n): continue
        if n!=3: assertlt(1-t/n,delta)
        assertlt(t/p-1,delta)
        ps.append(n);p=n;t=t+I(n).ln()
    assertlt(1-t/599,delta)
    assertlt(t/p-1,delta)
    L=I(3914)
    bd=bD(L,0,True)
    assertlt(L**6*bd,720)
    assertlt(sum(I(factorial(k))/L**(k-5) for k in range(6,21))+L**5*(bd+err(L)),Q('.19'))
    B=1/L+196/L**2
    assertlt(Q('.19'),720*B)
    R=I('5.573412'); c=I('1.89')
    def last(U):
        return U**5*I('379.7')*(I('1.52')*(U/R).ln()-c*sqrt(U/R)).exp()
    assertlt(Q('.99'),1-Q('.48')/3800-c/(2*sqrt(R*3800)))
    assertlt(16*(-I(2)).exp()/(8*PI),500)
    assertlt(I(1169)/Q('6.455'),500)
    v=I('3.04')/c
    assertlt(462*(Q('3.04')*v.ln()-c*v).exp(),500)
    assertlt(500/LN2**2,1100)
    assertlt(1100*L**6*(-I(114)).exp()+last(L)/(Q('.99')*L),last(L)*B)
    print('PT small-piece and domination checks OK; a(anchor)',last(L))

if __name__=='__main__':
    fks();pt()
    L=I(100); logder=cH*(-L/2).exp()/(2*A_C(L))
    assertlt(I('1e-8'),logder)
    assertlt(logder,I('1e-7'))
    print('CH2 log slope at 100',logder)
