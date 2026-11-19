"""Exact number/interval certificates. Run with /usr/bin/python3.10."""
from fractions import Fraction as F
from math import factorial, comb

def exp_bounds(x):
    x=F(x)
    if x<0:
        lo,hi=exp_bounds(-x)
        return 1/hi,1/lo
    k=max(1,(x.numerator+x.denominator-1)//x.denominator)
    y=x/k
    s=term=F(1)
    for j in range(1,65):
        term=term*y/j
        s+=term
    return s**k,(s+term*y/65*F(66,65))**k

def ln_unit(x,n=70):
    z=(F(x)-1)/(F(x)+1)
    assert 0<=z<=F(1,3)
    s=2*sum(z**(2*j+1)/(2*j+1) for j in range(n))
    return s,s+2*z**(2*n+1)/((2*n+1)*(1-z*z))

def ln_bounds(x):
    x=F(x); k=0
    while x>=2:x/=2;k+=1
    while x<1:x*=2;k-=1
    a,b=ln_unit(x);c,d=ln_unit(2)
    return a+k*(c if k>=0 else d),b+k*(d if k>=0 else c)

# s, rounded c1,c2, certified total both signs (columns above or equal).
rows=[('.70','4.842','4.898','75000'),('.75','6.173','4.500','515'),
      ('.80','7.798','4.101','6.13'),('.81','8.161','3.693','2.59'),
      ('.82','8.538','3.613','1.095'),('.83','8.927','3.533','.466'),
      ('.84','9.330','3.453','.199'),('.85','9.747','3.373','.0852'),
      ('.86','10.176','3.293','.0366'),('.87','10.620','3.213','.01576'),
      ('.875','11.076','3.133','.01057')]
# For .70, .75 use the previous row inclusive endpoint.
rows=[tuple(map(F,row)) for row in rows]
H=3*10**12

# Include a fine top mesh; constants from the enclosing [0.87,0.88] row.
mesh=[F(i,1000) for i in range(700,870)] + [F(i,10000) for i in range(8700,8750)]
def bracket(s):
    for t,c,d,W in rows:
        if s==t:return c,d
    table=[('.75','6.173','4.500'),('.80','7.798','4.101'),('.81','8.161','3.693'),
           ('.82','8.538','3.613'),('.83','8.927','3.533'),('.84','9.330','3.453'),
           ('.85','9.747','3.373'),('.86','10.176','3.293'),('.87','10.620','3.213'),
           ('.88','11.076','3.133')]
    return next((F(c),F(d)) for t,c,d in table if s<=F(t))
def wproof(s,y,Y,Ly):
    c,d=bracket(s);r=(8*s-5)/3;q=5-2*s
    return 2*(c*exp_bounds(-r*y)[1]*exp_bounds(q*Ly)[1]/(r-q/y)
           + d*Y**2*exp_bounds(-y)[1]/(1-2/y))

def rup(x,base):
    return F((x*base).__ceil__(),base)

def ehi(t): return rup(exp_bounds(t)[1],10**150)

def rounded_weights():
    # Certificates retained separately: first column is lower beta in units 1/10000.
    from pathlib import Path
    out=Path(__file__).with_name('weights.txt')
    y=F(287296,10000);Y=F(287297,10000);Ly=F(3358,1000)
    a,b=ln_bounds(H)
    assert y<a<b<Y and ln_bounds(Y)[1]<Ly
    w=[(s,rup(wproof(s,y,Y,Ly),1000000)) for s in mesh]
    w=[(s,min(v for _,v in w[:i+1])) for i,(s,_) in enumerate(w)]
    assert all(b<=a for (_,a),(_,b) in zip(w,w[1:]))
    assert w[-1][0]==F('.8749')
    expected=''.join(f"{int(s*10000)} {int(v*1000000)}\n" for s,v in w)
    if __name__=='__main__' and 'make' in __import__('sys').argv:
        out.write_text(expected)
    else:
        assert expected==out.read_text()
    return w

def cert_density():
    # Round logarithms to short rationals before exponentiating, for efficiency.
    y0,y1=ln_bounds(H); y=F(287296,10000);Y=F(287297,10000)
    assert y<y0<y1<Y
    Ly=F(3358,1000)
    assert ln_bounds(Y)[1]<Ly
    def check(r,q,c,d):
        a=exp_bounds(-r*y)[1]; b=exp_bounds(q*Ly)[1]
        cst=2*(c*a*b/(r-q/y)+d*Y**2/(H*(1-2/y)))
        return cst
    for s,c,d,W in rows:
        tmp=check((8*s-5)/3,5-2*s,c,d)
        print(float(s),float(tmp),float(W))
        assert tmp<W

def power_coeff(L,w):
    return ((L/3+1)**2/6+2)*ehi(-F('.175')*L)+F('2.091')*L*ehi(-F(5,24)*L) + (
         sum((a-b)*ehi((t-F('.875'))*L) for (s,a),(t,b) in zip(w,w[1:])) + w[-1][1])

if __name__=='__main__':
    # Machin: atan addition gives pi=16 atan(1/5)-4 atan(1/239).
    def atan(x,n):
        return sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n))
    def pai(n):
        return (16*atan(F(1,5),n)-4*atan(F(1,239),n+1),
                16*atan(F(1,5),n+1)-4*atan(F(1,239),n))
    pi0,pi1=pai(8)
    assert F(25,8)<pi0<pi1<F('3.144')
    cert_density()
    w=rounded_weights()
    for L in [F(185),F(190),F(191),F(192),F(195),F(200),F(250),F(400)]:
        val=rup(power_coeff(L,w),10**7)
        print("L, certified psi coefficient", L, float(val))
        if L==200: assert val<F('.028')
        if L==190: assert val<F('.019535')

