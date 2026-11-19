"""Analytic Mertens constants: endpoint checks of monotone majorants."""
from verify import I,D,pi,c,dense,H
E=lambda x:I(x).exp()
def lt(a,b):
    assert I(a).b<I(b).a,(a,b)

log2=I(2).log()
lt(I('.137')+I('.443')+I('2.463')/I(100).log(),4)
def dyad(y):return I(4)*(I(y).log()+2*log2)/(5*y)
lt(2*(I('.5922435112')/14+dyad(100)),'.2')
lt(2*dyad(H),'2e-11')
lt((2*pi).log(),2)
lt(-(1-E(-2)).log()/2,(2*pi).log())
def ve(L):return 1+I('7.3938')/L+10*E(-I(L)/6)
# normalized against e^{-L/2}; the high zeros have slower exponent.
def je(a,b):
    return (1+I(1)/a)*(I('.4')+I('4e-11')*E(3*I(b)/8)+2*E(-I(a)/2))
def rem_scaled(a):
    f=1+I(1)/a
    return (ve(a)+I('.4')*f)*E(-3*I(a)/8)+I('4e-11')*f+2*f*E(-7*I(a)/8)
eta=I('1.0001')
lt(E(I('3.25')*E(-I(17)/2)/17),eta)
lt(E(29),10**13); lt(E(58),'2.169e25')
lt(E((I(29)**2/(8*pi)+3)*E(-I(29)/2)/29),eta)
lt(E((c+117*E(-I(58)/2)+I('5e-11')*E(-I(58)/8))/58),eta)
lt(E((dense(I(189),True)+rem_scaled(189))*E(-I(189)/8)/189),eta)
lt(I('.791')+ve(17)+je(17,29),'3.25')
lt(I('1.415')+je(17,29),'3.25')
lt(ve(29)+je(29,58),3)
# c includes psi const; keep slow small high-zero term separately.
lt(ve(58)+(1+I(1)/58)*(I('.4')+2*E(-29))+I('113.67'),117)
lt((1+I(1)/58)*I('4e-11'),'5e-11')
split=189
lt(eta*I('3.25')*E(-3*I(17)/8),'.01970')
lt(eta*(I(29)**2/(8*pi)+3)*E(-3*I(29)/8),'.01970')
lt(eta*(c*E(I(split)/8)+117*E(-3*I(58)/8)+I('5e-11')),'.01970')
for L,K in [(split,'.01970'),(200,'.01886'),(300,'.01517'),(500,'.01311'),
            (1000,'.01183'),(3000,'.01099'),(30000,'.01052'),(1000000,'.01046')]:
    u=dense(I(L),True)+rem_scaled(L)
    lt(u*E(u*E(-I(L)/8)/L),K)
    print('shared Mertens power constant',L,K)
# Strict Dusart dominance for the products/reciprocal sum; weighted comparison weaker.
lt(eta*I('3.25')*I(17)**2*E(-I(17)/2),'.2')
lt(eta*(I(29)**4/(8*pi)+3*I(29)**2)*E(-I(29)/2),'.2')
lt(eta*(c*split**2+117*58**2*E(-29)+I('5e-11')*58**2*E(-I(58)/8)),'.2')
lt(I('.01970')*split**2*E(-I(split)/8),'.2')
print('strict Dusart comparison for every L>=17')

# Extend the compact power profile backward, keeping the stronger early bounds.
lt(I('.791')+ve(14)+je(14,17),'3.75')
lt(I('1.415')+je(14,17),'3.75')
U=I('3.75')*E(-7)
lt(I('3.75')*E(-3*I(14)/8)*E(U/14),'.01970')
lt(E(14),2278383)
for x,k in [(100000,'.597'),(500000,'.372')]:
    z=I(x).log()
    lt(I(k)*E(z/8)/z**2,'.01970')
    print('early-to-power bridge',x,k)

lt(eta*I('3.25')*I(18)**2*E(-9),'.130')
for coeff in [eta*(I(29)**4/(8*pi)+3*I(29)**2)*E(-I(29)/2),
       eta*(c*split**2+117*58**2*E(-29)+I('5e-11')*58**2*E(-I(58)/8)),
       I('.01970')*split**2*E(-I(split)/8)]:
    lt(coeff,'.130')

def cross(L):return I('.01970')*I(L)**2*E(-I(L)/8)
for lo,hi,target,base in [(40,41,'.2',2278382),(35,36,'.3',912560)]:
    lt(I(base).log(),16)
    lt(target,cross(I(base).log()))
    lt(target,cross(lo))
    lt(cross(hi),target)
    print('unique matched power/polynomial crossover',lo,hi,target)
