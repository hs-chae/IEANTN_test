#!/usr/bin/python3.10
from cert import *
def poly_integral(a,k,L):
    assert a>0
    return (-I(a)*L).exp()*sum(I(factorial(k)//factorial(k-j))*I(L)**(k-j)/I(a)**(j+1) for j in range(k+1))
def im(S,L,R=None):
    return sum(c*((poly_integral(a,k,L) if a else I(0))-
                  (poly_integral(a,k,R) if a and R is not None else I(0)))
               if a else c*(R-L) for c,a,k in S)
A=[(I('.791'),Q(1,2),0)]
B=[(I(Q(1,25)),Q(1,2),2)]
K=Q('29.9')
@lru_cache(None)
def m_tail(m):
    return im(S0 if m==0 else S1, Q(190 if m==0 else 169))
def phi_tail(L,m):
    J=Q(190 if m==0 else 169)
    S=S0 if m==0 else S1
    if L>=J: return ev(S,L),im(S,L)
    j=m_tail(m)+im(CH,max(L,58),J)
    if L>=58:return ev(CH,L),j
    j+=im(B,max(L,K),58)
    if L>=K:return ev(B,L),j
    return ev(A,L), j+im(A,L,K)
def tails(L):
    # normalized by 1 and by 1/L (i.e. L*upper bound for log prime powers)
    v=I(L)
    c=I('1.000000147');delta=I('166.64')/v**3
    w=(2*c-1+delta)*(-v/2).exp()+I('2.67')*(-2*v/3).exp()
    t=(2*(1+1/v)*c-1+delta)*(-v/2).exp()+I('2.67')*(1+1/v)*(-2*v/3).exp()
    return w,t
def piecewise(l,u):
    # E on block clipped to one Phi piece, bound decreasing E, J from its left endpoint.
    v=I(l); w=I(u)
    F,J=phi_tail(l,0)
    if l<K:
        # Weight better on the entire portion above K.
        J0=im(A,l,K);J1=phi_tail(K,0)[1]
        WV=F/v+(1/v+1/v**2)*J0+(1/I(K)+1/I(K)**2)*J1
    else: WV=F/v+(1/v+1/v**2)*J
    tW,tP=tails(l)
    W=WV+tP/v
    U=F+J+tW
    return ((W.exp()-1)*w**3, W*w**3,U*w**2)
def spectralparts(m):
    a=Q(1,8) if m==0 else Q(5,32)
    S=S0 if m==0 else S1
    Z=S[4:]
    D=S[:4]+[(I(12),a+Q(1,6),4),(I(15),a+Q(1,2),2)]
    return a,Z,D
def pure(L,m):
    a,Z,rem=spectralparts(m)
    v=I(L); z=ev(Z,L); d=ev(rem,L); j=im(rem,L)
    w,t=tails(L)
    # L times log error, and weighted sum error
    tlog=(1+2/(3000000000000*v))*z+d+(1+1/v)*j+t
    tw=z+d+j+w
    x=tlog/v
    # exp(x)-1 <= x/(1-x) (x>=0, x<1), without cancellation
    tprod=tlog/(1-x)
    res=I(a*L).exp()
    return tprod*res,tlog*res,tw*res
def mertens():
    assert I('21.41').exp().b<D('2000000000')
    assert I('29.9').exp().b<D('10000000000000')
    assert I(62).exp().a>D('324000000000000000000000000')
    assert (I('3.14159265358979323847')/3000000000000).b<CH[0][0].a
    assert I('1.000000147').a>I(1).a
    print('B0 early inverse-log coefficients from exp(21.41) to exp(200):')
    A=[D(0)]*3
    for l,u in [(Q('21.41'),K),(K,Q(58)),(Q(58),Q(190)),(Q(190),Q(200))]:
        M=[D(0)]*3
        while l<u:
            r=min(u,l+Q(1,16))
            M=[max(v,x.b) for v,x in zip(M,piecewise(l,r))]
            l=r
        print(u,*[f'{x:.9E}' for x in M])
        A=[max(x,y) for x,y in zip(A,M)]
    assert all(v<D(c) for v,c in zip(A,['.05','.05','.05']))
    # Tail constants on rays. Each e^(aL)-rescaled positive summand is decreasing
    # on the displayed rays (the leading exponent may be constant).
    tab=[
     (0,155,'.224'),(0,180,'.026'),(0,190,'.02053'),(0,200,'.01880'),(0,240,'.01650'),
     (0,300,'.01491'),(0,500,'.01292'),(0,1000,'.01174'),(0,5000,'.01097'),
     (1,155,'.517'),(1,169,'.327'),(1,180,'.289'),(1,200,'.260'),
     (1,240,'.231'),(1,300,'.209'),(1,500,'.181'),(1,1000,'.165'),(1,5000,'.153'),
    ]
    for m,L,c in tab:
        u=pure(Q(L),m)
        print('pure',m,L,c,*[f'{x.b:.9E}' for x in u])
        assert all(z.b<D(c) for z in u)
    for m,Lw,Lp in [(0,190,186),(1,170,167)]:
        a,_,_=spectralparts(m)
        assert (pure(Q(Lw),m)[2]*(-I(a)*Lw).exp()).b<D('1e-12')
        assert (pure(Q(Lp),m)[0]*(-I(a)*Lp).exp()/Lp).b<D('1e-14')
        print('fixed-error onsets',m,Lw,Lp)
    # Density tail: J(ln(T)) <= J(h) < 6; numeric constants in D.
    d=Q(1,3);q=Q(7,2)
    integ=sum(comb(3,j)/h**j*(factorial(j)/I(d)**(j+1)+(q-3)*factorial(j+1)/(h*I(d)**(j+2))) for j in range(4))
    assert integ.b<6
    assert (2*I('7.798')*6*I(6)**Q(1,3)/16).b<12
    assert (12*I('4.101')*(Q(1,4)+Q(1,62)+Q(2,62**2))).b<15
    for m in (0,1):
        for v in [169,180,190,200,240,300,500]:
            F,J=phi_tail(Q(v),m)
            a,Z,rem=spectralparts(m)
            b=pure(Q(v),m)
            print('at',m,v,'pointwise cert:',*[f'{(r*(-I(a)*v).exp()/(v if j<2 else 1)).b:.9E}' for j,r in enumerate(b)])
    # Strict comparison of spectral vs raw D02 and old data on [200,infty)
    E1=ev(S1,Q(200))*I(Q(5,32)*200).exp()
    assert E1.b<D('.3')
    assert S0[-1][0].a>D('.01')
    assert (I('.3')*(-I(Q(1,32)*200)).exp()).b<D('.01')
    assert (I('.3')*(-I(Q(5,32)*200)).exp()).b<CH[0][0].a
    assert all(x.b<D('.019') for x in pure(Q(200),0))
    assert (I('.019')*200**2*(-I(25)).exp()).b<D('.05')
if __name__=='__main__':mertens()
