#!/usr/bin/python3.10
"""Higher order barrier, then oscillation-preserving ray certificates."""
import cert
from mertens import spectralparts
from cert import *

def wide_Finit(L):
    b=I(600).log()
    ps=[p for p in range(2,601) if all(p%d for d in range(2,p) if d*d<=p)]
    c=len(ps)+(600-sum(I(p).log() for p in ps))/b
    def ant(s):
        assert s.a>0 and s.b<=100
        n=512
        z=s.log()
        t=I(1)
        for j in range(1,n+1):
            t=t*s/j
            z+=t/j
        return z+I(0,(2*t*s/((n+1)**2)).b)
    return c+ant(I(L))-ant(b)

T=Q(62)
H=3000000000000
CZ=(2*I(29).exp()/25+4*I(62).exp()*(ev(CH,58)+ev(powers,58))/58**2)
@lru_cache(None)
def setup(m):
    _,Z,D=spectralparts(m)
    return Z,D+powers,CZ+I(62).exp()*ev(Z,T)/(H*62**2)

@lru_cache(maxsize=128)
def osc(l,m):
    Z,D,c=setup(m)
    v=I(l)
    assert l>=62
    return (v**4*ev(Z,l)*(1+(1+2/(v*(Q(3,4)-3/T)))/(H*v))
       + sum(co*v**(4+k)*(-I(a)*v).exp()*(1+1/(v*(1-a-2/T))) for co,a,k in D)
       + c*v**5*(-v).exp())

def osc_loss(l,m):
    x,y=osc(l,m),osc(l-1,m)
    z=I(l)
    return (z/(l-1))**5*y+2*Alim(l)*x+x*x/z**4

def old_loss(l,m):
    return loss(l,l,m,False)

@lru_cache(maxsize=128)
def osc_tail(l,m,K): # controls H_K using first residual from H_70
    j=K-3
    assert l-1>=8*(8+j)
    return (osc_loss(l,m)*I(l)**j).b<I(g(K+1)).a

def find(l,r,test):
    assert test(r)
    while l<r:
        t=(l+r)//2
        if test(t):r=t
        else:l=t+1
    assert test(l)
    return l

def main():
    cert.Finit=wide_Finit
    N=70
    main_ode(N,95)
    for k in [26,27,30,35,40,45,50,55,60,65,69]:
        onset=[]
        for m in (0,1):
            start=(8*(8+k-3)+1)*2
            z=find(start,10000,lambda z:osc_tail(Q(z,2),m,k))
            onset.append(Q(z,2))
        print('profile',k,*onset,flush=True)

    # At four smaller onsets, retain CH and old S bounds in addition to oscillatory.
    # Preselect exploratory positive point values, but certify strips and the analytic tail.
    for m,c in [(0,100),(1,100),(0,145),(1,145)]:
        j=2 if c<145 else 3
        a=145-c if c<145 else g(7)
        extras=[(j,a)]+[(s-4,g(s)) for s in range(j+5,28)]
        def tailpt(z):
            L=Q(z,4)
            return (osc_loss(L,m)*I(L)**j).b<I(a).a
        root=find(4*(8*(8+j)+1),1600,tailpt)
        def pt(z):
            L=Q(z,16)
            return (sum(I(a0)/I(L)**h for h,a0 in extras)-mini(osc_loss(L,m),old_loss(L,m))).a>0
        # Threshold proposals are searched on the mesh; unsuccessful proposals are not claims.
        begin=find(16*(160 if m else 185),4*root,pt)
        ends=Q(root,4)
        L=Q(begin,16)
        buf=Q(1,32)
        while True:
            l=L; good=True
            while l<ends:
                u=min(l+buf,ends)
                val=sum(I(a0)/I(u)**h for h,a0 in extras)
                if val.a<=mini(osc_loss(l,m),loss(l,u,m,False)).b:
                    good=False
                    break
                l=u
            if good:break
            L+=buf
        print('margin',c,'B'+str(m),'onset',L,'tail',ends,flush=True)

if __name__=='__main__':main()
