
from density import *
from certify import qc, local, fac, comb
from osc02 import LOW,HIGH,G
import sys
assert (LOW/EL(10)+HIGH/EL(20*B0)+G)/400<3
from functools import lru_cache

# All input to certificates is rational.
def termq(u,J,Q):
    v=0
    for b,m,c,M in Q:
        d=1-c-F(2-m,J)-(M/(J*(J-M)) if M else 0)
        assert d>0
        v+=b*u**m*E(c*u)*(u/(u-M) if M else 1)*(1+1/(d*u))
    return v

# Anchors can be derived from full B0 bound, or from earlier D02 transfer.
@lru_cache(None)
def branches(cap, full=False):
    stack=[]
    for j,Q in opts(cap):
        if not full:
            # A small collection suffices for certificates; full is for pointwise profile.
            if len(Q)>3 or Q[0][2] not in [F('.25'),F('.20'),F('.16')]:continue
        for J in (110,140,150,160,170,180,190,200):
            if J<j:continue
            J=F(J)
            stack.append((J,Q+P,qc(J)+val(J,CH+P)))
    if cap==B2:
        J=F(200)
        stack.append((J,((F(1,64),2,F(5,32),0),)+P,qc(J)+val(J,CH+P)))
    return stack


@lru_cache(maxsize=20000)
def qosc(u,h,cap,upper=False):
    assert u>=34
    ds=((LOW,F(1,2)),(HIGH,1-cap))
    # Absolute contribution of the psi integral in partial summation.
    extra=sum(b*E(c*u)/u*(1+1/(1-c-F(1,10))) for b,c in ds)
    extra+=G*E(u)*(1/u+u/20)+400003*u*E(u)
    pm=F('.9999')*EL(h/2)
    if h<=58:
        v=minv(u,cap)
        v=min(v,(F('.0398')*u*u-F('.385')*u+F('5.80'))*E(u/2))
    else:
        v=val(u,CH)
        for j,Q in opts(cap):
            if j<=u and u>=100 and (len(Q)==3 or j<=110 and len(Q)==4):
                v=min(v,val(u,Q))
        if u>=145:
            for k in (F('.75'),F('.80')):
                v=min(v,val(u,discrete(cap,k,F(1,400))))
        if cap==B2 and u>=200:v=min(v,u*u*E(5*u/32)/64)
    if upper:return max(0,v+extra-pm)
    return v+extra+sum(b*E(c*u)*(1+1/(u*(1-c-F(1,10)))) for b,m,c,M in P)

@lru_cache(maxsize=20000)
def q(u,h,cap,upper=False):
    a=local(u,h,True,upper)
    if not a:return a
    if u>=34:a=min(a,qosc(u,h,cap,upper))
    if u<110:return a
    return min([a]+[termq(u,J,Q)+u/J*E(u-J)*K for J,Q,K in branches(cap) if J<=u<=J+26 or (J==110 and u>=J)])
    
@lru_cache(None)
def model(N):
    A=[fac(j) for j in range(N+1)]
    C=[sum(A[k]*A[j-k] for k in range(max(0,j-N),min(j,N)+1)) for j in range(2*N+1)]
    Z=[sum(comb(j,k)*fac(k) for k in range(j+1))-C[j] for j in range(4,N+1)]
    assert min(Z)>0
    return A,C,Z
def data(N):
    if N==20:return F(24),F(10),12
    V=F(2*(N+2));return V,5/EL(V),2
@lru_cache(maxsize=10000)
def basic(l,N):
    V,H0,D=data(N);assert l-1>=V
    A,C,Z=model(N)
    s=sum(F(a)/l**k for k,a in enumerate(A))
    return s, D*fac(N+1)/l**(N+1)+H0*l*E(l),H0*l*E(l-1),sum(c/l**(j-4) for j,c in enumerate(C) if j>N)
def pen(l,h,N,qp,qm):
    s,r,rm,conv=basic(l,N)
    t=r+qp
    return conv+h**4*(2*s*t+t*t+rm+l/(l-1)*qm)
def check(l,h,N,p,qp,qm,extra=F(0)):
    z=[c-(p[i] if i<len(p) else 0) for i,c in enumerate(model(N)[2])]
    assert len(p)<=len(z)
    return sum(d/(h if d>=0 else l)**i for i,d in enumerate(z))>pen(l,h,N,qp,qm)+extra

def tail(J,N,p,cap):
    J=F(J)
    z=[c-(p[i] if i<len(p) else 0) for i,c in enumerate(model(N)[2])]
    if min(z)<0:return False
    j=len(z)-1
    residual=sum(c/J**i for i,c in enumerate(z))
    if j>=N-3 or j+5>J-1:return False
    for j0,Q in list(opts(cap))+[(100,discrete(cap)),(100,discrete(cap,F(".80")))]:
        if j0>J-1 or J<101 or any(j+4+m>c*(J-1) for b,m,c,M in Q):continue
        def qq(u):
            ds=((LOW,F(1,2)),(HIGH,1-cap))
            extra=sum(b*E(c*u)/u*(1+1/(1-c-F(1,10))) for b,c in ds)
            extra+=G*E(u)*(1/u+u/20)+400003*u*E(u)
            return val(u,Q)+extra+sum(b*E(c*u)*(1+1/(u*(1-c-F(1,10)))) for b,m,c,M in P)
        if residual>pen(J,J,N,qq(J),qq(J-1)):return True
    for J0,Q,K in branches(cap):
        if J0>J-1 or any(j+4+m>c*(J-1) for b,m,c,M in Q):continue
        qq=lambda u:termq(u,J0,Q)+u/J0*E(u-J0)*K
        if residual>pen(J,J,N,qq(J),qq(J-1)):return True
    return False

def cell(l,h,N,p,cap,step=F(1,32)):
    if check(l,h,N,p,q(l,h,cap,True),q(l-1,h-1,cap)):return None
    mid=(l+h)/2
    if h-l<=step:return l,h
    return cell(l,mid,N,p,cap,step) or cell(mid,h,N,p,cap,step)

def cover(l,h,N,p,cap):
    l,h=F(l),F(h)
    while l<h:
        r=min(l+2,h)
        if l<F('39.47')<r:r=F('39.47')
        bad=cell(l,r,N,p,cap)
        if bad:return bad
        l=r
    return None

def run(cap,mode):
    A,C,Z=model(100)
    if mode=='early':
        cases=[(s,j,20,p) for s,j,p in [
          ('36.8',225,['.01']),('36.85',225,['.04']),('37',225,['.10']),
          ('39.47',225,['.10']),('40.5',225,['.52']),('42.8',225,[1]),
          ('48',230,[1,14,6]),('49',230,[1,14,30]),('50',230,[1,14,100]),
          ('52',230,[1,14,130]),('55',230,[1,14,145]),
          ('56',230,[1,14,145]),('54',230,[1,14,145]),('58',230,[1,14,145]),
          ('160',230,[1,14,145,1412]),('176',230,[1,14,145,1412]),('183',230,[1,14,145,1412]),
          ('200',230,[1,14,145,1412]),('170',230,Z[:3]),('184',230,Z[:4]),
          ('195',230,Z[:5]),('200',240,Z[:5]),('220',240,Z[:6]),('250',290,Z[:8]),
          ('275',300,Z[:8]),('300',330,Z[:8]),('330',365,Z[:10]),
          ('360',395,Z[:10]),('425',475,Z[:13]),('450',500,Z[:13]),
          ('550',600,Z[:16]),('580',630,Z[:16]),('630',680,Z[:16])]]
    else:
        cases=[(s,s+65,m+8,Z[:m]) for m,s in
           [(8,250),(8,280),(10,330),(13,400),(16,480),(16,500),(20,590),(20,650),(24,710),(24,760),(32,910),(32,980),(40,1110),(40,1200),(56,1500),(56,1600),(72,1890)]]
    for l,J,N,p in cases:
        p=list(map(F,p))
        if tail(l,N,p,cap):
            print("PASS DIRECT",cap,l,J,N,len(p),p if len(p)<5 else "",flush=True);continue
        test=cover(l,J,N,p,cap)
        if test:print('CELL FAIL',cap,l,J,N,len(p),p if len(p)<5 else '',tuple(map(float,test)),flush=True);continue
        print('PASS' if tail(J,N,p,cap) else 'TAIL FAIL',cap,l,J,N,len(p),p if len(p)<5 else '',flush=True)

if __name__=='__main__':run(F(sys.argv[1]),sys.argv[2])
