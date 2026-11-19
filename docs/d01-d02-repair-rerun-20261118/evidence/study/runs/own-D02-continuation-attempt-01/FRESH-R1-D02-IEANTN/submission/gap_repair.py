"""Closed-cell and monotone-tail verification for gap_repair.md."""
from verify import I,D,pi,c,dense,C,fac,EC,E as oldE,part,g,factpoly,vpoly
from spectral_repair import E,J,lt
B=lambda L: (3*E(7)+1)*L*E(-L)
def Wprefix(L):
    return B(L)+(I('.1')*(1+I(14)/3)*E(-L/2)
                 +I('4e-12')*(1+I(56)/33)*E(-L/8)+2*E(-L))/L
# Use J residual only once at the local boundary and 2/7 in B.
pp2=I('1.000000147'); pp3=I('1.78')
def Vprime(L):
    return pp2*E(-L/2)*(1+I(14)/(3*L))+pp3*E(-2*L/3)*(1+21/L)
def Uprime(L):
    return I('.9999')*E(-L/2)*(1+2/L*(1-E((7-L)/2)))
def eru(L,upper):
    opts=[EC(L)]
    if L.a>=34 and L.b<=58:
        w=2*(L/(pi*E(1))).log()
        opts.append(((L-w)**2-4)*E(-L/2)/(8*pi)+Wprefix(L)+(-Uprime(L) if upper else Vprime(L)))
    if L.a>=100:
        opts.append(dense(L)+Wprefix(L)+(-Uprime(L) if upper else Vprime(L)))
    error=oldE(L,True,upper).b
    out=min(error,min(o.b for o in opts)+(13*L*E(-L)+3*fac(19)/L**19).b if upper else min(o.b for o in opts))
    return I(0,out)
def proof(L,pv=False):
    u,v=eru(L,True),eru(L-1,False)
    if pv:
        assert E(L).b<=D('1.2e17')
        u=I(0,min(u.b,(16*L*E(-L)+3*fac(19)/L**19).b))
    return I(g(L.b).a)-L**4*(L/(L-1)*v+2*factpoly(L)*u+u*u)
lt(E('39.326'),'1.2e17')
lt(E(7)/49*J(7)+I(2)/7,1)
def adapt(lo,hi,target,pv):
    from decimal import getcontext
    getcontext().prec=45
    a,b=D(lo),D(hi); count=0; low=D('Infinity')
    stack=[(a,b)]
    while stack:
        a,b=stack.pop()
        L=I(a,b)
        val=proof(L,pv)-target
        if val.a>0:
            count+=1
            low=min(low,val.a)
            continue
        assert b-a>D('1e-7'),(L,val)
        mid=(a+b)/2   # shared endpoint, no uncovered interval even if rounded
        stack.extend([(mid,b),(a,mid)])
    print('closed adaptive join',lo,hi,target,pv,count,low,flush=True)

def deep_tail(n,st,cert=True):
    from math import comb
    m=n+8; b=2*(m+2)
    L=I(st);z=L-1
    assert z.a>=max(100,b) and z.a>8*(m+1)
    def coeff(j):
        return (sum(fac(i)*comb(j,i) for i in range(min(j,m)+1))
            -sum(fac(i)*fac(j-i) for i in range(max(0,j-m),min(j,m)+1)))
    A=[coeff(j) for j in range(2*m+1)]
    if cert:
        assert A[:4]==[0]*4 and all(x>0 for x in A[4:m+1])
        lt(sum(max(0,-A[j])/L**(j-m) for j in range(m+1,2*m+1)),A[m])
    def em(t):
        return dense(t)+Wprefix(t)+Vprime(t)+3*t*E(b-t)+2*fac(m+1)/t**(m+1)
    ea,eb=em(L),em(z)
    S=sum(fac(j)/L**j for j in range(m+1))
    loss=L**(m-1)*(L/z*eb+2*S*ea+ea**2)
    rhs=sum(A[j]*L**(m-1-j) for j in range(n+1,m))
    if cert:
        lt(loss,rhs)
        print('refined order tail',n,st,'truncation',m,'loss/rhs',loss/rhs,flush=True)
    return loss.b<rhs.a

if __name__=='__main__':
    import sys
    if '--explore' in sys.argv:
        for n,guess in [(4,161),(5,190),(6,221),(8,289),(10,359),(12,430),(14,502),(16,575),(17,614),(20,722),(24,868),(32,1161),(48,1748),(64,2336)]:
            st=guess
            while not deep_tail(n,st,False):st+=1
            while deep_tail(n,st-1,False):st-=1
            print(n,st,flush=True)
    else:
        for row in [
            ('36.54','36.745','.002',True),
            ('36.745','36.91','.1',True),
            ('36.91','39.326','.164',True),
            ('36.98','37.5','.2',True),
            ('37.5','39.326','.4',True),
            ('39.1','39.326','.84',True),
            ('39.3','39.326','.88',True),
            ('39.326','39.94','.164',False),
            ('39.94','42.482','.4',False),
            ('40','42.482','.425',False),
            ('42.482','60','1',False),
            ('43','60','1.06',False),
            ('45','77','1.209',False),
            ('46','67','1.246',False),
            ('47','61','1.27',False),
            ('48','55','1.30',False),
            ('49','52','1.32',False),
            ('59','80','1.20',False),
            ('80','100','1.15',False),
        ]:
            a,b,q,pv=row
            adapt(a,b,I(q),pv)
        tails=[(4, '160.54'), (5, '189.18'), (6, '220.73'), (8, '288.15'), (10, '358.34'), (12, '429.78'), (14, '501.87'), (16, '574.34'), (17, '610.67'), (20, '719.91'), (24, '865.96'), (32, '1158.82'), (48, '1745.95'), (64, '2333.94')]
        for n,st in tails: deep_tail(n,st)
