"""Ramanujan whole-ray certificates; all decisions by directed intervals."""
import ram
from smoothed import *
from math import factorial as fac, comb
a=I('1.048e-12')
@lru_cache(None)
def psirad(v,b):
    t=I(v)
    return min([combined(t,b)]+[sm(t,b,h) for h in ('5e-13','8e-13','1.05e-12','1.4e-12')],key=lambda x:x.b)
def divpow(n,t,k):
    if k<0: return I(n)*t**(-k)
    n=I(n)
    # avoid first rounding the tiny reciprocal power and then amplifying it
    for _ in range(k): n=n/t
    return n
def point(t,b,up):
    t=I(t)
    es=exp(-t/2)
    pp=I('-.9999' if up else '1.4262')
    opts=[ram.AT[j]+(ram.BT[j]+pp)*es for j in range(len(ram.TS))]
    opts+=[a+(I('113.67')+pp)*es]
    if t.a>=I(145).b and t.a<I(330).a:
        # Each h is fixed for the entire cell.
        opts+=[psirad(F(t.a*32//I(1).a,32),b)+pp*es]
    if t.a>=I(330).b and t.a<I(920).a:
        U=I(330)
        cc=minI(C(U,b),oldC(U,b))
        opts+=[cc*exp(-(1-b)*t)+pp*es]
    return min(opts,key=lambda x:x.b)
def carry(t,b):
    t=I(t); k=1-b; es=exp(-t/2)
    # bound integrated psi with J_b; theta correction with 8/3.
    # The prefix and left boundary total is <12000 in unnormalized units.
    return ((I('.0462')*(1+I(F(8,3)))+I('1.4262')*I(F(8,3)))*es
             + I('3.1e-12')*(1+1/(1-k-F(1,8)))*exp(-k*t)
             + I('1.84')*exp(-t))/t +12000*t*exp(-t)
def rad(t,b,up):
    r=point(t,b,up)+carry(t,b)
    return minI(r, ram.which(t,t,up,b))

class Model:
    def __init__(self,N,v):
        self.N=N; self.v=v; self.C=4*fac(N+1)
        self.dd=[sum(fac(j)*comb(n,j) for j in range(min(N,n)+1))-
                 sum(fac(j)*fac(n-j) for j in range(max(0,n-N),min(N,n)+1))
                 for n in range(2*N+1)]
        assert self.dd[:N+1]==ram.dd[:min(N,14)+1]+self.dd[15:N+1]
    def P(self,t): return sum(divpow(fac(j),t,j) for j in range(self.N+1))
    def anchor(self):
        t=I(self.v)
        assert (t*(1-F(self.N+2,self.v))*4).a>=t.b  # derivative correction
        m=4*self.v
        q=F(2*self.v**(m+1),(m+1)*fac(m+1))
        assert self.v*2<m+2
        li=log(t/ram.LN2); a=b=I(1)
        for j in range(1,m+1):
            a=a*t/j; b=b*ram.LN2/j
            li+=(a-b)/j
        li+=rng(0,q)
        v=t*exp(-t)*li
        less(self.P(t),v)
        less(v,self.P(t)+divpow(self.C,t,self.N+1))
    def loss(self,t,u,l):
        return (2*self.P(t)+divpow(self.C,t,self.N+1)+u)*(divpow(self.C,t,self.N-3)+t**4*u)+t**5/(t-1)*l
    def gap(self,t,b,k):
        return sum(divpow(self.dd[n],t,n-k) for n in range(k,2*self.N+1))-t**(k-4)*self.loss(t,rad(t,b,True),rad(t-1,b,False))
    def monotail(self,u,b,k,w):
        t=I(u); w=F(w); d=self.dd
        j=k if w<d[k] else k+1
        assert w<=d[k] and j<self.N+1 and u-1>=8*(j+2) and u>=300
        # Use inherited plateau radius, sufficient at the far right.
        bb=1-b
        z=I(299)
        pref=exp(bb*z)*ram.rd(z,b)
        A=I(2)*self.P(t)+divpow(self.C,t,self.N+1)+pref*exp(-bb*t)
        l=A*divpow(self.C,t,self.N+1-j)+ (A*pref)*exp(j*log(t)-bb*t)+(pref*t/(t-1))*exp(j*log(t)-bb*(t-1))
        less(l+sum(divpow(-d[n],t,n-j) for n in range(j+1,2*self.N+1) if d[n]<0),d[j]-(w if j==k else 0))
    def check(self,l,u,b,k,w,step):
        l,u,w,step=map(F,(l,u,w,step))
        assert l-1>=self.v
        self.monotail(u,b,k,w)
        count=0
        def box(a,c):
            nonlocal count
            f=self.gap(rng(a,c),b,k)-w
            if f.a>0:
                count+=1
                return
            if c-a<=F(1,1024):
                raise ValueError('not certified', a,c,b,k,w,approx(f))
            z=(a+c)/2
            box(a,z); box(z,c)
        a=l
        while a<u:
            c=min(u,a+step)
            box(a,c)
            a=c
        print('certified',str(b),str(l),str(u),k,str(w),count,flush=True)
def verify():
    ram.verify_common()
    less(log(I(H)/(2*PI))**2/I('6.28')+I('1.8642'),'117.02')
    less(I('1.048e-12')*10**5+(I('113.67')+I('1.4262'))*100+3+
         I('1.84')/16+exp(I(16))/16**2*(I('.0462')*exp(I(-8))+I('3.1e-12')*exp(I(-2))+I('1.84')*exp(I(-16))),12000)

if __name__=='__main__':
    verify()
    M=Model(14,24); M.anchor()
    HH=Model(27,55); HH.anchor()
    import sys
    if sys.argv[1]=='diagnose':
        for b in [Q,J]:
            for t,k in [(36,4),(36.5,4),(36.8,4),(37,4),(38,4),(40,4),(45,5),(47,6),(48,6),(49,6),(50,6),(166,6),(167,6),(168,6),(169,6),(170,6),(175,6),(180,6),(185,6),(186,6),(187,7),(189,7),(190,7),(205,7),(210,7),(235,8),(260,9)]:
                print(b,t,k,approx(M.gap(I(str(t)),b,k))[0],flush=True)
            for k in range(13,25):
                t=(430+(k-13)*41 if b==Q else 365+(k-13)*32)
                print('high',b,k,t,approx(HH.gap(I(t),b,k))[0]/HH.dd[k],HH.dd[k],flush=True)


    elif sys.argv[1] in ('base','new','high'):
        cases={
          'base':[(36.61,4,.02),(36.70,4,.06),(36.88,4,.14),(37,4,.20),(38,4,.56),
                  (40.01,4,1),(45,5,10.20),(47.08,5,14),(47.55,6,20.5),
                  (50,6,23),(170,6,23),(200,6,115),(217,6,145)],
          'new':[(48,6,48),(48.75,6,76),(49,6,82),(50,6,86),
                 (172,6,108),(176,6,126),(185.4,6,145),
                 (189,7,535),(209.9,7,1412),(235.1,8,13985),
                 (262,9,145450),(292,10,1610021),(319,11,19063832),
                 (348,12,241691425),(378,13,3277187246)]}
        group=sys.argv[1]
        if group=='high':
            for k,l0,l1 in [(14,530,406),(15,565,445),(16,606,476),(17,648,511),
                            (18,682,536),(19,718,567),(20,755,596),(21,794,626),
                            (22,832,655),(23,870,685),(24,908,715),(25,950,748),(26,1010,778)]:
                for b,l in [(Q,l0),(J,l1)]:
                    try:
                        if b==Q and k==26:
                            HH.monotail(l,b,k,HH.dd[k])
                            print('certified monotone',str(b),l,k,HH.dd[k],flush=True)
                        else: HH.check(l,l+52,b,k,HH.dd[k],1)
                    except (AssertionError,ValueError) as e: print('trial rejected:',k,l,str(b),str(e),flush=True)
        else:
            for l,k,w in cases[group]:
                try: M.check(str(l),max(300,int(l)+80),Q if group=='base' else J,k,str(w),2)
                except (AssertionError,ValueError) as e: print('trial rejected:',l,k,w,str(e),flush=True)
