from profiles import *

eta_rows=[
(1,0,'1'),(2,1,'1.2323'),(908994923,1,'.001'),
(2,2,'3.965'),(3594641,2,'.2'),(122568683,2,'.05'),
(7713133853,2,'.01'),(2,3,'20.83'),(32321,3,'10'),
(89967803,3,'1'),(158822621,3,'.78'),(767135587,3,'.5'),
(2,4,'151.3')]
eta_rows=[(I(x).ln(),k,I(eta)) for x,k,eta in eta_rows]
def theta_lower(v):
    return maxi(0,1-mini(*[eta/v**k for a,k,eta in eta_rows if v.l>=a.r or k==0]))

def squaretail(v,k,weighted=True):
    Y=ef(k-1,v)
    t=theta_lower(v)
    if weighted:
        return maxi(0,t*k/(k-1)-c0)*Y,(c0*k/(k-1)-t)*Y
    # integral 1/k*int exp(-(k-1)w)/w dw
    d=1/((k-1)*v)
    mainlo=maxi(0,d*(1-d))/k
    mainhi=mini(d,d*(1-d+2*d*d))/k
    lo=maxi(0,t*mainlo+(t-c0)/(k*v))*Y
    hi=(c0*mainhi+(c0-t)/(k*v))*Y
    return lo,hi

def prime_powers(u):
    u=I(u)
    # k>=4, split p<=x^(1/4) and p>x^(1/4)
    v=u/4
    _,f4=squaretail(v,4)
    r4=c0*(ef(I('.75'),u)+2*(1+maxi(0,v-LN2))*ef(1,u))+f4/(1-ef(1,v))
    a,b=squaretail(u/2,2)
    c,d=squaretail(u/3,3)
    lo1,hi1=a+c,b+d+r4
    a,b=squaretail(u/2,2,False)
    c,d=squaretail(u/3,3,False)
    lo0,hi0=a+c,b+d+r4/u
    a,b=squaretail(u,2,False)
    return lo1,hi1,lo0,hi0,maxi(0,lo0-b/(1-ef(1,u))),hi0-a

def outputs(u,cap):
    u=I(u)
    w=werr(u,cap)
    S=primitive(u,cap)
    wneg=w
    if u.l>=I(10000).ln().r and u.r<=I(10**13).ln().l:
        wneg=mini(w,I('.751')*ef(I('.5'),u)+S)
    z=w/u+S/u**2
    zn=wneg/u+S/u**2
    if u.l>I(10**9).ln().r:
        for adaptive in (False,True):
            T=evalT(u,adaptive)
            if u.l<=T.ln().r:continue
            Q=ch(u,True,adaptive)/u+3*ef(99,u)/u
            z=mini(z,Q)
            zn=mini(zn,Q+PI**2/(3*T*T*u*u))
    l1,h1,l0,h0,ld,hd=prime_powers(u)
    A=I((ld-zn).l,(hd+z).r)
    a,b=I(A.l),I(A.r)
    P=maxi(-expm1(-b),expm1(-a))
    Q=maxi(-expm1(a),expm1(b))
    return P,Q,maxi(h0+z,zn-l0),maxi(h1+w,wneg-l1)

def theta_transfers(u):
    u=I(u)
    bs=[]; bws=[]
    for a,k,eta in eta_rows:
        if k<2 or a.r>u.l:continue
        bs.append(eta/(k*u**k)+eta*(1+I(1)/(k+1))/u**(k+1))
        bws.append(eta/((k-1)*u**(k-1))+eta/u**k)
    if not bs: return None
    r=mini(*bs); wr=mini(*bws)
    aa,bb=squaretail(u,2,False)
    bb/=1-ef(1,u)
    return maxi(-expm1(-r+aa),expm1(r+bb)),maxi(-expm1(-r-bb),expm1(r-aa)),r,wr


CUT=I(10**19).ln()
def pi_after_cut():
    return I('1.06e-12')*(190-CUT)+232*ef(I('.5'),CUT)+I('.112')*ef(I('.125'),I(190))

def pi_transfers(u):
    """Extra finite-log branch from the Buth(e) estimate in PT PDF p.8."""
    u=I(u)
    if u.r>CUT.l or u.l<I(10**13).ln().r: return None
    B=(I('1.95')+I('3.9')/u+I('19.5')/u**2)*ef(I('.5'),u)+2*u*ef(1,u)
    T=pi_after_cut()
    it=I('4.22')*(ef(I('.5'),u)-ef(I('.5'),CUT))+2*((u+1)*ef(1,u)-(CUT+1)*ef(1,CUT))
    R=B/u+it/u+T/CUT
    W=B+it+T
    D=(R+ef(1,u)/u)/(1-ef(1,u))
    return expm1(D),expm1(D),R,W

def combined(u,cap):
    u=I(u)
    vals=list(outputs(u,cap))
    branches=[theta_transfers(u),pi_transfers(u)]
    direct=[None]*4
    if u.l>=I(2278382).ln().r: direct[0]=direct[1]=I('.2')/u**3
    if u.l>=I(2278383).ln().r: direct[2]=I('.2')/u**3
    if u.l>=I(912560).ln().r: direct[3]=I('.3')/u**2
    branches+=[direct]
    for branch in branches:
        if branch:
            vals=[mini(a,b) if b is not None else a for a,b in zip(vals,branch)]
    return tuple(vals)

if __name__=='__main__':
    for t in ('16','16.11809565095832','28','30','40','60','100','150','165','170','180','190','200','250','300','400','600','1000'):
        u=I(t)
        k=(3,3,3,2)
        print(t, 'U1 coefficient',float((prime_powers(u)[1]/ef(I('.5'),u)).r))
        for cap in (basecap,newcap):
            rows=outputs(u,cap)
            print(cap,*[float((x*u**ki).r) for x,ki in zip(rows,k)])
