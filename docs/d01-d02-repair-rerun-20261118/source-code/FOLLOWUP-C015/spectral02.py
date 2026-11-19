"""D02 cap and paired same-method B0 comparator."""
from density_repair import *

BETA=F(27,32)
GAP=1-BETA
BETA0=F(7,8)
GAP0=1-BETA0

def major_fks(s):
    if s>=F(4,5):return major(s)
    assert s>=F(3,4)
    a=1-F(8,3)*(1-s);q=5-2*s; h=I(H).log()
    t=I(1)/a; z=t
    for j in range(4):
        t=t*(q-j)/(a*h);z+=t
    return 2*(I("7.7979")*power(h,q)*ex(-a*h)*z+I("4.1006")*(h*h+2*h+2)/H)

def dusart_mass(s):
    # Dusart PDF p. 5, Theorem 2.3, with refined log(1+y) integration.
    p=F(8,3)*(1-s);a=1-p;q=5-2*s
    h=I(H).log()
    t=I(1)/a; z=t
    for j in range(4):
        t=t*(q-j)/(a*h);z+=t
    y=I('4.9')*power(I(3),p)*power(h,q)*ex(-a*h)
    assert low(a,q/h)
    assert 6<2*q<=7
    t=I(1)/(2*a); z2=t
    for j in range(6):
        t=t*(2*q-j)/(2*a*h);z2+=t
    return 2*(y*z - y*y*z2/(2*(1+y))+I('51.5')*(h*h+2*h+2)/H)

def major_ext(s):
    a,b=major_fks(s),dusart_mass(s)
    return I.raw(min(a.lo,b.lo),min(a.hi,b.hi))

def make_layers(beta, offset=F(4,5), step=F(1,1000), fine=F(1,100000)):
    assert F(3,4)<=offset<beta<=BETA0
    points=[offset]
    # Include all intermediate thousandths, and resolve the final 0.001 more finely.
    for j in range(int(offset/step)+1,int(beta/step)+1):
        if j*step<beta:points.append(j*step)
    points.extend(j*fine for j in range(int((beta-step)/fine)+1,int(beta/fine)+1)
                  if points[0]<j*fine<beta)
    points=sorted(set(points))
    masses=[]
    for s in points:
        v=major_ext(s).hi
        masses.append(min(v,masses[-1]) if masses else v)
    return [(I.raw(a-b,a-b),1-s,0) for a,b,s
            in zip(masses,masses[1:]+[0],points[1:]+[beta]) if a>b]

# A common grid through BETA, with a common envelope below it.
def paired_layers(offset=F(4,5), step=F(1,1000), fine=F(1,100000)):
    cut=make_layers(BETA,offset,step,fine)
    grid=sorted(set([offset]+[1-g for _,g,_ in cut]+[1-g for _,g,_ in make_layers(BETA0,offset,step,fine)]))
    assert grid[-1]==BETA0 and BETA in grid
    masses=[]
    for s in grid[:-1]:
        v=major_ext(s).hi
        masses.append(min(v,masses[-1]) if masses else v)
    def modes(stop):
        i=grid.index(stop)
        return [(I.raw(a-b,a-b),1-s,0) for a,b,s in
                zip(masses[:i],masses[1:i]+[0],grid[1:i+1]) if a>b]
    return modes(BETA),modes(BETA0)

L2,L0=paired_layers()
def modes(beta=BETA,h=F(1,5),admissible=100):
    # T=exp(hL); V=exp(hL+1).  h>=1/6 and h<=1/4 here.
    assert F(1,6)<=h<=F(1,4) and admissible>=86
    a=I(admissible); T=ex(h*a); V=ex(h*a+1)
    assert low(T,a) and low(T,51) and low((ex(a/2)-2)/5,T)
    assert low(V,I('2.45')*T) and low(V,10**6)
    # For simplicity use the established upper .16 v^2 for v>=26,
    # as in density_repair.py.
    # When h*a+1<26 use monotonicity in V and the bound at v=26.
    w=max(h+F(1,admissible),F(26,admissible))
    return [(I(F('.16')*w*w),F(1,5),2),(I('2.091'),h,1)]+(L2 if beta==BETA else L0)

def evaluate(L, ms, scale=0):
    return sum(c*L**k*ex(-(g-scale)*L) for c,g,k in ms)

def critical_sum(U,V):
    u=I(U).log(); v=I(V).log(); p=(2*PI).log()
    c=1/(2*PI)+(I('.137')*u+I('.443'))/(U*u*(u-p))
    r=I('.137')*u+I('.443')*u.log()+I('1.588')
    return 2*c*(v-u)*((v+u)/2-p)+4*r/U

# Above H, FKS (2.1) is at most .16 (v^2-log(H)^2)+4R(H)/H
# when v >= log H. On L>=a>= log(H)/h:
# v=h L+1 = h (L-a)+(h a+1), retaining the smaller constant.
def refined_modes(beta,h,a,offset,ls):
    modes(beta,h,a)   # admissibility and V>T*
    u=I(H).log(); p=(2*PI).log()
    c=1/(2*PI)+(I('.137')*u+I('.443'))/(H*u*(u-p))
    r=I('.137')*u+I('.443')*u.log()+I('1.588')
    assert low(I('.16'),c)
    v=I(h*a+1)
    assert low(v,u)
    w=2*c*(v-u)*((v+u)/2-p)+4*r/H
    w1=2*c*h*(v-p)
    w2=c*h*h
    assert low(I(128),2*I('39.5797647802')+critical_sum(30610046000,H))
    # Compact representation: (coefficient, decay, degree, polynomial origin).
    return [(w,1-offset,0,a),(w1,1-offset,1,a),(w2,1-offset,2,a),
            (I(128),F(1,2),0,0),(I('2.091'),h,1,0)]+[(c,g,k,0) for c,g,k in ls]

offsets=[F(j,1000) for j in (775,780,785,790,795,800)]
# Match the finest original table cap in both calculations; use a denser
# grid just before the cap in the later tail tests.
RLS={off:paired_layers(off,F(1,1000),F(1,100000)) for off in offsets}
HP=[(F(1,4),112),(F(1,5),140),(F(9,50),156),(F(1,6),168),
    (F(21,100),134),(F(19,100),148),(F(17,100),165),
    (F(4,25)+F(1,150),168)]
HP=sorted(set(HP))
RM={(h,a,o,z):refined_modes((BETA,BETA0)[z],h,a,o,RLS[o][z])
    for h,a in HP for o in offsets for z in (0,1)}

# Extra grid splits just below each cap and symmetry-aware low mass.
SP_OFF=[F(j,1000) for j in (765,770,775,780,785,790,795,800)]
SP_LS={o:paired_layers(o,F(1,1000),F(1,100000)) for o in SP_OFF}
SP_HP=[(F(1,4),144),(F('.24'),144),(F('.23'),146),
       (F('.225'),148),(F('.22'),150),(F('.21'),156),(F('.2'),160),
       (F(1,6),188)]
def sym_modes(beta,h,a,o,ls):
    rr=refined_modes(beta,h,a,o,ls)
    # First three modes comprise the polynomial bound S(V) above H.
    # At beta>1/2 at most half the total weight, by reflection.
    D=sum(c for c,g,k in ls)
    base=rr[0][0]/2-D
    if base.lo<0:return None
    return ([(base,1-o,0,a)]+[(c/2,g,k,b) for c,g,k,b in rr[1:3]]
        +[(c/2,F(1,2),k,b) for c,g,k,b in rr[:3]]+rr[3:])
SM={(h,a,o,z):q for h,a in SP_HP for o in SP_OFF for z in (0,1)
    for q in [sym_modes((BETA,BETA0)[z],h,a,o,SP_LS[o][z])] if q}
RM.update(SM)
def eval4(L,ms,scale=0):
    return sum(c*(L-a)**k*ex(-(g-scale)*L) for c,g,k,a in ms)

# Keep only a handful of fast valid shapes for practical finite certificates.
FAST=[(F(1,4),112,F('.775')),(F(1,5),140,F('.8'))]+[
    key for key in [(F(1,4),144,F('.775')),(F(1,4),144,F('.78')),(F('.23'),146,F('.775')),
                    (F('.225'),148,F('.78')),(F('.22'),150,F('.78'))]
    if (*key,0) in SM and (*key,1) in SM]
HMOD=tuple((h,a,modes(BETA,h,a),modes(BETA0,h,a)) for h,a in
          [(F(1,4),86),(F(1,5),86),(F(1,4),104),(F(1,5),130)])

def spectral(L,beta=BETA,scale=0,fast=True):
    assert L.lo>=86*S
    z=int(beta==BETA0)
    candidates=[evaluate(L,n if z else m,scale) for h,a,m,n in HMOD if L.lo>=a*S]
    candidates += [eval4(L,m,scale) for h,a,o in FAST if L.lo>=a*S
                   for m in [RM[h,a,o,z]]]
    if not fast:
        candidates += [eval4(L,m,scale) for (h,a,o,j),m in RM.items() if j==z and L.lo>=a*S]
    if z==0 and L.lo>=200*S:candidates.append(L**2*ex(-(GAP-scale)*L)/64)
    from mertens import mn
    return mn(*candidates)

def decreasing_scaled(ms,B,g):
    groups={}
    for c,r,k,a in ms:
        if B<a or r<g:return False
        p=groups.setdefault((r,a),[I(0),I(0),I(0)])
        for j in range(k+1):p[j]+=c*comb(k,j)*(B-a)**(k-j)
    return all((p[j+1]*(j+1)-(r-g)*p[j]).hi<=0
               for (r,a),p in groups.items() for j in (0,1))
def scaled_ms(B,z=0):
    g=GAP0 if z else GAP
    for h,a,m,n in HMOD:
        v=n if z else m
        p=[(c,r,k,0) for c,r,k in v]
        if B>=a and decreasing_scaled(p,B,g):yield p,('basic',h,a)
    for (h,a,o,j),v in RM.items():
        if z==j and B>=a and decreasing_scaled(v,B,g):yield v,('refined',h,a,o)
if __name__=='__main__':
    boot_height()
    from mertens import thetaCH
    for l in [86,100,130,150,160,165,170,172,175,180,185,190,195,200,210,225,250,300,350,420,600,1000,2000,10000,100000,1000000]:
        L=I(l)
        opts=[(eval4(L,m,GAP).hi,who) for m,who in scaled_ms(l)]
        m=min(opts,default=(0,None))
        print(l,spectral(L,BETA,GAP,False),spectral(L,BETA0,GAP0,False),
              (m[0]/S,m[1]),flush=True)
    print('top masses',L2[-1],L0[-1])
