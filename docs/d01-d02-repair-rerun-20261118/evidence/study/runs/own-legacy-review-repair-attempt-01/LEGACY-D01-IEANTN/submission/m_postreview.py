"""Exact new Mertens checks. See mertens_postreview.md for derivations."""
from ram_repair import Q, eu, el, q, logb, psi_new, c, AC, A0
from m_repair import u as old_u

p0=Q('.048')
s0=Q(18)
sl=Q('2.25')
def scaled_pi_slab(t):
    return sl*t*t*eu(-t/2)

def pi_constants():
    # Anchor |Delta(18)-dtheta(18)| <= 2.04 sqrt unit, established in ram_repair.py.
    assert Q('.0463')*(1+Q(18,7))<Q('.166')
    r=Q(7,8)-2/s0
    assert Q('3.2e-12')*(1+1/r)<Q('7.5e-12')
    assert (Q('1.000000147')+Q('1.78')*eu(-s0/6))*Q(18,7)<Q('2.81')
    assert (Q('2.04')/s0+
            (Q('.0463')+Q('3.2e-12')*eu(3*s0/8)+4*eu(-s0/2))/s0**2
            +2*eu(-s0/2)/s0)<Q('.114')
    a,b=AC,A0
    k=1+1/a
    sv=eu(-a/2)
    high=eu(3*b/8)
    M=Q('.166')/a+Q('7.5e-12')*high/a+Q('.114')*a*eu(9-a/2)
    Z=k*(Q('.048')+Q('3.3e-12')*high+2*sv)
    qw=(a+2)/(a*(a+1))
    assert Q('.9999')*(2-4*qw)-M-Z-Q('.502')*sv>0
    assert M+Q('2.81')/a+Z+k*(Q('2.0000003')+Q('2.67')*eu(-a/6))<sl
    assert Q('1.95')+Q('3.9')/a+Q('19.5')/a**2+2*a*sv<sl

# S controls L*D1, L*Z_Q and D2 in absolute value after adding Psi.
def correction(L):
    w=1+1/L
    s=eu(-L/2);t=eu(-2*L/3);e=eu(-L)
    Z=Q('4.5e-15') if L>=190 else Q('3.3e-12')
    return (1+Q('.0003')+w*p0)*s+w*(Q('2.67')*t+Z*eu(-L/8)+2*e)+Q('.502')*e

def power_coef(L,fine=False):
    w=1+1/L
    Z=Q('4.5e-15') if L>=190 else Q('3.3e-12')
    U=psi_new(L,fine)+(1+Q('.0003')+w*p0)*eu(-3*L/8)+w*(
        Q('2.67')*eu(-Q(13,24)*L)+Z+2*eu(-Q(7,8)*L))+Q('.502')*eu(-Q(7,8)*L)
    r=U*eu(-L/8)/L
    assert 0<=r<1
    return U/(1-r)

# (coefficient, log onset for analytic join, finite top).
FIN=[
 ('.011','22.9',9000000000),
 ('.004','25.2',90000000000),
 ('.003','25.83',170000000000),
 ('.0024','26.35',290000000000),
]
RAYS=[
 ('.001','28.39'),('.00066','29.35'),('.00050','30.68'),
 ('.00025','32.3'),('.00010','34.4'),('.00005','36'),('.00002','46.1'),
 ('.000005','49.56'),('4.4e-6','49.97'),('8.2e-8','59.95'),
 ('4.3e-8','64.4'),('3.8e-8','74'),
]
POWERS=[
 (185,'.01973'),(187,'.01955'),(190,'.01929'),
 (250,'.01612'),(400,'.01345'),(600,'.01230'),(900,'.01163'),
 (1300,'.01125'),(2000,'.01097'),(3500,'.01076'),(9000,'.01058'),
 (12000,'.01055'),(18000,'.01051'),(100000,'.01047'),
]
def early_d2(t):
    s=eu(-t/2); v=eu(-2*t/3); r=eu(-t/8)
    # Lower sign omits nonnegative bias; upper sign is larger termwise.
    return (Q('1.837401')*s+Q('2.67')*v+Q('3.2e-12')*r+2*eu(-t))
def ray(L,k,d2=False):
    a=AC; b=A0; d=Q(190)
    if L<a:
        if d2:
            assert L**2*early_d2(L)<k
        else:
            v=old_u(L)
            assert 0<=v<1 and L**3*v/(1-v)<k,(L,k,float(L**3*v/(1-v)))
    if L<=b:
        v=scaled_pi_slab(max(L,a))
        assert 0<=v<1 and v/(1-v)<k,(L,k,float(v/(1-v)))
    T=max(L,b)
    if T<=58:
        v=min(q*58**2+Q('113.67')*T**2*eu(-T/2),c*T**4*eu(-T/2))+T*T*correction(T)
        assert 0<=v<1 and v/(1-v)<k,(L,k,float(v/(1-v)))
    T=max(T,Q(58))
    if T<=d:
        # Plateau term grows; every other term decreases after L>=43.7 when scaled by L^2.
        v=q*d*d+T*T*(Q('113.67')*eu(-T/2)+correction(T))
        assert 0<=v<1 and v/(1-v)<k,(L,k,float(v/(1-v)))
    T=max(L,d)
    assert T*T*eu(-T/8)*power_coef(T)<k

def weighted(rows):
    # Rows (real onset interval in log x, decreasing coefficient).
    c=[Q(r[2]) for r in rows]
    assert all(x>y for x,y in zip(c,c[1:]))
    assert all(x[1]<y[0] for x,y in zip(rows,rows[1:]))
    p=[]
    for i,(lo,hi,k) in enumerate(rows):
        p.append(Q(3,2)*c[i]-lo*lo/2*sum((c[h-1]-c[h])/rows[h][1]**2
                                         for h in range(i+1,len(c))))
    return [max(p[i:]) for i in range(len(c))]

def main():
    pi_constants()
    for k,L,top in FIN:
        assert eu(Q(L))<top
        ray(Q(L),Q(k))
        print('finite top and entire analytic join',k,L,top,flush=True)
    for k,L in RAYS:
        ray(Q(L),Q(k))
        print('analytic logarithmic coefficient',k,L,flush=True)
    for k,L in [('.002','27'),('.001','28.5'),('.00066','29.45')]:
        ray(Q(L),Q(k),d2=True)
        print('direct weighted log coefficient',k,L,flush=True)
    for A,k in POWERS:
        v=power_coef(Q(A))
        print('common power coefficient at',A,float(v),flush=True)
        assert v<Q(k),(A,k)
    for A,k in [(100000,'.010456'),(200000,'.010451'),(500000,'.010447'),
                (1000000,'.010446'),(5000000,'.0104448')]:
        v=power_coef(Q(A),True)
        assert v<Q(k)
        print('fine mesh power coefficient at',A,float(v),flush=True)
    R=[(3909275995,'.011'),(4760000000,'.010'),(8500000000,'.009'),
       (12000000000,'.008'),(16000000000,'.007'),(22000000000,'.006'),
       (30000000000,'.005'),(38622120594,'.004'),(103268901665,'.003'),
       (149179986112,'.0024'),('27','.00205')]
    R += [(a,k) for k,a in RAYS]
    rows=[(*((Q(a),Q(a)) if isinstance(a,str) else logb(Q(a))),k) for a,k in R]
    z=['.01212','.01104','.00983','.00872','.00763','.00656','.00549',
       '.00445','.00332','.00269','.00224','.00111','.000734','.000550',
       '.000278','.000115','.000061','.000022','.00000572',
       '5.09e-6','1.05e-7','6.27e-8','5.71e-8']
    assert len(z)==len(R)
    for (a,k),U,t in zip(R,weighted(rows),z):
        assert U<Q(t)
        print('weighted step whole-ray bound',a,t,float(U),flush=True)
if __name__=='__main__':
    main()
