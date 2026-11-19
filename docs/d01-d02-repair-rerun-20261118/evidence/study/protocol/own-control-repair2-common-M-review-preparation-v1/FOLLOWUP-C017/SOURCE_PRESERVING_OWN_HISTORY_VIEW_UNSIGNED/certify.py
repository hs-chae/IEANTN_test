from profiles import *
from mertens import prime_powers,outputs,pi_after_cut,CUT
import json
from pathlib import Path

def verify_instances():
    print('source-independent finite numerical instances')
    def B1(a,b):
        v=I(a).ln(); z=I(b).ln()
        R=I('.137')*v+I('.443')*v.ln()+I('1.588')
        lw=v-(2*PI).ln()
        return (1/(2*PI)+(I('.137')*v+I('.443'))/(a*v*lw))*(z-v)*((z+v)/2-(2*PI).ln())+2*R/a
    assert (2*(I('39.5797647802')+B1(30610046000,H))).r<116
    assert (2*(I('.5922435112')/14+((100*E/(2*PI)).ln())/(2*PI*100)+(I('.4')*I(100).ln()+I('4.1'))/100**2)).r<D('.1')
    assert ell.r<29 and (1/(2*PI)+2/H).r<(I(1)/6).l
    assert (I(8)/3*(ell+I(3).ln())+2*ell.ln()+(I(8)/3+2/ell)/dat(616)[3]).r<97
    assert U(I(140)).l>2*dat(616)[0].r
    assert (I('3.965')/I('18.5')**2).r<D('.012')
    assert (c0*(1+I('1.25')/I('18.5')+I('18.5')*ef(1,I('8.5'))/LN2**2)).r<D('1.08')
    assert (2/LN2+3/(LN2**2)*(E-I(2).power(I('.5')))+I('.75')*(X(I(10))-E)+I('.1')).r<17000
    assert (2/LN2+600/LN2**2).r<1255
    for N,a,cap in ((20,24,'.5'),(20,32,'11'),(30,50,'59')):
        v=I(a)
        r=vintegral(v)-v.exp()/v*horner([factorial(j) for j in range(N+1)],1/v)
        assert 0<r.l and r.r<D(cap)
    for arr in (d,dN):
        assert arr[:4]==[0]*4 and all(x>0 for x in arr[4:31])
    print('verified reciprocal zero sums, R anchors, all projected polynomial coefficients')

def power_coefficients():
    rows=[]
    data=[(170,'.0155','.276'),(180,'.01455','.2583'),(190,'.0138','.2445'),
          (200,'.01318','.2332'),(250,'.01128','.1989'),
          (300,'.01030','.1813'),(400,'.00929','.1633'),
          (600,'.00848','.1488'),(1000,'.00795','.1394')]
    for t,p,q in data:
        u=I(t)
        for cap,k in ((basecap,p),(newcap,q)):
            z=spectral(u,cap)/ef(1-I(cap)/800,u)
            assert z.r<D(k), (t,cap,z,k)
        rows.append((t,p,q))
    print('spectral half-width at these log-onsets:',rows)
    # Lower barriers for selected B0 numerical incumbent: last positive bin.
    _,g,c,a,b=dat(basecap-1)
    A=I(1)/3
    sub=g*2*A/(1+a)+c*2*A/(1+b)
    assert sub.l>D('.0017')
    z=2/(H*I('.008')*ef(I('.125'),I(189)))
    def st(d):
        power=z.power(-d)
        return (1-power)/d+2*power/(1+d)
    assert z.l>1 and (g*st(a)+c*st(b)).l>D('.004')
    assert (I('.004')*ef(I('.125'),I(189))).r<D('1e-12')
    assert (I('.277')*ef(I(1)/32,I(170))).r<D('.0017')
    assert (I('.277')*ef(I(5)/32,I(170))).r<D('1e-12')
    # Pointwise envelope for old asymptotic psi shapes, with conservative
    # weakened common lower comparison, plus genuine table-step minima.
    assert (g*2*(2/(H*I('2.1e-12')))/(1+a)+c*2*(2/(H*I('2.1e-12')))/(1+b)).l > D('.0016')
    assert (I('.0016')*ef(I('.125'),I(168))).l>D('1.05e-12')
    for u,bnd in ((167,'1.03e-12'),(168,'9.5e-13')):
        L=I(u)
        W=min(spectral(L,newcap,h).r for h in ('5e-12','2e-12','1e-12','5e-13','2e-13'))
        assert W<D(bnd), (u,W)
    # The same fixed-window branch has a convex ratio to e^-alpha*u on a compact log slab.
    hh=None
    for h in ('5e-12','2e-12','1e-12','5e-13','2e-13'):
        if all((spectral(I(t),newcap,h)/ef(I(5)/32,I(t))).r<D('.276') for t in (167,170)):
            hh=h;break
    assert hh is not None
    print('D02 power join and earlier strict separation from log 167, using box width',hh)
    for L in (167,170,190,1000):
        u=I(L)
        assert (I('.0017')*ef(I('.125'),u)).r < (ef(1,u.power(I('.5')))).l
    f=Path('source_tables.json')
    if f.exists():
        j=json.loads(f.read_text())
        for t,val,*_ in j['steps']:
            assert (I('.0017')*ef(I('.125'),I(max(t,167)))).r<D(val)
        for t,*args in j['shapes']:
            assert (I('.0017')*ef(I('.125'),I(t))).r<(ef(1,I(t).power(I('.5')))).l
    print('strict-cap separation and source tails checked')

def P(u,c,k,m):
    # Sufficient tail at u, using monotone ratio, k=4,...,29.
    return mtail(I(u),c,k).l > D(m)

def tail_checks():
    for k in range(4,30):
        assert sum((I(j-1)*dNplus[k+1+j]/(I(140)**j) for j in range(2,len(dN)-k-1)),I()).r<dN[k+1]
    print('R full-coefficient real log onsets (sufficient; grid step .1):')
    table=[]
    for k in range(6,30):
        row=[]
        for cap in (basecap,newcap):
            a=1-I(cap)/800
            L0=max(D(141),((k+6)/a).r+1)
            start=max(1700,int((L0*10).to_integral_value(rounding=ROUND_CEILING)))
            stop=20000
            assert P(D(stop)/10,cap,k,dN[k])
            while start<stop:
                m=(start+stop)//2
                if P(D(m)/10,cap,k,dN[k]):stop=m
                else:start=m+1
            assert P(D(stop)/10,cap,k,dN[k])
            row.append(str(D(stop)/10))
        table.append((k,dN[k],*row))
    for r in table: print(*r)
    for u,k,m0 in ((190,6,50),(225,7,790),(250,8,60),(300,9,118000)):
        assert P(u,basecap,k,m0)
        assert P(u,newcap,k,dN[k])
        # Independent failure of that higher coefficient in the selected
        # B0 lower-bound formula even if its box width can vary arbitrarily.
        # Use lower barrier for its uncertainty and exact Li ideal.
        def f(v):return v*ef(1,v)*vintegral(v)
        U=I(u)
        ideal=U/(U-1)*f(U-1)-f(U)**2
        L0=mini(I('1e-12'),I('.004')*ef(I('.125'),U))
        L1=mini(I('1e-12'),I('.004')*ef(I('.125'),U-1))
        los=U/(U-1)*L1+2*f(U)*(L0-I('.988')*ef(I('.5'),U))
        target=sum((I(dN[j])/U**j for j in range(4,k+1)),I())
        assert (ideal-los-target).r<0
        print('fixed log onset, k, B0 certified coefficient, D02 full coefficient:',u,k,m0,dN[k])

def finite_join():
    targets=[(4,D(k)) for k in ('0','.1','.25','.5','.75','.9','1')]+[(5,D(k)) for k in ('8','10','12','14')]
    last=[D('28.1')]*len(targets)
    # For k=4,5 prove tail at 200 using (strictly) full coefficient.
    for k in (4,5): assert P(200,basecap,k,dN[k])
    assert P(200,newcap,4,1) and P(200,newcap,5,14)
    for p in range(1405,10000): # each entire closed slab of width 0.02
        u=I(D(p)/50,D(p+1)/50)
        pen=penalty(u,basecap,True)
        A4=horner(d[4:],1/u)-u**4*pen
        A5=horner(d[5:],1/u)-u**5*pen
        for i,(k,t) in enumerate(targets):
            if (A4 if k==4 else A5).l<=t: last[i]=u.r
    res=[(k,str(t),str(a)) for (k,t),a in zip(targets,last)]
    print('R short-onset whole rays (log scale):',res)
    assert last[0]<29 and last[6]<31.5 and last[-1]<47.5

def mertens_tails():
    a=I(10**7).ln()
    b=I(10**13).ln()
    # The U1 bound divided by exp(-u/2) is decreasing on u>=16.
    pu=(prime_powers(a)[1]/ef(I('.5'),a)).r
    assert pu<D('1.111')
    s=I('.1')+I(20)/H*ef(-I(3)/8,b)+2*ef(I('.5'),a)
    ww=I('.791')+s+I('1.111')
    zz=ww+s/a
    w=ww*a*a*ef(I('.5'),a)
    z=zz*a*a*ef(I('.5'),a)
    assert w.r<D('.165')
    assert (z*(zz*ef(I('.5'),a)/a).exp()).r<D('.166')
    # Sharper signed reciprocal-power tail at the 25-million join:
    t25=I(25000000).ln()
    z25=(I('.791')+s+s/t25)*t25*t25*ef(I('.5'),t25)+prime_powers(t25)[3]*t25**3
    assert (z25*(z25/t25**3).exp()).r<D('.10994')
    print('M sharper coefficient at x=25000000, products and reciprocal sum: .10994')
    # Normalize the finite-li transfer and the tail after its cutoff.
    # Check the psi-to-pi bounds used to obtain the remaining integral after CUT.
    e=I('113.67')+I('.6')/CUT+17000*CUT*ef(I('.5'),CUT)+powterm(CUT)/ef(I('.5'),CUT)
    f=PI/H+120/(H*CUT)*ef(I('.125'),CUT)+12/CUT*ef(1,CUT)
    assert e.r<D(116) and f.r<D('1.06e-12')
    m=I(190)
    a0=I('.125')
    rr=spectral(m,basecap)/ef(a0,m)
    assert (rr+(17000*m*ef(1,m)+powterm(m)+6*spec_simple_prim(m,basecap)/m)/ef(a0,m)).r<D('.014')
    t=pi_after_cut()
    assert (I('1.95')+I('3.9')/b+I('19.5')/b**2).r<D('2.11')
    def pi_C(x):
        z=I('6.33')*x*x*ef(I('.5'),x)+(4*x+2)*x*x*ef(1,x)+CUT*CUT*t
        q=(z+x*x*ef(1,x))/(1-ef(1,x))
        return q*(q/x**3).exp()
    assert pi_C(b).r<D('.002')
    for u,c in ((32,'.0009'),(36,'.00027'),(40,'.00017')):
        assert pi_C(I(u)).r<D(c)
    ww=(I('114.1')+I('1.111'))*CUT*CUT*ef(I('.5'),CUT)+(PI/H+I(20)/H*ef(a0,CUT)+2*ef(1,CUT))*190**2
    zz=ww+spec_simple_prim(CUT,basecap)*190
    assert (zz*(zz/CUT**3).exp()).r<D('.00008')
    for u,c in ((17,'.117'),(18,'.079'),(19,'.053'),(20,'.036'),(21,'.024'),(22,'.016'),(23,'.011'),
                (24,'.007'),(25,'.0045'),(26,'.003'),(27,'.002'),(28,'.002')):
        x=I(u)
        v=(I('.791')+s+prime_powers(x)[1]/ef(I('.5'),x)+s/x)*x*x*ef(I('.5'),x)
        assert (v*(v/x**3).exp()).r<D(c)
        print('M inverse-log whole-ray coefficient, log onset',u,c)
    print('M extra medium-level full ray C:',(32,'.0009'),(36,'.00027'),(40,'.00017'),('log(10^19)','.00008'))
    # Power-tail rows: all absolute product/sum errors <= coefficient times X^(-alpha)/L
    # except logp/p, which has no division by L.
    assert (I('.014')*I(190)**2*ef(I('.125'),I(190))).r<D('.00008')
    print('M power-tail special D02 log onset 167: .277')
    for L,c0s,c1s in ((170,'1','.277'),(190,'.014','.245'),(200,'.0132','.234'),
                      (250,'.0113','.199'),(300,'.0104','.182'),(400,'.0094','.164'),
                      (600,'.0085','.149'),(1000,'.0076','.132'),(2000,'.0071','.125'),(10000,'.00681','.1193')):
        for cap,c0i in ((basecap,c0s),(newcap,c1s)):
            if L==170 and cap==basecap:continue
            u=I(L); a=1-I(cap)/800
            # A tiny allowance absorbs the primitive and all prime-power tails.
            r=mini(spectral(u,cap),continuous_spectral(u,cap))/ef(a,u)
            t=I('1.212')*ef(I('.5')-a,u)+21/I(H)+3*ef(1-a,u)
            b=(r+t)*(I(D(c0i))*ef(a,u)/u).exp()
            assert b.r<D(c0i), (L,cap,b,c0i)
        print('M power-tail coefficient, log onset, B0 and D02:',L,c0s,c1s)

if __name__=='__main__':
    verify_instances()
    power_coefficients()
    tail_checks()
    finite_join()
    mertens_tails()
