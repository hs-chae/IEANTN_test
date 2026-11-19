"""Finer high-zero weights with local, upward-rounded FKS Table 8 constants."""
from certificate import *
ROW=[('.75','.80','7.798','4.101'),('.80','.81','8.162','3.693'),
     ('.81','.82','8.538','3.613'),('.82','.83','8.927','3.533'),
     ('.83','.84','9.330','3.453'),('.84','.85','9.747','3.373'),
     ('.85','.86','10.176','3.293'),('.86','.87','10.620','3.213'),
     ('.87','.88','11.076','3.133')]
row=[tuple(map(F,r)) for r in ROW]
@lru_cache(None)
def Z_loc(s):
    h=log(H)
    candidates=[]
    for a,b,c,f in row:
        if a<=s:
            u=min(s,b)
            q=5-2*u;d=(8*u-5)/3
            candidates.append(2*c*exp(q*log(h)-d*h)/(d-q/h)+2*f*(h*h+2*h+2)/H)
    return I(min(j.l for j in candidates),min(j.h for j in candidates),True)
@lru_cache(None)
def rt(b):
    pts=sorted({F(3,4)+F(i,4000) for i in range(501) if F(3,4)+F(i,4000)<b}
        | {b} | ({b1} if b==b0 else set()))
    z=[Z_loc(s) for s in pts[:-1]]+[I(0)]
    c=[z[j]-z[j+1] for j in range(len(pts)-1)]
    assert all(t.h>=0 for t in c)
    return ts(b)[:4]+tuple((I(max(0,t.l),t.h,True),0,1-pts[j+1]) for j,t in enumerate(c))
@lru_cache(None)
def rp(b,v):
    a=F(61);t=rt(b)
    return transfer(t,a,v,CH(a)+value(t,a)/a)
def pc(b,v):
    d=1-b
    return value(tuple((c,k,r-d) for c,k,r in rt(b)),v)
def mc(b,v):
    d=1-b
    mass=(4+6*(v*v+4*v+8))*e(-(F(1,2)-d)*v)+I(F(400,H))
    powers=4*e(-(F(1,2)-d)*v)+10*e(-(F(2,3)-d)*v)
    z=pc(b,v)+(1+1/v)*mass+powers
    return z/(1-z*e(-d*v)/v)
def main():
    assert I(F('.0039')).lt(F('.0107')*(1-e(-F(180)*F('.003'))))
    for b in (b0,b1):
        assert I(F('.0107')).lt(rt(b)[-1][0])
        margins=('.0227','.0162','.0136') if b==b0 else ('.321','.227','.191')
        for v,c in zip((160,250,400),margins):
            assert mc(b,F(v)).lt(F(c))
        print('refined Mertens constants',str(b),[mc(b,F(v)).pt() for v in (160,250,400)],flush=True)
        rr=[]
        for k in (8,10,12,16,20,24):
            for n in range(160,550):
                v=F(n)
                if (mc(b,v)*v*v*e(-(1-b)*v)).lt(F(1,10**k)):
                    rr.append(n); break
        assert rr==([201,240,278,355,431,507] if b==b0 else [177,207,238,299,360,421])
        print('refined Mertens onsets',str(b),rr,flush=True)
        a0=[192,223,256,290,325,360,396,432,468,504,540,576,613,649,685,722] if b==b0 else [180,190,214,240,266,292,318,345,372,399,426,453,480,507,535,562]
        res=[]
        for j,n0 in enumerate(a0,1):
            for n in range(max(160,n0-10),n0+1):
                v=F(n)
                assert (j+6)/v+1/(v-1)<F(1,8)
                if (v**(j+6)*(rp(b,v-1)+F('2.07')*rp(b,v))).lt(slack(j,v)):
                    res.append(n);break
        assert res==([190,222,255,289,324,359,395,431,467,503,539,575,612,648,684,721] if b==b0 else [170,188,212,238,264,290,316,343,370,397,424,451,478,506,533,560])
        print('refined Ramanujan onsets',str(b),res,flush=True)
        if b==b0:
            bad=[]
            for j in range(170*8,res[0]*8):
                l,r=F(j,8),F(j+1,8)
                upper=r**7*(pick([CH(l-1),rp(b,l-1)])+F('2.07')*pick([CH(l),rp(b,l)]))
                if not upper.lt(slack(1,l,r)):bad.append(l)
            assert not bad
            print('F1 B0 remaining join cells:',str(bad[:1]),str(bad[-1:]),flush=True)
if __name__=='__main__':main()
