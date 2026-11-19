
from osc02 import *
import sys
# Upper bounds for E_w and for L times (E_1,E_P,E_Q), per domain.
# Source CH2 Lemma 9.2 is available throughout [20,29.9].
def bounds(u,h,cap,branch):
    j=1-cap
    f=4/(H*u)
    # max(signed differences) via simple absolute envelopes (cf. exact signed branch)
    zW=HIGH*E(j*u)+LOW*E(u/2)+G*E(u)
    zK=(1+f)*HIGH*E(j*u)+(1+4/(14*u))*LOW*E(u/2)+G*E(u)
    if branch==0: v=F('.791')*E(u/2);p=bp(u)
    elif branch==1: v=u*u*E(u/2)/25;p=powint(u,0)[0]
    else:v=val(u,CH);p=bp(u)
    s=v+(1+1/u)*(zK+p) if branch==1 else v+(1+1/u)*zK+p
    assert 0<=s<u
    return v+zW+p,s/(1-s/u)

def bridge(start,cap,test): # [start,150]; analytic density continuation checked below
    u=F(start)
    for h,idx in ((F('29.9'),0),(F(58),1),(F(150),2)):
        while u<h:
            n=min(u+F(1,64),h)
            w,d=bounds(u,n,cap,idx)
            assert test(w,d,u,n), (u,n,float(w),float(d))
            u=n

def short(E,J,k,tar):
    return E(F(J))*F(J)**k<F(tar)

def unified(cap,sig,cut,C,start=20):
    # From 58 to the cut, scale the CH plateau and decaying terms separately.
    start,cut,C=map(F,(start,cut,C))
    assert start<=58 and cut>=150 and 0<sig<=1-cap
    u=start
    for h,i in ((F('29.9'),0),(F(58),1)):
        while u<h:
            v=min(u+F(1,64),h);w,d=bounds(u,v,cap,i)
            assert max(w,d)<C*EL(sig*v),(cap,sig,C,u)
            u=v
    plateau=F('1.048e-12')/EL(sig*cut)
    w0,d0=bounds(F(58),F(58),cap,2)
    # common scaled numerator (before exp conversion); replace terms by upper differences
    # subtracting a from these certified rational enclosures preserves an upper bound.
    r=d0-F('1.048e-12')
    s=plateau+r/EL(sig*58)
    assert s/(1-(F('1.048e-12')+r)/58)<C
    assert max(pars(cut,cap))*E((1-cap-sig)*cut)<C

if __name__=='__main__':
    for cap, rows in (
      (B0, '150 .01786;175 .01459;185 .01378;190 .01343;200 .01283;225 .01173;250 .01098;300 .01001;400 .00901;800 .00783;1500 .00735;3000 .00707;10000 .00680'),
      (B2, '150 .31245;165 .27423;170 .26463;175 .25615;180 .24861;185 .24186;190 .23578;194 .23134;200 .22528;205 .22071;210 .21653;225 .20583;250 .19246;300 .17531;400 .15765;600 .14306;800 .13661;1000 .13291;1500 .12807;3000 .12298;10000 .11864')):
        for row in rows.split(';'):
            j,c=map(F,row.split())
            if not max(pars(j,cap))<c:
                print('TRIAL FAIL',cap,j,c,[float(a) for a in pars(j,cap)],flush=True)
                continue
            print('TAIL PASS',cap,j,c,flush=True)
    for s,t in [('20','.0357'),('20.3','.0317'),('20.5','.0292'),('21','.0238'),('21.45','.0197'),('21.45','.0196'),('22','.0158'),('24','.011')]:
        try:
            bridge(s,B0,lambda w,d,l,h:max(w,d)*h*h<F(t))
        except AssertionError as exc:
            print('BRIDGE FAIL',s,t,exc,flush=True);continue
        assert max(pars(F(150),B0))*E(F(150,8))*150**2<F(t)
        print('BRIDGE PASS',s,t,flush=True)
    for cap,sig,cut,c in [(B2,F(5,32),'168','.270'),(B2,F(1,8),'168','.00141'),(B0,F(1,8),'186.2','.01370')]:
        unified(cap,sig,cut,c)
        print('UNIFIED PASS',cap,sig,cut,c,flush=True)
    for err in map(F,('1e-12','1e-15','1e-20','1e-30')):
        for cap in (B0,B2):
            l,J=149,800
            assert max(pars(F(J),cap))*E((1-cap)*J)<err
            while J-l>1:
                m=(l+J)//2
                if max(pars(F(m),cap))*E((1-cap)*m)<err:J=m
                else:l=m
            print('ONSET',err,cap,J,flush=True)
    assert EL(F('21.45'))*2100000000>1
    assert F('.00141')<F('.005')/2
