"""Mertens repair certificates; all tests cover closed intervals or monotone tails."""
from repair_check import QB,QD,dnew as df,chtrial
from check import I,D,pi,Gas,imin,grid
from mertens_check import U, V

def W3(L,early):
    v=L/2;y=L/3;u=L/4
    eta=lambda t:I('3.965')/t**2
    s=eta(v)
    if early:s=imin(s,v**2*(-v/2).exp()/(8*pi))
    a=eta(y);b=eta(u)
    if early:
        tiny=I('1e-10')
        return ((-v).exp()*(1+s+tiny)+(-2*y).exp()*(I('.5')+a+tiny)
            +(-3*u).exp()*(2+(I(1)/3+b+tiny)/(1-(-u).exp())))
    return ((-v).exp()*(1+3*s)+(-2*y).exp()*(I('.5')+I('2.5')*a)
        +(-3*u).exp()*(2*(1+b)+(I(1)/3+I(7)/3*b)/(1-(-u).exp()))) 

def scal(L,b,early):
    # Common bound for L^2|w| and L^3 times any of the other 3 errors.
    e=b+df(L)*(1+1/L)+W3(L,early)
    assert (e/L).b<1
    return e*L**2/(1-e/L)
def smallstrip():
    J=64000000
    JJ=I(256000000); delta=I('.0003'); lJ=JJ.ln()
    assert ((1-1/lJ-(3+1/lJ)*delta)/2).a>D('.465')
    assert ((1+(3+1/lJ)*delta)/(2*(1-1/JJ))).b<D('.502')
    assert ((1+3*delta)/(1-1/JJ)).b<D('1.003') and (1-3*delta).a>D('.997')
    S=I(10**19)
    assert Gas(S.ln()).b<D('1e-7') and (2*I('1e-7')*(V/2).exp()/S).b<D('1e-10')
    const=I('.791')+I('.0463')*(1+1/U)+I('3e-12')*(3*V/8).exp()*(1+1/U)
    const+=2*(-U/2).exp()*(1+1/U)+W3(U,True)*(U/2).exp()
    C=const/(1-const*(-U/2).exp()/U)
    print('uniform scaled square-root enclosure',C)
    assert C.b<D('1.939')
    # On this strip the common upper scale is decreasing, from the signs
    # of L^2 exp(-aL) and the other factors discussed in the proof.
    rows=[]
    for x in [J,66000000,82000000,115000000,180000000,256000000,300000000,600000000,10**9,2*10**9,10**10]:
        l=I(x).ln(); u=scal(l,I('.791')*(-l/2).exp(),True).b
        co=((I(u)*100000).b.to_integral_value(rounding='ROUND_CEILING'))/100000
        rows.append((x,str(co)))
    assert D(dict(rows)[256000000])<D('.045') and all(D(t)>D('.0097') for _,t in rows)
    print('refined post-sieve coefficients:',rows)

def large():
    # Traverse backwards, bound each compact cell via independent endpoint
    # enclosure, and retain the largest subsequent ceiling (closed cells).
    starts=[30,34,38,42,46,50,55,60,65,70,75,80,100,150,200,210,220,230,240,250,260,280,300,350,400]
    br=starts+[420]
    for mode in ['basic','density']:
        v=I(420); Q=I('.00129')*v**2 if mode=='basic' else QD(v)
        mx=scal(v,Q*(-v/8).exp(),False).b
        # Basic tail L^4 e^-L/8 decreasing; density terms decreasing separately.
        vals=[]
        for a,b in reversed(list(zip(br,br[1:]))):
            for L,m in grid(a,b,'.25'):
                x=imin(Gas(L),chtrial(L))
                if mode=='density' and m>=110:x=imin(x,QD(L)*(-L/8).exp())
                if m>=40:x=imin(x,QB(L)*(-L/8).exp())
                mx=max(mx,scal(L,x,False).b)
            vals.append((a,str(mx)))
        # Conservative strict rounding to two significant digits (upwards).
        vals=[(l,str(D(e).quantize(D(10)**(D(e).adjusted()-1),rounding='ROUND_CEILING'))) for l,e in reversed(vals)]
        assert D(vals[0][1])<D('.0097')
        print(mode,'log onset, whole ray scaled ceiling:',vals)
        if mode=='basic':
            # Bridge to prior analytic results if necessary; this test covers
            # exactly [log(10^13),30], no source fallback presumed for it.
            u=scal(I(V.a,30),chtrial(I(V.a,30)),False)
            print('join at 1e13 to exp(30):',u)
            assert u.b<D('.0097')
        else:
            # At and after each start normalize by e^-L/8. Every component
            # decreases, including the correction for converting z.
            rows=[]
            for a in [200,225,250,300,360,400,500,750,2000,5000,17000,20000,200000,1000000,10000000]:
                v=I(a)
                e=QD(v)+(df(v)*(1+1/v)+W3(v,False))*(v/8).exp()
                t=(e/(1-e*(-v/8).exp()/v)).b
                rows.append((a,str(t.quantize(D('.000001'),rounding='ROUND_CEILING'))))
            print('density log onset, pure power coefficient:',rows)
    v=I(241)
    cushion=(df(v)*(1+1/v)+W3(v,False))*(v/8).exp()/v**2
    u=I('.001284399')+cushion
    z=u*v*(-v/8).exp()
    assert (u/(1-z)).b<D('.001285')
    print('basic normalized power .001285 from log onset 241')
    rows=[]
    for a in [1200,2000,5000,20000,200000,1000000]:
        v=I(a)
        e=QB(v)/v**2+(df(v)*(1+1/v)+W3(v,False))*(v/8).exp()/v**2
        k=(e/(1-e*v*(-v/8).exp())).b
        rows.append((a,str(k.quantize(D('.000000001'),rounding='ROUND_CEILING'))))
    print('basic log onset, normalized power coefficient:',rows)
if __name__=='__main__':
    smallstrip()
    large()

