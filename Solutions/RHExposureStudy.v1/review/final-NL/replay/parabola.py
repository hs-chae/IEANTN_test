"""Directed quadrature for the absolute Fourier moments of 1-u^2.
This is an enclosure of continuous integrals, not a sampled conjecture:
see Intervals.md for the total variation and analytic tail bounds.
"""
from bounds import I, F, PI, log, exp, GAMMA

def trig(t, N=45):
    """Taylor with next-term endpoint, for positive t<=.002."""
    t=F(t)
    assert 0<t<=F('.002')
    d=t*t
    cos=1
    sin=t
    tc=F(1)
    ts=t
    for j in range(1,N):
        tc*=-d/((2*j-1)*(2*j))
        ts*=-d/((2*j)*(2*j+1))
        cos+=tc
        sin+=ts
    c2=cos-tc*d/((2*N-1)*(2*N))
    s2=sin-ts*d/((2*N)*(2*N+1))
    return I(min(sin,s2),max(sin,s2)), I(min(cos,c2),max(cos,c2))

def run():
    A=100
    h=F(1,500)
    term_s,term_c=trig(h)
    s,c=trig(h/2)
    isum=mom=I(0)
    j0=j1=I(0)
    C=0
    for j in range(A*500):
        x=(j+F(1,2))*h
        y=4*(s-x*c)/x**3
        abs_upper=max(-y.l,y.h)
        isum+=abs_upper
        if x>1:
            a=(8*x).__floor__()
            if a!=C:
                C,a0=a,F(a,8)
                la=log(a0)
            lg=la+(x-a0)/a0
            mom+=abs_upper*lg
            if x>2:
                neg=max(F(0),-y.l)*F(3,4)/x
                j0+=neg
                j1+=neg*lg
        s,c=s*term_c+c*term_s,c*term_c-s*term_s
    tail0=F(4,A)+F(2,A*A)
    tail1=F(4,A)*(log(A)+1)+F(2,A*A)*(log(A)+F(1,2))
    b0=(h*isum+h/2*F('4.54')+tail0)/PI
    b1=(h*mom+h/2*F('7.7')+tail1-F(4,3)+F(2,135))/PI
    # We care about upper bounds; print their outward decimal ceilings.
    for name,u,b in [('mass/pi',b0,'1.24'),('logmoment/pi',b1,'.50')]:
        assert u.lt(b), (name,float(u.h),b)
        print(name,'<',F((u.h*10**6).__ceil__(),10**6),flush=True)
    a0=h*j0+h/2*F('1.7')+F(3,2*A*A)+F(1,A**3)
    a1=h*j1+h/2*3+F(3,2*A*A)*(log(A)+F(1,2))+(log(A)+F(1,3))/A**3
    jj0=F(4,3)-GAMMA+2*a0
    jj1=F(13,9)-F(4,3)*GAMMA+GAMMA**2/2-PI**2/24+2*a1
    assert jj0.lt('.831') and jj1.lt('.574')
    print('regularized absolute moments upper ceilings:',
          [(j.h*10**6).__ceil__() for j in (jj0,jj1)])
    # Uniform elementary margins at the smallest log and the largest width.
    L=24
    d0=F('.465')*L - F('.93')*log(L)-F('.25')
    assert (d0/L).gt('.33')
    assert ((F('.93')*log(2*PI*F('.33'))-F('.25'))*F(4,3)-F('.50')).gt('.07')
    dm=48*exp(-12)
    assert (2*dm*(F(7,6)+F('4.54')*(1+F('.28')*log(1/dm))+F('.28')*F('6.1'))).lt('.011')
    J=200
    w=2*(F('.465')*J-F('.93')*log(J)-F('.25'))/J
    assert (w*F('1.0003')).lt('.88')

if __name__=='__main__': run()
