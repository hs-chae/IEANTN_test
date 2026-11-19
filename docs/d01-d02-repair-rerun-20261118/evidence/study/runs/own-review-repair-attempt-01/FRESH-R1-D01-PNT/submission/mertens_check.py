from check import I, D, pi, imin, Gas, df, q, BASIC

N=I(64000000)
U=N.ln()
V=I(10**13).ln()
def W(L, early=False):
    eta=lambda v:I('3.965')/v**2
    y=L/3; a=eta(y)
    s=eta(L/2)
    if early: s=imin(s,(L/2)**2*(-L/4).exp()/(8*pi))
    return (-L/2).exp()*(1+3*s)+(-2*L/3).exp()*(2*(1+a)+(I('.5')+I('2.5')*a)/(1-(-y).exp()))
def scaled(L,b,early=False):
    a=b+df(L)+W(L,early)
    d=b+df(L)*(1+1/L)+W(L,early)
    return a*L**2,d*L**2/(1-d/L)
def check_join():
    delta=I('.0003')
    assert (((I('.791')+I('1.000000147'))/8000)+I('1.78')*(-2*U/3).exp()).b<delta.a
    assert (Gas(V)+I('1.000000147')*(-V/2).exp()+I('1.78')*(-2*V/3).exp()).b<delta.a
    assert (1-3*delta).a>D('.997')
    assert ((1+3*delta)/(1-1/N)).b<D('1.003')
    t=I(58)
    assert (Gas(t)+I('1.000000147')*(-t/2).exp()+I('1.78')*(-2*t/3).exp()).b < (t**2*(-t/2).exp()/(8*pi)).a
    for a in scaled(U,I('.791')*(-U/2).exp(),True): print(a); assert a.b<D('.087')
    for a in scaled(I(66000000).ln(),I('.791')*(-I(66000000).ln()/2).exp(),True): assert a.b<D('.087')
    fine=[(64000000,'.0868'),(82000000,'.079'),(115000000,'.070'),(180000000,'.060'),
          (300000000,'.050'),(600000000,'.040')]
    for x,c in fine:
        t=I(x).ln()
        for a in scaled(t,I('.791')*(-t/2).exp(),True): assert a.b<D(c),(x,c,a)
    # Log-normalized square-root coefficient on the complete small finite-height strip.
    dscaled=I('.094')+I('3e-12')*(3*V/8).exp()+2*(-U/2).exp()
    Dw=I('.791')+dscaled*(1+1/U)+W(U,True)*(U/2).exp()
    assert (Dw/(1-Dw*(-U/2).exp()/U)).b<D('2.151')
    print('post-sieve coefficient onsets',fine)
    # L^2 times the three pieces in a,d decrease, except the constant in Gas.
    h=200 if BASIC else 110
    eps=pi/(3*10**12)
    f=I('113.67')*(-V/2).exp()
    vv=I(h)
    a=(f+df(V)*(1+1/V)+W(V))*V**2+eps*vv**2
    assert a.b<D('.04') and (a/(1-a/V**3)).b<D('.040')
    for a in scaled(vv,q(vv)*(-vv/8).exp()): assert a.b<D('.040')
    # Small power-tail constants; all normalized non-leading terms decrease after these points.
    vals=[(500,'.005001')] if BASIC else [(200,'.020'),(224,'.018'),(272,'.016'),
       (312,'.015'),(376,'.014'),(493,'.013'),(773,'.012'),(2354,'.011'),
       (4321,'.0108'),(32507,'.0106')]
    for K,c in vals:
        t=I(K)
        b=q(t)
        if BASIC: b=b/t**2
        u=b+((-t/2).exp()+df(t)*(1+1/t)+W(t))*(t/8).exp()
        if BASIC: u=b+(u-b)/t**2
        assert (u/(1-(u*(t**2 if BASIC else 1)*(-t/8).exp()/t))).b < D(c),(K,c,u)
    print('power-ray onsets',vals)
    print('Mertens finite join constants, all-ray coefficient ceilings, and power-tail checks passed')
if __name__=='__main__':check_join()
