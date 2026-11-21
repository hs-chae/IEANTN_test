"""Directed illustration of pointwise bound ratios. Proofs of the uniform
comparisons are in the mathematical notes, not inferred from this table."""
from bounds import F,I,PI,log,exp,ei,prove_cell

def upper_per_mille(q):
    return (1000*q.h).__ceil__()

def run():
    print('L psi(B5)/LN(B2) theta(B5+D)/LN(B2) pi/schoenfeld li-error A/LN firstMertens width(a)/sqrt(a)log(a); each per mille upper bound')
    for L in map(F,(44,60,100,150,200,1000)):
        v=L/2-log(L)
        B5=(v*v+F('1.662')*v+F('1.148')+L)/(2*PI)+F('.14')
        B2=L*(L-log(L))/(8*PI)
        theta=B5+F('1.00000075')+3*exp(-L/6)
        P=(B5+F('1.1')+F('.094')/L)/L+5*exp(-L/2)
        A=B5+F('1.2')
        D=F('.465')*L-F('.93')*log(L)-F('.25')
        d=D*exp(-L/2)
        # sinh(d)/d <= exp(d^2) for 0<d<1 by the positive series.
        width=(2*D/L)*exp(d/2+d*d)/(1-d/L)
        print(int(L),*[upper_per_mille(r) for r in (B5/B2,theta/B2,P/(L/(8*PI)),
              A/(3*L*L/(8*PI)),width)])
    K=38358837682
    q0=632207037
    assert 2521*15215723==K+1
    dk=lambda x: exp(1)*q0*(log(x)-1)/log(x)**2
    assert dk(K+1).gt(67600000) and dk(K).lt(67700000)
    print('local real branch slope bounded by [67600000, 67700000]')
    L=F('38.95')
    def normalized_li(v): return v*exp(-v)*ei(v)
    def schoenfeld(v): return v**2*exp(-v/2)/(8*PI)
    q=L**4*(L/(L-1)*(normalized_li(L-1)-schoenfeld(L-1))
              -(normalized_li(L)+schoenfeld(L))**2)
    assert q.lt(0)
    print('independent two-sided Schoenfeld envelope at L=38.95 is below',
          F((q.h*1000).__ceil__(),1000))
    for name,v in [('height',409),('center',700)]:
        try:
            c=prove_cell(v,v,name)
        except AssertionError as exc:
            model,a,b,marg=exc.args[0]
            assert marg < 0
            print('uncertified lower envelope (model, L, millionths)',model,a,marg)
        else:
            raise AssertionError(('expected a nonpositive envelope',c))
if __name__=='__main__':run()
