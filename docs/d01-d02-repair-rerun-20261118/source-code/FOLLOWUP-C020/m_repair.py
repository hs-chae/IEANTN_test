"""Exact certificates; proof and domain joins in mertens_repair.md."""
from ram_repair import Q, eu, el, pl, logb, theta_new
from pathlib import Path
Z=Q('3.3e-12')
alpha,eps,eta=Q('1.47e-7'),Q('.0001'),Q('1.78')
D=Q('1.048e-12')
AC=Q('29.9')
BI=1-2/AC+8/AC**2
def u(L):
    s=eu(-L/2);t=eu(-2*L/3);e=eu(-L)
    w=(L+1)/L**2
    up=(Q('.791')+eps+BI)*s/L+w*((Q('.048')+2*alpha)*s+Q(3,2)*eta*t+Z*eu(-L/8)+2*e)+e
    # Lower sign: discard the nonnegative B1, which still leaves a smaller loss.
    dn=((Q('.751')+alpha)*s+eta*t)/L+w*((Q('.048')+2*eps)*s+Z*eu(-L/8)+2*e)+e
    return max(up,dn)
# Coarse step certificates; (coefficient, log-onset, closed integer finite top).
ROWS=[
 ('.011','22.9',9000000000),
 ('.010','23.1',11500000000),
 ('.009','23.28',13000000000),
 ('.008','23.6',18000000000),
 ('.007',24,26500000000),
 ('.006','24.285',35500000000),
 ('.005','24.82',61000000000),
 ('.00205',27,None),
 ('.001',32,None),
]
def thresholds():
    # Low-zero integral uses D01 smooth.md; high bound uses D02 reciprocal tail.
    assert Q('.0463')*(1+2*Q(20,18*19)/14)<Q('.048')
    assert Q('3.2e-12')*(1+2*Q(20,18*19)/(3*10**12))<Z
    a=Q('29.9')
    assert Q('1.95')+Q('3.9')/a+Q('19.5')/a**2<Q('6.31')/3
    def pif(t):
        return Q('6.31')*t**2*eu(-t/2)+5*t**3*eu(-t)+Q('7e-9')*t**3
    a1=max(pif(a),pif(Q(40)))
    b1=max(pif(Q(32)),pif(Q(40)))
    mid=2*D*190**2+Q('114.674')*(40**2+2*40)*eu(Q(-20))+40**3*eu(Q(-40))
    for k,x,top in ROWS:
        k,x=Q(k),Q(x)
        if top is not None:
            assert eu(x)<top
        if x<=a:
            U=u(x)
            assert U<1 and x**3*U/(1-U)<k,(x,k,float(x**3*U/(1-U)))
        p=b1 if x>=32 else a1
        assert p<1 and p/(1-p)<k
        assert mid/(1-mid)<k
        assert Q('.01955')*190**2*eu(Q(-190,8))<k
    # Weighted-sum coefficients from the exact Stieltjes transfer, L=27 split.
    for x,k,z in [(3909288921,'.011','.014'),(4760000000,'.010','.0124'),
                  (8500000000,'.009','.0111'),(12000000000,'.008','.0099'),
                  (16000000000,'.007','.0087'),(22000000000,'.006','.0075'),
                  (30000000000,'.005','.0064')]:
        lo=logb(Q(x))[0]
        k,z=Q(k),Q(z)
        assert lo<27 and Q(3,2)*Q('.00205')<z
        C=Q(3,2)*k-(k-Q('.00205'))/2*(lo/27)**2
        print(x,'weighted whole-ray upper coefficient',float(C))
        assert C<z
    # Theta partial summation: bracket the prime reciprocal-square tail.
    L=Q(18)
    assert (1-1/L-Q('.001')*(3+1/L))/2>Q('.470')
    assert (Q(1,2)+1/(3*(el(L)-1)))*(1+Q('.001')*(3+1/L))<Q('.502')
    assert 1/(2*(el(L)-1))>Q('.502')/(el(L)*L) # sufficient scale separation at left
    assert Q('.502')/L<Q(1,2)

def power():
    for a,k in [(600,'.01231'),(900,'.01164'),(1300,'.01127'),(2000,'.01099'),(3500,'.01078'),(9000,'.01059'),(12000,'.01055'),(18000,'.01052')]:
        L=Q(a)
        C=theta_new(L)
        s=eu(-3*L/8); t=eu(-Q(13,24)*L);v=eu(-7*L/8)
        U=C+(1+1/L)*(Q('2.0860003')*s+Q('2.67')*t+Z+2*v)+L*v
        r=U*eu(-L/8)/L
        print('power from',a,'scaled bound',float(U/(1-r)))
        assert r<1 and U/(1-r)<Q(k),(a,k)
if __name__=='__main__':
    thresholds()
    # Signed all-output scaling: 65<=L<=190 use theta endpoint q+116Z,
    # sqrt and cube integrals, and the integrated psi absolute bounds.
    L=Q(65); A=Q(190)
    for L,k in [(Q(50),Q('4.4e-6')),(Q(60),Q('8.2e-8')),(L,Q('4.3e-8'))]:
        d=D*A**2+116*L**2*eu(-L/2)+ (L**2+L)*(
           Q('2.0860003')*eu(-L/2)+Q('2.67')*eu(-2*L/3)+Z*eu(-L/8)+2*eu(-L))
        d+=L**3*eu(-L)
        assert d/(1-d)<k,(L,k,float(d/(1-d)))
        assert Q('.01955')*A**2*eu(-A/8)<k
    power()
