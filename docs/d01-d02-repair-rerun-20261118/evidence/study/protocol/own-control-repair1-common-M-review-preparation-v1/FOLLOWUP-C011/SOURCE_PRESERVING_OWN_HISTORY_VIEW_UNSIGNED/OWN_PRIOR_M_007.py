"""Ancillary inequalities for the locked all-ray comparisons."""
import sys
sys.path.insert(0,sys.argv[1])
from intervals import I,F,PI,log,exp
l=F(170)
q1=F('.0039')
# Majorize q by its exponential component. Once past max(onset,170),
# eta/L^2 decays more slowly than exp(-L/8).
for a,k in [(201,8),(240,10),(278,12),(355,16),(431,20),(507,24),
            (202,8),(240,10),(279,12),(356,16),(432,20),(508,24)]:
    assert (log(q1)-F(a,8)).lt(-k*log(10)-2*log(a)),(a,k)
for a,eta in [('23.25','.2'),('26.5','.05'),('30.25','.01'),('36.25','.001'),(53,'1e-6'),(62,'1e-7')]:
    v=max(l,F(a))
    assert (log(q1)-v/8).lt(log(F(eta))-2*log(v)),(a,eta)
# Comparison of cited CH2 log-derivative estimate terms.
t=F(1000)
rt=lambda t:F('.137')*log(t)+F('.443')*log(log(t))+F('1.588')
assert (1/PI*log(t/(2*PI))+rt(t-1)+rt(t+1)).lt(20*log(t))
assert (F('2.9')/PI*log(t/(2*PI))+F('2.8')*(F('.4')*log(t)+4)+F('.00202')+3).lt(20*log(t))
# All permitted early CH2 constants satisfy aa<1e-6, cc<120:
T=10**7; Hstar=3000175332800
assert (PI/(T-1)+PI**2/(3*T*T)).lt(F('1e-6'))
y=log(Hstar/(2*PI))
assert (y*y/(2*PI)-y/(6*PI)).lt(120)
v=F('23.25')
assert ((F('2e-6')+(124+240/v)*exp(-v/2)+10*exp(-2*v/3))/v).lt(1)
# PT Lemma 2 low T < 2*pi*e never used in the Perron mass estimate.
v=F(61)
assert I(v+51).lt(exp(v/2)/6)
assert I(F('12.546')).lt(3*v)
print('All-row B0 log floor, vertical estimate slack, positive early conversion denominator and Perron left checks passed')
