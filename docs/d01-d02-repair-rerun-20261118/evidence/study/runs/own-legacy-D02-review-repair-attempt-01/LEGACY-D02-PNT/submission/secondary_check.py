"""Replays QRH-free C014 subroutines and current tertiary comparisons."""
from refine import test_M,test_short
from analytic_check import pi_check,test_density
from extra_check import high_unconditional,signed_small_ramanujan
from ray_check import finite_mertens_checks
from portfolio_check import I,e,a0
from endpoint_check import main as endpoint

def tertiary():
    L=I('186.03')
    assert a0*e(L/8)+117*e(-I(180)*3/8)<I('.01317')
    assert I('.0131652')+3*e(-L*3/8)<I('.01317')
    assert e(-I(180)/8)<I('1e-9')
    u=I('1e-9'); k=I('.01318'); m=I('.01317')
    assert k/(1-k*u)<I('.013180001')
    assert 1/(1-k*u)<I('1.00000001')
    assert m*(1+k*u)<k
    assert I('.013180001')+I('.013166')*I('1.00000001')<I('.02635')
    assert I('.02635')-m*(2+I(7)/8*I('.02635')*u)>I('.0000099')
    print('Current secondary theta, prime interval and primorial checks passed')

if __name__=='__main__':
    pi_check();test_density();test_M();endpoint()
    high_unconditional();signed_small_ramanujan();finite_mertens_checks()
    test_short();tertiary()
