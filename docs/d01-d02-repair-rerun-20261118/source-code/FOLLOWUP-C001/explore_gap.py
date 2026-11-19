from math import *
from fractions import Fraction
H=3000175332800
def ch(L):
    t=min(H,2*pi*pi*exp(L/2)/L)
    v=log(t/(2*pi))
    z=pi/(t-1)+pi*pi/(3*t*t)+(v*v/(2*pi)-v/(6*pi))*exp(-L/2)
    return min(z,pi/3e12+113.67*exp(-L/2))
def E(L,upper):
    v=ch(L)
    iz=.376*exp(-L/2)/L**2+12e-12*exp(-L/8)/L**2+10000*exp(-L)
    d=(v+(-exp(-L/2) if upper else 1.2551*(exp(-L/2)+2*L*exp(-2*L/3))))/L+iz
    if L<=58: d=min(d,L*exp(-L/2)/(8*pi))
    if L<=39.4 and upper: d=0
    return d
a=[factorial(i) for i in range(21)]+[5*factorial(21)]
cs=[sum(a[i]*comb(j,i) for i in range(min(20,j)+1))-sum(a[i]*a[j-i] for i in range(22) if 0<=j-i<22) for j in range(43)]
def bound(L):
    u=sum(a[i]/L**(i+1) for i in range(22))
    z=E(L,True)
    return sum(c/L**(j-4) for j,c in enumerate(cs) if j>=4)-L**5*E(L-1,False)-L**6*z*(2*u+z)
for L in [35,35.5,36,36.5,37,37.5,38,38.5,39,39.4,39.400001,39.5,40,40.5,41,41.5,42,42.5,43,43.5,44,44.5,45,46,47,48,49,50,55,60,70,100,180]:
 print('%8f %10f'%(L,bound(L)))
