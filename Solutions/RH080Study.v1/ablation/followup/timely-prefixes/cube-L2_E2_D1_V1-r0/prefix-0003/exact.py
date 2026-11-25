from fractions import Fraction as F
from math import factorial
def e(x):
 x=F(x); k=x//1
 return F("2.718281828")**k*sum((x-k)**j/F(factorial(j)) for j in range(12))
def upper(x):
 x=F(x); s=sum(x**j/F(factorial(j)) for j in range(20))
 return s+x**20/F(factorial(20))/(1-x/21)
pi=F("3.1415")
assert upper("2.24")<3*pi
assert e(8)>2980 and e("5.81")>F(1000,3)
assert 2154001**3<10**19 and F("2.719")**14<2154000<e("14.583")
for n,t,u,c,b in [(1250,"35.35","7.14",".788","2.408"),(2000,"44.72","7.601",".802","2.408"),(2980,"54.58","8",".8145","2.438")]:
 t,u,c,b=map(F,(t,u,c,b))
 assert t*t<n<e(u)
 assert F(8,9)*F(n,n+1)-(F("1.8203")*u-b)/(3*t)>c
for n,t,l,c in [(11,3,2,".75"),(25,5,3,".86"),(49,7,3,".90"),(169,13,5,".95"),(400,20,5,".9669"),(1024,32,6,".9796")]:
 assert t*t<=n and F("2.719")**l<n
 assert (1-F(19,30*t))/(1+F(1,n*l))>F(c)
q=F("14.583")-F("3.139");h=F("5.81")
A=2/pi*((q+2)*h+h*h/2+2*q+2)+F(".031")
assert F(".997")*F(2154000,2154001)-A/(3*1467)>F(".9796")
print("Exact scalar checks passed; not verification of analytic sources.")
