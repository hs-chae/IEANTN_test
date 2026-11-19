import math as m
from math import factorial as f, comb
import mpmath as mp
mp.mp.dps=50
def A(l,n): return sum(f(k)/l**k for k in range(n+1))
for a in [36,37,38,39,40]:
 print('li',a)
 for n in [9,12,14,16,18,20,22]:
  exact=(mp.ei(a)*a/mp.exp(a)-A(mp.mpf(a),n))*mp.mpf(a)**(n+1)/f(n+1)
  c=1/(1-(n+2)/a)
  print(n,float(exact),c)
def err(l):return ((l*l+2*l)/ (8*m.pi))*m.exp(-l/2)+100*l*m.exp(-l)
for l in [37,38,38.5,39,39.4,39.5,40,40.5,41,42,43,44,45,47,50,55,58]:
 x=mp.exp(l)
 g=(mp.ei(l-1)*m.e/l/x-(mp.ei(l)/x)**2)*l**6
 # use exact e
 g=(mp.ei(l-1)*mp.e/l/x-(mp.ei(l)/x)**2)*l**6
 d=(2*float(mp.ei(l)*l/x)+err(l))*err(l)*l**4+err(l-1)*l**5/(l-1)
 print(l,float(g),d,float(g)-d, float(g)-err(l-1)*l**5/(l-1))
