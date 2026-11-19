# Exploratory floating-point only. Rigorous acceptance is in verify.py.
from math import *
H=3e12; h0=log(H); c=1.048e-12
cuts=sorted(set([i/1000 for i in range(780,876)]+[.87499]))
cs=[(7.8,4.11),(8.17,3.7),(8.54,3.62),(8.93,3.54),(9.34,3.46),(9.75,3.38),(10.18,3.30),(10.62,3.22),(11.08,3.14)]
def w(s):
 a,b=cs[max(0,min(8,floor(100*s+1e-8)-79))]
 r=(8*s-5)/3;q=5-2*s
 return a*exp(-r*h0)*h0**q/(r-q/h0)+b*exp(-h0)*(h0*h0+2*h0+2)
ws=[w(s) for s in cuts[:-1]]
vs=[(1-cuts[i],1.000001*(ws[i-1]-ws[i])) for i in range(1,len(ws))]+[(.125,1.000001*ws[-1]),(.25,2),(1,3)]
def components(L,k):
 yield (.22,.0071*L**2);yield (.5,.0142*L**2)
 yield from vs
 if k: yield (.5,3)
def dense(L,k=0):return sum(a*exp(-r*L) for r,a in components(L,k))
def EF(L):return 3*L*exp(7-L)+(L*L+2*L)*exp(-L/2)/(8*pi)
def EF2(L):
 k=(1-2.4/L)**2
 return 3*L*exp(7-L)+exp(-L/2)/(8*pi)*((L-2.4)**2+2*L*(k+(1-k)*exp((34-L)/2)))
def EC(L):return 3*L*exp(12-L)+c*(1+1.2/L)+117*exp(-L/2)*(1+3/L)
def EQ(L):
 return 2e-16*L*exp(100-L)+(.0018*L**2)*exp(-L/8)*(1+1/(.875*L))+3*exp(-L/2)*(1+1/(.48*L))
def ED(L):return 2e-16*L*exp(100-L)+sum(a*exp(-r*L)*(1+1/((.98-r)*L)) if r<.98 else a*exp(-L)*(1+L/100) for r,a in components(L,1))
def Es(L,d=True):
 a=[EC(L)]+([EF2(L)] if 34<=L<=58 else [])+([EF(L)] if L<=58 and L>=7 else [])+([EQ(L)] if L>=200 else [])+([ED(L)] if L>=100 and d else [])
 return min(a)
def Sm(L):return sum(factorial(j)/L**j for j in range(19))
def Rex(L):return 1e5*L*exp(-L)+factorial(19)*3/L**19
def prof(L,d=True):
 E=Es(L,d)+Rex(L); F=Es(L-1,d)+Rex(L-1)
 return L**4*((L/(L-1))*(Sm(L-1)-F)-(Sm(L)+E)**2)
if __name__=='__main__':
 for L in [32,33,34,35,36,37,38,39,40,43,45,48,50,52,54,58,59,60,65,70,80,95,100,110,120,130,140,145,150,160,180,190,200,220,240,250,270,300,400,500,750,1000]:
  print(L,prof(L,False),prof(L),dense(L)*exp(L/8) if L>=100 else '')
 for j in range(4,15):
  print(j,sum(factorial(k)*comb(j,k) for k in range(min(j,12)+1))-sum(factorial(k)*factorial(j-k) for k in range(j+1) if k<=12 and j-k<=12))
