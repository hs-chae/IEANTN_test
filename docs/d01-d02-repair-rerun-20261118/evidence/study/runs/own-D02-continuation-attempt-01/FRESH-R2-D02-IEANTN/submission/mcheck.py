from verify import I,F,exp0,log,piB,dens

# Monotone interval tail bounds for sums and both products simultaneously.
def CH(T,l,r):
 l,r=F(l),F(r)
 assert exp0(l).above(max(10**9,T))
 v=log(I(T)/(2*piB)); C=(v*v-v/3)/(2*piB); A=piB/(T-1)
 # All exponential monomials here decrease for t>=l>20.
 l2=I(l)**2
 return A*r*r+(C+I('1.001'))*l2*exp0(-l/2)+I('2.67')*l2*exp0(-2*l/3)+piB**2*r/(3*T*T)+3*l2*exp0(-99*l)
def rel(c,L):return c/(1-c/I(L)**3)
H=3000175332800
for T,a,b,c in [(10**7,26,30,'.051'),(10**7,30,40,'.010'),
 (H,40,58,'.0004'),(H,58,100,'.00000011'),(H,100,210,'.000000047')]:
 z=rel(CH(T,a,b),a)
 assert z.below(c)
 print('analytic CH2 normalized',a,b,'<',c,'checked',z.fmt())
assert exp0(26).below(195730000000)

# Difference between capped and uncapped prime-power tails can only help absolute caps.
for L,d,kW,kH in [(200,'.021','.19','.191'), (300,'.016','.145','.145'), (800,'.012','.109','.109')]:
 b=I(L); c=I(d)
 assert dens(L).below(d)
 correction=(I('1.001')*exp0(F(-3*L,8))+I('2.67')*exp0(F(-13*L,24)))
 w=9*c+correction
 h=(9+8/b)*c+correction
 assert w.below(kW)
 assert (h/(1-h*exp0(F(-L,8))/b)).below(kH)
 print('density caps',L,kW,kH)
assert (I('.191')*210**2*exp0(F(-210,8))).below('.000000047')

assert (I(".191")*200**2*exp0(-25)).below("1.1e-7")
