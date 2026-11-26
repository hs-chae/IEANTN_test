from fractions import Fraction as F

q = F(20582561296, 24680948495)
g, b, f = (q, 2*q), (F(944247, 10**6), F(1163388, 10**6)), (F(9,8), F(16,15))
def meet(u, v):
    return (v[0]-u[0])/(u[1]-v[1])

assert g[0] < b[0] < f[0] and g[1] > b[1] > f[1]
assert meet(g,b) == F(544470055511653,2490320656859788)
assert meet(b,f) == F(542259,290164)
assert 0 < meet(g,b) < meet(g,f) < meet(b,f)

T = 10**18
ds, bs, us = 1-4*F(119725872611533800,8*T), F(887721072633027910,T), F(546871713113309800,T)
df, bf, uf = F(15*533333333333333333,8*T), F(1120475208606944546,T), F(533333333333333333,T)
assert min(ds,bs,us,df,bf,uf) > 0
assert bs/ds + F(1,2000000) < b[0] and 2*us/ds <= b[1]
assert bf/df + F(1,250) < f[0] and 2*uf/df == f[1]
print("Exact rational checks passed.")
