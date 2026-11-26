"""Independent exact scalar regression checks; no analytic assumptions tested."""
from fractions import Fraction as Q

q = Q(20582561296,24680948495)
g, s, f = (q,2*q), (Q(944247,10**6),Q(1163388,10**6)), (Q(9,8),Q(16,15))
line = lambda pair, x: pair[0]+pair[1]*x
inv = lambda pair, c: (c-pair[0])/pair[1]
cross = lambda ab, cd: (cd[0]-ab[0])/(ab[1]-cd[1])
u,v = cross(g,s),cross(s,f)
U,V = line(g,u),line(f,v)
assert (u,v,U,V) == (Q(544470055511653,2490320656859788),Q(542259,290164),
                      Q(3731134672774344,3112900821074735),Q(9048441,2901640))
assert 0 < u < cross(g,f) == Q(172404138261,356130660736) < v
assert q < Q(103,100) < U < 3 < V < 5 < 16
assert g[1] > s[1] > Q(9,8) > f[1] > 0
a3,a5 = Q(685251,387796),Q(465,128)
assert inv(s,3) == a3 > max(inv(g,3),inv(f,3))
assert inv(f,5) == a5 > max(inv(g,5),inv(s,5))
O = lambda c: Q(8,9)*c-Q(18203,20000)
W = lambda a: Q(9,8)*(a+Q(18203,20000))
assert (O(Q(103,100)),O(16),W(1)) == (Q(973,180000),Q(2396173,180000),Q(343827,160000))
assert (O(3),O(5)) == (Q(105391,60000),Q(636173,180000))
assert (a3-O(3),a5-O(5)) == (Q(61212941,5816940000),Q(70933,720000))
assert (W(a3),W(a5)) == (Q(46719158823,15511840000),Q(3270933,640000))
assert (W(a3)-3,W(a5)-5) == (Q(183638823,15511840000),Q(70933,640000))
assert W(v)-V == Q(13152201,1658080000) and v-O(V) == Q(4384067,621780000)
for a in [v,a3,a5]:
    assert Q(103,100) <= W(a) <= 16
d = 10**18
bs = lambda c: (c*(1-4*Q(119725872611533800,8*d))-Q(887721072633027910,d))/(2*Q(546871713113309800,d))
bf = lambda c: (c*Q(15*533333333333333333,8*d)-Q(1120475208606944546,d))/(2*Q(533333333333333333,d))
L3,L5 = Q(193269011844967139,109374342622661960),Q(31036198331144443607,8533333333333333328)
assert bf(3) < bs(3) == L3 and bs(5) < bf(5) == L5
assert a3 < Q(1767041,10**6) < L3 and a5 < Q(3637,1000) < L5
assert L3-O(3) == Q(1726734183826542841,164061513933992940000)
assert L5-O(5) == Q(9864964558708324124141,95999999999999999940000)
print("Exact scalar checks passed")
