"""Exact rational regression checks. No external data required."""
from fractions import Fraction as Q

q = Q(20582561296, 24680948495)
G = (q, 2*q)
S = (Q(944247, 10**6), Q(1163388, 10**6))
F = (Q(9, 8), Q(16, 15))
O = (Q(163827, 160000), Q(9, 8))
curves = G, S, F

def val(line, x):
    return line[0] + line[1]*x

def inv(line, y):
    return (y-line[0])/line[1]

def cross(L, R):
    return (R[0]-L[0])/(L[1]-R[1])

u = cross(G, S)
v = cross(S, F)
assert u == Q(544470055511653, 2490320656859788)
assert v == Q(542259, 290164)
rho, sigma = val(G, u), val(S, v)
assert rho == Q(3731134672774344, 3112900821074735)
assert sigma == Q(9048441, 2901640)
assert q < Q(103, 100) < rho < 3 < sigma < 5 < 16
lower, upper = (inv(O, c) for c in (Q(103,100), Q(16)))
assert (lower, upper) == (Q(973,180000), Q(2396173,180000))
assert 0 < lower < u < 1 < v < upper
assert G[1] > S[1] > O[1] > F[1] > 0
assert val(O,v)-val(F,v) == Q(13152201,1658080000) > 0
assert val(O,1) == Q(343827,160000)
assert val(S,1) == Q(421527,200000)
assert val(O,1)-val(S,1) == Q(33027,800000)

for C, ac, base, D, W, X in (
    (3, (Q(53460284189,41165122592), Q(685251,387796), Q(225,128)),
     Q(105391,60000), Q(61212941,5816940000), Q(183638823,15511840000),
     Q(24431148000,61212941)),
    (5, (Q(102822181179,41165122592), Q(4055753,1163388), Q(465,128)),
     Q(636173,180000), Q(70933,720000), Q(70933,640000), Q(3024000,70933)),
):
    assert tuple(inv(L,C) for L in curves) == ac
    A = max(ac)
    assert A == ac[1 if C==3 else 2]
    assert min(val(L,A) for L in curves) == C
    assert base == inv(O,C)
    assert A-base == D > 0
    assert val(O,A)-C == W > 0
    assert Q(103,100) <= val(O,A) <= 16
    assert X == Q(21,5)/D
assert inv(F,3)-inv(O,3) == Q(311,240000)
assert inv(S,5)-inv(O,5) == -Q(840041177,17450820000)
print("Exact rational checks passed.")
