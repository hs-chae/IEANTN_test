from fractions import Fraction as Q

q = Q(20582561296, 24680948495)
b = Q(18203, 20000)
G, S, F = curves = [(q, 2*q), (Q(944247, 10**6), Q(1163388, 10**6)),
                    (Q(9, 8), Q(16, 15))]
def crossing(i, j):
    return (j[0]-i[0])/(i[1]-j[1])
def width(i, a):
    return i[0]+i[1]*a
def inv(i, c):
    return (c-i[0])/i[1]
def old(a):
    return Q(9, 8)*(a+b)
def lead(c):
    return Q(8, 9)*c-b

u, w, v = crossing(G,S), crossing(G,F), crossing(S,F)
assert (u,w,v) == (Q(544470055511653,2490320656859788),
                   Q(172404138261,356130660736), Q(542259,290164))
assert 0 < u < w < v
assert G[1] > S[1] > F[1] > 0
U, V = width(G,u), width(S,v)
assert U == width(S,u) == Q(3731134672774344,3112900821074735)
assert V == width(F,v) == Q(9048441,2901640)
assert q < U < 3 < V < 5
assert width(G,w) == width(F,w) > width(S,w)
assert lead(Q(103,100)) == Q(973,180000)
assert lead(16) == Q(2396173,180000)
assert old(1) == Q(343827,160000)
for c, i, a, d, gain, dwidth in [
        (3,S,Q(685251,387796),Q(105391,60000),
         Q(61212941,5816940000),Q(183638823,15511840000)),
        (5,F,Q(465,128),Q(636173,180000),
         Q(70933,720000),Q(70933,640000))]:
    assert a == inv(i,c) == max(inv(j,c) for j in curves)
    assert Q(103,100) <= c <= 16 and Q(103,100) <= old(a) <= 16
    assert d == lead(c)
    assert a-d == gain > 0 and old(a)-c == dwidth == Q(9,8)*gain
for i, a in [(G,u),(S,v),(F,v)]:
    assert old(a)-width(i,a) > 0
print("Exact rational regression checks passed.")
