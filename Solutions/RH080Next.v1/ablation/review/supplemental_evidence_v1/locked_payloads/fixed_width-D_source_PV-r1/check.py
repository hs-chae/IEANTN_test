from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import re

q = Q(20582561296, 24680948495)
gsf = [(q, 2*q), (Q(944247, 10**6), Q(1163388, 10**6)), (Q(9, 8), Q(16, 15))]
def at(line, a):
    b, m = line
    return b + m*a

def inv(line, c):
    b, m = line
    return (c-b)/m

def crossing(left, right):
    b, m = left
    d, n = right
    return (d-b)/(m-n)

g, s, f = gsf
A, T, B = crossing(g, s), crossing(g, f), crossing(s, f)
assert (A, T, B) == (Q(544470055511653, 2490320656859788),
                    Q(172404138261, 356130660736), Q(542259, 290164))
assert 0 < A < T < B and g[1] > s[1] > f[1] > 0
assert at(g, A) == at(s, A) == Q(3731134672774344, 3112900821074735)
assert at(s, B) == at(f, B) == Q(9048441, 2901640)
assert g[0] < at(g, A) < 3 < at(f, B) < 5

g3, s3, f3 = [inv(line, 3) for line in gsf]
g5, s5, f5 = [inv(line, 5) for line in gsf]
assert (g3, s3, f3) == (Q(53460284189,41165122592), Q(685251,387796), Q(225,128))
assert (g5, s5, f5) == (Q(102822181179,41165122592), Q(4055753,1163388), Q(465,128))
assert 0 < g3 < f3 < s3 and 0 < g5 < s5 < f5

o = (-Q(18203, 20000), Q(8, 9))
assert [at(o, c) for c in (Q(103,100), 16)] == [Q(973,180000), Q(2396173,180000)]
assert at(o, Q(103,100)) < A < B < at(o, 16)
assert inv(o, 1) == Q(343827,160000)
assert [at(o, c) for c in (3, 5)] == [Q(105391,60000), Q(636173,180000)]
assert (s3-at(o, 3), f5-at(o, 5)) == (Q(61212941,5816940000), Q(70933,720000))
assert (inv(o,s3)-3, inv(o,f5)-5) == (Q(183638823,15511840000), Q(70933,640000))
assert [(inv(o, 0)-b, 1/o[1]-m) for b,m in gsf] == [
    (Q(150039188346073,789790351840000), -Q(107192444281,197447587960)),
    (Q(318687,4000000), -Q(9597,250000)),
    (-Q(16173,160000), Q(7,120))]
assert inv(o, 2) > max(at(s, 2), at(f, 2))

scale = 10**18
caps = ((1-4*Q(119725872611533800,8*scale),Q(887721072633027910,scale),
         Q(546871713113309800,scale)),
        (Q(15*533333333333333333,8*scale),Q(1120475208606944546,scale),
         Q(533333333333333333,scale)))
def cap(c, v):
    d, u, m = v
    assert d > 0 and m > 0
    return (c*d-u)/(2*m)
r3, r5 = cap(3,caps[0]), cap(5,caps[1])
assert r3 == Q(193269011844967139,109374342622661960) > max(s3,cap(3,caps[1]))
assert r5 == Q(31036198331144443607,8533333333333333328) > max(f5,cap(5,caps[0]))
assert (r3-at(o,3), r5-at(o,5)) == (
    Q(1726734183826542841,164061513933992940000),
    Q(9864964558708324124141,95999999999999999940000))
print("Exact arithmetic checks passed.")

src = Path("/source_pv")
for c_file, lean_file in (("population_norm.c", "PopulationSource.lean"),
                          ("flat_population_norm.c", "FlatPopulationSource.lean")):
    embed = next(l for l in (src/"source"/lean_file).read_text().splitlines()
                 if l.startswith("def sourceChars : "))
    nums = re.findall(r"Char[.]ofNat ([0-9]+)", embed)
    assert nums
    decoded = bytes(map(int, nums))
    assert decoded == (src/c_file).read_bytes()
    print(c_file, sha256(decoded).hexdigest())
