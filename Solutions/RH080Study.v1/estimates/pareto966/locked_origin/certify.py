#!/usr/bin/python3.10
"""Exact scalar checks for candidate.md, no floating-point decisions."""
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from math import isqrt
from pathlib import Path
import sys


def require(cond, label):
    if not cond:
        raise AssertionError(label)
    print(label, "OK")


@lru_cache(maxsize=None)
def log_reduced(q, N=32):
    # 1 <= q <= 2. Positive atanh series with geometric upper remainder.
    if not 1 <= q <= 2:
        raise ValueError(q)
    z = (q-1)/(q+1)
    z = Q(z)
    z2 = z*z
    term = z
    s = Q(0)
    for k in range(N):
        s += 2*term/(2*k+1)
        term *= z2
    return s, s + 2*term/((2*N+1)*(1-z2))


@lru_cache(maxsize=None)
def log_bounds(q):
    q = Q(q)
    if q < 1:
        raise ValueError(q)
    e = 0
    while q > 2:
        q /= 2
        e += 1
    a, b = log_reduced(q)
    c, d = log_reduced(Q(2))
    return a+e*c, b+e*d


def atan_bounds(z, N=24):
    # Even count gives a lower partial sum for alternating terms.
    if N % 2 or not 0 <= z <= 1:
        raise ValueError((z,N))
    s = sum((-1)**k*z**(2*k+1)/(2*k+1) for k in range(N))
    return s, s+z**(2*N+1)/(2*N+1)


def pi_bounds():
    # Machin: pi=16 atan(1/5)-4 atan(1/239), by angle addition.
    a,b = atan_bounds(Q(1,5))
    c,d = atan_bounds(Q(1,239))
    return 16*a-4*d,16*b-4*c


def sqrt_bounds(q, scale=10**15):
    q = Q(q)
    if not q >= 0:
        raise ValueError(q)
    k = isqrt((q.numerator*scale**2)//q.denominator)
    return Q(k,scale),Q(k+1,scale)


def H_upper(M):
    M = Q(M)
    _,Lu = log_bounds(M)
    s,_ = sqrt_bounds(M)
    pi,_ = pi_bounds()
    return (1+1/M)*(3*Lu+3/M-2)*Lu/(4*pi*s)


def F_upper(M):
    M = Q(M)
    s,_ = sqrt_bounds(M)
    return (Q(19,10)+Q(39,10)/M)/(3*s)-Q(7,8)/(M+1)


def raw_S_upper(n):
    # Upper bound on normalized RHS of exact pointwise inequality,
    # deliberately NOT an upper bound on the prime count.
    a,b = n**3,(n+1)**3
    La,Ua = log_bounds(n)
    Lb,Ub = log_bounds(n+1)
    sa,_ = sqrt_bounds(a)
    sb,_ = sqrt_bounds(b)
    _,piu = pi_bounds()
    err_lower = (sa*(3*La-2)*3*La+sb*(3*Lb-2)*3*Lb)/(8*piu)
    return (b-a-err_lower)*Ua/(3*n*n*Lb)


def basic_checks():
    m = 2980
    lo,hi = log_bounds(m)
    require(7 < lo <= hi < 8 and m**3 > 2300000000, "source cutoffs and m<exp(8)")
    require(2154434**3 < 10**19 < 2154435**3, "cube root bracket")
    require(F_upper(m) < Q("0.01132"), "finite defect < 0.01132")
    require(H_upper(m) < Q("0.256640"), "Schoenfeld initial defect < 0.256640")
    require(H_upper(3000) < Q("0.2564"), "Schoenfeld defect at 3000 < 0.2564")
    require(1+Q(7,8*3001)-Q("0.256640")>Q("0.7436"), "initial coefficient > 0.7436")
    require(H_upper(2154433) < Q("0.033007995"), "Schoenfeld seam defect < 0.033007995")
    require(H_upper(2160000) < Q("0.033"), "Schoenfeld defect at 2160000 < 0.033")
    require(1+Q(7,8*2160001)-Q("0.033007995")>Q("0.96699241"), "seam coefficient > 0.96699241")
    for x,c in [(3*10**6,"0.9707"), (10**7,"0.98119"), (10**8,"0.99219"), (10**9,"0.99686")]:
        require(H_upper(x)<1-Q(c), f"coefficient {c} for n >= {x}")
    require(raw_S_upper(2154435) < Q("0.967"), "exact RHS of plain pointwise S is < 0.967 at witness")


def check_pins():
    for name,len_bytes,h in [
        ("Schoenfeld1976.pdf",1795864,"8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897"),
        ("Buthe1511.02032v2.pdf",259815,"350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1"),
    ]:
        b=(Path("/corpus/literature")/name).read_bytes()
        require(len(b)==len_bytes and sha256(b).hexdigest()==h,"primary pin "+name)


if __name__ == "__main__":
    basic_checks()
    if "--pins" in sys.argv:
        check_pins()
