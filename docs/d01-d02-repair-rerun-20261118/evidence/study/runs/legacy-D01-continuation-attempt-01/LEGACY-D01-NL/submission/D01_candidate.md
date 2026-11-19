# A-D01 — result index

All domains below are real unless explicitly indexed by integers.
H is exactly PsiMajorant in /task/INPUT_CONTRACT.json. S is the zeta
strip Re rho<=7/8: proved from H in this submission, and also a
literal admitted conclusion of OpenAIQRH Thm 1.1. No full RH.

## Requested families

**Ramanujan (ramanujan.md).** Let n=38,358,837,682. The last real
zero/failure boundary is r in (n+.2179,n+.2180), defined by
`e*r*632207037/log r = 1644673232^2`. Under H (or S) R(r)=0 and
R(x)>0 for every x>r; n is the last integer exception. This closes
the gap beyond the original exp(58) range to exp(3915). The original
literal lower *real* endpoint has a short discrepant sliver: a new
exact prime count gives R(n)<0, with counts constant on [n,n+1].
Use the admitted theorem only at its integers on that part.
Independently of density tables, R(x)>.05*x^2/log^6 x from exp(36.96),
and R(x)>x^2/log^6 x from exp(43). The adaptive margin G and
explicit higher-order positive margins are in ramanujan.md.

**Mertens (mertens.md).** Whole-ray strict improvements over
Dusart on the original product and reciprocal-sum domains, and
over the original log-weighted reciprocal-sum coefficient from
912565, with sharper piecewise envelopes. New sharp real starting
points at the original tolerances have exact brackets
(2278381.71,2278381.72), (2278382.10,2278382.20), (912559.98,912560.00)
for joint products, reciprocal sum, weighted reciprocal sum.
All three signed deviations are strictly positive on [2,10^13],
with explicit lower margins (the normalized P log has opposite sign).
On x>=exp(200), under S and the source density estimates, both product
relative errors and the reciprocal prime sum are bounded by
.019851*x^(-1/8)/log x, the weighted sum by .01985*x^(-1/8).
The full coefficient profiles tend to at most .0106*(1+1/(3*10^12))
in their respective power scales. H-only and density-free variants
are recorded. The spectral-tail proof treats the product as a prime
power truncation with separated positive spill, not just a bound
from inserting |theta-x| into an integral.

## Other derived results

**Chebyshev (density.md).** Under S, for log x>=185,
|psi(x)-x|<=x^(7/8)D(log x), with D explicitly given, D(185)<.022,
D(200)<.020, and D(infinity)=.0106. Uniformly on the whole H ray this
improves the supplied majorant by a factor at least 31250. Density-free
fallback .0045*x^(7/8)*log^2 x on x>=exp(185).

**Tertiary (tertiary.md).** Explicit counts in shorter intervals
of lengths x^(5/8)*log(x)^(51/4)/50000 and
.004*x^(5/8)*log(x)^(51/4)/(log log x)^3 on their stated rays;
primes between sufficiently large consecutive cubes; improved explicit
extremal totient/primorial bounds. Turnkey reproducibility below.

## Status and replays

Supported arguments with directed ordinary certificates, not kernel
proofs. No fresh verification of finite RH, CH2 source computations,
PT's low Ramanujan computation, or original density tables is claimed.
Exact source locators, inequalities on entire rays and limitations
are in the respective result documents and notes.md.

From /work/submission:
```
PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 -u check.py
PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 -u pi_exact.py
/usr/bin/gcc -std=gnu11 -O3 -Wall -Wextra sieve.c -o /work/mertens-check
/work/mertens-check | PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 endpoints.py
```
Pipe the actual newly built certificate's stdout, not a stored approximate
number. No external data, floating comparisons, or model calls are used
by any certificate assertion. Use default assertions (no -O for
Python, no -DNDEBUG for C).
