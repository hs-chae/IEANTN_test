# Mertens products and prime sums: D02 and matched controls

Let (x>1, t=log x). The four errors are
[
 E_P=|e^gamma tP_{
m raw}(x)-1|,quad
 E_Q=|e^{-gamma} Q_{
m raw}(x)/t-1|,quad
 |S|=left|sum_{ple x}1/p-log t-M
ight|,quad
 |W|=left|sum_{ple x}log(p)/p-t+B_3
ight|.
]
Here (P_{
m raw}=prod_{ple x}(1-1/p)), (Q_{
m raw}=1/P_{
m raw}),
(M=gamma+sum_p(log(1-1/p)+1/p)), and
(B_3=gamma+sum_plog p/[p(p-1)]). Constants and step conventions
are exactly those in `mertens.md` (Dusart Theorems 5.6–5.9,
PDF pp.17–20). Keep the original caps: (0.2/t^3) from
2278382 for the products and from 2278383 for (|S|);
(0.3/t^2) from 912560 for (|W|).
Keep every result and interval of the own D01 file as a B0
branch. There are no new hypotheses except D02 where stated.

## Power/log coefficient tradeoffs, each on a whole real ray

With D02, every row gives the indicated **strict** cap for
(E_P,E_Q,|S|) in units (x^{-5/32}/t), and for (|W|)
in units (x^{-5/32}), on all (tge a).

| (a) | coefficient | (a) | coefficient |
|---:|---:|---:|---:|
| 150 | .348 | 210 | .250 |
| 160 | .320 | 220 | .242 |
| 169 | .300 | 250 | .225 |
| 170 | .299 | 300 | .2071 |
| 180 | .282 | 332 | .200 |
| 190 | .269 | 400 | .189 |
| 200 | .2582 | 550 | .1761 |
| | | 800 | .167 |
| | | 1250 | .160 |

The new B0 construction (same proof with (b=7/8))
gives bounds with (x^{-1/8}) replacing (x^{-5/32}):
at (a=200,300,800) the respective coefficients are
(.01831,.01474,.01187). Compare to inherited D01's
(.191,.145,.109) for the first three and (.190,.145,.109)
for the weighted sum. Most of that coefficient gain is B0:
retain the oscillating high-strip term until after integration.
D02 then improves the exponent by (1/32). For example
at (a=200), the ratio of the two *new rounded* caps is
((.2582/.01831)e^{-t/32}), less than .028 on that whole ray
and decreasing. A smaller B0 constant in the different
(1/8)-exponent units does not mean a better error.
Conversely for a fixed exponent and onset (7) furnishes the
unrounded functional coefficient and not only table rows.
Using the hypothesis directly in an absolute Abel integral
would have left (t^2) for (W) and (t) for the other
three residuals rather than (1) and (1/t).

## Log-power and finite/onset comparisons

These are common coefficients for (E_P,E_Q,|S|) in units
(t^{-3}) and (|W|) in units (t^{-2}), again strict for
the new rounded caps on the indicated whole ray.

| log onset | B0 coefficient | D02 coefficient if smaller here |
|---:|---:|---:|
| 26 | .0503 | |
| 30 | .0093 | |
| 35 | .0013 | |
| 40 | .000182 | |
| 45 | .000024 | |
| 50 | .00000301 | |
| 58 | (1.004cdot10^{-7}) | |
| 65 | (3.781cdot10^{-8}) | (3cdot10^{-8}) |
| 100 | (3.781cdot10^{-8}) | (3cdot10^{-8}) |
| 200 | (1.017cdot10^{-8}) | (2.77cdot10^{-10}) |

At fixed coefficient (10^{-8}) there are whole rays
starting at 201 (matched B0) and 177 (D02); for (10^{-9})
the onsets are 220 and 192. At (3cdot10^{-10})
one may take 230 and 200. D02 also gives (1.182cdot10^{-8})
from (t=175).
For the B0 log ray .0503 an earlier **(x)** onset is
(9750000000): the last inherited finite bin has weighted
coefficient .0100 and reciprocal and log-product coefficients
.0096; converting the log-product coefficient gives (<.0100)
there and the bin extends beyond (e^{26}).
The earlier bin/suffix tradeoffs of `mertens.md` remain valid.

The new analytic log-power rays use the direct CH2 Corollary 1.2
and Proposition 9.1 transfers (PDF pp.3,34–36) of `mertens.md`.
For the numerical cap on each closed quarter-log cell
([l,r]), test a collection of heights (T) (the exact list
is in `mnew.py`); discard heights with (e^llemax(T,10^9)).
All retained heights are verified by FiniteRH Theorem 1.
Bound the increasing terms of
[
 t^2 A_T+(C_T+1.001)t^2e^{-t/2}
 +2.67 t^2 e^{-2t/3}+pi^2t/(3T^2)+3t^2 e^{-99t}
]
at (r), the decreasing terms at (l); this bounds normalized
(|S|,|W|,|Z|) as asserted in the inherited proof. Convert to
relative product caps by (cmapsto c/(1-c/l^3)).
Select the smallest certified bound over heights for each cell and
the maximum over cells. Switch at (t=190) (B0) or 169 (D02)
to the corresponding new decreasing log-shape power envelope
from (7) frozen at its switch. There are no gaps. The earlier
fixed coefficient improvements are mostly from varying the CH2
height, not from D02; the improvement at and beyond the long-ray
junction also yields a uniformly lower cap at earlier onsets.

### New B0 finite real bounds below the inherited starting bin

All four columns give numerator caps, divided by (10^4);
scale (|W|) by (t^2), the other three by (t^3).
These are closed real intervals in (x), with non-strict caps.

| (x) bin | (|S|) | (|W|) | (E_P) | (E_Q) |
|---|---:|---:|---:|---:|
| [2,10] | 30394 | 37078 | 25371 | 32026 |
| [10,100] | 36147 | 43427 | 33002 | 36124 |
| [100,1000] | 39703 | 45502 | 38260 | 39592 |
| [1000,10000] | 22704 | 25693 | 22467 | 22602 |
| [10000,50000] | 12699 | 14133 | 12652 | 12672 |
| [50000,100000] | 8194 | 8921 | 8182 | 8187 |

Use `mfinite.py`. With an elementary Eratosthenes sieve,
compute prefix sums at primes through 100000. Use the exact
(gamma,M,B_3) inclusions certified in the reviewed
`sieve-results.txt`, and outward fixed-point log arithmetic.
On every interval between adjacent knots the prime sums
are constant until the right endpoint, and the subtracted
(log t,t) are increasing. This encloses the signed errors
on the whole interval. The software also checks a prime at
a bin endpoint on both sides (closed-bin convention);
all other prime jumps are included by their next cell.
Convert (Z) to (P,Q) separately by directed exponentials
before normalizing by the right endpoint value of (t^3).
At (100000) the inherited finite branch is present, at the
last inherited endpoint the CH2 branch is present, and both
new tails start before the end of their analytic covers.
For (1<x<2) the exact products are 1 and the sums are zero.
For sharper finite pointwise evaluation use the same prefix
intervals but evaluate the trend at the given (x), not both
cell endpoints.

## Whole-domain envelope and source comparisons

The estimator is defined *pointwise*, not a choice of a
single table branch for every (x). Form the B0 envelope
by retaining the inherited signed intersection in
`mertens.md`, all its numerical caps on their original
domains, the new finite cells above, the CH2 cell caps,
and the new (b=7/8) terms in (6). Also allow
Platt–Trudgian 2021 Theorem 1 and Corollary 1 (PDF pp.2–3)
in the Chebyshev intersection. This makes the comparison
cumulative: e.g. FKS Theorems 1.1–1.2 and Corollary 1.4
(PDF pp.2–3 and Tables 5–6 pp.22–23), Dusart Proposition 3.2
and Theorems 3.3 and 4.2 (PDF pp.7–9, 11–12), all
legal CH2 heights, the FiniteRH Corollary 1 ranges (PDF p.4),
and the direct comparison bounds of Dusart are not replaced
by the new tail. A published adjustable inequality may
be used at every parameter choice satisfying its exact
hypotheses (intersection/infimum); numerical cells optimize
only over the stated finite set. With D02 intersect also
with (6) for (b=27/32), and add the new verified table rows.
In (6), use the signed intervals for (F,U), and perform
(W=F+J_0, S=U+J_1, Z=U+J_{1,c}=S-C_x) with the inherited
prime-power intervals. From signed endpoints of (Z) the
nonlinear product conversions in `mertens.md` are exact;
take minimum with the direct product estimates on their
valid domains. One can also use any frozen coefficient
from (7) at any (ale t). The result is no weaker at any real
point, including below (e^{200}); no original branch gets
extrapolated to a different domain. This is a furnished
source envelope, not an optimality assertion over possible
new proofs from the sources.

For a quantitative whole-domain comparison of the furnished
analytic branches, for (tge169) write
[
 d(t)=min(1.03cdot10^{-12}, .004e^{-t/8}).
]
The new D02 cap is strictly less than (d(t)) on this ray
in the (W) units, and (d(t)/t) for the other errors:
verify .300 at 169, compare both exponentials there, and
use (alpha=5/32>1/8). The directly evaluated B0
signed branches on that ray have the following floors
on **their reported error radii**, not on the true errors.

* The B0 estimates (2), (3), (6) in the tail and (D)
  in `density.md` all contain the centered relative
  cap (.005e^{-t/8}) with the appropriate (1/t)
  for the (U)-weight; for (2) use its last band as in
  `ramanujan-d02.md`. All legal CH2 heights have radius
  at least (pi/3000175332800) in the normalized
  (psi,F) units, or that divided by (t) for the
  direct (U)-radius apart from the factor (1-e^{-99t}).
  The offset of the (psi)-center is bounded by
  (pi^2/(3T^2)); for the (U)-center it is at most
  (pi^2/(3T^2t^2)). Even allowing the offsets, these
  intervals contain the centered cap (1.04cdot10^{-12})
  with the corresponding units. The other finite-height
  Schoenfeld-shaped branches do not reach (t=169)
  (even CH2 9.3's height is too high there).
* The direct published Chebyshev power/log and table
  bounds being intersected do not provide smaller
  radii here. For Dusart 3.3 and 4.2 use
  (.01/t^4) as a lower bound for all their caps;
  it exceeds (.005e^{-t/8}) from 169 by differentiation.
  In Dusart Table 1 rows up to 1000 all radii are
  (>1.04cdot10^{-12}); for the remaining rows
  the smallest listed constant exceeds (2.35cdot10^{-20})
  and (tge1500). For Platt–Trudgian's table constants
  (tge1000) and the smallest is (>6cdot10^{-29}).
  The continuous bounds in their Theorem 1 and
  Corollary 1 have (Age1,B>0,Cle2,R>5), so are
  larger than (e^{-t/8}) for (tge1000).
  For FKS Corollary 1.4 use (0.848sqrt t<t/8).
  In FKS (4.1), even allowing the published parameter
  choices, if (T<2H) use its (epsilon_1=2(log x_0)^2/T)
  term, otherwise use the second term of (epsilon_2)
  in (3.8) with (B_1(H,T)>1) by (2.1), (sigma_1=.9).
  These are more than (.005e^{-(log x_0)/8}),
  hence also the needed bounds for (tgelog x_0).
  For FKS Theorem 1.2 any valid (R) is (>.28):
  Platt–Trudgian Lemma 2 at 18 and 1000 ensures there
  is a zero in that ordinate interval, with real part
  (1/2), so (Rge 2/log1000).
  Formula (5.2) gives (A(x_0)>6cdot10^{-6}).
  At (t=1000), ((t/R)^{3/2}>1000) and
  (2sqrt{t/R}<120); the ratio of the bound to
  (e^{-t/8}) is thereafter increasing since
  (1/8+3/(2t)-1/sqrt{Rt}>0).
  The exact endpoint comparisons for these
  inequalities are in `comparison.py`.
* Consequently the corresponding intervals in
  (psi,	heta,F,U,W,S,Z) retain both signs at the
  smaller radius (d(t)) (or divided by (t)).
  The signed Abel integrals of the central-containing
  intervals cannot reduce the symmetric endpoint
  allowance, and all prime-power shifts are bounded by
  (3e^{-t/2}), in the appropriately scaled units.
  This is smaller than both (10^{-17}) and
  (.001 e^{-t/8}) for (tge169).
  The inherited or new B0 rounded log-power caps do
  not cut below these central allowances:
  (t^2 d(t)le 1.03cdot 10^{-12}cdot180^2) up to
  180 and (le .004cdot180^2e^{-180/8}) thereafter;
  for the additional small log caps beginning at 200 or
  later check the latter form at their specific starts.
  The original product and sum caps are larger still.
  The two product comparisons from (Z) use
  (e^{d(t)/t}-1ge d(t)/t); a direct B0 relative
  cap is also (>d(t)/t).

The strict radius comparison concerns the stated evaluated
bounds (including the original printed numerical tables and the
specified continuous FKS bounds), not all conceivable
reoptimizations of e.g. Dusart (3.3) or all deductive
consequences of (B_0). Adding further legal original-source
candidates is monotone for the envelope in both premise classes.
No independent blind baseline was run. For power shapes,
`sharpness.md` gives a theorem about the full deductive
comparison: an original-only proof of a D02 strength power
shape in *any one* of the four quantities would already
give the new zero restriction and hence D02 itself.
