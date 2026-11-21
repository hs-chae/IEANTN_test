# Ramanujan: positive margins, two analytic transfers, and a finite audit

Use G and RG as in the mission, with exact right-continuous pi and natural
logarithms. The main all-real conditional conclusion uses the pinned Mathlib
RiemannHypothesis. Auxiliary finite/partial-height components are distinguished
below. These are unreviewed mathematical derivations with reproducible evidence.

## Results and logical dependencies

1. Under RH, RG>0 for all log x>=38.95 using only the analytic envelope
   (no numerical sign of li-pi, numerical zero list, or finite prime-count table).
   More precisely the polynomial/exponential envelope below gives explicit margins
   on every real x in the certified cells. For L=log x>=60,
   RG >= 1 + 14/L + 142/L^2.
2. Let k=38358837682. There is a unique root kappa in (k,k+1) with
   k+0.21792636514465 < kappa < k+0.21792636514466. G(kappa)=0, and
   G(x)<0 for k<=x<kappa; G(x)>0 for kappa<x<k+1.
   Native exact-integer/rational computation is in last_real.py/out.
3. With RH, G(x)>0 for every real x>kappa, and kappa is the largest real
   counterexample to the *strict* inequality. An independent chain of evidence
   is the new C++ finite audit on [k+1,1630650286564], the independent published
   Büthe inequalities plus the analytic checker on [exp(28.12),exp(43.7)],
   and the RH analytic checker from exp(38.95) onwards. The native computation
   is not independently formalized, and neither Büthe's computation nor
   the prior Dudek–Platt sieve is rerun inside Lean.
4. Without assuming full RH, the proof gives strict positivity on
   (kappa,exp(665)], using published verified RH up to height 3e12
   (Platt–Trudgian, arXiv:2004.09765, Thm 1), and the independently
   published Büthe and Platt–Trudgian estimates specified below.
   In particular the new high window [exp(101),exp(665)] uses a centered
   Logan average and Brun–Titchmarsh to undo the smoothing. This is a
   finite-height calculation, not a new unconditional asymptotic estimate
   or a proof of RH. The gap to the large-x unconditional onset remains.

## Analytic engine: exact cancellation before checking any cells

Write n=16, z=1/L, P_-(L)=sum_{j=0}^{16} j! L^-j and
P_+(L)=sum_{j=0}^{15} j! L^-j + 4*16! L^-16. For all u>=24,
```
P_-(u) <= u exp(-u) li(exp u) <= P_+(u).
```
Proof: for t with u=log t, derivative of the difference between li(t) and
t/u sum_{j=0}^{15} j! u^-j is 16!/u^17. The derivative of C t/u^17 is
(C/u^17)(1-17/u). Thus C=16! is a lower barrier, C=4*16! an upper
barrier; both base inequalities at u=24 follow from directed Ei evaluation
in bounds.py. This is for classical li=Li2+Ei(log 2), not Li2 with
the additive constant silently dropped.

For integer m=0,...,32 let A_m=sum_{j<=min(m,16)} j! binom(m,j), and B_m
be the coefficient of z^m in P_+(1/z)^2. Let H(z)=sum_{m=4}^{32}
(A_m-B_m) z^(m-4). The first four differences for m=0,1,2,3 vanish;
H starts with 1+14z+145z^2. All omitted terms in (L/(L-1))P_-(L-1)
are nonnegative: its expansion in z is sum_{j=0}^16 j! z^j/(1-z)^(j+1).
Therefore the baseline scaled li gap is bounded below by H(1/L).
This recovers exact cancellation before enclosing any interval, instead of
separately enclosing two functions of magnitude exp(2L) as in Johnston §5.
The factorial expansion/cancellation itself is classical (Dudek–Platt
Lemma 2.1; Hassani also general coefficients, cited by Axler 2022).

Suppose eps_-(u), eps_+(u)>=0 bound the one-sided normalized errors:
pi(exp u) lies between exp(u)/u (P_-(u)-eps_-(u)) and
exp(u)/u (P_+(u)+eps_+(u)). Put R_±(u)=u^4 eps_±(u). Then for L>=25,
```
RG >= H(1/L) - (L/(L-1))^5 R_-(L-1)
             - 2 P_+(L) R_+(L) - R_+(L)^2/L^4 .
```
It suffices that the two prime bounds are available at L-1 (lower) and L
(upper); the upper count bound is nonnegative so squaring preserves it.
To certify a closed log-cell [a,b] use z in [1/b,1/a], where 1/b=0
for the terminal semi-infinite cell. Evaluate each H monomial at the
appropriate extremity by its coefficient sign. To bound the penalty
use the upper bounds on R from below, P_+(L)<=P_+(a), and the decreasing
prefactors evaluated at a. Thus a table of roughly 30 cells gives
continuous coverage, not a sampling test.

* In the RH cells use PNT.md B5 and the signed p_± as eps_±=u exp(-u) p_±.
  R_± decreasing from u>=35. To check this, v=u/2-log u >=u/4,
  v'<=1/2, so (v^2)'<=4v^2/u and v'<=2v/u. Rewrite the negative
  constant for the upper estimate by grouping the linear term as u-7
  plus a positive constant; (u-7)'<=4(u-7)/u for u>=35.
  The resulting positive bracket grows at derivative at most 4/u times
  itself (the .094/u term is decreasing). After multiplication by
  u^4 exp(-u/2) this decreases, as does 5u^5 exp(-u). The same reasoning
  works if R is further multiplied by u^2 for u>=59.
  The stronger asymptotic bound follows by factoring z^2 from the terms
  after 1+14z and bounding all negative high terms at z=1/60; then
  L^2 times the penalty is decreasing on L>=60 (first factor rewrite
  L^2 R_-(L-1)=(L/(L-1))^2 (L-1)^2 R_-(L-1)). The rational anchor and
  polynomial coefficient comparison for 142 are checked in bounds.py.
* In the Büthe cells use eps_+=0 and
  eps_-(u)=exp(-u/2)(1.95+3.9/u+19.5/u^2).
  Each term of u^4 eps_- decreases for u>=27.
  This uses Büthe arXiv:1511.02032 Thm 2 (1.9)–(1.10) and stays
  inside its window [2,10^19] at both arguments.
* In the partial-height cells the scaled error splits into an increasing
  algebraic part and a decreasing exponential part, detailed next.

## Finite-height analytic transfer, two routes

Let H0=3e12, assume all zeros with |Im rho|<=H0 are on the line as in the
published verification (no separate RH beyond that in this section). Put
c0=36, eta=c0/H0, and let U on [-1,1] have density
```
c0/(2 sinh c0) * I_0(c0 sqrt(1-u^2)).
```
It is nonnegative, even and normalized, with transform
```
K(z)= (c0/sinh c0) sin(sqrt(z^2-c0^2))/sqrt(z^2-c0^2).
```
This is the Logan kernel used in Johnston §2; an elementary proof:
average exp(c0 X+i z Z) for a uniform point (X,Y,Z) on the unit sphere.
Conditioning on Z (uniform [-1,1]) yields the displayed I_0 factor.
Rotational invariance first for real linear parameters gives
sinh(sqrt(c0^2+r^2))/sqrt(c0^2+r^2); replace r by i z by the entire identity.
Set T=eta U. Averaging psi(xe^(T+s)) for s=0,±eta applies the factor
K(eta(gamma-i beta)) exp(rho s) to the zero term x^rho/rho.
Derivation uses the integrated formula and integration by parts on the
compact interval in log x, including endpoints in the test weight.
This average is legitimate even when an endpoint is a prime power;
the weight has no atoms. The resultant zero sums converge absolutely.

For gamma real with |gamma|>H0, write z=u+i v with |u|>=c0, |v|<=eta
using 0<=beta<=1, and w^2=z^2-c0^2. Then
```
|Im w|^2 = (sqrt((u^2-v^2-c0^2)^2+4u^2 v^2) - (u^2-v^2-c0^2))/2
          <= v^2+c0 |v| < (.000022)^2.
```
For the middle inequality differentiate in u^2 to see it decreases, or
use the square-root formula at |u|=c0. Also
|sin(w)/w| <= exp(|Im w|) min(1,1/|w|), including at zero;
for |u|>=2c0, |w|>=|u|/2. For low zeros use the positive probability
measure and hence multiplier <=exp(eta) for |s|<=eta. The N-count low
sum from PNT.md gives exp(eta) sum_{0<|gamma|<=H0} 1/|gamma|<116.
This upper bound is not a retrieved sum over individual zeros.

**Shifted bracket.** Take s=±eta to bracket psi(x).
For t in the support at x>=3, the nonzero constant/trivial terms
of the explicit formula have magnitude <1.9. The smooth main term
differs from x by at most x eta exp(2eta), using E(s+T)=s and
that each bracket displacement has constant sign. For high zeros split
at 2H0, counting <=2N(2H0)/H0 on the first part and using the Laurent
tail estimate in Lee–Nosal (11) on the second. The total relative
high error is at most
```
exp(eta+.000022)*(c0/sinh c0)
  *[2 log(2H0)/pi + log(2H0)/(pi c0)].
```
Added to the main shift this is <eta0=1.24e-11 (bounds.py).
Thus |psi(x)-x|<=116 sqrt(x)+eta0*x+1.9 for x>=3.
Since 0<=psi-theta<1.00000075 sqrt(x)+3 x^(1/3) by
Platt–Trudgian arXiv:1407.1914v1 Cor. 2, for log x>=12,
|theta(x)-x|<=118 sqrt(x)+eta0*x.

Apply Abel summation with anchor A=exp(12). The correction
pi(A)-li(A)-(theta(A)-A)/12 has magnitude <82: both quantities
being subtracted are negative by Büthe Thm 2 and their magnitudes are
bounded separately by 82. For u=log x>=12 the two integrals are bounded
by 3 sqrt(x)/u^2 and 1.2 x/u^2, respectively, by differentiating
sqrt(x)/u^2 and x/u^2 from A. Thus a normalized two-sided bound is
```
eps_shift(u) = 118(1+3/u)e^(-u/2) + eta0(1+1.2/u) + 82u e^(-u).
```
For the certificate use on [a,b] the exponential terms in u^4 eps
at a (decreasing there), and algebraic terms at b (increasing).
This gives the full window [exp(42),exp(407)] with no huge grid.

**Centered, undo smoothing with BT.** For s=0 the high zero term
is smaller than the preceding tail bound: split at H1=1.05 H0.
For the near part
```
2[N(H1)-N(H0)]/H0 <= .05 log(H1/(2pi))/pi + .56 (log H0+log H1)/H0.
```
For the distant part |w|>=.3 eta|gamma|, and from LN (11) its
summed coefficient before the common kernel constants is at most
log(H1)/(.3 eta pi H1). The total of near and distant is <1.25.
Also main averaging error is <=x eta^2 exp(eta)/2 since E(T)=0.
Combining these two errors gives <2.2e-14 x. As before low errors are
<116 sqrt(x) and trivial/constant <1.9.

To control theta(x)-E theta(xe^T), the positive and negative halves of
the shift have opposite signs, so bound by the larger of the two
half-expectations. Use explicit Brun–Titchmarsh
pi(y+h)-pi(y)<=2h/log h for h>1 (Montgomery–Vaughan,
as applied with this normalization in CMS arXiv:1708.04122 §6).
For t=|T|<=eta let t0=1e-15 and take the interval at max(t,t0);
it contains the original one-sided interval. Its length h is
>=x t0 exp(-eta), <=x exp(eta)(t+t0), so for L>=100 it exceeds 1
and log h>=L-35. Each prime in that interval contributes at most L+eta.
By symmetry the expected half-absolute shift satisfies
```
E(T_+)=eta I_1(c0)/(2 sinh c0) < .066 eta,
```
from integrating u I_0(c0 sqrt(1-u^2)) or its nonnegative Bessel series.
This constant is checked in bounds.py via a finite rational sum and tail.
Therefore each half weighted error is
<=2x exp(eta)(L+eta)/(L-35)(.066 eta + t0/2)
<=1.59e-12 x L/(L-35). Subtract E(psi-theta)(xe^T) using
the Platt–Trudgian upper bound (cost <1.01 sqrt(x) here), so
```
|theta(x)-x| <=118 sqrt(x) + d(L) x,
d(L)=1.59e-12 L/(L-35)+2.2e-14, L>=100.
```
For the same Abel transfer keep this stronger pointwise bound, but for
the integral use the shifted bound valid from the anchor A. Thus
```
eps_center(u)=118(1+3/u)e^(-u/2)+ d(u)+1.2 eta0/u+82u e^(-u)
    (u>=100).
```
For u^4 eps, the two algebraic terms are increasing from u=100 because
d/du [u^5/(u-35)]>0 and the other terms are positive powers; the
exponential terms decrease there. This handles both L and L-1 on
[101,665]. The improvement over the shifted method is removal of
the full support-length cost in x; BT pays the first moment of half
the centered kernel. This uses the same verified height as Johnston,
not an extrapolation of his table.

## Native finite interval and last real endpoint

For each closed cell [a,b] of the integer mesh in finite_ram.cpp,
the sufficient exact inequality
```
E * a * pi_floor_lower(a/e) > upper_Qlog(a) * pi_upper(b)^2
```
uses fixed-point units Q=2^48, E/Q<=e, and log(a)<=upper_Qlog(a)/Q.
The terms e x/log x and pi(x/e) are nondecreasing for x>=e, so
the inequality at the mesh bounds implies strict positivity throughout.
Prefix counts are obtained by a segmented sieve counting every odd
candidate given the least-factor composite test. The small-prime
presieve merely marks multiples of 3,5,7,11,13; those primes themselves
are restored when contained. Coarse counts use grid_floor(floor(aQ/(E+2)))
for the lower pi and grid_ceil(b) for upper pi. Failed coarse cells
are merged and re-sieved; tests are then at the left endpoint and every
prime in the remainder of the closed interval, which is sufficient
even when pi(x/e) jumps in the meantime. The denominator logs use a
20-term atanh expansion with upward rounded fixed-point products;
for the common coarse grid use the tangent log a<=log a0+(a-a0)/a0.
All main comparisons are in uint128: E<2^50, n<2^41 and pi<2^36
(guarded on the computed table), so products on the left fit in 127 bits
and those on the right with the log guard fit in 126 bits. Prefixes and
floor divisions likewise fit their declared integer types.
The integer minimum certificate is obtained by taking
floor((E*a*py-lx*px^2)/lx) for each accepted coarse cell or fine jump,
where lx=upper_Qlog(a); the same sufficient inequality bounds G below
by that quotient everywhere on the cell. Integer-only invocation and
exact results are in finite_ram.out.
All cells are covered including the last endpoint. This replaces the
Dudek–Platt table plus about 5.3e8 floating stepping checks, both by
a much smaller required sieve and a directed-arithmetic all-real test.
It remains native-assisted: compiler behavior and full C++ semantics
have not been formally connected.

last_real.py is separate, uses exact quotient prime counting, never
uses the segmented prefix table. For n>=2 include all v in {floor(n/i):1<=i<=n} in a descending list.
The Python list can also include a redundant near-sqrt key; division
of that key by p>=2 lies in the small-integer portion of the list.
Initialize counts v-1 and process p<=floor(sqrt(n)) in increasing order.
At p prime remove composite values whose least prime factor is p;
their quotients by p are surviving numbers q>=p. This yields
S(v)-=S(floor(v/p))-S(p-1), v>=p^2, traversed decreasing so the RHS
is from the prior stage (floor(v/p)<v). At each stage the difference
S(p)-S(p-1) detects p prime, because smaller least factors have
already been removed. All floor-division queries are in the quotient
domain, and it includes integers up to floor(sqrt n) since the
quotient chain crosses them without skipping. The least factor of a
composite is <=sqrt(n), proving the mathematical algorithm. Logarithms
use range-reduced atanh with the omitted positive tail bounded by
a geometric series; e uses the positive exponential Taylor series.
On [k,k+1], floor(x/e)=14111427770 everywhere. On [k,k+1) also
pi(x)=1644673232, so the strict increase of
g0(x)=e x/log x * 632207037 - 1644673232^2 gives the unique root.
For the right bracket near k+1 the audit uses the continuous
extension of this branch; no claim about pi(k+1) is needed for this step.
Finite_ram tests k+1 independently. Monotonicity and bisection give
the stated rational enclosure, not just sampled sign.

## Comparison to primary literature and residual questions

* Dudek–Platt arXiv:1407.1901v1 Thm 1.3 is a known last **integer**
  result under RH, with analytical Lemma 3.2 at 1.15e16 and a large
  sieve in §3.1. Our RH-only envelope begins later than their route
  that uses sign information and computation; the Büthe bridge
  begins much earlier and the new C++ check is independent of their
  table. Calling their known theorem new is incorrect.
* Platt–Trudgian arXiv:1809.03134v2 Thm 2 as written uses
  38358837682 < x <= exp(58) as a real range. This cannot be literally
  true near the lower endpoint: the exact audit exhibits a real
  negative region there, and the branch just right of that integer is
  continuous. Axler (2022) pp. 1149–1150 and Johnston Thm 5.1 use the
  safe integer lower bound 38358837683. No conflict with those statements.
* Johnston arXiv:2109.02249v2 Thm 5.1 achieves the finite window to e^103
  with short numerical grid cells and several Thm 4.1 constants. The
  present e^665 window is a mathematical extension relative to that
  explicit range with an exact rational envelope verified on larger cells.
  We did not treat his finite-height `a,K` table as valid outside its
  conditions or use unverified high zero sums.
* Axler (2022), doi:10.7153/mia-2022-25-71 Thm 1.1 gives a different
  unconditional range x>=exp(3158.442). We do not bridge the gap between
  our upper endpoint and such an asymptotic unconditional range. The
  shifted and centered smoothers have a nonvanishing relative-error
  floor, so merely extending their cell table would eventually fail.
* Main auxiliary analytic inputs (zero count, integrated formula, finite
  RH computation, Büthe, BT) are not Lean formalized here. Numerical
  rational arithmetic and program semantics are separately documented;
  they do not by themselves certify the input analytic theorems.


The directed illustration in comparisons.out checks that the lower
envelope obtained by using only independent two-sided Schoenfeld errors
(at both x/e and x, with exact analytic li) is below -.284 at L=38.95.
Thus that particular two-endpoint envelope cannot certify this onset;
no statement about its actual sign or other methods follows from this
negative lower estimate. The shifted and centered templates likewise
fail their positivity test at L=409 and L=700 respectively.


For the local positive envelope just right of the crossing, the slope of
the continuous branch is e*632207037*(log x-1)/(log x)^2 on [k,k+1],
which is decreasing there as a function of log x. Directed bounds at
the two endpoints (comparisons.py) place this slope strictly between
67,600,000 and 67,700,000. Thus
```
67600000*(x-kappa) < G(x) < 67700000*(x-kappa),  kappa < x < k+1.
```
The factorization k+1=2521*15215723 shows it is composite as well, so
the same branch in fact connects continuously through the endpoint
k+1. The native test includes that endpoint independently. The native run
certifies G(x)>=10,786,299 on [38,358,837,683, 1,630,650,286,564]. This
local envelope complements the directed integer lower bound across
the next finite interval and the RG envelopes on the analytic cells:
the positive all-real conclusion is not just an integer-rounding claim.

Equivalently the exact root is exp(-W_{-1}(-e*632207037/1644673232^2)),
where W_{-1} denotes the inverse of w->w exp(w) for w<-1.
No numerical evaluation of Lambert W is needed.
