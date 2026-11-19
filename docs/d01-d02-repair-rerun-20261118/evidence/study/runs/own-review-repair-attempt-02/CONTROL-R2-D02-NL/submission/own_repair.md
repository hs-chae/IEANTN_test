# D02 own-review continuation: conformance and additive improvements

Read this file together with candidate.md, repair_spectrum.md and
repair_applications.md. All old valid branches and evidence remain;
combine lower profiles by maximum and upper profiles by minimum
over their actual domains. Trust tier is B0 (the seven originals)
or B0 with the exact PsiMajorant of INPUT_CONTRACT.json, as marked,
plus written proof and ordinary deterministic interval/integer
certificates. Not Lean, source-first PV, or a new independent review.

## Closure of the actual x-mode defect

Own review identifies `R-code-x-mode` at the old
repair_evaluate.py:31–39, trigger `x 1e70`. The old x-mode CLI
took the nondegenerate log interval I(log x) and multiplied an
already scaled Horner slice by another L^4. Its reported endpoints
exceeded 737 million when the actual scaled R was below 1.1.
The same error was not present in the point-log branch. The erroneous
implementation and its claim are superseded, not used in any ray
certificate. The exact pre-edit bytes are in before_own_repair.zip.

Let c_j be the projected **positive** coefficients in the continuous
tail, and p(L) its unscaled nonnegative penalty, including the
negative projected coefficients. For every real L in the computed
log enclosure U with inf U>=141, the normalized profile in
x^2/L^(k+2) units, after dropping the terms of degree below k, is
```
    sum_{j>=k} c_j L^(k-j) - L^k p(L).
```
Therefore the implementation is precisely
`horner(c[k:],1/U) - U**k * cost(U,cap,high)`, using the
**same** path for point and nonpoint interval arguments.
For the evaluator k=4. The cost in repair_r.py is the one proved in
repair_applications.md, with the same guarded real domain for the
shifted argument. Each use of Decimal arithmetic in this expression
goes through intervals.py: elementary operations have outward
rounding and the exponentials/logarithms use neighbors of the
correctly rounded value. Composition thus encloses the expression
for every L in U, without any assumption that it is monotone in U.
Taking the maximum of lower endpoints of individually eligible
profiles is lawful. R1 is a different expression, not a Horner
slice: its two positive-count brackets are in x/L units and it
really does need L^4 multiplying the entire expression.

fixed_x_check.py actually invokes the repaired CLI in the failing
x mode. Its opposite enclosure uses the upper normalized count
at L-1 and the nonnegative lower normalized count at L, with
the original count error estimates. It asserts nondegenerate U,
both lower endpoints between 1.09 and their respective upper
endpoints, and both upper endpoints below 1.1. It also checks
a separately evaluated, explicitly unscaled polynomial (including
leading zeros) for both polynomial orders and three slice indices.
The numerical regression complements, and is not a substitute for,
the interval identity. No implication about the old claim is inferred
from running only a point-log test. The executable is a decimal
illustration on arguments for which its analytic enclosures and
Decimal operations evaluate, not an arbitrary-precision library.

Also corrected the medium Mertens conversion in certify.py: its
bound is q*exp(q/L^3) with q=(z+L^2 e^(-L))/(1-e^(-L)).
The denominator stays in *both* occurrences of q. The full
certify.py replay, including that fix, has byte-identical output
to analytic_run.txt. No middle-ray constants change. Imported
finite_mertens.py no longer interprets the parent program's x/log
CLI arguments or changes its interval precision at import. Its
standalone sweep still uses precisely its original precision and
argument convention. Tested actual x-mode calls below 2 and at 2.
Old plotted wording about R2 continuity stays withdrawn; the
historical jump at L=32 and the separate continuous fixed-anchor
tail are unchanged. All other qualified review objects are retained.

## Stronger common spectral lemma: retain the logarithm

Use H, ell, p, q, G=G_s, C as in spectral.md (original density
source: Dusart2018 PDF p.5 Theorem 2.3). For t=H exp(y), y>=0,
set
```
Z(y) = (G/2) exp(-(1-p)y) (1+y/ell)^q.
```
The bound on 2 N_s(t)/t is **2 log(1+Z(y))** plus
C exp(-y)(1+y/ell)^2. Since 1-p-q/ell>0 on the entire strip
s>=.77 used here, Z(y)<=G/2. Integrating z/(1+z) over [0,Z]
shows `2 log(1+Z) <= 2Z - Z^2/(1+G/2)`.
To obtain a directed upper enclosure of an integral of the
logarithmic majorant, compute the previous upper moment bound
for 2Z and the second term, and subtract a **lower** moment bound
for the correction. In detail:
```
 correction integral >= G^2/(4+2G) *
    integral m_A(y) exp(-2(1-p)y)
                  sum_{n=0}^6 binom(2q,n)(y/ell)^n dy .
```
For the undamped bound m_A=1. Otherwise m_A is the same
nonnegative piecewise multiplier (repair_spectrum.md). Taylor
with positive seventh derivative, since 6<2q<7 on this strip,
proves the lower polynomial. The upper Taylor polynomial of
degree four for 2Z uses negative fifth derivative as before.
The exact gamma integrals and shifted damped tails are the ones
in repair_spectrum.md. If using the old linearized undamped
majorant as a second option for the term being corrected, it
bounds the integral of 2Z plus the second term too, so the same
correction can be subtracted from either. No subtraction of an
upper bound in place of a lower bound is used.

At fixed y, log(1+exp(B_s)) is convex in the affine real function
B_s=log Z(y), and decreases with s; the second density term is
independent of s. Thus its integral is decreasing and convex
also, including when multiplying by a nonnegative damping
multiplier. Prefix minima of upper node enclosures keep every
node valid by monotonicity. Chords and the transition clipping
of repair_spectrum.md still apply to the *true integrated
majorant*, not to the Taylor correction. Since the clipped
majorizing nodes decrease, their layer excess has the same
nonnegative mixture and all tail-derivative arguments from
repair_spectrum.md apply. For the default width the new first
node is below the old one, so U(140)>2M(.77); for the fixed-width
proof we do not require this inequality. Define E_log by using
these new nodes in the same secant-layer formula. At a fixed
width the unscaled E_log is nonincreasing, and e^(a L) E_log
convex. For the default scaling use precisely the same monotone
domains as the old secant (no change to the smoothing bias).

For fixed h also improve the full positive high-frequency
weight used for clipping and for the two symmetric base terms.
Let A=2/(Hh), w(t)=min(1/t,2/(ht^2)), and write the FKS original
PDF pp.4–5 Lemma 2.1/Remark 2.2 count as J(t)+an error bounded by
R_N(t)=.137 log t+.443 log log t+1.588. The smooth main term has
J'(t)=log(t/(2pi))/(2pi). The high count including a possible
atom at H is bounded by J(t)-J(H)+R_N(t)+R_N(H), taking a limit
from the left at H. Stieltjes summation with -w' now gives the
upper bound
```
 integral_H^infty [ log(t/(2pi))/(2pi) ] w(t) dt
          + (2 R_N(H) + .137+.443/ell) min(1,A)/H .
```
Indeed R_N'(t)<=(.137+.443/ell)/t and
w(t)<=w(H) H/t. Under t=H exp(y) the main integral has integrand
(ell-log(2pi)+y)/(2pi) times min(1,A exp(-y)). Integration at
max(0,log A) is exactly log_layer.weight. All finite h in
second_m.WIDER meet 0<h<=.1; this bound is for the undoubled
full high weight as required in (S). This uses no new estimate
for zero phases, nor the possibly ambiguous FKS Table 8
parameter authorization. The improved constants use the
original theorem before discarding its logarithm.

## Ramanujan: added margins, matching comparison, exact endpoint

For the same strict profile (R3) of ramanujan.md, the new default
E_log may replace E_sec in the jbound of repair_applications.md.
The new pointwise polynomial is strict at L>=141 with either
N=30 or 64; the scaled monotonicity/derivative check for the
whole-ray certificate is unchanged. second_r_run.txt gives
**every** order 6–62 at m=d_k on closed real rays. Enclose the
fixed anchor at 128 again, keep the negative polynomial
coefficients as penalties, and check the analytic monotonicity
hypotheses at the final left point rather than assuming
bisection is sound without that check. For k=6–12 the
compact_r_run.txt rows give additional earlier finite joins.
Selected best onsets after both checks:

| k | B0 | D02 |
|---:|---:|---:|
|6|216.14|184.94|
|7|249.2|209.48|
|8|283.33|234.78|
|9|318.15|260.63|
|10|353.43|286.87|
|11|389.01|313.38|
|12|424.83|340.08|
|62|2255.7|1711.6|

For the compact check only, extend the **unscaled** J upper bound
by taking the minimum with E_log at all WIDER fixed widths and
CH2 Corollary 1.3 (original PDF p.3), always adding the same
primitive and transient. Then every term of the positive penalty
is nonnegative and nonincreasing: the fixed-width secants and CH2
bounds are nonincreasing, so are primitive terms divided by v,
v e^(-v), T(v), remainders and P_N on these domains. The minimum
of the J bounds therefore does not increase. On a closed slab
[l,r] the sliced positive polynomial is bounded *below* at r,
and L^k p(L) bounded *above* by r^k p(l). This suffices throughout
the slab even though the fixed-width bias is not decreasing after
multiplication by L^k. Compact slabs of width .01 end at the
new default-ray onsets, checked independently. At fixed log onsets
190,225,250,300 take the best of the two new checks:
B0 coefficients 63,847,1076,120349 respectively, versus
D02 full 145,1412,13985,145450. The compact check of a fixed row
joins after three log units to the default certificate; it is
not claimed to beat the default at every onset.

For the designated R1 profile, allow E_log on the same menu
for both caps at eligible arguments. Its unscaled value cannot
increase when the cap is shortened: all common clipped panels
and the base weight are identical within a given width, and
the integral of weighted positive right excess on the deleted
panels is nonnegative. The same reasoning works for the default
layer. The stronger pointwise comparison for psi below now
shows a strict gain in (R1) from L>=166.1, using the upper
bracket there and nonincrease of the uncertainty at L-1.
The positive normalization and subtraction of the common prime
power term are as in ramanujan.md. The added finite box menu
does not invalidate the old fixed-onset B0 uncertainty barrier:
second_m.separation checks the last node >.004 at those widths
below .008 exp(-189/8), while at any larger width its bias suffices
for v>=189. Thus the original obstruction for the selected B0
R1 comparison formula still applies; it is not an upper bound
on true R or a limit on all B0 proofs. The envelope max inherits
everything, without a claim of strict improvement at points
where a different profile controls that max.

The exact terminal sign threshold is unchanged, and only the
old large integer result is inherited. root_zoom.py repeats the
finite distinct-floor prime counts and refines the strictly
opposite signs around the unique root to the open bracket
```
38358837682.21792636514465772878464871678638
  < r <
38358837682.21792636514465772878464871678639 .
```
It does not alter the open endpoint for strict positivity or
the included equality for the nonnegative bound. Locally for
x in [n,n+1], retain the exact R expression in ramanujan.md.
The older B0 early margins (including 30.716 and 47.0194)
and their connected quantitative domains are unchanged.

## Mertens: added power and finite branches

The errors are exactly the four in mertens.md: relative products
with e^gamma L or its reciprocal, and centered 1/p and log(p)/p
sums with the exact Dusart constants M and B_3. In the signed
formulas (M1)–(M2), add pointwise E_log, its default plus all
WIDER fixed choices for each cap, combined with the same
primitive, signed prime-power corrections and exponentiation.
Keep every applicable old bound. For uniform outputs use
C x^(-a)/L for the first three errors and C x^(-a) for the
weighted sum, strictly on closed real rays. The analytic
coefficient is the old allowance of repair_spectrum.md plus
e^(aL) E_log; apply the same product-safe conversion. Here are
new rows; second_m_run.txt has the full reproduction:

| L onset | C (B0, a=1/8) | C (D02, a=5/32) |
|---:|---:|---:|
|17|.01239|.22775|
|190|.01239|.2200|
|200|.01218|.21150|
|250|.010496|.181831|
|300|.009578|.166055|
|400|.008636|.149754|
|600|.007862|.136335|
|1000|.007337|.127204|
|2000|.006986|.121110|
|10000|.006726|.116580|

The limiting coefficients of the new default majorants are
<.0066610 (B0), <.1154620 (D02). These limits include the
primitive allowance and are not theorems claiming those exact
strict constants on every ray. For the rows not purely default,
choose one h for a whole log slab of width .125. Mertens power
normalization makes E_log and the positive allowance convex
for this fixed choice, so the larger endpoint normalized
coefficient bounds the slab; for exponential conversion,
evaluate the remaining monotonically decreasing factor e^(-aL)/L
at the left endpoint. The selected menu is finite and both values
are outwardly checked. Default rays at the terminal slab
endpoints close the compact joins. From L=17 to 32 the previous
B0 inverse-log coefficient .117 gives the normalized bound
.117 e^(aL)/L^2 for all four, increasing there by a>=1/8.
From 32 to 185 (B0) or 166 (D02) use CH2 Corollary 1.3 at H
and the following normalized majorant:
```
(pi/H)e^(aL) +115 exp(-(.5-a)L)+21/H+3 exp(-(1-a)L).
```
Indeed the earlier 1.111 e^(-L/2) bound on U_1, the inequalities
D_0<=U_0<=U_1/L, and (1+1/L) times (P) add at most
1.215 e^(-L/2)+(21/H)e^(-aL)+3 e^(-L) to the CH2 error
before power normalization. This covers all four. The displayed
coefficient is a convex positive sum of exponentials; the larger
value at the endpoints and conversion at 32 prove the complete
middle joins, not just integer L. The earliest lengthened power
rays are representational tradeoffs: earlier pointwise minima
can already be substantially smaller. Their matched uniform
ratio is (.22775/.01239)exp(-L/32), crossing 1 at
32 log(.22775/.01239) in (93.16,93.18). From L=200 the
stronger ratio (.21150/.01218)exp(-L/32) is <.03353 and
decreases on the entire matched ray.

For the selected all-point dominance beginning at L=166.1:
retain the original two-piece B0 endpoint barrier. New fixed B0
choices with h>=2.1e-12 have bias at least 1.05e-12; at
smaller h the new last-node coefficient is checked >.0016.
The default coefficient is larger as well. Hence on [166.1,168]
the barrier is at least the CH2 finite-height floor (even using
the full verified height); the old thresholds at 168 suffice as
their exponential comparison only improves by decreasing L.
At L=166.1 and 167 the D02 fixed choices 1.05e-12 and 1e-12
respectively give total bounds <1.044e-12 after allowances and
conversion, in units 1 or 1/L. Each applies respectively through
167 and 168 by unnormalized monotonicity (including the absolute
allowance and relative conversion for that fixed width). From
168 onward the new .22775 row is below the constant and power
parts of the barrier, by the checked comparisons at 168 and the
decreasing ratios. The previous proof for the opposite signed
endpoints, including the small prime-power and log-product
conversion corrections, applies with more than the required
slack: see repair_spectrum.md and mertens.md. New simple B0 rows
also remain above the barrier where eligible; added finite
branches expire well before 166.1 when considered as arithmetic
prefixes, and their uniform inverse-log rays exceed the barrier
by the same decreasing relative comparison. This is pointwise
separation of the explicit analytic estimate envelopes, not
a lower bound on observed errors. Source comparisons retain
all eligible original tables, CH2 choices and nonnegative
transfer tails on matched domains, as in sources.md. The B0
comparison is a within-proof cap ablation, not a separate
blind run. The shorter exponent in the bounds for D02 is due
only to the input-implied cap, not to changing an original result.



The earlier small-x power onsets in power_prefix_monotone_run.txt
use an independent finite join with the same C as the L=17 row:

| tier | C | closed onset for P, Q and sum 1/p | closed onset for weighted sum |
|---|---:|---:|---:|
| B0 | .01239 | 356197 | 367949 |
| D02 | .22775 | 293 | 307 |

These are sufficient real x onsets. The smaller exponents'
different constants trade off against one another as above;
the early D02 analytic-power bound is not asserted to beat a
direct exact finite calculation.
For each tier and component, inspect the actual post-update prefix
at a prime p and the left limit at the next prime q. On [p,q) the
raw prefix values are fixed. If c=Q_raw exp(-gamma) and the signed
unscaled errors are e_P=L/c-1, e_Q=c/L-1, e_R=A-log L-M
and e_W=B-L+B_3, the derivatives of their signed power-normalized
values, divided by e^(aL), are
```
 (aL+2)L/c-(aL+1),  a(c-L)-1,
 (aL+1)e_R-1,       a e_W-1 .
```
Interval evaluation on the entire log slab determines
monotonicity when a derivative has one sign. Then the absolute
maximum is bounded at the two endpoints. Otherwise evaluate the
whole log slab directly. The actual q is accounted for by the next
post-update prefix, or by the join at the next prime 500009.
From that prime through exp(17)<25000000, use the older prime-event
maxima for x>=500000 (each <=.370099). Both one-sided endpoint
checks are within the old maxima range from 500009 onward, so
the earlier derivative proof in finite.md includes every such slab.
Convert via .370099 exp(aL)/L^2, whose maximum on this log interval
is bounded by the larger of its values at log(500000) and 17
(the derivative changes sign only from negative to positive).
Then join to the L>=17 rays above. A preliminary scan used only
raw interval widths; a join phrased at the nonprime 500000 was
superseded by the actual succeeding prime. Endpoint derivative checks
tightened the slab estimates without moving the final prime onsets. Only the final
monotone run with the 500009 join supplies the earlier onsets.
This finite component is common arithmetic; the D02 premise is
needed for the stronger large-x exponent, not for the prefix counts.

### Extended B0 finite joins

The next table gives strict bounds in C/L^3 units for P, Q and
the reciprocal sum, and C/L^2 for the weighted sum. Onsets are
closed real x, not log x. These rows require no D02 premise.

| C | P | Q | sum 1/p | weighted sum |
|---:|---:|---:|---:|---:|
|.081|30971648|30971648|30971648|33930112|
|.08|30971904|30971904|30971904|33931904|
|.075|33932672|33932672|33932672|40881408|
|.07|40881536|40881536|40881536|45946496|

The algorithm is that of the earlier closed-block computation:
sieve exactly through 100000000, build the three increasing
raw prefixes from 2, then enclose each raw quantity between the
pre-block entering prefix's lower endpoint and the post-block
exiting prefix's upper endpoint. Propagate with the interval of
*all* L within the closed block, including the reciprocal for P.
There are no skipped blocks from 30000000 through 100000000,
each of width 128 in x, each including both endpoints.
The first block meeting a sufficient strict condition after the
last unproved block begins at that last block's right endpoint
and rechecks it independently. The sieve count is 5761455
and its bitmap hash is recorded by second_finite.py. The
original normalizer receipt, with enclosures independent of x,
is used verbatim. The final maxima caption in the new stdout is
a legacy label; the loop actually starts at 30000000, not at
25000000, and maxima are not used for the onsets.

At L=log(100000000) the earlier decreasing analytic coefficient
formulas (repair_spectral.finite_tail with this new join argument)
give upper bounds .063635804 for the first three and .066387896
for the fourth, both below .07. Their monotonicity is exactly
that for the 60-million join, verified on L>=17 through
log(10^13) in mertens.md and repair_applications.md. The old
later pieces have coefficients below .002 and .00008, respectively.
This proves the new rays to infinity. In particular the finite
branch that previously did not reach .08 for the weighted sum
does so now, and .07 holds simultaneously from 45946496. On this matched
ray that is .35 times the direct Dusart coefficient .2 for each
of the first three errors and 7/30 times .3 for the fourth.
The pointwise minimum still retains all other source transfers.
At any specific real x<=100000000, finite_query.py uses
the exact prime set up to floor(x) and outward normalization
to add the corresponding pointwise bounds. An arithmetic
pointwise branch need not have the conservative uniform block
constant. Earlier onsets at these smaller constants may require
resolving one-sided prime events or root crossings within the
last unproved blocks; none of those last blocks is declared an
arithmetic counterexample. No new finite-height zeta computation
is needed for these improvements.

## Attempts and remaining limitations

The nonlinear count gain is only of order the normalized
density at the endpoint, so it improves constants and some
profiles but not the exponent. The hypothetical direct input
still permits boundary zeros; the explicit-formula majorants
do not establish phase cancellation. Trying only optimized
widths cannot replace the limiting cap constant, and using
a fixed h in the analytic infinite tail would leave a bias.
Choice of widths is not optimized globally. Tried to use
FKS Corollary 2.9/Table 8 (PDF pp.7, 26) as a smaller density
constant; its displayed optimization uses delta below 1
despite Theorem 2.7's parameter line in the pinned extraction.
No branch here uses that potentially mismatched table, and
no outside source was used to resolve it. The nonlinear
Dusart correction avoids that dependency. At high Ramanujan
orders compact fixed-width joins can even lose to the default
certificate because of the interval penalty and the widely
separated scales; we keep both. No quantitative full-margin
claim is inferred from finite sampling, and no global best
possible constants or thresholds are asserted.
