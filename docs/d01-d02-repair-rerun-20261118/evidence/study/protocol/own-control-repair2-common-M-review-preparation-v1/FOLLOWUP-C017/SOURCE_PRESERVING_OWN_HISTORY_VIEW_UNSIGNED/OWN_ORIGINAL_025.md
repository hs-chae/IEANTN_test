# Application upgrades in the repair continuation

All conventions in ramanujan.md and mertens.md are unchanged. This
supplement adds branches; it does not substitute a weaker statement
on any domain. In particular the exact terminal Ramanujan sign ray
is unchanged (including the inherited early integer-computation trust).

## Ramanujan: early compact joins and high-order strict real rays

With the normalization (R3), the following earlier B0 onsets replace
the previously listed **sufficient** early onsets for the same
margins. The right column remains a valid join used in the proof.

| k | m | improved log onset | old log onset |
|---:|---:|---:|---:|
|4|0|28.1102|28.14|
|4|.1|28.2814|28.30|
|4|.25|28.5606|28.58|
|4|.5|29.1022|29.12|
|4|.75|29.7846|29.80|
|4|.9|30.3014|30.32|
|4|1|30.716|30.74|
|5|8|32.2178|32.24|
|5|10|44.8948|44.92|
|5|12|45.7624|45.78|
|5|14|47.0194|47.04|

Each join verifies the same R2 interval formula on **each closed
slab** of width .0002 from .08 before the old onset to that onset;
discard slabs through the last one not certified. The applicable
source guards are those in profiles.py and ramanujan.md. The proof
of the remainder does not change at the finite joins, and the old
tail certificate covers everything beyond the right endpoint.
These improvements require no D02 hypothesis.

For the high profiles use the new secant layer in the tail penalty
of ramanujan.md. Replace the spectral input there by
min(E_h,E_cont,E_sec), where h=e^(-v/4). Still use the basic (P)
upper bound, the same one-sided prime power estimate and absolute
anchor residual upper. For 6<=k<=29 continue with N=30. For
30<=k<=62 use N=64 and anchor 128: the unnormalized anchor residual
is in (0,6*10^7) by the same convergent V series. Hence the
normalized upper remainder is
```
r_64(v) = 6*10^7 v e^(-v) + (128/62) 65! / v^65.
```
The lower remainder is strictly positive, and the upper follows by
the derivative comparison in ramanujan.md. For N=64 the projected
coefficients are now carried through degree 128, keeping the positive
ones and charging the negative ones to the penalty. The code checks
the required coefficient signs and anchor enclosure exactly/outwardly
with integer or Decimal interval arithmetic.

For clarity, the unnormalized positive penalty used here is
```
p(L) = L/(L-1) [J_up(L-1)+T(L-1)]
       + [2P_N(L)+J_up(L)+r_N(L)] [J_up(L)+r_N(L)]
       + sum_j max(0,-d_j^(N))/L^j
J_up(v) = min(E_h(v),E_cont(v),E_sec(v)) +
          (6/v)[.1 exp(-v/2)+20 exp(-av)/H+2 exp(-v)]
          +17000 v exp(-v).
```
It yields the strict lower profile x²/L² times
[sum_j max(0,d_j^(N))/L^j minus p(L)]; N=30 or 64 both valid on
L>=141. This particular tail profile is continuous: all three spectral
bounds in its minimum are continuous in v, the anchors are fixed, and
the formula has no finite domain switch there. The old R2 profile
on its earlier domains is valid but is not continuous.

To certify a whole closed ray in (R3) with m<=d_k, compare the penalty
times L^(k+2) with the remaining positive allowance as in ramanujan.md.
For L>=141 with L-1>=(k+6)/a, use the scaled monotonicity of all
three E terms (including the new lemma in repair_spectrum.md).
All negative coefficients kept in the penalty have degrees >k+2,
as checked at each comparison. The anchor correction has degree
N+1>=k+2 and an exponentially decreasing part under this scaling;
the factors L/(L-1) are decreasing and the prime power term with
v² is covered. The positive allowance has derivative >=0 once
the derivative test in repair_r.py passes at the left endpoint:
the sum in that test decreases with L. The strict comparison
therefore proves the claim everywhere to infinity, including the
onset. The bisection is just a way to locate sufficient onsets,
not used to infer any failed arithmetic inequalities.

The full certificate table (repair_r_full_run.txt, rows beginning
`full`) gives each exact d_k and both onsets for k=6 through 62.
Extracts, all with m=d_k:

| k | B0 log onset | D02 log onset |
|---:|---:|---:|
|6|216.2|185.3|
|7|249.3|209.7|
|8|283.4|234.9|
|9|318.2|260.8|
|10|353.5|287|
|16|569.4|448.1|
|29|1046.4|806|
|59|2145.3|1628.9|
|62|2255.7|1711.7|

At the original four fixed onsets (190,225,250,300) and
orders (6,7,8,9), the refined B0 coefficients are respectively
60, 847, 1062 and 120324. D02 still gives the full coefficients
145, 1412, 13985 and 145450. The selected B0 spectral-certificate
obstruction in ramanujan.md remains valid: the new B0 term by itself
is at least .0066 exp(-v/8), above the old .004 exp(-v/8) barrier.
There is no arithmetic upper bound asserted there. More generally
the displayed penalty gives a sufficient coefficient at any fixed
new onset passing the same derivative test and monotonicity
hypotheses, capped at d_k for this whole-ray shape.

In (R1) or (R2), include E_sec in E_b on its permitted domain,
and on D02 include the extra fixed-width secant choices.
Independently minimize the two pi sides, then take the maximum
with the valid strict polynomial and uniform bounds and the
terminal sign bound. At L>=166.4 the upper pi uncertainty entering
(R1) is strictly lower in the refined D02 envelope than in the
matched B0 envelope: use the psi strict comparison in
repair_spectrum.md at v=L and the prime-power subtraction common
to both. The primitive cannot increase on passage to D02, by
the same layer counting bound with the shorter right-hand interval.
At v=L-1 the D02 box/default/primitive and common branches
give nonincrease (uncertainties are minimized with all incumbents);
the squared upper bracket in (R1) is positive. All finite
alternative pi branches have expired at L>=166.4; the late PT
Corollary 2 bound is covered by its slower decay and the prior
source comparison. This is an improved onset for strict gain in
the designated pointwise R1 profile, not a claim that the maximum
with every uniform branch must be strict at every earlier point.

## Mertens: completing missing common finite joins and adding stronger ones

In the same units as finite.md, these new rows hold **strictly**
on the stated closed real rays, using B0 alone:

| C | P | Q | sum 1/p | weighted sum |
|---:|---:|---:|---:|---:|
|.11|12894433|12894433|12894487|12902077|
|.105|12901888|12901888|12901888|13022976|
|.10|12911611|12911611|12914903|18002111|
|.095|18002176|18002176|18002176|22052992|
|.09|22052224|22052224|22052224|30949504|
|.085|30949376|30949376|30949376|30971904|
|.082|30967296|30967296|30967296|33901696|

The .11 and .10 entries are the old fine sweep joins plus the
new extension. For .105 and the remaining new rows use the
compact interval scan in repair_finite.py from 10 million to
60 million. The sieve is exact, including endpoints. On each
closed block of 128 integer spacings, all three unnormalized
positive cumulative quantities are nondecreasing (product
of p/(p-1) and the two sums). Bound them by the left pre-update
and right post-update prefix intervals. The first left interval
is obtained by sieving and summing from 2; all later left
intervals include the preceding right endpoint. This encloses
all real points and jumps in the closed block. Evaluate the
normalized errors in interval arithmetic with u in the whole
logarithmic block, including the reciprocal of Qhat for P.
No monotonicity of normalized errors inside this block is
assumed. The left endpoint after the last unproved block
begins a chain of certified closed blocks. The old fine sweep
and the block sweep overlap through 25 million, and the log
tail below overlaps at 60 million. The normalizer intervals
are transferred verbatim from the 25-million certified
finite_run.txt; they are enclosures independent of x.

At 60 million the same analytic estimates from the common
inverse-log theorem in mertens.md, using U0^+ for the first
three errors instead of U1^+/u, give normalized coefficients
less than .077911 and .081342 respectively. The decreasing
coefficient proofs there require only u>=17 and remain valid
through log(10^13). The pieces from log(10^13) to log(10^19)
and onward are already below .002 and .00008 respectively.
Thus the extension and the finite onsets are all whole-ray
claims. The new finite pointwise envelope can also directly
use these prefix sums with floor(x) and the actual log x,
rather than the more conservative uniform block rows.
On the large analytic tails take the pointwise minimum with
the additional secant and power branches of repair_spectrum.md.

The previous finite-only bottleneck for .10 (and the weighted
.11) is therefore removed. At the present 60-million join the
particular simple U1 and signed CH2 bound does not already yield
.08 for the weighted sum. The finite extension and its analytic
join, not a new analytic assumption, account for the improved
inverse-log rows. Further fine optimization of these arithmetic
onsets may use prime-slab root isolation; block right endpoints
are sufficient only. Neither this refinement nor tightening the
old zero cutoffs is required for any stated ray.
