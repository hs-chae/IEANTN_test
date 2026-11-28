# Exact prime-population transfer at widths 3 and 5

Let h(c,x)=c sqrt(x) log(x), let N(c,x) count primes in (x,x+h(c,x)],
and let M(c,x) count primes in (x,x+h(c,x)). A margin means a fixed
positive real number for each fixed choice of parameters, valid at
all sufficiently large real x. There is no explicit onset.

## Three-curve result

Use ordinary zeta RH. The Gaussian branch uses
CMSFunctionalInput.v1.population_reduction. The affine branches use
BRFourierInput.v1.norm_identity and BRFourierInput.v1.uniform_population_q1.
Assume all three source predicates for the joint result. They are explicit
hypotheses (not derived from RH in Lean).

For target a>=0 put
G(a)=q(1+2a), q=20582561296/24680948495,
S(a)=(944247+1163388a)/1000000, F(a)=9/8+(16/15)a.
Their exact lower envelope E and the width set certified directly by the
three curves and width monotonicity are:

| Target | E(a) | Certified widths c with GoodCoefficient(a,c) |
|---|---|---|
| 0 <= a < A | G(a) | c > G(a) |
| A <= a <= B | S(a) | c >= S(a) |
| B <= a | F(a) | c >= F(a) |

Here A=544470055511653/2490320656859788 and B=542259/290164.
Solving the crossing equations gives respectively A (G/S), B (S/F),
and D=172404138261/356130660736 (G/F). Exact cross multiplication gives
0<A<D<B and slopes 2q>1163388/1000000>16/15; subtract the corresponding
linear equations at their zeros to get the branch order, including both
ties. At A use S to attain the common width; at B either affine curve
works. For the left branch take epsilon=c-G(a)>0. For a fixed target,
width monotonicity for x>=1 preserves the same positive margin, since
the right endpoint increases and the left endpoint is unchanged.
Lowering the target also preserves validity; because all three widths
increase in a, it cannot improve their direct width envelope. This table
does not characterize the actual good-width set: in particular it
does not exclude Gaussian attainment or any better estimate.

In the inverse direction let
P(c)=max((c-q)/(2q),(c-944247/10^6)/(1163388/10^6),(c-9/8)/(16/15)).
For c>q this is the direct target frontier; its branches in the same
order change at wA=3731134672774344/3112900821074735 and
wB=9048441/2901640, the common widths at A and B. On q<c<wA every
0<=a<P(c) is certified, but P(c) is only a supremum of directly
certified targets (equivalently every deficit from it is eventually
allowed). At c>=wA the frontier target is certified with margin,
including c=wA. At c<=q no nonnegative target is certified directly.
For x>=1 the underlying piReal uses natural floor, and both counts
are finite.

| Total width | G inverse | S inverse | F inverse | Octic leading count / sqrt(x) |
|---|---|---|---|---|
| 3 | 53460284189/41165122592 | 685251/387796 | 225/128 | 105391/60000 |
| 5 | 102822181179/41165122592 | 4055753/1163388 | 465/128 | 636173/180000 |

Consequently t3=685251/387796 and t5=465/128 are the largest targets
obtained by direct inversion at their respective widths, attained
with positive eventual margins under RH and the two BR predicates
alone. This means not just a liminf at least t3 or t5, but a liminf
strictly greater. The margin from the rounded-curve statements alone
is not numerical. Nor does fixed-width subdivision improve the explicit
leading coefficient from the same three lines: P_+(c)=max(0,P(c))
is convex as a maximum of affine functions and P_+(0)=0. For a
partition of C>0 into c_i>=0, convexity gives
P_+(c_i)<=(c_i/C)P_+(C), hence the sum of the subdivision targets
is at most P_+(C). This is a scalar observation for adding those
leading targets, not an impossibility result for other arguments.
See below for a separate refinement using the
underlying witnesses rather than their rounded curves.

## Endpoints and zero-based ranks

For y=x+h(c,x), the half-open count is piReal(y)-piReal(x). The open
count is pi'(ceil_nonnegative(y))-piReal(x), where pi'(m) counts primes
strictly below the natural number m. For x>=0 the formulas count
exactly the asserted primes: integer p<=x iff p<=floor(x), and
p<y iff p<ceil(y). Subtract the lower set (or use natural truncated
subtraction when the interval is empty). Opening the interval deletes
at most the single prime equal to y. If N(c,x)/sqrt(x)>=a+d for d>0,
increase the threshold to include x>=1 and x>=(2/d)^2. Then
M(c,x)/sqrt(x)>=a+d/2. The reverse implication, from a strict-open
margin to a half-open margin, is immediate from M<=N. Without the
margin, subtracting one would not necessarily preserve a strict
inequality with the same right-hand side.

For x=p_n, the first n primes are smaller and p_n is prime, so
pi'(p_n)=n and piReal(p_n)=n+1. For k>=1 the ordering gives
p_n<p_(n+k). If k<=N(c,p_n) but p_(n+k)>y, then at most n+k primes
are <=y, contradicting piReal(y)>=n+1+k. If k<=M(c,p_n)
but p_(n+k)>=y, at most n+k primes are <y, again a contradiction.
Thus the half-open rank conclusion allows equality at y; the open
conclusion does not. Since p_n>=n+2 tends to infinity, the real
threshold applies eventually at p_n. In particular for c=3 or 5
and all sufficiently large n, simultaneously for
1<=k<=floor(t_c sqrt(p_n))+1, the prime p_(n+k) lies in the
strict-open interval. The extra 1 follows from the strict count
M(c,p_n)>t_c sqrt(p_n) and integrality, not from assuming that
the upper endpoint is composite.

## Exact comparison with the preserved original baseline

The separate original RH+Green+Nicolas+BPT package asserts an
open count strictly greater than
((8/9)C-18203/20000+(21/5)/log(x))*sqrt(x) for x>=exp(24) and
103/100<=C<=16. Preserve separately its explicit-onset leading count 1
at C=343827/160000. Write L(C)=(8/9)C-18203/20000 and
O(a)=(9/8)(a+18203/20000). Only use O(a) as a comparison of
inverted leading widths when 973/180000<=a<=2396173/180000,
obtained by solving 103/100<=O(a)<=16. The positive vanishing
correction at equality itself is no positive limiting margin.

At widths 3 and 5 the exact gains t_c-L(c) are respectively
61212941/5816940000 and 70933/720000. In the opposite direction,
O(t3)-3=183638823/15511840000, O(t5)-5=70933/640000, and
O(1)-E(1)=33027/800000. More generally the exact saving in leading
width is O(a)-G(a), O(a)-S(a), or O(a)-F(a) on the indicated branch,
restricted to the original target domain. Its minimum in that
domain is 13152201/1658080000 at a=B: the first two differences
are strictly decreasing, the last strictly increasing, and they
match at the breaks. On the epsilon branch this is an infimum-width
saving: choosing any epsilon smaller than the saving still gives
a strict improvement of the width coefficient with a margin.
At fixed widths the octic correction eventually falls below the
positive leading gain, but this compares two lower-bound formulas,
not actual counts and not explicit finite-x performance. No claim
about best-known bounds or global superiority is made.

## Separate witness-level refinement (beyond direct curve inversion)

The same certified affine witnesses allow the BR population consumer
to be applied before rounding to the three input lines. With D the
BR denominator, V an upper bound for amplitude mass and M_peak the
attained window maximum, the named uniform input gives the normalized
count an eventual lower bound of (cD-V)/(2 M_peak) minus a vanishing error.
The consumer handles padding the rational mesh by zeros. Given
a<(cD-V)/(2 M_peak) use half the positive difference as margin after
the error is sufficiently small. The positive denominator and peak
and the following exact data are checked in the Lean refinement:

* Sparse: D=1-4*119725872611533800/(8*10^18),
  V=887721072633027910/10^18, M_peak=546871713113309800/10^18.
* Flat: D=15*533333333333333333/(8*10^18),
  V=1120475208606944546/10^18, M_peak=533333333333333333/10^18.

At widths 3 (sparse) and 5 (flat) this gives all targets strictly below
u3=193269011844967139/109374342622661960 and
u5=31036198331144443607/8533333333333333328, respectively, with the
same hypotheses and strict-open transfer. These certify positive
numerical slack over t3 and t5, e.g. the midpoints are good targets.
The liminf is at least u_c, by allowing every fixed positive deficit;
attainment as GoodCoefficient at u_c is not inferred. Thus these
supremum bounds are stronger than the direct inverses, but are not
part of the requested three-curve envelope or an optimality result.
The exact supremal leading gains given by these witness bounds over the octic expressions are
1726734183826542841/164061513933992940000 at 3 and
9864964558708324124141/95999999999999999940000 at 5; any fixed
positive deficit from these gains is eventually allowed. As above
there is no transferred explicit onset.

## Verification and provenance

Run from /work/submission using the assigned bounded wrapper:
    /bin/lean Transfer.lean

The file checks the branch arithmetic, attainment/epsilon transfer,
inversion, comparison, actual strict-open count and rank steps, and
the optional witness refinement. The checked main results have only
propext, Classical.choice and Quot.sound in their axiom audit; RH and
the named inputs are theorem parameters. No native or numerical
oracle is used for the new arithmetic. The first attempts to unfold
the line names omitted the local abbreviations; inverse comparison
with nested constant denominators also failed with raw linarith.
The submitted check unfolds the abbreviations and normalizes the
inverse lines before linear comparison. No claim was taken from failed
runs. Not inferred in general: equality on the Gaussian-only boundary,
attainment at u_c, or explicit onsets.

Source locators (assigned mount /source_pv/source):
* RH080EstimatePack.lean, namespace RH080Exposure.Estimates, roots
  gaussian, sparse, flat; exact curve propositions in
  IEANTN/Nodes/RHAsymptoticGaussian/v4/Conclusions.lean:31 and
  IEANTN/Nodes/RHWeightedPopulation/v1/Conclusions.lean:12-25.
* IEANTN/Vocabulary/CMSFunctional.lean, piReal, halfOpenCount,
  normalizedPopulation, GoodCoefficient, SourceCMSPopulation;
  CMSPopulationFunctionalSource.lean, goodCoefficient_mono.
* IEANTN/Nodes/BRFourierInput/v1/Conclusions.lean, norm_identity and
  uniform_population_q1. PopulationMatchedControl.lean:15-29,
  kernel_only_sparse_witness and kernel_only_flat_witness;
  ExplicitBRPopulationConsumer.lean:53-60, source_BR_population_goodCoefficient.
* Frozen literature (/corpus/literature): CMS1708.04122v2, admissibility
  and C_+(A) in (1.3), B in (1.12), Theorem 3 (1.13) and proof
  section 5; Blanquer_Robles_2026, Lemma 5 in section 2.1 (norm
  identity), Proposition 6 in section 3 (uniform count), specialized
  in the assigned interface to q=1 and ordinary zeta RH. The separate
  baseline is the supplied COMMON_FACTS.md statement (see also the
  PrimeInterval.v4.optimized_strict_family references in the frozen
  BASELINE_THEOREM_MATRIX.md).

This is the assigned C_network exposure. The Gaussian and affine
providers imported here use kernel-only numerics. The separate
coordinator C-source/AST/execution-to-ANT routes for the affine curves
are not used or reverified here; the shared C files are
/source_pv/population_norm.c and /source_pv/flat_population_norm.c.
Source-first claims are scoped to the actual C ports and the supported
C semantics/verification setup, not arbitrary C/C++/CUDA code and not
end-to-end certification of compiler, runtime, OS or hardware.
No source-first transfer for the original large FFT, or for this
submission, is claimed. Written mathematical transfer and checked
Lean transfer are distinct from both the published analytic inputs
and the coordinator's source-first results.
