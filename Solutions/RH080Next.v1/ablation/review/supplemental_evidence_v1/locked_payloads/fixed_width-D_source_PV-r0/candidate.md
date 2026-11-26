# Eventual prime populations at widths 3 and 5

## Results and scope

Put H(x)=sqrt(x) log(x), N(c,x)=# primes in (x,x+cH(x)], and M(c,x)=# primes in (x,x+cH(x)). Write Good(a,c) for the packet's GoodCoefficient. All eventual statements below are for sufficiently large **real** x; thresholds may depend on the parameters. None inherits the old onset.

Under ordinary RH and **both** `BRFourierInput.v1.norm_identity` and `BRFourierInput.v1.uniform_population_q1`, the exact inverse targets of the three advertised curves at widths 3 and 5 are respectively
`A3=685251/387796` and `A5=465/128`. Both satisfy Good at their stated widths, hence both N and M exceed the corresponding target times sqrt(x) by an eventual positive multiple of sqrt(x). No CMS hypothesis is required for these conclusions.

Using the supplied exact affine witness caps rather than the rounded advertised lines, the stronger numbers are
`B3=193269011844967139/109374342622661960` and
`B5=31036198331144443607/8533333333333333328`.
Under the same three premises **every a<B3 is Good at width 3, and every a<B5 is Good at width 5**. Thus both strict-open normalized liminfs are at least their respective B; equivalently for every eta>0 the counts normalized by sqrt(x) are eventually at least B-eta, even simultaneously. Neither Good at B nor a pointwise eventual count at B is asserted. These are lower guarantees, not upper bounds on what any argument can prove about primes. B3 and B5 are the largest leading outputs of the two rational witness caps at these widths; A3 and A5 are the largest inverse targets of the three stated lines.

## Envelope of the advertised curves

With q=20582561296/24680948495, write

- G(a)=q(1+2a),
- S(a)=944247/1000000+(1163388/1000000)a,
- F(a)=9/8+(16/15)a.

The adjacent crossing targets are
u=544470055511653/2490320656859788 and v=542259/290164. Indeed dividing the respective intercept differences by the differences of slopes gives these rationals, and 0<u<v. Since the slopes are strictly decreasing in the order G,S,F, G<=S iff a<=u and S<=F iff a<=v. Therefore for a>=0,
`E(a)=min(G(a),S(a),F(a))` equals G for a<u, S for u<=a<=v, and F for a>v. The nonadjacent crossing is irrelevant: in the middle segment S is below both.

Under RH and the named inputs of the selected branch, every c>E(a) is Good: use epsilon=c-G(a)>0 in the Gaussian region, and use monotonicity of counts in c for x>=2 in the affine region. On a>=u, E(a) itself is Good (including both ties). For a<u the Gaussian certificate only gives an infimum upper bound; it does not give Good at G(a). Neither statement identifies the true optimal width. Monotonicity follows since H(x)>0 for x>1 and the half-open intervals are nested. A common unconditional-in-branch statement above E uses RH and all three named predicates, including `CMSFunctionalInput.v1.population_reduction`.

At fixed width c the exact inverse comparison is
`E(a)<=c iff a<=max((c/q-1)/2, (c-944247/1000000)/(1163388/1000000), (c-9/8)/(16/15))`.
This follows from disjunction for min<=c and the three positive slopes. The winning inverse is Gaussian up to width G(u)=3731134672774344/3112900821074735, sparse up to S(v)=9048441/2901640, then flat. For c<q there is no nonnegative target in this inversion. For q<c<G(u) the inverse yields a normalized liminf bound by proving eventual guarantees at each smaller nonnegative target; it does not prove Good at the inverse. At c=q nonnegativity gives the trivial liminf lower bound 0. At c=3,5 the winning branches are sparse and flat, respectively. Substitution gives S(A3)=3 and F(A5)=5 exactly.

## Refinement without rounding to the advertised lines

In the general affine estimate let D=F_test(0)-4*positiveLeak, L a certified upper bound for its whole-line L1 norm, and M0 the attained absolute window maximum. At fixed c>0 the normalized half-open count is eventually at least (cD-L)/(2M0) minus a quantity tending to zero. In the following table each row gives the exact D,M0,L used; T=10^18.

| window | D | M0 | L |
|---|---|---|---|
| sparse | 1-4*119725872611533800/(8T) | 546871713113309800/T | 887721072633027910/T |
| flat | (15*533333333333333333)/(8T) | 533333333333333333/T | 1120475208606944546/T |

These are the existing witness propositions, not a new floating-point computation. In particular the flat normalization is not rounded to 1. Evaluate the two affine expressions at each width and take their maximum to obtain B3 (sparse) and B5 (flat). Both strictly exceed the corresponding A. For any a<B, use half the gap B-a as a positive margin after the vanishing remainder has become smaller than that margin. The caps are not claimed to equal the exact norms. The raw lower estimate alone cannot discard a possibly adverse vanishing error at equality.

## Endpoints and indices

For x>=2 and c>0 the difference of prime counts at the two natural floors counts precisely the primes p with x<p<=y=x+cH(x). Indeed primeCounting counts primes at most its argument and for a natural p, p<=floor(z) iff p<=z for z>=0. The lower set is a subset of the upper set. Passing to strict-open deletes at most one prime, namely y if y is an integer prime. If N/sqrt(x)>=a+d eventually with d>0, also impose x>=(2/d)^2 and x>=2; then M/sqrt(x)>=a+d/2. In particular M>a sqrt(x). No rounding of normalized bounds or assumption that y is not prime is needed.

An index consequence for any nonnegative Good target is obtained with p_n the zero-based nth prime. The number strictly below p_n is n (nth-rank), hence the number at most p_n is n+1. Let y=p_n+cH(p_n). Primes below y are precisely the primes strictly below the natural ceiling of y. If at least k>=1 primes lie strictly between p_n and y, at least n+1+k lie below y. If p_{n+k}>=y, at most n+k lie below y, by its nth-rank, a contradiction. Thus for k=floor(a sqrt(p_n))+1 we get p_{n+k}<p_n+cH(p_n) eventually, since the strict count exceeds a sqrt(p_n), and p_n>=n+2 transfers the real threshold. This also applies to each nonnegative a strictly below the appropriate B.

## Exact comparison with the preserved octic benchmark

The separate RH+Green+Nicolas+BPT package in COMMON_FACTS gives on x>=exp(24), 103/100<=c<=16, the strict-open bound
`M(c,x)/sqrt(x) > O(c)+21/(5 log x)`, where `O(c)=(8/9)c-18203/20000`.
The inverse of the leading term W(a)=(9/8)(a+18203/20000) is within the theorem's width domain exactly for 973/180000<=a<=2396173/180000. Only on this domain do we compare W with E as a width benchmark. The exact leading width savings W-E there are
`163827/160000-q+(9/8-2q)a` on the Gaussian branch,
`318687/4000000-(9597/250000)a` on the sparse branch,
and `-16173/160000+(7/120)a` on the flat branch.
They are strictly positive: S<W for a<=2 by direct substitution at 2 and monotonicity of the difference; F<W for a>=2 by the corresponding argument. Where the Gaussian branch is used, choose 0<epsilon<W-E for an actual attained saving W-E-epsilon. The octic positive correction supplies a strict count at the inverse width, but tends to zero and by itself is not a uniform positive margin there.

| width | old leading count | A minus old lead | B minus old lead |
|---|---|---|---|
| 3 | 105391/60000 | 61212941/5816940000 | 1726734183826542841/164061513933992940000 |
| 5 | 636173/180000 | 70933/720000 | 9864964558708324124141/95999999999999999940000 |

At A3 and A5 the inverse old width exceeds 3 and 5 by 183638823/15511840000 and 70933/640000, respectively. The B gains are leading gains; any smaller positive gain at each width follows as an eventual strict count. The finite-x bonus remains part of the old theorem and is not included in the savings; the table does not compare actual counts (which are the same primes) or prove any finite-x advantage. In particular retain the old strict leading-count-1 result at width 343827/160000 and x>=exp(24). No superiority beyond the stated leading comparison, and no best-known claim.

## Provenance and verification

- Packet: /task/COMMON_FACTS.md items (1)–(3) and the paragraph “Original comparison.” The octic arithmetic is formalized here; its separate analytic/count theorem is used as supplied, not reproved.
- CMS primary: /corpus/literature/CMS1708.04122v2.pdf, (1.3), (1.12), Theorem 3 (1.13) (text lines 99, 264–275). BR primary: /corpus/literature/Blanquer_Robles_2026.pdf, Lemma 5 (4), Proposition 6 (6), and “The moduli 1 and 2” (text lines 138–141, 338–342, 503–505). These are locators for general analytic interfaces, not published statements of our constants. In the BR modulus-one specialization the error shape is log(log x)/log x+2 log(x)/sqrt(x), with an eventual constant; the limit is checked in `ExplicitBRPopulationConsumer.brQ1Error_tendsto_zero`.
- Assigned /source_pv/source: `RH080EstimatePack.lean` (the three named kernel routes), `PopulationActualConsumers.lean` (source-first affine curve consumers), `IEANTN/Nodes/AffineFourierPrograms/v1/Conclusions.lean` (exact witness caps), `AffineProgramsSolution.lean` (source-first witness construction), `WeightedPopulationSolution.lean` (rounded curves), `ExplicitBRPopulationConsumer.lean` (padding and removal of vanishing error). The transfer and exact arithmetic, strict endpoints, and rank step are checked in Transfer.lean.
- Supplied source-first scope: the two fixed inputs in /source_pv/{population_norm.c,flat_population_norm.c}; restricted scalar C source syntax and preprocessing checks, AST correspondence, checked unsigned execution of the selected program, output and rigorous mathematical enclosure. See `PopulationSource.lean` / `FlatPopulationSource.lean`, the respective `Execution` and `Main` files, and `PopulationSourceFinal.lean` / `FlatPopulationSourceFinal.lean`, `source_first_periodic_norm`; the scalar host contract is in `ScalarHost.lean`. This transfer consumes these certificates, not an external executable's printed decimals. No verification of arbitrary C, compiler, runtime/library, OS, or hardware; no new C++/CUDA or old large-FFT PV. The Gaussian remains kernel-only. Source-first vs kernel-only does not change the mathematical input values. No inference of an advantage from exposure.

Run this with the assigned bounded Lean wrapper:
`LEAN_PATH=/source_pv/objects /bin/lean /work/submission/Transfer.lean`.
See verification.txt for the final checked run and attempts.txt for limitations and failures.
