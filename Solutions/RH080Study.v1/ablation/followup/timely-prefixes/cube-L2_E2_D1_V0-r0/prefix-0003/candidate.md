# Improved strict-open counts between real consecutive cubes

**Kernel-checked conditional result (B):** let N(a,b) count actual primes p with a<p<b. Assume ordinary RH, Schoenfeld Theorem 10 (6.1) as a named source predicate, and Büthe Theorem 2 (1.6) and (1.7) as two named finite source predicates. Then, for **every real n ≥ 369**,
    
    N(n^3,(n+1)^3) > 0.96699 n^2/log n.

This includes n ≥ exp(8), where it improves the inherited 0.7 coefficient. It changes the formal assumption package: it adds the three named theta predicates and does not need Green, Nicolas, or BPT. This is not presented as an RH-only proof inside Mathlib, nor as a record. **Unchanged package (B):** every real n ≥ exp(8) has N(n³,(n+1)³) > **0.78117 n²/log n**, using the inherited RH/Green/Nicolas/BPT package. The new consumer `FreshCubes.Octic.cube_78117` is checked against the literal inherited `OcticFamily`. The analytic link is the existing `RHOcticPush.OptimizedFinal.strict_count_family` (OcticOptimizedCertified.lean), not a newly derived explicit formula.

## Reproduce

From /work/submission: `/usr/bin/python3.10 build.py SchoenfeldCube`. On a previously built workspace rerun `/bin/lean SchoenfeldCube.lean` for the final axiom audit. Checked in Lean 4.34.0-rc2. See theta.audit. Source predicates are explicit hypotheses, not axioms.

## Source locators and endpoints

* Lowell Schoenfeld, *Sharper Bounds for the Chebyshev Functions θ(x) and ψ(x). II*, Math. Comp. 30(134) (1976), 337–360, Theorem 10 (6.1), printed p. 337, DOI 10.1090/S0025-5718-1976-0457374-X. Local primary PDF `/corpus/literature/Schoenfeld1976.pdf`, SHA256 `8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897`, matching the local primary-pin addendum (not the quarantined publisher response). The proof applies this only at arguments strictly above 2.3·10^9.
* Jan Büthe, *An analytic method for bounding ψ(x)*, arXiv:1511.02032v2, Math. Comp. 87 (2018), 1991–2009, DOI 10.1090/mcom/3264, Theorem 2 (1.6),(1.7), printed/PDF p. 2. Local PDF SHA256 `350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1`. Bounds are unconditional published finite computations, not newly reevaluated. Definitions follow the assigned `SECONDARY_SOURCE_FACTS.json`: θ(t)=sum of log(p) for p≤t.
* Passing from θ(b)−θ(a) to N(a,b) can lose the prime at b but never p=a: θ(b)−θ(a)≤(N(a,b)+1)log b. This is a finite-set lemma in ThetaCube.lean, for all real 1<a≤b.

## Derivation

Write L=log(n), U=log(n+1), x=n³, y=(n+1)³. For n≥45/4, L≥12/5, U≤n/4, and U≤L+1/n. Hence 3U(n²/L)≤3n²+5n/4. Also (n+1)√(n+1)−n√n≤(8/5)√n and √n≥10/3. For the latter use √n√(n+1)≤n+1/2 and multiply the desired inequality by √n.

The finite estimates imply θ(y)−θ(x)>y−x−1.95(n+1)√(n+1)+.05n√n. The spare 3n+1 in y−x compensates for 5n/4 from replacing L by U, at most 3n/4 for one endpoint, and at most .936n for the root increment. Thus throughout the valid finite slab, N(x,y)>n²/L−(19/30)n√n/L. This part does not require RH. Here x≥1423 already at n=45/4.

For n≥2,154,433, both arguments are inside Schoenfeld's ray. Its error envelope is increasing here, so two copies of the error at y suffice. The main-term buffer above absorbs the endpoint loss and denominator change. This gives N(x,y)>n²/L−(n+1)√(n+1)(3U−2)/(4π). The loss divided by n²/L is at most ((n+1)/n)²·U(3U−2)/(4π√(n+1)). For a=14.583 we have U≥a, e^(a/2)≥1467.75 by the 22-term exponential series, and for v=U−a≥0,

    (a+v)(3(a+v)−2) ≤ a(3a−2)(1+v/2+v²/8)
                    ≤ a(3a−2) e^(v/2).

Use ((n+1)/n)²≤1.000001 and π>3.14159 to bound the normalized loss by .03301. All guarding inequalities are exact in Lean. The switch has (2,154,433+1)³≤10^19, so no real n is missing. For n≥369 the finite coefficient is at least .96699 since √n≥19.2.

The generic `cube_from_theta` also yields guaranteed earlier tradeoffs: for c≤.96699 use n≥45/4 and (1−c)√n≥19/30. The two pointwise source profiles in the code are stronger than discarding all dependence on n.

## Scope and next work

`CompactDualVerified` is imported and its fixed-A Fourier obstruction is inspected separately. It says the positive-denominator L1-Fourier quotient at A=36/11 exceeds .8 under its hypotheses. It is not a gap impossibility theorem and is not used to count cubes. No source-first C/C++/CUDA PV or new verification of published zero/prime tables. See the separate exact finite bridge below.

## Unchanged assumptions: adaptive octic proof

Put s=√n/L. If s≤16 use exactly C=s from x=n³; its width is 3n² and its normalized coefficient is 8/9−(.91015 L−1.4)/√n. With v=L−8≥0, √n=e^4 e^(v/2)≥54.598(1+v/2); compare affine functions to get ≥.78117. The same bound ensures s>1.03. If s>16, take k=ceil(s/16), equal open cells of width H=3n²/k and C=s/(1.001k). For n≥exp(8)>2500, throughout the cube, √u log u≤1.001(3n√n L): use (1+1/2500)(1+1/5000) for the square-root ratio and (1+1/20000) for the log ratio. Thus every octic window fits inside its cell. C lies in [1.03,16] since s/16≤k<s/16+1<s/8. No shared cell endpoint is counted.

If 16<s<19 then L<11, since for L≥11 the exponential tangent bound at L=11 gives √n≥210(1+(L−11)/2)>19 L. Hence every log u<35, allowing debt d=.79015 in place of .91015. Use k/s<1/8 in this band, and k/s<1/16+1/19 elsewhere with d=.91015. In each case (8/9)/1.001−d k/s>.78117; multiply by n²/L and sum the disjoint strict cells. This corrects the earlier loose geometry and preserves the positive logarithmic bonus near the critical widths. The onset case, not the rounded cell count at large n, is the bottleneck for this particular proof. The normalized onset expression for the single conservative 3n² cell is about .781171; this is not an upper bound on the true count or on other constructions.

Reproduce both consumers: `/usr/bin/python3.10 build.py SchoenfeldCube OcticCube`. The octic file imports only the literal family and finite-set/geometry support. A direct rebuild of the upstream baseline hit the partial LeanCert module-directory shadowing from /source_pv/objects (missing LeanCert.Core.Expr there). The optional `build.py --isolate-lean-cert PowerPopulation` separates the scratch copy of the baseline LeanCert prefix; the local consumer does not depend on that workaround. No claim of freshly replaying the original analytic closure.

## All-real earlier onsets with exact finite arithmetic

The analytic theorem needs no new prime sieve. A separate reproducible integer certificate (not Lean-kernel checked, not source-first PV) uses `/usr/bin/python3.10 cube_sieve.py` to bridge up to 369. It gives, with the same theta package for the infinite tail, the following strict lower coefficients:

| coefficient | onset |
|---|---:|
| .84 | n ≥ 2 |
| .94 | n ≥ 12 |
| .96 | n ≥ 25 |
| .96699 | n > 11863^(1/3)−1 |

This last onset is sharp for the stated coefficient: at n=11863^(1/3)−1 the count is exactly 149 and the inequality fails. The finite audit is a reproducible written certificate, not an independent external review.

Proof of the finite bridge: sieve every integer through 370³ by marking multiples starting at p² for each surviving p≤√(370³). Every composite has a prime factor in this range; no prime is marked. On each closed real cell [m/d,(m+1)/d], every prime in the strict inner window (((m+1)/d)³,(m/d+1)³) works for the full cell. The inclusive integer endpoints are floor((m+1)³/d³)+1 and floor(((m+d)³−1)/d³). The checker counts the common primes by updating differences of two overlapping integer intervals; it checks overlap and monotonicity at each step. The lower bound for log(m/d) uses powers-of-two reduction to [1,2] and ten rounded-down terms of 2∑z^(2j+1)/(2j+1), z=(v−w)/(v+w). The upper bound adds the per-term rounding and a geometric bound 2z^21/(21(1−z²)) for the tail. The inequality tested is count·log_lower(m/d)·d² > c·(m+1)², with all denominators cleared. Thus no interpolation of sampled prime counts is assumed.

The only remaining local strip is [21.8068,21.8069]. Throughout it the left cube lies strictly between 10369 and 10371, and 10370 is composite. At the algebraic onset the right cube is exactly prime 11863, which is excluded. The exact integer checks establish 149 primes in [10371,11862], show that 149 is insufficient at the onset using log_upper(21.8069) and 21.8068², and show that 150 suffices throughout the strip after the entrance using log_lower(21.8068) and 21.8069². The remaining closed cells cover from 21.8069 onwards. In a coarse grid with d=100 even n=76.34 had insufficient *cell* lower bound, not an actual counterexample; refining the grid materially changes the guaranteed range.

## Matched primary comparisons (published results quoted, not new predicates)

* CMS arXiv:1708.04122v2, Theorem 5, and Blanquer Robles v2 (21 Nov 2026), Theorem 3, use ordinary RH and give existence on the half-open forward window at x≥4 with widths .88 and .85125 times √x log x, respectively. At x=n³ and n≥exp(8), even 3n² is strictly smaller than the cube length and these windows are shorter still, so the half-open transfer gives a strict cube prime at the same n. They guarantee existence much earlier; our improvement concerns *counts*, not shortening their windows.
* Blanquer Robles, Theorem 3, printed p. 2, gives a finite population expression at x≥4·10^18 only. On the matched domain n³≥4·10^18, divide its printed bracket by MW·t to obtain f(t), t=log x≥42. Put k=.85125 log(2)/2<.3. Applying log z≤z−1 to t/42 gives log(kt)≤log(12.6)+(t−42)/42<2.61+(t−42)/42. With its printed σ,β,κ, this gives f(t)<.033 since (1.61β−κ)>0 and [.00000164065364394+(2.61β−κ)/42]/MW<.033. For disjoint exact-width cells in the cube, the sum of its displayed population lower expressions is therefore ≤(.033/.85125)·((n+1)³−n³)/(3L), below .04 n²/L on this range. Deducting closed endpoints cannot improve that sum. This compares numeric lower-bound expressions for a specified tiling, not upper bounds on primes or all consequences of the paper. No finite population statement at exp(24) is inferred.
* Blanquer Robles Theorem 2 Eq. (2) (p. 2; q=1 ordinary-RH specialization discussed at end of §3) and CMS Theorem 3 are eventual population results, not explicit starts. For example at target α=1 the displayed Blanquer width is 2.35648342; the octic family gives a strict liminf >1 at C=2.15 (within its width domain), since (8/9)·2.15−.91015>1. At small α the published width is shorter, and the octic C≥1.03 guard cannot be discarded. Chirre–Gonçalves–de Laat arXiv:2005.02393v3, §1.3, gives an eventual ordinary-RH comparison, not a finite onset (its Theorem 1 instead assumes GRH for progressions). The inherited .834021+ε normalized gap comparison and the imported fixed-A obstruction are both separate from cube density.
