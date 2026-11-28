# Growing-rank prime-index bounds

Write p_n=Nat.nth Nat.Prime n (p_0=2), L(x)=sqrt(x) log x, U_c(x)=x+cL(x). Put
```
G(a) = (20582561296/24680948495)(1+2a)
S(a) = 944247/1000000 + (1163388/1000000)a
F(a) = 9/8 + (16/15)a
B(a) = min(S(a), F(a))
E_e(a) = min(G(a)+e, B(a)).
```
The combined claims use ordinary RH and the explicit predicates
`CMSFunctionalInput.v1.population_reduction`,
`BRFourierInput.v1.norm_identity`, and
`BRFourierInput.v1.uniform_population_q1`. These literature-backed analytic inputs are **not** discharged by RH or newly proved here. Gaussian alone needs only RH+CMS; either affine BR branch needs only RH+both BR predicates.

**Exact fixed-cap bound.** For each beta≥0 and e>0, eventually in n, simultaneously for every integer 1≤j≤floor(beta sqrt(p_n))+1,
```
p_(n+j) - p_n < E_e(beta) L(p_n).
```
No padding is needed on the BR branches. In particular if B(beta)≤G(beta) the exact upper coefficient is B(beta). All these inequalities are strict at the right endpoint.

**Rank-adaptive bound.** In the same range put t=(j−1)/sqrt(p_n). For every eta>0, eventually uniformly in these j the coefficient can be taken to be E_0(t)+eta. Both bounds hold at once (take their minimum after taking the maximum of the two onsets). Equivalently the limsup of the maximum over the finite rank range of the normalized gap minus E_0(t) is at most zero, i.e. its positive part tends to zero. The displayed limiting envelope does not assert an eventual Gaussian bound with no epsilon; in the adaptive theorem the Gaussian input is used at e=eta/2.

The lower-envelope switches for E_0 are G→S at 544470055511653/2490320656859788 and S→F at 542259/290164. These follow by solving G=S and S=F, observing that the former parameter is smaller and that the slopes strictly decrease in the order G,S,F. These are comparisons of supplied lines, not optimality claims over all possible tests or analytic inputs. For example at beta=1 the exact fixed-cap coefficient is 421527/200000=2.107635, and at beta=0 the near-Gaussian coefficient applies to the next prime.

## Exact bridge and uniformity

If y≥p_n, then p_k≤y iff k+1≤piReal(y), since floored y is an integer and an increasing enumeration counts precisely its initial segment. Lean implements this by `Nat.lt_nth_iff_count_lt` at floor(y)+1 and `Nat.count_nth_succ_of_infinite` for piReal(p_n)=n+1. Subtracting n+1 is legitimate by monotonicity. Thus j≤piReal(y)−piReal(p_n) iff p_(n+j)≤y. For j≥1 the strict inequality holds iff the difference is ≥j+1, or equals j and y is not a prime. Indeed ≥j+1 puts the strictly larger p_(n+j+1) at or before y; if the difference is exactly j, p_(n+j) is the last counted prime, so equality holds precisely if y is itself a prime. The lower open endpoint follows from strict increase and j≥1. The argument does not assume U_c(p_n) nonintegral.

Given GoodCoefficient(a,c), choose its positive delta. Strict increase of the integer primes implies p_n→∞; also c>0 and L(p_n)>0, so U_c(p_n)≥p_n. Eventually N(c,p_n)≥(a+delta)sqrt(p_n)>a sqrt(p_n)+2. Hence the count is ≥j+1 whenever j−1≤a sqrt(p_n); for a≥0 this rank inequality is exactly the requested floor cap. The strict bridge gives the result. This proves the exact fixed cap by selecting the smallest of the three widths at a=beta. More generally the eventual population exceeds a sqrt(p_n)+K for any fixed K, and the same width works at rank parameter a+delta/2, using the remaining delta/2 as the new population margin.

For adaptive uniformity, let g be a continuous target profile. At each a∈[0,beta] suppose there is some c_a<g(a) with GoodCoefficient(a,c_a). At that width use the preceding rank headroom to pass to b_a>a. Then the open set {t: t<b_a, c_a<g(t)} contains a and the width works for all ranks in this neighborhood. Use finitely many of these neighborhoods by compactness, and take the maximum of their fixed onsets. In fact use c_a+(g(a)−c_a)/2<g(t) for their second defining inequality; the minimum of these finitely many positive half differences gives a uniform positive coefficient margin below g. For the main adaptive bound use g=E_0+eta and c_a=E_(eta/2)(a)≤E_0(a)+eta/2. Neither the finite cover nor the fixed cap assumes analytic thresholds uniformly in a.

A diagonal consequence (written): some integer-valued b(n)→∞ permits the same adaptive bound for every j≤floor(b(n)sqrt(p_n))+1 with error 1/b(n) once b(n)≥1. Apply the fixed-cap-uniform adaptive theorem for each integer k≥1 with beta=k and eta=1/k; choose strictly increasing thresholds N_k≥k above its onsets and set b(n)=max({0}∪{k:N_k≤n}). This does not yield the result for any prescribed unbounded cap.

## Separate strengthened consequence using a frozen upper-bound input

In addition, use the Montgomery–Vaughan inequality as stated in CMS (6.10), `/corpus/literature/CMS1708.04122v2.txt` lines 1393–1402, PDF §6.2: pi(z+y)−pi(z)<2y/log y for real z,y>1. This is a separate premise in Lean (`BrunTitchmarsh`, weakened to ≤). For x≥4 and 0≤d≤c, put y=(c−d)L(x)+sqrt(x), z=U_d(x). The endpiece count is at most pi(z+y)−pi(z); log y≥(log x)/2. Dividing by sqrt(x) bounds the endpiece by 4(c−d)+4/log x, uniformly even as c−d→0. Thus if the original GoodCoefficient(a,c) has margin delta, set u=min(c/2,delta/16). At width c−u the loss is eventually ≤delta/2, proving GoodCoefficient(a,c−u) with strictly smaller positive width. Apply the compact margin lemma with target B to obtain some kappa(beta)>0 such that the strict adaptive coefficient B(t)−kappa(beta) works uniformly. With the original combined assumptions one can then use min(B(t)−kappa(beta), E_0(t)+eta, E_e(beta)). This gives a strict qualitative leading BR saving but no numerical kappa. It is not needed for the direct transport and does not justify dropping Gaussian epsilon: the Gaussian margins at positive e are not bounded below uniformly as e→0.

## Baseline comparison (separate package)

With the coordinator's RH+Green+Nicolas+BPT package and C=max(1.03,(9/8)(beta+18203/20000))≤16, its strict-open count at p_n≥exp(24) exceeds beta sqrt(p_n)+(21/5)sqrt(p_n)/log(p_n). The extra term exceeds 1 throughout this range (sqrt(x)/log x is increasing for log x>2 and at exp(24) the term is >1 by exp(12)>13). The first j primes above p_n are therefore strictly before the right endpoint for the same rank cap. In particular at beta=1 compare 2.107635 (eventual, RH+BR) to 2.14891875 (explicit p_n onset, separate package). The new estimates do not inherit that onset.

## Optional n-only normalization (written proof)

Add the classical PNT premise piReal(x)~x/log x, stated for example in CMS §1, lines 264–267 of the frozen text, not used in the preceding transport. Evaluating at the primes gives n+1=(1+o(1))p_n/log p_n. Logs give log(n+1)/log p_n→1 since log log p_n/log p_n→0, then p_n/(n log n)→1. Set A_n=sqrt(n log n) and D_n=A_n log n for n≥2. Thus sqrt(p_n)/A_n→1 and L(p_n)/D_n→1. In the n-only cap j≤floor(beta A_n)+1 set s=(j−1)/A_n. Uniformly for 0≤s≤beta, t=s A_n/sqrt(p_n) differs from s by o(1) and lies in [0,beta+1] eventually. E_0 is continuous and uniformly continuous on that compact set. For any fixed eta>0 use the adaptive result at beta+1 with allowance eta/2, then absorb the uniform o(1) from changing both rank and width scales (E_0 is bounded on this compact set). This gives p_(n+j)−p_n < (E_0(s)+eta)D_n simultaneously for all such j. No PNT or n-only Lean proof is claimed here.

## Verification and boundaries

B_named exposure: `/source_pv/ESTIMATE_NAMES.md`, `/source_pv/EXPOSURE.json`. `Transport.lean` imports `RH080EstimatePack` and consumes the named roots `RH080Exposure.Estimates.gaussian`, `.sparse`, `.flat`. The authoritative common statement types are in `/source_pv/FLAT_FACTS.json`; analytic source locations: CMS Theorem 3/(1.13), following (1.3) and (1.11); BR norm identity and uniform population predicates as named in COMMON_FACTS and the exact declarations, from the frozen Blanquer–Robles corpus (see the affine-window Fourier development in §2 and the population combination in §3.4, starting at line 475 of the frozen text). Relevant generic source locators: `Mathlib/Data/Nat/Nth.lean` (infinite nth/count lemmas) and `Mathlib/NumberTheory/PrimeCounting.lean` (primeCounting/count definitions).

Replay in this executor: `cd /work/submission; /bin/lean Transport.lean` (non-login /bin/bash; no extra paths needed). The exact bridge, fixed cap, adaptive theorem, and supplemental BR saving conditional on its explicit premise typecheck. Axiom audit prints only propext, Classical.choice and Quot.sound. Baseline comparison, switch arithmetic and optional n-normalization above are written derivations. No new numerical experiments or source-first verification: imported estimates are kernel routes here, even though the packet describes separate C-source routes for the BR pair. Neither C semantics nor compiler/runtime/OS/hardware is verified by the present Lean transport. The original large FFT migration is not completed or used.

Unsuccessful routes: using just j primes for a strict-open bound fails when the endpoint is the last prime; selecting a different onset at each exact moving rank is not a uniform proof. Pointwise positive margins alone were not used to infer a uniform positive width reduction. Initial Lean names for a prime-specific counting lemma and strict sqrt bound did not resolve; the checked proof instead uses generic count/nth and square identities.
