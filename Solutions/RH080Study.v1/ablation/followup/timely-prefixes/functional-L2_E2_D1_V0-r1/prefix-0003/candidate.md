# CMS fixed-penalty obstruction and alternative prime-gap bounds

## Results and scope

1. **No: the fixed ordinary-RH CMS optimization cannot reach 0.8.** The supplied Lean kernel result gives a uniform lower bound 100/123 for the quotient in the L1–L1 subcase; `Obstruction.lean` imports `CompactDualVerified` and checks the uniform reciprocal. The full original CMS class is covered by the written Fejér argument below. Independently retesting the original BR dual with directed integer and rational arithmetic gives the stronger full-class floor (1/(1.207854736255)), about 0.82791412. None of these is a lower bound on the actual prime gaps.
2. **New asymptotic upper bound:** ordinary RH and the general CMS gap reduction give
   [
   limsup_{n	oinfty}rac{p_{n+1}-p_n}{sqrt{p_n}log p_n}
     le 0.833946826621 < 0.833947.
   ]
   Here (p_0=2). The new degree-48 rational Gaussian witness is checked by the directed arithmetic in this submission, not by the Lean kernel. This improves the inherited 0.834021 but does not purport to find the optimizer or the mathematical optimum. No explicit onset follows.
3. **Separate explicit result:** strict intervals ((x,x+0.8sqrt{x}log x)) contain a prime for **all real (4le xle e^{174})**, with the source premises in explicit.md. This does not extend to a whole ray at 0.8. For a whole-ray alternative use the rational affine window in `w4.json`, coefficient **0.851062**, from x≥e^42 by analysis and from x≥4 with the finite-gap source bridge. See explicit.md and the replay commands. No asymptotic Iwaniec improvement or hypothesis on Dirichlet L-functions was used in this explicit calculation.
4. **What would have to change analytically:** retain CMS Corollary 4 but improve its effective leading exterior-prime bound. With the scalar parameter from CMS (1.11), a *proved* (Ble2.43036) would already suffice for a normalized gap bound strictly below 0.8 via the new degree-44 witness. This is not an estimate of B under RH. The exact criterion for the scalar route and the limits of the threshold computation are below. A different analytic reduction (for example one controlling the weighted signed exterior contribution or exploiting cancellation in the zero sum) need not obey this functional obstruction. Finite bounds need effective quantitative error control even with a better leading coefficient.

## Exact functional and obstruction

Use (widehat F(v)=int F(u)e^{-2pi iuv},du); write (J(F)=int_{|v|>1}(widehat F(v))_+,dv), (M(F)=int |F|), (D_A(F)=F(0)-AJ(F)), (R_A=M/D_A) if (D_A>0). CMS arXiv:1708.04122v2 (1.3) takes the supremum (C^+(A)) of (D_A/M) over nonzero continuous integrable tests with real Fourier transform; it reduces to real even functions as in CMS §2 and BR §2. The reciprocal of the supremum is the infimum of the positive-denominator quotients (the feasible positive subclass is nonempty, e.g. sinc squared). Infinite leakage cannot increase the score. Our explicit witnesses meet the stronger conditions of Schwartz decay or the BR affine-window conditions.

A real even compact step V with V=1 a.e. on (-1,1) and (1-Ale Vle1) a.e. outside satisfies (widehat F-A1_{|v|>1}(widehat F)_+le widehat F V) pointwise a.e. Multiply by (m_T(v)=(1-|v|/T)_+) and integrate. The first term tends to F(0): the inverse kernel is (Toperatorname{sinc}^2(Tu)), a positive mass-one approximate identity, with tails outside any fixed neighborhood bounded pointwise by (1/(pi^2Tu^2)); continuity at zero and L1 suffice. For the positive penalty apply dominated convergence by finite J. For the right side apply dominated convergence by (M|V|), and Fubini, to get (int Fcheck V). Thus (D_Ale |check V|_infty M); the uniform lower bound after inversion also excludes a sequence of quotients converging down to 0.8. No integrability of (widehat F) was required in this written proof (BR proof of Theorem 4). The kernel subcase has integrability of both F and its transform as explicit hypotheses. The three audit prints in Obstruction.log list only propext, Classical.choice, Quot.sound.

For the exact arithmetic retest use BR supplement certificates/dual-rh.json, the original 24 cells per unit with support 10, with exact feasibility checked. Write the heights (b_j), followed by (b_N=0). Then (check V(0)=2sum b_j/m), and otherwise (check V(u)=sum_j(b_{j-1}-b_j)sin(2pi j u/m)/(pi u)). By folding the odd periodic numerator and reducing the denominator it suffices to bound ([0,m/2]), with nonzero multiples of m giving zero. The directed sine FFT uses the antisymmetric jump vector (imaginary coefficient divided by −2) with the absolute sum as stage amplitude and adds the input rounding error. It encloses (sup_k |S(k)|/k) for signed sine numerator S on (u=mk/G) using k≥1; include exact zero separately. The curvature bound (4pi^2int |V(v)|v^2,dv) and chord error (|K''|_infty (m/G)^2/8) extend it to the real continuum. See exact formulae in window_cert.py and BR §2.3. This improved lower bound is E-tier, not a promotion of the kernel constant or the actual C grid code.

## Gaussian certificate

In each JSON the ascending coefficients represent (p(y)=sum_j c_j y^{2j}), with (y=sqrtpi x) at scale 1. The actual pair is (F(x)=p(sqrtpi x)e^{-pi x^2}), (widehat F(v)=q(sqrtpi v)e^{-pi v^2}) with (q(y)=sum c_j(-1)^j 2^{-2j}H_{2j}(y)), physicists' Hermite polynomials. Differentiate the Gaussian transform to obtain this identity; (H_{n+1}=(2y-partial_y)H_n) evaluates the exact coefficients. Both functions are even continuous Schwartz functions, F(0)=1, and in particular eligible for the general source predicate in /representation/source/IEANTN/Vocabulary/CMSFunctional.lean. The PNT, zero enumeration, and cube inputs are not new assumptions in this witness.

The rational certificate partitions the nonnegative y-ray up to 20 by Bernstein control points under dyadic bisection (all coefficients simultaneously nonnegative or nonpositive give a constant sign). A scale-preserving integer de Casteljau step exactly implements subdivision. Any undecided terminal interval is bounded by its largest absolute Bernstein ordinate times its length and exp(-lo²). On signed intervals integrate (p(y)e^{-y^2}) via linearity and
[
 I_j(x)=rac{2j-1}{2}I_{j-1}(x)-	frac12 x^{2j-1}e^{-x^2},
 quad I_j(x)=int_0^x y^{2j}e^{-y^2},dy.
]
Here (I_0) is enclosed by its alternating integrated Taylor series (directed integer recurrence for terms, wait for a decreasing tail), or for x≥10 by the Gaussian integral and tail (e^{-x^2}/(2x)). The same integration-by-parts recurrence with plus sign encloses the absolute-coefficient tail from 20. The transform wing starts just *below* √π (using a Machin enclosure) and keeps only positive part. The two half-line integrals are multiplied by 2/√π rounded upwards. Exponentials use a small-range alternating polynomial followed by directed squaring. All comparisons proving upper bounds are exact rational comparisons, independent of the floating search. For a scaling s>0 the implementation divides mass by s and uses wing lower endpoint √π/s.

For g24.json the tests yield (Mle0.748511460006, Jle0.031303255887); insert A=36/11 and F(0)=1, with strictly positive denominator. CMS Corollary 4 (1.14), B≤36/11 (1.12) and monotonicity of C⁺ give the asserted limsup. This uses exactly the general CMS reduction in the inherited package, not the BR numerical theorem as a premise. For g243.json (Mle0.683874163417, Jle0.059726537720). The certified sufficient cutoff ((1-5M_{
m cap}/4)/J_{
m cap}>2.43036) gives the claimed strict result **conditional on** a new (Ble2.43036). At A=2.43 the rounded certified quotient is ≤0.799979590620. This threshold concerns the redesigned witness, not an unauthorized parameter swap in the inherited Lean predicate.

## Exact scalar criterion and analytic dependency

CMS defines (B=limsup_{x	oinfty}(pi(x+sqrt x)-pi(x))/(sqrt x/log x)) over real x, and (1.12) uses Iwaniec, Thm. 14, for (Ble36/11). In the derivation of (5.10)–(5.11), each exterior block has length √a and is charged using any (B'>B), after a sufficient but unspecified threshold. This is the precise leading term to replace if keeping a scalar charge (B' dsqrt a,J), with (d=2piDelta) in the notation of explicit.md. Controlling a different statistic, a density average missing the worst-case blocks, or just recomputing a Gaussian for an arbitrarily smaller A does not supply that bound; an improved *weighted* exterior-prime estimate for the chosen witness, with (o(dsqrt a)) remainder, would suffice instead and need not imply a uniform B estimate.

For the best limsup bound obtainable from the unchanged scalar CMS formula the exact criterion is (Ble A_*), where
[
 A_*=sup_{F:J>0, J<infty}
 rac{F(0)-5M(F)/4}{J(F)}
]
over the original admissible class. This is a characterization, not an exact numerical evaluation. Indeed C⁺(A) is finite and convex on A≥1 (supremum of affine scores and the box V=1 on the interior, 0 elsewhere gives C⁺(1)≤2). It is continuous for A>1. J=0 cannot meet the score 5/4 by the uniform fixed-penalty dual. For any score ≥5/4 at A≤36/11, J/M is bounded away from zero by subtracting the fixed dual bound; this remains true for scores tending to 5/4 when A<36/11. If A<A_* a witness scores strictly above 5/4. If A>A_* and A<36/11, even a maximizing sequence approaching a score ≥5/4 is impossible: its J/M is bounded below by a positive constant, and its score is at most 5/4−(A−A_*)J/M. At and above 36/11 use the fixed strict uniform obstruction. Continuity, the strict obstruction and the strict new primal result imply (2.43036<A_*<36/11), with (C^+(A_*)=5/4) (no attainment claim). A pointwise witness at the threshold would additionally require attainment of the displayed supremum. Thus modifying the exterior charge enough to cross this criterion, or changing the form of the reduction, is necessary for a 0.8 guarantee by optimization; identifying A_* exactly is open here.

## Reproduce and classify

From /work/submission, use non-login /bin/bash and these commands:
```
LEAN_PATH=/source_pv/objects /bin/lean Obstruction.lean
/usr/bin/python3.10 gauss_cert.py g24.json 36/11 .833947
/usr/bin/python3.10 gauss_cert.py g243.json 2.43036 .8
/usr/bin/python3.10 window_cert.py dual /corpus/literature/Blanquer_supplement/certificates/dual-rh.json 1048576 1.20786
/usr/bin/python3.10 window_cert.py ray w4.json 524288 .851062
/usr/bin/python3.10 window_cert.py slab /corpus/literature/Blanquer_supplement/certificates/witness-ap.json 32768 .8 42 174 16
```
The explicit proof includes a finite historical gap source only for the extension down to x=4. Without that source the written results start at e^42. Source predicates (B-tier) are not new Lean axioms or derived ordinary RH results inside Mathlib. Outside Lean, the deterministic exact-arithmetic checks plus derivations are E-tier, kernel numeric proof D-tier, floating optimizers F-tier. These checks do not connect the actual C characters or execution to a real specification (no C-tier source-first PV claim). No Ramanujan work.

**Limitations and failed searches:** increasing Hermite dimension from 24 to 34 (Gaussian degree 48 to 68) with the tested continuation gave a weaker value about 0.833956; scale 0.85 did not reliably improve the directed result. A finite sampled smooth objective underestimated the true (absolute-value) integral near its zeros; only the independent directed certificate was retained for validity. For the explicit ray 0.85106 failed the leading-margin check for w4.json; the approximate Gaussian or high-density grid alone would not establish it. For the slab, positivity was extended by retaining the negative zero log moment and using shorter MV blocks; without continuum concavity endpoint tests would not imply the whole range. A search for stronger reduced-penalty duals and exact bounds on A_* was incomplete at this checkpoint.
