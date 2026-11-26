# Transfer of the three population bounds

This is conditional on ordinary RH and on the explicitly named literature-backed inputs in /task/COMMON_FACTS.md, not on RH alone. Write G(a)=q(1+2a), S(a)=944247/1000000+1163388a/1000000, F(a)=9/8+16a/15, with q=20582561296/24680948495. Width multiplies sqrt(x) log(x).

## Width envelope

Set u=544470055511653/2490320656859788 and v=542259/290164. For a>=0 the minimum is G(a) on [0,u], S(a) on [u,v], and F(a) on [v,infinity). Indeed S-G=(2q-1163388/1000000)(u-a) and F-S=(1163388/1000000-16/15)(v-a); both prefactors are positive, and 0<u<v. For a<u this gives an infimum of the widths delivered by these curves, not a GoodCoefficient assertion at G(a). At a=u sparse attains the common value, and at a>=u at least one affine input attains the minimum. A larger width preserves GoodCoefficient by eventual monotonicity of primeCounting and positivity of sqrt(x) log(x).

## Widths 3 and 5

At width 3 the Gaussian, sparse and flat inverse levels are respectively 53460284189/41165122592, 685251/387796, and 225/128. At width 5 they are 102822181179/41165122592, 4055753/1163388, and 465/128. For each width the Gaussian is strictly worse than both affine choices. Sparse wins at 3, flat at 5, and the corresponding affine GoodCoefficient(685251/387796,3) and GoodCoefficient(465/128,5) follow by substitution under RH and the two BR inputs only. This means an unspecified strictly positive eventual surplus above each displayed level, not merely a limiting bound. No optimality for actual primes, nor quantified surplus or onset, is claimed.

Each count in the assumed GoodCoefficient is half-open; restricting to the strict-open interval loses at most one prime, because the only possible omitted element is the right endpoint. If delta>0 works in the half-open bound, eventually sqrt(x)>=2/delta, so delta/2 works in the open bound. In particular the open count is eventually strictly larger than the stated inverse level times sqrt(x).

## Exact scope and inverse frontier

For a>=0 the direct rule, including width monotonicity, is precisely
`G(a)<c or S(a)<=c or F(a)<=c`. Equivalently c is strictly above the envelope, or c is at least the envelope and a>=u. This is an iff about the **rule**, not about the actual prime population. The G–F intersection lies strictly between u and v, where S is below both; it is not a knot. At c=G(a), a>0, every 0<=b<a is certified by the Gaussian using epsilon=G(a)-G(b). Thus one gets a liminf at least a there (even for the strict-open count), without a positive surplus at a. The case a=0 gives only the trivial nonnegative lower limit at c=q from this boundary argument.

The inverse levels of slopes and intercepts (t,b) are (c-b)/t. Their maximum gives the nominal leading inverse. It is the Gaussian inverse for q<c<U, the sparse inverse for U<=c<=V, and the flat inverse for V<=c, where U=3731134672774344/3112900821074735 and V=9048441/2901640. For c<=q no nonnegative target is directly certified. Indeed the sparse inverse is <= the Gaussian inverse iff c<=U, and the flat inverse is <= the sparse inverse iff c<=V, with U<V. At U the sparse line supplies attainment, at V both affines do. In the Gaussian-only range the supremal level is not directly certified, but every smaller nonnegative one is. For 3 and 5, the reported levels are **largest directly certified numerical targets**, not largest actual GoodCoefficient targets: GoodCoefficient itself implies existence of a larger target at the same width (replace a by a+delta/2 and use delta/2 as margin). No explicit size of that improvement follows from substitution alone.

### Rank corollary

For either selected pair (a,c), eventually in real x, every natural m with m<=a sqrt(x) satisfies
`x < p_(piReal(x)+m) < x+c sqrt(x) log(x)`.
Indeed, with y the right endpoint, the open count is #primes strictly below y minus piReal(x); there are no missing ranks between these two cutoffs. More explicitly, primes are strictly enumerated by Nat.nth, and for x>=0 an integer prime p exceeds x iff it exceeds floor(x), while p<y iff p<ceil(y). Below ceil(y), the prime indices are precisely 0 through Nat.primeCounting'(ceil(y))-1; at or below floor(x), they are 0 through piReal(x)-1. Since the strict-open count exceeds a sqrt(x), it exceeds m, so piReal(x)+m is within the open block. At x=p_n the lower cutoff is n+1 (n primes less than p_n and p_n itself). Taking m=floor(a sqrt(p_n)) therefore puts p_(n+1+floor(a sqrt(p_n))) strictly inside the interval for all sufficiently large n; p_n>=n+2 ensures the real eventual threshold is passed. The +1 is essential with the zero-based indexing.

## Preserved original baseline

The separate RH+Green+Nicolas+BPT package proves the explicit strict-open bound from the packet for x>=exp(24) and 103/100<=C<=16, with positive (21/5)/log(x) correction. Its leading bound at widths 3 and 5 is respectively 105391/60000 and 636173/180000 times sqrt(x); both coefficients are below the selected new ones. This is a comparison of leading coefficients, not an inherited explicit onset. The original leading count 1 at 343827/160000 retains its own explicit onset and separate hypotheses.

Write B(c)=(8/9)c-18203/20000 and O(a)=(9/8)(a+18203/20000). Comparing widths at fixed level uses O only on
`973/180000 <= a <= 2396173/180000`, exactly B([103/100,16]).
Comparing populations at fixed width uses B only on [103/100,16]. Here are the exact differences (new-minus-old for population, old-minus-new for width at the selected target):

| Total width | Population gain | Width saved at its new target |
|---:|---:|---:|
| 3 | 61212941/5816940000 | 183638823/15511840000 |
| 5 | 70933/720000 | 70933/640000 |

Both inverse baseline widths used in the last column lie in [103/100,16]. For target 1 the sparse width 421527/200000 saves 33027/800000 over 343827/160000, with no inherited onset. At equal target a the general leading saving is O(a)-G(a), O(a)-S(a), or O(a)-F(a) on the three envelope branches. The first two decrease (their new slopes exceed 9/8), the third increases since O-F=(7/120)(a-48519/28000). The continuous difference consequently has minimum at v of 13152201/1658080000>0. Thus the envelope gives a positive leading saving on the actual original domain; in the Gaussian branch subtract the chosen positive epsilon from the infimum saving. The flat-only crossing at a=48519/28000 does **not** mark a loss for the envelope (it is on the sparse branch). At equal width, the exact nominal gain is the corresponding inverse minus B(c), with the same strict-versus-attained rule at the Gaussian inverse.

### Nonexplicit uniform comparison on the original width domain (written)

Let H be all three named analytic inputs together with RH. For every c>=103/100, a=B(c)+1/200 is nonnegative and O(a)=c+9/1600. Since the minimum saving exceeds 9/1600, c is strictly above the envelope at a. Hence H implies GoodCoefficient(a,c), and strict-open count eventually exceeds a sqrt(x). This pointwise step is Lean checked. For a uniform conclusion on [103/100,16], apply it to the **finite** grid j/400 for integers 412<=j<=6400. Take the maximum of the finitely many thresholds and 2. For any c in the domain choose j=floor(400c), so the open interval at j/400 is contained in the one at c and B(c)-B(j/400)<1/450. Their comparison gives open count > (B(c)+1/360)sqrt(x) simultaneously for this whole domain. If x is also at least exp(1512), this bound exceeds the original displayed lower bound including its logarithmic term. The threshold from the grid remains unknown: exp(1512) alone is **not** a new onset. This compares formulas, not actual prime counts or all published theorems.

## Proof and source audit

- `Transfer.lean`: complete Lean proof of the width envelope and direct-rule characterization, attained/epsilon claims, width 3/5 substitutions, inverse arithmetic, at-most-one endpoint loss and positive margin, rank and eventual prime shifts, exact leading savings, and the pointwise GoodCoefficient gain used for the finite-grid argument. Run `/bin/lean /work/submission/Transfer.lean` with the assigned wrapper and offline imports. Checked with exit 0; printed axiom dependencies for key theorems are only propext, Classical.choice and Quot.sound. The uniform finite-grid deduction and liminf interpretation above are written, not claimed as kernel checks.
- Assigned exposure B_named: /source_pv/ESTIMATE_NAMES.md, /source_pv/EXPOSURE.json and RH080EstimatePack.olean. Roots RH080Exposure.Estimates.gaussian, .sparse and .flat. /source_pv/FLAT_FACTS.txt searchable declaration locators: CMSFunctionalInput.v1.population_reduction (line 441), BRFourierInput.v1.norm_identity (332), .uniform_population_q1 (383), IEANTN.CMSFunctional.GoodCoefficient (28976) and .halfOpenCount (29076). Exact trees are in FLAT_FACTS.json. RH and these analytic inputs remain explicit hypotheses; named compiled estimates are not proofs of the source predicates.
- Primary locators in /corpus/literature: CMS1708.04122v2, (1.3), (1.11)–(1.13), Theorem 3 and proof §5.2 (text lines 96–103, 258–275, 1056ff.). Blanquer_Robles_2026 §2.1 Lemma 5, (4) (text 128–142: arbitrary rational support-five affine window), and §3 Proposition 6, (6), proof §§3.1–3.4 (338–483; the named q=1 population input uses a vanishing logarithmic remainder). These are source locators, not a new Lean formalization of the papers. The selected coefficients are the supplied coordinator results, not quotations of paper theorems. Original strict-open bound: /task/COMMON_FACTS.md, Original comparison; preserved rank formulation in /corpus/literature/BASELINE_THEOREM_MATRIX.md:418–431.
- Verification levels: packet Gaussian is kernel-only, and this new transfer uses ordinary compiled kernel estimates for both affine routes. /source_pv/population_norm.c and /source_pv/flat_population_norm.c are the supplied C source bytes; this arm does not have authenticated authored source-first consumers or an authored graph. The common packet separately records completed source/AST/execution/numerics-to-ANT routes for the two coordinator affine results, not for the Gaussian or the original large-FFT migration. No C execution is used in this transfer. A source-first certificate limited to the fixed numerical C programs and their modeled integer/control/I/O semantics would not by itself certify an arbitrary C port, compiler lowering, runtime/stdio, OS or hardware, or another C++/CUDA implementation. No such broader verification or exposure advantage is claimed.

## Negative checks and limits

- Equating the Gaussian infimum with GoodCoefficient at the boundary would drop epsilon; replacing the strictly-open count with the half-open count could include a prime at y. Neither shortcut was used.
- The first Lean endpoint attempt tried to infer floor(y)<=ceil(y) directly using le_floor_iff; the inferred goal had an extra floor of a natural cast. The completed proof uses the cast comparison with le_ceil. The first inverse-order proof using linear arithmetic alone did not normalize nested rational divisions; ring_nf before linarith resolved it.
- A preliminary baseline crossing analysis tracked where the flat line alone beats O. This yielded a false candidate active crossing; evaluating the sign at the actual sparse–flat knot corrected it. Neither that crossing nor the G–F intersection is a change of the active bound.
- Strict-open transfer, inversion and comparison do not quantify the input surplus at 3 or 5, decide Gaussian-boundary attainment, prove an explicit onset for the new results, re-verify the named analytic inputs, or produce any source-first PV for this submission.
