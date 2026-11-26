# Growing-rank forward transport (written result)

Put \(P=p_n\), \(S(P)=\sqrt P\log P\), and
\[
G(t)=\frac{20582561296}{24680948495}(1+2t),\quad
B(t)=\frac{944247+1163388t}{10^6},\quad F(t)=\frac98+\frac{16}{15}t .
\]
Under RH and CMSFunctionalInput.v1.population_reduction, for every fixed beta >= 0 and eps > 0, eventually in n, simultaneously for all 1 <= j <= floor(beta sqrt(P))+1,
\[
0 < p_{n+j}-P < (G(\beta)+\varepsilon) S(P).
\]
Under RH and BRFourierInput.v1.norm_identity and BRFourierInput.v1.uniform_population_q1, replace the coefficient by min(B(beta), F(beta)) with no epsilon. With all the premises take min(G(beta)+eps,B(beta),F(beta)). The eventual threshold can depend on beta and eps; none of these statements supplies an onset.

**Exact order bridge.** For y >= P and j >= 1, p_(n+j) <= y iff piReal(y) >= n+j+1 iff the count of (P,y] is >= j. Indeed, floor(y) is nonnegative and primes <= floor(y) form exactly an initial segment of the strictly increasing prime enumeration; P itself has index n, so subtract n+1 without truncation. Strictly below a real y, the count in (P,y) is the half-open count minus 1 if y is an integer prime and otherwise unchanged. Equivalently p_(n+j) < y iff that open count is >= j. Thus a half-open count >= j+1 suffices even at a prime endpoint; half-open count >= j alone does not. The inequality P < p_(n+j) follows from strict increase.

**Margin.** GoodCoefficient(beta,c) gives delta > 0 and X such that N(c,P) >= (beta+delta)sqrt(P) for P >= X, using positivity of sqrt(P). Since p_n >= n (by strict increase), for all large enough n, P >= X and delta sqrt(P) > 1. Then N(c,P) > beta sqrt(P)+1 >= floor(beta sqrt(P))+1, so the integer count is at least j+1 for *every* permitted j. The order bridge with y=P+cS(P)>P proves the result. In fact any fixed number of additional ranks can be absorbed by the margin, and beta can be replaced in the rank ceiling by beta+delta/2 with this same width. The endpoint cannot be discarded just from half-open membership.

**Rank-sensitive strengthening.** Write E=min(G,B,F), with only the available lines used for a smaller hypothesis package. For every beta >=0 and eta >0, eventually all indicated j satisfy the strict bound with coefficient E((j-1)/sqrt(P))+eta. For beta>0 choose a finite uniform mesh on [0,beta] of spacing d with Ld < eta/2, L the maximum slope. At each mesh point apply the fixed-rank result with Gaussian error eta/2 (if used). For each j round t=(j-1)/sqrt(P) up to a mesh point u; the condition j-1 <= u sqrt(P) gives j <= floor(u sqrt(P))+1. Take the largest of the finitely many thresholds, and use E(u) <= E(t)+Ld (apply the slope bound to a minimizing line at t). For beta=0 just use the single mesh point 0. One may intersect this eventual estimate with the exact BR cap at beta, when available. In particular, for the largest permitted j the limsup of the normalized difference is <= E(beta); the limsup is not an eventual strict inequality at the unperturbed Gaussian coefficient.

The lower envelope changes from G to B at 544470055511653/2490320656859788 and from B to F at 542259/290164. Indeed the intercepts increase, slopes decrease, and these adjacent crossings are in increasing order (all exact rational comparisons). At the first crossing the shared value is attained as an eventual strict cap via B; at the second via either BR line. With a fixed nonzero Gaussian error the first crossover need not be the same: the displayed min formula is authoritative.

Source roots: /source_pv/objects/RH080EstimatePack.olean, RH080Exposure.Estimates.gaussian, .sparse, .flat; see /source_pv/ESTIMATE_NAMES.md. These are compiled kernel routes, not source-first PV. The named general analytic predicates are separate from RH. CMS source: /corpus/literature/CMS1708.04122v2.txt lines 271–274 (Theorem 3, (1.13)) and section 5. No C verification is claimed by this transfer, and the original explicit-onset baseline is not inherited.
