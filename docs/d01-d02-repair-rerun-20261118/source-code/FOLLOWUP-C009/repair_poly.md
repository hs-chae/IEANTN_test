# New whole-real-ray Mertens inverse-log tradeoffs

Use \(D_1,D_2,Z\) and the two relative errors with the exact constants of [mertens.md](mertens.md). In the table below, a row \((c,n_1,n_P,n_2)\) asserts
\[
 |D_1|\le c/L^3\quad(x\ge n_1),\qquad
 |e^{\pm Z}-1|\le c/L^3\quad(x\ge n_P),\qquad
 |D_2|\le c/L^2\quad(x\ge n_2).
\]
All onsets apply to real \(x\), inclusively. The inequalities are stated non-strict on the finite segment. No added hypothesis, RH beyond the verified height, or assumption about sample behavior is used.

| \(c\) | \(n_1\) | \(n_P\) | \(n_2\) |
|---:|---:|---:|---:|
|.0391|180612571|180612571|188200043|
|.040|180592613|180592613|187513559|
|.043|180218959|180218959|180558101|
|.047|113194369|113194369|179846189|
|.050|110219027|110219027|113194369|
|.055|110119007|110119007|110170799|
|.060|47002957|47002957|51843221|
|.063|45963157|45963157|47332391|
|.065|40891091|40891091|46909067|
|.070|40877261|40877261|40890511|
|.075|33930191|33930191|39706801|
|.080|30971683|30971683|33930191|
|.085|30921853|30921809|30971737|
|.090|18337549|18337549|30922673|
|.095|17991473|17991473|18338083|

The .047 weighted-sum onset in this table is the **joins** column, not the preceding flagged endpoint. Finite evidence for all but the .063 row is repair_mpoly.out; the .063 tradeoff is retained from m_poly_2b.out. Flag endpoints are not assertions of actual violations. No best possible coefficient or exact least onset is inferred. The former table, exact real coefficient onsets and old finite evidence remain separate valid branches.

## Proof and replay of the finite component

repair_mpoly.cc changes only the upper limit, trial coefficients/scaling, and avoids redundant checking of an unchanged state at a composite cut relative to mertens.cc (the older m_poly_2b.cc uses the original scale for its trial coefficients). The proof of sieve, dyadic logarithm error, tail constants and test thresholds is in mertens.md. We give the extended width and coverage details here.

Eratosthenes crosses out the multiples from \(p^2\) for unmarked \(p\) through \(\sqrt N\), using 64-bit indices. The unsigned prime scan ends at \(N=4000000000<2^{32}-1\), so its loop counter, each recorded event, and its final increment all fit. The bit-packed vector has \(N+1\) entries addressing the inclusive range. A product \(p^2\) initially fits in u64 since \(p<2^{32}\); later \(p^m\) only multiplies with the guard \(p^m\le D/p\), so \(p^m m\le 56D\) in the loop for the correction, \(D=2^{56}\). All exponent scalings for logs remain between 0 and 32 (integers \(\le N\), log-log from 1000). Both log bounds here are \(<23D\) for \(n\le N\), with ample slack at \(N\). For example the weighted sum is bounded by \(2+2\log N\) from \(\theta(x)\le2x\) (Dusart Thm 4.2) and partial summation. Sum \(1/p\) is below the harmonic sum; log \(Q\) is below \(2\sum_{p\le N}1/p\). Bounds on rounded totals add much less than \(D\): use \(N\) times the elementary per-prime rounding allowances (no more than \(2EL+120\) dyadic units per prime, \(EL=16384\)). All these totals fit u64. The square and cube directed numerators fit u128, since \(23^3D^2<2^{126}\) even with the added ceilings (their slack is larger than all ceiling corrections); the test denominators multiplied by 10000 and the \(c D^2\) test numerators with the integer scaled coefficient \(c\le950\) fit u128. Signed differences use i128. The analytic constant computation through \(10^7\) is unchanged. In particular no floating rounding enters the flags at the larger limit.

Fixed-state intervals between events obey the monotonic admissible endpoint argument of mertens.md: the sum intervals are constant there and both admissible endpoints for each tested normalized error move upwards. The sufficient log-product threshold is \(c/(L^3+c)\), not a direct test on either product's actual error. A prime checks both pre-event left limit and post-event value; a composite test has identical states and need only be done once. The next-success invariant after the last flagged test establishes the entire interval from the listed join through \(N\), and the same argument holds for the .063 proof with \(N=2000000000\). The algorithm reuses the smaller finite computation and tail estimates for the three normalization constants, not an unproved numerical value.

## Analytic joins and comparison

The new repair_mpoly.py repeats every interval and tail inequality from mcert.py joins() with the new coefficient .0391 and \(L_0=22.1\). This is legitimate because the signed CH2 small-\(x\) branch still applies on the subset \(L_0\le L\le29.9\), the other bounds and monotonicity checks are unchanged, and \(e^{L_0}<4000000000\) is certified. In each .02 log-cell the decreasing bracket is evaluated at its left end and all polynomial scales at the right end, including any shorter last cell. The same checks from 29.9 to 58, 58 to 200 and the decreasing analytic tail from 200 all pass at the smaller coefficient. This proves coverage and overlap for all 4-billion rows. The earlier .063 certificate uses the same proof at \(L_0=21.4\), \(e^{L_0}<2000000000\). No unchecked interval occurs. The entire output is the minimum with all prior and new signed and spectral branches, not a succession of unchecked crossing guesses. At matched domains the .0391 row is a strict reduction of the *bounding functions* relative to .10 and the original .2/.3 coefficients; larger coefficients with earlier onsets preserve the tradeoffs. On sufficiently large rays the spectral bounds dominate; see the explicit monotonic comparison from \(L=189\) in repair.md.

To replay from the submission directory with the assigned non-login bash, run:

    export PYTHONDONTWRITEBYTECODE=1
    /usr/bin/python3.10 repair_mpoly.py
    /usr/bin/g++ -O3 -std=c++17 repair_mpoly.cc -o /work/replay-m4
    /work/replay-m4
    /usr/bin/python3.10 m_poly_2b.py
    /usr/bin/g++ -O3 -std=c++17 m_poly_2b.cc -o /work/replay-m2
    /work/replay-m2

Keep assertions enabled. The larger replay uses about 0.5 GB for the bit-packed sieve; outputs are small and reproducible. Execution proves the numerical obligations at ordinary exact-arithmetic trust, not source-first PV. Proof of the analytic kernels and threshold directions is separate. Earlier attempts keeping the 2-billion limit with these analytic inequalities did not certify .046 at \(L=21.416\); .047 passed the analytic test at that limit but smaller coefficients could not be obtained just by rerounding the same proof. At the 4-billion limit and \(L=22.1\) the .039 attempt fails this cell test (first certified upper bound for scaled \(D_2\) about .0390435). This is not a lower bound on the true errors. The finite replay and the signed CH2-to-RH tail around \(L=22.1\), not D01, are the bottlenecks for further polynomial gains by this route. A larger scan would need wider counters and renewed width checks, while a sharper analytic bridge would change the signed transfer itself. The ambiguous finite weighted CH2 line (9.1) was not used in either stage.
