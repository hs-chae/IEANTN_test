# Same-stage repair and strengthened B0 portfolio

All results here are derivations from B0, not gains from D01: see the proof of premise redundancy in candidate.md. Review feedback is not a mathematical premise. All new analytic rays are strict and include their stated left endpoints. Retain the earlier portfolios in ramanujan-proof.md and mertens-proof.md and take, respectively, the maximum of applicable lower profiles and the intersection/minimum of applicable signed/absolute envelopes. No optimization over all B0 proofs is claimed.

## Correct characterization of the CH2 premise

Let \(D(L)=\sum_{n\le e^L}\Lambda(n)/n-L+\gamma\). CH2 PDF p. 35, Lemma 9.2 display (9.1), literally reads
\[
 -.7585825520\ldots\ \le D(\log x)\le .787\ldots\qquad(1\le x\le10^{12}+3).
\]
It does not contain \(\sqrt{x}\), and **does not imply** \(|D(\log x)|\le .8/\sqrt{x}\). The immediately following proof explicitly says it computes \(\sqrt{x}D(\log x)\) through \(10^{10}\); it uses the harmonic-adjusted weighted computation for larger \(x\), with the displayed \(O^*(1/x)\) correction inside the \(\sqrt{x}\) factor, and reports that the extrema on \([1,10^{12}+3]\) are reached below \(10^{10}\). PDF p. 36, proof of Cor. 1.3, invokes the stronger finite bounds. Thus at **inherited published finite-computation trust** we retain an optional signed intersection using the normalized magnitude \(.8e^{-L/2}\), credited to the reported finite computation, not to the literal display. The conservative implemented range is \(13\le L\le27.6\) with \(e^{27.6}<10^{12}+3\); the split integral uses it only up to 27. No larger range is needed. The directly printed weighted Cor. 1.3, PDF p. 3, instead gives \(\pi/(3\cdot10^{12})+113.67/\sqrt{x}\) for \(x\ge1\). The separately printed **unweighted** Lemma 9.2 bounds for \(\psi(x)-x\) are unaffected. In the mounted CH2.txt the display and normalized-computation passage are at physical LF 5224–5266, followed by the use in the Cor. 1.3 proof after the PDF page 36 heading; the PDF locators take precedence.

The old code used the normalized bound by default in wcap and jw. It is now opt-in (normalized=True). With it disabled, the old cell at \(L=16\) failed to certify \(.175/L^2\) for \(W_2\); see the original own-ablation.stdout. This was a sufficient-test failure, not a counterexample. The repaired main proof gives the row independently of the normalized computation, at an earlier onset and with a better coefficient at \(L=16\). There is no independent replay of the CH2 weighted computation, no formal Lean, no source-first PV, and no new finite RH verification.

## Cap-free finite bias repair

Use the signed identities in mertens-proof.md. Improve both \(B,A_*\) at every \(13\le L\le22\) using \(N=10^5\), \(X=4\cdot10^9\), \(e^{22}<X<N^2\). For \(p>N\) every exponent \(j\ge2\) has \(p^j>x\). Sieve precisely the primes up to \(N\). For the small-prime part of the total \(B\) before subtraction sum \(\log p/[p(p-1)]\). For the total \(A_*\) sum \(1/(jp^j)\) for \(p^j\le10^{24}\), \(j\ge2\), and add \([0,2N/10^{24}]\) for the omissions; per prime the first omitted term is at most \(10^{-24}\) and the geometric ratio at most \(1/2\).

For the \(p>N\) tail, \(|\theta(t)-t|<.007t\) over \(t\ge N\) follows from unweighted CH2 Lemma 9.2 plus Dusart Cor. 4.5 through \(L=29.9\), finite RH \(\theta\) through 58, and CH2 Cor. 1.3 plus the power correction thereafter. Each piece decreases, with onset tests in bias_repair.py. For a decreasing differentiable weight \(w\) with \(tw(t)\to0\), partial summation bounds the difference between the prime-weighted tail \(\int_{(N,\infty)}w\,d\theta\) and \(I_0=\int_N^\infty w\,dt\) by \(.007(2Nw(N)+I_0)\); use the boundary term at \(N\) and \(\int_N^\infty-tw'(t)dt=Nw(N)+I_0\). For \(B\) use \(w=1/[t(t-1)]\), \(I_0=-\log(1-1/N)\). For \(A_*\) use \(w=1/(2t^2\log t)\) for \(j=2\): alternating integration-by-parts terms through indices 4 and 5 enclose \(I_0\) as in the old sieve, with radius \(3\cdot .007/(2N\log N)\). The positive \(j\ge3\) residual is bounded by \(\sum_{n>N}1/[3(n-1)^3]\le1/[3(N-1)^2]\). No rounded values of normalizing constants are inputs.

Subtract terms at \(p^j\le x\) from each total, storing outward enclosures after each subtraction. Both tails decrease and use the right value at a jump. On a whole \(L\)-cell compare powers to the integer floors of the interval endpoints of \(e^L\). The lower bound uses the value after all powers at most the upper floor, the upper bound uses the lower floor. Intersect these with the analytic bias intervals at the current point only; the integral in the formula for \(a_-\) still uses the original analytic upper ray. Use the resulting signed envelopes for both sums and both exponentiated products.

Cap-free whole rays (blank means no claim in that column):

| \(L\) from | First three errors \(<C/L^3\), \(C\) | \(W_2\) error \(<C/L^2\), \(C\) |
|---:|---:|---:|
|15.7|.185|.19|
|15.89||.175|
|16|.160|.167|
|17.6|.09||
|17.7||.09|

bias_repair.py checks covers to 240 inclusive. At 22 the default analytic branch takes over; at 240 the bound with power coefficient .021 is already implied by the .0196 ray, and the polynomial comparison ratio \(.021 L^2e^{-L/8}/C\) decreases there. The same code checks the originally flagged row at 16 separately. Trials at 15.5 for coefficients .185 and .2, and at 17.6 for .09 in the fourth error, failed sufficient tests, not the actual inequalities. All unrelated Mertens branches, the same-Dusart-margin joins, scan and obstruction witnesses are retained.

## Improved high-zero boundary term and Mertens power proof

Retain the hypotheses and notation of the density mass in candidate.md (FKS Cor. 2.9, (2.17), Table 8, PDF pp. 7–8, 26). For \(.8\le\sigma<.875\) use the exact printed constants of the applicable closed row. Taylor's theorem with negative fifth derivative gives \((1+z)^q\le\sum_{j=0}^4 q^{\underline j} z^j/j!\) for \(z\ge0,\ 3<q=5-2\sigma<4\). Thus an upper bound for the first integral in the mass formula, replacing the earlier tangent-log bound, is
\[
h^q e^{-ah}\sum_{j=0}^4 \frac{q^{\underline j}}{a^{j+1}h^j},
\qquad h=\log H,\quad a=1-8(1-\sigma)/3>0.
\]
Use \(z=(v-h)/h\), and integrate the polynomial terms by \(\int_0^\infty y^j e^{-ay}dy=j!/a^{j+1}\). Multiply by \(2c_1\) and add the same \(2c_2(h^2+2h+2)/H\). Round the masses up to fixed-point endpoints. Their running minimum still bounds the actual nonincreasing high-zero mass. Form successive differences as before, now refining the last spacing to \(10^{-5}\). Terminal padding at zero is only algebra, not zero exclusion at \(7/8\).

For \(L\ge100\) take \(T=e^{L/4}\), \(V=e^{L/4+1}\) in FKS Thm. 3.2 (PDF p. 8), using the same tuple as candidate.md. Admissibility holds at 100 and persists since \(T/L,T/51,(\sqrt{x}-2)/(5T)\) increase; \(T^\star\le 2.45T<V\), \(V>10^6\). In the reciprocal-zero sum calculation of candidate.md use \(v=\log V\ge26\): \(2c(vp+u^2/2-up)>23\) already at 26, with \(u=\log 10^6,\ p=\log(2\pi)\), checked in boot_height. Consequently the sum is \(<.16v^2\le.16(.26L)^2<.011L^2\). The truncation cost is \(2.091Le^{-L/4}\). The new \(\psi\)-profile with layers \((c_i,g_i)\) is
\[
|\psi(e^L)e^{-L}-1|\le P_{\psi}(L)=.011L^2e^{-L/5}+2.091Le^{-L/4}+\sum_i c_i e^{-g_iL}.
\]
Use it as one more signed boundary branch throughout \(L\ge100\).

For power rays from \(B\ge180\), the scaled majorant before relative-product exponentiation is
\[
U_*(L)=e^{L/8}\big(P_\psi(L)+(1+1/L)J+1.84e^{-L}
+1.002e^{-L/2}+2.67e^{-2L/3}\big).
\]
The guards for the same Dusart row \(e^{B/2}>767135587\) and \(K<.001\) are now explicitly tested at each onset. Terms of \(U_*\) decrease or are constant, including \(L^2e^{-3L/40}\) and \(Le^{-L/8}\); use the monotone \(U_* /(1-U_*e^{-L/8}/L)\) for the relative products (as long as the denominator is positive, tested at onset). This proves entire rays from the onset tests in density_repair.py. In the early power cover use the cap-free signed finite branch and the new \(P_\psi\) in addition to the old analytic branches. This cover ends at 200, where the old .0196 power coefficient suffices for any early coefficient tested larger than .0196.

The following exact \((L,C)\) pairs give strict bounds \(C x^{-1/8}/L\) for the first three errors and \(C x^{-1/8}\) for the fourth:

| \(L\) | \(C\) | \(L\) | \(C\) |
|---:|---:|---:|---:|
| 13 | .0199 | 420 | .01358 |
| 193 | .0196 | 600 | .01259 |
| 200 | .01896 | 1000 | .01172 |
| 215 | .018 | 2000 | .01106 |
| 225 | .01744 | 5000 | .01067 |
| 237 | .017 | 10000 | .01056 |
| 250 | .01643 | 20000 | .01051 |
| 300 | .01513 | 100000 | .01046 |
| 350 | .01432 | 1000000 | .010454 |

In particular the old .0196, .018 and .017 margins begin earlier, and the revised coefficients at the old common onsets are smaller. The .0197 and .0198 early trials hit the transition near \(L=189\) where the CH2 Cor. 1.3 constant floor and the spectral envelope compete. A shorter FKS height removed enough of this obstruction to certify .0199 from 13, but those smaller constants remain uncertified from 13. The limiting coefficient of this **majorant** is a mass upper bound plus the fixed \(J\) term, not a lower bound on the true error.

For a power row and a polynomial row \(A/L^k\), the exact ratio is \((C/A)L^{k-r}e^{-L/8}\) with \(r=1\) or 0 according to the component. It increases up to \(8(k-r)\) and decreases thereafter. This supplies the comparison over the whole overlap, by testing the ends or specifying the roots of the ratio equal to 1 on the two monotone portions. For the .0199 row against the new polynomial rows and the remaining old later polynomial rows, the ratio is greater than 1 at each polynomial onset and less than 1 at 200 (comparison_repair.py); there is exactly one crossing in each overlap, the root on the decreasing portion. Against the latest old polynomial row the new .0196 power ratio is already below 1 at 193 and declines thereafter. These comparisons concern the explicit rows, not optimality of the signed envelopes.

An obstruction to changing the exponent is that these estimates do not exclude zeros on or arbitrarily close to \(\Re\rho=7/8\). If any of the four errors were \(O(x^{-b}(\log x)^k)\) for \(b>1/8\), the signed identities and the \(O(x^{-1/2})\) power corrections would give \(D\) or \(Z\) decay at any exponent \(b''<\min(b,1/2)\) (use log locally at 1 for the products). Multiply the respective Stieltjes measure by \(t\) or \(t\log t\) to recover \(d\psi\). The normalized main terms contribute \(dt\), and boundary/integral errors give \(\psi(x)-x=O(x^{1-b'})\) for \(1/8<b'<b''\), absorbing logarithms. By the Euler product and partial summation for \(\Re s>1\),
\[
-\frac{\zeta'(s)}{\zeta(s)}-\frac{s}{s-1}
=s\int_1^\infty(\psi(t)-t)t^{-s-1}dt.
\]
The integral would be analytic for \(\Re s>1-b'\), so no zero could lie there, by meromorphic continuation and the nonzero residue at a zero. This is a necessary condition, not an assertion that a boundary zero exists. D01 does not provide this zero exclusion.

## Ramanujan: finite profile improvements and arbitrary-order rays

Write \(F_R(L)=R(e^L)L^6/e^{2L}\). The connected strict positive ray remains \(x>r\), with the same exact local root and inherited integer finite computation, and a strengthened analytic join from \(L=36.526\). For earlier profiles include \(P_\psi\) above plus the same Dusart power-removal terms in the positive-mode anchor formula for \(\pi\) (ramanujan-proof.md; ramanujan.py join). The anchor \(a=140\) is already covered by CH2. For a mode \(cL^ke^{-gL}\), \(0\le g<1\), the scaled integrated part is bounded by \(cL^ke^{-gL}L/[a^2(1-g)]\); retain both anchor-error terms. The new option is used only on cells contained in \([140,360]\); otherwise the old branch remains. The existing exact coefficient subtraction, shifted error, special sign domain and interval subdivision are unchanged. Closed cells run to the displayed end, or to 360 with the prior rational tail checked there. Examples of failed sufficient tests are .9 from 39.37, 1.2 from 44.52 or extending to 81 in the indicated test, 1.3 from 47.17, degree 2 from 218, and degree 3 from 254. None is a counterexample.

The new strict inequalities \(F_R>\) the stated profile (no change to earlier valid rows) include:

| Profile | Closed \(L\)-domain |
|---|---|
| 0 | from 36.526 |
| .005 | from 36.535 |
| .1 | from 36.735 |
| .5 | from 37.766 |
| .9 | from 39.374 |
| 1 | from 39.98 |
| 1.05 | [40.35, 290] |
| 1.2 | [44.6, 80] |
| 1.3 | [47.2, 56] |
| \(1+14/L\) | from 47.15 |
| \(1+13/L+100/L^2\) | from 48.2 |
| \(P_2,P_3,P_4,P_5\), respectively | from 222, 255, 310, 351 |

These give both earlier onsets at fixed margins and larger margins at old onsets (e.g. at the old degree-16 onset 4000, degree 40 is now certified on the same whole ray). The preceding .005 onset 36.54 and other subunit rows can still be listed as weakest sufficient triggers, but are dominated on their exact former domains.

For arbitrary order define the full coefficients
\[
A_j=j!\sum_{i=0}^j1/i!-\sum_{i=0}^ji!(j-i)!,\qquad P_d(L)=\sum_{j=4}^{d+4}A_j L^{4-j}
\quad(d\ge0).
\]
For \(j\ge4\), the internal reciprocal-binomial sum is at most \(2/j+2(j-3)/(j(j-1))\le2/3\). The first four terms of \(\sum 1/i!\) already sum to \(8/3\) and the \(i=4\) term is positive. Hence \(A_j>0\), so higher degree is stronger at every overlapping \(L\).

Choose \(N=d+6\), \(A=\max(32,2(N+1))\), \(T_N(L)=\sum_{k<N}k!/L^{k+1}\), and \(\ell(L)=e^{-L}\mathrm{li}(e^L)\). For \(L\ge32\), \(0<\ell\le1\) by the old anchor at 32 and \(\ell'+\ell=1/L\); at the anchor \(T_{22}\le 3/32\) by a ratio bound and the correction is \(<5/32\). Also \(0<T_N(A)\le2/A\le1\) by its ratio bound \(1/2\). Exactly
\[
\ell(L)-T_N(L)=e^{A-L}(\ell(A)-T_N(A))+N!\int_A^Le^{v-L}v^{-N-1}\,dv.
\]
The integral is between \((1-e^{A-L})L^{-N-1}\) and \(2L^{-N-1}\), since \(g'\ge g/2\) for \(g=e^v v^{-N-1}\) on \(v\ge A\). If \(e^{A-X}X^{N+1}<N!/2\) at \(X=B-1>A\), this persists on \(L\ge X\) and implies \(e^{A-L}<1/2\), since \(N!< L^{N+1}\). Thus \(T_N\) and \(T_N+3N!/L^{N+1}\) are strict lower and upper barriers on the ray for both \(L\) and \(L-1\).

Expand the shifted lower polynomial by the positive binomial series through coefficient \(j=2N\) and square the positive upper polynomial. Coefficients through \(j=N-1\) are the full ones. Subtract \(P_d\) and rescale by \(L^{d+1}\): the leading coefficient is \(A_{N-1}>0\); drop positive subsequent terms and bound negative terms at \(B\). Deduct the absolute \(\pi\) error using the prior sp branch at both arguments. The rescaled cost multiplies by \(L^{d+5}\); each exponential times its polynomial decreases for \(L-1>8(9+d)\), since the maximal degree including integration is \(d+8\) and rates are at least \(1/8\). The factors \(L/(L-1)\), the upper square polynomial and the unscaled error are nonincreasing. The rational check at \(B\) uses \(e>2718/1000\) and floored exponents as in the prior tail. The check margin tends to \(A_{N-1}\), the exponential costs tend to zero even after flooring, and the barrier test eventually succeeds. Thus doubling \(B\) in ramanujan_orders.py terminates for every \(d\). Binary search is only a heuristic; every reported endpoint is directly checked. Strict \(F_R>P_d\) on an explicit real ray follows at every order.

Useful certified \((d,L\text{ from})\) pairs are \((6,376),(7,409),(8,448),(9,485),(10,517),(11,553),(12,592),(13,625),(14,664),(15,699),(16,736),(17,770),(18,808),(20,881),(22,953),(24,1025),(28,1169),(32,1320),(40,1612)\). Higher orders and earlier small-degree rows are tradeoffs, not grounds to discard the latter's early domains. As before \(F_R\to1\) excludes a larger constant margin on a whole ray. The very early analytic gap is still limited chiefly by the error in the shifted prime count; near the actual real root no fixed positive normalized margin can persist, by continuity there and exact vanishing.

## Reproduction and accounting

Run /usr/bin/python3.10 replay_repair.py from /work/submission using non-login /bin/bash with assertions enabled. certificates.md explains the exact arithmetic; repair-evidence.txt records the runs. The prior research bytes and prior review bytes are separately retained in prior-candidate.zip and prior-review.zip; own-ablation.stdout is a byte-identical convenience copy. The controller's prior observed research lower bound and review exclusion are recorded in research-accounting.json. The shell lacked ls (exit 127 at initial pwd/list), and cat also failed at one attempted workfile creation. Python opened both required JSONs and the permitted files and recovered the workfile creation step. The locale warning did not prevent execution. No unresolved execution interruption or delegation.
