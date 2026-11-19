# Mertens products and two prime sums

Use inclusive cutoffs and \(L=\log x\). Write \(\mathsf M,\mathsf B_3\) for the constants in Dusart PDF p. 17 Theorem 5.6 and p. 18 Theorem 5.7:
\[
 \mathsf M=\gamma+\sum_p(\log(1-1/p)+1/p),\qquad
 \mathsf B_3=\gamma+\sum_{m\ge2}\sum_p\log(p)/p^m .
\]
Define \(E_S=\sum_{p\le x}1/p-\log L-\mathsf M\), \(E_W=\sum_{p\le x}\log p/p-L+\mathsf B_3\), and
\(Z=\log Q_{\rm raw}(x)-\gamma-\log L\).
The relative errors for \(P_{\rm raw},Q_{\rm raw}\) are \(|e^{-Z}-1|, |e^Z-1|\), respectively. All stated envelopes are for absolute errors, with non-strict inequalities unless specifically indicated.

## Signed pointwise portfolio

Let
\[
 A=\sum_{2\le n\le x}\frac{\Lambda(n)}{n\log n}-\log L-\gamma,\quad
 H=\sum_{n\le x}\frac{\Lambda(n)}n-L+\gamma,\qquad K(v)=1/v+1/v^2 .
\]
In terms of the shared \(\delta\),
\[
 H=\delta(L)-\int_L^\infty\delta(v)\,dv,\quad
 A=\delta(L)/L-\int_L^\infty K(v)\delta(v)\,dv
   =H/L-\int_L^\infty H(e^v)/v^2\,dv.                    \tag{1}
\]
In the last integral \(H(e^v)\) denotes \(H\) evaluated at \(x=e^v\). These are partial summation identities with vanishing limits: Dusart Theorems 5.6–5.9 fix the constants, and the omitted positive prime-power tails tend to zero by the estimates below. One can equivalently take the first two identities by integrating from a finite anchor and passing to infinity using \(G_b\).

Use the signed source intersections in common.md for \(\delta\) and for \(z(v)=e^{-v}\theta(e^v)-1\). A signed transfer in (1) means integrating with the negative of the *opposite* endpoint and subtracting, i.e. if \(\delta\in[l,u]\), then \(\delta(L)/L-\int K\delta\in[l(L)/L-\int Ku,\ u(L)/L-\int Kl]\). Use an integrable full-ray envelope for the tail. Preserve CH2 Corollaries 1.2–1.3 for \(H\) (all permissible \(T\), on the stated domains); use the third formula in (1) with their intersection and the new \(H\) interval, as another option. Also directly use the two Dusart tail formulas (proofs of Theorems 5.6–5.7, PDF pp. 17–19) for \(E_S,E_W\): they are the first two formulas of (1) with \(z\) instead of \(\delta\) and the appropriate sums on the left. In particular the \(k,\eta_k\) versions of Dusart Theorem 4.2 yield bounds \(\eta_k/k\cdot L^{-k}+\eta_k(1+1/(k+1))L^{-k-1}\) for \(E_S\) if \(k>0\), and \(\eta_k/(k-1)\cdot L^{1-k}+\eta_k L^{-k}\) for \(E_W\) if \(k>1\). The integral transfer of the pointwise intersection is at least as strong.

### Oscillatory rather than absolute integration

There is a much smaller alternative for the integral corrections in (1):
\[
\begin{split}
 J_H(L)&=.1e^{-L/2}+10^{-11}e^{-(1-b)L}+2.1e^{-L},\\
 J_A(L)&=K(L)\big(.2e^{-L/2}+2\cdot10^{-11}e^{-(1-b)L}+2.1e^{-L}\big).
\end{split}                                                    \tag{2}
\]
On \(x\ge2\), they bound the absolute values of the first and second integrals. Thus keep \([\delta_-(L)-J_H,\delta_+(L)+J_H]\) and \([\delta_-(L)/L-J_A,\delta_+(L)/L+J_A]\) among the intervals for \(H,A\).

Proof of (2): use Dusart (2.1), PDF pp. 3–4, with the symmetric ordinate cutoffs of the classical explicit formula, away from the countable jumps. The formula's midpoint convention at a jump is irrelevant to integration; the endpoint term in (1) is always the actual inclusive \(\delta(L)\). For compact log-intervals inside \((0,\infty)\), the truncated zero series converges in \(L^2\). Indeed, when integrating its squared modulus, the cross integral for \(\rho,\rho'\) has magnitude bounded by \(C\min(1,|\gamma-\gamma'|^{-1})\), using the complex primitive with exponent \(\beta+\beta'-2+i(\gamma-\gamma')\). Group the signed ordinates in unit intervals, with multiplicity \(O(\log(2+|j|))\) in bin \(j\) by CH2 Corollary B.3 (PDF p. 43). The double series of these cross-majorants is bounded by a constant times \(\sum_{j,k} w_j w_k/(1+|j-k|)\), where \(w_j=\log(2+|j|)/(1+|j|)\). This converges: when \(|j|\) and \(|k|\) are within a factor two, the sum over \(k\) for a fixed \(j\) is \(O(\log^3(2+|j|)/(1+|j|)^2)\); otherwise sum the farther bin first using \(1+|j-k|\gg 1+\max(|j|,|k|)\). This proves the Cauchy criterion in \(L^2\). The limit is the one in the classical formula by a.e. pointwise convergence and uniqueness in measure. Compact termwise integration is consequently justified for the two bounded kernels.

For \(H\) the full integral of each zero term is bounded by \(e^{(\beta-1)L}/|\rho(1-\rho)|\). For \(A\) integrate against \(K\) by parts using a primitive from infinity: the term is bounded by \(2K(L)e^{(\beta-1)L}/|\rho(1-\rho)|\), since \(K\) is decreasing. The same estimates with harmless factors of two dominate compact integrations with moving upper bound, so infinity can be passed through the series. CH2 Corollary B.2 bounds \(N(t)\le(t/2\pi)\log(t/2\pi)\), with no positive ordinates below 14. Hence
\[
 2\sum_{\gamma>U}1/\gamma^2
 \le (2/\pi)(1+\log(U/(2\pi)))/U
\]
at \(U=14,H_0\), giving \(<.1,\ <10^{-11}\) respectively. Apply finite RH up to \(H_0\) and the B0/B1 strip to the rest. The nonzero elementary terms in \(\delta(v)\) are \(-e^{-v}(\log(2\pi)+\tfrac12\log(1-e^{-2v}))\), whose integrated absolute contribution is at most \(2.1e^{-L}\), or \(2.1K(L)e^{-L}\) for \(A\). This completes the estimates. One may retain the exact signed integral of these elementary terms with a symmetric bound only on the zero component.

### Prime powers, exact bias, and the products

Put \(T_0=\sum_{m\ge2,\,p^m>x}1/(m p^m)\), \(T_1=\sum_{m\ge2,\,p^m>x}\log(p)/p^m\), and \(U_0=\sum_{m\ge2,\,p>x}1/(m p^m)\). Then
\[
             E_S=A+T_0,\qquad E_W=H+T_1,\qquad Z=A+T_0-U_0=E_S-U_0.   \tag{3}
\]
In particular, the correction to \(A\) in \(Z\) is nonnegative, not arbitrary in sign, and there is no extra \(1/\log x\) loss for the weighted sum. Equalities at exact prime powers adopt the cutoff \(p^m>x\) in the tails.

For \(\theta\) use \(\epsilon(t)=20.83/(\log t)^3\) for \(t\ge2\) from Dusart Theorem 4.2; any stronger envelope may also be used in the integrals. Set \(y=\sqrt x,z_*=x^{1/3}\). When \(x\ge8\), an upper bound for \(T_1\) is
\[
 U_1(x)=\frac{1+3\epsilon(y)}y+
 \frac{2(1+\epsilon(z_*))+(\tfrac12+\tfrac52\epsilon(z_*))/(1-1/z_*)}{z_*^2}.
\]
A lower bound is \(\max(0,(1-3\epsilon(y))/y)\). For the square contribution use
\(\sum_{p>y}\log p/p^2=-\theta(y)/y^2+2\int_y^\infty\theta(t)/t^3\,dt\).
For the rest, primes \(p\le z_*\) have geometric tail at most \(2\log p/x\); for \(p>z_*\) bound by \((1-1/z_*)^{-1}\sum_{p>z_*}\log p/p^3\), and apply partial summation as for the squares. Always \(T_0\le T_1/L\) since \(m\log p>L\). Its lower bound is \(\ell(\sqrt x)\) with
\[
 \ell(t)=\max\{0,[1/(\log t+1)-3\epsilon(t)/\log t]/(2t)\}.
\]
Indeed keep only the squares and integrate \(1/(w^2\log w)\) against \(d\theta(w)\); the main integral against \(dw\) is \(\ge1/[t(\log t+1)]\) by the substitution \(w=te^u\) and convexity with the probability density \(e^{-u}\). The absolute error is \(\le3\epsilon(t)/(t\log t)\) by partial summation. Also \(0\le U_0\le (1+3\epsilon(x))/(2(x-1)L)\) by the same upper bound for \(\sum_{p>x}1/p^2\) and the geometric tail. The identical calculation at an arbitrary prime cutoff \(t\) justifies the normalization intervals in sieve.cpp. For \(2\le x<8\) the same identities hold and the tail sums themselves, or elementary geometric/integer bounds, can be used instead.

Use (3) to intersect signed intervals for all three errors, with lower and upper bounds on the positive tails; for \(T_0-U_0\) keep at least zero as its lower bound. Retain the original direct sum bounds: \(.2/L^3\) for \(E_S\) at \(x\ge2278383\), \(.3/L^2\) for \(E_W\) at \(x\ge912560\), and \(.2/L^3\) for both product errors at \(x\ge2278382\) (Dusart Theorems 5.6, 5.7, 5.9, PDF pp. 17–20). In the asymptotic part of Dusart's proof of 5.9, also retain the direct signed exponential consequences of its \(.1973/L^3\) and its tail bound (or compute them by the sharper pointwise \(\theta\) transfer above). Two direct relative product bounds \(\eta<1\) for both \(P,Q\) imply \(-\log(1+\eta)\le Z\le\log(1+\eta)\); individual relative bounds can be intersected by applying the logarithm separately. After all intersections, if \(Z\in[l,u]\), the separate product envelopes are \(\max(e^{-l}-1,1-e^{-u})\) and \(\max(e^u-1,1-e^l)\), respectively. In particular, keep both reciprocal branches rather than using an avoidable factor two. These pointwise instructions compare domains without requiring a single choice of branch for all \(x\).

## Simple whole-ray exponential bounds and comparison

For every row \((\mathrm{mode},u,c)\) in mertens.py, with \(a=1/8\) in B0 and \(a=5/32\) in B1, the following hold for all \(x\ge e^u\):
\[
 |E_W|\le c x^{-a},\qquad
 |E_S|,\ |e^\gamma L P_{\rm raw}-1|,\ |e^{-\gamma}Q_{\rm raw}/L-1|
       \le c x^{-a}/L .
\]
There are also the early-envelope rows \((0,40,.01334)\) and \((1,40,.2665)\). The certificate evaluates \(e^{a u}G_b(u)\); \(e^{aL}G_b(L)\) thereafter decreases termwise (weakly for the top rate), and so do the appropriately scaled tail/oscillatory corrections \(e^{aL}(J_H+U_1)\), \(e^{aL}(LJ_A+U_1)\). If the log-product radius is \(D\le1/2\), both relative errors are \(\le D(1+2D)\). For the early-envelope rows, on the interval up to the listed pivot \(v\) bound the renormalized CH2 constant term by its value at \(v\) and the renormalized square-root term by its value at 40. Use the spectral proof starting at the pivot. This ensures both joins and the full infinite ray. The code represents the real exponent \(a\) exactly. For example, at \(\log x=200\), the B1 coefficient .222 suffices; at 300 it is .172. This replaces the logarithmic loss of the direct assumption rather than just tightening its coefficient. Constants with later domains are kept when stronger pointwise.

For two such branches with coefficients \(c_0,c_1\), the B1 branch improves the B0 branch exactly when \(L>32\log(c_1/c_0)\), on the intersection of the stated domains (equality is a tie). This applies to each of the four quantities with its matching logarithmic factor. For the primary smoothed pointwise branch using \(\min(C,G_b)\), the B1 envelope is never worse; from \(L=170\) its \(\delta\) radius is strictly smaller (verify against the CH2 floor at 170 and use monotonicity; clipping shows strict improvement against \(G_{7/8}\)). Its \(J\) terms are also smaller. Hence the primary absolute envelopes improve strictly on this ray for both product errors and both sums. Earlier or competing finite-source/transfer branches are handled by intersection, not assumed strictly improved. At large \(L\) the matched original logarithmic and stretched-exponential error branches are weaker than the B0 exponential reconstruction, not a suitable substitute for it. The reconstructed bounds are not claimed optimal over all proofs possible from B0.

## Finite and logarithmic options

The following are sufficient real onsets for errors at most \(c/L^3\) for each product and the reciprocal sum, or \(c/L^2\) for the weighted sum:
\[
\begin{array}{c|rrrr}
 c & P& Q&E_S&E_W\\ \hline
 .10&12911611&12911611&12914903&18002111\\
 .15&5001809&5001809&5001809&7105289\\
 .20&2278381.578425&2278381.714012&2278382.179859&3452179\\
 .25&1514831&1514831&1514831&1520747\\
 .30&624917&624917&624917&912559.997526\\
 .40&359837&359837&359837&368359\\
 .60&96043&96043&96043&155921\\
 1&24317&24317&24317&24571
\end{array}
\]
Every line uses only B0. The smallest tabulated coefficient .10 joins to the analytic bounds from \(e^{18}<67000000\) (for \(E_W\), .086 and for the other three .091). The improvement of the product and reciprocal-sum real onsets at .20, and of the weighted onset at .30, is inside the final uncertified gap of the coarse cell method. The integral part of each of these old onsets is unchanged when converting to inclusive integer statements. These small gains are sufficient, not optimal. For the four special refinements, the differential check is as follows. Within the gap, write \(z_P=\log(e^\gamma L P_{\rm raw})\), with \(d z_P/dL=1/L\). The signed normalized product errors multiplied by \(L^3\) have derivatives \(L^2(4e^{z_P}-3)\) and \(L^2(2e^{-z_P}-3)\). The analogous signed derivatives for the sums are \(L^2(3E_S-1)\) and \(L(2E_W-L)\). In these gaps the intervals certify all unscaled errors needed for these tests are small (absolute logarithmic product and centered sums \(<.1\), and \(L>10\)). Each signed scaled error is therefore monotone, so checking both endpoints of the sliced gap bounds its greatest absolute value.

The finite replay sieves through \(67000000\) by Eratosthenes. It sums each normalizer up to that point, enclosing the missing tail by the previous partial summation estimates and bounding \(\gamma\) by the same elementary trapezoid proof as for the Ramanujan calculation. On each prime gap, the log product and the centered prime sums vary monotonically; check their appropriate interval endpoints with the greatest value of \(L^k\) on the closed cell. At the next prime check the updated side in the next cell, or as the individual terminal point. For \(0\le t\le1/2\) the C++ code bounds \(e^t-1\) by \(t+t^2/[2(1-t/3)]\) and \(1-e^{-t}\) by \(t-t^2/2+t^3/6\), keeping separate checks of both products. All arithmetic in the gap tests is fixed-point with outward rounding. Its last-uncertified-cell right endpoints are not claimed to be failures or optimal onsets.

Additional pure-logarithmic profiles are certified by mertens.py. Its LOGS rows \((\text{mode},u,k,c_W,c_P)\) mean \(|E_W|\le c_W/L^k\) and the other three errors \(\le c_P/L^{k+1}\) for \(L\ge u\). For example the product/reciprocal-sum \(L^{-7}\) coefficient at \(u=55\) decreases from 44.10 to 23.90; for \(L\ge175\) B1 achieves 10.15 there, compared with the exhibited weaker 11.61 B0 certificate at \(u=200\). Likewise compare the \(L^{-9}\) rows at \(u=40\) (1534000 vs. 901000). These are exact sufficient constants and comparator onsets, not fitted optima. In each log-cell use the decreasing error bounds at its left endpoint and the powers \(L^k\) at its right endpoint, including the right limit when crossing a finite-source cutoff. Beyond 320 use the just-proved exponential branch: the rescaled \(L^j e^{-aL}\) decreases for the tested exponents. All valid estimates, including these input-independent early improvements, are kept by pointwise minimum on matched domains.

For differing pure logarithmic exponents the comparison is exactly the comparison of \(L^{k_1-k_0}\) with the ratio of the constants, reversing when testing the opposite inequality. To compare a power-exponential bound \(c x^{-a}/L^d\) with \(\eta/L^k\), compare the ratio \((c/\eta)L^{k-d}e^{-aL}\) with 1. It is decreasing for \(L>(k-d)/a\), so after this point one verified endpoint comparison gives whole-ray dominance, and otherwise any crossing there is unique. Before that point it is increasing when \(k>d\), so the turning point and the matching domain suffice. In particular the B0 exponential bounds already improve Dusart's .2 and .3 bounds for every \(L\ge40\) (insert the early B0 row at 40, then use the decreasing ratio). B1 does not replace the earlier finite-source branches.
