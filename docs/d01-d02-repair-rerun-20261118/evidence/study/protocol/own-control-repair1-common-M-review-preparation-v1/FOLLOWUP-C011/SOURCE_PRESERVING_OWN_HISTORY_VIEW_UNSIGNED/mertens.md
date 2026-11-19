# Mertens products and prime sums

See **upgrade.md** for tighter coefficients and onsets, additional early connected and finite branches, and stronger density-free comparisons. The results below are the retained base portfolio.

For \(x\ge2,\ L=\log x\), write
\[
 S(x)=\sum_{p\le x}1/p-\log L-M,\qquad
 W(x)=\sum_{p\le x}(\log p)/p-L+B_3 .
\]
As in Dusart Thms. 5.6–5.7 (PDF pp. 17–19),
\[
 M=\gamma+\sum_p[\log(1-1/p)+1/p],\qquad
 B_3=\gamma+\sum_{m\ge2}\sum_p(\log p)/p^m .
\]
Let \(\Delta(x)=\log Q_{\rm raw}(x)-\gamma-\log L\). The requested errors are \(|e^{-\Delta}-1|\) for \(P_{\rm raw}\) and \(|e^\Delta-1|\) for \(Q_{\rm raw}\).

## Main late bounds and matched comparisons

Each row below means simultaneously
\[
 |W(x)|<C x^{-d},\qquad
 |S(x)|,\ |e^{-\Delta(x)}-1|,\ |e^{\Delta(x)}-1|<C x^{-d}/L .
\]
All onsets are closed and refer to \(L\).

| Onset | B0 \(d=1/8\): \(C\) | B1 \(d=5/32\): \(C\) |
|---:|---:|---:|
|160|.0227|.321|
|250|.0162|.227|
|400|.0136|.191|

The larger B1 prefactors do not imply a weaker bound: for the first row the ratio is \((.321/.0227)e^{-L/32}\), less than 1 throughout \(L\ge160\); the other rows also give strict same-onset improvements on their entire rays. The same ratio argument applies to finer anchor-dependent coefficients given below. These pure-power rays use the locally tuned density weights in common.md; the simpler uniform-weight certificates are also retained in certificate.log. Signed tail integration leaves a factor \(1/L\) on each reciprocal-prime or product error, and no logarithmic loss for \(W\). An independent-of-density-table branch on \(L\ge200\) gives, under the exact input, \(0.015626\,x^{-5/32}L^2\) for \(|W|\) and \(0.015626\,x^{-5/32}L\) for the other three errors (all strict).

For a **fixed** logarithmic-format margin \(\eta\), the following are certified closed onsets for \(|W|<\eta/L^2\) and each other error \(<\eta/L^3\). These use anchor-dependent constants, not rounded constants from the previous table.

| \(\eta\) | B0 | B1 |
|---:|---:|---:|
|\(10^{-8}\)|201|177|
|\(10^{-10}\)|240|207|
|\(10^{-12}\)|278|238|
|\(10^{-16}\)|355|299|
|\(10^{-20}\)|431|360|
|\(10^{-24}\)|507|421|

A purely B0 collection of simultaneous all-ray margins in this format is also useful, since fixed-coefficient comparisons with the old Dusart rays can be made much earlier than the D02 improvement: \((L_{\min},\eta)=(23.25,.2),(26.5,.05),(30.25,.01),(36.25,.001),(53,10^{-6}),(62,10^{-7})\). In each case past a finite join use the B0 power bound. Keep all the separate earlier Dusart rays, and the exact real repairs below. There is no blind-run or best-known claim.

## Identities and prime powers

Use \(u(v)=\sum_{n\le e^v}\Lambda(n)/n-(v-\gamma)\) and \(z(v)=\sum_{2\le n\le e^v}\Lambda(n)/(n\log n)-(\log v+\gamma)\). With \(x=e^L\), define
\[
 C_w=\sum_{p^m>x,m\ge2}(\log p)/p^m,\quad
 C_s=\sum_{p^m>x,m\ge2}1/(mp^m),\quad
 C_Q=\sum_{p\le x,\ p^m>x,\ m\ge2}1/(mp^m).
\]
Then \(W=u(L)+C_w,\ S=z(L)+C_s,\ \Delta=z(L)+C_Q\). The tail caps are \(0\le C_w\le G(L)=4e^{-L/2}+10e^{-2L/3}\), and \(0\le C_Q\le C_s\le G(L)/L\). For \(m=2\) use \(\theta(y)\le2y\) (Dusart Thm. 4.2, table PDF p. 11) in partial summation from \(\sqrt{x}\). For \(m\ge3\), on \(p>x^{1/3}\) the full geometric series is at most \(2/p^3\) and integration gives \(6x^{-2/3}\). On \(p\le x^{1/3}\) the first allowed power term is \(<1/x\), the series is at most \(2/x\), and \(\theta(x^{1/3})\le2x^{1/3}\). Divide termwise by \(\log(p^m)>L\) for the other caps. One can optionally sharpen the squared-prime contribution to \(C_w\) with its exact formula \(-\theta(\sqrt x)/x+2\int_{\sqrt x}^\infty\theta(t)t^{-3}dt\) and the θ envelope below.

Partial summation, anchoring at infinity, gives
\[
\begin{aligned}
 u(L)&=e_\psi(L)-\int_L^\infty e_\psi(v)\,dv,\\
 z(L)&=e_\psi(L)/L-\int_L^\infty e_\psi(v)(1/v+1/v^2)\,dv,\\
 z(L)&=u(L)/L-\int_L^\infty u(v)/v^2\,dv .
\end{aligned}\tag{7}
\]
Indeed both centered errors tend to zero by the corresponding Dusart prime-sum limits and the power-tail estimates, and the displayed integrals converge with the ψ estimates. All jumps are included at the right, hence these equalities hold also at integers and prime powers. Alternatively use \(e_\theta(v)=e^{-v}\theta(e^v)-1\) in the first two equations to obtain \(W,S\), and then \(\Delta=S-\sum_{p>x,m\ge2}1/(mp^m)\). The latter subtracted term is at most \(4e^{-L}/L\): use \(\sum_{m\ge2}1/(mp^m)\le1/p^2\) and the θ bound. The exact callbacks to Dusart here are for constants/limits, not their error sizes in the new late result.

Use (4) from common.md for the signed ψ integrals in (7). A simultaneous log-error bound is
\[
 |\Delta|,\ |S|\ \le J_b(L)=
 \frac{E_b^\theta(L)+(1+1/L) B_d(L)+G(L)}{L},
 \qquad |W|\le L J_b(L).
 \tag{8}
\]
One may use \(L_b\) rather than \(E_b^\theta\) in (8), or just \(E_b\): the stronger endpoint is valid by (2). For a simple constant on \(L\ge a\ge160\), set
\[
 Z_a=C_b(a)+e^{da}\big[(1+1/a)B_d(a)+G(a)\big].
\]
Termwise \(e^{dL}\) times the numerator in (8) is nonincreasing on the ray. Since \(e^y-1\le y/(1-y)\) for \(0\le y<1\), take any \(C>Z_a/(1-Z_ae^{-da}/a)\) with positive denominator. This proves the power table by interval checks at its anchors and the log-rate table since \(L^2e^{-d L}\) decreases there. The density-free D02 branch uses \(v^2e^{-5v/32}/64\) instead of \(E_b^\theta\); divide the scaled tails by \(L^2\) and check at 200. Each missing term decreases thereafter (compare \(L^2e^{-dL}\) or \(Le^{-dL}\) as appropriate). Signed integration is essential for the displayed density-free coefficient near \(1/64\); integrating the unsigned D02 majorant alone costs about \(1+1/d\).

For the B0 logarithmic-format tradeoffs at earlier \(L\), CH2 gives \(|u(v)|\le A+114e^{-v/2}\) globally or \(a_T'+C_Te^{-v/2}\) for \(e^v>\max(T,10^9)\), with \(a_T'=\pi/(T-1)\); the verification may round this to \(a_T\) from common.md. In either case write \(a,c\) for the two coefficients. By the third formula (7),
\[
 |W|\le a+(c+4)e^{-L/2}+10e^{-2L/3},\qquad
 |S|,\ |\Delta|\le J=\{2a+(c+4+2c/L)e^{-L/2}+10e^{-2L/3}\}/L.
\]
For fixed \(T\) this remains valid on the entire larger ray, even if a different \(T\) works better there. On quarter-unit cells \([l,r]\) up to the indicated join (160, 170 or 215), bound \(L^3 J/(1-J)\) by evaluating the constant term \(2a L^2\) at \(r\), the decaying exponentials times their powers at \(l\), and \(1/(1-J)\) at \(l\). The single B0 density ray at the join covers everything thereafter. The family of all fixed \(T\)'s can be used in the envelope instead of prescribed sampled heights.

## Whole-domain envelopes and what the comparisons mean

The following specifies simultaneous numerical envelopes for all real \(x\ge2\), including where none of the displayed simple late inequalities is yet available. Infima are of **valid bound values**, not of observations. They can be evaluated using convergent elementary integrals, or enclosed by finite integration followed by the explicit power tails. Intersect intervals, and keep direct relative-product controls on their given scale.

* For relative ψ take the minimum of applicable: CH2 Cor. 1.2 (all permissible \(T\)), 1.3 and 9.3; FiniteRH Cor. 1; Dusart Prop. 3.2 Table 1 (PDF pp. 8–9) and Thm. 3.3; FKS Cor. 1.4, Thms. 1.1–1.2 formula families (4.1), (5.2) at their legitimate parameters, and their tabulated controls (Tables 5–6, pp. 22–23); PT 1809.03134v2 Thm. 1 Table 1; (2) and (3) of common.md. The source-row numbers needed for straightforward evaluation are in source_rows.json, generated from the bound originals. Use the original hypotheses at row endpoints (where \(x_0>e^{1000}\) is required there is no need to admit the row with exponent exactly 1000). At \(x=2\) do not use the open FKS Cor. 1.4 domain. B1 keeps the B0 branches and adds both B1 variants and the literal D02 majorant on \(L\ge200\).
* For θ take the ψ bound plus the prime-power bound (common.md), and the minima with Dusart Thm. 4.2 (all rows), FiniteRH Cor. 1, and PT 1809.03134v2 Cor. 1 (all rows). For shifted intervals one can intersect the symmetric bound with the interval obtained by subtracting a number in \([0,(\psi-\theta)_{\rm cap}/x]\) from the ψ interval. The same pointwise θ input is available to the Ramanujan envelope.
* For \(u\), take the CH2 weighted bounds and (7): keep the best endpoint ψ bound, use the minimum of integrated absolute envelope and the applicable signed bound (4). For \(z\), similarly use both formulas (7), allowing the best \(u\) envelope in the last integral, not only one original \(T\). Keep the θ-based alternatives for \(W,S\). Add the positive power-tail intervals to \(u,z\) as appropriate, and use \(\Delta=S-\sum_{p>x,m\ge2}1/(mp^m)\) as an additional log control. From any logarithmic interval \([\ell,u]\), the sharp transformed envelope from that interval alone is \(\max(|e^\ell-1|,|e^u-1|)\) for \(Q\) and \(\max(|e^{-\ell}-1|,|e^{-u}-1|)\) for \(P\).
* Intersect with all the direct Dusart 5.6–5.9 error bounds (Theorem 5.9 statement is PDF p. 19), the local repairs and all the simple bounds above on their valid domains. The error bounds for \(P,Q\) and the related prime sums are correlated, not independent tests.

This gives whole-domain non-worsening, not a claim that no other argument using B0 can do better. It is substantial to compare against the reconstructed QRH branches, not only the literal Dusart estimates. For example one can prove **strict dominance on the entire ray \(L\ge170\)** against the explicit B0 envelope just specified (using the numerical rows, fixed-height CH2 family and the common reconstruction). Here are lower comparisons for the *bound values*, not for the actual errors:

1. For \(L\ge170\), the B0 endpoint radii for ψ, θ, and the independent CH2 weighted bound are all at least
\[
 q(L)=\min(1.04\cdot10^{-12},.0039e^{-L/8}).
\]
CH2 weighted and ψ have constant floors at least \(\pi/(H_*-1)\); for the centered ψ form the shift is less than \(10^{-6}\) times its radius. The finite RH rays and Cor. 9.3 have expired. For the B0 telescoping density bound use the last six grid increments, all with \(Z\ge Z(.8745)>.011\), so their sum is \(\ge .011(1-e^{-.003L})e^{-L/8}\). The tuned grid works as well: its last twelve increments have \(Z>.0107\), giving \(.0107(1-e^{-.003L})e^{-L/8}\). The no-density bound is larger. The minima with the tabulated rows and elementary powers preserve the lower comparison: source_rows.py checks the left comparisons to \(.0039e^{-L/8}\), and the logarithmic decay rates of each stretched-exponential row and elementary powers are smaller than \(1/8\) throughout each relevant ray. Constant rows need only the left test. Even reoptimizing FKS (4.1) does not upset this comparison: at its anchor \(L_0>1000\), either \(T\le H\) and \(\epsilon_1\ge2L_0^2/H\), or \(T>H\) and \(\epsilon_2\ge (e^{-L_0/10}-e^{-L_0/2})2R(H)/H>.99\cdot10^{-12}e^{-L_0/10}\), using their (2.1), (3.7)–(3.11) with \(\sigma_1=.9\) and Rosser's constants for the counting-error function \(R(H)\). For FKS (5.2), the additive \(6.8979\cdot10^{-6}\) bounds \(A(x_0)\) below, and any lawful zero-free parameter \(R\) satisfies \(R>2/\log100\) by the existence of the first zero at height \(14\ldots\) (CH2 Lemma B.7 proof, PDF p. 46) on the line; otherwise its real part .5 would be in the excluded region. These lower bounds on the explicit formulas suffice at 1000 and then by logarithmic decay comparison. Direct Dusart output bounds likewise exceed \(q\) in the weighted scale and \(q/L\) in the other scales. The local small-x repairs have expired.
2. The transferred bound intervals have the endpoint radius plus a nonnegative integral allowance; any possible shifts from prime-power terms are at most \(2G(L)\) in the weighted scale or \(2G(L)/L\) in the other scales. For \(L\ge170\) these shifts are less than \(.001q\) (check at 170 and compare decay rates). Thus intersecting preserves a centered interval of at least \(.998q\), or \(.998q/L\) respectively. Converting the product intervals preserves a relative radius of at least \(.99q/L\) (using \(1-e^{-t}\ge t-t^2/2\)); the claims are about these displayed enclosures, not a lower bound on actual arithmetic fluctuations. This argument also permits using the simple B0 log and power table rows in the minimum, since each has radius at least \(q\) or \(q/L\) wherever applicable.
3. Conversely \(.321e^{-5L/32}<.99q(L)\): verify both comparisons at 170, then use \(5/32>1/8\). Hence the B1 error envelopes beat all these explicit B0 branch values throughout this ray. The same estimates include the source-only envelope that omits the new B0 reconstruction. No universal comparison with every possible reoptimization/argument from B0 is asserted.

## Exact small-x real onsets, B0 only

Dusart's coefficient .2 for \(S\) and the two relative products, and .3 for \(W\) (with the original powers), admit the following least real closed onsets. These are roots of the normalized positive errors on the indicated single prime gap; the brackets are strict.

| Error | Coefficient and power | Root bracket |
|---|---|---|
| \(|S|\) | \(.2/L^3\) | \((2278382.112,2278382.114)\) |
| \(|W|\) | \(.3/L^2\) | \((912559.997,912559.998)\) |
| \(|e^\Delta-1|\) | \(.2/L^3\) | \((2278381.711,2278381.712)\) |
| \(|e^{-\Delta}-1|\) | \(.2/L^3\) | \((2278381.575,2278381.576)\) |

Before the root the bound fails locally, at the root equality holds, and from there through the original onset it holds; later it holds non-strictly by the original theorem. Thus the integer onsets are unchanged. These refinements use neither D02 nor QRH. For \(|W|\) the gap from the last prime to the old onset is \([912559,912560]\); in the other cases start at 2278379, with no further prime through 2278383 (the product join is at 2278382). On these gaps the centered errors \(S,W,\Delta\) are positive and \(<.01\), by the endpoint estimates and monotonic decrease before normalization. The derivatives of \(L^3S,\ L^2W\) are negative (\(3S-1<0,\ 2W-L<0\)); for \(L^3(e^\Delta-1)\) the sign is that of \(3(e^\Delta-1)-e^\Delta\), and for \(L^3(1-e^{-\Delta})\) the sign is that of \(3(1-e^{-\Delta})-e^{-\Delta}\). Both are negative on these gaps. Thus endpoint sign checks and the intermediate value theorem certify the unique roots without sampling the whole gap.

small.py uses an exact Eratosthenes sieve through \(N=8\cdot10^6\) and directed arithmetic for the cumulative sums and constants. For \(\gamma\), the trapezoid sum for \(1/t\) gives
\(0\le\gamma-(H_g-\log g-1/(2g))\le 1/(6g^3)+1/(12g^2)\) at \(g=10^5\); each trapezoid error is at most \(\sup|f''|/12\). For the constants, use \(|\theta(t)-t|\le\epsilon t\) for \(t\ge N\) with \(\epsilon=.2/\log^2N\), from Dusart Thm. 4.2 (table PDF p. 11; surrounding argument pp. 11–12). The tail for \(B_3\) has main term \(1/N\) from \(p^{-2}\), error at most \(3\epsilon/N\) from partial summation, and higher powers nonnegative at most \(6/N^2\) by \(\theta(t)\le2t\). For \(M\)'s subtracted tail use the weight \(g(t)=1/(2t^2\log t)\): its integral is \(\frac12\int_{\log N}^\infty e^{-v}/v\,dv\); θ uncertainty is at most \(3\epsilon/(2N\log N)\) by partial summation. Eight integrations by parts bracket this integral with the alternating factorial expansion and the first omitted term. Higher powers in \(M\)'s tail add at most \(3/(N^2\log N)\) by the same θ control. Finite evaluation of \(\sum_{m\ge2}1/(mp^m)\) keeps terms 2–4 for \(p\ge1000\) and bounds the tail by \(2/(5p^5)\); for smaller primes it uses the exact log identity. These bounds justify both constants and local signs. Failure at any point arbitrarily close below each root proves minimality for that coefficient on a final real ray, regardless of additional hypotheses.

## Remaining power bottleneck

A better power exponent is not just a matter of sharpening the prime-power correction. If, for some \(d'>5/32\), one proved \(W(x)=O(x^{-d'}(\log x)^k)\), partial summation in \(\sum_p(\log p)p^{-s}\) gives
\[
 \sum_p\frac{\log p}{p^s}=\frac1{s-1}-B_3+(s-1)\int_1^\infty W(x)x^{-s}\,dx
 \quad({\rm Re}\,s>1)
\]
(with the same normalization extended below 2). The last integral continues to \({\rm Re}\,s>1-d'\). Adding the absolutely convergent \(m\ge2\) terms, holomorphic for \({\rm Re}\,s>1/2\), would exclude zeros with \({\rm Re}\,s>\max(1-d',1/2)\). Bounds for \(S\) with the same better exponent imply such a \(W\) bound with one extra \(\log x\), by partial summation with weight \(\log x\); a better relative product exponent first transfers to \(\Delta\), then to \(S\) at a cost \(O(1/(x\log x))\). Thus a power improvement beyond \(5/32\) would need genuinely stronger zero information. This does not preclude better coefficients or logarithmic savings at the same boundary.
