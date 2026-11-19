# Mertens products and prime sums: signed error envelopes and earlier domains

Assume B0 only; the D01 comparison holds on every domain by common.md. Define
\[
\begin{split}
 C_P&=e^\gamma L P_{\rm raw}(x), & C_Q&=e^{-\gamma}Q_{\rm raw}(x)/L,\\
 E_1&=\sum_{p\le x}1/p-\log L-M,&
 E_{\log}&=\sum_{p\le x}(\log p)/p-L+B_3 .
\end{split}
\]
Here \(M=\gamma+\sum_p(\log(1-1/p)+1/p)\) and \(B_3=\gamma+\sum_p\log p/[p(p-1)]\), exactly as in Dusart Theorems 5.6–5.7 (PDF pp.17–19). All x are real, with the right-continuous prime cutoff \(p\le x\).

## Results and comparisons

1. For \(x\ge10^5\), each of \(|C_P-1|,|C_Q-1|,|E_1|\) is **less than** \(0.01970\,x^{-1/8}/L\), and for \(x\ge500000\), \(|E_{\log}|\) is **less than** \(0.01970\,x^{-1/8}\). Replace 0.01970 by any applicable smaller coefficient from this closed-ray table. For \(L\ge a\) use:
   
   | \(a\) | 200 | 300 | 500 | 1000 | 3000 | 30000 | 1000000 |
   |---|---:|---:|---:|---:|---:|---:|---:|
   | coefficient | .01886 | .01517 | .01311 | .01183 | .01099 | .01052 | .01046 |

2. The signed envelopes below give smaller bounds than the power table at many points, including the short and middle log ranges. In particular a single piecewise branch \(1.0001\,W(L)\), divided by L for the first three errors, is **strictly stronger than Dusart's** \(0.2/L^3\) (three errors) and \(0.3/L^2\) (weighted sum) at **every** \(L\ge17\). Here \(W\) is specified below. This comparison uses monotonic inequalities across the full domains, not an estimated crossover. For a direct comparison of the uniform .01970 power profile alone against the original polynomial constants, \(0.01970 L^2e^{-L/8}\) increases up to 16 and then strictly decreases. On the original matched domains the power profile is weaker until a unique crossover in \(40<L<41\) for .2 and \(35<L<36\) for .3, and stronger thereafter. The interval brackets and value at the earlier domain endpoint are directed checks in mverify.py. Take the minimum of the branches, not a replacement of the better earlier branch by a worse power envelope.

3. **Early rays.** The following constants bound the errors after multiplication by \(L^3,L^3,L^3,L^2\) respectively, from the indicated **real** onset inclusive to infinity. The extended checks after this table strengthen some entries further. These are earlier onset / larger coefficient tradeoffs, with complementary exact finite-interval branches.

   | onset x | P | Q | reciprocal sum | weighted sum |
   |---|---:|---:|---:|---:|
   | 2 | 3.826 | 3.960 | 3.971 | 4.551 |
   | 1000 | 2.247 | 2.261 | 2.271 | 2.570 |
   | 10000 | 1.266 | 1.268 | 1.271 | 1.414 |
   | 100000 | .596 | .596 | .597 | .656 |
   | 500000 | .343 | .343 | .343 | .372 |
   | 900000 | .288 | .288 | .288 | .313 |
   | 1000000 | .275 | .275 | .276 | .296 |
   | 2000000 | .209 | .209 | .209 | .2248 |

   Additional weighted whole-ray coefficients are .30151 from 912000, .212 from 3000000, .162 from 5000000 and .130 from 10000000. The last number .130 applies on that ray to **all four** scaled errors. Further simultaneous coefficients for the first three scaled errors are .19844 from 3000000, .15013 from 5000000, and .120 on \([10000000,66000000]\) (retain the finite .120 even though the combined ray uses .130).

   **Matched fixed-margin onsets and matched fixed-onset improvements.** New strict inequalities on the entire rays:
   
   | error(s) | scaled coefficient | real onset |
   |---|---:|---:|
   | both products | .2 | 2278381.8 |
   | both products | .19999 | 2278381.9 |
   | both products | .19998 | 2278382 |
   | all first three errors | .2 | 2278382.2 |
   | all first three errors | .19992 | 2278383 |
   | weighted sum | .3 | 912559.998 |
   | weighted sum | .2999995 | 912560 |
   
   The fractional onsets are real numbers, not rounding rules. Join each finite certificate to the analytic .130 bound from \(e^{18}\). The original Dusart 5.6, 5.7, 5.9 (PDF pp.17–20) non-strict error bounds are retained starting at \(2278383,912560,2278382\), respectively. Within these exact domains use them in the pointwise minimum. Below 2 the sums and raw products are identically 0 and 1 respectively (use the definitions of the normalized errors for \(1<x<2\)). No nearest-integer interpretation of the onsets is used.

The proof of redundancy matches all old and new branches on any matched domain, regardless of relative strengths of individual branches. In particular D01 cannot lower an onset at fixed tolerance, or improve a tolerance at fixed onset, over the entire lawful B0 envelope.

## Prime-power accounting and two exact transforms

For \(L>0\) put
\[
 K(t)=t^{-1}+t^{-2},\quad
 U=\sum_{p\le x,\ p^m>x,\ m\ge2}\frac1{m p^m},\quad
 T_0=\sum_{p>x,\ m\ge2}\frac1{m p^m},\quad
 V=\sum_{p^m>x,\ m\ge2}\frac{\log p}{p^m}.
\]
Then with \(u(t)=(\psi(e^t)-e^t)e^{-t}\),
\[
\begin{split}
 D_Q:=\log C_Q &= u(L)/L-\int_L^\infty u(t)K(t)\,dt+U,\\
 E_1 &=u(L)/L-\int_L^\infty u(t)K(t)\,dt+U+T_0,\\
 E_{\log}&=u(L)-\int_L^\infty u(t)\,dt+V .
\end{split}
\]
Partial summation of the end-inclusive weighted prime-power sums gives the local terms and the tails; the asymptotic constants are fixed by Dusart 5.6–5.9 and the prime-power tails tending to zero. For example \(\sum_{n\le x}\Lambda(n)/(n\log n)=\log Q_{\rm raw}(x)-U\); \(\sum_{n\le x}\Lambda(n)/n=\sum_{p\le x}\log p/p+\sum_p\log p/[p(p-1)]-V\). The integrals converge absolutely by common.md. Endpoint jumps affect the local terms, not the integrals. The inequalities \(0\le U\le U+T_0\le V/L\) follow from \(m\log p>L\).

For \(x\ge4\), separate \(m=2\) and put \(y=\sqrt{x}\). Partial summation over \(p>y\) shows
\[
 \sum_{p>y}\log p/p^2=-\theta(y)/y^2+2\int_y^\infty\theta(z)z^{-3}\,dz
 \le (1+7.3938/L)e^{-L/2}.
\]
Indeed Dusart Thm 4.2 with \(k=1\) gives \(|\theta(z)-z|\le1.2323\,z/\log y\) there. For \(m\ge3,\ p>x^{1/3}\), use \(\sum_{m\ge3}p^{-m}\le2p^{-3}\) and \(\theta(z)\le2z\): the tail is at most \(6 x^{-2/3}\). This holds even for \(x^{1/3}<2\). For \(p\le x^{1/3}\), the geometric tail beginning with the first allowed power is at most \(2/x\) per prime before log weighting; the total is at most \(4x^{-2/3}\). Consequently
\[
 V\le V_b(L)=(1+7.3938/L)e^{-L/2}+10e^{-2L/3}.
\]
For all \(x>1\) one can use \(4e^{-L/2}+10e^{-2L/3}\) instead (drop the negative square-tail boundary term and use \(\theta\le2z\)). Also \(T_0\le1/(2\lfloor x\rfloor)\) for \(x\ge1\) by the geometric bound \(\sum_{m\ge2} p^{-m}/m\le1/[2p(p-1)]\) and the telescoping sum over integers. These bounds are not independent for U and \(T_0\): use \(V_b/L\) for the *combined* tail.

## Signed integrated cancellation

Bounding the transformed integral by \(\int|u|\) is a valid competing branch but on the limiting power scale costs large constants (up to a factor of 8 in the integral). Instead integrate the **zero sum** before taking absolute values. Define
\[
 J_j(L)=0.2j\,e^{-L/2}+2\cdot10^{-11}j\,e^{-L/8}+2e^{-L},\qquad j=1,2.
\]
For every \(L\ge1\),
\[
 \left|\int_L^\infty u(t)\,dt\right|\le J_1(L),
 \qquad \left|\int_L^\infty u(t)K(t)\,dt\right|\le K(L)J_2(L).
\]
More generally the first bound applies to \(j=1\) with constant kernel 1, and the second to any bounded nonnegative decreasing continuously differentiable kernel \(k\) on the ray with \(K(L)\) replaced by \(k(L)\).

**Proof and interchange.** Use Dusart (2.1), PDF pp.3–4, with symmetric ordinate truncation and half-value at jumps. On t compact in \([1,\infty)\), the zero series converges in \(L^2\) as well as pointwise off the jumps. To see this, FKS Lemma 2.1 and Remark 2.2 (PDF pp.4–5) give \(O(\log(n+2))\) positive ordinates in \([n,n+1)\), with an identical negative-ordinate bound. The integral of the product of any two exponentials \(e^{(\rho-1)t}\overline{e^{(\rho'-1)t}}\) on the compact interval has magnitude \(\ll (1+|\gamma_\rho-\gamma_{\rho'}|)^{-1}\) by integration by parts and \(0<\beta,\beta'<1\), uniformly in the pair. Group ordinates by unit bins. The resulting absolute double majorant for the series of integrated products is summable: same-sign comparable indices \(m\in[n/2,2n]\) cost \(O(\log^3(n+2)/n^2)\) after summing in m, and for \(m>2n\) the sum of \(\log(m+2)/m^2\) is \(O(\log(n+2)/n)\). Opposite signs have at least the separation used in the same estimates. Finitely many small bins cause no problem since they have finite ordinates bounded away from zero. Hence the tails are Cauchy in \(L^2\) and the limit agrees almost everywhere with (2.1), by the a.e.-convergent subsequence of \(L^2\) convergence. Now integrate against either kernel on a compact interval, and extend the integration to infinity: for kernel 1 the transformed term is bounded by \(e^{(\beta-1)L}/(|\rho||1-\rho|)\) on the infinite ray; bounded-interval integrals satisfy the same bound with factor 2 uniformly in the upper endpoint. For decreasing \(k\), integrating by parts in the complex exponential gives the bound \(2 k(L)e^{(\beta-1)L}/(|\rho||1-\rho|)\), also uniformly on finite intervals (boundary at the upper endpoint plus the variation of k costs at most \(k(L)e^{(\beta-1)L}\)). This makes the dominated interchange over the spectral series legitimate when taking the upper endpoint to infinity.

For constants, \(|\rho||1-\rho|\ge\gamma_\rho^2\); below H use finite RH, above H use QRH. From FKS Lemma 2.1 and its Rosser triple in Remark 2.2, \(N(t)<t\log t/5\) for \(t\ge100\): the error plus \(7/8\) is \(<4\log t\le(t/25)\log t\), and \(1/(2\pi)+1/25<1/5\). Dyadic blocks give the positive-ordinate sum \(\sum_{\gamma_\rho\ge y}\gamma_\rho^{-2}\le4(\log y+2\log2)/(5y)\) for \(y\ge100\), assigning all upper-endpoint ordinates to the next block. The first zero has ordinate \(>14\) (CH2 Appendix B, PDF p.43, opening of B.1, before Lemma B.1 in the extraction around physical LF 6133–6143); FKS Table 1 (PDF p.5) bounds \(\sum_{0<\gamma_\rho<100}\gamma_\rho^{-1}\) by .5922435112. Adding the dyadic bound at 100 and doubling gives \(<.2\) for all ordinates, while at H it gives \(<2\cdot10^{-11}\) for the high ordinates alone. The residual terms in (2.1), after normalization, have absolute value \(\le2e^{-t}\) for \(t\ge1\). These yield the asserted \(J_j\). No sign cancellation of zeros or unproved uniform convergence of the unsmoothed formula is assumed.

## Piecewise proof of the analytic constants

Use signed bounds \([u_-(L),u_+(L)]\) for u. On \(17\le L\le29\), CH2 Lemma 9.2 (PDF p.35, **its ψ estimate**) supplies \([-1.415,.791]e^{-L/2}\); no interpretation of the scaling of its displayed weighted-sum estimate is needed. On \([29,58]\) use \(|u|\le L^2 e^{-L/2}/(8\pi)\) from PlattTrudgianFiniteRH Cor. 1, PDF p.4. On \([58,189]\) use \(|u|\le c+113.67e^{-L/2}\) from CH2 Cor.1.3 (PDF p.3). Beyond 189 use D from common.md.

For weighted error and L times each of the log-product and reciprocal-sum errors one may bound the needed absolute values by
\[
 \max\{-u_-+(1+1/L)J_2,\ u_++(1+1/L)J_2+V_b\}.
\]
This is at most the following \(W(L)\) on the indicated intervals, using only comparisons with monotone majorants:
* \([17,29]\): \(3.25e^{-L/2}\).
* \([29,58]\): \((L^2/(8\pi)+3)e^{-L/2}\).
* \([58,189]\): \(c+117e^{-L/2}+5\cdot10^{-11}e^{-L/8}\).
* \([189,\infty)\): \(D(L)+(1+1/L)J_2(L)+V_b(L)\).

All joins are closed, with both branches applicable there. The first two bounds follow by scaling by \(e^{L/2}\); the small high-ordinate term then increases, and is tested at the right endpoint, the other nonconstant reserve terms at the left. For the third use the separate exponent forms and the bounds on their coefficients at 58. Where \(D_Q\in[-W/L,W/L]\), both relative product errors are bounded by \(e^{W/L}-1\le (W/L)e^{W/L}\). On \([17,189]\), \(e^{W/L}<1.0001\) by the first-row endpoint test and the strictly smaller subsequent bounds for \(W/L\) (also directly checked). On \([189,\infty)\) the same inequality follows from the density scaled test there.

For the shared power constants, \(e^{L/8}W(L)\) on the last branch is termwise nonincreasing, as is \(W(L)/L\). So it suffices to check \(e^{L/8}W(L)e^{W(L)/L}\) at each left threshold. To extend the first power constant back to 17, bound the scaled first branch at 17, the second at 29 (each power times exponential is decreasing), and the third by testing the rising floor at 189 and the decaying part at 58. On [14,17], the CH2 signed interval is still valid and the same endpoint tests give \(W\le3.75e^{-L/2}\); testing \(3.75e^{-3L/8}\exp(3.75e^{-L/2}/L)\) at 14 gives the first power constant on that entire band. On \([\log 10^5,14]\) for the first three errors, and \([\log 500000,14]\) for the weighted sum, use the certified early polynomial coefficients .597 and .372 respectively. The quotient \(e^{L/8}/L^2\) decreases up to 16, so testing those coefficients times this quotient at the left endpoints closes both finite joins. For strict dominance over Dusart, test \(1.0001 L^2 W(L)<.2\) similarly (powers times exponential decrease in the relevant ranges); beyond 189 use the uniform power branch and decreasing \(L^2e^{-L/8}\). The same comparison implies the stated .3 dominance for the weighted error. The proof with 18 in place of 17 yields the stronger common polynomial coefficients .130 on the ray L≥18. mverify.py performs the endpoint inequalities with directed arithmetic. All monotonic criteria just used follow by logarithmic differentiation.

## Pointwise signed intersection (including alternative transforms)

The following specifies a single pointwise envelope, not just the uniform power constants. All options are used only on their valid domains. Intersect signed intervals for the same quantity before converting to absolute errors.
* At each L take the intersection of the ψ intervals above, common.md for \(L\ge100\), CH2 Cor. 1.3 for all x, CH2 Cor. 1.2 for each admitted \(T\in[10^7,H]\) and \(x>\max(T,10^9)\) (use its stated shifted central term), and FKS Cor.1.4 (PDF p.2, \(x>2\)). Other literal applicable ψ rows (e.g. FKS Theorems 1.1–1.2 tables) may be intersected without changing the proof. Adding D01 to the intersection does nothing because D is already smaller at every allowed L.
* **For ψ only**, intersect the spectral tail bound \(J_j\) (with K multiplier as appropriate) with \([\int u_- k,\int u_+ k]\), where k is 1 or K. For both prime sums one can also use the separate transform with \(\theta\) in place of ψ and **omit** all prime-power correction terms; constants are the same (Dusart 5.6, 5.7). In this alternative use integrals of the signed **θ** endpoints, not the unshifted ψ spectral interval. The shifted spectral interval proved in spectral_repair.md is an additional valid branch. For \(\theta\), take the intersection of Dusart Thm 4.2's applicable error rows, the finite RH θ bound on its domain, and the interval obtained by subtracting \([\max(.9999,1-4/L^3)e^{-L/2},(1.000000147)e^{-L/2}+1.78e^{-2L/3}]\) from the ψ interval for \(x\ge121\) (use lower zero otherwise). For D_Q from \(E_1\), subtract \([0,1/(2\lfloor x\rfloor)]\); the identity is \(D_Q=E_1-T_0\).
* A competing weighted-ψ bridge uses \(A(t)=\sum_{n\le e^t}\Lambda(n)/n-t+\gamma\). Bound A using the above ψ transform (with no V), intersected with CH2 Cor. 1.2 for all valid T and Cor.1.3 on the whole domain. The log-product/reciprocal-sum core \(D_Q-U\) also equals \(A(L)/L-\int_L^\infty A(t)/t^2\,dt\), by Stieltjes integration. Intersect this interval too before adding the tails. All integrals of interval endpoints converge, since the density branch is present; these are explicit functions of L, not integrals of unknown primes.
* If \(D_Q\in[l,h]\) the relative product envelopes are separately \(\max(e^{-l}-1,1-e^{-h})\) for P and \(\max(e^h-1,1-e^l)\) for Q. For the sum errors use the maximum of an upper endpoint and the negative lower endpoint. Relative envelopes may also be converted back to signed log intervals before intersection; for example simultaneous original relative bounds \(d\) on P and Q give \(|D_Q|\le \log(1+d)\). Then take the minimum with every applicable displayed constant or original branch and with the finite exact-sieve branch (below). This operation is valid on the entire union, whether or not numerical branch-switch points are known. Literal Dusart branches have log normalization as above; they are not replaced by a bound valid only after a later crossover.

## Finite sieve and exact joins

early.py builds an ordinary Eratosthenes sieve through \(N_0=2278383\), marking from \(p^2\) (each composite has a smaller prime factor \(\le\sqrt{N_0}\)). It first encloses the normalizing constants using \(n=10^4\) for \(\gamma\): \(H_n-\log n-1/(2n)\le\gamma\le H_n-\log n-1/(2n)+1/n^2\). To see this, sum the trapezoidal errors for \(1/t\) on \([j,j+1]\), \(j\ge n\), using convexity and the bound \(2/j^3\) on the second derivative. The errors are between 0 and \(2/(12j^3)\); passage to the limit uses the definition of \(\gamma\). For M the omitted positive log remainder has magnitude at most \(1/(2N_0)\) by telescoping over integers. For \(B_3\), the omitted sum is \(\le(1+\log N_0)/(N_0-1)\) by monotonicity of \(\log t/[t(t-1)]\) and integration of \((N_0/(N_0-1))\log t/t^2\) from \(N_0\).

Each running prime sum and log-product is accumulated outward. On the entire interval between consecutive primes (left included, right excluded), use the constant arithmetic prefix and the interval of log x computed from the endpoints. Close the last interval through \(N_0\) and explicitly check the post-jump value if an endpoint is a prime. The maxima in early.log are upper bounds, not estimates of a true maximizer. For any specific x in this range the same prefix code and interval normalizers give a stronger pointwise branch by plugging in that x rather than taking a block maximum; no analytic extrapolation of the finite data is used. The whole-ray rows follow from the outward maxima through \(N_0\) and the original bounds from there onward. For the improved weighted rows below .300 use the extended join below, not just the \(N_0\) sieve. This finite calculation is independent of D01 and of the literature's finite prime tables.

**Extended finite weighted bridge.** weighted.py verifies the scaled error \(L^2|E_{\log}|\) through \(N_1=66000000>e^{18}\) with all onsets in the log output. All valid cells use prefix sums through their left prime. Bounds are exact integers at scale \(S=10^{20}\): prepare a logarithm bracket at the first prime n of each block, end the block before \(n+\max(1,\lfloor n/2048\rfloor)\), and for \(p=n+h\) add the rational lower \(h/n-(h/n)^2/2\) and upper \(h/n-(h/n)^2/2+(h/n)^3/3\) from the alternating series. Divide the outward brackets by p using floor/ceiling to accumulate the weighted prefix. For \(B_3\), use the same gamma bracket with \(n=10^5\) and the prime prefix through \(N_2=25000000\). The omitted prime tail is \(\int_{(N_2,\infty)} [t(t-1)]^{-1}\,d\theta(t)\). Its main term with \(d\theta\) replaced by \(dt\) is \(J=-\log(1-1/N_2)\); partial summation of \(|\theta(t)-t|\le\eta t\), \(\eta=.2/(\log N_2)^2\) (Dusart Thm 4.2), bounds the error by \(\eta[2/(N_2-1)+J]\). This improves the loose integer-tail normalization and is checked with outward arithmetic. Clip the first cell to L at the stated onset, and exclude the pre-jump cell if its right prime is exactly the onset. For a constant prefix on a cell the error is \(d=c_0-L\). The positive part of \(L^2d\) decreases if \(2d<L\) and the negative part of \(-L^2 d\) increases there. This holds throughout active cells by the upper error check \(d<1\) and \(L>2\). Thus bound the two parts separately at the appropriate left or right endpoint, using the local upper bound for the scaling factor. The final composite endpoint is evaluated as a closed upper endpoint. The analytic .130 bound from \(e^{18}\) completes the weighted rays without extrapolating the finite computation.

**Extended product/reciprocal bridge.** smallprod.py uses the same sieve to \(N_1\) and the same logarithm brackets. To bound \(\log\log p\) within a block, compute a bracket at the anchor n, then use \(v-v^2/2\le\log(1+v)\le v\) for \(v=(\log p-\log n)/\log n\), using the nonnegative lower ratio for the left expression and the upper ratio for the right one. Prefixes of \(\sum1/p\) and \(\log Q_{\rm raw}\) use outward integers at scale \(S\). For \(p\ge1000\) compute the reciprocal series through powers 4, with remainder at most \(1/[5 p^4(p-1)]\); for smaller p use directed ln. The constants use \(\gamma\) at \(n=10^5\), and a precise tail for \(M\) after \(N_0\). Specifically, for \(f(t)=1/(2t^2\log t)\), partial summation bounds the difference between \(\int_{(N_0,\infty)} f\,d\theta\) and its main term \(J=\int_{N_0}^\infty f(t)dt\) by \((10/L_0^3)[2N_0 f(N_0)+J]\) with \(L_0=\log N_0\). The main term is \((2N_0 L_0)^{-1}\int_0^\infty e^{-w}/(1+w/L_0)\,dw\); the geometric identities truncated at even degree 8 and odd degree 9 give upper and lower rational functions of \(L_0\), respectively. The remainder from all powers \(m\ge3\) is between 0 and \(1/[6N_0(N_0-1)]\) by summing \(1/[3(1-1/N_0)p^3]\) over integers above \(N_0\) and integrating \(t^{-3}\).

To pass an entire cell with an onset clipped to its left edge, use endpoint monotonicity of the **scaled** signed errors. With \(\delta=D_Q\) one has \(\delta'=-1/L\) on each cell in log coordinate. The run checks \(|\delta|<.1\) throughout each active cell using endpoint brackets. For Q the scaled signed error \(L^3(e^\delta-1)\) then decreases (derivative \(L^2(2e^\delta-3)<0\)), and for P \(L^3(e^{-\delta}-1)\) increases (derivative \(L^2(4e^{-\delta}-3)>0\)). Thus each sign of the product error is tested at the appropriate endpoint. Convert log magnitudes using \(1-e^{-d}\le d\), \(e^d-1\le d/(1-d)\), \(0\le d<1\). For the reciprocal sum \(E_1'=-1/L\), and \(E_1=D_Q+T_0<1/3\) by the same check and the bound on \(T_0\), hence \(L^3 E_1\) decreases. Outward log upper endpoints furnish exact integer powers and comparisons. The successful log maxima are strictly below each coefficient claimed above; mverify.py closes the analytic tail after \(e^{18}\) for them. This extended join was necessary to prove the earlier onsets at the *same* Dusart tolerances rather than just larger earlier bounds.

## Bottlenecks and attempts

Replacing ψ by the D01 bound inside either exact transform loses the log-square gain and has a much larger coefficient even after integration by parts; it cannot improve the matched ray because the *local* ψ term alone has a better B0 certificate. Treating the integrated error in absolute value works, but unnecessarily magnifies the main power term; signed spectral integration was needed to remove that factor. Taking only a uniform power profile is also uncompetitive at moderate x: the finite-RH square-root branch, the absolute constants from CH2, the optional θ cumulative transform, and exact sieve all matter. The late leading coefficient here is limited by cumulative right-edge zero density, not by D01. There is no new assertion of a stronger zero-free half-plane or of optimality of its power 7/8. Improving the residual early gap between finite and analytic constants is not controlled usefully by density or D01. We used an extended exact sieve and improved normalizer tails to close several better weighted joins. The final certificates cross the original .2 and .3 onsets by small explicit real amounts. Tested still earlier values \(2278381.5\) (the products), \(2278382\) (the reciprocal sum), and \(912559.995\) (weighted sum) did not pass the respective coefficient tests; an upper bound exceeding the target is not by itself a counterexample. No minimality claim is made for these onsets.

The corrected and enhanced analytic branches in **spectral_repair.md** further tighten this portfolio; take the minimum with all valid branches here. No numeric certificate in this file used an unshifted spectral θ interval.
