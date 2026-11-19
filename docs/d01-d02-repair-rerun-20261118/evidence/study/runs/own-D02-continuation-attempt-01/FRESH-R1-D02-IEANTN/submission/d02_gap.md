# Ramanujan: real onset, matched margins, and higher-order profiles

Let \(L=\log x\), \(R(x)=ex\pi(x/e)/L-\pi(x)^2\), \(Y(L)=L^6e^{-2L}R(e^L)\). Use B0, and D02 only where marked. Logs and all closed ranges in this file are **real**, and displayed strict lower margins are strict at both endpoints. The output envelope is the maximum of all valid branches, including the entire D01 floor.

**Exact connected sign ray (inherited).** Let \(N=38358837682\) and \(z\) be the root of \(ez(632207037)/\log z=(1644673232)^2\) on \((N,N+1)\), with
\(38358837682.21792636514419<z<38358837682.21792636514511\).
Then \(R(z)=0,\ R(x)>0\) for all real \(x>z\), and \(R<0\) on \([N,z)\). On \([z,N+1]\), \(R(x)\ge67000000(x-z)\); least strict integer onset \(N+1\). The two exact counts, segmented sieve to \(10^{11}\), and Dudek–Platt Lemma 3.4 (PDF p.10, LF698–715) through \(1.15\cdot10^{16}\) join the analytic bounds as in ramanujan.md. No new assumption improves the exact sign onset. The literal real reading \(N<x\) of Platt–Trudgian PNT Theorem 2 (p.3, LF205–212) is false near \(N\); retain its integer restriction and its real ray \(L\ge3915\), as well as Dudek–Platt Theorem 1.2 at \(L\ge9658\). No full RH is invoked.

## Quantitative real domains

B0-only new margins (keep the other earlier tradeoffs of gap_repair.md):

| Closed log range | Strict \(Y>\) |
|:--|--:|
| [36.528,∞) | .001 |
| [36.531,∞) | .002 |
| [36.737,∞) | .1 |
| [36.890,∞) | .168 |
| [36.98,37.5] | .207 |
| [39.912,∞) | .4 |
| [40,∞) | .431 |
| [42.471,∞) | 1 |
| [45,76] | 1.212 |
| [46,68] | 1.241 |
| [47,63] | 1.264 |
| [48,55] | 1.308 |
| [49,52] | 1.321 |
| [59,73] | 1.220 |
| [75,100] | 1.152 |

Closed joins are recorded in d02_checks.log. In particular the .168 profile crosses \([39.326,39.912]\) without the PV-li premise; the .4 interval joins \([42.471,60]\) at margin 1, which overlaps the inherited unit-margin ray. At fixed onset 40, .431 replaces .425; at fixed margin .4 the log-onset improves from 39.94 to 39.912; at onset 36.98 the ray guarantee is .168 instead of .164. The floor proves \(Y\to1\), so \(q>1\) cannot hold on an eventual ray.

**D02 comparisons (bounded intervals).** At fixed \([100,175]\), B0 certifies \(Y>1.0820\), and B0+D02 certifies \(Y>1.0838\). At fixed left endpoint 100 and margin 1.0837, the respective sufficient right endpoints are 172.1 and 175.3. Also \(Y>1.0777\) on \([175,190]\) under D02. These compare sufficient profiles, not extrema. D02 helps when the reduced spectral local bound in (A) begins winning over the CH2 floor near 168; the proof does not use its raw bound below 200.

## Factorial profiles

Let
\[
 C_j=j!\sum_{i=0}^j1/i!-\sum_{i=0}^j i!(j-i)!,\qquad
 P_n(L)=\sum_{j=4}^n C_jL^{4-j}.
\]
The first terms are \(1+14/L+145/L^2+1412/L^3+13985/L^4\). Below are strict closed-ray log-onsets. The two columns are within-method ablations, not blind baseline experiments; both keep all legal original premises. For \(n=4,5\) the table gives the spectral-tail joins, not the best connected onsets. In fact \(Y>P_5\) on \(L\ge47.02\) over B0: join the closed cells on \([47.02,58],[58,100],[100,190]\) to the B0 tail. Separate B0 finite intervals: \(Y>P_6\) on \([52.1,125]\), \(Y>P_7\) on \([57.5,91]\), and \(Y>P_8\) on \([64,66]\). There is no certified \(P_6\) coverage of the full gap between 125 and 186.54; unit and \(P_5\) profiles are connected there.

| Profile | B0 log-onset | B0+D02 log-onset |
|:--|--:|--:|
| \(P_4\) | 160.19 | 142.34 |
| \(P_5\) | 188.83 | 163.33 |
| \(P_5+0.5\cdot145/L^2\) | 195.43 | 168.37 |
| \(P_5+0.9\cdot145/L^2\) | 208.68 | 178.34 |
| \(P_5+0.99\cdot145/L^2\) | 218.34 | 185.19 |
| \(P_6\) | 220.37 | 186.54 |
| \(P_7\) | 253.57 | 211.07 |
| \(P_8\) | 287.78 | 236.44 |
| \(P_{10}\) | 357.97 | 288.63 |
| \(P_{12}\) | 429.41 | 341.9 |
| \(P_{14}\) | 501.51 | 395.74 |
| \(P_{16}\) | 573.97 | 449.92 |
| \(P_{17}\) | 610.3 | 477.09 |
| \(P_{20}\) | 719.55 | 558.84 |
| \(P_{24}\) | 865.62 | 668.21 |
| \(P_{32}\) | 1158.51 | 887.63 |
| \(P_{48}\) | 1745.69 | 1327.75 |
| \(P_{64}\) | 2333.71 | 1768.62 |
| \(P_{100}\) | 3658.04 | 2761.7 |

Thus, for example, .99 of the sixth term in addition to \(P_5\) is supported from 185.19 instead of 218.34 by the matched tail tests. At log-onset 186 the D02 ray supports that premium while the B0 connected certificate there gives \(P_5\). This is not an impossibility claim about stronger B0 proofs. Without FKS Cor.2.9 the D02 density-free branch still proves \(P_{12},P_{17},P_{32},P_{64},P_{100}\) from \(420,561,982,1874,2875\), respectively.

## Proof of the finite profiles and joins

Let \({\rm Li}_2(x)=\int_2^x dy/\log y,\ S_m(t)=\sum_{j=0}^m j!/t^j,\ F_m(x)=xS_m(L)/L\). End-inclusive partial summation gives
\[
 \frac{L}{x}(\pi(x)-{\rm Li}_2(x))=u_\theta(L)+Le^{-L}
 \left[2/\log2+\int_{\log2}^L e^t u_\theta(t)t^{-2}dt\right],
\quad u_\theta=e^{-t}\theta(e^t)-1.
\]
Retain the old EC, EF, EF2, ED errors of ramanujan.md. For a sharper integral, split at 7, write \(u_\theta=u-q,\ q=e^{-t}(\psi-\theta)(e^t)\), and put \(w_0(t)=e^t/t^2\). The \(\psi\) part of the integral from 7 to \(L\) equals
\[
 w_0(7)B_1(7)-w_0(L)B_1(L)+w_0'(7)B_2(7)-w_0'(L)B_2(L)
       +\int_7^L w_0''(t)B_2(t)dt .
\]
For \(t\ge7,\ 0<w_0',w_0''\le w_0\). Apply (B) of d02_analysis.md and its second-primitive estimate. For each exponential \(e^{-dt}\) of the spectral bound integrate \(w_0(t)e^{-dt}\) by the log-derivative lower bound \(1-d-2/7\). For the residual of \(B_2\) use \(\int_7^\infty 2t^{-2}\,dt=2/7\). The boundary costs at 7 together with this last cost are \(<2\), checked. The elementary prefix including \(2/\log2\) is at most \(3e^7\) by Dusart Thm 4.2's non-strict \(|u_\theta|\le1\), as in ramanujan.md. Thus the normalized bound for prefix plus \(\psi\) integral is
\[
 W_\pi(t)=(3e^7+2)t e^{-t}
 +\frac{.0462[1+(1+14/3)/14]e^{-t/2}
 +4\cdot10^{-12}[1+(1+(1-r-2/7)^{-1})/14]e^{-rt}
 +4e^{-t}}t,\quad r=1-b.
\]
The upper and lower costs of \(q\) including its local contribution are
\[
 V_\pi=1.000000147e^{-t/2}(1+14/(3t))+1.78e^{-2t/3}(1+21/t),\quad
 U_\pi=.9999e^{-t/2}[1+(2/t)(1-e^{(7-t)/2})].
\]
Use Dusart Cor.4.5 (p.13 LF1129–1133) and Prop.4.3 (p.12 LF1049–1056); for the upper integral the log-derivative minima are \(3/14,\ 1/21\), respectively, and for the lower use \(s^{-2}\ge t^{-2}\) within the integral and integrate the square-root term. Thus the error above \({\rm Li}_2\) is bounded by the upper \(u\) estimate plus \(W_\pi-U_\pi\); below \({\rm Li}_2\) use the negative lower \(u\) estimate plus \(W_\pi+V_\pi\). Take the better of competing applicable bounds at each argument separately.

For \([34,58]\), compete with CH2 (9.4) (Cor.9.3, p.36, LF5336–5363) and Cor.1.2 (p.3, LF193–218) at \(T=2\pi^2 e^{t/2}/(t-h)\), \(h=0,3,4,5\), checking the \(T,x\) restrictions on the entire evaluation interval. With \(v=\pi_{\rm circular}/T\), \(1\le v\coth v\le1+v^2/2\) by monotonicity and the derivative in CH2 Lemma 4.2 (pp.13–14, LF1666–1668 and proof of Prop.9.1). This gives a signed interval about \(u=0\). Compete with CH2 Cor.1.3 and (A) in their own validity domains. The code omits (A) in the finite cells before argument 160 for convenience; it is valid already at 100. The inherited one-sided \(\pi<\mathrm{li}\) computation is used only through \(1.2\cdot10^{17}\) (Dudek–Platt proof of Lemma 3.2, p.8, LF561–562), with \(\mathrm{li}-{\rm Li}_2<3\) and the inherited exact Li anchor at 30: \(12<{\rm Li}_2(e^{30})-F_{18}(e^{30})<13\). For the upper error from \(S_{18}\) add \(13t e^{-t}+3\cdot19!/t^{19}\); positivity of the Li remainder needs no addition to the lower error. This is all as in ramanujan.md.

For nonnegative upper and lower normalized errors \(U,V\) from \(S_m\), respectively, the gap bound is
\[
 Y\ge G_m-L^4\left[\frac L{L-1}V(L-1)+2S_m(L)U(L)+U(L)^2\right],\quad
 G_m=L^4\left[\frac L{L-1}S_m(L-1)-S_m(L)^2\right]. \tag{G}
\]
The shifted loss and the upper error in the squared term are separate estimates. verify.py checks the coefficient absorption for \(G_{18}\) on \(L\ge36\), proving decrease and \(G_{18}-P_n\ge\sum_{j=n+1}^{26}C_j L^{4-j}\) for \(4\le n\le17\). Thus on a closed cell use the right endpoint for the main term or reserve and enclose the loss over the entire cell. Bisect failed cells at shared interior endpoints. A theorem requires every closed cell to pass, not just selected points. The earliest PV cell joins the inherited finite sign bridge since \(e^{36.528}<e^{36.98}<1.15\cdot10^{16}\).

## Analytic factorial tails

For \(m\ge n+2,\ b_m=2(m+2)\), the absolute normalized Li truncation loss is at most \(3t e^{b_m-t}+2(m+1)!/t^{m+1}\) on \(t\ge b_m\). At the anchor \({\rm Li}_2(e^{b_m})\le e^{b_m}/\log2,\ F_m(e^{b_m})\le2e^{b_m}/b_m\); afterward the derivative of the difference is \((m+1)!/\log^{m+2}x\) and the log-coordinate integrand's log derivative is at least \(1/2\). Write \(E_m(t)\) for this loss plus \(D_b+W_\pi+V_\pi\), or substitute \(D_b^{\rm df}\) for \(D_b\). The coefficients of \(G_m\) as \(\sum_j C_j^{(m)}L^{4-j}\) are
\[
 C_j^{(m)}=\sum_{i=0}^{\min(j,m)}i!\binom ji
             -\sum_{\max(0,j-m)\le i\le\min(j,m)}i!(j-i)! .
\]
This exact convergent expansion for \(L>1\) follows by expanding powers of \(1/(1-1/L)\). Terms below 4 vanish. Through \(m\) the other coefficients are the positive \(C_j\): after dividing by \(j!\), the first sum is \(>8/3\), and the second at most \(2+2/j+2(j-3)/(j(j-1))\le8/3\) (use the binomial coefficient bounds for the interior terms). Only \(m<j\le2m\) can have negative terms. At the onset \(a\) check their total negative magnitude after scaling by \(L^{m-4}\) is \(<C_m\), hence later by decrease. For \(0\le\eta<1\) the reserve of \(G_m-P_n-\eta C_{n+1}L^{3-n}\), scaled by \(L^{m-5}\), is at least the nondecreasing polynomial
\[
 (1-\eta)C_{n+1}L^{m-n-2}+\sum_{j=n+2}^{m-1} C_j L^{m-1-j}.
\]
Compare it with the scaled loss \(L^{m-1}[L E_m(L-1)/(L-1)+2S_m(L)E_m(L)+E_m(L)^2]\). Each exponential monomial \(t^p e^{-dt}\), after scaling and either shift, decreases if \((m-1+\max(p,0))/(a-1)<d\); for the positive spectral mixture use \(d\ge1-b,\ p=0\). Inverse-power Li remainders decrease even after the scaling, and remaining factors are positive decreasing. The checks are made at the closed left endpoints and prove the whole rays. For arbitrary \(n,\eta\), taking \(m=n+4\) and increasing the onset must eventually pass: the scaled loss tends to zero, the reserve does not, and the negative-tail absorption eventually holds. optimize_d02.py chooses among selected \(m,k\) and hundredth onsets; optimized.log contains each certified tuple. No calculus or numerical claim of global optimality is needed.

**Raw D02 alternative.** Do not keep an \(e^{-L/8}\) spectral primitive in a raw high-order estimate. Keep instead the original \(E_C\) integral prefix through 200, of size \(<4\cdot10^{-17}e^{200}\) by the same integral computation and the directed check. For \(t\ge200\) integrate absolutely from 200 using direct D02 and \(q\le3e^{-t/2}\). The pure direct error \(E_m^{\rm raw}(t)\) is at most
\[
 4\cdot10^{-17}t e^{200-t}
 +\frac{t^2}{64}e^{-r_2t}\left(1+\frac1{(1-r_2)t}\right)
 +3e^{-t/2}\left(1+\frac1{.48t}\right)+3t e^{b_m-t}+2(m+1)!/t^{m+1}.
\]
The log-derivative lower bounds in the integrals are \(1-r_2\) and .48. The same tail proof, now with \(a-1\ge200\), gives \(P_6,P_{12},P_{17},P_{32},P_{64},P_{100}\) from \(253,421,562,983,1875,2876\), respectively. This explains how high order benefits even without density; it does not meet the stronger earlier spectral profiles.

## Exact Li profile and an original-only comparison at the new exponential rate

Let \(B(L)=Le^{-L}{\rm Li}_2(e^L),\, A_\pi(L)=Le^{-L}\pi(e^L)\), and \(Y_{\rm Li}=L^4[\frac{L}{L-1}B(L-1)-B(L)^2]\). On \(L\ge36\), use (G) with \(B\) in place of \(S_m\) and with the signed errors **against Li** as above, without truncation. This is an additional computable pointwise lower branch. It can also intersect the exact-\({\rm Li}_2\) errors with the literal \(\pi-\mathrm{li}\) intervals in Platt–Trudgian Finite RH Cor.1 (p.4, LF138–150) and Platt–Trudgian PNT Cor.2 (p.3, LF122–135), on their original domains, by adding the exact shift \(\mathrm{li}(2)\) to both endpoints. They are not needed for the new numerical check. For a whole-ray symmetric bound put \(E_\pi=D_b+W_\pi+V_\pi,\ C_a=e^{z(a-1)}E_\pi(a-1)\), \(a\ge101,\ 0\le z\le1-b\). Under the monomial log-derivative tests at \(a-1\),
\[
 |Y-Y_{\rm Li}|<3.24\, C_a L^4 e^{-zL}\qquad(L\ge a).
\]
Indeed \(B<1.02,\ A_\pi+B<2.05\) on \(L\ge100\) by the \(m=2\) truncation, the old-cap error at 100 and decrease. In the exact difference of the two gaps, the shifted factor costs at most \(1.01 e^{5/32}\), and the squared difference costs at most 2.05, total \(<3.24\). For example, at the matched log-onset 201 the coefficient of \(L^4e^{-L/8}\) improves from .060 to .00161, and coefficient .831 of \(L^4e^{-5L/32}\) holds there under D02.

Any eventual **one-sided** estimate \(Y\ge Y_{\rm Li}-C L^j e^{-rL}\) with \(r\in[1/8,5/32]\) implies the zeta cap \(1-r\). To prove, put \(d=A_\pi-B\). Rearrange the exact identity:
\[
 d(L)\le \frac L{(L-1)(A_\pi+B)}d(L-1)+O(L^{j-4}e^{-rL}).
\]
The coefficient is eventually at most \(3/4<e^{-r}\) since \(A_\pi+B\to2\). Iterating on the positive part of \(d\), with a bounded unit initial interval and a geometric series, gives \(\pi(x)-{\rm Li}_2(x)\le C'x^{1-r}(\log x)^k\) eventually for some nonnegative integer \(k\). For \(P=\pi-{\rm Li}_2\), \(F(s)=\int_2^\infty P(x)x^{-s-1}dx\) initially on \(\Re s>1\) satisfies
\[
 (sF(s))'=\zeta'(s)/\zeta(s)+\sum_{p,m\ge2}\log p\,p^{-ms}+2^{1-s}/(s-1).
\]
This follows by partial summation and differentiation; the prime-power sum is holomorphic on \(\Re s>1/2\). The real pole at 1 cancels, and there are no real zeta zeros on \((1/2,1)\). Thus \(F\) continues locally along the real interval \((1/2,\infty)\). The Mellin transform of the nonnegative function \(C'x^{1-r}(\log x)^k-P(x)\) started at a large cutoff also continues locally along real \(s>1-r\). If its abscissa of convergence were there, analyticity in a neighborhood of that abscissa would give a Taylor expansion about a convergent real point \(c\) close to the abscissa reaching a real \(c-h\) strictly left of it. Its Taylor terms at \(c-h\) are nonnegative integrals; monotone convergence of the exponential series gives actual Mellin convergence at \(c-h\), contradiction. Hence \(F\) is holomorphic on \(\Re s>1-r\) by integral convergence and local gaps. Its derivative identity excludes zeros strictly to the right. This compares the new exponential precision even against an unknown B0 proof: a matching B0 rate would itself prove the stronger zeta exclusion. No strict logical separation of premise closures is asserted.

## Further attempts and limits

Optimizing the lawful CH2 height and taking the second primitive improved finite margins over B0, but local errors still control the finite-height plateau and the gap between the early and late \(P_6\) domains. Extending the one-sided PV-li inequality beyond its certified original domain would be invalid. The stronger targets 1.212 on \([45,77]\) and 1.220 on \([59,75]\) hit failed directed cells near their right edges and were shortened, not treated as counterexamples about the primes. The raw D02 loss and the variant keeping the B0 primitive were compared; the old \(e^{-L/8}\) integrated term actually spoiled some very high-order raw tests, motivating the direct-prefix repair. Further increases of factorial truncation do not remove the local spectral loss. These are proved sufficient frontiers, not global optimality claims.
