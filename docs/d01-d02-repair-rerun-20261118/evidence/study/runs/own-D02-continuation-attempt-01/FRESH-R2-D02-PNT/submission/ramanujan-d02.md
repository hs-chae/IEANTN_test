# Ramanujan gap: connected rays, high-order profiles, and earlier finite bounds

For real \(x>1\) use \(\pi(x)=\#\{p\le x\}\), \(L=\log x\), \(R(x)=ex\,\pi(x/e)/L-\pi(x)^2\), and \(F_R(L)=R(e^L)L^6/e^{2L}\). All gaps below are **strict**, and all displayed log-onsets are included. The assumptions are B0 plus D02 unless a result is marked B0 only.

## Endpoint and tail statements

The exact last real counterexample is still the B0 endpoint \(r=38358837682.217926365\ldots\) defined as the unique root in \((38358837682,38358837683)\) of the scalar equation in ramanujan-proof.md, with the same exact rational enclosure. In particular \(R(r)=0\), the strict positive real ray is \(x>r\), and its first integer is 38358837683. No earlier connected onset is possible. The strict linear margin just to the right of \(r\) is inherited. The real bridge uses the published Dudek–Platt integer computation and Lemma 3.4 (PDF pp. 8, 10), then monotonic interpolation, not the false literal real-left-end reading of Platt–Trudgian Theorem 2 (arXiv:1809.03134v2 PDF p. 3). No assertion of a new rerun to \(1.15\cdot10^{16}\).

Write \(P_d(L)=\sum_{j=0}^d A_{j+4}/L^j\), where
\[
 A_j=\sum_{k=0}^j k!\binom{j}{k}-\sum_{k=0}^j k!(j-k)!.
\]
The first five coefficients are \(1,14,145,1412,13985\). They are positive at every included order, as shown in repair.md. The whole-ray **D02** onsets for \(P_2,P_3,P_4\) are respectively \(185.5,210,235.5\). The finite certificates go through \(196,217,241\) respectively and join an analytic tail on those exact endpoints. Additionally \(F_R>1+14/L+100/L^2\) from 172, on a closed finite cover through 196 and the \(P_2\) ray thereafter. All inherited profiles remain applicable, including lower-order profiles at much earlier \(L\). The new powers do not change the limit \(F_R\to1\).

The strengthened matched B0 onsets for these three degrees are respectively 218, 250, 284, via covers through 227, 257, 290 and the corresponding analytic tails (the inherited onsets were 222, 255, 310). These are B0-only secondary improvements, included in the comparison rather than frozen out of it.

For larger degrees we obtain the following onsets. For comparison the second onset column uses the *same* proof with \(b=7/8\) instead of \(27/32\), including all the new B0 density improvements. It is not an independently constructed baseline; take the minimum with the inherited onsets wherever those are earlier.

| \(d\) | D02 | Matched B0 tail |
|---:|---:|---:|
|5|266|324|
|6|292|359|
|7|318|394|
|8|345|429|
|9|372|465|
|10|398|501|
|11|425|537|
|12|452|573|
|13|479|610|
|14|506|646|
|15|534|682|
|16|561|719|
|17|588|755|
|18|615|791|
|20|670|864|
|22|725|938|
|24|780|1011|
|28|889|1157|
|32|999|1304|
|40|1219|1597|
|50|1494|1964|
|60|1770|2334|
|80|2321|3070|

Thus at fixed margin \(P_{40}\), for example, the improvement is from 1597 (the inherited onset was 1612) to 1219; at the fixed compensated B0 onset 1597, use \(P_{50}\) in place of \(P_{40}\). At \(L=210\) or later the conditional \(P_3\) improves \(P_2\) pointwise, since \(1412/L^3>0\). This is not an optimal-onset claim.

There is also a more precise entire-ray profile not limited to any finite order. Set \(R_{\rm li}(x)=ex\,\mathrm{li}(x/e)/L-\mathrm{li}(x)^2\), with the **PV** logarithmic integral. For each \((B,C)\) in
\[
\begin{split}
 &(173,.815),(181,.776),(191,.737),(200,.71),(211,.677),\\
 &(251,.602),(301,.549),(421,.485),(601,.446),(1001,.412),\\
 &(2001,.388),(10001,.370),(1000001,.367)
\end{split}
\]
we have \(|R(x)-R_{\rm li}(x)|<C x^{59/32}/L^2\) for \(L\ge B\). The matched B0 profile has \(C=.041,\ B=201\), with exponent \(15/8\). Consequently \(R>R_{\rm li}-C x^{59/32}/L^2\) is an additional lower profile. At \(L=201\) the new .71 residual is smaller by a factor \((.041/.71)e^{201/32}>30\), continuing to improve relatively. Comparing bounds does not assert a lower bound on the true oscillation. Use the maximum of these and all the other proved lower profiles.

## Secondary improvements independent of D02

The following B0 results use no change in the zero cap:

* By exact segmented sieve, \(F_R(L)>.00000752\) on \([n+1,n+100001)\) in the \(x\) variable, \(n=38358837682\). Prime counts at \(n\) and \(m=14111427770\) are those of count.cpp in the inherited proof. The sieve to \(\lfloor\sqrt{n+100000}\rfloor\) and the two segmented sieves mark exactly composites, beginning at \(\max(p^2,p\lceil a/p\rceil)\) in a segment starting at \(a\). For every \(j=n+1,\ldots,n+100000\) enclose \(j/e\) tightly enough to certify its integer floor, update the two counts, and use the exact \(R(j)\). On \([j,j+1)\), \(R(x)\ge R(j)>0\), so \(R(j)(\log j)^6/(j+1)^2\) is a lower bound for \(F_R\) throughout the cell. No assertion is made at the excluded endpoint of this margin.
* Using only CH2 Lemma 9.2's **unweighted** \(\psi\) bound and the reported finite positive-sign bound \(\pi<\mathrm{li}\) in FiniteRH §3.3 (PDF p. 5), we obtain \(F_R>0,.1,.5\) respectively on \([27.9,30.9],[28.35,30.9],[29.5,30.9]\) in \(L\). The shifted argument is at most 29.9. These quantitative estimates do not need the next optional numerical leaf.
* At the trust of the **explicitly displayed additional finite \(\pi\) bound** reported in Platt–Trudgian arXiv:1809.03134v2, PDF p. 8, last formula in §4 (physical LF 790–801), use its \(1.95+3.9/L+19.5/L^2\) inequality through \(10^{19}\). This is a source-reported estimate, not a new inference from an outside paper or an independent replay. Platt–Trudgian §4 starts by defining its \(\mathrm{li}\) with lower limit 2 (PDF p. 7); allow \(2Le^{-L}\) for the normalized conversion to PV, since \(0<\mathrm{li}_{PV}(2)<2\) as checked in early02.py. This also covers a PV interpretation of the reported bound. The negative sign \(\pi<\mathrm{li}\) from FiniteRH §3.3 works for PV in either convention, by positivity of the same constant.

  At this stated original finite trust the following are strict bounds on **closed** intervals or rays; in the finite cases the target need not persist beyond the listed end:

  | Profile | \(L\)-domain |
  |---|---|
  | \(0\) | \([27.8,43.74]\), already in the strict connected sign ray |
  | \(.1\) | \([27.95,\infty)\) |
  | \(.5\) | \([28.75,\infty)\) |
  | \(.9\) | \([29.95,\infty)\) |
  | \(1\) | \([30.4,\infty)\) |
  | \(1.05\) | \([31,290]\) |
  | \(1.2\) | \([31.85,80]\) |
  | \(1.3\) | \([32.75,43.74]\) (also retain the inherited later interval) |
  | \(1+9/L\) | \([33,\infty)\) |
  | \(1.4\) | \([34.2,43.74]\) |
  | \(1+14/L\) | \([38,43.74]\) |
  | \(1+13/L+100/L^2\) | \([39,43.74]\) |

  Finite covers to 43.74 use early02.py. For .1, .5, .9 and 1 join to the respective inherited whole rays, which already start before 43.74. For \(1.05\) use the closed interval \([40.34,290]\) proved with the new integrated bounds; for \(1.2\) and \(1+9/L\) the reported bound can still improve the shifted error across 43.74, verified by a closed cover to 80 (join \(1+9/L\) to the inherited ray starting at 45). The sign branch with cutoff 43.74 uses the verified \(e^{43.74}<10^{19}\), not rounding the cutoff up. Finite R certification does not use the report outside its verified range in either argument.
* Without the optional quantitative Platt–Trudgian leaf, refinements still give the following real rays at B0 trust: \(.005,.1,.5,.9,1\) from \(36.534,36.732,37.762,39.37,39.972\) respectively; the constant \(1.05\) on \([40.34,290]\) and \(1.2\) on \([44.59,80]\); \(1+14/L\) from 47.13 and \(1+13/L+100/L^2\) from 48.15; and \(P_3\) on \([60,90]\). The finite connectors and prior rays are listed in verify02.py, e.g. \([47.13,100]\) overlaps 47.15 and \([48.15,101]\) overlaps 48.2. The sign analytic join moves to 36.525 without either the optional quantitative \(\pi\) leaf or D02. These secondary results improve on fixed margins and onsets before the new high-zero cap controls the main error.

## Shifted prime-count estimate and residual

Use \(A(L)\) for an upper bound on \(|Le^{-L}(\pi(e^L)-\mathrm{li}(e^L))|\). From \(\theta\), partial summation with the anchor \(a=8\) gives the identity in ramanujan-proof.md. It applies without upper restriction on \(L\), and the finite anchor error is at most \(e^4(8^2+8)/(8\pi)\) times \(Le^{-L}\). For the boundary, take any of the inherited bounds on \(|e^{-L}\theta(e^L)-1|\) or the new spectral \(\psi\) bound plus Dusart Cor. 4.5 corrections \(c_Ue^{-L/2}+1.78e^{-2L/3}\), \(c_U=1.000000147\). The CH2 Cor. 1.2 alternatives may use \(T=.55e^{L/2}\) and \(T=.60e^{L/2}\) in addition to the old ratios on \(34\le L\le58\); the same extreme guards \(10^7\le T\le H\), \(x>\max(T,10^9)\) hold. The finite guard is evaluated on the entire arithmetic cell.

For the integrated part apply Dusart (2.1), with the compact convergence justification in spectral-proof.md. After integrating by parts in \(v\) once, a group with real parts \(\le b\) and reciprocal-square mass \(J_0\) is bounded by
\[
 J_0\left(\frac{b}{b-1/4}\frac{e^{bL}}{L^2}
                      +\frac{e^{8b}}{64}\right)
\]
before multiplying by \(Le^{-L}\), for \(b>1/4\). The \(2/v^3\) term is at most \(1/4\) times the integral of \(e^{bv}/v^2\), whose log derivative is \(\ge b-1/4\). Use \(b=1/2,\ J_0=.12\) at low height and \(b=b_2\) or \(b_0,\ J_0=8\cdot10^{-12}\) above \(H\). The constant/trivial contribution costs \(1.84/8\) before normalization. Prime power removal under the integral is at most \(4c_U e^{L/2}/L^2+21.36e^{L/3}/L^2\) by the same derivative estimate. This is integ in applications02.py. It avoids the growing integral prefactor of a distant absolute prime-count anchor. Near the finite threshold also split at \(T=L-8\) (a log-coordinate, not a spectral height); for either zero/prime-power exponent \(B\) bound \(Le^{-L}\int e^{Bv}/v^2\,dv\) on the two pieces respectively by
\[
 \frac{L e^{BT-L}}{T^2(B-1/4)},\qquad
 \frac{e^{-(1-B)L}}{L(B-2/T)}.
\]
The \(2/v^3\) factor on the pieces costs at most \(1/4,2/T\) respectively. Keep the same boundary terms. Denominators are positive on the stated \(L\)-domains. For the CH2-only early lower bound specifically use the negative boundary error at most \(.751e^{-L/2}\) from unweighted Lemma 9.2 and then remove prime powers.

Use any independent upper approximation \(U_L\ge Le^{-L}\mathrm{li}(e^L)\). For \(L\ge34\) the normalized absolute residual from the exact log-integral gap is bounded by
\[
 L^4\left[\frac{L}{L-1}A(L-1)+A(L)(2U_L+A(L))\right].
\]
This follows by a difference of squares and the linear shifted term with its stated factor. For a lower profile only, the unshifted \(A(L)\) may be replaced by 0 where the one-sided sign \(\pi\le \mathrm{li}\) is known. The D02 gain is in both \(A(L-1)\) and \(A(L)\), each using its own source guards and the cap-improved integrated tail; never substitute the new \(\psi\) assumption at an out-of-domain shifted argument. For the absolute-residual rows choose a spectral mode with nonincreasing scaled \(e^{g v}\Phi(v)\) from \(v=B-1\) as in the Mertens check. The integrated and power-removal corrections likewise decrease after scaling, by their rates and polynomial factors (in particular the sole \(ve^{-v}\) factor is already decreasing after scaling). With \(u=e^{g(B-1)}A(B-1)\) evaluated using the **same** majorant for all \(v\ge B-1\), and the inherited upper log-integral polynomial \(U_L\) nonincreasing, the bracket is at most
\[
 e^{-gL} u\left(\frac{B}{B-1} e^g+2U_B+u e^{-gB}\right).
\]
Divide the full scaled inequality by \(L^6/x^2\); \(2-g=59/32\) in D02. The error and the model may both be further improved pointwise by the legal intersections of the estimates; the upper residual is not necessary for a signed profile at small \(L\).

## Polynomial and finite certificates

Use the \(N=22\) log-integral barriers and exact coefficient subtraction in ramanujan-proof.md from \(L\ge34\); for \(27\le L\le43.74\) use \(N=18\), anchored at 26 with upper coefficient \(5N!\). The exponential-integral series check proves the barriers at 26, and their derivative test is \(5(1-(N+1)/26)>1\). This covers the shifted argument as well. Squaring the upper positive polynomial and positively truncating the shifted lower binomial series through order \(2N\) gives the same coefficient rule as before. Coverage subtracts the desired profile coefficients first, then bounds the remaining polynomial and the error on entire closed arithmetic cells, with additional splits at 30.9 in the early range and at the sign guard 43.74. Domains of individual source options are tested at both cell ends.

On the arbitrary-degree tail use \(N=d+6\), \(a=\max(32,2(N+1))\), and \(X=B-1\). The barriers from repair.md are \(S_N\) and \(S_N+3N!/L^{N+1}\) for \(e^{-L}\mathrm{li}(e^L)\); they follow from the exact integrating-factor identity and the guard \(2e^{a-X}X^{N+1}<N!\), which persists from \(X\). At onset check it with \(e>2718/1000\). Subtract \(P_d\) from the truncated shifted model minus the upper square. The scaled main coefficient at order \(L^{-d-1}\) is \(A_{d+5}>0\); drop positive later terms and evaluate negative later terms at \(B\) after multiplying by \(L^{d+1}\). The scaled error requires \(L^{d+5} A(L-1)\) and \(L^{d+5} A(L)\). To bound it, use the positive spectral modes with the displayed integrated correction and replace \(1/v\) in the correction by \(1/(B-1)\). For a mode \(c(v-a_0)^k e^{-rv}\), \(v=L\) or \(L-1\), check \(r\ge(d+5)/X+k/(X-a_0)\) at \(X\) if \(k>0,\ X>a_0\), and \(r\ge(d+5)/X\) for \(k=0\). Then both scaled modes are nonincreasing, by the log derivatives (the shifted \(L^{d+5}\) factor grows no faster than \(v^{d+5}\) in logarithmic derivative). The factor \(L/(L-1)\), \(U_L\) and the unscaled error also decrease. The strict onset test consequently proves the entire tail. Evaluate scaled exponentials directly as \(\exp((d+5)\log B-rv)\); for sufficiently large arbitrary-degree searches an exact rational upper \((1000/2718)^{\lfloor rv\rfloor}\) avoids any reliance on fixed-point underflow.

This supplies a terminating doubling search in every degree: for fixed \(d\), the barrier and derivative guards eventually hold, the main scaled estimate tends to \(A_{d+5}>0\), and the exponential terms (including the rational upper bounds) times fixed polynomials tend to 0. No optimality or monotonicity of the sufficient-test search in its integer parameter is assumed; all printed endpoints are directly checked. This proves true all-order rays, not a fit to numerical data.

## Limits of the improvements

At \(L\) near 170–190 the independent CH2 floor prevents using the new cap to fill the entire earlier high-order gap. A finite \(P_3\) window \([60,90]\) is useful but cannot just be joined to a higher-order spectral ray across an unchecked transition. In particular the tried \(P_2\) onset 185, \(P_3\) onset 209, and \(P_4\) onset 235 fail the stated sufficient method. The attempted bridge for \(1+10/L\) right of 43.74 failed (the shift exits the sharp finite reported domain); \(1+9/L\) succeeds, and stronger early profiles remain finite. Around the actual root, continuity and \(R(r)=0\) rule out a fixed positive margin immediately above \(r\); the sign ray is already exact. Away from the pointwise estimates the old long finite computation is primarily sign information. No attempt treats it as a certified uniform quantitative margin; the new small segment scans one real region independently. These limitations are not counterexamples to the improved target inequalities.
