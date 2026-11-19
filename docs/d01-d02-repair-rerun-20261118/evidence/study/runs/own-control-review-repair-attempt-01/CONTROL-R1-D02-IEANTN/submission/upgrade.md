# Repair-stage improvements: both application families

Here \(L=\log x\); B0 and B1, \(F_j,R,W,S,\Delta\), and the raw products have the meanings in common.md, ramanujan.md and mertens.md. Onsets below are closed in \(L\), all listed improvements use strict inequalities, and **all** ranges are real. All valid earlier branches remain in the pointwise portfolios. B0 is a within-method reconstruction from the seven permitted originals, not an independent blind run. Nothing here assumes full RH. The explicit statements depending on FKS Corollary 2.9 use it at stated original-paper trust; the density-free results below are separate.

## 1. Ramanujan: earlier connected B0 margin and new late B1 improvements

At B0 trust we prove:
* \(R>(x^2/L^6)F_0\) for every \(L\ge30.75\). This improves the connected B0 onset 42.8 and does **not** use Table 8.
* \(R>(x^2/L^6)F_1\) on \([34.4,43.74]\) as a new separate window; retain the whole ray \(L\ge47.5\). We do not claim a join for \(F_1\).
* \(R>(x^2/L^6)F_2\) on \([38.52,43.74]\); retain \([53,120]\) and the applicable late rays.

The largest real failure of positivity remains \(r\) in ramanujan.md, at the stated inherited integer-computation trust. These B0 improvements give quantitative margins well below the original analytic positivity threshold, not a new positivity endpoint or a D02 gain.

The following matched onsets give \(R>(x^2/L^6)F_j\) on the corresponding entire rays. They use the weighted density result proved in §3, not literal use of the D02 majorant before \(e^{200}\).

| \(j\) | B0 | B1 |
|---:|---:|---:|
| 2 | 221.12 | 187.18 |
| 3 | 254.28 | 211.69 |
| 4 | 288.48 | 237.04 |
| 5 | 323.34 | 262.94 |
| 6 | 358.65 | 289.22 |
| 7 | 394.26 | 315.75 |
| 8 | 430.08 | 342.48 |
| 9 | 466.07 | 369.34 |
| 10 | 502.17 | 396.31 |
| 11 | 538.37 | 423.37 |
| 12 | 574.64 | 450.49 |
| 13 | 610.97 | 477.66 |
| 14 | 647.35 | 504.88 |
| 15 | 683.77 | 532.13 |
| 16 | 720.22 | 559.42 |
| 17 | 756.70 | 586.73 |
| 18 | 793.21 | 614.07 |
| 19 | 829.73 | 641.42 |
| 20 | 866.28 | 668.79 |
| 21 | 902.85 | 696.18 |
| 22 | 939.43 | 723.58 |
| 23 | 976.02 | 751.00 |
| 24 | 1012.63 | 778.43 |
| 25 | 1049.25 | 805.86 |
| 26 | 1085.88 | 833.31 |
| 27 | 1122.52 | 860.76 |
| 28 | 1159.17 | 888.23 |
| 29 | 1195.82 | 915.70 |
| 30 | 1232.48 | 943.17 |
| 31 | 1269.16 | 970.66 |
| 32 | 1305.83 | 998.15 |
| 33 | 1342.52 | 1025.64 |
| 34 | 1379.20 | 1053.14 |
| 35 | 1415.90 | 1080.64 |
| 36 | 1452.60 | 1108.15 |
| 37 | 1489.30 | 1135.66 |
| 38 | 1526.01 | 1163.18 |
| 39 | 1562.72 | 1190.70 |
| 40 | 1599.44 | 1218.22 |
| 41 | 1636.16 | 1245.76 |
| 42 | 1673.04 | 1273.51 |
| 43 | 1717.38 | 1310.73 |

For example, at the common onset \(L=800\) the displayed B0 envelope gives \(F_{18}\) and B1 gives \(F_{24}\); at \(L=1000\) these are \(F_{23}\) and \(F_{32}\). Each additional included coefficient is positive (verified by its exact formula). These are certified margin comparisons, not exclusions of better B0 proofs. For fixed \(F_{43}\) the sufficient onset drops from 1717.38 to 1310.73. The whole-domain envelope retains early sign and all finite windows even when the late asymptotic profiles do not yet apply.

**Higher density-free fallbacks.** The same \(F_j\) conclusions hold on these closed rays without using the FKS density statements, using (3) of common.md in B0, or the **literal** D02 bound plus prime-power cost in B1. Retain earlier density-free \(j=1,2,4,8\) comparisons too.

| \(j\) | B0 | B1 |
|---:|---:|---:|
| 16 | 869.84 | 646.17 |
| 24 | 1168.86 | 870.72 |
| 32 | 1467.03 | 1094.58 |
| 43 | 1882.82 | 1410.23 |

In addition, in the named Li-proxy construction (compare ramanujan.md), the density-free D02 transfer beats the reconstructed B0 allowances at **both** arguments on \(L\ge436\). At \(v=435\), \(v\,P_{\rm D02}(v)<.99\min(1.04\cdot10^{-12},.0039e^{-v/8})\) for the transfer \(P_{\rm D02}\) with anchor 200. Multiplication by \(v\) or \(ve^{v/8}\) makes each term in that transfer decreasing there: the polynomial degree is at most 2 and \(2/v<5/32-1/8\). Then use \(v=L,L-1\) and the B0 allowance floor in §4. This comparison concerns proxy allowances, not actual fluctuations or the supremum over other profile constructions.

### Proof of the early branches

Use the Büthe absolute π bound quoted in PT PNT arXiv:1809.03134v2 PDF p. 8, extraction LF 695–705, now at **full** strength \(\big(1.95+3.9/v+19.5/v^2\big)e^{-v/2}/v+2e^{-v}\) for the normalized error on the used range. Also use PT FiniteRH PDF p. 5, extraction LF 182–185, reporting Büthe's signed upper bound for \(2\le x\le10^{19}\) at original trust. The upper normalized π allowance there is at most \(2e^{-v}\) even allowing a constant normalization difference. Both allowances are valid for the used arguments through \(v=43.74\) (\(e^{43.74}<10^{19}\)). The bound \(2\) on the normalization difference follows from the same \(\operatorname{Ei}\) series as in ramanujan.md at \(\log 2\) with \(.57<\gamma<.59\); its tail after degree 180 is less than twice the first omitted term. Alternatively, the signed inequality is unchanged if its original convention starts at 2 and the PV convention has the larger value. After the cutoffs, use only the corrected B0 providers in ramanujan.md.

For cells near the early onset keep the same degree-24 factorial sum \(P\) but use the barrier at anchor 28 with \(K=25!/(1-26/28)\) (instead of 31). The sub-/supersolution proof is identical; the Li series inequalities at 28 and \(28P^+(28)<1.04\) are tested. Hence \(f(L)\le1.04/L\) and \(LU(L)<.01\), from the signed bound until its cutoff, then using the CH2 branch available from 37 onwards to cap \(U\) as in ramanujan.md. Use \(2.09\) instead of \(2.07\) in the loss bound. The polynomial coefficient changes are the exact cross and square terms of \((P+K/v^{26})^2\); expansion cuts at degree 26 as before. All used \(L-1\) are at least 28, all selected CH2 arguments lie to the right of their anchors, and the finite cells split at both the unshifted and shifted cutoffs of each applicable provider. On a cell the numerator allowances are bounded from their left endpoints and powers contributing to the loss are bounded from the right. The sign of each term determines which endpoint to use in the lower polynomial. The F0 cells from \(43.74\) through \(47.5\) succeed even with the signed branch removed immediately to the right of the cutoff, overlapping the source-corrected \(L\ge42.8\) B0 F0 proof. The same check for F1 fails on the first cell past 43.74: that is a failure of the bound after loss of signed π information, not a counterexample. The first cell for \(F_2\) at 38.50 also did not certify; 38.52 does.

### Proof of the high-order profiles

Use (6) of ramanujan.md with anchor 61 and the new positive θ majorant in §3; with no density use anchor 61 and (3) or anchor 200 and exactly the D02 coefficient and \(\theta-\psi\) cap. The extension to a term \(v^1e^{-dv}\) in (6) uses the same logarithmic derivative bound \(1-d-2/a\). The transfer is evaluated in scaled form in upgrade.py to avoid multiplying large powers by loose absolute enclosures of tiny exponentials.

For the main late \(j=2,\ldots,16\) table keep the degree-24 Li barrier at 31. For \(j=17,\ldots,43\) and the supplementary high-order fallbacks use \(m=48,\ a=61\) and
\[
 P_m(v)=\sum_{k=0}^m k!/v^{k+1},\qquad P_m^+(v)=P_m(v)+K_m/v^{m+2},\qquad
 K_m=\frac{9}{8}\frac{(m+1)!}{1-(m+2)/61}.
\]
Indeed \(P_m'+P_m=1/v-(m+1)!/v^{m+2}\), and the added term gives a supersolution on \(v\ge61\). At 61 the series through degree 260 with at most twice its first omitted term suffices to verify \(P_m<f<P_m^+\) (successive tail ratios are at most \(61/262<1/2\)); the uninflated \(K_m\) failed the upper anchor test and is not used. The same factorial polynomial computation now retains exponents through \(m+2=50\) in \(P_m(L-1)/L\), dropping only positive terms. In particular the lower bound on \(L^{j+1}\) times the normalized proxy excess above \(F_j\) is
\[
 c_{j+7}+\sum_{n>j+7}\min(D_n,0)\,a_0^{\,j+7-n}\quad(L\ge a_0),
\]
where \(a_0\) is the tested onset and \(D_n\) are the exact polynomial coefficients after subtracting \((P_m^+)^2\). No \(K_m\) term enters \(D_n\) for \(n\le m+2\). For the gap loss, the global CH2 cap still justifies the \(2.07\) linearization (or intersect with it first). The \((j+6)/a_0+1/(a_0-1)<1/8\) test ensures that the normalized loss terms decrease for the **entire** ray; their rates are at least \(1/8\), with at most one positive power at \(L-1\) or \(L\) outside \(L^{j+6}\). Thus all finite rational certificates at the onsets prove full tails. Floating-point suggestions in suggest() never certify a threshold; each accepted rational threshold passes the outward-interval test with exact slack independently of the suggestion.

## 2. Mertens products and prime sums: strengthened rate tradeoffs

In the following table each row bounds \(|W|<C x^{-d}\) and all three other errors \(|S|,|e^{\Delta}-1|,|e^{-\Delta}-1|<C x^{-d}/L\) on the entire closed ray. The last factors remain \(1/L\); the new assumption increases \(d\), not the power of this factor.

| Onset \(L\) | B0 \(d=1/8\) | B1 \(d=5/32\) |
|---:|---:|---:|
|160|.02232|.3148|
|250|.01594|.2230|
|400|.01342|.1874|

All six coefficients improve those of the retained table in mertens.md. Each B1/B0 ratio at matched onset is less than one and decreases as \(e^{-L/32}\).

For the fixed log rates \(|W|<\eta/L^2\) and each of the other errors \(<\eta/L^3\), the new certified closed onsets are:

| \(\eta\) | B0 | B1 |
|---:|---:|---:|
| \(10^{-8}\) | 200.12 | 176.04 |
| \(10^{-10}\) | 238.90 | 206.73 |
| \(10^{-12}\) | 277.57 | 237.43 |
| \(10^{-16}\) | 354.45 | 298.62 |
| \(10^{-20}\) | 430.83 | 359.54 |
| \(10^{-24}\) | 506.83 | 420.21 |

Additionally at B0 trust keep these **early** log-rate conclusions: \(10^{-6}\) on \([52.9,\infty)\), \(10^{-7}\) on \([58.3,\infty)\), and \(10^{-8}\) on \([64.4,97.6]\). The latter is a finite branch, **not** continuous up to the final \(10^{-8}\) ray. None of the sharp small real onsets for the original Dusart coefficients is displaced by this; those local roots are arithmetic, independent of B1.

**Density-free power/log fallback:** use \(d=1/8,\ C=.040079\) on \(L\ge160\) in B0 and \(d=5/32,\ C=.015625000000005\) on \(L\ge200\) in B1. Here the respective output bounds are \(|W|<C L^2x^{-d}\) and all three other errors \(<C Lx^{-d}\). Thus from the matched \(L=200\) onward the density-free B1 improvement is both in the coefficient and in the exponent. In particular the sharper B1 coefficient uses the exact D02 \(1/64\) and the original signed \(k\)-tail in (4), not a rounded assumption. Here are closed onsets for the same log-rate format using only these density-free fallbacks, separate from the better density results above:

| \(\eta\) | B0 | B1 |
|---:|---:|---:|
| \(10^{-8}\) | 304.65 | 230.56 |
| \(10^{-10}\) | 345.52 | 263.44 |
| \(10^{-12}\) | 385.90 | 295.89 |
| \(10^{-16}\) | 465.59 | 359.85 |
| \(10^{-20}\) | 544.27 | 422.93 |
| \(10^{-24}\) | 622.23 | 485.40 |

### Proof of the new Mertens estimates and joins

For \(L\ge39\) the sharper right bound \(k(L)[6e^{-L/2}+(400/H)e^{-dL}]\) of (4) applies: its proof uses \(5\cdot10^6 e^{-.4L}<1\) on this extended range, not a pointwise truncation at \(L=39\). Replace \(B_d\) in (8) by this sharper bracket without the \(k(L)\) factor. If \(D\) is the chosen endpoint bound (for \(\psi\), or the conservative θ majorant used at late endpoints), the resulting common numerator bounds \(|W|,L|S|,L|\Delta|\) by
\[
 N(L)=D(L)+(1+1/L)[6e^{-L/2}+(400/H)e^{-dL}]+G(L).
\]
The normalized products additionally cost at most \(1/(1-N(L)/L)\) when \(N(L)/L<1\). For a pure-power row use \(D\) of §3, and \(e^{dL}N(L)\) decreases by the same termwise differentiation as before. For the density-free rows \(e^{dL}N(L)/L^2\) decreases using (3) in B0 and the exact \(\frac{1}{64}L^2e^{-5L/32}\) in B1; also \(Le^{-dL}\) decreases, so the exponential-conversion denominator is worst at the anchor. The \(L^2 e^{-dL}\) and \(L^4 e^{-dL}\) derivatives control the corresponding log rates. All shown anchor inequalities are checked as strict with intervals.

For the early windows use CH2 Cor. 1.2 ψ centers shifted to 1 (all sampled \(T\)'s valid already at \(L=39\)), CH2 Cor. 1.3, and literal FiniteRH ψ through \(e^{58}\), as alternative bounds for \(D\); keep \(d=1/8\). For a cell \([l,r]\) of length at most \(1/16\), forms \(a+c e^{-L/2}\) contribute at most \(a r^2+c l^2e^{-l/2}\) to \(L^2N(L)\). The finite-RH branch similarly contributes at most \(l^4e^{-l/2}/(8\pi)\) if \(r\le58\); the other terms and \(1+1/L\) achieve their upper majorants at \(l\). If \(B\) is this interval upper bound for \(L^2N(L)\), the simultaneous log-rate test is \(B/(1-B/l^3)<\eta\) with positive denominator. The two connected rays use these cells through the closed joins 170 and 215, with the B0 density tail tested at those joins. The finite \(10^{-8}\) window only uses its finite cells. Before the new early windows, this method still meets the actual source constraints and finite-sieve roots in mertens.md; it is not an extrapolation of a small fitted coefficient.

## 3. Better zero-density compression, with original source caveat

Let \(h=\log H,\ \alpha=(8s-5)/3,\ q=5-2s\). In each original FKS Table 8 row use the same upward-rounded \((c,f)\) as refine.py. In the Stieltjes integral of common.md replace the exponential majorant of \((h+w)^q\) by its degree-four Taylor polynomial at \(w=0\), valid for **all** \(w\ge0\) since \(3<q<4\) and the fifth derivative is negative. This gives the two-sided reciprocal-mass allowance
\[
 Z_4(s)=\frac{2c\,h^qe^{-\alpha h}}{\alpha}
       \sum_{k=0}^4\frac{q(q-1)\cdots(q-k+1)}{(\alpha h)^k}
      +\frac{2f(h^2+2h+2)}H
\]
(empty falling product 1). Here \(\int_0^\infty w^k e^{-\alpha w}dw=k!/\alpha^{k+1}\) cancels the Taylor denominators. It is nonincreasing inside each row since each factor decreases there and is positive (\(h>1\)); take the prefix minimum as in common.md, preserving nonincrease across row edges. The degree-four polynomial is bounded by \(h^q e^{qw/h}\), so this sharpens the per-row allowances and the resulting pointwise positive endpoint envelope. The shared \(1/4000\) grid, including \(27/32\), and telescoping construction are unchanged; the positive form also retains the \((.04v^2+2)e^{-v/4}\) bulk term. Use the original \(12.546v e^{-v/2}\) remainder of (1) and \(119e^{-v/2}\) for low zeros plus prime powers. Thus the new θ and corresponding ψ majorants are valid for all \(v\ge61\). Do not infer independent validity of the optimized Table 8 parameter calculation: (2.17) is used as the **stated** corollary, with the printed \(\delta\) discrepancy still documented in common.md. The off-line strip boundary changes from \(7/8\) to \(27/32\) exactly by the Mellin argument of common.md; the new table gains below \(L=200\) are not from the literal D02 inequality at those points.

## 4. Expanded whole-domain comparisons and remaining gaps

The overall envelopes are those in the base portfolio with all new applicable branches included, so they are non-worsening on their complete domains. Include the full-strength Büthe allowance and signed bound in the π interval minima only over the range proved above; except for locally sharper products and sums, no strict whole-domain comparison outside the following proved rays is asserted.

For the explicit Mertens envelope including both old and new branches, the strict B1-vs-B0 comparison extends to **\(L\ge168.9\)**. Use the same \(q(L)=\min(1.04\cdot10^{-12},.0039e^{-L/8})\) bound-value argument as in mertens.md. At 168.9 the final .003-wide slices of all three density grids still beat \(.0039e^{-L/8}\) (for the new grid use \(Z_4\) at its last left endpoint). Their prefactors increase thereafter. The source-row floor and all added B0 log-rate rows are tested at their applicable left boundaries, using log decay rates; the finite B0 window expires before 168.9. The new B0 density-free rates also exceed the \(q\) floor (after scaling, their coefficients multiply \(L^2\)); its log-rate rows from the fallback table start no earlier than the corresponding smaller-onset B0 density rows and have the same coefficients. The new primitives only reduce nonnegative integration radii, so the centered subinterval argument is unaffected. The power-tail shifts are still \(<.001q\), verified separately for both components at 168.9. At that point the new B1 coefficient from the pure-power formula times \(e^{-5L/32}\) is \(<.99q\), both comparisons certified. Both ratios decrease on the ray by differentiation of the scaled coefficient and by \(5/32>1/8\). The density-free B1 Mertens bound **alone** also beats that explicit B0 envelope throughout \(L\ge435\): check \(.015625000000005\,435^2 e^{-435/32}<.99\cdot.0039\), and \(L^2e^{-L/32}\) decreases there. On \(L\ge435\) the exponential component is the lesser component of \(q(L)\). These are comparisons of upper bound radii; they are not lower bounds on actual errors and do not claim a universally best B0 envelope.

Exact checks, including failed-bound attempts distinguished from disproofs, are in upgrade.py/upgrade.log and the repair notes. Independent verification of the large inherited finite sign proof and of admissible parameters behind the optimized FKS corollary remain open here. Near the upper limit of the original signed π interval, the absolute π allowances still block a connected \(F_1\) bridge; sharper signed information could change that. For the final Mertens exponent, see the power limitation in mertens.md: the hypothesis used does not exclude zeros on the new boundary, so the smaller coefficients and shorter onsets are not a proof of a better exponent. No new formal verification or source-first PV is claimed.
