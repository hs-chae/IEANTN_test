# D02 repair and improved portfolio (FOLLOWUP-C018)

Read together with `candidate.md` and `finite-proof.md`. The current envelope is the maximum of the valid Ramanujan lower branches and the minimum of the valid Mertens upper branches in these documents. Same real and strictness conventions as in candidate.md. The **primary** computations for the new results below use only the Dusart 2.3 density, but retain FKS 3.2 as the all-real explicit formula. This is not simply the earlier Ramaré fallback: the new signed truncation argument certifies **all 12** previously unsupported stronger constants on their exact proposed rays, and improves them. Neither a blind B0 run nor a proof of global optimality is asserted.

## Repair ledger

* Density formula (RQ-density-default, MQ-density-default) and affected `(B)` and `(R)` branches: FKS Cor. 2.9, \(2.17\), printed first panel of Table 8, PDF p.26, LF lines 3169–3186 gives first two coefficients **6.1727, 7.7979**, not 5, 6.3. The c2 coefficient 5 is outward. `verify.py` and the written formula now use the corrected values. This branch explicitly takes the published conclusion of Cor. 2.9 as its premise, not the printed Theorem 2.7 as applied to the tabulated δ values. Use `RAM_ONLY=1` to avoid the discrepancy entirely; every highlight below and in candidate.md has that independent proof.
* M-sign-split-default: the legacy coarse remainder's 106 is replaced by **130**; 60 remains valid. Indeed \(4(6.1727)/.19<130\) at the actual band start .745. The **old** 106 bound is retired, not justified by corrected table entries or by replay. The Ramaré 220/618 branch and its established polynomial and power estimates are retained. The improved remainder below is a different proof.
* M-power-0-{180,190,200,210,220}, M-power-1-{160,170,180,185,190,200,210}: each **original numerical statement** proved in `refine-M-evidence.txt` (lines marked “restored”), using the new remainder and no FKS density. These include .025 and .431 at their original onsets, not the larger fallback coefficients. Matched M-ratio-default and M-guard-default consequently follow with .0135/.226 as previously stated; the closed comparison used original source domains. The new guard below goes further. Legacy weaker rows and continuous alternatives remain valid. `repaired-comparison-ram-only.txt` is the comparison with the independent density switch active.
* M-source-small-false, M-boxes-false: retire **exactly** the unguarded FKS 5.2 source branch and the envelope that used it. At \(L=.01\), the true relative error is 1, not less than .002; at \(L=10^{-20}\) the old ungated minimum's unsigned \(W_1\) transfer cost is less than 20, versus \(W_1>45\). For the latter, integrate \(2u^{3/2}k_1(u)\) up to 4 (cost at most \(56/3\)) and \(59.18u^{-4}k_1(u)\) afterward, and add the endpoint cost at most \(2\sqrt L\). No consequence of that minimum on this low range survives. The **repaired** branch is used only on \([.85,2100]\). On \([.85,1]\), \(\psi(e^L)=\log 2\); exact outward cell evaluation checks the inequality there. On \([1,40]\), the proposed radius is bounded below by its smaller endpoint value (its log derivative changes sign at most once, from + to −), greater than .77, so Dusart 3.3 applies. For \(40<L\le1000\) and \(1000<L\le2100\) use the two step bounds in the proof of FKS 5.2 (p.17, LF1928ff), respectively; the proposed radius decreases there and exceeds the step bound at each right endpoint. At \(L=40,1000\) use the preceding interval. The checks are in `refine.py`. For \(x<2\) the exact sums/products and relative Chebyshev error replace any fabricated small-\(x\) expression. The signed kernel identities themselves are unchanged, now with only valid input boxes.
* The exact limsup proof is given below, including control of the finite multiplier; the earlier real endpoint correction and inherited literature domains remain unchanged. All original candidate bytes (including original evidence) remain recoverable verbatim from `prior-exact.json`, by writing each value with UTF-8 encoding to the named file in a **separate** flat directory. The old unsupported or false claims therein are history, not active statements.

## 1. Ramanujan improvements

New sufficient starts for \(G=L^6 R/x^2\) strictly greater than the indicated profile, all inclusive in \(L\). An unchanged cell in this table comes from the prior valid proof. The comparison is within the same method/premise sets, not to a weak sign-only baseline.

| Profile | B0 start | B1 start |
|---|---:|---:|
| .1 | 36.94 | 36.94 |
| .5 | 38 | 38 |
| .9 | 39.56 | 39.56 |
| 1 | 40.16 | 40.16 |
| \(P_1+14/L^2\) | 47.45 | 47.45 |
| \(P_1+19/L^2\) | 48 | 48 |
| \(P_1+42/L^2\) | not certified at 48 | 48 |
| \(P_1+82/L^2\) | not certified at 53 | 53 |
| \(P_2\) | 216.55 | 185.6 |
| \(P_3\) | 250 | 209.95 |
| \(P_4\) | 285 | 236 |
| \(P_5\) | 319 | 262 |
| \(P_6\) | 355 | 288 |
| \(P_7\) | 392 | 316 |
| \(P_8\) | 426 | 341 |
| \(P_9\) | 462 | 368 |
| \(P_{10}\) | 498 | 395 |
| \(P_{12}\) | 571 | 449 |
| \(P_{15}\) | 680 | 531 |
| \(P_{20}\) | 862 | 667 |

At \(L\ge200\), upgrade the certified pair to \(P_1+116.6/L^2\) (B0) and \(P_2+1240/L^3\) (B1); at \(L\ge240\) to \(P_2+1320/L^3\) and \(P_4+67000/L^5\), respectively. The early bounded B0 components become \(P_2\) on \([52.3,125]\), \(P_3\) on \([57.7,91]\), \(P_4\) on \([63.8,71.8]\). The exact connected strict-sign ray \(x>r\) is **unchanged**; in particular \(x=r\) is excluded. The high-margin domains are not thereby all connected.

Here are the improvements to (R). For the upper count only, use the reported \(\theta(t)<t\) throughout \(2\le t\le 10^{19}\) (FiniteRH §3.3, p.5, explicit report of a finite computation), with \(e^{43.74}<10^{19}\). Discard its nonpositive contributions in the upper \(\pi\) error, both in full prefix and in the individual cells where applicable. The lower count is unaffected. Refine the early moving windows to widths \(1/4\), with the same rigorous upper bound \(L(e^{-z_1}-e^{-z_2})/(L-z_2)^2\) on each integral weight. The prefactor is evaluated outward on the full L-cell, and all validity tests are over the entire cell.

For the spectral tail use the finer mesh described below for \(s_0=.745\) and the full verified height \(H_*=3000175332800\) in its mass bounds; keep the old \(J\) and the majorant \(.02u^2 e^{-.255u}\) for low zeros. In \(\int_{L/2}^L\) use
\((L/u)^2\le e^{4(L-u)/L}\), by integrating the derivative of \(-2\log u\). For each endpoint monomial \(c u^j e^{-du}\), \(d\le 2/3\), the ratio of the integrated term to the endpoint majorant is therefore at most (1/[L(1-d)-4]), hence at most (1/(L/3-4)). The pre-(L/2) prefix is unchanged. This bounds the late π error by \(b^*(L)(1+1/(L/3-4))+\mathrm{prefix}(L,L/2)\), with the new mesh. Its multiplicative factor decreases, so the scaled-loss proof of monotonicity in candidate.md §3 applies verbatim to the new tail; in particular \(L-1>8(4+n+1+3)\) and the power checks in `higher.py` are enforced. The earlier and late interval bounds are intersected where valid. For a bounded extension of a previous ray the explicit interval overlaps the old ray inclusive of its first point. Otherwise the finite and monotone pieces join at the certified common endpoint. See `refine-R-evidence.txt` for cell counts and tail slacks, or run `RAM_ONLY=1 /usr/bin/python3.10 ramref.py`. The new code uses (R) minus the target with canceled terms, not a sample of \(G\).

In the two treatments only the cap \(\beta\) and the branch directly using D02 change. The explicit-formula range and all finite data are identical. The new table documents earlier matching higher-margin onsets and stronger conditional margins at fixed endpoints; it does not imply that B0 is incapable of proving these conclusions by a different argument.

## 2. A stratified truncation remainder for Mertens

Let \(a=1-\beta\), \(H_*=3000175332800\), \(h_*=\log H_*\), and \(T=e^{u/2}/6\) in FKS Theorem 3.2, as in candidate.md. Put \(s_0=.72\) (mesh branch) or .745 (continuous branch). Dusart 2.3 applies already at these lower splits: with \(p=8(1-s)/3, d=1-p, q=5-2s\), use \(A=4.9\,3^p,B=51.5\); the optional second branch substitutes a lawful FKS pair, or keeps the Dusart pair. For the high zero series use the right-endpoint cumulative mesh as in \(Z\), but with spacing \(1/2000\) (final short cell allowed) and \(H_*\) instead of \(H\) in the quartic Taylor mass. Let \(Z_*(u)\) denote its **unscaled** majorant. Both branches include cap atoms. Low zeros and the Perron remainder are bounded by
\[
 (.04u^2+13u+2)e^{-u/2}+.02u^2e^{-(1-s_0)u},
\]
using (B)'s derivation with \(s_0\) substituted, and the **old** \(J\) based on \(H\) (a safe enlargement). This is the cost of omitting low-real-part zeros, not all zeros above \(T\).

For the missing high zeros **above** \(T^\star\), use disjoint real-part cells \([s,t)\) of width \(1/100\) starting at \(s_0\), including the final cap in its cell. The cost per cell is bounded by
\[
 2e^{-(1-t)u}\int_T^\infty
   (A(s)y^{p(s)}(\log y)^{q(s)}+B(s)(\log y)^2)\frac{dy}{y^2}.
\]
We may bound a cell by its cumulative mass without subtracting another upper bound. The product of \(e^{-(1-t)u}\) and \(T^{-d}\) is critical: bounding all cells by the cap at this step is far more costly. With \(v=\log T=u/2-\log 6\), the two terms are bounded by
\[
 \frac{2A\,6^d}{2^q(d-q/v)}\,u^q e^{-(1-t+d/2)u}
 +12B((u/2)^2+u+2)e^{-(1-t+1/2)u}.
\]
Indeed \(v^q\le(u/2)^q\), \((1+w/v)^q\le e^{qw/v}\) and \(\int_T^\infty (\log y)^2y^{-2}dy=(v^2+2v+2)/T\). These are the positive terms \(\kappa_\nu(u)u^{n_\nu}e^{-b_\nu u}\) in `parts`, together with the low/perron terms above. Their prefactors are positive nonincreasing where the checked denominators are positive. This proves the high-series decomposition of candidate.md with the new remainder everywhere on the stated rays. In particular at the used endpoints (lowest mesh start 130) \(T\ge H_*\); the proof does not extend the direct hypothetical \(\psi\) majorant to earlier arguments.

The weighted transfer via (K) consequently gives, for \(j=0,1\),
\[
 L^j |W_j(L)| \le
 \min(1+2(1+j/L)/H_*,\,1+j/(aL)) Z_*(L)
 + \sum_\nu \kappa_\nu(L)L^{n_\nu}e^{-b_\nu L}
 \left(1+\frac{1+j/L}{b_\nu-n_\nu/L}\right).
 \tag{M*}
\]
For each remainder use the decreasing prefactor and \((1+w/L)^n\le e^{nw/L}\) in the integral. The first zero multiplier follows by direct parts as before. For the second put \(f(u)=u^{-j}\), \(\lambda=\rho-1\). The contribution of \(-e^{\lambda u}/\rho\) under (K) is **exactly** \(\int_L^\infty f(u)e^{\lambda u}\,du\): integrating \(f'\) in \(k_j=f-f'\) produces the endpoint which cancels. Multiplying by \(L^j\), one integration by parts gives main term \(e^{\lambda L}/(1-\rho)\) and difference in absolute value at most
\[
 \frac{j\,e^{(\Re\rho-1)L}}{aL|1-\rho|}.
\]
Here \(|1-\rho|\ge|\Im\rho|\), as is \(|\rho|\); the mesh majorizes weights \(1/|\Im\rho|\), not just \(1/|\rho|\). This proves (M*) including the exactly 1 multiplier for \(j=0\). All integrals commute with the high series by absolute reciprocal summability and uniform exponential majorization. For the original proposed limsup, apply this exact calculation and dominated convergence after scaling by \(e^{aL}L^j\); off-cap terms vanish, while the cap mass is bounded by the quartic \(C(\beta)\). The positive remainders and prime power terms tend to zero after scaling and the exponential conversion multiplier tends to 1. Thus the proof does not substitute 1 for a limiting finite-height factor which is actually greater than 1.

**Continuous version.** For \(s_0=.745\) let \(C_R(s)\) be the quartic Taylor density mass evaluated with \(H_*\) and the Ramaré pair. The log derivative of the positive first portion is negative, with magnitude bounded by
\[
 \frac83(h_*+\log 3)+2\log h_*+\frac{8}{3d}
 +\left(\frac{8}{3d}+8\right)\frac{r}{1-r},\qquad r=\frac{q}{h_*d}.
\]
In fact the \(j\)-th polynomial term's log derivative has extra magnitude at most \(j(8/(3d)+8)\), since \(q-k\ge1/4\) for \(k\le3\). Successive terms have ratio at most \(r<1\), so the weighted mean of \(j\) is at most \(\sum_{k\ge1}r^k\); the inequality for each tail weight follows by shifting its terms by \(k\). The additive \(B\) term is constant. All bounds decrease with \(s\) and their value at .745 is less than 105. Therefore the same continuous integration as \(C\) gives \(Z_*(L)\) replaceable by \(C_R(\beta)e^{-aL}L/(L-105)\). The resulting cap bounds are <.006664 (B0), <.116246 (B1), also valid in the exact limsup argument without the finite factor.

**Prime-power signed refinements.** Enlarge \(D_-\) where \(x\ge121\) by \((1-\eta)e^{-L/2}\), with \(\eta=\min(10^{-4},4/L^3)\), using Dusart Proposition 4.3 p.12 in addition to Theorem 4.2. For \(x\ge121\) a lower bound on \(L^jT_j\) is the positive part of
\[
 (1-\eta)e^{-L/2}
 \left(\frac1{1/2+j/L}+\frac{j/L}{1/2+(j+1)/L}\right)-D_+(L).
\]
Use the exact parts expression for \(T_j\) in \(T\), the lower \(D\) valid over its full future tail, and \(u^{-k}\ge L^{-k}e^{-k(u-L)/L}\) for \(u\ge L\). Use zero below 121. For the log product use \(T_{1,\mathrm{tr}}=T_1-A_{>x}\), so its lower bound is at least 0 and at least the **unscaled** lower bound for \(T_1\) minus \(1/(2\lfloor x\rfloor)\). Intersect the resulting signed boxes with all other valid boxes *before* applying the exponential conversion. The improved \(D_-\) is also admissible in the \(\psi\)-to-\(\theta\) signed box. These lower-tail bounds often matter to signed comparisons, not to the single simultaneous unsigned constant.

## 3. Improved simultaneous Mertens bounds

Same normalization as candidate.md §1: each row means at most \(C x^{-a}/L\) for the three unweighted errors and at most \(C x^{-a}\) for the weighted error.

| \(B_0:a=1/8\), \(L_0\) | C | \(B_1:a=5/32\), \(L_0\) | C |
|---:|---:|---:|---:|
|150|.01751|130|.416|
|160|.01593|140|.353|
|170|.01476|150|.311|
|180|.01386|160|.282|
|190|.01314|169|.263|
|||170|.261|
|200|.01256|180|.245|
|210|.01207|185|.238|
|220|.01166|190|.232|
|250|.01075|200|.221|
|300|.00981|210|.213|
|400|.00884|220|.205|
|600|.00808|250|.189|
|1000|.00745|300|.172|
|2000|.00704|400|.155|
|4000|.00685|600|.141|
|10000|.006735|1000|.130|
|||2000|.123|
|||4000|.120|
|||10000|.1175|

Rows dominated by the following connected joins are included as reproducible sufficient tests; use the pointwise minimum, not a priority list. In fact \(C=.01343\) (B0) and \(C=.265\) (B1) are both valid already from **\(x=2278382\)** for the products, **\(x=2278383\)** for \(E_1\), and **\(x=912560\)** for \(E_w\). For use as pointwise envelopes, take `refine.rad` with `with_tail=False` (divide by the normalization to get the symmetric primitive box) on \(L\ge130\) for the mesh branch or \(L\ge600\) for the continuous branch, and then use the signed transfers in §2. The split CH2 integral on its proven interval in the next paragraph can also be included as a pointwise primitive bound, with the relevant weights and product conversion. For a row or a particular evaluation of (M*) we add the harmless unsigned \(T\) with \(D_-=0\) for the certificate. After scaling the right-hand side by \(e^{aL}\), its positive terms are nonincreasing: the exponent gaps are nonnegative for the spectrum and strictly positive for the remainders, \(L_0(b_\nu-a)>n_\nu\) is checked, denominators increase and kernel prefactors decrease. The product multiplier also decreases. Thus checking the left endpoint proves the whole ray. `refine.py` checks the historical exact rows, the table here, and the joins. The signed pointwise refinement (M*) may use the effective remainder plus all prime-power intervals instead of its symmetric overestimate.

**Early-to-late joins for the power shape.** Up through \(L=20\) use the direct Dusart polynomial branches, bounding \(e^{aL}(.3/L^2)\) by its maximum at the endpoints of \([13.7,20]\), with \(e^{13.7}<912560\). This endpoint rule follows from convexity of \(aL-2\log L\). On \([20,50]\) use the existing .04 polynomial branches and the same test. For \(50\le L\le t\), split the exact \(W_1=W_0/L-\int_L^\infty W_0(u)du/u^2\) at \(t=185.8\) (B0), or \(t=167.75\) (B1), with CH2 \(c+B e^{-u/2}\), \(c=1.0472\cdot10^{-12},B=113.67\), before \(t\); beyond \(t\), use the independently checked \(C e^{-au}\) for \(W_0\) itself, valid by (M*) without prime powers. After multiplying by \(L\), the resulting unweighted bound before powers is
\[
 c(2-L/t)+B(1+2/L)e^{-L/2}+\frac{LC e^{-at}}{at^2}.
\]
The weighted \(W_0\) bound is smaller. Multiply by \(e^{aL}\), add the (T) terms (drop \(D_-\)), and bound the first and third terms at \(t\) (monotonicity since \(at>1\)), the decaying terms at 50 with rate (1/2-a). For the product conversion the separate unscaled log bound is checked at once by using \(L\ge50, L\le t\). At \(L\ge t\) use (M*) alone; its certified coefficient is at most the same \(C\). These joins give one power bound on the entire stated real rays. The older polynomial and finite branches remain in the minimum even where this power form is larger.

**Supplementary B0 polynomial improvements.** With the stronger \(D_-\) the analytic polynomial joins use \(1.000100294e^{-L/2}+2.67e^{-2L/3}\) in \(T\), giving for the three unweighted errors .08/\(L^3\) from \(L=18.05\), .077/\(L^3\) from 18.15, .037/\(L^3\) from 20. For \(E_w\) they give .079/\(L^2\) from 17.95, .0774/\(L^2\) from 18, .035/\(L^2\) from 20. The proof is by the same full closed-cell joins to 200 as before, with the same monotone tail (dropping the tail subtraction at 200). No new finite sieve assumptions. These improvements do not need D02.

**Comparisons.** At \(L\ge200\) the new matched-row ratio is \((.221/.01256)e^{-L/32}<.035\) (the original pair is also retained, with its own ratio <.033). The new sufficient log onsets for the scaled targets \(10^{-14},10^{-18}\) are (223,295) in B0 and (197,255) in B1. The conversion to target radii uses \(L|E_1|,L|\mathcal P-1|,L|\mathcal Q-1|,|E_w|\), not only the log errors. The exact power crossover convention is unchanged. The sharper power is obtained from D02's zero exclusion; the direct \(L^2/64\) input has not been extended left of 200 or used as a certified radius reduction constant below 200.

The pointwise strict comparison against the enumerated B0 envelope now starts at **\(L=169\)**. In the weighted scale \(L^j\) (with \(j=1\) also for each relative product), let \(g=\min(1.047\cdot10^{-12},.005e^{-L/8})\). The non-CH2 source radius comparisons of candidate.md §6 hold with the same .005 on this earlier ray: `comparison.guards(169)` checks actual applicable table/curve powers at their first matched arguments, using the positive log-derivative proof of ratios. For CH2 the floor is \(>1.047\cdot10^{-12}\) on the applicable ray. For the B0 spectral boxes, the relevant endpoint coefficients in both meshes and both continuous bounds exceed .005. Connecting to CH2 across the new power join does not remove that guard: the primitive \(W_0\) and integrated \(W_1\) bounds before the join still have the CH2 endpoint floor, and the late bound is spectral. Pure constant-coefficient power branches have \(C>.005\). The only negative corrections are prime power or product-tail subtractions and exponential conversion. Their scaled size before exponentiation is bounded by \(2D_+(L)+Le^{-L}\), which is less than (.01g) on this ray (each ratio decreases against both parts of the minimum). Hence the signed boxes even after intersection contain both signs with scaled magnitudes at least (.99g); direct relative polynomial/product boxes also contain the corresponding signs after log conversion, by the same polynomial guard and \(1-e^{-r}\ge r-r^2/2\). The exponential conversion loses less than a further factor .01 in this comparison. The B1 estimate from (M*) is at most \(.263e^{-5L/32}\) in this scale from 169. It is strictly below (.9g) at 169 and thereafter by comparison of both exponential rates. So all four improved radii are strictly smaller than the enumerated valid B0 envelope there, not merely than a selected weak original polynomial. This is a radius comparison, not a claim about the value or sign of any true prime error. No strict ordering against arbitrary unenumerated refinements is inferred. The B1 envelope contains every valid B0 choice everywhere, including where this stronger strict comparison has not been certified.
