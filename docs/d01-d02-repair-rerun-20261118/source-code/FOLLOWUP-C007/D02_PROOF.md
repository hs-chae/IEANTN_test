# D02: a stronger spectral edge and its two applications

## Scope and inheritance

All variables \(x\) are real unless explicitly called integers; prime sums count their right endpoint. All decimals in assertions are exact rationals. B0 denotes the seven pinned originals. Index 0 below uses only B0 and index 1 uses B0 plus the exact D02 hypothesis
\[
 |\psi(x)-x|\le x^{27/32}(\log x)^2/64 \qquad(x\ge e^{200}).
\]
No full RH is assumed. The new **basic** branches do not use FKS Corollary 2.9 or Table 8; the **density** branches use the stated corollary and the original \(a_1=.77\) table. See the inherited note about the table's \(\delta\) versus Theorem 2.7 in foundation.md. This report does not recompute that source table from other literature.

The complete supported floor is incorporated, not replaced: the claim IDs in OWN_D01_VALIDATED_FLOOR.json refer to ramanujan.md, mertens.md, foundation.md, repair.md and their linked numerical receipts. In particular keep the exact connected positivity boundary, finite-table and signed branches, all 770 validated objects including source branches, and all nondominated basic/density tradeoffs. The two deliberately retired historical objects in the floor index are not premises. The old B0 proof of D01 is retained; the D01 conclusion is not being used to replace the new spectral edge. The index-0 calculations below are new reconstructions and secondary improvements within this trajectory, **not** an independent blind baseline.

## 1. Shared analytic bounds

Set \(L=\log x, E(x)=\psi(x)-x, a_0=1/8, a_1=5/32, b_i=1-a_i, H=3\cdot 10^{12}, h=\log H, d_H=h-\log(2\pi)\). We use \(s,\rho\) for complex arguments and zeros; \(\beta=\Re\rho\). The original QRH Theorem 1.1 (PDF p.4) gives \(\beta\le b_0\). The new input gives **\(\beta\le b_1\) for every nontrivial zero**:

For \(\Re s>1\), the Euler product and integration of the absolutely convergent Dirichlet series give
\[
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty E(t)t^{-1-s}\,dt.
\]
Indeed each jump (\(\Lambda(n)\)) contributes \(s\int_n^\infty t^{-s-1}dt=n^{-s}\). On every compact subset of \(\Re s>27/32\), the D02 tail and its logarithm-multiplied versions are dominated by an integrable fixed power times a fixed power of the logarithm. The integral over the finite initial segment is holomorphic without any D02 hypothesis there. The identity theorem for meromorphic functions extends the equality to this half-plane (the continuation of \(\zeta\) is available in CH2 Appendix A, pp.40–41). The log derivative has a pole at any zero of \(\zeta\), so no such zero occurs in the open half-plane. The argument does not remove zeros **on** the edge. This is why several improved bounds begin before logarithmic argument 200. The coefficient and log power in the premise are used as stated, not as a stronger claim about the boundary; this particular continuation would in fact work with any fixed log power.

### Perron estimate without the density table

FiniteRH Theorem 1, PDF p.2, verifies the critical line through \(H\) (CH2 Cor.1.3 gives the exact available height \(H_*=3000175332800\)). Let \(\operatorname{pos}(y)=\max(0,y)\) and
\[
 \begin{split}
 t&=a_i L+c-.9,\\
 B_{i,c}(L)&=\operatorname{pos}((t^2-d_H^2)/(4\pi)+1.8642)\\
 &\hspace{7mm}+(t^2/(2\pi)+1.8642)e^{-(1/2-a_i)L}+2.091Le^{-c}.
 \end{split}
\]
Then \(|E(x)|/x\le e^{-a_iL}B_{i,c}(L)\) on \(L\ge40\) for \(c=4.3,4.4,4.5,4.6,4.65,4.7,6,8\). Apply FKS Theorem 3.2, PDF p.8 with \((40,1/2,0,2.091)\), to \(T=e^{a_iL+c}\). The checker verifies the lower and upper inequalities for \(T\) at 40; they persist since \(a_iL+c-\log L\) increases and \(e^{L/2}/T\) increases while \(2/T\) decreases. Write \(T^*\in[T,2.45T]\) for its adjusted height. Then \(\log(T^*/(2\pi))\le t\). Use PT PNT Lemma 2 (PDF p.4) for the sum of reciprocal absolute nonzero ordinates. At most half its weight strictly above \(H\) has \(\beta>1/2\), by reflection in the critical line at fixed ordinate. Subtract the lower reciprocal-sum bound at \(H\) and divide by two; if \(T^*\le H\) there are no such zeros. The other zeros have exponent at most \(1/2\). This proves all three terms using the given constant for the real-\(x\) Perron remainder. There are no real nontrivial zeros (CH2 Appendix B preceding Lemma B.1).

For \(c=4.65\) the reflected polynomial has one root in \((0,190)\) and one negative root, checked for each \(i\). For \(L\ge199\), each positive summand and hence \(B_{i,4.65}+10^{-8}\) has log derivative \(\le 1/(L-190)+1/L\). For the critical-line term use \(t/L\) decreasing and the exponential factor decreasing, and for the linear term use \(1/L\). This bound is for functions used in the ray proof, not for the arithmetic error itself.

### Log-free density refinement

Use FKS Corollary 2.9, eq. \(2.17\), PDF pp.7–8 and the **upper** Table 8 on p.26. On \(.75\le s\le b_i\), the constants in
\[
 N(s,T)\le C_{1,i}T^{8(1-s)/3}(\log T)^{5-2s}
                  +C_2(\log T)^2 \quad(T\ge H)
\]
can uniformly be taken as \(C_{1,0}=11.0756, C_{1,1}=9.7462, C_2=4.1007\), from the respective first-column maxima of the intersected rows. For real \(s\) here put \(j=5-2s, p=8(1-s)/3\). For \(r=1,2\) use weights \(W_{r,s}=2\sum_{\gamma_\rho>H,\ \beta>s}\gamma_\rho^{-r}\), summing positive ordinates with multiplicity. There is no mass at \(H\) for \(\beta>s\), and the upper boundary vanishes since \(p-r<0\). Integration by parts, and substituting \(T=He^y\), give the upper bound
\[
 W_{r,s} \le F_{r,i}(s)+2 r C_2 H^{-r}
                         (h^2/r+2h/r^2+2/r^3),
 \quad
 F_{r,i}(s)=2r C_{1,i}H^{-(r-p)}h^j
  \sum_{k=0}^4 (j)_k/[ (r-p)^{k+1}h^k].
\]
Here \((j)_k\) is the falling factorial. The Taylor remainder after degree four for \((1+y/h)^j\) is nonpositive on \(y\ge0\) because \(3<j<4\); integration against \(e^{-(r-p)y}\) cancels each (k!). This bounds \(W\) also in the left limit at the spectral edge, where a boundary atom is allowed.

The following upper bounds on \(-(\log F_{r,i})'\) hold for **both** \(r=1,2\) (checked by enclosing the weighted average of the five log derivatives on touching closed cells in \(s\), not by sampling):
\[
\begin{array}{c|ccccc}
 s & [.85,.875]&[.825,.85]&[.8,.825]&[.775,.8]&[.75,.775]\\
 k & 89&90&91&93&95
\end{array}
\]
Use just the portions in the relevant domain. The positive constant term in the weight bound preserves the slope bound. The edge ceilings for \(r=1\) are \(D_{1,0}=.010444061, D_{1,1}=.146294481\); for \(r=2\), \(D_{2,0}=2.504947\cdot10^{-15}, D_{2,1}=3.1525781\cdot10^{-14}\). Their directed checks, including additive terms, are in the evidence.

For \(v=b_i-s\) let \(k(v)\) use the slopes of the indicated cells (in reverse order in \(s\)); prolong the final slope to all \(v\ge b_i-.75\). Write \(v_j>0\) for its knots, \(k_j\) for the slopes just to the right of the knots, and \(k_0=k(0)\). Put \(f(v)=\int_0^v k(u)\,du\). Then \(W_{r,b_i-v}\le D_{r,i}e^{f(v)}\) until the last \(s=.75\). For \(L\ge110\) define
\[
 F_i(L)=\frac{L}{L-k_0}
       +\sum_j\frac{L(k_j-k_{j-1})e^{f(v_j)-Lv_j}}
                          {(L-k_j)(L-k_{j-1})}.
\]
This is \(L\int_0^\infty e^{f(v)-Lv}\,dv\), by adding one slope change at a time to the initial infinite exponential. Every summand is positive and decreasing in \(L\); in the summation \(L/[(L-k_j)(L-k_{j-1})]\) is decreasing as well. The layer integral with lower boundary \(e^{-(b_i-.75)L} W_{r,.75}\) is bounded by \(D_{r,i}F_i(L)\): the continuation of the majorant past \(b_i-.75\) absorbs the lower boundary since it is nondecreasing in \(v\). This layer calculation is valid for a truncated zero sum as well, bounding it by the full absolutely convergent weighted sum over \(\beta>.75\).

For \(r=1\), apply FKS Theorem 3.2 with \(T=e^{L/4}\) on \(L\ge110\). At adjusted height the full reciprocal weight is \(\le .01L^2+118\) and the reflected weight above \(H\) is \(\le .005L^2\) by PT PNT Lemma 2: use \(\log(T^*/(2\pi))\le L/4-.9\) and \(d_H^2/(4\pi)>1.8642\). Treat \(\beta\le1/2\), \(1/2<\beta\le.75\), and \(\beta>.75\) separately. This gives \(|E(x)|/x\le e^{-a_i L}Q_i(L)\) with
\[
 Q_i=D_{1,i}F_i+.005 L^2e^{-(1/4-a_i)L}
       +(.01L^2+118)e^{-(1/2-a_i)L}+2.091Le^{-(1/4-a_i)L}.
\]
Every term decreases on \([110,\infty\)); \(Q_i\to  D_{1,i}\). This choice of cut and slopes also gives an improved B0 comparison. The statement is about the majorant, not an asymptotic equivalent to the arithmetic error.

### Integrated errors and a useful table-free smoothing join

Continue using the integrated formula for \(D(x)=\int_0^x E(t)\,dt\) and the weighted tail from foundation.md, with the low-ordinate constant .0463 from repair.md. All zero denominators are bounded below by the squared absolute ordinate, in the formula for \(D(x)\) and in its integrated tail with kernel \(t^{-2-u}\), \(u\ge0\). Replacing the edge in those proofs gives
\[
 d_i(L)=.0463e^{-L/2}+3\cdot10^{-12}e^{-a_i L}+2e^{-L},
 \quad |D(x)|/x^2\le d_i(L),\qquad
 \left|\int_x^\infty E(t)t^{-2-u}dt\right|\le x^{-u}d_i(L).
\]
The corresponding bound for the extra kernel \((1+\log t)/\log^2t\) is \(d_i(L)(1+1/L)/L\), by the Laplace identity in foundation.md and absolute convergence. These \(d_i\) are valid for \(x\ge2\), not just \(x\ge e^{200}\).

For a tighter bound in both formulas, use
\[
 \widehat d_i=.046301e^{-L/2}+1.5\cdot10^{-12}e^{-a_iL}+2e^{-L}.
\]
Of the squared-ordinate weight above \(H\), at most half contributes with \(\beta>1/2\) by reflection. The rest is covered by the extra .000001 in the critical-line term. In density mode an additional choice for \(L\ge110\) is
\[
 d_i^{(2)}=.046301e^{-L/2}+1.5\cdot10^{-12}e^{-L/4}
                       +D_{2,i}F_i(L)e^{-a_iL}+2e^{-L}.
\]
Split at \(\beta=.75\) and apply the just-proved layer sum with \(r=2\). These are upper bounds on the integrated error and, separately, on the weighted tail with the same multipliers; they are not obtained by integrating \(|D|\) with a triangle loss. Their log-weight bounds follow as above.

Since \(\psi\) is nondecreasing, with \(0<\delta<1\) the averages over \([x(1-\delta),x]\) and \([x,x(1+\delta)]\) enclose its value at \(x\), including jumps. Their linear main terms differ from \(x\) by \(\delta x/2\). With \(c=2.45\cdot10^{-6}\), choose \(\delta=ce^{-a_iL/2}\). The bounds from \(\widehat d_i\) at the two ends of either average give
\[
 \frac{|E(x)|}{x}\le e^{-a_iL/2}
 \left(\frac{c}{2}+\frac{1+(1+10^{-8})^2}{c}
      [.046301e^{-(1/2-a_i)L}+1.5\cdot10^{-12}+2e^{-(1-a_i)L}]\right)
 \le 2.451\cdot10^{-6} e^{-a_iL/2}\quad (L\ge110).
\]
The bracket and \(\delta\) decrease, and their endpoint checks suffice. In particular this needs neither a density estimate nor a truncated explicit formula. As an optional density branch at \(L\ge111\), take \(d=d_i^{(2)}(L-10^{-7})\) and \(\delta=2\sqrt d\), checked \(\le10^{-8}\) at the left endpoint and thereafter decreasing. The same averages give \(2.000001\sqrt d\) for \(|E|/x\), because \(L+\log(1\pm \delta)\ge L-10^{-7}\) and \(d_i^{(2)}\) is decreasing. This trial is more expensive and does not replace the Perron density branch.

For the full pointwise prescription take the intersection of the inherited signed intervals (including all valid CH2 truncations and original-source bounds) and the symmetric intervals from every eligible new \(\psi\) bound. Insert the direct D02 symmetric bound only where \(L\ge200\). For the basic/conditional compact certificates we deliberately use subsets of this full intersection. The direct bound is not the best branch even over its entire eligible domain: the normalized table-free coefficient in §3 below is \(<.0020012<1/64\), including the other Mertens corrections. D02 changes the results mainly **through its inferred spectral edge**, not by replacing the B0 bounds at the same evaluation point with its input majorant.

## 2. Ramanujan gap: improved connected domains, margins and high profiles

Let \(R(x)=ex\pi(x/e)/\log x-\pi(x)^2\), \(g(L)=L^6e^{-2L}R(e^L)\), and
\[
 P_m(L)=\sum_{j=4}^{4+m}\frac{c_j}{L^{j-4}},\qquad
 c_j=\sum_{i=0}^j i!\binom ji-\sum_{i=0}^j i!(j-i)!.
\]
All numerical profile assertions below are **strict** and endpoints written as log onsets are inclusive. Keep the inherited sign ray \(x>r\) with \(R(r)=0\), where \(38358837682+.217926<r<38358837682+.217927\); the least inclusive integer onset is \(38358837683\). The inherited published finite computation and its exact corrected real extension are used only at their stated trust. There is no possibility of reducing the real positive whole-ray onset below this root. The new unconditional analytic positivity ray starts at \(e^{36.524}\).

**D02 dependent.** In density mode \(g>P_2\) holds for all \(L\ge186.95\), rather than the best matched within-method B0 start \(220.70\). The early compact \(P_2\) window is retained and extended in B0 through 125.25. The secondary B0 windows also include \(P_3\) on \([57.36,91.62]\) and \(P_4\) on \([63.30,72.06]\), in basic mode as well (d02_earliest.txt). The following compares connected high-profile starts; P1 is already a density ray from 47.040 in B0.

| Order \(m\) | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| B0 upper sufficient log onset |220.70|253.80|288.00|322.80|358.10|393.70|430|466|502|
| D02 upper sufficient log onset |186.95|211.40|236.70|262.60|288.85|315.35|342.05|368.90|395.85|

For example, at the fixed onset 200 a qualifying whole-ray relative profile in place of \(P_1\) is \(P_2\), raising the bound by \(145/L^2\) in normalized units; at 400 it is \(P_{10}\) in place of \(P_7\). This is a comparison of certified portfolios, not an assertion of failure of any stronger profile in B0. At individual real points, use the full shifted envelopes below instead of rounding to an order.

**D02 basic connected join.** Without FKS Table 8, \(g>P_1\) now holds on \(L\ge47.040\), where the inherited basic window was broken between 190.8 and 271.2. The new closed strip \([185,310]\) is certified using the table-free smoothing estimate and pointwise basic Perron/finite-height minima, and meets the table-free tail from 205. The analogous closed-strip checks give basic \(P_2,P_3,P_4\) rays beginning at 232.625, 260.825, 289.125, joining their analytic starts 233, 262, 290. The B0 runs of the same smoother and Perron trial still leave the \(P_1\) hiatus; see the evidence.

**High-order tradeoffs, including new secondary orders.** In d02_rays.txt every entry at index \(m=0,\ldots,205\) is an inclusive log onset for \(g>P_m\) valid on the whole ray. Select the matching mode and index: 0 = B0, 1 = with D02. These are provided in addition to all better inherited or compact starts. Illustrative rows:

| \(m\) | 15 | 25 | 45 | 50 | 100 | 150 | 200 | 205 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| B0 density |684|1049|1785|1967|3806|5647|7488|7674|
| D02 density |532|806|1358|1494|2873|4253|5634|5775|
| B0 basic |797|1171|1917|2101|3953|5802|7649|7835|
| D02 basic |601|882|1443|1580|2970|4357|5742|5883|

**Early fixed margins, secondary B0 findings.** Each entry is an inclusive start for the stated strict constant margin for \(g\), on the entire subsequent ray. At these starts D02 does not improve the fixed-margin certificates; the binding constraint is the finite-height estimate at the shifted argument, not the far tail.

| \(c\) |0|.11|.20|.42|.50|.71|.75|.90|.92|1|
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| inherited |36.554|36.786|36.988|37.554|37.790|38.520|38.682|39.394|39.504|39.996|
| new B0 |36.524|36.756|36.960|37.526|37.762|38.494|38.658|39.370|39.482|39.974|

At the eight inherited starts for .11 through .92, the replacement whole-ray margins are respectively .124, .212, .430, .509, .716, .756, .904, .924. The limit \(g(L)\to 1\) prevents any constant margin \(>1\) on a whole ray. This limitation does not constrain the nonconstant \(P_m\)'s.

### Proof and reproduction for the Ramanujan claims

Use the principal-value logarithmic integral \(f(L)=e^{-L}\operatorname{Ei}(L)\), not the PT PNT normalization at 2. For the prime-counting bounds use \(R1\) and \(R2\) of ramanujan.md, recomputed with the new spectral exponent in the integral loss. The resulting relative integral remainder is
\[
 I_i(L)=.1852 e^{-L/2}/L^2 + 12\cdot10^{-12}e^{-a_iL}/L^2+10000e^{-L}.
\]
In the integration by parts of \(R1\) use \(d_i\). The exponent in the high-ordinate integral is \(1-a_i\), and the multiplier \((1+9/(8(1-a_i-1/8)))\) after the boundary term is \(<4\) for both \(i\). On \([2,e^{16}]\) the same initial bound as in \(R1\) is valid since the added high-ordinate term has a smaller exponent. Thus a symmetric \(\psi\) majorant \(b(L)\) gives the following upper/lower normalized errors:
\[
 A_+(L)=[b(L)-e^{-L/2}]/L+I_i(L),\quad
 A_-(L)={b(L)+1.2551(e^{-L/2}+2Le^{-2L/3})}/L+I_i(L).
\]
Replace \(A_+\) by zero where the original signed \(\pi\) estimate applies (FiniteRH §3.3, PDF p.5, through \(10^{19}\)). One may clamp either error from below by zero for the polynomial method, which only weakens that side; in the full interval version use the sharper signed errors before clamping the lower bound for \(\pi\) itself to zero. In particular insert the \(\psi\) bounds at \(L\) and **separately at \(L-1\)**; the direct D02 evaluation in the second argument is not used before \(L=201\). All the spectral estimates instead apply at \(L-1\) as soon as that argument meets their own stated domain.

To improve the early margin use Dusart Thm.5.1 (PDF p.14), upper bound valid for real arguments \(>1\), to majorize \(L(J(e^L)-\pi(e^L))/e^L\), where \(J=\sum_{p^k\le x}1/k\), by
\[
 \sum_{k=2}^4 \bigl[1+k/L+2(k/L)^2+7.59(k/L)^3\bigr]e^{-(1-1/k)L}
       +1.2551(2L-4)e^{-4L/5}.
\]
There are at most \(2L-4\) remaining powers \(k\ge5\); Dusart Cor.5.2 in its full domain \(\pi(t)\le1.2551t/\log t\), used as in the inherited R2, covers their counts. Include an additional CH2 Cor.1.2 trial cutoff
\[
 T=\min(H_*,\max(10^7,\pi^2 e^{L/2}/[L/2-\log(L/\pi)-1/6])).
\]
On the early checker strip the denominator is positive and increasing and \(T\le H_*<x\); all eligibility conditions hold since the smaller argument has \(L\ge35.4\). The signed and older CH2 branches are independently retained. These refinements are B0. The proof that the constant >1 is impossible, independent of D02, is the finite-order asymptotic expansion \(g(L)=1+14/L+O(L^{-2})\) in repair.md.

For any \(\pi(e^L)/e^L\) intervals \([\ell(L),u(L)]\) from this construction, with \(\ell\) clamped to 0, the two-sided interval
\[
 [L^5\ell(L-1)-L^6u(L)^2, L^5u(L-1)-L^6\ell(L)^2]
\]
also bounds \(g\) pointwise (non-strict). Take the strongest of this interval, all eligible strict \(R3\) polynomial bounds, and all strengthened and inherited margins/windows as a whole-domain prescription. For an explicit width comparison on \(L\ge201\), the normalized error of \(\pi\) from li is \(\le [Q_i(L)+10^{-8}]e^{-a_iL}/L\) on either side. In the displayed interval this gives a width \(O(L^4e^{-a_iL})\) around the li gap, not restricted to any one profile order. Explicitly, put
\[
 G(L)=L^5 f(L-1)-L^6 f(L)^2.
\]
For every real \(L\ge201\),
\[
 |g(L)-G(L)|\le
 \begin{cases}
 .061L^4 e^{-L/8} & (\text{B0 density}),\\
 .86L^4 e^{-5L/32} & (\text{D02 density}).
 \end{cases}
\]
Indeed \(Q_i(200)+10^{-8}\) is at most .019 or .267, respectively; each majorant decreases. The unshifted \(Lf(L)<1.01\) by the Taylor upper bound at 200 and the factor \((Q_i(L)+10^{-8})e^{-a_iL}<.001\). Accordingly the unshifted squared difference costs at most the normalized cap times \(2.021 L^4e^{-a_iL}\), and the shifted contribution costs the cap times \((201/200)e^{a_i}L^4e^{-a_iL}\). The endpoint constant comparisons are directed. The D02 centered error bound is strictly smaller than its matched B0 bound at every \(L\ge201\), by the ratio at 201 and exponential monotonicity. The full pointwise formulas are stronger than this simplified envelope.

For the strict polynomial checks, continue formula \(R3\). Write \(l_n(L)=\sum_{j=0}^n j!/L^{j+1}\), \(u_n=l_n+K(n+1)!/L^{n+2}\). The new checker uses \((n,K;\text{anchor})=(20,4;32),(50,3;95),(100,3;180),(160,3;275),(210,3;360)\). The derivative comparisons from the inherited proof apply since each anchor \(v\) has \(v(K-1)\ge K(n+2)\); directly compare li at the anchor using \(4v\) terms, twice the first omitted absolute majorant, and the bracket \(-e^{-1}<\operatorname{Ei}(-1)<0\). The absolute term ratio from there is at most \(1/2\). Higher precision is used at the anchors to avoid subtracting near-equal values in low precision. Thus the expansions bound all further values above their anchors. At \(L\) in \(R3\) the shifted lower expansion is strictly truncated, giving strictness even if other estimates are non-strict. For profile order \(m\), the code uses the identities and checks positivity of the needed \(C_{n,j}=c_j\) for \(4\le j\le m+5\) (the equality follows from \(m+5\le n\)). It removes exactly the coefficients of \(P_m\); it does not subtract two numerically rounded nearly equal profiles.

On the closed compact cells see d02_rays.txt and d02_smooth.txt; every certified window is a union of touching cells, not an interpolation of point evaluations. For each compact-to-tail claim the compact endpoint is beyond the separately certified tail start. Early fixed-margin cell checks run to 47.05 and overlap the inherited whole-ray margin 1. The reported retained \(P_2\) early window joins the inherited window via the new checked \([111,125.25]\).

For the infinite tails, put \(p(L)=Q_i(L)+10^{-8}\) (density) or \(p(L)=B_{i,4.65}(L)+10^{-8}\) (basic). The non-Perron losses in \(A_\pm\), after normalization by \(Le^{a_iL}\), fit the cushion: the checker tests the sum at 110 and each summand decreases thereafter. Thus let \(\alpha(L)=p(L)e^{-a_i L}/L\), also using \(\alpha(L-1)\) for the shifted loss. Multiplying the leftover \(R3\) loss by \(L^{m+1}\) gives
\[
 L^{m+5}\frac{L}{L-1}p(L-1)e^{-a_i(L-1)}
 +L^{m+5}p(L)e^{-a_iL}{2Lu_n(L)+p(L)e^{-a_iL}}.
\]
In density mode it decreases when \(L\ge111\) and \((m+5)/(L-1)<a_i\). In basic mode \(L\ge200\), the log derivative of \(p\) is bounded as in §1; the larger test \((m+6)/(L-1)+1/(L-191)<a_i\) suffices. The bracket in the second term is nonincreasing as well. The polynomial surplus after retaining the first positive term and all negative terms is nondecreasing, because each negative term's absolute magnitude decreases. A strict loss-versus-surplus endpoint comparison then proves the whole ray. The checker uses splitting searches only to choose sufficiently good endpoints, not to infer optimality. Nothing here asserts a B0 or D02 infimal onset for the \(P_m\) profiles.

## 3. Mertens products and prime sums

Use the exact Dusart Thms.5.6–5.7 constants (PDF pp.17–19)
\[
 M=\gamma-\sum_{p}\sum_{k\ge2}\frac1{kp^k},\qquad
 B_3=\gamma+\sum_p\frac{\log p}{p(p-1)}.
\]
For \(x\ge2\) use \(w=\sum_{p\le x}\log(p)/p-\log x+B_3\), \(r=\sum_{p\le x}1/p-\log\log x-M\), \(z=\log Q_{\rm raw}(x)-\gamma-\log\log x\). Then the relative product errors are \(|e^{-z}-1|\) and \(|e^z-1|\), using \(P_{\rm raw}=\prod_{p\le x}(1-1/p)\), \(Q_{\rm raw}=P_{\rm raw}^{-1}\). These are correlated bounds, as are the two prime-sum estimates established by the common method. All upper bounds here are non-strict, endpoints inclusive.

### Scaled coefficient and power results

Write \(mathcal E=(|w|, |r|, |e^{-z}-1|, |e^z-1|)\). A “scaled coefficient” \(C\) means \(mathcal E\le(C/L^2,C/L^3,C/L^3,C/L^3)\) componentwise on the whole stated ray. The strongest displayed rows for a given assumption are always used together with **all** eligible original and inherited alternatives. From the new density-mode tables:

| inclusive log onset | 170 | 180 | 190 | 200 | 220 | 240 | 300 | 400 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| matched B0 | \(3.756\cdot10^{-8}\) | \(3.756\cdot10^{-8}\) | \(3.448\cdot10^{-8}\) | \(1.048\cdot10^{-8}\) | \(9.698\cdot10^{-10}\) | \(8.963\cdot10^{-11}\) | \(6.926\cdot10^{-14}\) | \(4.150\cdot10^{-19}\) |
| with D02 | \(2.632\cdot10^{-8}\) | \(5.813\cdot10^{-9}\) | \(1.289\cdot10^{-9}\) | \(2.862\cdot10^{-10}\) | \(1.415\cdot10^{-11}\) | \(6.992\cdot10^{-13}\) | \(8.269\cdot10^{-17}\) | \(2.173\cdot10^{-23}\) |

At fixed scale coefficient \(10^{-8},10^{-10},10^{-12},10^{-18}\), one may respectively use log onsets \(176.39,206.99,237.62,329.20\) with D02 versus \(200.38,239.07,277.67,392.71\) with the matched B0 density construction. Further starts including the powers in the following paragraph are in d02_coeff.txt. The corresponding **table-free** comparison is in d02_basic_mid.txt; for example at \(L=230\) the new coefficient is \(9.727\cdot10^{-10}\), versus \(5.771\cdot10^{-8}\) in the B0 basic calculation. These are sufficient bounds, not minimal coefficients or starts.

* **Basic D02:** on \(L\ge40\), bounds on \(\mathcal E\) are \(.0020012\,x^{-5/32}(L^2,L,L,L)\). The parallel B0 basic bounds \(.001285\,x^{-1/8}(L^2,L,L,L)\) are also valid from \(L=40\) (an earlier basic onset than in the inheritance). Keeping the pointwise coefficient in place of these constants gives a stronger basic normalized limit \(a_i^2/(4\pi)\). For example in the D02 mode at \(L\ge1200\) and at \(L\ge5000\), one may use .001999291 and .001963277 on the same shapes, with \(c=4.65\). The density branch has no \(L^2\) loss.
* **Density D02:** on \(L\ge200\), bounds on \(\mathcal E\) are \(.266350\,x^{-5/32}(1,L^{-1},L^{-1},L^{-1})\); on \(L\ge400\) the same shape has coefficient .188769; on \(L\ge1050.68\) it has .16; on \(L\ge3643.22\), .15. The all-ray pointwise coefficient \(D_{1,1}F_1(L)\) plus the other \(Q_1\) terms, prime-power terms, and integrated/product corrections gives a limiting coefficient at most \(.146294481+3.1525781\cdot10^{-14}\) when using \(d_1^{(2)}\). The matched limit of the corresponding B0 upper-bound function is at most \(.010444061+2.504947\cdot10^{-15}\) but with the slower \(x^{-1/8}\) exponent. These limits are for explicit majorants, not limits of actual errors. The conservative finite and power rows in d02_coeff.txt use \(d_i\), which avoids depending on the squared-density tests for the tabulated claims.
* **Secondary B0 strip:** on \(64000000\le x\le 10^{13}\), replace 1.939 by 1.916 in \(|w|\le C/\sqrt x\), and by 1.8292 in the other three bounds \(C/(\sqrt x L)\). In particular from \(64000000\) there are also whole-ray scaled coefficients .07738 for \(w\) and .07388 for the other three, improving .07815; the inherited post-\(10^{13}\) join is \(<.0097\). Keep the sieve's earlier onsets and exact endpoint bounds, not just the new strip. The late onset of the input is not the bottleneck for this finite strip; the finite estimates of \(\psi\) and square/cube/fourth-prime tails set the accuracy.

The power comparisons here are entire-domain, not sample comparisons. For two coefficients and shapes \(C_i x^{-a_i} L^{q_i}\), the ratio \(D02-mode shape over B0-mode shape\) is \((C_1/C_0)e^{-L/32} L^{q_1-q_0}\), decreasing for \(L>32\max(q_1-q_0,0)\), and tends to zero. Check the ratio at the common onset when it lies in this region, or bound any crossing by solving the stated one-variable inequality on the monotone pieces. In particular the two new basic powers with equal log factors compare strictly on the entire \(L\ge40\) by the ratio at 40; the pure powers with .266350 and .018830 compare strictly on their common \(L\ge200\). Against a \(d/L^k\) old power of a logarithm the ratio is \((C/d)L^{q+k}e^{-a_i L}\), decreasing past \((q+k)/a_i\), so these shapes need not be ordered at earlier starts. For any weaker exponent \(0<a'\le a_i\), a pure-power row with coefficient \(C\) from log onset \(v\) also yields coefficient \(Ce^{-(a_i-a')v}\) at that onset in the weaker normalization. All such branches are intersected rather than declared obsolete at a join. These comparisons do not purport to exhaust unknown B0 derivations.

### Complete pointwise update, not a selected-branch comparison

In \(M1\) of mertens.md use signed intervals as follows. Let \([e_-,e_+]\) bound \(E(x)/x\) by the full intersection in §1. Use a symmetric radius \(\mathfrak d\) for the weighted integral with \(u=0\), taking the minimum of eligible \(d_i,\widehat d_i,d_i^{(2)}\) and all inherited options. The normalized circuit is
\[
 w=(E(x)/x)-\int_x^\infty E(t)t^{-2}dt+W,\quad
 r=(E(x)/(xL))-\int_x^\infty \frac{E(t)(1+\log t)}{t^2\log^2t}\,dt+U,
 \quad z=r-\sum_{p>x,k\ge2}1/(kp^k).
\]
Use the interval for the common second integral with radius \(\mathfrak d(1+1/L)/L\) and intersect with direct signed integrals of eligible pointwise bounds, using \(e_-\) and \(e_+\) separately. Thus all the old absolute-integral and intermediate source options remain. For \(z\) one can equivalently use the same common \(\psi\) terms and the exact tail \(V=U-\sum_{p>x,k\ge2}1/(kp^k)\), with nonnegative \(V\le U\). The Stieltjes boundary is the right-continuous one, as proved in \(M1\).

In the inherited \(W_3\), log-tail, and square-boundary lower formulas improve the uniform \(\theta\) envelope: at \(j=\sqrt x,x^{1/3},x^{1/4}\) intersect the old \(\eta_j\) with any uniform upper bound for \(|\theta(t)/t-1|\) for \(t\ge j\). For example take the monotone minimum of eligible Gas, the basic constant-power bound, the smoothed table-free bound and \(e^{-a_i L}Q_i(L)\), each at \(\log j\) on its own domain, plus
\[
 \kappa(L)=(1+1.47\cdot10^{-7})e^{-L/2}+1.78e^{-2L/3}
\]
at \(L=\log j\). This uses \(0\le(\psi-\theta)/x\le \kappa(L)\) from Dusart Cor.4.5 (PDF p.13), with the right-count convention via right limits if needed. Each selected function stays valid and nonincreasing at every future argument. Retain the inherited signed \(W_3\) strip and the stronger log-tail options for \(U,V\). For the alternative signed \(\theta\) branch use the interval transferred from the full signed \(\psi\) interval and the interval for \(K=\psi-\theta\): \(0\le K/x\le \kappa\), optionally \(K\ge\theta(\sqrt x)\). Integrate signed endpoints using the two \(M1\) kernels as in mertens.md; alternatively use the old closed elementary \(\theta\) expressions when sharper. In the centered \(\Lambda/n\) branch intersect the old signed CH2 interval with \([e_- -\mathfrak d,e_++\mathfrak d]\) and use the inherited centered-weight kernel for the other sums. This updates that branch without regarding its use of the same \(\psi\) input as a separate trial.

Intersect these new bounds with all eligible B0 ones, including the finite branch through 256 million, direct original Dusart Thms.5.6–5.9 (PDF pp.17–20), all earlier table and power branches and the new B0 variants. For the product errors, first translate the final interval for \(z\) through the exponential with the respective sign and take the maximum endpoint error; then take the minimum with applicable direct product bounds. Keeping both signs until this step can be stronger than collapsing to a symmetric error radius. This supplies a pointwise prescription throughout \(x\ge2\) and gives weak dominance by construction at every matched point. It does not rely on searching for crossings of the large multibranch minima. The strict improvements just reported compare verified coefficients at fixed onsets or verified onsets at fixed coefficients, even against the new B0 spectral reconstruction. Eventually the D02 exponential power in \(L\) is strictly faster than every named B0 ray shape (the best B0 spectral exponent here is \(1/8\)); the finite-height branch has a plateau and the pure log-power and classical exp-of-square-root majorants are slower. This is a comparison to the lawful source and reconstructed portfolio, not a claim that B0 logically cannot prove \(5/32\).

### Numerical certificates and tails for §3

For a common sufficient bound put \(B=b+d_i(1+1/L)+W_3\), using the generic \(W_3\) of repair.md. The error vector is bounded by \(B/(1-B/L)\) times \((1,L^{-1},L^{-1},L^{-1})\) when \(B/L<1\), by \(M1\) and \(e^v-1\le v/(1-v)\) for \(0\le v<1\). Nonnegativity and the domain checks are included. In the density-tail case \(b=e^{-a_iL}Q_i(L)\). Then the normalized coefficient after division by \(e^{-a_i L}\) decreases on \(L\ge110\): \(Q_i\) decreases and the normalized \(d_i\) and \(W_3\) terms are products of decreasing positive factors or constants. The exponent \(B/L\) decreases also. The same reasoning holds when using \(d_i^{(2)}\) on this ray. The log-scaled coefficient \(L^2B/(1-B/L)\) decreases there too: apply \(L^je^{-cL}\) decreasing once \(L\ge j/c\) to the constituent summands \((j\le4)\); for the \(F_i\) part only \(j=2, c=a_i\) is needed. Thus endpoint tests furnish the power rows and the fixed log-coefficient inversions on entire rays. For the tables using finite minima, cover \([150,420]\) by touching width-.125-or-shorter cells, then use monotone analytic \(Q_i\) or the basic constant power after 420. Backward maxima over these closed cells give the reported upper bounds. This is actual interval coverage, including the joins.

For basic uniform normalization write \(a=a_i\), \(s=c-.9\). Where the positive part in \(B_{i,c}\) is active, its combination with the explicit-formula remainder normalized by \(L^2\) is \(A+B_1/L+C/L^2\) with
\[
 A=a^2/(4\pi),\quad B_1=as/(2\pi)+2.091e^{-c},\quad C=(s^2-d_H^2)/(4\pi)+1.8642<0.
\]
Hence its maximum is at most \(A-B_1^2/(4C)\); where inactive, bound the remainder by \(2.091e^{-c}/40\). Normalize the critical-line and prime-power/weighted-tail terms by \(e^{-aL}L^2\); they decrease for \(L\ge40\) since \(s>0\) and all remaining factors are positive decreasing. The conversion denominator for the uniform bound increases since \(Le^{-aL}\) decreases there. The chosen \(c=4.4\) gives a certified normalization \(<.0020012\) for D02 and \(c=4.65\) gives \(<.001285\) for B0. For the listed later D02 rows with \(c=4.65\), the polynomial normalized bound itself decreases past 1200, checked by \(1200>-2C/B_1\); the reflector is active there and stays active. This also explains the normalized limit. To prove the constant row on the entire ray it is essential to account for the positive part, not to maximize the polynomial when it is negative and silently use that value for all \(L\).

For the improved finite strip keep the signed \(\theta(t)\le t\) up to \(10^{19}\) (FiniteRH §3.3 p.5) and \(\theta(t)\le(1+10^{-7})t\) above via Gas. For the square boundary \(v=\sqrt x\), a small exact sieve through 10000 checks a relative lower deficit at most .019 on \(8000\le v\le10000\): for integer \(n\), on \([n,n+1)\) use \(\theta(n)/(n+1)\). For \(10^4\le v\le \sqrt{10^{13}}\), use \(\psi(v)\ge v-.751\sqrt v\) from CH2 Lemma 9.2 (p.35) and
\(\psi(v)-\theta(v)=\sum_{k\ge2}\theta(v^{1/k})\le \sum_{k=2}^{21}v^{1/k}\)
on this strip. Intersect with the old square-boundary \(\eta_v\)'s; keep the old signed cube and fourth bound of repair.md. In the Stieltjes square-power formula the boundary \(\theta(v)\) enters with negative sign; the forward integral of the positive \(\theta(t)-t\) costs at most \(10^{-10}/v\), checked by \(2\cdot10^{-7}v/10^{19}<10^{-10}\). Thus replace \(\eta_v\) by the new lower deficit bound in the signed \(W_3\) bound. Multiply by \(\sqrt x\) symbolically before interval evaluation. The strip checker encloses \([\log(64000000),\log(10^{13})]\) by closed width-.01-or-shorter cells on the two sides of the square boundary at \(\log v=\log(10000)\), rounding the interval endpoint evaluations outwards. For the unweighted and product errors, do not bound the square part of the log tail by \(W/L\). Its main term is \(\frac12\int_v^\infty t^{-2}/\log t\,dt\); multiplying it by \(Lv\) makes it
\(\int_0^\infty e^{-s}/(1+s/\log v)\,ds\).
Use the even truncation \(1-u+u^2-u^3+u^4\) as an upper bound for \(1/(1+u)\) on \(u\ge0\). The resulting main coefficient is \(1-1/\log v+2/(\log v)^2-6/(\log v)^3+24/(\log v)^4\). The normalized boundary error (in units \(1/(vL)\)) is still at most \(\eta_v\). The positive tail beyond \(10^{19}\), after multiplying by \(L\), is at most \(3\cdot10^{-7}/10^{19}\): use \(L/(2\log t)\le1\) and \(2+1/\log t<3\) in the derivative. This costs \(<10^{-10}\) in the normalized units. Keep \(W_3/L\) for powers \(k\ge3\). Both \(U\) and \(V\) are bounded by this improved log-tail bound. The scaled maxima are \(<1.916,1.8292\). For the post-sieve join from 64 million multiply by \(L^2e^{-L/2}\), decreasing there, and use the inherited whole-ray joins past \(10^{13}\). This secondary improvement does not depend on D02 or the spectral density table.

## 4. Limitations and substantive tests

* The gap between the early \(P_2\) window and its late D02 ray is not certified. Near \(L=145\) the finite-height bound is about \(10^{-12}\) relative on each \(\psi\) argument; after the two additions in \(R3\) it exceeds the \(P_2\) surplus. Higher \(50, 100, 160, 210\) Taylor calibrations, shifted and asymmetric intervals, alternative Perron cutoffs, the smaller density split, and both smoothed squared-ordinate bounds were tested. Finer cell widths alone do not fix a deficit of the pointwise sufficient bound. No new sign near the inherited exact last zero has been inferred from the macroscopic hypothesis.
* In the Mertens tails, taking an integral of the direct D02 absolute bound loses a large constant, retains the original log factors and cannot exploit the signed integrated formula. Taking the spectral edge first, then reciprocal-ordinate density, removes both logs. Optimized basic truncation reduces the coefficient; the stronger reciprocal-square bound reduces the tail-integral part further, but the main logarithm-free coefficient remains governed by the unsmoothed pointwise error. The more expensive density smoother was tested around the crossover (receipt d02_final_extras.txt); it does not displace the unsmoothed density branch on the ultimate ray. Near ordinary finite onsets the D02 spectral saving in the integrated terms is negligible and cannot replace actual prime computations. The finite strip sieve proof is B0 and is not an attribution to D02.
* A faster Mertens exponential power would constitute genuine additional spectral information: for example if \(w=O(x^{-a_1-\epsilon}L^k)\) with \(a_1+\epsilon<1/2\), partial summation of \(d(\theta-x)=t\,dw\) gives \(\theta(x)-x=O(x^{1-a_1-\epsilon}L^k)\), since \(1-a_1-\epsilon>0\). The same argument for \(r\) uses \(t\log t\,dr\) and increases the log power by at most one. Either relative product bound transfers to \(z\) by taking a logarithm for large \(x\), then to \(r\) by the \(O(1/x)\) tail. Add the prime-power bound and repeat the Mellin argument of §1. This would exclude zeros on the D02 edge; D02 itself does not exclude that edge by this argument. Nothing proves such an edge zero exists. The present numerical coefficients are sufficient, not optimal or best known in an unrestricted sense.
