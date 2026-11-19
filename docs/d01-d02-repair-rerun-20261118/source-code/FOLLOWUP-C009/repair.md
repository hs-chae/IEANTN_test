# D01 own-review repair and further bounds

This supplements [psi](psi.md), [Ramanujan](ramanujan.md), and [Mertens](mertens.md). All claims use the original common sources (**B0 only**) and ordinary exact-arithmetic certificates at the same trust tier. Onsets below are inclusive, \(x>1\) and \(L=\log x\) are real. No full RH, uncertain \(a_1=.618\) subconvexity premise, or new source is used. The D01 assumption is redundant by the original \(.020x^{7/8}\) proof in psi.md. The strongest lawful consequence sets and thus pointwise envelopes on any matched domain coincide, not merely the estimates shown below. These improvements are separate B0-only arithmetic, not treatment gains or an independent blind B0 stage.

## Exact repair and retained history

In the **old** Mertens formulas, \(H=3\cdot10^{12}\). Both high-zero multipliers tend to \(1+2/H\), not 1. Each normalized coefficient actually tends to
\[
(1+2/H)\,.010445=3133500000002089/300000000000000000.
\]
No old inequality changes, including all ten rounded spectral rows. The false sentence is corrected in candidate.md and mertens.md. The original wording is in prior_candidate.md and prior_mertens.md, with original scripts and receipts unchanged. Below we derive a different, stronger coefficient without the factor.

The literal lower real endpoint in PT 2021 Thm 2 was already disproved by the candidate and is not reinstated. The last failing real remains \(x_*\) in ramanujan.md, with equality there and strict positivity on the open ray \((x_*,\infty)\). The claim still uses the published finite **integer** conclusion at inherited trust, without the unsupported general real-start stepping argument or an independent resieve of that huge computation. The local counts, rational bracket and real interpolation are unchanged. These are the two distinctions identified in the own review. Review replays and source readbacks are evidence and feedback, not premises.

## Common high-zero bound, refined

In the new proof only, put \(H'=3000175332800\), \(h'=\log H'\), \(b=7/8\). The height is from Platt–Trudgian finite RH (PDF p.2 Thm 1; see also CH2 p.3). Keep the absolutely convergent series \(V(v)=-2\Re\sum_{\beta\ge.78,\gamma>0}e^{(\rho-1)v}/\rho\) of mertens.md. All its ordinates exceed \(H'\). Set \(A(s)=2\sum_{\beta\ge s,\gamma>0}1/\gamma\) for \(.78\le s\le b\). In particular \(A\) is nonincreasing. As in psi.md, FKS (PDF p.7 Cor. 2.9, (2.17); p.26 Table 8, **first block**) and summation by parts give
\[
 A(s)\le B_{c,d}(s)=2c\int_{h'}^\infty u^q e^{-\alpha u}du+2d e^{-h'}(h'^2+2h'+2),
 \quad q=5-2s,\quad\alpha=(8s-5)/3,
\]
with exact displayed \(c,d\) on each row. For fixed \(c,d\) this is convex in \(s\) since the nonconstant integrand is a positive multiple of \(\exp[-s((8/3)u+2\log u)]\). The degree-four Taylor bound for \(u^q\) about \(h'\) (fifth derivative negative since \(3<q<4\)) gives the endpoint enclosure
\[
 B_4(s;c,d)=2c\,h'^q e^{-\alpha h'}\sum_{j=0}^4
 \frac{q^{\underline j}}{\alpha^{j+1}h'^j}+2d e^{-h'}(h'^2+2h'+2).
\]
Use nine rows from [.75,.80] to [.87,.88], trimming the first at .78 and the last at \(b\). Split each interval into five equal subintervals. On a subinterval \([\ell,u]\), round both Taylor endpoint enclosures up to the \(10^{-9}\) grid, obtaining \(C,D\). The chord bounds \(A\) by convexity of \(B_{c,d}\). Take its minimum with the previously established right-endpoint cap (first part uses \(C\)), since \(A\) cannot rise. The resulting cap \(\mathcal B\) is continuous and nonincreasing: repair_cert.py verifies \(C>D\) and \(C\) at least the previous cap even at row switches. Clipping leaves at most one nonflat subsegment per part; the code builds their endpoints exactly as rationals and verifies \(\mathcal B(b)=K=.010443624\), with the unrounded upper enclosure at \(b\) strictly below that number. No uncertain subconvexity variant is used.

Layering the nonnegative zero weights and integrating the resulting majorant by parts gives
\[
 2\sum_{\beta\ge.78,\gamma>0}\frac{e^{-(b-\beta)v}}{\gamma}
 \le e^{-(b-.78)v}\mathcal B(.78)+\int_{.78}^b v e^{-(b-s)v}\mathcal B(s)ds
 =K+\int_{.78}^{b}e^{-(b-s)v}(-\mathcal B'(s))ds=:Z_*(v).
\]
There is no jump term. zg() evaluates the last integral on the nonflat subsegments. Therefore \(Z_*\) decreases to \(K\), by dominated convergence, regardless of whether there are zeros on \(\beta=b\).

Retain \(d_c(v)\) of mertens.md for \(e^{v/8}|\mathcal D(v)|\), where \(E(v)=(\theta(e^v)-e^v)/e^v=V(v)+\mathcal D(v)\). A different cutoff \(T=e^{2v/5}\) in the same admissible all-real FKS explicit formula (PDF p.8 Thm 3.2) yields another bound:
\[
\begin{split}
d_g(v)={}&.026v^2e^{-3v/8}+.013v^2e^{-7v/40}
 + W(.70,h';6.1727,4.4992)e^{-v/8}\\
 &+W(.75,h';7.7979,4.1006)e^{-.095v}
 +2.091v e^{-.275v}+e^{v/8}p(v)
 +\sum_i W(s_i,2v/5;c_i,d_i)e^{(s_{i+1}-b)v}.
\end{split}
\]
The \(W,p,s_i,c_i,d_i\) notations are those of psi.md and mertens.md. For \(v\ge100\), admissibility at 100 extends by increase of \(T/v\) and \((e^{v/2}-2)/T\). The bound in psi.md for the full reciprocal-ordinate sum with \(z\le 2v/5+1\) gives \(.026v^2\) by expanding the quadratic; use half that for \(1/2<\beta<.70\) by reflection. The next two strips \([.70,.75)\), \([.75,.78)\) use the first-block source rows \([.70,.75]\), \([.75,.80]\) at height \(H'\), scaled at their strip right ends. The last six bins cover the omitted high zeros (above \(T^*\), hence above \(T\)). The truncation and prime-power corrections are retained. Both cutoffs refer to the same \(V\), so \(d(v)=\min(d_c(v),d_g(v))\) bounds the scaled remainder. Each term decreases for \(v\ge100\) and tends to zero: for \(W(s,\kappa v;c,d)\) use the positive increasing tangent denominator and \(q/(\kappa v)<\alpha\) when \(\kappa=1/3,2/5\). The minimum preserves these properties.

## Mertens: cancel the old loss before bounding the mode

Use the endpoint-minus-tail identities for \(D_1,D_2,Z,J\) in mertens.md. For \(D_2\), the factor applied to a high mode \(e^{(\rho-1)L}/\rho\) is
\[
 1-\int_0^\infty e^{(\rho-1)t}dt=-\rho/(1-\rho),
\]
so the absolute contribution is at most \(e^{(\beta-1)L}/|\gamma|\), without the old \(2/H\) surcharge. For \(D_1\), represent \(1/L=\int_0^\infty e^{-Lu}du\) and \(w(L+t)=\int_0^\infty(1+u)e^{-(L+t)u}du\). The combined factor is
\[
 \int_0^\infty e^{-Lu}\left[1-\frac{1+u}{1-\rho+u}\right]du
 =-\rho\int_0^\infty\frac{e^{-Lu}}{1-\rho+u}du.
\]
The absolute contribution is at most \(e^{(\beta-1)L}/(L|\gamma|)\). Fubini per mode follows from \(\beta\le b<1\) and the integrable weight in \(u\); summation under the tail integrals follows from \(A(.78)<\infty\) and uniform exponential decay. This cancels the denominator \(\rho\), not the entire tail.

Thus for \(L\ge100\),
\[
 |D_2|\le e^{-L/8}(Z_*+9d)(L),\qquad
 |D_1|\le(e^{-L/8}/L)[Z_*+(9+8/L)d](L).
\]
The remainder uses its endpoint and the integral bound \(8e^{-L/8}d(L)w(L)\) (with weight 1 for \(D_2\)). Add \(3e^{-7L/8}\) to the normalized \(D_1\) coefficient to cover \(J\) as in mertens.md; call the result \(B_P(L)\). Include \([-u_P,u_P]\) in the signed \(Z\) intersections for \(u_P=e^{-L/8}B_P(L)/L\), using their exact exponential conversions. Both relative errors are at most \(u_P/(1-u_P)\); positivity of \(1-u_P\) is checked at 100 and then follows by monotonicity. The normalized coefficient for that product bound, as well as those for both sums, decreases and now has exact limit \(K\). This is not a limit assertion about the actual arithmetic errors.

The lines labelled M in repair.out give strict coefficients \(c\) on real inclusive \(L\)-rays: \(ce^{-L/8}/L\) for \(D_1\) and both relative products, \(ce^{-L/8}\) for \(D_2\). The endpoint check extends to the entire ray by monotonicity. For example the old .0195 from 200 holds from 183, with .018097 at 200 and .01579 at 250. The .01938 branch beats the rounded \(2.10\cdot10^{-12}/L\) plateau from 184 for \(D_1\) and both products. The .01893 branch beats the rounded \(D_2\) plateau on its ray from 189, and beats even the new .0391 polynomial bounds of the respective shapes there (test the endpoints; \(L^2e^{-L/8}\) decreases). These are comparisons with rounded branches, not assertions that every signed bound crosses there. Use the pointwise minimum including the old results. See [repair_poly](repair_poly.md) for the new inverse-log tradeoffs.

## Ramanujan: earlier quantitative rays

Extend the finite sign input by **Dusart 2018, PDF p.15, proof of Thm 5.1**, which explicitly reports \(\pi(x)<\operatorname{li}(x)\) for \(x<1.39\cdot10^{17}\) in the principal-value normalization (pp.13–14). It applies on the newly used section \(39.32\le L\le39.47\), with the strict log boundary certified, and no use of full RH or new finite computation up to that bound. Set \(r_+(L)=0\) for the one-sided branch up to 39.47, not at a substituted shifted argument. Both variable profiles in ramanujan.md extend by their formulas down to \(L=36.713\); their shifted li anchor and all endpoint error domains hold.

Each R closed line of repair.out is a closed log-interval test of \(G>c\) or \(G>c+14/L\) when the last Boolean is True. The first Boolean indicates use of the finite sign. Each cell uses the full interval of the polynomial, the left endpoint of the decreasing loss bracket and the right endpoint in \(L^4\). For \(14/L\) use the left endpoint upper bound. Bisect only if the full-cell proof has not passed, with failure asserted rather than discarding any cell. The resulting whole rays have strict margins:

| Start \(L\) | Margin |
|---:|---:|
|36.713|.001|
|36.717|.003|
|36.72|.004|
|36.737|.013|
|36.74|.014|
|36.793|.040|
|36.80|.043|
|36.88|.080|
|37|.137|
|37.042|.155|
|42.635|1|
|47.17|\(1+14/L\)|

For the first six rows, the new closed tests join at 36.72, 36.74 or 36.80, using the larger margins or retained bounds there and thereafter. The .043 test joins .08 at 36.88; the .08 test joins .137 at 37. The .137 and .155 tests join the two-sided bridge at 39.47, which extends to 40 and the original .370 ray. The last two tests join the earlier respective proofs at 42.65 and 47.25. The one-sided .85 over [39.32,39.47] is a bounded tradeoff only. Keep all earlier bounded margins, the exact low endpoint and its local and floor profiles. No constant \(>1\) is asserted on a whole ray. The maximum gives the compared margins/onsets, without claiming any are least possible.

## Ramanujan: new prime-count error and higher orders

Use the same \(\pi-\operatorname{li}\) identity and short-history bound as ramanujan.md. On \([100,v]\) the integral of \(V\) uses weights \(e^{\rho t}/t^2\). Since \(e^{\beta t}/t^2\) increases there for \(\beta\ge.78\), phase integration by parts gives
\[
 \left|\int_{100}^v e^{\rho t}/t^2\,dt\right|\le 2 e^{\beta v}/(\gamma v^2)
\]
(two endpoint amplitudes plus their difference). Sum absolutely by density. The resulting scaled endpoint and integral contribution is at most \(e^{-v/8}Z_*(v)(1+2/(H'v))\).

For the remainder, \(e^{7t/8}d(t)/t^2\) grows at rate at least \(1/4\) in the multiplicative sense: its value at \(u\le t\) is at most \(e^{-(t-u)/4}\) times its value at \(t\). For each non-bin term of both cutoff bounds, the exponential growth rate after multiplying is at least \(1/3\), losing at most \(2/t\) in powers. For bin tangent terms the rate is \(7/8-\kappa\alpha-(b-s_{i+1})\), with \(\alpha<2/3,\ b-s_{i+1}\le.075\), losing at most \(2/t\) in powers and \(q/(\kappa t^2(\alpha-q/(\kappa t)))<.01\) in the denominator. The latter bound is checked at 100 and decreases. For the second bin terms the exponential rate is at least \(7/8-2/5-.075\), again losing at most \(2/t\). Summing, then minimizing, preserves the growth inequality. This yields the new normalized \(\pi\) error
\[
 |r(v)|\le e^{-v/8}Q_*(v),\quad
 Q_*=(1+2/(H'v))Z_*+(1+4/v)d+3\cdot10^{-16}v e^{100-7v/8}\qquad(v\ge100).
\]
The last term is the original short-history bound rescaled. \(Q_*>0\) decreases. Include this choice for both error signs at their own arguments \(L,L-1\). This improves the pointwise envelope without discarding other branches.

Use also \(N=32\), \(A_N(v)=\sum_{i=0}^N i!/v^i\), \(U_N=A_N+3(N+1)!/v^{N+1}\). They strictly bracket \(F(v)=v e^{-v}\operatorname{li}(e^v)\) at \(v=69=2N+5\), with the same PV series and constant interval as in ramanujan.md, through degree \(6\cdot69\) and tail at most \(2\cdot69^{6\cdot69+1}/(6\cdot69+1)!\) by a geometric comparison. The ODE residuals have opposite strict signs for \(v\ge69\) since \(3(1-(N+2)/v)-1>0\). Form the analogous \(P_N(L)=\sum_{i=4}^{2N+2}a_iL^{4-i}\) by the positive expansion and exact upper square; \(a_i=C_i>0\) for \(4\le i\le N\), as checked by exact integers. Together with the rational variant this gives new pointwise gap profiles, e.g. for \(L\ge101\). Their loss with both errors bounded by the larger \(r_0=e^{-(L-1)/8}Q_*(L-1)\) is at most \(L^4 r_0[L/(L-1)+2U_N(L)+r_0]\).

Each R line after the anchor line in repair.out records \(k,c,a,j\) (exact means \(c=C_k\), half means \(C_k/2\)). It proves
\[
 G(L)>\sum_{i=4}^{k-1}C_i L^{4-i}+c L^{4-k}\quad(L\ge a).
\]
After multiplying by \(L^{j-4}\), the available reserve is at least
\[
 (C_k-c)L^{j-k}+\sum_{i=k+1}^j C_iL^{j-i}
 -\sum_{i>j,\ a_i<0}|a_i|a^{j-i}.
\]
This is weakly increasing. The scaled upper loss decreases by \(a>8j\) and decrease of the other factors when \(L^j\) is grouped with \(e^{-(L-1)/8}\); thus a directed proof at \(a\) suffices. Search just selects sufficient certificates. Keep the earlier order-16 quarter ray and others even if a particular onset is not advanced. In particular the exact order-31 and half order-32 profiles are new rays.

## Reproduction and remaining limits

Run PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 repair_cert.py from the submission directory. It uses the original 256-bit directed dyadic intervals, exact rational clipping, and exact comparisons (no printed floating value decides a sign). Tiny exponentials are rounded outward. Replay instructions for the new finite polynomial proof are in repair_poly.md. The original output receipts and branches are preserved. Neither Lean nor source-first PV is claimed.

The wider cutoff \(e^{2v/5}\) alone with two coarse density strips did not improve the medium spectral regime: the trial coefficient .035 at 130 failed, with product coefficient about .137 before taking the cutoff minimum and refining the chords. The common density cap, wider cutoff and combined mode transfer address different losses, and we retained the stronger pointwise branches rather than choosing one estimate globally. The limiting coefficient still reflects upper density estimates and absolute values, not direct knowledge of the spectrum at \(\beta=b\); no better exponent is proved. The Ramanujan quantitative bridge is limited by the end of the finite li sign and the loss from separate endpoint bounds. No independent check of the inherited large finite integer coverage or globally sharp margin is claimed.
