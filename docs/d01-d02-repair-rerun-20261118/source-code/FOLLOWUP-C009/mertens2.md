# Prime sums and Mertens products: D02 and original-input comparisons

For real \(x>1,\ L=\log x\), use the original constants of Dusart 2018 Theorems 5.6–5.7, original PDF pp.17–19:
\[
 D_1=\sum_{p\le x}1/p-\log L-M,\quad M=\gamma+\sum_p(\log(1-1/p)+1/p),
\quad D_2=\sum_{p\le x}(\log p)/p-L+B_3,\quad
 B_3=\gamma+\sum_{p,m\ge2}(\log p)/p^m.
\]
Let \(Z=\log Q_{\rm raw}-\gamma-\log L\); denote the two relative errors by \(E_P=|e^{-Z}-1|\) and \(E_Q=|e^Z-1|\). These are correlated outputs. The D01 floor, including every original direct/signed baseline, finite polynomial row, exact onset and spectral row, is retained. In particular include Dusart 5.6, 5.7 and 5.9, original PDF pp.17–20, not just an arbitrarily selected product estimate. Empty products and sums for \(1<x<2\) are exact.

## Explicit conclusions

In the following exponential rows the bound is **strict** \(ce^{-\alpha L}\) for \(|D_2|\), \(ce^{-\alpha L}/L\) for \(|D_1|,E_P,E_Q\), on the indicated real inclusive ray:

| Premises | \(\alpha\) | c | onset |
|---|---:|---:|---|
| B0 | 1/8 | .018865 | \(L=14\) |
| B2 | 1/8 | .0083 | \(L=14\) |
| B2 | 1/8 | .00145, .00120, .00100, .00070 | \(L=170,175,180,190\), respectively |
| B2 | 1/8 | .00049, .000090, .000018, .000000030 | \(L=200,250,300,500\), respectively |
| B2 | 5/32 | .290, .25, .20, .175 | \(L=171,204,314,519\), respectively |
| B2 | 5/32 | .15, .147, .1465 | \(L=3649,18933,63740\), respectively |

The fine-cap coefficients in extra2.out tighten the respective coarser choices in m2.out, and the pointwise functions below strengthen the rounded versions. At slope \(5/32\) we also have the following **exact real onsets** of non-strict whole rays (strict thereafter), where each root is characterized by equality with the indicated envelope. Decimal brackets are open; their upper endpoints are sufficient onsets including endpoints.

| error | root bracket for c=.29446 | root bracket for c=.29389 |
|---|---|---|
| \(|D_1|\) | (115.9567,115.9568) | (115.9899,115.9900) |
| \(|D_2|\) | (199.5221,199.5222) | (199.5729,199.5730) |
| \(E_P\) | (115.2993,115.2994) | (115.3334,115.3335) |
| \(E_Q\) | (115.8036,115.8037) | (115.8357,115.8358) |

This slope and these tiny onsets coexist because the exponent first gives a very generous bound in the small and moderate range, then becomes strong in the tail. The proofs do not assume the D02 inequality for small x. At c=.29389 the slightly later onsets buy a strictly smaller constant on the whole common domain. There are certified violations immediately to the left of each root; thus minimality is for those fixed bounds and the final whole ray, not for a different coefficient or functional shape.

Further strict log-power comparisons: the table's coefficient is for \(c/L^m\) for \(|D_2|\) and \(c/L^{m+1}\) for the other three.

| m | inclusive onset L | B0 c | B2 c |
|---:|---:|---:|---:|
| 3 | 61 | not asserted here | .0000051 |
| 4 | 57.6 | .00134 | .000851 |
| 5 | 55 | .253 | .144 |
| 6 | 52 | 48 | 24.3 |

At matched slope \(1/8\), more log factors are available. For any \(m\ge0\), if the pure-exponential table gives a D02-slope coefficient c from a, then on \(L\ge a\) the corresponding slope-\(1/8\) coefficient with \(L^{-m}\) for \(|D_2|\) and \(L^{-m-1}\) for the others is at most
\(c u^m e^{-u/32}\) with \(u=\max(a,32m)\). This follows by differentiation, including all possible interior maxima; it does not use a sampled crossover. For example for \(L\ge200\) one can use \(.098e^{-L/8}/L\) for \(|D_2|\) and \(.098e^{-L/8}/L^2\) for the others (use the independently checked .00049 same-slope coefficient and the monotonicity of \(Le^{-L/32}\)). The spectral comparison from \(L=200\) saves a factor greater than 20 relative to *every* reported B0 spectral coefficient function at slope \(1/8\), since those functions are at least their respective limits \(\ge .010443618317\), while \(.00049<.010443618317/20\). The D02 rounded .00049 branch also improves the inherited rounded plateaux and polynomial estimates there: \(e^{-L/8}\) and \(L^2e^{-L/8}\) decrease, and the strict comparisons hold at 200. For the strongest stated same-shape paired connected rays the fixed-onset comparison above is .0083 vs .018865 at \(L=14\). None of these statements equates a computed majorant with the actual error or declares it a globally optimal consequence of all originals.

## Whole-domain signed prescription

Retain all pointwise formulas of mertens.md and repair.md, including their finite-prime interval method, direct original estimates, and CH2 and \(\psi/\theta\) signed transfers on their exact domains. Strengthen the \(\psi\) intervals by intersecting with the new spectral bounds (both b choices when B2 is admitted) and the direct D02 interval only for \(v\ge200\); subtract the two distinct signed power corrections to get \(\theta\) intervals. Then use the inherited endpoint-minus-tail formulas for \(D_1,D_2,Z\), their separately signed integrals, and both \(e^{\pm Z}\) transformations. This operation can only narrow the existing intervals. One may also use the clipped inherited spectral path at .78 (spectral2.md). These instructions compare on *all* matched domains (take the pointwise min), including where a finite or CH2 branch beats a spectral bound. A strict comparison of two individual bounds does not imply their difference survives intersection with every other bound at every x.

For the new sharper path set \(S(v)=\sum_{n\le e^v}\Lambda(n)/n-(v-\gamma)\), \(\Phi(v)=\sum_{2\le n\le e^v}\Lambda(n)/(n\log n)-\log v-\gamma\). Define \(A_{\rm pp}=\psi-\theta\),
\[
 B(x)=\sum_{m\ge2,\,p^m>x}(\log p)/p^m,\quad C(x)=\sum_{m\ge2,\,p^m>x}1/(mp^m),\quad
 J(x)=\sum_{p>x}[-\log(1-1/p)-1/p].
\]
Partial summation, convergent corrections, and the Dusart normalizations give \(D_2=S(L)+B\), \(D_1=\Phi(L)+C\), \(Z=\Phi(L)+C-J\). In particular \(0\le C-J\le C\le B/L\); \(p>x\) implies \(p^m>x\). From \(-A_{\rm pp}(x)/x+\int_x^\infty A_{\rm pp}(t)t^{-2}dt\) and the signed power estimates,
\[
 0\le B\le(2\cdot 1.000000147-.9999)e^{-L/2}+(3/2)1.78e^{-2L/3}=:B^+(L)\qquad(x\ge121).
\]
Sharper signed intervals for \(B,C,J\) follow by the same partial summation with their respective decreasing kernels, as in mertens.md. Throughout, tails are \((x,\infty)\) and sums to x are right-continuous.

Apply to the relative \(\psi\) error the endpoint-minus-tail operators at \(L\), with endpoint factors \(1,1/L\) and tail weights \(1,w(v)=(v+1)/v^2\) for \(S,\Phi\), respectively. For example the \(S\) identity follows from partial summation and \(S\to0\) (use Dusart \(D_2\to0\) and \(B\to0\)); the \(\Phi\) identity follows from its convergent correction to Dusart \(D_1\). On high modes, the combined factor for \(S\) is \(-\rho/(1-\rho)\), cancelling the original \(1/\rho\). For \(\Phi\), write \(1/L=\int_0^\infty e^{-Lu}du\) and \(w(v)=\int_0^\infty(1+u)e^{-vu}du\); after combining it is \(-\rho\int_0^\infty e^{-Lu}/(1-\rho+u)du\). The resulting magnitudes of the high-mode contributions are at most \(e^{-\delta L}Z_b(L)\), \(e^{-\delta L}Z_b(L)/L\), respectively. All integrals are absolutely dominated by the density sum times the shaped exponential, so the exchanges are valid.

For the remainder, use \(d_i(v)\le d_i(L)e^{-\lambda_i(L)(v-L)}\) before taking minima. Put
\[
 Y_2=Z_b+\min\sum_i d_i(1+1/(\delta+\lambda_i)),\qquad
 Y_1=Z_b+\min\sum_i d_i(1+(1+1/L)/(\delta+\lambda_i)).
\]
Then \(|S(L)|\le e^{-\delta L}Y_2(L),\ |\Phi(L)|\le e^{-\delta L}Y_1(L)/L\) for \(L\ge100\). To \([-e^{-\delta L}Y_2,e^{-\delta L}Y_2]\) add the interval for B; to \([-e^{-\delta L}Y_1/L,e^{-\delta L}Y_1/L]\) add the respective signed intervals for C and \(C-J\). In the quick analytic bound use \([0,B^+]\), \([0,B^+/L]\). Intersect the resulting intervals with the inherited intervals. For any final signed interval \([\ell,u]\) for Z, use the **separate** relative envelopes \(\max(e^{-\ell}-1,1-e^{-u})\) for P, \(\max(e^u-1,1-e^\ell)\) for Q. This pointwise prescription is stronger than identifying the two product errors, and does not discard any stronger finite or exact signed choices.

For a simple common numerical certificate let \(c_i(L)=Y_i(L)+e^{\delta L}B^+(L)\), \(z=e^{-\delta L}c_1(L)/L\), bound the product coefficient by \(c_1(L)/(1-z)\) (since \(e^z-1\le z/(1-z)\) for \(0\le z<1\)). Each \(Y_i,c_i\) is nonincreasing; \(z<1\) at 100 and thereafter. Consequently the endpoint tests prove entire rays. Their limiting coefficient at the true power \(5/32\) is \(K_{b_2}\); the finer cap gives .146288736869 exactly in this expression, and the exact-integral version has the integral limit in spectral2.md, about .146288736864. The b0 versions have limits near .010443618318 at slope \(1/8\). These numbers are bounds, not asymptotic error constants. The D02 exponent improves that slope, and the \(\log^2 x\) in the hypothetical input is not carried through the final inequalities.

## Proof of connected Mertens rays and all finite joins

The CH2 Corollaries 1.2–1.3 (original PDF p.3) give \(|S(v)|\le A(v)=a+113.67e^{-v/2}\), \(a=1.048\cdot10^{-12}\). The important intermediate bridge uses an improved signed tail of \(S\), not a frozen plateau integral to infinity. For \(V\ge100\) let
\[
 {\cal T}_b(V)= e^{-\delta V}\left[\frac{2Z_b(V)}{H}
 +\min\sum_i\frac{d_i(V)(1+1/(\delta+\lambda_i(V)))}{\delta+\lambda_i(V)}
 \right].
\]
Then \(\left|\int_V^\infty S(v)v^{-2}dv\right|\le{\cal T}_b(V)/V^2\). Indeed after transferring the high modes to S their coefficients have denominator \(1-\rho\); integrate their phase once more against the decreasing \(e^{(\beta-1)v}/v^2\). Boundary plus variation gives a further \(2/\gamma\) factor. The expression for the remainder comes from the above rate bounds on the whole ray, freezing its weighted kernel by \(1/V^2\). On \(100\le L\le V\), partial summation also yields
\(\Phi(L)=S(L)/L-\int_L^\infty S(v)v^{-2}dv\), so use
\[
 |D_2|\le A(L)+B^+(L),\quad
 L\max(|D_1|,|Z|)\le A(L)(2-L/V)+L{\cal T}_b(V)/V^2+B^+(L).
\]
Use these even when not rounded to simple shapes. One can also replace the use of \(A\) under the integral by the pointwise min of all applicable bounds. This can give an improvement before the endpoint of a winning spectral branch via the improved tail, though at truly small x the finite interval often controls the full minimum. Different V choices remain valid everywhere they apply; take their min.

In m2.py testexp(), use \(V=168.7136\) or \(188.92\) with the coarse cap. With the fine cap, extra2.py gives \(V=168.7\) and \(188.909\). On \([100,V]\) the constant part of the bound after scaling by \(e^{\alpha L}\) is increasing (\(\alpha(2-L/V)>1/V\)); all exponential decays are bounded at 100 after scaling. For the scaling \(L^m\) in powjoin() the constant part is increasing (\(m\ge1\)); the decaying terms are decreasing since \(L>2m\). Before 100 but from the listed intermediate cutoff use the unrefined \(A(L),2A(L)\) bounds for \(|S|,L|\Phi|\) plus \(B^+\); split the constant and exponential parts as checked in m2.py, with cuts at 61,70,100 for the log powers. At \(V\) the tail checks already hold, and \(e^{(\alpha-\delta)L}\) or \(L^m e^{-\delta L}\) is then nonincreasing. Thus the table does not extrapolate a bounded grid past its tail. In the product conversion the added factors \(1/(1-z)\) are checked by explicit rational slack on these intervals.

For early exponential joins use the B0 signed \(\theta\) bound \(|E(v)|\le2.1e^{-v/2}\) on \([10,29.9]\) from CH2 Lemma 9.2 and the powers, and the finite-RH \(\theta\) bound \(v^2e^{-v/2}/(8\pi)\) on \([29.9,58]\) (PT finite RH original PDF p.4 Corollary 1 or PT 2021 PDF p.9 Lemma 6). Beyond 58, the inherited absolute theta integral is bounded by \(2.1\cdot10^{-10}\), from CH2 to 200 and the B0 QRH exponential thereafter. After 29.9 the corresponding total integral bound is \(2(29.9^2+4\cdot29.9+8)e^{-29.9/2}/(8\pi)+2.1\cdot10^{-10}\). In the \(w\)-weighted integrals on a tail, bound w by its initial value; for the changing weights below 29.9 the normalized factor is \(Lw(L)=1+1/L\). Also \(LJ\le2/(e^L-1)\) as in the floor. For \([10,29.9]\) the exponential terms in the scaled first interval are decreasing; the fixed tail contribution after scaling increases and is bounded at 29.9. The code tests the log-product bound \(<.01\) as slack. On \([29.9,58]\) the scaled polynomial times exponential terms decrease, and scale the fixed tail at 58. For the slope-\(1/8\) connected rows, instead use the inherited .28 polynomial from \(L=14\) through 17 and .10 from 17 to 29.9 (check onsets against the exact finite join receipts, then \(e^{L/8}/L^2\) has no interior maximum). Hence these branches also have no gaps.

For the D02 fast-exponent small onsets, small() enumerates all primes through 22030, and uses constant arithmetic values on each closed frozen prime cell, i.e. the right endpoint for this cell is evaluated *pre*-jump. The next cell includes the correct post-jump. In each cell the outward interval in L encloses the normalized errors for the *entire* cell including these conventions, not merely instantaneous checks at prime arguments. \(e^{10}<22030\) certifies overlap. The last potentially failing cells are (113,127) and (199,211); the latter for \(D_2\). In these cells roots() uses the fixed state and analytic monotonicity. For example the signed normalized \(D_1\) derivative, divided by \(e^{\delta L}\), is \((1+\delta L)D_1-1\); for \(D_2\) it is \(\delta D_2-1\). For \(E_P,E_Q\) use the signed expressions \(L e^{\delta L}(1-e^\gamma P_{\rm raw}L)\) and \(e^{\delta L}(e^{-\gamma}Q_{\rm raw}-L)\), with derivative factors \(1+\delta L-(2+\delta L)e^\gamma P_{\rm raw}L\) and \(\delta(e^{-\gamma}Q_{\rm raw}-L)-1\). In each case the signed normalized quantity strictly decreases, starts above c, ends inside \((-c,c)\), and crosses c in the stated bracket. The constants \(\gamma,M,B_3\) come from the inherited directed intervals, also replayed through \(10^7\) and their analytic tails by normalize_replay.py. A pointwise exact prime sum or product up to any tested cutoff is still used where stronger.

## What the input does not settle

Applying D02 as a pointwise magnitude on its own would give e.g. the weighted error bound
\[
 |S(L)|\le e^{-\delta L}\frac{L^2+L^2/\delta+2L/\delta^2+2/\delta^3}{64}\qquad(L\ge200)
\]
by an absolute endpoint-minus-tail estimate; for \(\Phi\) the tail integrates \((v+1)e^{-\delta v}/64\). These bounds are much larger than the new no-log-loss bounds on their entire input ray. Using this direct condition below \(e^{200}\) would be invalid. The analytically material use is the Mellin continuation and the resulting clipping. The early polynomial scan and original fixed-coefficient real endpoints do not directly improve through the pointwise input. The late integration tail can be tightened as above, but its effect cannot remove the actual prime-jump obstructions at the old coefficients documented by the inherited witnesses.

There is a boundary obstruction to improvements **at the new exact exponential power**. For example any \(|D_2|=o(e^{-\delta L})\) would also give \(S=o(e^{-\delta L})\) since the power tail is faster. For \(\Re z>0\), summation by parts yields
\[
 -\zeta'(1+z)/\zeta(1+z)=1/z-\gamma+z\int_0^\infty e^{-zv}S(v)dv .
\]
If \(S=o(e^{-\delta v})\), then at \(z=-\delta+\epsilon+i\gamma_*\) the integral times \(\epsilon\) tends to zero as \(\epsilon\downarrow0\): truncate at a fixed point, then use the \(o(1)\) bound on the rest and \(\epsilon\int_0^\infty e^{-\epsilon v}dv=1\). This contradicts the pole if there is a zero on the boundary at ordinate \(\gamma_*\). The same reasoning applies to improving any of the other three bounds to \(o(e^{-\delta L}/L)\): after removing the faster prime-power and reciprocal corrections it gives \(\Phi=o(e^{-\delta L}/L)\), and \(S(L)=L\Phi(L)+\int_L^\infty\Phi(v)dv\) by the inverse partial summation. Thus improving the log power at exact \(\delta=5/32\), or increasing that exponential power, would demand boundary exclusion. Neither B0's nor D02's stated strip excludes its boundary. This is a mathematical bottleneck, not a claim that boundary zeros exist.

Optimizing the density by replacing the crude tangents with exact integrals and refining the common cap led to the fine/exact-integral branches. FKS (2.13) suggests a further small logarithmic density refinement, but the necessary unrounded auxiliary data for an independently optimized tuple are not all printed in the allowed sources; no such change, or use of the second Table 8 block, is made. Near the CH2 plateau/exponential crossover an attempt with the coarse .294 coefficient and the early whole ray fails the sufficient join inequalities; shortening the tail by phase and using the finer cap gave the stronger c=.29389 result. These are bounding-function tests, not proofs of best possible constants. The finite and small-error B0 discoveries are separate from the D02 treatment gains.
