# Ramanujan gap: D02 and separate original-input improvements

Let \(L=\log x,\ R(x)=(ex/L)\pi(x/e)-\pi(x)^2,\ G(L)=L^6R(x)/x^2\). All log onsets in this file are real and inclusive unless explicitly indicated. A strict bound on \(G\) is a strict bound on \(R\) by multiplying by \(x^2/L^6>0\). Retain the complete validated D01 floor, which here needs only B0. In particular the final strict-positivity ray is \(x>x_*\), with \(x_*=38358837682+\xi,\ .21792<\xi<.21794,\ R(x_*)=0\); this is independent of D02. See ramanujan.md and the review for the exact equation, finite integer trust, and the local derivative bound. We do not use the false literal real lower endpoint of PT Theorem 2. The included literature baselines are Dudek–Platt (PDF p.2 Thm 1.2; finite proof pp.8–10) and PT 2021 (PDF p.3 Thm 2; p.9 Lemma 6), and all applicable direct \(\pi\) and Chebyshev bounds are retained.

## Main results and comparison

Write
\[
 C_j=\sum_{i=0}^j i!\binom ji-\sum_{i=0}^j i!(j-i)!,\qquad
 T_{k,c}(L)=\sum_{i=4}^{k-1}C_i L^{4-i}+cL^{4-k}.
\]
Thus \(T_{6,c}=1+14/L+c/L^2\), \(C_6=145,\ C_7=1412\). Selected strict **connected** rays are:

| Assumptions | Onset L | Lower bound on G |
|---|---:|---|
| B0 | 47.15 | \(1+14/L\) |
| B0 | 47.6 | \(T_{6,8}\) |
| B2 | 48 | \(T_{6,40}\) |
| B2 | 49.2 | \(T_{6,80}\) |
| B2 | 49.6 | \(T_{6,80.25}\) |

These are not merely tail estimates starting at their analytic-cutoff joins. The finite-to-tail proofs are below. The small-L segments of each B2 result need only B0, but the B2 estimates fill the late part of the connection. In particular it is not correct to describe the onset 48 as extrapolating the assumed pointwise \(\psi\) bound down to \(e^{48}\).

For the higher-order profile keep **every certified row** of higher2.out, compare2.out and order192.out. The latter certifies exact order 191 from \(L=5276.87\) in B2 versus \(7010.70\) in B0, and half of degree 192 from \(5285.44\) versus \(7020.08\), with the same ray proof. The latter refines selected onsets to hundredths of a log unit. Some matched real onsets (exact order means \(c=C_k\)):

| Profile | Reconstructed B0 | B2 |
|---|---:|---:|
| \(T_{6,97.5}\) | 199.63 | 171.33 |
| exact 6 | 221 | 186.97 |
| exact 7 | 253.59 | 211.74 |
| exact 8 | 288.82 | 237.68 |
| exact 16 | 574.57 | 450.91 |
| exact 31 | 1121.98 | 860.85 |
| exact 32 | 1158.96 | 888.66 |
| exact 64 | 2334.57 | 1768.99 |
| exact 127 | 4654.81 | 3510.03 |
| \(k=128,c=C_{128}/2\) | 4665 | 3519 |

At fixed L use the maximum of all applicable profiles, not a sequence chosen at samples. For example compare2.out evaluates the coefficient of \(L^{-2}\) above \(1+14/L\) in the same \(P_{48}\) model with the available signed plateau and QRH refinements and then the D02 spectral model. It is enclosed in \([77.026,77.027]\) versus \([88.227,88.228]\) at 170, and \([62.201,62.202]\) versus \([118.838,118.839]\) at 175 (these are enclosures of *lower bounding functions*, not of the true coefficient). Use the receipt as authoritative to a grid unit if a paired number is on a last-place rounding boundary. At L=165 the plateau wins both in that comparison. Pointwise strict improvement of the clipped spectral formula is proved in spectral2.md, symbolically for all its valid arguments. Intersecting error intervals and maximizing lower gap profiles is non-worsening on every matched domain, even where D02 is not the winning branch. This B0 reconstruction is not an independent blind run, and an earlier certified onset is not asserted least possible.

## Prime-counting transfer and exact pointwise profiles

Use the principal-value normalization in Dusart §5.1, original PDF pp.13–14. Put \(r(v)=v e^{-v}[\pi(e^v)-\operatorname{li}(e^v)]\), \(F(v)=v e^{-v}\operatorname{li}(e^v)\), and \(E(v)=\theta(e^v)/e^v-1\). Partial summation gives
\[
 r(v)=E(v)+v e^{-v}\left(\int_{\log 2}^v e^t E(t)t^{-2}dt+
  2/\log 2-\operatorname{li}(2)\right).
\]
In the bracket the past through 100, pre-multiplied by \(e^{-100}\), has absolute value \(<3\cdot10^{-16}\) by the B0 short-history check in ramanujan.md and cert.py density(). On \([100,v]\) use spectral2.md. For \(\beta\ge.70\), \(e^{\beta t}/t^2\) is increasing there. Integration by parts in the phase gives
\[
 \left|\int_{100}^{v} e^{\rho t}t^{-2}dt\right|
 \le 2e^{\beta v}/(\gamma v^2).
\]
The boundary terms and variation give this bound, and summation is justified by the absolute density estimate. This gives the high contribution \(e^{-\delta v}(1+2/(Hv))Z_b(v)\). For the remainder, for any rate \(\mu>0\) in spectral2.md, the integral of \(e^{bt}d_i(t)/t^2\) on this interval is \(\le e^{bv}d_i(v)/(v^2\mu_i)\). Take each cutoff fixed while integrating, then minimize. The powers in \(p(t)\) after \(e^t/t^2\) have growth rates \(>1/4\), so
\[
 |r(v)|\le e^{-\delta v}Q_b(v),\qquad
 Q_b(v)=(1+2/(Hv))Z_b(v)+\min\sum_i (1+1/(\mu_i v))d_i(v)
 +(1+4/v)e^{\delta v}p(v)+3\cdot10^{-16}v e^{100-bv}.                \tag{3}
\]
All terms decrease in v after normalization, and \(Q_b\to K_b\). On the positive side of r one can instead *subtract* \(.9999e^{(\delta-1/2)v}\) in place of the positive power term: the \(\theta-\psi\) contribution to the integral on \([100,v]\) is nonpositive. One can integrate the signed corrections themselves before bounding, or use the clipped inherited spectral and other old signed estimates. The smaller of valid bounds is used separately at \(v=L-1\) and \(v=L\); in particular no upward extrapolation of a shifted source's finite domain is made.

For any established two-sided error endpoints \(-r_-(v)\le r(v)\le r_+(v)\), define \(A_N(v)=\sum_{i=0}^N i!v^{-i}\), \(U_N=A_N+3(N+1)!v^{-(N+1)}\). The following strict lower profile uses both arguments:
\[
 G(L)> L^4\left\{\frac{L}{L-1}A_N(L-1)-U_N(L)^2\right\}
 - L^4\left\{\frac{L}{L-1}r_-(L-1)
       +(2U_N(L)+r_+(L))r_+(L)\right\}.                          \tag{4}
\]
It follows from the strict barriers for F (and positivity of the upper bound used in squaring). Retain the rational expression and its cancellation-safe polynomial variant \(P_N\) below. Alternatively one may use exact F in (4), with a **non-strict** bound if both F endpoints are exact. Intersect the B0 and B2 signed error estimates before using the profile, wherever valid. One-sided finite comparisons use \(r_+(L)=0\) only at the non-shifted point from the reported finite \(\pi(x)<\operatorname{li}(x)\) result (Dusart original PDF p.15 proof of Thm 5.1, \(x<1.39\cdot10^{17}\); also Dudek–Platt proof of Lemma 3.2 for its smaller interval).

## Factorial barriers, remainder and ray certificates

\(e^{-v}\operatorname{li}(e^v)\) satisfies \(y'+y=1/v\). After substituting \(A_N/v,U_N/v\) the residuals lie strictly below and above \(1/v\) for \(v\ge2N+5\): the upper residual's excess is \([3(1-(N+2)/v)-1](N+1)!/v^{N+2}>0\). Use ODE comparison from the certified initial values \(A_N(v)<F(v)<U_N(v)\) at \(v=2N+5\). The anchor uses the PV expansion \(C+\log v+\sum_{j\ge1}v^j/(j\,j!)\), \(C\in[-1,1]\) by the integral argument in ramanujan.md. After degree \(6v\) the tail is \(\le 2v^{6v+1}/(6v+1)!\). Higher precision at \(N=128\) is essential; divide the scaled numerator by \(e^v\) in one operation (not by multiplying a separately rounded tiny reciprocal). These are directed tests, not asymptotic assumptions.

By the positive binomial expansion of \(LA_N(L-1)/(L-1)\), discarding terms of degree greater than \(2N+2\) in \(1/L\), and exactly squaring \(U_N\), get \(P_N=\sum_{i=4}^{2N+2}a_i L^{4-i}\). Coefficients \(a_0,\ldots,a_3\) vanish and \(a_i=C_i\) for \(4\le i\le N\). Code checks with exact integers. All \(C_i>0\) for \(i\ge4\): divide by \(i!\), use \(\sum_\ell1/\ell!\ge 1+1+1/2+1/6+1/24\), and bound the reciprocal binomial sum by \(2+2/i+2(i-3)/(i(i-1))\le 8/3\).

For any row \(a,N,k,j,c\) of the certificate, \(a\ge101,2N+6\), \(a>8j\), and \(k\le j\le N,\ 0\le c\le C_k\). Freeze normalized error factors in (3) at a and a-1, using the last base not exceeding that argument and the rational upward rounding in Q. For \(L\ge a\), after multiplying the cost in (4) by \(L^{j-4}\) the resulting positive expression decreases: it is \(L^j e^{-\delta L}\) times a nonincreasing positive bracket. Against it use the nondecreasing expression
\[
 (C_k-c)L^{j-k}+\sum_{i=k+1}^j C_i L^{j-i}
              -\sum_{i>j,\ a_i<0}|a_i|a^{j-i}.
\]
A strict directed test at a therefore gives the full ray. The rescaled exponential is evaluated as \(\exp(j\log a-\delta a)\), avoiding underflow. Bisection proposes onsets only; the final assertion and this monotonicity prove them. Nothing restricts formal order to 128: for a fixed N the ODE gives the leading positive remainder \((N+1)!/v^{N+1}\) asymptotically, by splitting its exponential convolution at \(v/2\) and dominated convergence on the last half. Thus one can search for a later anchor using arbitrarily precise certificates; the same ray test with \(j=k+1\) eventually succeeds for any fixed k. The orders in the receipts through degree 192 are the ones actually computed, not claims of optimal truncation.

## Closed-interval joins and secondary B0-only results

In joins2.py the cells through 58 use early2.py. Its improved history starts at \(v=10\), with absolute historical contribution \(<2020\) by the finite-RH estimate up to there and the inherited short-history argument. On \([10,29.9]\), CH2 Lemma 9.2 (original PDF pp.35–36) and the powers give \(-2.1e^{-t/2}\le E(t)\le-.2089e^{-t/2}\). Integrate the lower magnitude using growth \(e^{t/2}/t^2\) at rate at least .3. The positive history is therefore \(\le2020\) and the negative is \(\le2020+7e^{29.9/2}/29.9^2\) at 29.9. From 29.9 to 58 accumulate signed upper integrals in width-\(.02\) cells including the cut 33.3. Use finite-RH theta or CH2 Cor 1.3; from 33.3 also use CH2 Cor 1.2 (p.3), at \(T=m\,2\pi^2 e^{t/2}/t\), \(m=1,1.1,1.17,1.25\), with domains checked at the endpoints. Here \(\pi\) in constants is the circle constant. The center of that result is between 1 and \(1+\pi^2/(3T^2)\) after relative normalization, so omit its correction on the negative side, add it on the positive side. Subtract the signed powers on the correct side. In each cell bound the entire coefficient multiplying \(e^{-t/2}\) by interval arithmetic and multiply the integral kernel \(e^{t/2}/t^2\) by its safe endpoint bound. For a requested v use the history to the next cell endpoint as an upper bound; the cumulative bounding integrals are nonnegative. The gap cost is bounded on the entire outer cell using the two shifted r arguments, decreasing scalar factors, and \(L^4\) at the upper endpoint. Apply interval Horner to the polynomial or continued test. If an interval cannot certify the sign, bisect or fail, never delete it.

From 58 through each finite-to-tail join use grid() with the scaled coefficient \(L^{k-4}P_N\) after subtracting the early exact terms. Use each signed term at its monotone extremum on the full cell. A shorter B0 plateau for \(v\ge100\) splits the past CH2 convolution at \(w=v-20\): use the inherited history bound \(2a/w^2+345e^{-w/2}/w^2+2000000e^{-w}\) scaled by \(v e^{-20}\), with \(a=1.048\cdot10^{-12}\); on \([w,v]\) the constant and \(e^{-t/2}\) errors have unscaled growth at least \(1-2/w,\ 1/2-2/w\) in the integral. The code's resulting factors all decrease with v. Also freeze \(Q_b\) at 168,188 when helpful and applicable at the actual shifted argument. The endpoints 166,170,171 in the B2 rows and 191 in the B0 row are included in both the finite and ray certificates. Thus there is no missing finite slice. The \(1+14/L\) row from 47.15 joins the inherited 47.17 row.

Other B0 strict whole rays from the early checks, paired with the inherited intervals at their joins:

| onset | margin | connection |
|--:|--:|---|
|36.688|.001|new .003, then .004|
|36.692|.003|new .004|
|36.694|.004|inherited .004 at 36.72|
|36.712|.013|inherited .014 at 36.74|
|36.715|.014|inherited .014 at 36.74|
|36.772|.040|new .043|
|36.780|.043|inherited .043 at 36.88|
|36.863|.080|at 37 joins .137 (inherited or new)|
|36.98|.137|new two-sided bridge via .163|
|37.02|.155|same .163 bridge|
|37.05|.163|both sides of 39.47, then retained .370 at 40|
|42.615|1|inherited 42.65|

Bounded B0 tradeoffs include \(G>.885\) over \([39.46,39.47]\); \(G>1.305,\ 1.31,\ 1.32\) respectively on \([48,55.5],[49,54],[50,52]\); exact order 6 on \([54,124]\) and exact order 7 on \([58,88]\). Bounded rows are not advertised as whole rays. The small-\(x\) B0 window in mid2.py proves \(G>.01,.12,.28,.50,.69,.85,1,1.06\) on intervals with respective starts \(28,28.2,28.5,29,29.5,30,30.6,30.9\), all ending at 30.93. Use \(N=10\), anchor at \(v=25\), the same finite sign at x, and \(x/e<10^{13}\) for CH2's signed error. The short history is anchored at \(x=10^4\) with \(\pi(10^4)=1229\), \(\theta\) by trial division and log enclosures, and \(\pi(10^4)-\operatorname{li}(10^4)-(\theta(10^4)-10^4)/\log(10^4)>-6.28\). From \(\log10^4\) through 19.3 integrate \(-E\le2.14e^{-v/2}\) at growth .28 in the unscaled kernel; after 19.3 use \(-E\le1.83e^{-v/2}\) and rate \(1/2-2/19.3\). This explains signloss(). A uniform rounded positive margin across its gap up to 36.688 is not established by this method; the inherited *strict positivity* is connected through all of it.

## Limitations

Using D02 directly in the late prime-counting convolution gives a log-squared coefficient term, uniformly much worse than (3) on \(v\ge200\). Trying to merge disconnected exact-sixth windows via the plateau alone fails near its maximum normalized loss; D02 makes a materially larger connected partial sixth coefficient possible, but not an unbroken c=145 connection from 54. Raising a constant gap margin above 1 on an entire ray is impossible by \(G\to1\), not by sampling. For the normalized \(\operatorname{li}\)-gap approximation, an improvement of the **two-sided** remainder to \(o(L^4e^{-\delta L})\) would imply \(r(L-1)-2r(L)=o(e^{-\delta L})\) by (3) and \(F(L)=1+O(1/L)\). The bounded normalized error then satisfies a contracting recurrence with coefficient \(e^\delta/2<1\), hence \(r=o(e^{-\delta L})\). Partial summation back to \(\theta\) would give \(\psi(x)-x=o(x^b)\), excluding zeros on \(\Re s=b\) by the Abelian argument in mertens2.md. This is not an impossibility assertion for one-sided lower bounds; the boundary is simply not excluded by the available zero-strip input. Reducing losses near the earliest positivity onset calls for finer finite counts or a substantially sharper signed local majorant, not the tail input.
