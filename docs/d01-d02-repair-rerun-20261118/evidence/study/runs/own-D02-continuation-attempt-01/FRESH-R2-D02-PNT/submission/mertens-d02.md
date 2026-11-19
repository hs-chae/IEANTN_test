# Products and prime sums: D02 and B0 frontiers

All the inherited results in mertens-proof.md and repair.md remain applicable. Define \(L=\log x\), \(P=\prod_{p\le x}(1-1/p), Q=1/P,\ W_1=\sum_{p\le x}1/p,\ W_2=\sum_{p\le x}(\log p)/p\), using real \(x>1\) and right-continuous counting. The four errors, in this order, are
\[
 E_1=|e^\gamma LP-1|,\ E_2=|e^{-\gamma}Q/L-1|,\quad
 E_3=|W_1-\log L-M|,\ E_4=|W_2-L+B_3|.
\]
Here \(M=\gamma+\sum_p(\log(1-1/p)+1/p)\) and \(B_3=\gamma+\sum_p\log p/[p(p-1)]\) as in Dusart Theorems 5.6–5.7 (PDF pp. 17–19). No normalization switch. The two reciprocal products and the two sums are correlated consequences.

For each D02 row \((B,C)\), **strictly**
\[
 E_j<Cx^{-5/32}/L\quad(j=1,2,3),\qquad E_4<Cx^{-5/32}
 \quad (L\ge B).
\]
The B0-only rows have the same statements with \(x^{-1/8}\) instead. All endpoints are included. Use the minimum of applicable entries, not an extrapolation of any row to an earlier point.

| \(B\) | D02 \(C\) | B0 \(C\), new independent secondary result |
|---:|---:|---:|
|13|.262|.015|
|170|.258||
|175.1|.25||
|180|.243|.0141|
|181.1||.014|
|190|.231||
|200|.221|.01277|
|210|.213||
|225|.202|.01167|
|250|.189|.01092|
|300|.173|.00995|
|350|.162|.00935|
|420|.153|.00882|
|600|.141|.00810|
|1000|.130|.00750|
|2000|.122|.00705|
|10000|.1166|.00673|
|100000|.11563|.006671|
|1000000|.115568|.006668|

In particular the B0 secondary result gives the inherited .0196 margin from \(L=13\), not just 193, and the inherited .014 margin from 181.1 rather than 350. It is not a baseline blind run. The conditional power row at \(L=200\) is smaller than the improved B0 row there by a factor \(>.01277 e^{200/32}/.221>29\) (the ratio formula applies throughout their overlap). That comparison is between proved margins, not true errors or every possible numerical estimate at that point.

## Signed whole-domain envelope and proof

Use the exact normalized transforms from mertens-proof.md:
\[
 D(L)=E(L)-\int_L^\infty E(v)dv,\qquad
 Z(L)=E(L)/L-\int_L^\infty E(v)(1/v+1/v^2)dv.
\]
Their definitions are \(D=\sum_{n\le x}\Lambda(n)/n-L+\gamma,\ Z=\sum_{2\le n\le x}\Lambda(n)/(n\log n)-\log L-\gamma\). The signed deviations of \(W_2,W_1,\log(e^{-\gamma}Q/L)\) are \(D+B(x),Z+A_*(x),Z+A_*(x)-C_*(x)\), with
\(B=\sum_{p^j>x,j\ge2}\log p/p^j,\ A_*=\sum_{p^j>x,j\ge2}1/(jp^j),\ C_*=\sum_{p>x,j\ge2}1/(jp^j)\).
Keep the inherited analytic and exact finite bias bounds unchanged; use the finite cap-free bias table from repair.md through \(L=22\). They do not require unsettled interpretations of the normalized CH2 finite calculation. Optional normalized CH2 may still be intersected at its inherited trust only.

In the signed interval calculations replace the old \(J\) by \(J_b\) from spectral-proof.md. For the pointwise \(\psi\) boundary let \(-p_-\le E(L)\le p_+\) use the tightest original signed bound and all applicable new spectral shapes (including the basic, split and symmetric variants plus the direct D02 bound when valid); keep all old weighted CH2 bounds and the identity \(Z=D/L-\int_L^\infty D(v)dv/v^2\). Specifically the new radii before weighted CH2 intersections are
\[
 d_\pm=p_\pm+J_b+1.84e^{-L},\qquad
 z_\pm=\bigl[p_\pm+(1+1/L)J_b+1.84e^{-L}\bigr]/L .
\]
Add the signed bias intervals before computing radii (use the integer-telescoping upper bound on \(C_*\) from the inherited proof). For log-product interval \([\ell,u]\), the \(P,Q\) relative-error radii are respectively \(\max(1-e^{-u},e^{-\ell}-1)\) and \(\max(e^u-1,1-e^\ell)\). This is a pointwise envelope, valid also at prime jumps: only the integrated explicit formula uses the mid-value, and that convention changes no integral. Tail integrals and normalization are justified in the inherited proof and spectral-proof.md. The B0 version replaces \(b_2\) everywhere by \(b_0\), omits the direct D02 leaf, and is otherwise identical.

For the power tables write \(g=1-b\), and use any positive spectral shape \(\Phi\) for \(|E(L)|\). On all the numerical tail starts \(B\) (including both joins), the guard \(\exp(B/2)>767135587\) and Dusart Theorem 4.2 give \(K=.5/(B/2)^3<.001\) for the normalized \(\theta\) error above \(\exp(B/2)\). With the inherited bias bound, \(0\le B(x)\le1.002e^{-L/2}+2.67e^{-2L/3}\) on these rays; also \(0\le A_*-C_*\le A_*\le B(x)/L\). Set
\[
 U(L)=e^{gL}\left[\Phi(L)+(1+1/L)J_b(L)+1.84e^{-L}
                     +1.002e^{-L/2}+2.67e^{-2L/3}\right].
\]
For the first three errors (using the log error first for the products) the unexponentiated magnitude is at most \(Ue^{-gL}/L\); for the fourth use \(Ue^{-gL}\). If \(Ue^{-gL}/L<1\), use \(e^t-1\le t/(1-t)\) for \(0\le t<1\). Thus a common scaled bound is \(U/(1-Ue^{-gL}/L)\).

For the chosen spectral shape test that \(e^{gL}\Phi(L)\) is nonincreasing from \(B\). Organize terms by common rate \(r\) and polynomial origin \(a\); translate the resulting polynomial to \(L=B+y\) and write \(P_0+P_1 y+P_2 y^2\). The scaled derivative is its exponential times
\[
 (P_1-(r-g)P_0)+(2P_2-(r-g)P_1)y-(r-g)P_2y^2 .
\]
Test \(B\ge a,\ r\ge g\), and the first two coefficients \(\le0\) (the last is automatic). All other terms of \(U\) decrease or are constant; hence the exponentiation guard and bound follow on the whole ray from a single interval evaluation of this monotone expression at \(B\). For huge \(B\) evaluate the **scaled** modes directly before exponentiation (no underflow assumed exact). This also proves the claimed .221 bound on the actual \(\psi\) boundary for \(L\ge200\); \(U\) majorizes its scaled magnitude.

For \(13\le L\le173\) (D02) and \(13\le L\le193\) (B0), finite_m checks the first row by exact interval arithmetic on covering cells; it uses the cap-free signed intervals and, for \(L\ge112\), can use the same absolute exponentiation bound on a whole cell with the CH2/selected-spectral minimum. Its simplified \(K<.001\) guard already holds at 112. Split at all needed noninteger boundaries in the implementation, in particular 29.9; options requiring a domain are used only on contained cells. Both closed finite covers join their respective tail at a common endpoint. This proof is not a point sample. Before \(L=13\) keep all original, clipped-cell and other inherited bounds (for \(1<x<2\) the raw values are exact). On the full real domain take the intersection of valid signed branches, and/or the minimum of applicable separate absolute bounds. The finite sieve data and neighboring fixed-margin obstruction witnesses in the inherited portfolio remain valid; no D02-only improvement of those numerical endpoints is claimed.

## Bottlenecks and controls

Direct absolute integration of the input alone illustrates the distinction: for \(g=5/32,\ L\ge200\) it gives \(|D|\le e^{-gL}[(1+1/g)L^2+2L/g^2+2/g^3]/64\), \(|Z|\le e^{-gL}[(1+1/g)L+1/g+1/g^2]/64\), before bias. These follow by integrating the displayed powers in the kernels. Our spectral projection and integrated-zero bounds remove two log powers compared with that route. The transfer back from any stronger power for one of the four errors is also useful: power corrections are \(O(x^{-1/2})\) here. If an error were \(O(x^{-b'}(\log x)^k)\) with \(b'>5/32\), take a logarithm near 1 in the product cases to recover the corresponding signed transform. Multiplying its Stieltjes measure by \(t\) or by \(t\log t\), and integrating by parts, gives \(\psi(x)-x=O(x^{1-b''})\) for any \(5/32<b''<\min(b',1/2)\). For precision, differentiating the main term \(L-\gamma\) or \(\log L+\gamma\) after multiplication gives \(dt\); in the boundary and integrated error terms the multiplier and its derivative cost at most \(x\) times a fixed log power, which is absorbed by the strict choice of exponent. The log-derivative identity forces exclusion of zeros on a strictly larger half-plane. We do not have that exclusion or prove it impossible.

The early D02 common-power rows .306, .268, then .262 were improved by low-zero splitting, symmetry, and the independent Dusart logarithmic density bound. A .261 whole-ray trial still fails the sufficient test around \(L=168\), where the CH2 floor and the cap-weighted spectrum compete. For B0 a .01495 whole-ray trial fails at 13 in the signed fourth-error branch; that failure is not a violation of the actual prime-sum inequality. Neither failure removes an inherited bound. Eventual constants are limited here by positive upper mass on the terminal band (and the smaller integrated contribution), not by a lower bound on the true error. Section comparison.md gives all-domain comparisons and crossovers, in particular a strict gain against the complete explicit retained original-input frontier at \(L\ge200\).
