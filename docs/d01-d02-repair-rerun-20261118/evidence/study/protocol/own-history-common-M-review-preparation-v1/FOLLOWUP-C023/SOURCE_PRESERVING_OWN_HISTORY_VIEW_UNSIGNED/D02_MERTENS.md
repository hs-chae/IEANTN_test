# Mertens products and two prime sums: full envelope and explicit rays

Use real x≥2, L=log x and products/sums over p≤x, inclusive. Let
\[
 P=\prod_{p\le x}(1-1/p),\quad Q=1/P,\quad Z_Q=\log Q-\gamma-\log L,
\]
\[
 D_1=\sum_{p\le x}p^{-1}-\log L-M,\qquad
 D_2=\sum_{p\le x}(\log p)/p-L+B_3.
\]
Here \(\gamma\) is Euler's constant, \(M=\gamma+\sum_p[\log(1-1/p)+1/p]\) and \(B_3=\gamma+\sum_p\log p/[p(p-1)]\), as in Dusart2018 Thms.5.6–5.7 (PDF pp.17–19). The two normalized relative errors are \(E_Q=|e^{-\gamma}Q/L-1|\), \(E_P=|e^\gamma L P-1|\); neither is defined by dividing by the *other* product's error scale.

## New uniform rays

Each row below holds on its entire subsequent **closed** real ray. The coefficient K bounds \(E_Q,E_P,|D_1|\) in units \(L^{-3}\) and \(|D_2|\) in units \(L^{-2}\).

| log onset | K | premises |
|---:|---:|---|
|59.99|4.27e-8|B0|
|60.15|4e-8|B0|
|60.34|3.75e-8|B0|
|60.855|2.9873e-8|B0+D02|
|171|2.16e-8|B0+D02|
|172|1.86e-8|B0+D02|
|176.18|1e-8|B0+D02|
|180|5.59e-9|B0+D02|
|184.2|3e-9|B0+D02|
|191.5|1e-9|B0+D02|
|200|2.79e-10|B0+D02|

Thus, for example, at the inherited L=74 onset 3.8e-8 becomes 2.9873e-8, and 4.3e-8 at L=64.4 is beaten already with B0 at L=59.99. The first three rows are improvements from the B0 proof work, not from the contract. Keep earlier original and D01 rays, finite steps, and nonuniform analytic caps, for instance the stronger finite-π signed interval where available. The new common K=2.9873e-8 proof pays for the finite log segment through the CH2-to-density join, not just the short domain where CH2 itself is decreasing in units \(L^{-3}\).

The following are pure power rays under B0+D02. The coefficient K is now in units \(x^{-5/32}/L\) for \(E_Q,E_P,|D_1|\), and \(x^{-5/32}\) for \(|D_2|\).

| log onset | K | log onset | K |
|---:|---:|---:|---:|
|169|.300102|1000|.162328|
|170|.298321|2500|.152450|
|190|.269799|10000|.147651|
|200|.259244|100000|.146183|
|250|.225620|1000000|.146038|
|400|.188868|5000000|.146025|
|600|.173283| | |

B0 secondary: .010443 in the corresponding units with exponent −1/8 from L=5000000. Larger displayed coefficients in different exponential units are not directly comparable by their magnitude. At L≥169, .300102 \(e^{-L/32}\) is <.01044 and decreases, so the D02 power radius strictly beats **all the displayed frozen inherited B0 power rays on their common domains**, including the stronger far B0 coefficients. The same argument works for the inherited nonuniform power-coefficient formulas here: their nonnegative parts include the final density weight >.01044. The result also agrees with the matched clipping comparison in D02_PROOF.md. Moreover for all L≥200 the endpoint ψ coefficient is <.260 in units \(e^{-5L/32}\) instead of the unprocessed input \(L^2/64\); the zero-density step drops two powers of L relative to simply transferring the assumed pointwise inequality.

To spend some of the new power gain on an extra log factor, one may use the smaller exponent d' and p≥0: use \(K x^{-d'}/L^{1+p}\) for the three reciprocal/product outputs and \(K x^{-d'}/L^p\) for the weighted sum. For example, the certified tuples (log onset, d', p, K) are
\[
 (200,9/64,1,2.279),\quad (400,1/8,2,.11262),\quad
 (500,1/8,3,3.668),\quad (600,1/8,3,.26928).
\]
These follow from bounding the decreasing factored coefficient at the onset and then using the decrease of \(L^p e^{-(5/32-d')L}\) for \(L\ge p/(5/32-d')\). They are alternate shapes, not inherently stronger than the unfrozen power envelope.

## Pointwise signed proof

Write \(Z=e^{-L/2}, C=e^{-2L/3}, X=e^{-L}\), \(w_1(v)=(v+1)/v^2\), \(w_2(v)=1\), \(v_j=L^{2-j}\), \(q_j=|w_j'(L)|/w_j(L)\). Set \(\alpha=.000000147,\ \epsilon=.0001,\ \eta=1.78\). Dusart Prop.4.3 and Cor.4.5 (PDF pp.12–13) give
\[
 (\psi-\theta)(e^L)e^{-L}=Z+\xi(L),\qquad -\epsilon Z\le\xi(L)\le\alpha Z+\eta C
\]
on L≥18. Stieltjes partial summation, or Dusart's exact formulas in the two theorem proofs, yields
\[
 D_j=d_\theta(L)/v_j-\int_L^\infty d_\theta(v)w_j(v)dv .
\]
The \(-Z\) part of \(d_\theta\) contributes \(B_1(L)=\tfrac12\int_L^\infty e^{-v/2}dv/v\) or \(B_2(L)=Z\), respectively; \(Z/(L+2)\le B_1\le Z/L\) (exponential mean 2 and convexity, or the integral directly). These biases are signed, not another endpoint absolute loss. The lower and upper residuals from \(-\xi(L)/v_j+\int\xi w_j\) are
\[
 -\frac{\alpha Z+\eta C}{v_j}-2\epsilon w_j(L)Z,qquad
 \frac{\epsilon Z}{v_j}+w_j(L)(2\alpha Z+1.5\eta C).
\]
They use \(w_j(v)\le w_j(L)\). All integrals are absolutely convergent.

The ψ tail after integration is bounded by
\[
 I_j=w_j(L)\Big[.0463(1+2q_j/14)Z+
  (1+2q_j/H)\min(J_d(L),3.2\cdot10^{-12})e^{-dL}+2X\Big].
\]
Indeed integrate against the primitive \(U_\psi\) from D02_PROOF.md and integrate once more per exponential mode for the term \(\int_L^\infty U_\psi w_j'\). If \(w_j\) is not constant, \(w_j''\ge0\) and \(\int_L^\infty w_j''=|w_j'(L)|\). The two resulting terms together cost at most \(2|w_j'(L)|/|1-\rho|\) times the original zero bound at L, by one boundary evaluation and the integral. For w=1 there is no such loss. Bound the trivial contribution by integrating the elementary nonzero term of Dusart (2.1) absolutely, at most \(2w_j(L)X\). The zero sums being integrated are absolutely convergent (moment k=2 and the low sum). This gives the stated I_j, including the smaller high-ordinate estimate and its precise factor L.

Use any original/D01/D02 signed interval \([a_-,a_+]\) for \(d_\psi\) valid at L; for example intersect the two new leaves in D02_PROOF.md, and retain the CH2 asymmetric interval at exact height H. Then a signed interval of \(D_j\) follows by adding \(B_j\), \([a_-,a_+]/v_j\), the signed ξ interval above and \([-I_j,I_j]\). Also intersect directly with any signed D_j from the old floor (finite transfers, exact finite steps and analytic bounds) and lawful B0 originals. The new high term may replace the old at any eligible log, but never forces a weaker envelope.

**Alternative local weighted endpoint.** Let \(D_\Lambda=\sum_{n\le x}\Lambda(n)/n-L+\gamma=d_\psi(L)-U_\psi(L)\). To see the identity, the finite partial summation formula uses \(\int_0^L d_\psi\), and \(\int_0^\infty d_\psi=-\gamma-1\) by the pole expansion in the proof of (S1) (equivalently, take the limit using the fast-decaying endpoint and the weighted Mertens constant). Use the explicit CH2 Cor.1.2 weighted endpoint at height H (and any other valid signed \(D_\Lambda\) bounds). For D2 use \(D_\Lambda+B_2-\xi+\int \xi\), with **no** primitive debit. For D1 use \(D_\Lambda/L+B_1-\xi/L+\int\xi w_1\), plus the error
\(-U_\psi(L)/L^2-\int_L^\infty U_\psi(v)w_1'(v)dv\).
If an absolute primitive cap is a positive sum \(S(L)=\sum c_a e^{-aL}\) as in D02_PROOF, this last error has absolute bound
\[
 S(L)/L^2+|w_1'(L)|\sum_a c_a e^{-aL}/a.
\]
This uses only decreasing \(|w_1'|\) and exact exponential integrals. Intersect both signed constructions: whenever the weighted endpoint is helpful, its primitive has one extra logarithmic denominator for D1. This is a distinct pointwise transfer, not an assertion that every argument selects it.

**Prime-power log correction and reciprocal errors.** The exact identity is
\[
 Z_Q=D_1-T_1,\qquad T_1=\sum_{p>x,k\ge2}(k p^k)^{-1}.
\]
For L≥18 retain the proven strict interval \(.470X/L<T_1<.502X/L\) and the stronger available pointwise enclosure using \(I=\int_x^\infty dt/(t^2\log t)\), as in mertens_repair.md. More explicitly, if \(\kappa(x)\) bounds \(|\theta(t)/t-1|\) on t≥x, use \([I/2-a/2,I/2+a/2+(I+a)/(3(x-1))]\) with \(a=3\kappa(x)/(xL)\). At L≥40 the new d-dependent θ cap is decreasing and supplies an eligible \(\kappa\); take the minimum with the other eligible caps and intersect the tail intervals. These bounds follow from Stieltjes partial summation on the open-at-x interval (x,∞), and the geometric majorant of the powers k≥3. For any resulting interval \([l,u]\) on \(Z_Q\), the two errors are bounded by
\[
 E_Q\le \max(e^u-1,1-e^l),\qquad E_P\le\max(e^{-l}-1,1-e^{-u}).
\]
This preserves signs and the distinction between reciprocals. It is stronger than forcing a single symmetric log radius wherever one side is already well-controlled.

Finally one can integrate any eligible full-ray D1 envelope \(|D_1(e^v)|\le A(v)\) to improve D2, irrespective of whether the symmetric D2 bound for that point uses a different source:
\[
 |D_2(e^L)|\le L A(L)+\int_L^\infty A(v)dv.
\]
Indeed \(dD_2=v\,dD_1\) for the Stieltjes differentials, and the end term at infinity is zero by the old Dusart bounds. Use the **minimum** of eligible D1 leaves before integrating, including all original and finite steps and the new ones. Each finite step may be integrated exactly; if the last piece starts at B and uses the new power tail, \(\int_B^\infty A(v)dv\le K e^{-dB}/(dB)\). In particular the earlier weighted transfer never worsens, and its integral component is strictly reduced whenever replacing a larger old bound by the new one on a positive-length subset of its integration domain. This is not a new square-root sign assertion.

## Entire-domain proof of the tables

For L≥40 the above signed identities imply a single common radius \(E(L)\) for \(L|D_1|,L|Z_Q|,|D_2|\). With \(k=1+1/L\) use
\[
 E=\Psi+(1+.0003+.048k)Z+
 k\{2.67C+(1+4/(HL))J_d(L)e^{-dL}+2X\}+.502X,
\]
where \(\Psi\) is either or the minimum of \(q+C_TZ\), \(F_d(L)e^{-dL}\). The .0003 coefficient bounds the two signed square-root ξ costs because \(k\le19/18\); for cube terms use \(1.5\eta k=2.67k\). The ψ weight factor uses \(q_1\le2/L\), so the low ψ coefficient is <.048. Here \(L B_1\le Z\). The product errors are ≤\((E/L)/(1-E/L)\) if \(E/L<1\). The tables use this safe bound; the pointwise envelope keeps the exact exponential conversion.

With the power choice of \(\Psi\), write \(E=U_0(L)e^{-dL}\). Each term of \(U_0\) is nonincreasing on L≥40; so \(U=U_0/(1-U_0e^{-dL}/L)\) decreases after positivity of the denominator at the onset. A single directed check proves each power row. For the pure-power log rows additionally use decreasing \(L^2 e^{-dL}\) on L>2/d. For the first log rows split [A,∞) at B=168.901 (D02) or 189.13 (B0). On [A,B] use the plateau version of E. The numerator \(L^2 E\) is convex: expand into nonnegative combinations of \(L^j e^{-aL}\) with j=0,1,2 and \(a\ge d\), plus \(qL^2\). The second derivative sign of each exponential-polynomial term follows from \((aL-j)^2-j\ge0\) on L≥43.7. Use the maximum of its endpoint values and a lower bound for the denominator at A (unscaled \(E/L\) decreases). On [B,∞) use the decreasing power choice in log units. This proves all joins, including B itself.

The within-method B0 interval at L=188 has symmetric radius in normalized log units larger than \(188^2 q>3.7009\cdot10^{-8}\): both B0 eligibility leaves for \(\Psi\) there are ≥q, verified with a **lower** bound on its spectral cap (not on the prime error). The strict logarithmic improvement at 60.855 is therefore not obtainable just by running that same B0 plateau-to-power calculation for the D02 target. The failed 2.9871e-8 sufficient trial with the specified join and the close left/right upper checks locate that method's near-169 crossover. Neither experiment is a counterexample for the actual errors. More generally the bottleneck for an even faster power or another factor of 1/L at fixed exponent 5/32 in these *unrecentered* outputs is the local spectral term, not the small integrated tail. Removing the admissible closed-strip boundary contribution would need new information about zeros or actual phase cancellation. The explicit log-power exchange above does not assume a narrower strip.

## Auxiliary arithmetic and positivity (kept separate)

For real y≥3 let \(N_y=\prod_{p\le y}p\), \(V_y=Q(y)/(e^\gamma\log\theta(y))\), here put L=log y. The old B0 positivity and margin remain. The new B0 calculation extends \(V_y-1>.1e^{-L/2}/L\) to L≤85.7, and D02 to L≤86.99. On \(84.5\le L\le86.5\) the D02 margin is .35 in the same units, and on \([84.5,86.75]\) it is .23. Also \(V_y>1\) up through L=87.15 under D02. For y=2 up to the next prime retain the old meaningful unnormalized inequality \(Q(y)>e^\gamma\log\theta(y)\); no positive-relative normalization is used with negative denominator.

In fact, with \(t=d_\theta(L)\),
\[
 \log V_y=\left[t/L-\log(1+\log(1+t)/L)\right]
 -\int_L^\infty d_\psi(v)w_1(v)dv
 +\int_L^\infty (\psi-\theta)(e^v)e^{-v}w_1(v)dv - T_1.
\]
The bracket is nonnegative by successive \(\log(1+u)\le u\) (the arguments are valid for y≥3). Use the convex tangent to \(w_1\) to bound the positive prime-power integral below by \(.9999w_1(L)(2-4q_1)Z\), and the decreasing weight to bound it above by \(w_1(L)(2.0000003Z+2.67C)\). In units Z/L on [84.5,B], lower-bound the positive term with \(k\ge1\) and the decreasing q at 84.5; for the high negative bound use \(J_d(B)e^{(1/2-d)B}\) because the unfactored rates are ≤.30. Bound decreasing multiplicative and low/trivial contributions at 84.5. The computed positive margin for \(\log V_y\) implies the same strict margin for \(V_y-1\). Failed positivity lower checks near 87.2 are diagnostics of this primitive method, not sign changes.

For the far ray \(L\ge A\), the next two numbers strictly bound \(1-V_y\) and \(V_y-1\) in units \(y^{-5/32}/L\), respectively:

| A | negative-side coefficient | positive-side coefficient |
|---:|---:|---:|
|170|6.063e-14|1.91e-13|
|180|5.785e-14|8.234e-14|
|190|5.554e-14|6.022e-14|
|200|5.361e-14|5.451e-14|
|210|5.196e-14|5.213e-14|
|230|4.931e-14|4.931e-14|
|400|4.005e-14|4.005e-14|
|1000|3.470e-14|3.470e-14|

For these rows \(|t|<10^{-12}\); the bracket in log V is at most \(.50001(1+1/L)t^2/L\). This follows by applying \(0\le z-\log(1+z)\le z^2/[2(1-|z|)]\) first to t, then to \(\log(1+t)/L\), using \(|\log(1+t)|\le |t|/(1-|t|)\). For the negative side omit both nonnegative terms and pay the ψ integral and T, and use \(1-e^{-z}\le z\). For the positive side add the prime-power upper integral and local quadratic term, and omit T; use \(e^z-1\le z/(1-z)\). All factored functions decrease as above, including the local square term after one exponent is factored out; the endpoint checks therefore prove the entire rays.

For general **integer** \(n\ge N_{e^A(1+3\varepsilon)}\), \(\varepsilon=10^{-12}\), both \(n/\varphi(n)\) and \(\sigma(n)/n\) are strictly less than
\[
 e^\gamma\log\log n\left(1+
 K(1+5\varepsilon)^{5/32}
 \frac{(\log n)^{-5/32}}{\log\log n-\log(1+5\varepsilon)}\right)
\]
with A and its **positive** K from the last table. Indeed \(\theta(u)/u\in(1-\varepsilon,1+\varepsilon)\) on u≥e^170, so \(\theta(u(1+3\varepsilon))>\theta(u)\). This supplies a prime strictly after u and no later than the displayed upper argument. Let \(N_y\) be the largest primorial ≤n, y its last prime. Then y≥e^A by the threshold and this prime gap bound. The factor ratios are at most Q(y) by decreasing \(p/(p-1)\) and the bound on the number of distinct prime factors; \(\sigma(n)/n\le n/\varphi(n)\). Moreover \(\theta(y)\le\log n<\theta(p_{\rm next})<(1+5\varepsilon)y\). Substituting in the primorial result proves the claimed inequality. This is a correlated arithmetic application, not separate evidence for the analytic premise.

## Envelope and scope

Use at every x≥2 the minimum of all eligible inherited and original absolute intervals and the new ones, intersecting signed intervals first when applicable, then converting the product logarithm separately in each direction. If x<e^18 the new ψ/ξ branch is not used; the original floors and exact finite envelopes remain. The original-source formulas and their precise domains are indexed in comparison.md (Dusart Thms.5.6–5.9 plus their proof inequalities, CH2 finite/analytic, PT, FKS original theorems and tables, and the finite RH leaves). The weak headline Dusart constants aren't treated as the sole original comparison. No globally optimal envelope over all conceivable B0 proofs or sign on an infinite ray is claimed.
