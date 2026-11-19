# Integrated explicit formula, signed Mertens bounds, and primorial consequences

This strengthens the fixed-cutoff integral in mertens.md. It uses the same premises and conclusions about zeros as candidate.md, and assumes no new numerical zero location beyond those admitted. It supplies a signed error interval useful alongside the simpler absolute envelopes. In particular it gives a finite range of strict positivity at primorials, as well as a smaller symmetric far-ray bound.

## 1. Derive the absolutely convergent primitive

Put \(f(t)=e^{-t}\psi(e^t)-1\) for \(t\ge0\), and \(U(t)=\int_t^\infty f(u)du\). This exists by the power estimate (candidate.md). The following formula is exact for every \(t\ge0\), including logs of prime powers:
```
U(t) = −∑_ρ exp((ρ−1)t)/(ρ(1−ρ))
       − log(2π) exp(−t) + ∑_{m≥1} exp(−(2m+1)t)/(2m(2m+1)).      (S1)
```
Here and below multiplicities are included. No interchange of the conditionally convergent unsmoothed explicit formula with an improper integral is required.

**Source and proof.** Use CH2 Eq. (B.9) (PDF p.46, proof of Prop. B.8, an original-paper citation of the partial fraction formula), CH2 functional equation (A.2), PDF p.41, and the first positive zero ordinate >14 stated in CH2 Appendix B.1, PDF p.43. The reciprocal-zero estimate of PT Lemma 2 shows \(\sum_\rho |\rho|^{-2}<\infty\): for γ>100, write \(1/\gamma^2=\gamma^{-1}\int_\gamma^\infty u^{-2}du\), and apply that estimate after Tonelli. Finitely many smaller zeros contribute finitely and the real axis has no nontrivial zeros as explained in candidate.md. Thus series for (S1) converge absolutely and uniformly for t≥0; all zeros satisfy β≤7/8 and γ is bounded away from 0.

Here are the local expansions involved. For Re z>0, the digamma relation
`digamma(1+z) = −γ+∑_{m≥1}(1/m−1/(m+z))`
follows by differentiating Gauss's limit \(\Gamma(v)=\lim n!n^v/[v(v+1)\cdots(v+n)]\). For completeness, the finite expression is \(\int_0^n u^{v-1}(1-u/n)^n du\) by repeated integration by parts, and converges to the gamma integral uniformly on compacta of Re v>0 by domination by \(u^{\operatorname{Re}v-1}e^{-u}\). Holomorphic differentiation gives the displayed series as well as \(\Gamma'(1)=-\gamma\). The identity extends wherever both sides are holomorphic, in particular limits as z→0 and z=.5. The finite harmonic odd-even split gives \(\operatorname{digamma}(3/2)=2-2\log2-\gamma\).
Also \(\zeta(1+z)=1/z+\gamma+O(z)\): after subtracting the pole, use the locally uniformly convergent sum \(\sum_{n\ge1}[n^{-s}-\int_n^{n+1}u^{-s}du]\) near s=1 and its telescoping value there. In the functional equation, the polar and constant parts of \(\Gamma(1-z)\zeta(1-z)\) are \(-1/z+0\); expansion gives \(\zeta(z)=-1/2-(\log2\pi)z/2+O(z^2)\). Hence \(\zeta'/\zeta(0)=\log2\pi\). Evaluating (B.9) at zero gives its constant \(C=\log2\pi-1-\gamma/2\).

For real s>0 let z=s+1. Euler product differentiation and elementary summation (absolute convergence) yield the Laplace transform \(\Phi(s)=\int_0^\infty f(t)e^{-st}dt=-\zeta'(z)/(z\zeta(z))-1/s\). Insert (B.9) and the digamma series:
```
Φ(s)= −∑_ρ 1/[ρ(z−ρ)] − log(2π)/z + ∑_{m≥1} 1/[2m(z+2m)].
```
This holds also at s=0 by dominated convergence on the integral, and uniform absolute convergence of the displayed series near s=0. By Fubini the transform of \(U\) is \([\Phi(0)-\Phi(s)]/s\). Termwise subtraction on the right shows this is exactly the transform of (S1). For elementary uniqueness, the difference is a continuous function tending to zero, as is clear for both sides. Substitute y=e^−t, and use s=1,2,...: the continuous difference on [0,1] integrates to zero against every polynomial, hence against itself by uniform polynomial approximation. It is identically zero. This avoids a contour truncation or any hypothesis about convergence of unsmoothed zero sums near jumps.

A second use of (B.9), at s→1 after removal of the pole, gives
\[
\sum_\rho\frac{1}{\rho(1-\rho)}=2+\gamma-\log(4\pi)<.0463.
\]
Indeed \(\zeta'/\zeta(s)=-1/(s-1)+\gamma+O(s-1)\), and the explicit constant and digamma(3/2) above give the identity. Each summand has positive real part since \(\operatorname{Re}(\rho(1-\rho))=\beta(1-\beta)+\gamma_\rho^2>0\). For \(|\gamma_\rho|\le H=3\cdot10^{12}\) the zero is critical-line and the summand is positive real. Its absolute sum over the finite-height region is therefore <.0463. The numerical constant is checked using Machin's identity and the elementary harmonic/trapezoid bound for Euler's constant in mertens.md. The trivial-zero sum minus the pole term in (S1) has absolute value ≤2e^−t: \(1<\log2\pi<2\), and the trivial sum is nonnegative and ≤(1/2)e^−3t.

## 2. High-ordinate weighted coefficient

The powers of H in this argument are essential. PT Lemma 2 gives \(2\sum_{\gamma_\rho>H} \gamma_\rho^{-2}<160/H\) by the integral above, since for u≥H the both-sign reciprocal sum is at most \((\log u)^2/6+2\). For \(\beta\ge s\), apply FKS Corollary 2.9 as in candidate.md, but now
`H · 2∑_{γρ>H, β≥s} γρ^−2 ≤ 4H ∫_H^∞ N(s,u)du/u³`.
Put z=log H, r=(8s−5)/3, q=5−2s. The bound after substitution is
```
4[c exp(−r z) z^q ∑_{j=0}^4 q(q−1)...(q−j+1)/(z^j(1+r)^(j+1))
  + d exp(−z)(z²/2+z/2+1/4)].
```
To see this, use the quartic Taylor upper bound for \((1+h)^q\) (3<q<4, fifth derivative negative), integrate each monomial against \(e^{-(1+r)u}\), and integrate the second coefficient's degree-two polynomial exactly. The argument and input constants retain the original FKS Table 8 trust. smooth.py gives the directed rational upper weights \(w_j^{(2)}\) with running minima on the same mesh as candidate.md. Define
\[
G(t)=160e^{-.175t}+w_m^{(2)}+
     \sum_{j=0}^{m-1}(w_j^{(2)}-w_{j+1}^{(2)})e^{(s_{j+1}-.875)t}.
\]
Using the staircase as before (and separately β<.70), the high-ordinate terms of (S1) have absolute value ≤ \(G(t)e^{-t/8}/H\). This improves on blindly dividing the pointwise coefficient F(t) by H. It gives \(G(190)/H<4.49\cdot10^{-15}\) and \(G(400)/H<3.20\cdot10^{-15}\) (the checker supports the associated rounded bounds in Section 4).

## 3. Signed Mertens/local errors

For \(L\ge8\), use either w(t)=1 (write q=0) or w(t)=(t+1)/t² (q=(L+2)/(L(L+1))). In both cases q=|w'(L)|/w(L). Then
```
S(L,q)=.0463(1+2q/14)e^(−L/2)
       +(1+2q/H)G(L)e^(−L/8)/H + 2(1+q)e^(−L).
J−(L,q)=.9999(2−4q)e^(−L/2),
J+(L)=(2(1+1.47e−7)+2.67e^(−L/6))e^(−L/2).
```
The signed integrals satisfy
`|∫_L^∞ Dψ(t) w(t)dt| ≤ w(L) S(L,q)`
and
`w(L) J− ≤ ∫_L^∞ (ψ(e^t)−θ(e^t)) e^−t w(t)dt ≤ w(L) J+`.
Proof of the first assertion: integrate by parts against U; the term U(L)w(L) is bounded via (S1). For each zero term in \(\int U(t)w'(t)dt\), one further integration by parts bounds it by its absolute contribution envelope at L times \(2|w'(L)|/|1-\rho|\), since \(w''\ge0\) and \(\int_L^\infty w''=|w'(L)|\). Here \(|1-\rho|\ge14\) in the low group and \(\ge H\) in the high group. For the remaining terms the bound 2e^−t gives the factor 1+q. Everything integrated is absolutely summable. For the second assertion, use Dusart Prop. 4.3 and Cor. 4.5; the upper uses w(t)≤w(L), and the lower integrates the tangent lower bound \(w(L)+w'(L)(t-L)\) (w is convex) against \(.9999e^{-t/2}\).

Set \(d_x=(\theta(x)-x)/x\); for E1 and Z use the nonconstant w, and for E2 use constant w. The following endpoints apply to the centered quantities of mertens.md:
```
E1 ∈ d_x/L + w(L) [ J−−S, J++S ],
Z  ∈ d_x/L + [ w(L)(J−−S)−e^−L, w(L)(J++S) ],
E2 ∈ d_x   + [ J−−S, J++S ].                                      (S2)
```
These enclosures follow from the tail identities and the correction sign, not an independence assumption. They yield a standalone absolute envelope by taking \(|d_x|\) bounded by the pointwise minimum of \(D+116e^{-L/2}\) (valid already L≥8), \(L²e^{-L/2}/(8\pi)\) if L≤58 (PT), and \(F(L)e^{-L/8}+(1+1.47e-7)e^{-L/2}+1.78e^{-2L/3}\) (L≥40). In particular, a simple such envelope for \(|E1|\) is \(D_\theta/L + w(L)(J_++S)\) where \(D_\theta\) denotes that nonnegative majorant. Use \(D_\theta+J_++S\) for \(|E2|\) (q=0) and \(\exp(D_\theta/L+w(L)(J_++S)+e^{-L})-1\) for both product errors. Take pointwise minima with mertens.md (which includes the original baselines). This makes the new result never worse on the full common domain, and supplies useful independent signed information. E.g. at all 110≤L≤190, the constant-dominated reciprocal-sum envelope drops from approximately 2D/L to at most 1.01D/L, as the nonnegative additional contributions at 110 (with scaling by L) are <.01D and decrease thereafter. This dominance can also be verified by monotonicity with smooth.py.

## 4. Primorials: a positivity interval and sharp far-ray coefficients

Write \(n_y=\prod_{p\le y}p\) and \(V_y=Q(y)/(e^\gamma\log\theta(y))\) for y≥3 (so denominator positive). Then
```
V_y − 1 > .10 /(√y log y)         for 3 ≤ y ≤ exp(84.5).
Q(y) > e^γ log θ(y)              for 2 ≤ y ≤ exp(84.5).
```
For L≥190:
```
−4.6e−15 y^(−1/8)/L < V_y−1 < 1.5e−14 y^(−1/8)/L.
|V_y−1| < 4.6e−15 y^(−1/8)/L      for L≥215;
|V_y−1| < 3.22e−15 y^(−1/8)/L     for L≥400.                      (S3)
```
There is no all-ray sign claim.

For the positivity range, subtract \(\log(1+\log(1+d_x)/L)\) from Z. Its removal leaves the local quantity \(d_x/L-\log(1+\log(1+d_x)/L)\), which is nonnegative by two applications of log(1+u)≤u. The lower bound in (S2) then gives the positivity margin by scaling by \(L e^{L/2}\). The exact finite interval checks at L≥8 use decreasing q and increasing \(G(L)e^{3L/8}\); the latter is a nonnegative sum of exponentials with positive rates. All certificate cells use whole-cell endpoint bounds. For 3≤y<e^8 an independent exact sieve through 3000 checks each prime endpoint (both Q and θ are constant until the next prime, while the required lower margin decreases). At y∈[2,3) the second assertion is trivial since θ=log2<1. 

For L≥190 one additionally has \(|d_x|<10^{-12}\), and the local term is at most \(.50001(1+1/L)d_x^2/L\): sum the absolute remainders \(d-\log(1+d)\) and \(L[u-\log(1+u)]\), \(u=\log(1+d)/L\), using \(0\le z-\log(1+z)\le z^2/[2(1-|z|)]\). Insert \(|d_x|<P e^{-L/8}\) with P=.01955. This leaves the monotone scaled negative and positive coefficients in smooth.py, using the signs of the local term and the prime-power bias. Exponentiation for the positive side uses \(e^b-1\le b/(1-b)\); the negative side uses \(e^{-b}-1\ge-b\). All coefficient terms decrease after the applicable endpoints. Thus (S3) is a whole-ray result, not asymptotic notation.

For a general integer n≥ \(n_{\exp(216)}\), factorization and the short-interval result imply the following simultaneously for \(n/\varphi(n)\) and \(\sigma(n)/n\):
\[
\text{ratio}< e^\gamma\log\log n\left(1+
4.6\cdot10^{-15}\,(1+10^{-12})^{1/8}
\frac{(\log n)^{-1/8}}{\log\log n-\log(1+10^{-12})}\right).
\]
To check it, take largest primorial N_k≤n with largest prime y; there are at most k prime factors counted distinctly, and p/(p−1) decreases. Thus n/φ(n)≤Q(y), and σ(n)/n≤n/φ(n). The threshold ensures y≥e^215 (a prime occurs before e^216 by the short-interval result). Also log n<θ(p_{k+1})≤y(1+.06 y^−1/8)≤y(1+10^−12) by that same gap and the θ bound. Now apply (S3) and compare log log N_k≤log log n, using the displayed upper bound on log n to replace y. With threshold \(n_{\exp(401)}\), the coefficient 4.6 may be replaced by 3.22. The positivity and smaller error coefficients improve the earlier primorial comparison in arithmetic.md rather than assume sign from an asymptotic.

Reproduce with /usr/bin/python3.10 -B smooth.py. All comparisons use directed rational bounds; diagnostics in floating point are not inputs. No self-contained proof of the original partial fraction expansion is claimed; its exact location and form are given above.
