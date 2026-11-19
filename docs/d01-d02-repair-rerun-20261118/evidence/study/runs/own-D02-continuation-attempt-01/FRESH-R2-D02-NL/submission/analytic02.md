# Analytic engines for both families

Let \(u=\log x,\ v(u)=e^{-u}\psi(e^u)-1,\ D=\psi-\theta,\ P_\theta=e^{-u}D(e^u),\ \eta=v-P_\theta\). Write \(B_0\) for the exact seven-paper input and \(B_2=B_0+\)INPUT_CONTRACT.json. Use cap \(b=7/8\) or \(27/32\), respectively, and \(c=1-b\). All decimals are exact rationals. The old engines and source locators in common.md are retained.

## The use of D02

On \(\Re s>1\) the absolutely convergent Euler product and partial summation give
\[
 -\zeta'/\zeta(s)=s\int_1^\infty\psi(t)t^{-s-1}dt
 =s/(s-1)+s\int_1^\infty(\psi(t)-t)t^{-s-1}dt.
\]
Under D02 the last integral converges locally normally for \(\Re s>27/32\): on compacta the part above \(e^{200}\) is bounded by a constant times \(t^{-1-\epsilon}\log^2 t\), including additional log factors on differentiation. The omitted finite segment is entire. Uniqueness of meromorphic continuation excludes any zero there, since the logarithmic derivative would have a nonremovable simple pole. It does **not** exclude boundary zeros. For \(B_0\) use OpenAIQRH Thm. 1.1, PDF p. 4, not full RH. Thus D02 acts even below \(e^{200}\) by changing the cap in the explicit formula; the pointwise D02 bound itself only applies on its stipulated ray. D02 implies D01 there since \(x>1\); common.md also derives D01 from \(B_0\), and every validated D01 theorem is retained.

## Endpoint majorants

Use FKS Thm. 3.2 PDF p. 8, parameters \((40,1/2,0,2.091)\) of common.md, with \(T=e^{.47u}\), \(u\ge100\). The admissibility \(\max(51,u)<T,\ 5T+2<e^{u/2}\) holds at 100 by directed rational checks and monotonicity thereafter. The error is at most \(2.091u e^{-.47u}\). For \(s\ge .75\) the zeros with \(\beta\le s\) give at most \(.036u^2e^{-(1-s)u}\), by Platt–Trudgian 1809.03134v2 Lemma 2 PDF p. 4, \(T\le T^*\le2.45T<2\pi T\), and \(\pi>25/8\). The others have \(|\gamma|>H=3\cdot10^{12}\) by 2004.09765v1 Thm. 1 PDF p. 2. There are no real nontrivial zeros, by positivity of the alternating Dirichlet series for real \(0<s<1\).

Let \(B(s)=2\sum_{\beta>s,\gamma>H}1/\gamma\), with multiplicities. Use FKS Cor. 2.9 (2.17), PDF p. 7, Table 8 p. 26 (the .77 block), i.e. \(N(s,t)\le c_1 t^{1-d}\log^r t+c_2\log^2t,\ d=1-8(1-s)/3,\ r=5-2s\). Use right limits in t. Also **Dusart Thm. 2.3, PDF p. 5** gives
\[
 N(s,t)\le t\log(1+(4.9/t)(3t)^{1-d}\log^r t)+51.5\log^2t
 \le 4.9\,3^{1-d}t^{1-d}\log^r t+51.5\log^2t
\]
for \(s\ge.52,t\ge2000\). Taking the smaller integrated bound is particularly helpful near both caps, a \(B_0\) improvement over the inherited density calculation. No use of the improved .618 subconvexity coefficient.

Partial summation (the restricted count vanishes at H by finite RH and \(N(s,t)/t\to0\)) gives twice the integral of either density majorant against \(dt/t^2\). With \(\lambda=\log H\), the explicit bound is
\[
  2c_1 H^{-d}\lambda^r d^{-1}
 \sum_{k=0}^4\frac{r(r-1)\cdots(r-k+1)}{(d\lambda)^k}
 +2c_2H^{-1}(\lambda^2+2\lambda+2).
\]
Indeed substitute \(t=He^y\) and use the fourth Taylor polynomial of \((1+y/\lambda)^r\), an upper bound for \(y\ge0,\ 3<r<4\) by the negative fifth derivative. The code bounds \(\lambda,\log\lambda,\log3\) by directed rationals.

For a grid \(s=s_0<\cdots<s_n=b\), use nonincreasing upper bounds \(B_i\) at \(s_i\) for \(i<n\) (minimum with all preceding bounds, since \(B\) is decreasing), and \(B_n=0\). The positive contribution from \(\beta>s\) is at most
\[
 \sum_{i=0}^{n-1}(B_i-B_{i+1})e^{-(1-s_{i+1})u}.
\]
Bound \(\exp((\beta-1)u)\) by its slab's right end and telescope the exact differences \(B(s_i)-B(s_{i+1})\). After collecting the original \(B(s_i)\) all weights are nonnegative. This includes \(\beta=b\); the final slab is geometrically refined. Add the low-zero and Perron terms. Grid starts .75 or .80, steps .001 or .0025, are used in the evidence. The coarser positive layer branches are also retained: on each threshold segment \([s,t]\) use constants dominating every relevant FKS row in (1) of common.md. Its log slope magnitude is at most \(M\) from slope(s) in density.py. The integral for that segment is bounded by \(B_t u e^{-(1-t)u}/(u-M)\), extending it to infinity in the distance from the right endpoint; for the lowest segment this also covers the initial term at s because \(u/(u-M)>1\). Here \(B_t\) bounds the same majorant at t. All branch domains and \(u>M\) are enforced. No truncation varying with u is integrated in this argument.

## An exact integrated explicit formula

Use Dusart (2.1), PDF pp. 3–4, in symmetric-height order at non-prime-powers; the halfway convention at jumps is immaterial only for integration. Let \(I_w(L)=\int_L^\infty w(u)v(u)du\) for \(w=1\) or \(w=k(u)=(u+1)/u^2\). On a fixed compact interval of positive u, the inner product of two functions \(e^{(\rho-1)u}\) is \(O(1/(1+|\gamma-\gamma'|))\), by integrating the oscillatory phase once. The number of ordinates in each unit bin n is \(O(\log(2+|n|))\) by Dusart Thm. 2.2 PDF pp. 4–5 or CH2 Lemma B.1. With the reciprocal rho coefficients, the double sum of these bounds is finite. For comparable positive absolute bin indices the inner sum is \(O(\log^2(2+n)/(1+n))\) times the outer \(O(\log(2+n)/(1+n))\). For \(|m|>2|n|\), summing in n gives \(O(\log^3(2+|m|)/(1+|m|)^2)\). Opposite signs only enlarge the ordinate distance. Hence the height sums converge in compact \(L^2\); a subsequence converges almost everywhere by choosing summable squared errors and using Chebyshev. Dusart's explicit formula identifies the limit. Compact integrals are termwise valid.

For \(a=\rho-1\), integration by parts gives
\[
 \left|\int_L^\infty w(u)e^{au}du\right|
 \le w(L)e^{(\beta-1)L}|a|^{-1}
 \begin{cases}1 & (w=1),\\1+4/(L|\gamma|)&(w=k).\end{cases}
\]
For k integrate the derivative term by parts again: \(-k'\) is positive decreasing and its integral has absolute bound \(2|k'(L)|e^{(\beta-1)L}/|a|\); \(|k'|/k\le2/L\). On finite \([L,A]\) the once-integrated bound with 2 instead of the bracket is uniform in A. Absolute summability with two ordinate denominators then justifies the limit of the integrated series to infinity. The trivial/pole correction \(e^{-u}[-\log(2\pi)-\frac12\log(1-e^{-2u})]\) is negative with magnitude \(<1.84 e^{-u}\) at \(u\ge20\).

Conjugate-inclusive inverse-square sums are \(<.0503\) over all ordinates, \(<5.8\cdot10^{-12}\) above H. CH2 Lemma B.1, PDF p. 43, records first ordinate \(>14.13\) and \(N(t)\le \frac{t}{2\pi}(\log(t/(2\pi))-1)+7/8+R(t)\) with \(R(t)=1\) through 280 and \(R(t)=.2\log t+2\) thereafter. Integrate the integer-rounded bound at right endpoints of cells of width at most 1/4 against \(4dt/t^3\) on \([14.13,280]\). For \(z=280,H\), the upper integral to infinity is
\[
 \frac{2\log(z/(2\pi))}{\pi z}+
 \frac{2(23/8+.2\log z)+.2}{z^2}.
\]
At H discard the nonpositive lower-boundary term. osc02.py checks these enclosures; the needed elementary pi intervals follow, e.g., from ten alternating terms of Machin's formula.

Put \(Z_1=.0503e^{-L/2}+5.8\cdot10^{-12}e^{-cL}\). For \(Z_k\), multiply the two terms by \(1+4/(14L)\) and \(1+4/(HL)\). Finite-height RH and the selected cap give
\[
 -w(L)(Z_w+1.84e^{-L})\le I_w(L)\le w(L) Z_w,\quad L\ge20.
\]
The old fixed-cutoff inequalities remain valid; this new branch avoids their strip and Perron losses in the integral.

## Evidence

Exp bounds are rational, using certify.py's alternating series and directed squaring; density.py uses exact halving and squaring for large arguments to avoid an absolute precision floor. The Rosser integral uses edge.py's rational atanh log series. No floating-point sample enters the theorems.
