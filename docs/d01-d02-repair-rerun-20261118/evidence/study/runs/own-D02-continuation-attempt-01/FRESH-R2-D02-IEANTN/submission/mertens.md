# Mertens products and sums \(B0, hence also B0+D01\)

Let \(x>1, L=\log x\). Write \(P=\prod_{p\le  x}(1-1/p), Q=1/P\),
and let the four reported quantities be
\[
 |e^\gamma LP-1|,\quad  |e^{-\gamma}Q/L-1|,\quad 
 |S|=\left|\sum_{p\le  x}{1\over  p}-\log L-M\right|,\quad 
 |W|=\left|\sum_{p\le  x}{\log p\over  p}-L+B_3\right|.
\]
Here \(\gamma=\lim(H_n-\log n)\),
\(M=\gamma+\sum_p(\log(1-1/p)+1/p)\) and
\(B_3=\gamma+\sum_p\log p/[p(p-1)]\); these are the exact constants of
Dusart Theorems 5.6 and 5.7, not decimal surrogates. Set \(Z=\log Q-\log L-\gamma\).

## Portfolio and comparisons

Take the pointwise minimum of the following available **certified**
bounds, or the sharper signed envelope below. All onsets are inclusive
real endpoints. An error cap is non-strict unless specified otherwise.

* Retain the published \(.2/L^3\) for the two product errors at
  \(x\ge 2278382\), for \(|S|\) at \(x\ge 2278383\), and \(.3/L^2\)
  for \(|W|\) at \(x\ge 912560\). Locators: Dusart PDF pp.17–20,
  Theorems 5.6–5.9. For the first theorem see its actual \(2278383\)
  threshold, not the product's \(2278382\).
* Finite certificates from \(100000\) onward: see `sieve-results.txt`.
  For each bin with output integers (s,w,z), use
  \(|S|\le  s/(10000L^3), |W|\le  w/(10000L^2), |Z|\le  z/(10000L^3)\).
  Use both adjacent rows at their common endpoint if desired. Convert
  the last cap exactly to \(\exp(z/(10000L^3))-1\) for both products.
  These bins describe a nonconstant envelope, not a monotonicity claim
  for the underlying prime functions. In particular different onsets
  and coefficients need not form a single ordering.
* At \(\log x\ge 26, 30, 40, 58, 100\), respectively, the common
  coefficients **.051, .010, .0004, .00000011, .000000047** are valid in
  the shapes \(c/L^3\) for both products and \(|S|\), and \(c/L^2\)
  for \(|W|\). The finite-to-analytic join is covered since the
  sieve's final integer is \(>e^{26}\). Bounds are strict on these rays.
* Power/log shapes from the analytic density branch:
  
  | real log onset | weighted cap after dividing by x^\(-1/8\) | other three caps after dividing by x^\(-1/8\)/L |
  |---:|---:|---:|
  | 200 | .190 | .191 |
  | 300 | .145 | .145 |
  | 800 | .109 | .109 |
  
  These bounds are strict. The sharper signed envelope actually
  uses (d\(L\)) and integrals, not only the three rounded coefficients.

As examples of whole-ray tradeoffs obtained by taking suffix maxima of
the finite table and joining to the tail, the coefficient .20 is
valid for both products and \(|S|\) from 2500000, and .213 for \(|W|\)
there; from 4000000 take .161 for the three \(L^{-3}\) bounds and
.172 for \(|W|\); from 20000000 take .090 and .096; from 50000000
take .057 and .062; from 100000000 take .057 and .060. Earlier
valid bounds with bigger coefficients are given by the finite table
and the same suffix operation. At \(x\ge  e^{26}\) use the analytic
coefficients directly. The original \(L^{-k}\) branches are never
discarded on the near joins: e.g. the published product cap is
useful at \(2278382\). These comparisons follow from the certified
constant caps, not from sampling. At \(L\ge 200\) the power branches
already beat the original log powers: the comparison is
\(c L^2 e^{-L/8}\), decreasing for \(L>16\), and the endpoint
check \(c=.191, L=200\) even gives \(<1.1\cdot10^{-7}\).
Use the minimum including the CH2 branches through the crossover.

## Signed transfer and pointwise envelope

The following formulas give explicitly evaluable bounds for every
\(x\ge 2\); on \(1<x<2\) use empty products and sums. Interval sums and
intersections are pointwise. Thus there is no requirement to extrapolate
a finite-height interval to infinity or ignore its complement.

Let \(E(y)=\psi(y)-y, D_p(y)=\psi(y)-\theta(y)\),
\(F=\sum_{2\le  n\le  x}\Lambda(n)/n-L+\gamma\) and
\(U=\sum_{2\le  n\le  x}\Lambda(n)/(n\log n)-\log L-\gamma\).
In log coordinates, let \(I_\psi(u)\) enclose \(E(e^u)e^{-u}\).
In particular take the pointwise intersection of (D) for \(u\ge 200\)
and applicable original branches:
  
* FiniteRH Corollary 1 (PDF p.4), CH2 Corollaries 1.2, 1.3,
  9.3 (PDF pp.3, 36, the latter only when its \(T\) condition holds);
* Dusart Proposition 3.2/Table 1 and Theorem 3.3 (PDF pp.7–9);
  FKS Theorems 1.1–1.2 with their respective tables and
  Corollary 1.4 (PDF p.3, Tables 5–6 PDF pp.21–23; use the
  individual starting conditions and \(R\) from those theorems).

For the CH2 Corollary 1.2 branch use the original center relative
to \(e^u\), \((\pi /T)\coth(\pi /T)-1\), with radius
\[
 A_T+C_T e^{-u/2},\quad 
 A_T={\pi \over  T-1},\quad 
 C_T={\log^2(T/(2\pi ))-\log(T/(2\pi ))/3\over  2\pi }.
\]
Allow **any** \(10^7\le  T\le 3000175332800\) for which
\(e^u>\max(T,10^9)\). This also determines a family of weighted
bounds below; these auxiliary heights do not introduce QRH as an
extra hypothesis. Using infima of all applicable bounds is valid.
Intervals for any other lawful original Chebyshev bound can
likewise be intersected, with its original hypotheses and domains.
The comparison with the strongest possible use of originals does
not depend on exhaustively optimizing these parameterized families:
the implication in `density.md` establishes equality of deductive
strength with and without D01.

Take \(I_\theta\) to intersect Dusart Thm 4.2, FiniteRH Cor. 1 and
\(I_\psi(u)-[d_-(e^u),d_+(e^u)]e^{-u}\), with
\(d_-(y)=.9999\sqrt y\) on \(y\ge 121\) and zero below, and
\(d_+(y)=(1+1.47\cdot10^{-7})\sqrt y+1.78 y^{1/3}\).
These enclose \(D_p(y)\) by Dusart Prop. 4.3 and Cor. 4.5, PDF pp.12–13.
Also use the larger of the two lower bounds in Prop. 4.3 when
applicable.

For either \(I=[I_-,I_+]\) define
\[
 {\cal T}_j(I)=
 \left[a_j(L) I_-(L)-\int_L^\infty b_j(u) I_+(u)\,du,\quad a_j(L) I_+(L)-\int_L^\infty b_j(u) I_-(u)\,du\right],
\]
where \(a_0=1, b_0=1, a_1(u)=1/u, b_1(u)=1/u+1/u^2\).
Then \(F\in{\cal T}_0(I_\psi), U\in{\cal T}_1(I_\psi)\),
\(W\in{\cal T}_0(I_\theta), S\in{\cal T}_1(I_\theta)\).
These are Abel summation with the limiting constant fixed:
subtract \(dy\) from \(d\psi\) or \(d\theta\), integrate \(dE\)
or \(d(\theta-y)\), and send the upper endpoint to infinity.
For \(S,W\) the constants follow directly from Dusart 5.6–5.7.
For \(F,U\) they follow from \(W=F+J_0, Z=U+J_{1,c}\) with
the prime-power tails below tending to zero, and Dusart 5.7 and 5.9.
The integrals converge by (D) and the prime-power difference bound.

Let \(J_j=\int_{(x,\infty)} a_j(\log y)y^{-1}dD_p(y)\).
These are tails over all \(p^k>x, k\ge 2\), with weights
\(\log p/p^k\) and \(1/(kp^k)\), for \(j=0,1\).
Let \(C_x=\sum_{p>x}\sum_{k\ge 2}1/(kp^k)\) and \(J_{1,c}=J_1-C_x\)
(the tail with \(p\le x\)). Then exactly \(S=U+J_1, W=F+J_0, 
Z=U+J_{1,c}=S-C_x\). In particular the raw \(P\) and \(Q\)
are not independently normalized products.
For interval evaluation of \(J_j\), use
\[
 J_j=-a_j(L){D_p(x)\over  x}+\int_L^\infty b_j(u)D_p(e^u)e^{-u}\,du.
\]
Insert \(d_\pm\) with appropriate signs and intersect the lower
endpoint with nonnegativity. For \(C_x\), use
\(0\le C_x\le 1/\lfloor x\rfloor\) by bounding each summand's
prime subtotal by \(1/(p(p-1))\) and telescoping over integers.
One may refine this using the smaller Dusart bound in the proof
of Theorem 5.9 where valid. Use \(0\le  J_{1,c}\le  J_1\) as well as
\(J_{1,c}=J_1-C_x\). For the simple numerical bounds it suffices that
\[
 0\le  J_0\le  1.001 e^{-L/2}+2.67e^{-2L/3}\quad (x\ge121),\qquad 
 0\le  J_{1,c}\le  J_1\le  J_0/L.
 \tag{PP}
\]
Indeed the endpoint subtraction saves \(.9999e^{-L/2}\) and
the integrals of \(d_+\) give \(2(1+1.47\cdot10^{-7})e^{-L/2}+
(3/2)1.78 e^{-2L/3}\); division by \(L\) for the log weights
is valid for every tail prime power.

**Sharper branch for \(U\) without an avoidable integral loss.**
CH2 Corollary 1.2 bounds \(F\) directly by \(A_T+C_T e^{-L/2}\)
for each allowed \(T\). If \(I_F\) is the intersection of these
intervals and \({\cal T}_0(I_\psi)\), then also
\(U=F/L-\int_L^\infty F(e^u)\,du/u^2\), where in this last
identity \(F(e^u)\) denotes the same residual evaluated at \(x=e^u\).
For a stronger alternative use CH2 Proposition 9.1, PDF pp.34–36,
simultaneously for \(1<\sigma \le 100\). Define
\[
 B_\sigma(x)=\sum_{n\le  x}\Lambda(n)n^{-\sigma}
             -(-\zeta'(\sigma)/\zeta(\sigma))
             -{x^{1-\sigma}\over 1-\sigma}.
\]
The Euler product identity at \(\sigma>1\) follows from unique
factorization and absolute convergence. Subtraction from the full
sum and partial summation give
\(B_\sigma=E(x)x^{-\sigma}-\sigma \int_x^\infty E(y)y^{-\sigma-1}\,dy\).
Thus \(\int_1^\infty B_\sigma\,d\sigma=U\); the interchange is
absolutely convergent by (D) (or the elementary cap near a
finite \(x\) followed by (D)). Its kernel is exactly \({\cal T}_1\).
By Proposition 9.1 the normalized interval for \(x^{\sigma-1}B_\sigma\)
has center \(-(\pi /T)\coth(\pi (\sigma-1)/T)+1/(\sigma-1)\le 0\),
and radius \(A_T+C_Te^{-L/2}\). Integrate that center and radius
with weight \(x^{1-\sigma}\) for a directional bound.
For \(\sigma>100\), \(|E(y)|\le  y\) from Dusart 3.3 gives
\(|B_\sigma|\le 3x^{1-\sigma}\).
In particular the asymmetric interval for \(U\) has upper bound
\(K=(A_T+C_Te^{-L/2})/L+3e^{-99L}/L\), and lower bound
\(-K-\pi ^2/(3T^2L^2)\), since the center above is at least
\(-\pi ^2(\sigma-1)/(3T^2)\) by CH2 \(7.2\). Notice the absence of
a factor \(1+O(1/L)\) on \(C_T\) or a factor 2 on \(A_T\), both
present in the naive transfer through an absolute \(F\) bound.

The reported envelope intersects all these intervals for each
quantity, via the just-given transfer identities, and the finite
and analytic symmetric caps on their domains. Given a signed
interval \([z_-,z_+]\) for \(Z\), the two product bounds are, respectively,
\(\max(e^{-z_-}-1,1-e^{-z_+})\) and
\(\max(e^{z_+}-1,1-e^{z_-})\). Finally intersect these output bounds
with the original relative-product inequalities; one may also
feed those back as bounds on \(Z\) via logs. This is an all-domain
envelope of the furnished branches, not a claim that no stronger
B0 construction is possible. All sums and product operations
refer to primes \(p\le x\), including at the jumps.

## Whole-ray numerical comparisons

For fixed \(T\), (PP) and the two direct CH2 weight bounds imply the
following upper cap on each of \(L^2|W|, L^3|S|, L^3|Z|\) in
the domain of the chosen height:
\[
 L^2\big(A_T+(C_T+1.001)e^{-L/2}+2.67e^{-2L/3}\big)
 +{\pi ^2 L\over 3T^2}+3 L^2 e^{-99L}.
\]
On \([a,b]\) with \(a\ge 26\), bound the increasing terms at \(b\)
and the other terms at \(a\), then use the product conversion
\(c\mapsto c/(1-c/a^3)\) (since \(e^v-1\le  v/(1-v)\) for \(0\le  v<1\)).
`mcheck.py` certifies the intervals \([26,30],[30,40],[40,58],
[58,100],[100,210]\) with heights \(10^7,10^7,3000175332800\)
for the first two and last three respectively. For the final join
\([210,\infty)\), verify \(.191\cdot210^2e^{-210/8}<.000000047\)
and use the decreasing monomial thereafter.

For the power shapes, (D) with decreasing \(d\) gives
\[
 |F|\le  9d(L)e^{-L/8},\qquad 
 |U|\le  (9+8/L)d(L)e^{-L/8}/L .
\]
Add (PP) and convert the log to relative error as above, taking the
worst at the *left* endpoint after rescaling. This proves the three
power rows. The exponential ratio of (PP) to \(e^{-L/8}\) decreases.
For smaller intermediate log values there is no need to force these
shape bounds through the finite-height floor; the whole-domain
minimum retains each stronger finite or CH2 bound where applicable.

For comparison, using only D01 *on the same tail* in these absolute
Abel maps (prior to the prime-power correction) would give
\((9L^2+128L+1024)x^{-1/8}/64\) and
\((9L+72)x^{-1/8}/64\), respectively. This is a valid but
dominated application of D01, since the monotone input envelopes
are nested pointwise for the entire tail. The improvement at
finite onsets comes from explicit prime summation and sharper
weight transfer, not from D01. There is no independent blind B0
run claimed. The remaining simple-tail bottleneck at the final
sieve join is the \(C_T/\sqrt x\) contribution from bounded-height
zero information, not the hypothetical long-tail coefficient.
