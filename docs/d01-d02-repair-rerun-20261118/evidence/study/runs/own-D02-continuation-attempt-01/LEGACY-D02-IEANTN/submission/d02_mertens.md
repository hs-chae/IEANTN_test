# Mertens products and sums: signed envelopes, strict baseline improvements
Theorems here are for real arguments and inclusive primes. `smoothing.md`
defines δ and proves the two integrated ψ tail bounds; δ=1/8 uses only the
admitted original papers, while δ=5/32 additionally uses A-D02.

## Signed envelope (x >= exp(18))
Set L=log x, Z=exp(-L/2), C=exp(-2L/3), X=exp(-L),
α=1.47e-7, ε=.0001, η=1.78, and w1(L)=(L+1)/L², w2(L)=1.
Let
  D1(x)=∑_{p<=x}1/p - log L - M,
  D2(x)=∑_{p<=x}(log p)/p - L + B3,
  DQ(x)=log Q(x)-γ-log L.
The constants M,B3 have the infinite-series definitions in Dusart 5.6–5.7.
Define
  B1(L)=.5*∫_L^∞ exp(-v/2)/v dv,  B2(L)=Z;
  F1(L)=w1(L)*(.085Z+3.3e-12 exp(-δL)+2X),
  F2(L)=.083Z+3.2e-12 exp(-δL)+2X.
Choose any deterministic lower and upper bounds -a_-(L)<=eψ(L)<=a_+(L).
In particular the following can be intersected whenever available:
* a_-=.751Z, a_+=.791Z on [18,29.9] (CH2 Lemma 9.2, PDF p.35);
* a_-=a_+=.0397888 L² Z for 18<=L<=58
  (finite-RH Cor.1, PDF p.4; the real range ends above exp(58));
* a_-=a_+=q+113.67Z (CH2 Cor.1.3, PDF p.3);
* the smoothed and truncated pointwise bounds from `smoothing.md`,
  and, if A-D02 is invoked, L² exp(-δL)/64 for L>=200;
* the original FKS Cor.1.4 pointwise bound, where it is smaller.
The density extension (separately labelled) offers still smaller a_± in
the far ray.

For j=1,2 set
  Uj = (a_+ + ε Z)/L^(2-j) + Fj + wj(L)*(2α Z + (3/2)η C),
  Wj = (a_- + α Z + η C)/L^(2-j) + Fj + 2 ε wj(L) Z.
Then
  Bj-Wj <= Dj <= Bj+Uj.
Also let t1=1/(2 floor(x)). For the logarithm of the normalized product
  ℓ=B1-W1-t1 <= DQ <= b=B1+U1.
Consequently the two product relative errors, in the order Q then P,
are bounded by max(exp(b)−1,1−exp(ℓ)), max(exp(−ℓ)−1,1−exp(−b)).
The same interval shows the signs when separated from zero.

## Derivation and constants
Dusart 5.6 and 5.7, formulas (5.7) and preceding identity, or Stieltjes
partial summation and those theorems' limiting constants, give
  Dj = z_theta(L)/L^(2-j) − ∫_L^∞ z_theta(v) wj(v) dv,
where z_theta(v)=(theta(exp v)-exp v)/exp v.
By Dusart Prop.4.3 and Cor.4.5 (PDF pp.12–13),
z_theta(v)=eψ(v)-exp(-v/2)-ξ(v) with
  −ε exp(-v/2) <= ξ(v) <= α exp(-v/2)+η exp(-2v/3)
for v>=18. Substituting, the -exp(-v/2) model contributes exactly Bj:
for j=1, differentiate exp(-v/2)/v and integrate; for j=2 use the
elementary exponential integral. For the errors use Fj from `smoothing.md`
and ∫_L^∞ exp(-c v) wj(v)dv <= exp(-cL) wj(L)/c.
Now DQ=D1−T1 with
  T1=∑_{p>x} ∑_{k>=2} 1/(k p^k) ∈ [0,1/(2 floor(x))]
by telescoping ∑_{n>floor(x)}1/[2n(n−1)]. P and Q are reciprocals. This
last tail correction is exact and not a cut off at p^k<=x.

## Whole-ray small-coefficient version without the A-D02 hypothesis
There is a nonincreasing coefficient K(x), given in the table below,
such that the Q and P relative errors are <=K(x)/L³ on the product
domain and |D1|<=K(x)/L³ on its own domain. Absolute-error and sign
envelopes above may further reduce these bounds pointwise.
Use the last row whose onset is at most x:
```
   onset x        K(x)
 2278381.750      .20000  (products only before 2278383)
 2278381.950      .19998  (products only before 2278383)
      3500000     .180
      5000000     .160
     18100000     .100
    111000000     .060
    181000000     .050
   1125000000     .030
   4760000000     .011
```
The D1 domain starts at 2278383. The `.19998` row is strictly smaller at
the entire original product onset 2278382 onward and at the entire
original prime-reciprocal onset 2278383 onward. The original product
constant .2 also starts a quarter unit earlier, hence the two advantages
are not conflated. Relative error computed against P and against Q is
covered simultaneously.

For D2, on x>=2278383 use
  |D2| <= 1.5 K(x)/L².
Indeed dD2 = v dD1 in the logarithmic variable v as Stieltjes measures,
and D2(v)−v D1(v)→0 by Dusart 5.6–5.7. Integration by parts gives
  D2(x)=L D1(x)+∫_L^∞ D1(exp v)dv.
Use K nonincreasing. It beats .3/L² at every such x. The original .3/L²
bound is retained for [912560,912561). The weighted finite check gives
.29998/L² on [912561,2278383]. The direct test for .29998 at 912560
did not certify, so no further claim is made at that endpoint.

### Proof of the piecewise numerical bound
The exact finite checks are in mfinite.cpp and mexact.cpp. They use an
Eratosthenes sieve, local prime counts, directed fixed-point arithmetic
for all noninteger quantities, and no external tables. For the analytic
links, a common absolute cap on |D1|,|DQ| is
  u(L)=(a+(1+α+ε)Z+ηC)/L + F1 +
           w1*(2(α+ε)Z+(3/2)ηC) + X,                 (†)
where a=max(a_-,a_+), δ=1/8, T1<=X and B1<=Z/L.
For |DQ|<=u<1, both relative errors are <=u/(1−u).
Use a=.791Z on [18,29.9], a=.0397888 L² Z on (29.9,58],
a=119Z+3.6e-6 exp(-L/16)+2X beyond 58. On each branch L³ u is
decreasing, termwise: the products of nonnegative polynomials in L
of degree at most 4 with negative exponentials are decreasing beyond
the left endpoints. (For the slow factor exp(-L/16) the degree is
only 2 and its branch starts at 58.) Thus L³u/(1−u) is decreasing too.
mcheck.py shows the .100/.060/.050/.030/.011 rays hold from
L=18/19/19.5/21/23, respectively. The finite checks extend each left
and connect the low coefficients before those exponentially large onsets.

The log/exp constants in the finite code are arithmetic certificates,
not calls to floating-point logarithms. For y=x/2^k in [1,2), put
z=(y−1)/(y+1)∈[0,1/3]. With scale S=2^60, logseries(floor(Sz))/S
is a lower bound for log y. Each update forming the next odd
power truncates twice, so in scaled units its error is bounded
by 2 + previous_error/9 (compare to powers of floor(Sz)/S).
The 40-term sum of term-rounding errors is <200 units; the z-argument
rounding costs <3 and the series tail is <1. Thus adding 300 per
log block safely upper-bounds it. This also handles log(log x) by
monotonicity. For γ, the trapezoidal approximation
H_N−log N−1/(2N) is below γ and within N^(-2): successive differences
are trapezoid errors for 1/t on [k,k+1], bounded by 1/(6k³) via
twice integrating the derivative or Taylor with integral remainder.
The sum of their bounds is <N^(-2). In code the γ index is N=10^6.

Let N0=10^7. For the M constant, accumulate positive terms
K1(N0)=∑_{p<=N0,k>=2}1/(k p^k) using floors; after p^k>S the
sum of remaining powers costs <2/S per prime. Rounding costs
at most 1/S per computed term. In the coarse routine use
0<=K1(∞)−K1(N0)<=1/(2N0). In the precise one bound this
last quantity between 2.89e-9 and 2.96e-9: for t>=N0,
|θ(t)/t−1|<.001 by CH2 Lemma 9.2 and Dusart 4.5 through 10^13
and CH2 Cor.1.3 plus Dusart 4.5 thereafter. Partial summation gives
 |∑_{p>N0}1/p²−I(N0)| <= .001*(3+1/log N0)/(N0 log N0),
where I(N0)=∫_{N0}^∞ dt/(t² log t). Integration by parts twice
brackets I between (1−1/log N0)/(N0 log N0) and
(1−1/log N0+2/log²N0)/(N0 log N0).
The total of k>=3 is <1/(2N0²). mcheck.py certifies the decimal endpoints.
For B3, use K2(N0)=∑ log p/[p(p−1)].
The tail for ∑_{p>N0}log p/p² is 1/N0 ± .003/N0 by the same θ
bound and partial summation. Replacing p² by p(p−1) costs at most
1.003/N0², so the bracket [.997/N0,1.00301/N0] is valid.

Coarse finite checking compares sums at both interval ends, and
log log x at the opposite ends by monotonicity. It reserves a factor
999/1000 of the target k/L³ for exponentiation and subtracts the
explicit elementary tail T1 on the lower side for the products.
Since the targeted k/L³ values are all <.001, this suffices.
The refined finite check uses the two opposite monotone thresholds
log L ± k/L³ for D1 and log L ± log(1+k/L³) for each plateau of log Q
(both derivatives positive in the required domain). Endpoints include
the left limits at primes and the exact point values. For log(1+t)
it tests the sufficient lower bound t−t²/2 with directed rounding,
so the finite proof covers all real x, not just samples. The
weighted version compares the monotone thresholds L ± k/L²
against the corresponding plateaus.

## Signed arithmetic consequences (non-density route)
For 20<=L<=29.9 the two normalized product errors have opposite signs:
Q/(exp γ * L)>1>P*exp γ * L. In fact DQ > .003*exp(-L/2)/L,
and D2 > .10 exp(-L/2) on this interval, unconditionally.
For the lower bound on B1, Jensen's inequality (or the tangent to
1/(L+t)) against the exponential law of mean 2 gives B1>=Z/(L+2).
Insert the one-sided CH2 Lemma 9.2 estimates, the lower Dj bounds
above, and T1<=X. The normalized lower inequalities follow by
the monotone endpoint comparisons in mcheck.py. The signs are
not asserted to persist forever.
