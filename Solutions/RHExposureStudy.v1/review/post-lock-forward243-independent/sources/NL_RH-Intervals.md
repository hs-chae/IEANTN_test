# Intervals: exact logarithmic triangular window, real count, and inversion

Hypothesis in the main bounds: pinned Mathlib RiemannHypothesis. Prime counting
uses primes p<=x; explicitly open intervals below are *strictly* open.

## A parametrized short-interval bound

Let L=log x>=24 and
```
D0 = L/2-log L-1/4,   D0<=D<=2L,   delta = D/sqrt(x),
a=x exp(-delta),      b=x exp(delta).
```
Then under RH,
```
#{p : a<p<b} > (D-D0+.08) sqrt(a)/log a.
```
In particular with D=D0 this proves an explicit count in a narrower interval
than the DGM existence bound, and with D=3L/2-log L-1/4 it gives >sqrt(x)
primes in the indicated open interval.

Proof: test the measure dpsi on (1,infinity) against
```
w(t)=t^(-1/2) max(0,1-|log(t/x)|/delta).
```
By twice differentiating the integrated explicit formula in PNT.md in the
distributional sense, the main term of the weighted sum is exactly
sqrt(x)*8(cosh(delta/2)-1)/delta >=sqrt(x)delta.
Each zero term under RH is e^(i gamma L) delta f(delta gamma), where
f(y)=2(1-cos y)/y^2 (f(0)=1). For rigor pair the locally uniformly convergent
Psi1 series with the piecewise smooth test function (integrate by parts twice,
including derivative jumps of the test); equivalently approximate by smooth
mollification on a compact interval inside (1,infinity), and the second
derivatives of the approximants have uniformly bounded total variation.
The absolute zero majorant is O_delta(sum |gamma|^-2). The derivative of the
trivial part b(t) is -1/[t(t^2-1)], and the constant -c disappears. Thus
its negative contribution has magnitude <2 delta/[sqrt(a)(a^2-1)]
by using t=xe^u and the log-window length 2delta. The test vanishes at
both endpoints, regardless of whether an endpoint is a prime power.

Use the zero-count M(t) and R(t) from PNT.md, with |R(t)|<=1+.28 log^+ t
for all t>0: for t<2pi we have N(t)=0 from N(12)=0, and |M(t)|<1.
Integration by parts with R(t), using f(delta t)->0 and R(0+)=-7/8,
bounds
```
sum_rho delta f(delta gamma)
 <= log(1/(2 pi delta)) + 1-gamma_E
        + 2delta [1+(7/3)(1+.28 log(1/delta))+.896].
```
The extra 1 covers the boundary at zero. For f, use the Fourier transform
of the triangle on [-1,1] to give |f'(y)|<=y/6 up to 2; for larger y
differentiate the expression and use |f'|<=2/y^2+8/y^3. Thus
int_0^infty |f'|<=7/3 and int_0^infty |f'| log^+y <3.2; use
log^+(y/delta)<=log(1/delta)+log^+ y for 0<delta<1.
The main density integral (M'(t)=log(t/(2pi))/(2pi)) follows from
```
int_0^infty f(y)y^s dy = pi/[Gamma(2-s) cos(pi*s/2)]  (-1<s<1).
```
Indeed write y^(s-2) by its positive gamma/Laplace integral,
integrate 2(1-cos y) exp(-ty) first to get 2/[t(1+t^2)], then apply the
beta integral. Evaluation and differentiation at s=0 give pi and
pi(1-gamma_E); differentiation is dominated in a neighborhood of 0.

The weighted nonprime prime powers are at most
```
Q = exp(delta/2)(L+delta)/sqrt(x) [2delta exp(delta/2)sqrt(x)+log K],
K=floor((L+delta)/log 2).
```
For k>=2 there are at most 1+2delta exp(delta/2) x^(1/k)/k possible
integer bases in the interval; each log p<= (L+delta)/k, and
t^(-1/2)<=exp(delta/2)/sqrt(x). Use sum_{k>=2} 1/k^2<=1 by telescoping
1/[k(k-1)], and sum_{k=2}^K 1/k<=log K. This deliberately counts
some composite bases, but does not use any precomputed prime-power table.

Numerical margins uniform in the entire stated domain:
* D0/L>.35 and increases, since (log L+1/4)/L decreases for L>=24.
  So D0 - [log(1/(2 pi D0/sqrt(x)))+1-gamma_E]
  = log(2pi D0/L)-1/4-(1-gamma_E) > .113
  (use gamma_E>.577, pi>3.14159).
* delta<=2L exp(-L/2)<=48 exp(-12)<.000295.
  The zero-count discrepancy, including the boundary, is <.0065 since
  delta(1+C log(1/delta)) is increasing on this small-delta range for the
  relevant coefficients. Q<.0155: use K<2L, L+delta<1.001L,
  exp(delta/2)<1.0002 and D<=2L; L^2 exp(-L/2) and
  L log(2L) exp(-L/2) decrease on L>=24. The trivial term is <.001.
* Subtracting these quantities leaves >.08 above D-D0. For D>D0 also
  log(1/delta) decreases, so its main density bound did not increase.
  Each prime contributes at most (log a)/sqrt(a), decreasing since a>exp(2).
  Dividing proves the claim. For D=D0+L, the conclusion exceeds sqrt(x)
  since exp(-delta/2)(L+.08)>L-delta (use delta L<.008).

Endpoint conversion example: for D=D0 and 24<=L<=75, the ratio
(b-a)/(sqrt(a) log a) is
```
(2D0/L) exp(delta/2) (sinh(delta)/delta)/(1-delta/L) < .88.
```
Here 2D0/L increases, at L=75 it is <.8784, and the remaining factor
is <1.0003. The map L -> log a = L-delta is strictly increasing
(delta decreases on this region by differentiation); its image
contains [24,74]. Therefore on exp(24)<=u<=exp(74) the new result
gives an open interval inside (u,u+.88 sqrt(u) log u) and a count there.

## Comparison with direct RH work

* Dudek–Grenié–Molteni arXiv:1503.05403v2 Thm 1.1: for x>=2,
  c=.5+2/log x, prime existence in (x-c sqrt(x)log x,x+c sqrt(x)log x),
  at least sqrt(x) primes with c replaced by c+1. Comparing radii,
  even the larger of a and b offsets in our D=D0 or D=D0+L cases
  respectively is strictly smaller for L>=24 (use e^delta-1<=delta e^delta
  and D delta e^delta<.015). This comparison is to the stated direct
  analytic theorem; Oliveira e Silva–Herzog–Pardi's gap verification,
  cited by DGM, performs much better for x up to 4e18.
* Carneiro–Milinovich–Soundararajan arXiv:1708.04122v2 Cor. 4 and
  Thm 5 give, respectively, asymptotic gap limsup coefficient <21/25
  and a prime in [x,x+(22/25)sqrt(x)log x] for x>=4. Our window has
  asymptotic full length coefficient 1, so it does not beat either
  asymptotically. The finite quantitative one-sided comparison above
  is meaningful only on its stated log band, especially beyond the
  smaller verified gaps. CMS Thm 3 also gives asymptotic count, not
  just existence; it is not uniformly beaten by this triangle.
* The new feature relative to DGM's additive triangle is that multiplying
  by t^(-1/2) and moving to log t gives the *exact* sinc^2 multiplier.
  Bounding the sum of its positive values for all zeros loses phase
  cancellation; this route alone is not designed to beat CMS's leading
  coefficient. No GRH or pair-correlation assumption.

## Wide interval and inverse variants

For exp(8)<=a<=b, write D(t)=psi(t)-t, ell=log a, Lb=log b, and let
Q_{a,b}=sum_{k=2}^{floor(Lb/log 2)} [pi(b^(1/k))-pi(a^(1/k))]/k.
Then the exact error in pi(b)-pi(a)-(Li2(b)-Li2(a)) is
D(b)/Lb-D(a)/ell - Q_{a,b} + I0(a,b) - c(1/ell-1/Lb) + Ib(a,b),
where 0<=Ib<=b_triv(a)(1/ell-1/Lb)
and |I0(a,b)|<=.094 sqrt(b)/Lb^2 by the same integration by parts
as in PNT.md with lower limit ell>=8. Here b_triv(t)=-log(1-t^-2)/2.
There is no stand-alone anchoring constant. To avoid two independent
errors on prime powers, use 0<=Q_{a,b}<=sum (floor(b^(1/k))-
floor(a^(1/k)))/k, or intersect with the separated PNT Q bounds.
Using signed endpoint bounds instead of absolute ones is important
when the anchor a is inside a verified one-sided range. This is about
(a,b], not (a,b); for open upper endpoint take b from the left (or
subtract 1 if b is prime). For existence in (a,b] require positive lower
count, not merely nonnegative. No inference about very short intervals
from this formula alone is claimed.

For a finite inverse example, let y solve li(y)=n for integer n and
1e10<=y<=1e19-1e10. (li strictly increasing on (1,infinity).)
Then y<p_n<=y+2.2 sqrt(y), where p_n is the n-th prime starting with
p_1=2. By the imported unconditional Büthe Thm 2, pi(y)<n.
Set b=y+2.2 sqrt(y)<=1e19; the lower error bound from that theorem
has coefficient 1.95+3.9/log b+19.5/log^2 b<2.16 since log b>23.
Meanwhile li(b)-n >= (b-y)/log b > 2.16 sqrt(b)/log b.
Hence pi(b)>n and in particular is >=n. This is a deduction from
published one-sided estimates; no claim of more accurate inversion
than exact prime counting or of novelty.

## Parabolic window: stronger explicit finite band

For L>=24 set
```
D1=.465 L-.93 log L-.25,     D1<=D<=2L,
delta=D/sqrt(x),            a=x exp(-delta), b=x exp(delta).
```
Under RH,
```
#{p : a<p<b} > [(4/3)(D-D1)+.04] sqrt(a)/log a.
```
In particular D=D1+3L/4 gives >sqrt(x) primes in strictly narrower
intervals than the earlier triangle at D0+L or DGM's count theorem.
With D=D1 the full interval length satisfies
(b-a)/(sqrt(a) log a)<.88 for 24<=L<=200, as in the triangle endpoint
conversion, using the upper ratio at L=200 and factor <1.0003. The map
L->L-delta increases (delta decreases at D=D1) and its image includes
[24,199]. Thus for exp(24)<=u<=exp(199) there is a prime in the open
interval (u,u+.88 sqrt(u) log u), with the displayed quantitative count
already in a narrower interval. No homogeneous <.88 asymptotic
coefficient is claimed from this window. For the count >sqrt(x), its
leading full-length coefficient is 2.43; taking a slightly larger D
gives a strictly greater liminf after division by sqrt(x). This compares
to the numerical upper 63/25 for alpha=1 in CMS Thm 3, not a bound on its
underlying unknown optimal constant 3/C^+(B).

Use the test w(t)=t^(-1/2) max(0,1-(log(t/x)/delta)^2). Its Fourier
multiplier is delta f(delta gamma), with f(y)=4(sin y-y cos y)/y^3,
f(0)=4/3. The main term is at least (4/3)sqrt(x)delta by the symmetry
of the weight and cosh>=1. As before the prime-power cost and the
trivial term are <.0155 and <.001. For the zeros we need absolute
values, since here the Fourier transform is signed. The useful bounds are
```
(1/pi) int_0^infty |f(y)| dy < 1.24,
(1/pi) int_0^infty |f(y)| log y dy < .50,
int_0^infty |f'(y)| dy < 4.54,
int_0^infty |f'(y)| log^+ y dy < 6.1.
```
The variation bounds follow from |f'(y)|<=4y/15 up to y=2 using the
second moment of the even test, and |f'|<=4/y^2+12/y^3+12/y^4
beyond 2 from the explicit derivative. For the first two integrals,
parabola.py evaluates h=.002 midpoint rectangles with directed rational
sine/cosine by their alternating Taylor bounds and exact interval
rotation. It bounds log at the midpoints by the tangent at the preceding
multiple of 1/8 for y>=1. The continuous enclosure adds h/2 times the
integrated variation: 4.54 for |f| on [0,100], and 7.7 for |f| log y on
[1,100] (use the log-variation bound plus int_1^infty |f|/y<1.6, from
|f|<=4/3 through 2, and <=4/y^2+4/y^3 thereafter). This midpoint
remainder bound follows by exchanging the variation integral with
integration over each half-cell; each derivative value is counted
over length at most h/2. For the missing log integral [0,1] use
f(y)>=4/3-(2/15)y^2>0 and log y<0, giving upper -4/3+2/135.
The two positive tails beyond A=100 are bounded using 4/y^2+4/y^3
and its product with log y; the integrals are explicitly
4/A+2/A^2 and 4(log A+1)/A+2(log A+1/2)/A^2.
Hence the quadrature is an all-real integral bound, not a point sample.

Apply Stieltjes integration by parts with the same M(t) and R(t) as
for the triangle, now to |f(delta t)| (absolutely continuous on
finite intervals even at zeros of f; its derivative modulus on
differentiability points is <=delta |f'(delta t)|).
The zero sum is bounded by
```
1.24 log(1/(2 pi delta)) + .50
+ 2delta [7/6+4.54(1+.28 log(1/delta))+.28*6.1].
```
The last term is <.011 on the whole domain, from delta<=48 exp(-12)
and monotonicity of the small-delta expression. The log factor in front
of 1.24 is positive throughout. At D=D1 the main term minus the first
two terms is at least (4/3)[.93 log(2 pi*.33)-.25]-.50 > .07 because
D1/L>.33 and increases. For larger D the logarithmic term decreases.
Total error <.011+.0155+.001, leaving >.04 in addition to the term
(4/3)(D-D1); then bound each prime's weight by log(a)/sqrt(a).
This gives a second independent test function beyond the exact triangle;
the direct CMS comparison is now over a substantially wider finite band.
