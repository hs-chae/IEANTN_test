# PNT: logarithmic smoothing and signed prime-counting conversion

All conditional conclusions in this note have explicit hypothesis the pinned Mathlib
`RiemannHypothesis`. This is a mathematical derivation, not a Lean formalization.
Use right-continuous psi, theta, pi. Write L=log x, c=log(2 pi), a=2 pi (the
number pi, not the counting function), and li = Li2 + li(2) with li(e^u)=Ei(u).

## Imported bounds and analytic inputs

* Lee–Nosal arXiv:2312.05628v4 Thms 1.1–1.2 give
  B1/sqrt(x)=L^2/(8 pi)-(L/(2 pi)+1.465)log L+1.2325 L (x>=11),
  B2/sqrt(x)=L(L-log L)/(8 pi) (psi x>=101, theta x>=2657).
  The parentheses in the page-marked text must be read against the derivation from
  (17) and Lemma 3.2, not linearly from the PDF extraction.
* Lee–Nosal (8): N(T)=M(T)+R(T), M(T)=T/(2 pi) log(T/(2 pi e))+7/8 and
  |R(T)|<=0.28 log T for T>=2 pi. N counts 0<Im rho<=T with multiplicity.
* Büthe, arXiv:1511.02032, Thm 2: |psi-x|<=.94 sqrt(x) for 11<x<=10^19;
  .05 sqrt(x)<x-theta<=1.95 sqrt(x) for 1423<=x<=10^19 (lower bound alone holds
  on [1,10^19]); 0<li-pi<=sqrt(x)/L(1.95+3.9/L+19.5/L^2) on [2,10^19].
  These are unconditional imported computations, not independently verified here.
* Schoenfeld (1976), Cor. 1: |pi-li|<sqrt(x)L/(8 pi) on x>2657 under RH (the exact equality endpoint can also be covered by Büthe or Johnston). In
  comparing absolute bounds for pi-Li2 one must add li(2) on the upper side,
  not discard it. Johnston Proposition 3.1 and Cor. 3.3 give unconditional
  finite windows accounting for verified height; do not extrapolate them.
* Platt–Trudgian arXiv:1407.1914v1 Cor. 2: 0<=psi-theta <
  1.00000075 sqrt(x)+3 x^(1/3), for x>0.

The absolutely convergent integrated explicit formula is supplied in Lee–Nosal (13)
and Dudek–Grenié–Molteni arXiv:1503.05403v2, p. 2. With its trivial terms written
out by the residues at -2k in the displayed Perron representation there, for t>1,
```
Psi1(t)=integral_0^t psi(v) dv
       =t^2/2 - sum_rho t^(rho+1)/(rho(rho+1)) - c t + kappa
           - sum_{k>=1} t^(1-2k)/(2k(2k-1)).
```
The series is locally uniformly absolutely convergent. The ordinary right and
half jump definitions give the same Psi1. Its first distributional derivative
on (1,infinity) gives psi(t)=t - sum_rho t^rho/rho -c+b(t),
b(t)=-log(1-t^-2)/2; the displayed zero term is interpreted through integration,
not asserted to converge absolutely pointwise. Integration against a compact
piecewise C^1 weight is justified by integration by parts against Psi1, including
endpoint terms. Against a continuous piecewise C^2 test function supported
away from 1 we can instead differentiate twice to address dpsi. These conventions
are reused in Weighted.md and Intervals.md. For tail integrals take limits after
the integration and bound the endpoint terms.

Under RH, Z=sum_rho 1/|rho|^2=2+EulerGamma-log(4 pi)<.047. Derivation: set
xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2. Take the difference of its Hadamard
log derivatives at 1 and 0 (the order-one canonical factors cancel the
linear constant), giving sum 1/(rho(1-rho)); by xi(1-s)=xi(s) the difference
is 2 xi'(1)/xi(1). Use zeta(1+s)=1/s+EulerGamma+O(s), and
Gamma'/Gamma(1/2)=-EulerGamma-2log 2 by duplication. RH makes
rho(1-rho)=|rho|^2. For the numerical inequality one can use
EulerGamma <= H_64-log(64)-1/130 and log(4 pi)>2.531. The harmonic bound
is obtained by summing log(1+1/k)-1/(k+1) >= 1/(2(k+1)^2) and using the
integral lower bound for that tail. Nontrivial real zeros are absent
because the alternating eta series is positive for 0<s<1 and zeta(s)
there equals eta(s)/(1-2^(1-s)). The classical xi zeros lie in the
critical strip, and the boundary/pole/trivials are as in RESEARCH.md.

## New two-box bound for psi

For all L>=35, set s=L/2-log(L/2). Under RH,
```
B3(x) = sqrt(x) [(s^2+s+1/2+L)/(2 pi)+.14],
|psi(x)-x| <= B3(x).
```
No extra verified height or sum over computed individual zeros is used for B3.
To prove it put delta=L/(2 pi sqrt(x)), T=2/delta (T>10^7), and average
psi(x exp(±(U+V))) where U,V are independent uniform [0,delta].
These averages bracket the exact psi(x) by monotonicity for all real x,
including prime powers. The main term differs by at most x delta exp(2delta)
since E(U+V)=delta. On t in the supports, |-c+b(t)|<=c<1.9.
An individual zero receives an exact multiplier ((exp(±rho delta)-1)/(±rho delta))^2.
Its absolute value at RH is <=exp(delta/2) [min(1,4/(gamma delta)^2) + C/|rho|^2],
where C=4 sinh^2(delta/4)/delta^2<.251. This follows by evaluating the
squared modulus before bounding the sine and hyperbolic sine terms. Both
averages are justified by the integrated formula with the continuous compact
log-triangular weighting including the Jacobian; the zero sum then converges
absolutely.

In fact N(12)=0, since M(12)+.28 log(12)<1. For T>=10^7, partial summation
with lower endpoint 12 gives
```
sum_{0<|gamma|<=T} 1/|gamma|
 <= (log(T/a))^2/(2 pi) + .56 log T/T
      + .56(log 12+1)/12 + 2 M(12)/12 - (log(12/a))^2/(2 pi)
 < (log(T/a))^2/(2 pi) + .131.
T^2 sum_{|gamma|>T} |gamma|^-3
 <= (log(T/a)+1/2)/(2 pi) + (1.12 log T+.187)/T .
```
In the latter use -2R(T)/T^3+6 integral_T^infty R(t)t^-4 dt;
a zero at T is counted only on the low side. The extra term for sinh is
<= .251 Z/12<.001. With T=4 pi sqrt(x)/L, log(T/a)=s. The claimed .14
absorbs all correction terms: delta<1.5e-7, exp(2delta)-1<3delta,
exp(delta/2)-1<delta, delta L^2<=35^3 exp(-17.5)/(2 pi)<.00018,
and log T/T is decreasing for T>=10^7. This also bounds the very small
constant term 1.9/sqrt(x).

At L>=35, B3 is strictly smaller than B1 and B2. More strongly,
B2-B3 > 1.15 sqrt(x), so the same route strictly improves the symmetric
theta bound after subtracting prime powers. To check put q=log(L/2). After
scaling B2-B3 by 2 pi/sqrt(x), its value is
L(.75 log L-log 2-1.5)-q^2+q-.5-.28 pi.
Use .75 log L-log 2-1.5>.473 at L=35, q^2/L<.235 throughout (decreasing),
and q-.5-.28 pi>0. For B1-B3 the corresponding value is
L(2 pi*1.2325-log 2-1.5)-q^2+q-.5-2 pi*1.465 log L-.28 pi;
use log L/L decreasing and <.102. These comparisons are against the stated
Lee–Nosal theorems, not against their finite underlying computations:
Büthe is much stronger where available (up to 10^19). Change from
Lee–Nosal (12)–(16): average in log x twice and apply the exact multiplier
before summing; track the 1/gamma^3 tail via the main N term instead of
the original hard split on the additive first difference.


## Exact-transform refinement (B4)

For all L>=35, an improved bound with the same domain and no numerical zero
table is
```
v=L/2-log L,
B4(x)=sqrt(x) [(v^2+1.846 v+1.28+L)/(2 pi)+.14].
```
Indeed keep f(delta gamma)=sinc^2(delta gamma/2) instead of replacing it by
min(1,4/(gamma delta)^2). The finite hyperbolic-sine correction is unchanged.
Compare sum_{gamma} f(delta gamma)/|gamma| to its density integral starting
at A=12, where N(A)=0. Write y=delta t, delta=L/(2 pi sqrt(x)), so the
main integral is
```
(1/pi) int_{A delta}^infty f(y)(log y+v) dy/y.
```
Subtract 1_{0<y<=1} in the integrand. The contribution of that indicator
is [v^2-log(A/(2 pi))^2]/(2 pi). The two regularized moments are
```
J_0=int_0^infty [f(y)-1_{y<=1}]dy/y = 3/2-gamma_E < .923,
J_1=int_0^infty [f(y)-1_{y<=1}]log y dy/y
    = (3/2-gamma_E)^2/2 + 5/8 - pi^2/24 < .64.
```
To prove this, expand pi/[Gamma(3-s)sin(pi s/2)] minus 1/s at s=0
using the Mellin transform in Intervals.md. Derivatives under the integral
after subtraction are dominated since |f(y)-1|<=y^2/12 near zero and
f(y)<=4/y^2 for y>=1. Here the log-Gamma derivative and its derivative at 3
are 3/2-gamma_E and pi^2/6-5/4, respectively, by the gamma recurrence.
For the removed integral on [0,A delta], |f(y)-1|<=y^2/12 and
|log y+v|<=|log(y/(A delta))|+log(A/(2 pi)), giving error <10^-10
after division by pi.

The R(T) integration-by-parts error bound, besides 2 M(A) f(delta A)/A,
is at most .56(log A+1)/A plus
```
.56 delta int_{A delta}^infty |f'(y)|/y log(y/delta) dy .
```
Both integrals int |f'|/y and int |f'| log^+y/y are <1 by the derivative
bounds in Intervals.md. Thus this extra term is <.000002 using
delta<1.5e-7. Combining the constant
2 M(A)/A+.56(log A+1)/A-log(A/(2 pi))^2/(2 pi)<.130 with the
hyperbolic sine correction <.001 and the exponentially small
factors as in B3 gives .14. Therefore B4 holds and B4<B3
(the coefficient in B3 after putting s=v+log 2 is 1+2log 2>1.846,
and its constant is log^2 2+log 2+.5>1.28).
Include B4 in Upsi. This sharpening uses the whole zero-density integral
of the exact smoothed profile, not a specialization outside a source range.


## Parabolic logarithmic average (B5)

The parabolic test in Intervals.md also sharpens the pointwise error.
For L>=35, write v=L/2-log L as before. The bound
```
B5(x)=sqrt(x) [(v^2+1.662 v+1.148+L)/(2 pi)+.14]
```
is strictly stronger than B4 and thus than the earlier bounds there.
Average psi(x exp(±delta+delta U)) for U with density (3/4)(1-u^2)
on [-1,1] and delta=L/(2 pi sqrt(x)). The averages are again
monotone brackets, with smooth main-term error <=x delta exp(2delta)
by the mean-zero symmetry of U; no strict convention at jumps is used.
The zero multiplier is exp(±rho delta) phi(delta(gamma-i/2)) under RH,
where phi(y)=3(sin y-y cos y)/y^3, and phi(0)=1. Treat the real-axis
multiplier through its absolute Mellin moments, not as nonnegative.

For 0<s<1, the signed Mellin transform is
```
int_0^infty phi(y)y^(s-1)dy = 3 Gamma(s) cos(pi*s/2)/((1-s)(3-s)).
```
Proof: use the cosine transform of the parabolic density, insert an
exp(-epsilon y) factor, then apply the gamma integral and dominated
convergence at epsilon->0; the bound for the inner expression is
Gamma(s)|u|^-s, integrable against the density. Subtract 1/s, and use
the constant and linear Taylor terms at s=0. The resulting signed
regularized moments are 4/3-gamma_E and
13/9-(4/3)gamma_E+gamma_E^2/2-pi^2/24. To make the absolute moments,
add twice the integrals of max(0,-phi(y))/y and its product with log y.
They vanish below 2, since phi(y)>=1-y^2/10 there. The directed midpoint
code parabola.py covers [2,100] and adds variation remainders h/2 times
1.7 and 3, respectively. To see these constants, on [2,infty) use
int |f'| <=4 and int |f'|log y<6.1 for f=4 phi/3 (as in Intervals.md),
so int |phi'|/y<=1.5 and int |phi'|log y/y<2.2875; then bound
int |phi|/y^2 <= (3/4) int_2^infty (4/y^4+4/y^5)<.18 and
int |phi|(1+log y)/y^2<.35 by integrating these power/log terms.
The tails after 100 use |phi(y)|<=3/y^2+3/y^3. Thus the absolute
regularized moments are bounded by .831 and .574, respectively.
The positive constant and linear terms are replaced by these upper
bounds because v>=0.

Apply the same density and R decomposition as for B4 to
|phi(delta gamma)|/|gamma|. Since |phi|<=1 on the real axis, the
A=12 discrepancy constant .130 is unchanged. Bounds
int |phi'|/y <2 and int |phi'|log^+(y)/y<2 follow from
|phi'|<=y/5 through 2 and 3/y^2+9/y^3+9/y^4 thereafter,
so the derivative discrepancy term is <.000003.
The removed integral on [0,A delta] is <10^-10 from |phi(y)-1|<=y^2/10.

For the imaginary shift, when |v'|<=delta/2,
|phi'(y+i v')|<=3 exp(delta/2) min(1,4/y^2): for |y|<=2
use the exact integral of the absolute density times |u|<=1;
for |y|>=2 differentiate the sine/cosine quotient and use
|y+i v'|>=|y| and |sin|,|cos|<=exp(delta/2).
Integrating along the imaginary displacement adds at most
(3delta/2) exp(delta/2) times the B3 hard-clipped zero sum without
sinh or main shift. That sum is <L^2 by the two N estimates there.
All exponentiation/shift correction terms are <.001 in total
using delta L^2<.00018 and delta<1.5e-7. Thus .14 covers the
.130 discrepancy and the tiny correction terms. This reuse of the
parabolic window is a distinct signed-Fourier route to PNT, not an
assumed numerical zero-table improvement.

## Complete signed psi and theta functions

Take the minimum Upsi of all applicable B1,B2,B3,B4,B5 and .94 sqrt(x) from
above, with exact finite sum for 2<=x<=11 as needed. Then Epsi<=Upsi/x.
For theta let K=floor(log x/log 2), and D=psi-theta=sum_{k=2}^K theta(x^(1/k)).
Valid lower and upper bounds D_-,D_+ are formed by summing
max(0,y-B2(y)), y+B2(y) at y>=2657, and exact finite sums at y<2657.
The upper bound can also be intersected with Platt–Trudgian Cor. 2.
Intersect [-Upsi-D_+,Upsi-D_-] for theta-x with [-B2,B2] if x>=2657
and [-1.95sqrt(x),-.05sqrt(x)] on the Büthe domain >=1423.
Outside those latter domains the psi/prime-power interval still applies.
For example at L>=35, D_+/sqrt(x)<=1.00000075+3 exp(-35/6)<1.01,
and B3+D_+<B2, including the asymmetric improvement. No interpolation
in x is used.

## New signed transform for pi

J(x)=sum_{p^k<=x}1/k=pi(x)+Q(x), Q=sum_{k=2}^K pi(x^(1/k))/k. Under RH,
partial summation with ordinary endpoints gives
```
pi(x)-Li2(x) = Mpi(L) +(psi(x)-x)/L - Q(x)+ I0(x)+Ib(x),
Mpi(L) = 2/log 2 - c(1/log 2 - 1/L),
Ib = integral_2^x b(t)/(t log^2 t)dt, 0<=Ib<.25.
```
I0 is the integrated zero term. With u=log t, integrate each term
int exp(rho u)/u^2 du by parts once using rho^-1. Absolute value is bounded
by Z [A(L)+A(log 2)+2 int_{log 2}^L exp(u/2)/u^3 du] for A(u)=exp(u/2)/u^2.
Justify passage to the sum by the formula for Psi1 and the resulting absolute
Z majorant. For L>=8, A'(u)=(u/2-2)exp(u/2)/u^3>=2 exp(u/2)/u^3 on u>=8.
On [log 2,8], the integrand decreases up to 6 then increases, and is <4.4
at both endpoints; A(log 2)<3. Thus |I0|<.094 sqrt(x)/L^2+3.2
(use interval length<7.31).
The unintegrated pointwise term retains the full sharpened bound Upsi,
while the integrated oscillation costs O(sqrt(x)/L^2), not O(sqrt(x)).
The prime power term is signed, not lumped immediately into a symmetric error.

With I=.094 sqrt(x)/L^2+3.2 and Q in [Q_-,Q_+], the resulting interval is
```
[Mpi-Upsi/L-Q_+-I,  Mpi+Upsi/L-Q_-+I+.25]
```
for pi-Li2, L>=8. For Q_± use the Schoenfeld envelope for each y>2657,
intersected with the signed Büthe bound through 10^19, and exact finite
count at smaller y (or max with zero below). For any x>=2 one may also
intersect with the imported Schoenfeld and Büthe intervals where valid,
after adding li(2). Below L=8 there is coverage for all x>=2 by Büthe.
Taking maximum absolute endpoint and multiplying by L/x yields Epi.
There is no unproved prime table hypothesis: every finite endpoint sum
is defined by trial division, or can be bounded by the independent source.

A smooth envelope for x>=exp(24) is useful for comparisons and Ramanujan.
For the following prime-power bounds there is no need to import a
computed sign of theta or pi, nor a prime-count table. For all y>=2,
theta(y)<=2 log(2) y by elementary induction on floor(y): the primes
strictly between m and 2m divide binom(2m,m), and the primes strictly
above m+1 up to 2m+1 divide binom(2m+1,m). The central binomial coefficients
are at most 2^(2m-1) (the two adjacent terms together are at least as
large as the middle term) and 2^(2m) (two equal middle terms), respectively.
For the even interval include the endpoint 2m when prime (the same
divisibility holds), and start at m=1, yielding both induction steps.
Thus splitting pi(y) at sqrt(y) gives
pi(y)<=sqrt(y)+4 log(2) y/log y < 4 y/log y.

At u=log y>=12 use the signed pi formula above, keeping only Q>=0:
```
pi(y) <= li(y) + sqrt(y)[u/(8 pi)+.094/u^2]+5.
```
For u>=12, li(y) <= 1.113 y/u, and for u>=17.5, li(y)<=1.067 y/u.
These anchors are rational checks in bounds.py; propagate by derivatives
b(1-1/u)>1 for each stated b and domain. The additive error scaled by u/y
is at most exp(-u/2)[u^2/(8 pi)+.094/u]+5u exp(-u), decreasing there.
Hence pi(y)<=1.13 y/u from u>=12, and <=1.07 y/u from u>=17.5.
No circular inference: these are bounds on pi obtained after dropping Q
entirely from the upper side, used independently at the smaller prime-power
arguments. For L>=24, sum through k=5 and then bound each term with k>=6:
```
Q(x)<=sqrt(x)/L [1.13+4(e^(-L/6)+e^(-L/4)+e^(-3L/10)
                               +(L/log 2)e^(-L/3))]
     <1.3 sqrt(x)/L.
```
Use 1.07 in place of 1.13 for L>=35, giving <1.1 sqrt(x)/L.
The nonconstant terms decrease throughout, and guarded anchors are in bounds.py.
For L>=35 also Q>=.99 sqrt(x)/L: theta(sqrt(x))> .99 sqrt(x) by
B2 and the decreasing upper bound h^2 exp(-h/2)/(8 pi) for h>=17.5,
and pi(y)>=theta(y)/log y. This lower bound retains a signed advantage.
The term Mpi(L)-li(2) has absolute value <1 for L>=8 (only needs two
anchors since it increases with 1/L), hence the total absolute
constant allowance including 3.2 and .25 is <5.
In particular for L>=24,
```
|pi-li| <= Upsi/L + sqrt(x)(1.3/L+.094/L^2)+5
        <= sqrt(x)[(L-log L)/(8 pi)+1.3/L+.094/L^2]+5
        < sqrt(x)L/(8 pi).
```
For the strict comparison scale by sqrt(x) and use
log L/(8 pi) increasing, the three added terms decreasing, and check
L=24. At L>=35 one has the stronger signed estimates
```
-p_-(x) <= pi(x)-li(x) <= p_+(x), 
p_- = B5/L + sqrt(x)(1.1/L+.094/L^2)+5,
p_+ = B5/L + sqrt(x)(-.99/L+.094/L^2)+5.
```
These are pointwise bounds and can be intersected with all earlier valid ones.
The same normalization addition li(2) applies to either comparison.
 Intervals.md gives a
separate non-telescoped difference version, avoiding the constant 3.2.

For 1<x<2 all the step functions are zero, so the small remaining
domain is trivial: Epsi=1 and Epi=|Li2(x)|/(x/log x).


The directed pointwise illustrations in comparisons.out are comparisons of
bounds, not samples used to prove their uniform validity. For example at
L=44 the B5 psi and transported theta bounds are at most .923 and .937 of
Lee–Nosal B2, respectively, and the new symmetric pi-li bound is at most
.858 of Schoenfeld at that x. At L=100 the respective numbers are .939,
.942 and .899. These ratios approach 1 for the PNT bounds as L increases:
the gain is in lower-order terms, not a smaller leading 1/(8 pi).
