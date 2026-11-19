# Mertens products and prime sums

Use H (the packet's PsiMajorant) or S (Re rho<=7/8, derived from H
or taken from the literal QRH Thm 1.1). See density.md. General
finite-RH, Chebyshev and prime-sum results used below retain original
trust labels. All domains are real, and all logs are natural.

Put L=log x, and define three signed deviations
* d_Q=log Q(x)-gamma-log L; d_P=-d_Q for the log-normalized P;
* d_1=sum_(p<=x) 1/p -log L-M;
* d_2=sum_(p<=x) (log p)/p -L+B3.

M,B3 are as in Dusart Thms 5.6–5.7 (PDF pp.17–18). Define
J(x)=.0462/sqrt(x)+3.1e-12*x^(-1/8)+1.84/x, h_0(L)=1/L+1/L^2.
Use the following upper spill bounds for x>=5e6, with u=L/2,
epsilon=20.83/u^3, eta=.000081, g=1-1/u+2/u^2:
  V_+(x)=[(1+eta)g+eta+epsilon]/(sqrt(x)*L)
             +(.66*x^(-2/3)+3.37*x^(-3/4))/L,
  W_+(x)=(1+2eta+epsilon)/sqrt(x)+.66*x^(-2/3)+3.37*x^(-3/4).
Let B(x) be any valid bound for |psi(x)-x|. Then for every x>=5e6,
  |d_Q|, |d_1| <= U_0(x):=B(x)/(x L)+h_0(L)J(x)+V_+(x),
  |d_2| <= U_1(x):=B(x)/x+J(x)+W_+(x).
Thus each of the two relative product errors is at most exp(U_0)-1;
the negative log side has error at most 1-exp(-U_0).
You may take the pointwise minimum of these envelopes and the
finite/whole-ray outputs below.

Valid B choices:
- CH2 Cor. 1.3 (PDF p.3): 1.048e-12*x+113.67*sqrt(x) for x>=1.
  One may also use the T-dependent bound in ramanujan.md.
- CH2 Lemma 9.2 (PDF p.35): signed bounds
  -.751*sqrt(x)<psi(x)-x<.791*sqrt(x) on [10^4,10^13].
- H: x^(7/8)*L^2/64 for L>=200.
- S: x^(7/8)*D(L) for L>=185 where D is in density.md.
  The density-free fallback .0045 x^(7/8)L^2 from density.md is
  also valid on L>=185 and suffices for the baseline comparisons.
  In addition under S with density, for L>=185 one may replace J
  by min(J,J_D):
  J_D=.0462/sqrt(x)+1.84/x+3.1e-12*x^(-1/4)
       + x^(-1/8)/H0 * [.0106 L/(L-92)+651 exp(-3L/40)],
  H0=3*10^12.

### Consequences and comparisons

**Signed finite range.** On the entire real interval [2,10^13],
  d_Q > .003/(sqrt(x)*L), d_1 > .003/(sqrt(x)*L),
  d_2 > .10/sqrt(x).
In particular the Q error is positive and the P error negative
in this range (the two normalized products themselves are reciprocals).
For x>=5e6 up to 10^13 a finer lower bound for d_Q,d_1 is
  (c(x)-.751)/(sqrt(x)*L)-h_0(L)J(x),
where c(x)=(1-epsilon)(g-6/u^3-1/(2sqrt(x)))-epsilon; for d_2 it is
  (1-2epsilon-.751)/sqrt(x)-J(x).
The C certificate proves the constant lower bounds through 10^8
and upper bounds d_Q,d_1<1.70/(sqrt(x)*L), d_2<1.88/sqrt(x)
on [10^4,10^8] (the finite primes/left-limit segments are included).

**Whole-ray baseline improvements.** Each nonblank entry gives
a strict upper bound on the corresponding absolute error for *every*
x at or above the entry's onset (not just until the next row).
First two columns divide by L^3, third also divides by L^3,
and fourth divides by L^2. Use the smaller value if rows overlap.
These are proved with H (or S and the density bound to replace H
beyond e^200); they do not require full RH.

|Onset x|abs log error d_Q|both relative product errors|abs d_1|abs d_2|
|--:|--:|--:|--:|--:|
|2,278,381.78| — |.199995| — | — |
|2,278,382|.19998|.199995| — | — |
|2,278,382.30| — | — |.19999| — |
|912,565| — | — | — |.29900|
|2,300,000|.19850|.19852|.19850| — |
|3,000,000|.19850|.19852|.19850|.21200|
|5,000,000|.15020|.15021|.15020|.16180|
|10^7|.11970|.11971|.11970|.12740|
|2*10^7|.08880|.08881|.08880|.09490|
|3*10^7|.08820|.08821|.08820|.09350|
|5*10^7|.07110|.07111|.07110|.07580|
|10^8|.067|.067|.067|.067|
|10^13|.034|.034|.034|.034|
|exp(200)|.00036|.00036|.00036|.00036|

At 912560<=x<912565 retain the literal
Dusart .3/L^2. On the original product and d_1 domains the
row at the original onset already strictly beats .2/L^3, and the
stronger later rows extend whole-ray improvements. Original
Dusart Thms 5.6–5.9 (PDF pp.17–20) are not discarded.

**Sharp onsets for the original tolerance constants.** This is
a second way to improve the original starts, as opposed to changing
coefficients. For products jointly, d_1, and d_2 respectively, the
smallest start of a closed whole ray with the original non-strict
tolerance (.2/L^3, .2/L^3, .3/L^2) is the unique root described
below. The exact brackets are respectively
  (2278381.71,2278381.72),
  (2278382.10,2278382.20),
  (912559.98,912560.00).
For the first two let p=2278379, q=2278421 (consecutive primes)
and set A=exp(-gamma) Q(p), r1=sum_(prime<=p) 1/prime-M.
Solve L^2(A-L)=.2 and L^3(r1-log L)=.2, respectively,
on [p,q). In this gap d_Q>0, hence the Q relative error
controls the absolute P error as well. For the third use the
consecutive primes p=912559, q=912581, and solve
L^2(r2-L)=.3 with r2=sum_(prime<=p) (log prime)/prime+B3.
These functions are strictly decreasing throughout the respective
gaps. Their derivatives in L have signs determined by
2A-3L, 3(r1-log L)-1, and 2(r2-L)-L. Each negative sign is
checked at the left endpoint and persists. The enclosure
tests use emitted dyadic anchors of the finite sieve and
endpoints.py; they also prove the three earlier strict rows
at 2278381.78, 2278382.30 and 912565. From each local root
up to the corresponding original onset the monotonic gap
bound applies. Beyond it the original baseline and our
whole-ray envelope apply; for strict rows beyond their old
sieve threshold use the C certificate and the analytic tail.
An open left neighborhood of each root violates the old
tolerance, proving sharpness even for noninteger arguments.
This local onset conclusion *at the old constants* can also
use the admitted original whole ray without assuming H or S.

**Power-decaying profile.** On x>=exp(200), under S, each relative
product error and |d_1| is <.019851*x^(-1/8)/L, and |d_2| is
<.01985*x^(-1/8). The full expressions U_0,U_1 with D(L) and J_D
are sharper asymptotically: the limiting coefficient in these
power scales is at most .0106*(1+1/H0). For example the coefficient
in the given H input is L^2/64 at the psi level; merely inserting H
into the nonspectral integral for Mertens would retain its large
L^2 and would pay an additional tail of approximately 8/L.
With the spectral estimate the tail does not cause this loss.
The constant power profiles are uniformly stronger than .2/L^3
or .3/L^2 on their complete ray: after multiplying by the respective
log powers use the decreasing L^2 exp(-L/8) and the bound at L=200.
For the version using only H in B, same proof with L^2/64 in place
of D(L) gives a weaker but still power-decaying profile.

### Proof of the spectral tail

Let E(t)=psi(t)-t, and S_a(x)=integral_x^infinity E(t)t^(-2-a)dt
for a>=0. Then |S_a(x)|<=x^(-a)J(x) for x>=100. Use the classical
formula in Dusart (2.1), PDF pp.3–4, away from prime powers.
A zero rho contributes -x^(rho-1-a)/[rho(1+a-rho)] after integration.
The magnitude of the constant/trivial terms is bounded by
log(2*pi)<1.84 pointwise for t>=100: their sum is
-log(2*pi)-.5 log(1-t^(-2)), with positive correction smaller than
log(2*pi). The strip and |1+a-rho|>=|1-rho| are used here.

Here are full interchange details. Put z=log t on a compact interval.
The Rosser N(T) bound in FKS Lemma 2.1/Remark 2.2 gives O(log T)
zeros in any unit interval near height T, counting multiplicities.
For a dyadic block T<=|Im rho|<2T, inner products of exp(rho z)
on that compact interval are O(min(1,1/|gamma-gamma'|)) by direct
integration, uniformly for 0<Re rho<1 (the bound is 1 at equality
of the ordinates). For each rho the sum of that majorant over the
block is O(log^2 T), by grouping |gamma-gamma'| into unit bands.
The block has O(T log T) zeros and |rho|>=T. Thus the square norm
of any partial block with coefficients 1/rho is O(log^3(T)/T).
The dyadic norms are summable, giving L^2 convergence of the
symmetric truncation. The limit agrees a.e. with Dusart (2.1)
(use the subsequence principle for L^2, or summable norm tails).
Multiplication by the bounded integration kernel on a compact
interval is continuous in L^2. The integrated zero series then
converges absolutely by the zero count, with coefficients
O(1/gamma^2); the upper endpoint can tend to infinity by domination
and the strip. Absolute integrability of the arithmetic tail for
Fubini follows from H, density.md, or the FKS Cor. 1.4 estimate.
Jump conventions do not affect these integrals.

For |Im rho|<=H0 the finite-RH computation applies. The sum of
1/(|rho||1-rho|) over these zeros is <.0462. To see this,
compare CH2 (B.9), PDF p.46 (locator: (B.9), Lemma B.9 proof),
at s=0 and at s=1 after subtracting the pole, and use
zeta'/zeta(0)=log(2*pi) (also CH2 proof near PDF p.35;
alternatively get it from the constant in Dusart (2.1)).
The finite part of zeta'/zeta at 1 is gamma (as recorded in CH2
Prop. 9.1 proof, PDF pp.34–35). This yields
  sum_rho 1/[rho(1-rho)] = 2+gamma-log(4*pi).
For clarity the digamma difference used is Psi(3/2)-Psi(1)=2-2log 2.
Indeed differentiate in s the limit
  int_0^m t^(s-1)(1-t/m)^m dt
    = m^s m!/[s(s+1)...(s+m)] -> Gamma(s)
by integration by parts and dominated convergence (also for the
derivative). The difference of the log derivatives at 3/2 and 1
is lim_m [2+2(H_(m+1)-H_(2m+3))]. All summands
1/[rho(1-rho)] have positive real parts, since the real part
of rho(1-rho) is beta(1-beta)+gamma^2. On the critical line
they are already the absolute weights. At high ordinates
>H0, |rho||1-rho|>=gamma^2, and twice CH2 Lemma B.5 is
<3.1e-12 at H0. These comparisons are in check.py.
For J_D split the high zeros at beta=.75: those below have
x^(beta-1)<=x^(-1/4); for the rest reuse the reciprocal-ordinate
sums of density.md and one extra 1/H0 factor. No truncation
error is involved in this absolutely convergent tail.

Now put D0=sum_(n<=x) Lambda(n)/(n log n)-log L-gamma
and D1=sum_(n<=x) Lambda(n)/n-L+gamma. Partial summation gives
 D0=E(x)/(x L)-int_x^infinity E(t)t^(-2)(1/log t+1/log^2 t)dt,
 D1=E(x)/x-S_0(x).
Their constants follow from Dusart Thms 5.6–5.7 and convergence of
the higher prime-power terms (dominated by integer p^-2 sums).
Use the log kernel representation int_0^infinity (1+a)t^(-a)da.
Fubini and the shifted S_a bound give h_0(L)J(x), rather than
integrating a pointwise majorant of E(t) and losing its cancellation.

### Spill, signed bounds and whole-ray comparisons

Let V=sum_(p^k>x,k>=2) 1/(k p^k), U=same but with p<=x, and
W=sum_(p^k>x,k>=2) log(p)/p^k. Direct expansion of the Euler factor
and constants shows d_Q=D0+U, d_1=D0+V, d_2=D1+W.
All spill terms are positive. Use theta(t)<(1+eta)t
as recorded in Dusart Prop. 4.4 proof (PDF p.13); the same proof
records theta(t)<t up to 10^11. Dusart Thm 4.2 gives
theta(t)>t(1-20.83/log^3 t) for t>=2.

For y=sqrt(x) and f(t)=t^-2/log t, integrate (1/2)dtheta against f
over (y,infinity). The main integral I satisfies
 I=1/(yu)*int_0^infinity e^-v/(1+v/u)dv,
so it lies between (g-6/u^3)/(yu) and g/(yu) by finite geometric
identities and integration of v^j e^-v. Partial summation,
using the lower bound at y and upper bound in the integral,
gives V2 <= .5[(1+eta) I+(eta+epsilon)y f(y)].
For W2 use t^-2 instead and no factor 1/2. For W3 the same proof
uses t^-3 at threshold x^(1/3), giving the coefficient
.5(1+eta)+eta+20.83/(L/3)^3 <.66. For k>=4 split p at
q=x^(1/4). Below q, each tail sum of p^-k is <=2/x
(strict threshold p^k>x); above q use the geometric factor
1/(1-1/q) and integrate theta(t)<(1+eta)t against t^-4.
Total <=[(1+eta)(2+4/(3(1-1/q)))]x^(-3/4) <3.37x^(-3/4).
For k>=3 the unweighted spill is at most the weighted spill/L
because k log p>L. These prove V_+,W_+.

To lower bound U for x<=10^13, keep only squares y<p<=x.
Here theta(y)<=y by the original bound up to 10^11. With the
lower bound for theta(t) otherwise, integrate to x to get
.5[(1-epsilon) int_y^x f -epsilon*y f(y)]. The omitted
tail int_x^infinity f is at most 1/(xL). This is c(x)/(sqrt(x)*L).
W>=W2 >=(1-2epsilon)/sqrt(x) by the same integration to infinity
with t^-2. The factors c and 1-2epsilon increase for x>=5e6:
epsilon decreases, and g-6/u^3 increases (derivative
(u^2-4u+18)/u^4>0); the factors multiplied are positive.
For 5e6<=x<=10^13, bound J(x)*sqrt x by its high-ordinate
component at 10^13 and its 1.84/sqrt x term at 5e6, and
1+1/L at 5e6. The scalar checks prove the signed margins on
this entire interval by CH2 Lemma 9.2. The sieve covers below.

For x>=10^8, sqrt x W_+(x)<=1.092 and V_+<=W_+/L;
every positive nonconstant term of sqrt x W_+ decreases.
Through 10^13 the signed bound gives U_0<=1.94/(sqrt x L)
and U_1<=1.94/sqrt x, using extrema of the individual terms
just as above; L^2/sqrt x decreases. Above 10^13 up to e^200
use B/x<=1.048e-12+113.67/sqrt x; after multiplying the
log bound by L^3 and weighted bound by L^2 all exponential
terms decrease, and the constant B/x term costs at most
1.048e-12*200^2. For L>=200 with H, the new term L^4 exp(-L/8)/64
decreases; the S variant is smaller by density.md.
This proves .067,.034,.00036 by check.py, using
exp(v)-1<=v/(1-v) for 0<=v<1. For the constant power profile,
multiply U_0 by L*x^(1/8) and U_1 by x^(1/8); with B=x^(7/8)D(L)
all resulting positive summands decrease for L>=200 (use W_+/L
for V_+). The checks at 200 prove the displayed coefficients
including the relative exponential correction. Formula J_D
proves the asymptotic coefficient limit.

### Independent finite certificate

sieve.c certifies exactly all finite table rows through N=10^8
and the finite signed/normalized bounds. It builds an odd
Eratosthenes sieve: a composite has a prime factor at most its
square root and is marked when that factor is processed. No prime
table or floating point is used. On each interval [p,q) between
consecutive primes all sums/products are constant. The smooth
subtractions log log x or log x increase, so the checker uses
the left endpoint for upper d and q^- for lower d, and the
opposite endpoints for positive multiplying factors. Interior
onsets use the larger left endpoint. At N the last closed
endpoint is included and N is composite.

To check the local roots pipe the sieve output through endpoints.py.
Each stored bound is an integer interval in units 2^-60.
For log(A/B) with 1<=A/B<=2 use the first 20 terms of
2 sum z^(2j+1)/(2j+1), z=(A-B)/(A+B)<=1/3. Rounding down z
and z^2 incurs respectively <=1 and <=5/3 units. In the
power recurrence the error is <=(previous error)/9+14/9
units, hence <=2 units in each power. The flooring of each
division adds <=1. Twice the summed error plus the
geometric remainder is <128 units (even twice 20*3+1<128).
Scale other ratios by powers of 2; compare logs at both endpoints
for log log. The gamma interval uses
 H_m-log m-1/(2m) <= gamma <= H_m-log m-1/(2m)+1/m^2.
Indeed the error is the sum over k>=m of the trapezoid error
integrating 1/t on [k,k+1]. It lies between 0 and
sum_(k>=m)1/(6k^3)<1/m^2, since the trapezoid error is at most
sup |f''|/12 (integrate a quadratic bound for the chord error).
This proof also supplies the scalar gamma enclosure in check.py.

Compute M=gamma-C and B3=gamma+F, where
C=sum_p [log(p/(p-1))-1/p] and F=sum_p log p/[p(p-1)].
Their positive omitted tails at N are at most
1/(12N),1.02/N respectively: for F use
(1+3*20.83/log^3 N)/(N(1-1/N)) by theta partial summation;
for C multiply the F bound by 1/(2log N).
All these comparisons are independently asserted in check.py.
Arithmetic uses signed __int128. For range safety note all
raw log numerator/denominator inputs are <=32*2^60; the
general scaled multiplications explicitly check overflow, and
there is a clean undefined-behavior-sanitizer replay (work notes).
No CRT libm, floating approximation, or checked table of primes
is a premise. Relative-error caps from logarithmic rows use
exp(v)-1<=v/(1-v) checked in check.py.
