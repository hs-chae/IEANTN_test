# Mertens products and prime sums

For real x>1 put u=log x. The counted primes and prime powers
include equality. The four errors treated here, in order, are
[
 |e^\gamma u P_{raw}(x)-1|,quad
 |e^{-\gamma}Q_{raw}(x)/u-1|,quad
 |\sum_{p\le x}1/p-\log u-M|,quad
 |\sum_{p\le x}(\log p)/p-u+B_3|.
]
Here M=gamma+sum_p(log(1-1/p)+1/p), and
B_3=gamma+sum_p log(p)/(p(p-1)) (Dusart, original PDF pp.17–18,
Theorems 5.6–5.7). Gamma is Euler's constant. The other two are
reciprocals after normalizing; the four are not independent results
from unrelated trials.

## Direct weighted transfer and its cancellation

Let Z_1(u)=sum_(n<=e^u) Lambda(n)/n -u+gamma and
Z_0(u)=sum_(2<=n<=e^u) Lambda(n)/(n log n)-log u-gamma. Then
[
 Z_1=g(u)-\int_u^\infty g(v)dv,\qquad
 Z_0=Z_1(u)/u-\int_u^\infty Z_1(v)\,dv/v^2.           \tag{M1}
]
For the first identity, partial summation gives
sum Lambda(n)/n=1+g+u+int_0^u g. The constant 1+int_0^infty g=-gamma
follows by letting s tend to 1 in the Euler identity in spectral.md:
the Laurent constant of -zeta'/zeta is -gamma (also used in
CH2 Proposition 9.1 proof, eq. (6.7)). The existence of the
integral follows from the spectral tail. For the second identity,
the Stieltjes derivative of Z_0 is (1/u) times that of Z_1.
Both normalized limits at infinity are zero: for Z_0 this follows,
for example, from Dusart Theorem 5.6 and its constant formula,
subtracting the prime-power tail from log Q_raw. Integrate by
parts over (u,infinity), so the value at u is right-continuous.

For a zero with beta<1 the two contributions to Z_1 in (M1)
combine to e^((rho-1)u)/(1-rho). In the tail of the second
identity, the additional denominator can be recovered despite
the factor 1/v^2: for Re lambda>0,
[
 \left|\int_u^\infty e^{-\lambda v}\,{dv\over v^2}\right|
 \le {e^{-u\Re\lambda}\over |\lambda|u^2}.
]
Use 1/v^2=int_0^infty t e^(-t v)dt and |lambda+t|>=|lambda|.
Combined with absolute summability after integration, this bounds
the absolute tail in (M1) by S_b(u)/u^2. The trivial part of
Z_1 is bounded by 2e^(-u) (the -log(2pi) contributions cancel).
As in spectral.md, the formula under integration ignores the
countable jumps but the endpoints themselves use the actual
right-hand values. This is an advantage over absolute integration
of the original psi majorant; no loss by a factor about 1/a
is needed on the leading endpoint term.

Use W^+=W^-=min(E_b+S_b, CH2 weighted half-widths); on
10^4<=x<=10^13 one can also take W^-<=.751 e^(-u/2)+S_b by
the signed CH2 Lemma 9.2. Then [-W^-,W^+] bounds Z_1,
and Z_0 lies in [-Z^-,Z^+] with
Z^±=W^±/u+S_b/u^2. All CH2 original choices for T in
Corollary 1.2 can be included for both ψ and the weighted sum;
the executable uses H and an adaptive T. No speculative weighted
interpretation of the numerical line (9.1) in CH2 is needed.


A further common branch uses CH2 Proposition 9.1 uniformly for
1<sigma<=100. Write a_sigma=sigma-1. The proposition bounds
the tail sum_(n>x) Lambda(n)n^(-sigma) after dividing by
e^(-a_sigma u), with center (pi/T)coth(pi a_sigma/T)
and half-width c_T=pi/(T-1)+C_T e^(-u/2). Partial summation
with g and Fubini give
\[
 Z_0(u)=-\int_1^\infty\left[\sum_{n>x}\Lambda(n)n^{-\sigma}
                      -e^{-a_\sigma u}/a_\sigma\right]d\sigma.
\]
Indeed integration of the signed difference gives
-g(u)/u+int_u^infty (1/v+1/v^2) g(v)dv, the
negative of the Z_0 Stieltjes transfer. The integrals converge
absolutely using the spectral bound and this partial summation.
For sigma>=100 even |g|<=1 gives bound 3e^(-a_sigma u)
on the difference by the same summation. The center
shift is nonnegative and at most pi^2 a_sigma/(3T^2).
Hence Z^+ may also take c_T/u+3e^(-99u)/u and Z^-
may take that plus pi^2/(3T^2 u^2), for any eligible T.
This avoids the S_b/u^2 term when this original spectral
information is better. It has the same pi/(T-1) floor
after multiplying by u, so it does not reverse the
matched strict improvement.

For comparison, using D02 directly with absolute integration,
|Z_1| is bounded on u>=200 by
[
 {e^{-a u}\over64}
 [u^2+u^2/a+2u/a^2+2/a^3],\qquad a=5/32.
]
For |Z_0|, partial summation against ψ instead gives
[
 {e^{-a u}\over64}[u+u/a+1/a^2+1/a].
]
To get the latter use endpoint g(u)/u and kernel 1/v+1/v^2
in the tail. The spectral method saves **two logarithms** in
both families of weights even relative to these D02-only
transfers, and works below e^200. Raw D02 does not beat the
inferred D02 spectral branch anywhere on its own domain:
e.g. .2332 e^(-5u/32)<u^2 e^(-5u/32)/64 for u>=200.

## Prime powers retained with their signs

Define
\[
 U_j(x)=\sum_{k\ge2}\sum_{p>x^{1/k}} w_j(p,k),\qquad
 w_0=1/(k p^k),\quad w_1=(\log p)/p^k;
\]
let T_0(x)=sum_(k>=2,p>x) w_0 and D_0=U_0-T_0. All these are
nonnegative and U_0<=U_1/u. The signed errors are exactly
[
 \log(e^{-\gamma}Q_{raw}/u)=Z_0+D_0,qquad
 \sum_{p\le x}1/p-\log u-M=Z_0+U_0,qquad
 \sum_{p\le x}\log(p)/p-u+B_3=Z_1+U_1.               \tag{M2}
]
Thus tails are not an extra independent symmetric uncertainty
for both ends. For an interval [l,h] on the first signed log error,
the two product bounds, in the order above, are
max(1-e^(-h),e^(-l)-1) and max(1-e^l,e^h-1).

Here are explicit signed prime-power bounds valid for x>=2.
Let c=1.0001 (Dusart p.13, proof of Proposition 4.4 has a
slightly better value), and t(v)=max(0,1-delta(v)), where
delta(v) is the minimum of the eligible Dusart Theorem 4.2
bounds eta_k/v^k for arguments >=e^v. Use its k=0 bound for
all v>=0. Then t is nondecreasing, theta(y)<=cy, and
theta(y)>=t(v)y for all y>=e^v. For k=2 or 3, put v=u/k and
Y_k=e^(-(k-1)v). Applying Stieltjes summation over p>e^v,
the two bounds for the w_1 tail are
\[
 Y_k[,t(v)k/(k-1)-c,]_+,qquad
 Y_k[c,k/(k-1)-t(v)].
\]
The same formulas work at k=4. For w_0 use the decreasing
weight f(y)=1/(k y^k log y) in the Stieltjes integral. The main
integral divided by Y_k lies between
\[
 m_-=[d(1-d)]_+/k,qquad m_+=\min(d,d(1-d+2d^2))/k,
 \quad d=1/((k-1)v).
\]
Expand 1/(v+w) geometrically with signed remainder under an
exponential integral. The signed bounds on the tail are
Y_k[t(v)m_-+(t(v)-c)/(k v)]_+ and
Y_k[c m_++(c-t(v))/(k v)], using the endpoint contributions
from Stieltjes summation. For T_0 use its k=2 term with v=u as
the lower bound, and the upper on that term divided by
1-e^(-u) as the upper.

For k>=4 put z=x^(1/4). If p>z, use the k=4 bound for w_1
divided by 1-1/z. For p<=z the first retained prime power is
>x, so summing the geometric progression costs at most
[theta(z)+sum_(p<=z) log p/(p-1)]/x. The sum inside is at
most 2c(1+max(0,log(z/2))) by partial summation and
p/(p-1)<=2. Divide the resulting w_1 upper by u for w_0.
Use zero as lower for k>=4. These formulas are implemented
in prime_powers(). In particular U_1/e^(-u/2) has the supplied
nonincreasing upper function on u>=16: the remaining factors
are e^(-u/6), e^(-u/4), the decreasing geometric factor,
and (1+max(0,u/4-log 2))e^(-u/2), with coefficients using the
nonincreasing delta. Hence U_1<=1.111 e^(-u/2) on x>=10^7.
This includes the finite joins of all the large power rows.

## Other branches, and the pointwise envelope

Take at each x the minimum of the four component bounds from
(M1)–(M2), the old direct bounds, the theta and pi transfers
below, and the applicable certified finite/power rows. This is
valid even when different components select different branches.
For 1<x<2 the prime lists are empty (exact product 1 and sums 0).
For 2<=x<=25000000 the interval sieve can instead evaluate
each component from the exact prime list at floor x and the
normalizer intervals. This retains the pointwise values on
each prime slab, not just the uniform rows.

* Direct original bounds: Theorem 5.9 gives .2/u^3 for both
  products on x>=2278382; Theorems 5.6 and 5.7 give .2/u^3 for
  sum 1/p on x>=2278383 and .3/u^2 for log p/p on x>=912560.
  Preserve those endpoints and the non-strict statements.
* Dusart theta-transfer branches: for each of the Theorem 4.2
  rows with k>=2, apply (5.7) and the proof of Theorem 5.7:
  r=eta_k/(k u^k)+eta_k(1+1/(k+1))/u^(k+1) for the
  reciprocal sum, and eta_k/((k-1)u^(k-1))+eta_k/u^k for the
  weighted sum. The signed log-product interval is
  [-r-T_0^+,r-T_0^-]. Select the smaller eligible row, not
  just k=3. More generally if e_theta^±(v) are pointwise
  one-sided relative theta errors, integrate the available
  past-cutoff envelopes against 1/v+1/v^2 for sum 1/p and
  against 1 for log p/p; the endpoint terms are e_theta^±(u)/u
  and e_theta^±(u). Use the opposite sign for the integral,
  as in Dusart (5.7). Besides the table, one can take finite
  RH theta or E_b and Dusart 4.3/4.5 for the admitted
  one-sided prime-power corrections. Minima are taken only
  on their valid domains; this integral version preserves
  pointwise improvements without extending a finite estimate
  to infinity. It is an alternative to (M1) which retains
  a useful oscillation cancellation.
* A finite-log li-transfer gives a useful common branch
  where the sharp empirical CH2 psi estimate is no longer
  available. Put B=log 10^19. Write F(v)=pi(e^v)-V(e^v);
  then the signed errors for the two sums are
  e^(-u)F(u)-int_u^infty e^(-v)F(v)dv and
  u e^(-u) F(u)-int_u^infty (v-1)e^(-v) F(v)dv.
  For log Q use w(x)F(u)+int_x^infty w'(t)F(log t)dt
  -int_x^infty (w(t)-1/t)dt/log t with
  w(t)=-log(1-1/t). These identities follow by partial
  summation with the exact normalizers (the constants are
  fixed by the vanishing normalized tails). One may then
  use the pointwise B^± of ramanujan.md under the integrals,
  with opposite signs for endpoint and prime-error integral.
  The simple executable branch pi_transfers() on
  log(10^13)<=u<=B instead integrates the Büthe bound
  v e^(-v)|F(v)| <= 2.11 e^(-v/2)+2v e^(-v)
  up to B, then bounds int_B^infty v e^(-v)|F(v)|dv by
  T=1.06e-12(190-B)+232 e^(-B/2)+.112 e^(-190/8).
  Indeed on [B,190] the common J transfer plus CH2 is
  <=1.06e-12+116e^(-v/2); after 190 it is <.014e^(-v/8)
  by the B0 spectral tail and (P). This also places
  F in the integrability class needed in these identities.
  For the log-product use w(x)<=1/(x-1) and
  |w'(x)|=1/(x(x-1)); the additional continuous main-tail
  correction has modulus <=e^(-u)/(u(1-e^(-u))).

For transparency, sources.md lists other exact common branches
(used by E_b and the pi/weighted transfers) and the scope of
the comparison. The minimum above is not a claim of optimal
over all deducible inequalities from the seven originals.

## Explicit large-tail portfolio, including tradeoffs

For every onset in the table, the first three errors are
**strictly less** than C x^(-a)/u and the fourth is strictly
less than C x^(-a) on the entire indicated closed ray.
Use a=1/8 in B0 and a=5/32 in D02.

| log onset | B0 C | D02 C |
|---:|---:|---:|
|167|use the pointwise common branch|.277|
|190|.014|.245|
|200|.0132|.234|
|250|.0113|.199|
|300|.0104|.182|
|400|.0094|.164|
|600|.0085|.149|
|1000|.0076|.132|
|2000|.0071|.125|
|10000|.00681|.1193|

For larger onsets the formula E_cont in spectral.md provides
a continuously decreasing coefficient tending to D(b). Add
at most 21/H to its limiting coefficient for the integrated
spectrum in these four errors, using (P). More precisely,
an upper coefficient before exponentiating is
[
 e^{au}\min(E_h(u),E_{cont}(u))
     +1.212e^{-(1/2-a)u}+21/H+3e^{-(1-a)u}.
]
This uses U_1<=1.111 e^(-u/2), (P), and
(1+1/u)S_b for the reciprocal normalization. Every term
is nonincreasing for u>=170 on the indicated power tails.
Use expm1(z)<=z e^z for nonnegative z to pass to both products.
certify.py checks coefficients at the ray onsets with this
extra factor included. On [167,170], D02 uses the fixed
h=5e-13 box; its coefficient after division by e^(-a u)
is a sum of positive exponentials in u, thus convex and bounded
by the larger endpoint. It is <.276 at both endpoints; the
prime-power/primitive allowances and exponential factor cost
less than .001 of coefficient there. This proves the finite
join, including the left endpoint 167.

The simple D02 and B0 power rows are comparable on their
matched whole domains, not just at a grid: their ratio is
(C_D/C_0)e^(-u/32), strictly decreasing. E.g. at 200
the ratio is <.035 for every later u. For the stronger
pointwise comparison, fix the B0 box family with arbitrary h.
If h>=2e-12 its bias term alone is >=1e-12. Otherwise its last
nonnegative coefficient in (S) is >.0017: lower bound the
computable A_h and damped D_(699) at h=2e-12 (monotonicity
in 1/h). Thus the B0 spectral uncertainty is at least
min(1e-12,.0017 e^(-u/8)); the default and continuous versions
also satisfy this lower barrier on their own uncertainties.
The same comparison holds for the incumbent CH2 and other
original bounds used in E_0 (all the applicable table and
shape checks appear in sources.md and certify.py).
For u>=170, .277e^(-5u/32) is strictly below both terms of
the barrier, with room for the primitive and powers. For
167<=u<=168 one can split at h=2.1e-12 instead, giving last
coefficient >.0016 and bias >=1.05e-12; hence the CH2 floor
pi/H is a lower barrier. A D02 box is already <1.03e-12
at 167 and is decreasing on this slab. For 168<=u<=170
use the 1e-12 barrier and a D02 box <9.5e-13 at 168.
These intervals prove strict gain from 167 for the selected
uniform analytical envelope. In particular it is not a
new estimate merely because an obsolete inverse-log row
was used as comparator. Shrinking E/Z in (M1)–(M2) with
the same prime-power intervals reduces the upper
uncertainties in all four errors; the other direct-original
transfers do not undercut the displayed D02 rows in this range.
If using the finite exact-arithmetic branch at much smaller x,
D02 has no effect.

## Common inverse-log improvements and joins

In this paragraph C means C/u^3 for the first three errors
and C/u^2 for the fourth (not the power-normalized table).
Several common analytical rays x>=e^v are verified:

| v | C |
|---:|---:|
|17|.117|
|18|.079|
|19|.053|
|20|.036|
|21|.024|
|22|.016|
|23|.011|
|24|.007|
|25|.0045|
|26|.003|
|27|.002|
|32|.0009|
|36|.00027|
|40|.00017|
|log(10^19)|.00008|

Here are details of the interval joins and monotonicity tests:
(1) On log(10^7)<=u<=log(10^13), use .791e^(-u/2) for ψ,
(P), and the monotone normalized bound for U_1. For (P),
use the lower end of this interval for 2e^(-u/2), and its
upper end for (20/H)e^(3u/8), after scaling by e^(-u/2).
At any proposed onset use the U_1 ratio there and check the
result after multiplying by u^2 e^(-u/2), which decreases
for u>4, and including expm1. All four are <.166/u^k
(with k=3 or 2) already on this piece. For the weighted sum
the coefficient is <.165.
(2) From log(10^13) to B, use pi_transfers(). After scaling
by u^k its constants are bounded using
u^2[6.33e^(-u/2)+(4u+2)e^(-u)]+B^2 T plus the
continuous main-tail/exponential corrections. The decaying terms
are evaluated at the left end of each proposed subray, and
T is fixed. The common normalized bound is <.002 there;
from u=32,36,40 use the sharper rows shown.
(3) From B to 190, use CH2 Corollary 1.3 plus (P) and U_1,
estimating the floor terms with u<=190 and the sqrt functions
with u>=B. This gives <.00008. From 190 onwards the B0
power row is smaller since u^2 e^(-u/8) decreases. No limiting
constant floor is integrated to infinity. These are analytic
whole-interval bounds with interval-arithmetic checks of the
constants only.

For the first three errors one can further certify the cheaper
join .10994/u^3 on x>=25000000. In piece (1) retain U_0^+
instead of U_1^+/u. The normalized coefficient at the join
before exponentiating is
(.791+s+s/u)u^2 e^(-u/2)+u^3 U_0^+(u), with s the uniform
S_b/e^(-u/2) bound in piece (1). Every term decreases there:
for k=2,3 the additional geometric-integral polynomial term
has the shape (u^2-c u+2c^2)e^(-u/c) with
c=k/(k-1)<=2, decreasing for u>=17, and the other
terms have the same monotonicity as in the U_1 argument.
The minimum with u^2 e^(-u/c) and the nonincreasing
one-sided theta factors preserve this. After exponentiation
the coefficient at this join is less than .10994 (see
certify.py), and pieces (2) and (3) are smaller still. This
supplies the .11 finite-to-analytic tradeoff in finite.md.

Additional finite join results are in finite.md. Their gains
are B0 results, not effects of the hypothetical assumption.
