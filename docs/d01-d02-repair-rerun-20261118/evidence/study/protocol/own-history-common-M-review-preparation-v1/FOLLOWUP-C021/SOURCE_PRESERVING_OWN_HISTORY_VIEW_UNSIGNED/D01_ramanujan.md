# Ramanujan: exact final exception and explicit quantitative gap

Write H for the input PsiMajorant and S for the strip Re rho <=7/8 for
nontrivial zeta zeros. H implies S; alternatively take S from the literal
OpenAIQRH Thm 1.1 (PDF p.4). In what follows the finite-RH and other
source computations retain their source trust labels.

## Real endpoint

Set n=38358837682, P=1644673232, Q=632207037. Let r be the unique real
root in (n,n+1) of exp(1)*r*Q/log(r)=P^2. Then, under H, R(x)>0 for
every real x>r, and R(r)=0. The same holds using S instead of H, even with the density-free fallback below. The integer
last exception is n with R(n)<0. In the presence of H (or S and the
specified source bounds) these are sharp real/integer positivity onsets.

**Literal baseline endpoint discrepancy.** Platt–Trudgian Thm 2 (PDF
p.3) literally states 38358837682<x<=exp(58), as quoted by the packet.
Its extension to every real point in that interval cannot hold:
pi_exact.py gives R(n) in (-14736928,-14736927), and both counts are
constant on [n,n+1]. Thus R is negative on (n,r), not just at n.
The certificate is exact, not a numerical crossover observation.
We use the admitted theorem only at integers >=n+1 (and keep its
original trust label), and do not deduce anything from an inconsistent
real sliver. The same source's exp(3915) ray is retained. Dudek–Platt
Thm 1.2 exp(9658) and Thm 1.3 (conditional on full RH) are retained as
literal statements. Theorem 1.3 concerns an integer, not a real threshold.

Indeed floor(x/e)=14111427770 throughout [n,n+1] by endpoint enclosures;
n+1 is divisible by 2521. Hence counts are P and Q, and x/log x strictly
increases. R(n+1) in (52886500,52886501). The checker certifies
  n+.2179 < r < n+.2180,
  R(x)>67623427*(x-r) for r<x<=n+1.
The latter uses the derivative eQ(log x-1)/(log x)^2,
decreasing here and >67623427 at n+1. For x>=n+1 below e^37,
R(x)>=R(floor x)>0: pi(x) is constant from the preceding integer,
pi(x/e) is nondecreasing, and x/log x increases. This only uses
the source's integer cases in (n,exp(58)]. The analytic bound below
starts at e^36.96, overlapping by more than 21 log units.

Exact counting proof for pi_exact.py: initialize S(v)=v-1 for each
distinct floor quotient v=floor(n/j), including all v<=isqrt(n).
When processing a prime p subtract from S(v) for v>=p^2 the count
S(floor(v/p))-S(p-1). This deletes exactly the surviving composites
p*m with least prime factor p, keeping p itself; m>=p has survived
all earlier stages. Descending v ensures old-stage right-hand
values, and floor(floor(n/j)/p)=floor(n/(jp)). The same sieve
recognizes p from S(p)-S(p-1). At the end no composite survives.
Only exact integer operations are needed for the counts.

## Quantitative bounds and domains

With L=log x, h(x)=x^2/L^6, supported bounds are
* H or S, no density tables: R(x)>.05 h(x) for x>=e^36.96
  and R(x)>h(x) for x>=e^43.
* S: R(x)>(1+13.8/L)h(x) for x>=e^51, and
  R(x)>(1+14/L+145/L^2)h(x) for x>=e^236
  (using the stronger density estimate in density.md).
  For x>=e^300 one may add +1412/L^3 to the quadratic bound.
* Adaptive lower envelope below, evaluable on all x>=e^36.96.
  A term derived from H is only included when assuming H;
  otherwise use the S estimates and omit the H term.
All are strict and on real rays. The two fixed S assertions do not
require H. The lower thresholds work with either H or S and
are independently checked in both variants. They give explicit positive margins
where the baseline only gave positivity, and the overlap with the
original integer verification fills its entire gap.

### Building the prime-count approximants

Use li_2(x)=integral_2^x dt/log t (not the principal value convention).
For z=log y let r_+(z),r_-(z) bound (pi(y)-li_2(y))*z/y
from above and its negative from above respectively. Define T set
as TS in check.py, a_T=3.142/T and b_T the ceiling to .01 of
(log(T/(2*pi))^2-log(T/(2*pi))/3)/(2*pi) (or any slightly inflated
hundredth as computed by the interval code). For every real t>=2,
|psi(t)-t|<=a_T t + b_T sqrt(t). CH2 Cor. 1.2 (PDF p.3) and Lemma 9.2
(PDF p.35) cover respectively t>max(T,10^9) and the rest; finite RH
is PT FiniteRH Thm 1 (PDF p.2). The centre correction is at most
pi^2/(3T^2), since y coth y <=1+y^2/3 (also CH2 proof of Cor. 1.3).
Every T chosen is allowed. Dusart Thm 4.2 proof (PDF p.11) quotes
psi-theta<1.4262 sqrt(t); Prop. 4.3 (PDF p.12) gives
psi-theta>.9999 sqrt(t) when t>=121. Hence an upper theta error
can use b_T-.99 (add .99 sqrt(t) at t<121), a lower theta error
can use b_T+1.43.

Partial summation gives pi(y)-li_2(y)=(theta(y)-y)/z
 + integral_2^y (theta(t)-t)/(t log(t)^2)dt + 2/log 2.
For z>=16, integrals of t^(v-1)/log^2(t) for v=1 and 1/2
are bounded respectively by 100000+2y/z^2 and 100+3sqrt(y)/z^2.
Prove using unit-log interval upper sums up to e^16 (check.py),
then differentiate y^v/log^2 y. The constant 2/log2 and the extra
upper theta correction below 121 cost less than 50 in total.
Thus each pair (a,b) just specified gives the bound
r0(z;a,b)=a(1+2/z)+b(1+3/z)e^(-z/2)+(100000a+100b+50)z e^(-z).
For r_+ only and z<=39.32, also use 2z e^(-z): the literature-backed
pi<li PV up to 1.2e17 is quoted in Dudek–Platt Lemma 3.2 proof (PDF
p.8), and Dusart Thm 5.1 proof (PDF p.15) gives the same input.
Here li_PV(2)<2: in log coordinates subtract 1 from e^u on [-1,log2],
bound (e^u-1)/u by 1 on [-1,0] and 1/log2 on [0,log2]; the
remaining contributions log log2 and the far negative integral
are both negative. This avoids a normalization switch.

Further symmetric choices, obtained by integrating the indicated
psi majorant only above its threshold and using CH2 Cor. 1.3
below that threshold, are
rH(z)=(z^2/64+z/56)e^(-z/8)+1.43(1+3/z)e^(-z/2)
       +(6e-17 exp(200-z)+3exp(-z))z, z>=200 under H;
rD(z)=.022(1+1.16/z)e^(-z/8)+1.43(1+3/z)e^(-z/2)
       +(7e-17 exp(185-z)+3exp(-z))z, z>=185 under S.
The prefix integral divided by exp(threshold) is bounded in check.py.
For the H tail the log^2 cancels in the integral; for S the derivative
of y^(7/8)/log^2 y is at least (1/1.16) times y^(-1/8)/log^2 y
above e^185. Without the density tables under S, the new bound .0045 x^(7/8)L^2
in density.md gives the symmetric alternative rN(z), z>=185,
obtained from rH by replacing z^2/64+z/56 by .0045(z^2+(8/7)z)
and changing the prefix term as in rD. The B(x) fallback only
needs strip S and FKS Theorem 3.2/reciprocal zero counts.
Take r_+,r_- as the separate minima of available choices.

### Cancellation and the all-real certificate

P_10(z)=sum_(k=0)^10 k!/z^k; C=199584000; c=.15. For z>=15,
 P_10(z)-cz exp(15-z) <= z e^(-z) li_2(e^z)
 <= P_10(z)+C/z^11+cz exp(15-z).
Use differentiation: the first derivative deficit in unnormalized units
is 11!/z^12, and the added upper term supplies C(1-12/z)/z^12.
At z=15, li_2(e^15)/e^15<=2/15+e^(-7.5)/log2<.15;
P_10(15)/15<.15. This is an explicit anchor, not a divergent-series
truncation with an assumed asymptotic remainder.

Define b_n=sum_(max(0,n-10)<=j<=min(n,10)) j!(n-j)!,
a_n=n! sum_(j=0)^n 1/j!, d_n=a_n-b_n for n<=10. Coefficients d_0..d_3
vanish; d_4..d_10 are 1,14,145,1412,13985,145450,1610021.
Indeed L/(L-1) P_10(L-1) has coefficients a_n for n<=10,
by the binomial series in 1/L, and only positive terms subsequently.
Let
 G(L)=sum_(n=4)^10 d_n/L^(n-4)-sum_(n=11)^20 b_n/L^(n-4)
      -2.06[C/L^7+c L^5 exp(15-L)+L^4 r_+(L)]
      -c L^5 exp(16-L)-L^5 r_-(L-1)/(L-1).
Then R(x)/h(x)>G(L) for L>=36.96. The lower prime count uses z=L-1;
an upper pi-square error is bounded by 2.06 times the additive
error in the normalized prime count because 2P_10(L)+error<2.06:
check at L=36.96 with one r0 choice, all varying terms decreasing.
This proves the advertised variable envelope on the entire ray.

check.py uses 1/50 closed-interval cells (not a sample at grid
points) for the displayed fixed margins on [37,300].
After L=300, multiply the magnitudes of all negative terms by L
(H unit margin) or by L^3 (S quadratic margin), substituting the direct
rH or rD. These terms are decreasing: they are sums of reciprocal
powers or positive multiples of L^j (L-1)^k e^(-c L),
with positive power exponents totalling at most 10 and c>=1/8
(negative exponents only help), or elementary reciprocal terms.
At 300 they are strictly smaller than 14 or 1412 respectively,
so d_5/L or d_7/L^3 covers all of them. The S quadratic margin then also implies the S slope margin.
The density-free unit variant uses rN and the same weight L.
For the additional cubic term at L>=300 multiply the costs by L^4
and use d_8=13985 at the anchor; the same monotonicity applies
(the total of positive power exponents is then at most 10).
