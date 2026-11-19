# Additional derived arithmetic consequences

These are separate from the two requested application families.
S means the 7/8 zeta strip, supplied by H or by the literal QRH
Thm 1.1. Results depending on FKS Cor. 2.9/Table 8, CH2 and finite
RH retain those input trust labels.

## Primes in short intervals

Write L=log x. Every real x>=e^240 has strictly more than
 .02 A(x)/log(x+A(x))
primes in (x,x+A(x)), where A(x)=x^(5/8)*L^(51/4)/50000.
Every x>=e^300 has strictly more than
 .05 B(x)/log(x+B(x))
primes in (x,x+B(x)), where
 B(x)=.004*x^(5/8)*L^(51/4)/(log L)^3.
Both lengths are strictly smaller on their full rays than
x/(5000 L^2) in admitted Dusart Cor. 5.5 (PDF p.16), and than
x/L^3 in Prop. 5.4 on their full rays. For the first comparison,
the ratio evaluated at each left endpoint is less than 1
(check.py), and logarithmic differentiation (in L) gives
-3/8+(59/4)/L-b/(L log L)<0, b=0 or 3. For log^-3 replace
59/4 by 63/4 and 5000 by 1; at the endpoints the first comparison
is already stronger, and this latter ratio also decreases.
For x>=e^200 there is also a prime in (x,x+.041 x^(7/8)] by
the pointwise Chebyshev improvement and 1.43 sqrt x prime
power correction. Its length is smaller than the two Dusart
lengths on this full ray (endpoint comparison and monotonicity).
Take the minimum of all available lengths; the B/A ratio
equals 200/(log L)^3, so B improves on A once log L>200^(1/3).
In particular for every integer n>=exp(2060/3) there is a
prime strictly between n^3 and (n+1)^3: take x=n^3 and
A(x)<3x^(2/3), since .00002 L^(51/4) exp(-L/24)<3 at
L=2060 (certified) and the ratio decreases thereafter.
These are bounds from the admitted packet, not a claim that
the exponent or the cubic onset is best known.

### Smoothed zero estimate

For interval length M in {A,B}, set h=M/2, T=2.1 x/h,
a=log T and w=1-|t-(x+h)|/h on x<=t<=x+2h, zero otherwise.
Integrate Dusart (2.1) against the triangular kernel in the
equivalent double-integral form
 sum_n Lambda(n) w(n)
 = [psi_1(x+2h)-2psi_1(x+h)+psi_1(x)]/h,
with
psi_1(y)=int_0^y psi(t)dt. No differentiation of an ordinary
function at prime powers is required: by unique factorization
psi_1(y)=sum_n Lambda(n)(y-n)_+ and its second difference is h w(n).
The contribution of x in (2.1) is h, and the -log(2*pi) term
has zero second difference after one integration. Its trivial-zero
correction -.5 log(1-t^-2) is decreasing, hence has a *negative*
second difference after one integration. Its magnitude divided
by h is at most 1/[x(x^2-1)] (differentiate the correction on
[x,x+2h] and use a double integral). This term is accounted for
in the scalar loss (it is <.001 on the whole range). The zero
integrations are justified on compact intervals exactly as in
mertens.md; after the integration the series is absolutely
convergent. For F(t)=t^(rho+1)/[rho(rho+1)], its second difference
equals int_0^h int_0^h F''(x+u+v) du dv = int int t^(rho-1) du dv.
The absolute normalized zero weight, after dividing by h^2,
is at most x^(beta-1) min(1,(T/|gamma|)^2). Indeed the
derivative bound gives the first part; from the four endpoint
terms get <=4(x+2h)^(beta+1)/(h^2 gamma^2), and x+2h<1.01x
(check at the onset and logarithmically differentiate); thus
4*(1.01)^2 <(2.1)^2. There are no real zeros by density.md.

Let K(s)=sum_(beta>=s) min(1,(T/|gamma|)^2).
By conjugation and layer integration,
 K(s)=4T^2 int_T^infinity N(s,t)t^(-3)dt.
For t where t coincides with a zero ordinate the convention is
irrelevant to the integral. For .60<=s<=.875 use FKS literal
Cor. 2.9/Table 8 (PDF pp.7,26), c1<=11.08,c2<=5.30,
p=(8/3)(1-s), q=5-2s. The density bound also holds for 1<t<=H0
since the count there is zero by finite RH. Substituting t=T exp(v)
and bounding (a+v)^q<=a^q exp(qv/a) gives
 K(s)<=d*T^p*a^q+11*a^2, with
 d=44.32/(2-16/15-3.8/a_min),
where a_min is a at the corresponding onset. Here a>=a_min>30
and the secondary inequality 21.2/(2-2/a_min)<11 is checked.
The function a is increasing directly from its formula below.

For low zeros beta<.60, the same integral uses N(t)<=t log t
from the Rosser bound in FKS Lemma 2.1 and Remark 2.2, valid
on t>=e^30. Thus their normalized contribution is at most
4T(a+1)x^(-2/5).
For beta>=.60, write x^(beta-1)=x^(-.4)+
 L int_.60^beta x^(s-1)ds and use K. Put lambda=L-(8/3)a.
For s in [.60,.875] the first contribution to x^(s-1)K(s)
is <= d a^(13/4) e^(-lambda/8)
    * exp(-(lambda-2log a)(.875-s)).
If mu=lambda-2log a lies in (0,L), the base term plus the
integral is bounded by d a^(13/4)e^(-lambda/8)*L/mu.
(The exact multiplier is L/mu+(1-L/mu)*exp(-.275mu).)
For the constant second term in K, the normalized bound after
layer integration is 11a^2 x^(-1/8). This is the source of the
gain over a pointwise psi difference.

Now write T=k exp(3L/8) L^(-51/4)(log L)^b with
(k,b,L0)=(210000,0,240) or (1050,3,300). We have 30<a<=3L/8.
The latter follows at L0 and persists since 12.75 log L
grows faster than log k+b log log L. Bound
 mu >= 32 log L-(8/3)log k-(8b/3)log log L >0.
In the main contribution the factors simplify to
 d*(3/8)^(13/4)*k^(1/3)*(log L)^(b/3)
    / [32 log L-(8/3)log k-(8b/3)log log L].
This decreases with L: for b=0 the denominator increases;
for b=3 divide by log L and use decrease of
log log L/log L (log L>e) and 1/log L. Also mu<L since a>30.
The low contribution is bounded by
4k(3L/8+1) exp(-L/40) L^(-51/4)(log L)^b,
and secondary by 11(3L/8)^2 exp(-L/8). Both decrease
on these rays by logarithmic differentiation.
Removal of higher prime powers costs at most 1.43 sqrt(x+M)
<1.44 sqrt x in the triangular sum, giving relative cost
 (2.88 k/4.2) exp(-L/8) L^(-51/4)(log L)^b,
again decreasing. The scalar checker bounds the sums of
these four relative costs by .934 and .822 respectively; the extra
<.001 trivial-zero cost leaves strict margins >.04 and >.10.
Each prime adds at most log(x+M), and h=M/2; endpoints have
weight zero. This proves the displayed strict count lower bounds.

For the separate pointwise length .041 x^(7/8), use
|theta(t)-t| <= .020 t^(7/8)+1.43 sqrt t for log t>=200.
At y=x+.041 x^(7/8), the sum of the two endpoint errors divided
by x^(7/8) is <.04001 (scalar checks; decreasing bound),
so theta(y)>theta(x). This proof avoids smoothing.

## Extremal totient and primorial bounds

For integers N>=2 define F(N)=max_(2<=m<=N) m/phi(m).
Let p be the largest prime with primorial product P_p=prod_(q<=p)q<=N.
Then F(N)=Q(p). Indeed by inclusion-exclusion
m/phi(m)=prod_(q|m) q/(q-1). Replacing its k distinct prime
divisors by the first k primes increases the ratio and does
not increase the minimum integer having those divisors. At most
pi(p) distinct divisors can fit, and P_p attains the maximum.
Thus if p>=e^200, put X=log N. With U=U_0(p) in mertens.md,
E_p=.020*p^(7/8)+1.43 sqrt p, and d=(E_p+log(2p))/p, we have
  | log( F(N)/(e^gamma log log N) ) |
      <= U + [-log(1-d)]/min(log p,log X).
Indeed theta(p)<=X<theta(p)+log p_next and p_next<2p follows
from the short interval result (or its pointwise variant).
Consequently |X/p-1|<=d<1, and
|log X-log p|<=-log(1-d). A second application of the mean
value bound for log compares log(log X) and log(log p).
In particular d<=.02001 p^(-1/8), and using the constant
Mertens bound one can simplify the last display to
 <.041*p^(-1/8)/log p
with the stated .020 and .019851.
Use -log(1-d)<=d/(1-d); the scalar conditions are proved by
bounds at log p=200 and decreasing exponentials. In particular,
for every integer N>=exp(2 exp(200)) the displayed log error is
 < .042/[(log N)^(1/8)*log log N].
Indeed a prime p0 in (e^200,e^200+.041 e^175] exists, and
theta(p0)<2e^200 by the Chebyshev estimate, so p>=p0.
To convert the denominator p^(1/8) log p to X^(1/8) log X,
the ratio X^(1/8)/p^(1/8) is at most (1+d)^(1/8) and
log X/log p <=1+[-log(1-d)]/log p. The same scalar tests give
the stated .042 cap.
For primes p<=10^13, the signed Mertens result plus
theta(p)<=p (Dusart Cor. 4.5 proof states theta(t)<t for
t<1.39e17) gives the strict Nicolas-type inequality
 P_p/phi(P_p)>e^gamma log log P_p.
No claim is made that this finite-range sign verification is
the largest known, nor that its sign persists on an unbounded ray.
