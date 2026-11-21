# Weighted: signed oscillatory tails plus prime-power correction

Hypothesis: pinned Mathlib RiemannHypothesis. Define, with ordinary endpoints,
A=sum_{p<=x}(log p)/p, Bx=sum_{p<=x}1/p,
W=log P where P=prod_{p<=x}(1-1/p)^(-1).
Let E,B,gamma be respectively the Mertens constants for A-log x,
Bx-log log x and W-log log x (gamma is Euler's constant).
Set L=log x and D=psi(x)-x. All elementary envelopes below have x>=exp(24).
Smaller onsets are supplied by Lee–Nosal Cor. 1.3 (imported).

## Signed inequalities

Put c=log(2 pi), z=.047, q=1/(2(x^2-1)), and
```
a_- = .955/sqrt(x)-1.045/x
a_+ = 1.045/sqrt(x)+5.25/x^(2/3)
w_- = (.955-1.045/4)/(sqrt(x)(L+2log 4))
w_+ = a_+/L
sW = z/sqrt(x) (1/L+3/L^2+4/L^3).
```
Then
```
A - L - E - D/x in
   [(c-q)/x - z/sqrt(x)+a_-, c/x + z/sqrt(x)+a_+],
W - log L - gamma - D/(x L) in
   [(c-q)/(x L) - sW +w_-, c/(x L)+sW+w_+].
```
For Bx-log L-B use the interval for W-log L-gamma with [0,1.045/(x L)]
added. One may use any valid signed D bound in PNT.md, including Büthe
for x<=10^19 and the new B3 for L>=35. For example bounds without D:
```
|A-L-E| <= [Upsi/sqrt(x)+1.20]/sqrt(x),
|W-log L-gamma|, |Bx-log L-B| <= v := [Upsi/sqrt(x)+1.20]/(L sqrt(x)).
```
For the two product conventions, P/(exp(gamma)L) and its reciprocal,
the corresponding absolute errors from 1 are <= exp(v)-1 <= 1.001 v.
Better asymmetric product errors come by exponentiating the signed interval:
if W-log L-gamma lies in [r,s], the product ratio lies in [exp r,exp s]
and its reciprocal lies in [exp(-s),exp(-r)].

## Proof

For x>=2 define C_A(x)=sum_{n<=x} Lambda(n)/n and
C_W(x)=sum_{n<=x} Lambda(n)/(n log n).
By Abel summation and the convergent error integrals, with f(t)=1/t
or 1/(t log t), respectively,
```
C_A = L + E_A + D/x - int_x^infty (psi(t)-t)/t^2 dt,
C_W = log L + gamma + D/(x L) -
           int_x^infty (psi(t)-t)(log t+1)/(t^2 log^2 t) dt.
```
The limits defining the constants exist from the pointwise B2 estimate.
The constant E_A is E+sum_{p,k>=2}(log p)/p^k by absolute convergence of
prime-power corrections and the definition of E; no numerical E is used.
For gamma, write C_W(u)=log log u+K+o(1). The Euler product gives
log zeta(1+s)=s int_1^infty C_W(t)t^-1-s dt for s>0.
Change variable v=s log t and use int_0^infty exp(-v)log v dv=-gamma.
Thus log zeta(1+s)= -log s-gamma+K+o(1); the simple pole of residue 1
gives K=gamma. The difference tending to zero is integrably bounded
outside a neighborhood of t=1, whose contribution vanishes as s->0
(including the integrable log log t singularity). This also gives
B=gamma-sum_{p,k>=2}1/(k p^k).

Let F(x)=int_x^infty (psi(t)-t)/t^2 dt. Using the integrated explicit formula
and Z of PNT.md, termwise integration (first on [x,y], then y->infinity)
gives
```
F(x)=F0(x)-c/x+int_x^infty b(t)/t^2 dt,
F0(x)=-sum_rho x^(rho-1)/(rho(1-rho)), |F0(x)|<=.047/sqrt(x).
```
Indeed antiderivatives at t are t^(rho-1)/(rho-1); all endpoint terms
are dominated by the summable |rho|^-2, so no assertion about conditional
pointwise convergence of psi's zero sum is needed. For t>=x,
0<=b(t)=-log(1-t^-2)/2<=q. For C_W put g(t)=(log t+1)/(log t)^2.
The zero-term error integral with the extra factor g(t) equals
g(x)F0(x) + int_x^infty g'(t)F0(t)dt, by integration by parts.
Now |g'(t)| <= (1/L^2+2/L^3)/t, so this is bounded by sW.
The constant and trivial-zero pieces are integrated directly using
int_x^infty g(t)t^-2 dt=1/(x L). In particular we did NOT bound the
tail by integrating the pointwise |psi-t| or |theta-t|; the second
denominator of the integrated zero kernel is the source of the gain.

The correction to A is positive after replacing E_A by E:
T_A=sum_{p<=x,k>=2,p^k>x}(log p)/p^k. For y>=sqrt(x),
(1-.015)y<=theta(y)<=(1+.015)y, and for y>=x^(1/3),
theta(y)<=1.05y. These follow from B2 since the arguments are >=e^12,
>=e^8 respectively, with .015 and .05 bounds from u^2 exp(-u/2)/(8 pi)
decreasing for u>=8. Abel summation from y to infinity gives
```
(1-.045)/y <= sum_{p>y}(log p)/p^2 <= (1+.045)/y
```
for y>=sqrt(x). For k=2 use this from y=sqrt(x) and subtract the tail
p>x to obtain a_-. For k>=3, split p<=x^(1/3) and p>x^(1/3). In the
first part each geometric tail starting at the first p^k>x is <=2/x,
so its contribution is <=2.1 x^-2/3. In the second part
sum_{k>=3}p^-k<=2p^-3; dropping the negative lower endpoint of Abel
summation would give 3.15 x^-2/3, from 2*3*1.05*int_y^infty t^-3 dt.
Their sum gives a_+. For W the analogous correction is T_W, term by
term bounded by T_A/L since log(p^k)>L. For its lower bound restrict
to k=2 and sqrt(x)<p<=4 sqrt(x)<=x; all log(p^2)<=L+2log4, proving w_-.
The tail W minus Bx normalization correction is nonnegative
sum_{p>x,k>=2}1/(k p^k), bounded by 1.045/(x L) since
sum_{k>=2}1/(k p^k) <= 1/((p-1)p log(p^2)) log p =1/(2p(p-1))
and more simply <= 1/((p-1)p), while
sum_{k>=2}1/(k p^k) <= 1/p^2 for p>=2.
Thus <=sum_{p>x}(log p)/p^2 / L <=1.045/(x L).

Numerical envelope constants: a_+ sqrt(x)<=1.045+5.25 exp(-4)<1.142.
For A add z and 1.9/sqrt(x); for B (the larger bound of B and W)
add .047(1+3/L+4/L^2) and (1.9+1.045)/sqrt(x); each total <1.20.
The symmetric bound minus sign is also covered because the correction
is nonnegative and q<c. With B2 substituted for Upsi,
v <= [(L-log L)/(8 pi)+1.20/L]/sqrt(x) < 0.00001, so exp(v)-1<=1.001v.

## Comparisons and limitations

* Relative to Lee–Nosal Cor. 1.3 (4) and (5), the stated symmetric bounds
  for A and Bx are <1/3 of their displayed bounds for every x>=exp(24):
  8 pi*1.20 < L log L throughout. For the direct and reciprocal product
  the ratio is also <1/3 if using the exact bound exp(v)-1<=v/(1-v).
  Indeed log L-8 pi*1.20/L>1.9 while L v<.001 throughout L>=24
  (by the decreasing elementary envelope); in particular
  [(L-log L)+8 pi*1.20/L]/(1-v)<L. Onset exp(24) is much
  later than their Cor. 1.3, so use that corollary below it.
* Lamzouri arXiv:1410.3777 Prop. 2.1, Lemma 2.3 already retain the
  positive bias from squares in a truncated zero expansion with big-O.
  The exact prime-power decomposition and the existence of a positive
  square shift are not new; this deduction gives a simple finite two-sided
  remainder and literal envelopes using the absolutely convergent tail.
* The constants here are estimates, not best possible. Further useful
  low-range refinement would require keeping the signed Büthe ranges
  individually, controlling smaller prime-power bases, or calculating
  finite prefix sums with certified logs.

## Earlier onset via exact small-base thresholds

A second envelope is sharper than all four simple bounds (4)-(7) of
Lee–Nosal Cor. 1.3 on exp(5.7)<=x<=10^19. Below exp(5.7), keep their
published bounds on their respective domains rather than extrapolating.
In this extension let C=1.00000075, c=log(2 pi), y=x^(1/3), L=log x, and
```
A0 = 2C-.60 + [1.5C + (y/(y-1))(1.5C-.48)] exp(-L/6)
             + .5 log 2 exp(-L/2),
U_A = .94 + A0 + .047 + c exp(-L/2),
U_B = .94 + A0 + .047(1+3/L+4/L^2) + (c+2C-.60) exp(-L/2).
```
Use |A-L-E|<=U_A/sqrt(x), |W-log L-gamma| and |Bx-log L-B|
<= v0:=U_B/(L sqrt(x)). For the two product conventions use
v0/(1-v0) (from exp(v0)-1<=v0/(1-v0) when 0<=v0<1).

Proof: use .94 sqrt(x) for |psi(x)-x| from Büthe Thm 2,
theta(t)<=C t from Platt–Trudgian Cor. 2, theta(t)>=.48 t for t>=6
and theta(t)>=.60 t for t>=17. For these latter two, bounds.py computes
exact primes by division and directed lower bounds on theta(m) for
integer m<=1423 and checks the inequalities against m+1; theta(t)
does not drop inside the unit cell. Above 1423 through 10^19 use
Büthe; beyond it the RH theta bound B2 is more than sufficient.
Both new small-base statements hold throughout the inputs of Abel's
improper tail integrals, not just up to x.
For the square tail starting above sqrt(x)>=17 retain the negative
lower endpoint from Abel, giving (2C-.60)/sqrt(x).
For p<=y, the tail for k>=3 after the first p^k>x is
<= (p/(p-1))/x. Bound by 1.5/x except at p=2, yielding upper
(1.5 theta(y)+.5 log 2)/x. For p>y, bound the k>=3 geometric tail
by p^-3*y/(y-1) and use
sum_{p>y} (log p)/p^3 <= (1.5C-.48)/y^2
by partial summation, retaining its lower endpoint.
This yields T_A<=A0/sqrt(x). As above T_W<=T_A/L, and the extra Bx
correction is <=(2C-.60)/(x L), using the square tail starting at x.
The signed oscillatory tail bounds continue to hold for these x.
The rational comparison at L=5.7 is U_B/(1-v0)<3 L^2/(8 pi).
Since U_B and v0 decrease and the comparison right-hand side increases,
this and U_A<U_B prove all four comparisons throughout the stated domain.
This improves onset for the stronger envelopes, not the smaller
onsets of the published baseline.

## A coupled signed consequence: cancel the pointwise oscillation exactly

For all real x>=exp(24) and under the pinned RH, put
D_A=A-L-E, D_B=Bx-log L-B, D_W=W-log L-gamma.
For each D_s in {D_B,D_W} the same strict signed inequality holds:
```
.13/(L sqrt(x)) < D_A - L D_s < 2.39/(L sqrt(x)).
```
The individual errors may be much larger or oscillate; subtracting
independent absolute envelopes would not give this sign.

Proof for W. From the Abel formula above, the pointwise D=psi(x)-x
cancels exactly, giving
```
D_A-L D_W = int_x^infty (L g(t)-1) (psi(t)-t)/t^2 dt + T_A-L T_W .
```
The constant -c integrates to zero since int_x^infty g(t)t^-2 dt=1/(xL).
The remaining zero contribution equals
(L g(x)-1)F0(x)+ L int_x^infty g'(t)F0(t)dt, so its magnitude is
<=.047(3+4/L)/(L sqrt(x)). The trivial-zero term is nonnegative:
L g(t)-1 decreases from 1/L to -1 and has zero integral against
t^-2 dt, while b(t) is decreasing. Subtract b at the unique crossing
of Lg=1 to see the integrand product has nonnegative sign.
Its upper bound is q/(x L), using Lg(t)-1<=1/L on the positive part.

For the positive prime-power correction, keep only squares with
2 sqrt(x)<p<=4 sqrt(x) (all <=x). By the signed square-tail bounds
the sum of log(p)/p^2 there is >=(.955/2-1.045/4)/sqrt(x)
=.21625/sqrt(x). On these terms 1-L/log(p^2)>=log(4)/(L+log(4)).
For an upper bound on all the terms use
1-L/log(p^k)<=(log(p^k)-L)/L, followed by nonnegative integration:
```
sum_{p<=x,k>=2,p^k>x} (log p)/p^k (log(p^k)-L)
 <= int_x^infty T_all(t) dt/t,
T_all(t)=sum_{p,k>=2,p^k>t} (log p)/p^k.
```
The upper bound a_+ from the first proof applies to T_all as that
proof already counted all eligible p>x too when bounding tails.
Thus after division by L the correction is <=
(2.09/sqrt(x)+7.875/x^(2/3))/L. For B, subtract at most
L*1.045/(x L)=1.045/x from the W result, and never add anything.
Scale by L sqrt(x), use L>=24, x^(-1/6)<=exp(-4), and
L/sqrt(x)<=24 exp(-12). The endpoint lower expression
.21625 log(4) L/(L+log(4)) - .047(3+4/L) - 1.045 L/sqrt(x)
exceeds .13, and the upper
2.09+7.875 x^(-1/6)+.047(3+4/L)+q/sqrt(x) is <2.39.
No prime-table hypotheses or pair correlation enter. This shares both
the boundary error and the constant term before taking absolute values.

## Independent small-window exact audit

On every real x in [50,300), all four of the Lee–Nosal Cor. 1.3 bounds
(4)–(7) hold with the right-hand side multiplied by .82. The sum A
baseline itself is checked on [44,50), and the reciprocal-prime-sum
and both product baselines hold with an extra factor .985 on [25,50).
This is an exact integer/rational computation (weighted_small.py/out),
not a check at isolated real samples and not a formal proof of Python.
It is unconditional given the published unconditional theta<=C x
and the classical unconditional Mertens limit theorems.
Use the preceding analytic envelopes beyond 300 (their onset exp(5.7)
is less than 300).

For the constants, E_A=-gamma in the Abel formula for C_A:
- zeta'/zeta(1+s)=1/s-gamma+O(s) from the Laurent series,
and Abel transform of C_A(t)=log t+E_A+o(1) gives 1/s+E_A+o(1).
So E=-gamma-sum_p log(p)/(p(p-1)); B was characterized above.
Enumerate primes <=10000 exactly by the ordinary composite sieve,
summing both constants with the directed log approximations in bounds.py.
For p>10000, bound the tails by
2 C(1+1/10000)/10000 for E (use the square tail and p/(p-1)),
and 2 C/(10000 log 10000) for B (use the square tail and
sum_{k>=2}1/(kp^k)<=1/p^2). This encloses the constants
without assuming their decimal values. GAMMA is bounded by the
finite harmonic estimates in bounds.py.

For each integer m, the prime sums and the product are constant for
m<=x<m+1. A-log x-E and Bx-log log x-B are each decreasing on
that interval, so the absolute errors are bounded by the maximum
of the two endpoint values calculated with its constant step values
(at m+1 use the left limit). The product ratio and its reciprocal
are each monotone there as well. The comparison right-hand sides
L^j/sqrt(x) (j=1,2) have a single interior maximum as functions of L,
so their minimum on the cell is at one of its endpoints. The exact
arithmetic script bounds the ratios on the full cells on this basis.

## Cross-family deduction: from the weighted error to prime counting

At every L>=35, under RH,
```
(x/L)(A-L-E)-2.22 sqrt(x)/L
    < pi(x)-li(x)
    < (x/L)(A-L-E)-1.89 sqrt(x)/L.
```
For pi-Li2 add li(2) to both endpoints. This is a signed comparison
between two fluctuating functions, not an absolute bound asserted to
beat PNT everywhere. It can be combined with an independently bounded
weighted error, or used to transfer information in the opposite direction.

Subtract (x/L)(A-L-E) from the signed pi identity in PNT.md.
The common pointwise psi(x)-x term cancels. The new signed terms are
-Q(x)-(x/L)T_A(x); the other terms are I0+Ib+(x/L)F0 plus the constant
(2-c)/log 2-li(2) and the trivial tail from F. Its absolute value is
<= sqrt(x)/L [.047+.094/L+4.5 L/sqrt(x)] < .05 sqrt(x)/L,
using |constant|<1, |I0|<.094 sqrt(x)/L^2+3.2, Ib<.25 and
the trivial tail <=q/L; then check L=35 and use monotonicity.
Meanwhile .99 <= L Q/sqrt(x) <=1.1 by PNT.md.
The bounds a_-,a_+ here give .954<sqrt(x) T_A<1.061 for L>=35.
Thus the downward shift, including the possible remainder, lies
strictly between 1.89 and 2.22 in units sqrt(x)/L. This deduction uses
the common oscillatory boundary information that independent absolute
PNT and Mertens bounds would destroy.
