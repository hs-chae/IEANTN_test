# Eventual population at widths 3 and 5

Let G(a)=q(1+2a), S(a)=(944247+1163388a)/1000000 and
F(a)=9/8+16a/15, where q=20582561296/24680948495. Let Y(c,x)=x+c sqrt(x) log(x).
For x sufficiently large let N(c,x) and M(c,x) be the numbers of primes in
(x,Y(c,x)] and (x,Y(c,x)), respectively.

**Fixed widths.** Under ordinary RH and the two named BR input predicates,
GoodCoefficient(685251/387796,3) and GoodCoefficient(465/128,5) hold:
substitution into S and F respectively gives exactly 3 and 5. Each width has
its own positive margin and eventual threshold. In particular for a = the
respective displayed coefficient, both counts are eventually strictly larger
than a sqrt(x), and in fact both exceed a sqrt(x) by any fixed additive
constant eventually. For half-open counts this follows immediately from
the margin; for strict-open counts the possible omitted right endpoint
costs at most one prime, so for any fixed K we may also require
delta sqrt(x)>K+1. Equivalently the strict-open count itself still has a
positive normalized margin, e.g. delta/2 eventually. There is no specified
uniform threshold or explicit onset here.

**Lower envelope on a >= 0.** Let u=544470055511653/2490320656859788
and v=542259/290164. The width frontier is G on [0,u], S on [u,v],
and F on [v,infinity), with both expressions equal at either shared
boundary. Indeed G-S=(2q-1163388/1000000)(a-u) and S-F=
(1163388/1000000-16/15)(a-v); both slopes are positive and 0<u<v.
The G/F crossing 172404138261/356130660736 lies strictly between u and v,
where S is smaller, so it is not a frontier breakpoint. With RH and all
three analytic inputs the available widths by direct use and monotonicity
are exactly the union (G(a),infinity) union [S(a),infinity) union
[F(a),infinity). To see monotonicity, for x>1, Y(c,x) is increasing in c;
then interval inclusion preserves the same count margin. Thus the endpoint
of this union is excluded for 0<=a<u, and is included for all a>=u
(in particular at u by S, despite the Gaussian epsilon). This is an
upper bound for the true infimum of good widths, not a proof of equality
to that unknown infimum or a claim of actual failure at the excluded endpoint.

The inverted width breakpoints are G(u)=3731134672774344/3112900821074735
and S(v)=9048441/2901640. At widths between these the best nominal
coefficient comes from S; above the latter it comes from F. Below the
first breakpoint, for c>q, the Gaussian inverse (c/q-1)/2 is a
supremum of available targets, not a proved GoodCoefficient at equality.
For every lower nonnegative target choose epsilon=c-G(a)>0. This gives a
liminf at least the supremum, not an eventual pointwise lower bound at it.
At c=q or below none of the three gives a nonnegative target directly.
Since G(u)<3<S(v)<5, the width-3 and width-5 values above are the largest
nominal targets obtained by this inversion. No CMS hypothesis is needed
for the two positive-margin conclusions themselves. These are not upper
bounds on what primes do: each conclusion even implies the existence of
some larger target by taking half the unspecified margin.

**Octic comparison.** Use the preserved baseline with its separate
RH+Green+Nicolas+BPT inputs. At c=3 and c=5 (inside [1.03,16]) the leading
strict-open coefficients are 105391/60000 and 636173/180000 respectively.
Subtracting them from the new nominal coefficients gives
61212941/5816940000 and 70933/720000 respectively. At the same nominal
targets the corresponding octic limiting widths exceed 3 and 5 by
183638823/15511840000 and 70933/640000 respectively. These width comparisons
use the inverse only for targets in [973/180000,2396173/180000], which maps
exactly onto [1.03,16]. The full old inequality also has +21/(5 log x)
in the normalized count and holds for x>=exp(24); it is not an asymptotic
claim only. Its strict-open leading count 1 at width 343827/160000
retains that explicit onset. None of the new results inherits it. No
best-known or general superiority claim.

**Rank consequence.** For an eventual base x=p_n, the primes greater
than p_n occur in increasing order p_{n+1}, p_{n+2}, ... . This follows
from the increasing enumeration Nat.nth of the infinite set of primes.
The first prime has index 0 and piReal(p_n)=n+1, so for a count m
there are precisely the next m indices in the interval (no intervening
prime can be skipped). In particular at either width for the displayed
positive target a, floor(a sqrt(p_n))+1 <= M(c,p_n), so that prime at
index n+floor(a sqrt(p_n))+1 is strictly below Y(c,p_n). An arbitrary
fixed additional nonnegative number of ranks can be guaranteed eventually
by using the additive margin. This application is eventual in n because
p_n>=n+2 (the enumeration increases by at least one per index).

**More on the comparison.** In the order G, S, F, the exact formulas for
the octic limiting width minus the envelope on its three branches are

- 150039188346073/789790351840000 - (2q-9/8)a;
- 318687/4000000 - (19194/500000)a;
- (7/120)a - 16173/160000.

Restrict these comparisons to the octic inverse domain above. Each is
positive there: the first two decrease and are positive at u and v,
respectively; the third increases and is positive at v. This is only a
comparison of these specified leading widths, with the first branch
interpreted as an infimum. For the fixed widths let g be the respective
exact positive leading gain. The new nominal leading lower bound exceeds
the full old lower-bound expression at x > exp(21/(5g)), wherever the
new bound is valid; this calculation is a threshold for comparing the
expressions, not an onset for the new theorem. The old positive logarithmic
term tends to zero after normalization, so the old displayed inequality
alone at the inverted width does not supply a fixed positive margin at
its limiting target.

At Gaussian inverse equality the lower-limit statement uses the extended
real liminf (or, equivalently, the eventual epsilon lower inequalities).
Thresholds can depend on epsilon, and the lower-limit statement also
holds for the open count by the same margin argument below the endpoint.
The Gaussian inverse lower-limit argument itself works at any fixed c>q;
in the affine portions of the frontier it gives a weaker nominal target.

**Verification and scope.** See `verification.md`. The written derivation
and `Transfer.lean` prove the transfer from the three supplied curves,
not their analytic hypotheses from RH. The Lean theorems include exact
prime-finset membership, the one-prime endpoint loss, positive open-count
margin and an exact rank equivalence. For that equivalence, put
b=ceil(y) and T=primeCounting'(b); for p_j<b, monotonicity gives
j+1=primeCounting'(p_j+1)<=T, and for p_j>=b it gives
T<=primeCounting'(p_j)=j. At x=p_n<y this yields
M=T-(n+1); for k>=1, p_(n+k)<y iff k<=M, and p_(n+k)>p_n by strict
monotonicity. Thus the rank and strict-open conclusions do not presume
anything about primality of the right endpoint.
