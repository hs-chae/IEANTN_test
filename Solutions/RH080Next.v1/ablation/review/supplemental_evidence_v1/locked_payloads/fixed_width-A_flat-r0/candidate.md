# Conditional transfer at total widths 3 and 5

**Result.** Assume ordinary RH for the Riemann zeta function and both named
BR inputs `BRFourierInput.v1.norm_identity` and
`BRFourierInput.v1.uniform_population_q1`. For each of the pairs
[
 (C,A)=(3,685251/387796),qquad (5,465/128)
]
there is a real (d_C>0) and a threshold (X_C) such that for every real
(xge X_C), the **strict-open** interval
((x,x+Csqrt{x}log x)) contains at least ((A+d_C)sqrt{x})
primes (the natural count is compared as a real number). The half-open
version is precisely an attained `GoodCoefficient(A,C)`. These are the
largest explicit leading coefficients given by direct inversion of the
three supplied curves; the slack is positive but not explicitly bounded
here. No CMS input is needed for these two bounds. Identifying the envelope
of all three applications uses RH and **all three** named analytic inputs,
including `CMSFunctionalInput.v1.population_reduction`.

## Transfer and endpoints

Write (y_C=x+Csqrt{x}log x) and (N(C,x)=pi_{mathbb R}(y_C)-
pi_{mathbb R}(x)), where (pi_{mathbb R}(t)) is the natural prime count
at the nonnegative floor of (t). For (x>1,C>0), this is the count in
((x,y_C]). The upper endpoint is nondecreasing in (C) for (xge1),
as the multiplier (sqrt{x}log x) is nonnegative, so
`GoodCoefficient(a,c)` implies `GoodCoefficient(a,C)` whenever (Cge c).
The same slack works after increasing the threshold to at least (1).

Let (M(C,x)) be the count in ((x,y_C)). Only (y_C) itself can be
removed from (N), and it contributes at most one. If the half-open
inequality has slack (delta>0), then for (x>1) beyond its threshold
and (xge (2/delta)^2),
[
 M(C,x)/sqrt{x} ge N(C,x)/sqrt{x}-1/sqrt{x}
  ge a+delta/2.
]
Thus a half-open GoodCoefficient is also a positive-slack strict-open
guarantee, with no enlargement of width. Conversely (Mle N), so the
strict positive-slack predicate implies the half-open one. Neither
argument replaces eventual quantifiers by an explicit onset.

## Exact envelope of the supplied width bounds

Let
[
 q=20582561296/24680948495,quad
 G(a)=q(1+2a),quad
 S(a)=944247/10^6+(1163388/10^6)a,quad
 F(a)=9/8+(16/15)a.
]
For (age0) the respective admissible-width sets **furnished by the
individual premises and width monotonicity** are ((G(a),infty)),
([S(a),infty)), ([F(a),infty)). For the first ray select
(epsilon=C-G(a)>0). This assertion describes the inputs, not the
unknown exact set of widths where the prime inequality is true.

Set
[
 u=rac{544470055511653}{2490320656859788},qquad
 v=rac{542259}{290164}.
]
Writing (S=s_0+s_1a), (F=f_0+f_1a), the two intersections follow
from (S-G=(2q-s_1)(u-a)) and (F-S=(s_1-f_1)(v-a));
(2q>s_1>f_1>0) and (0<u<v). Thus for (ale u),
(Gle Sle F); for (ule ale v), (Sle G,F); and for (age v),
(Fle Sle G). In particular the Gaussian-flat intersection does not
give an additional branch. Therefore the lower envelope is
[
 E(a)=min(G(a),S(a),F(a))=
 egin{cases}
 G(a)&0le a<u,\
 S(a)&ule a<v,\
 F(a)&vle a.
 end{cases}
]
The union of the furnished rays is ((E(a),infty)) for (a<u), and
([E(a),infty)) for (age u); the tie at (u) is attained by the
sparse curve, and both affine curves attain the tie at (v).
For (a<u) the assertion at width (E(a)) with positive slack for
**that** (a) is not supplied: we have an infimum of the furnished
widths, not a minimum. For the set of *all* actual good widths we only
infer (inf{C:mathrm{GoodCoefficient}(a,C)}le E(a)), not equality.

### Inversion at fixed width

All three slopes are positive, and their minimum is strictly increasing:
if (a<b), the line realizing the minimum at (b) is strictly larger
there than at (a), where it is at least (E(a)). It is continuous and
unbounded, with (E(0)=q). For (Cge q) write
[
 g(C)=(C-q)/(2q),quad s(C)=(10^6 C-944247)/1163388,quad
 f(C)=(15/16)(C-9/8).
]
Then (A(C)=E^{-1}(C)=max(g(C),s(C),f(C))): all lines at this
maximum are at least (C) and some line equals (C). The two switching
widths are
[
 
ho=E(u)=3731134672774344/3112900821074735,qquad
 sigma=E(v)=9048441/2901640 .
]
Use (g) on ([q,
ho)), (s) on ([
ho,sigma)), and (f) on
([sigma,infty)). For (q<C<
ho) every (0le a<A(C)) has an
eventual positive-slack guarantee, so the normalized strict and half-open
counts have liminf at least (A(C)). For example, for each
(eta>0) choose (a=max(0,A(C)-eta/2)<A(C)). This is not a
positive-slack guarantee for (A(C)), nor an argument for an eventual
pointwise bound at (A(C)). At (C=q) the nonnegative count gives the
zero liminf bound without any endpoint GoodCoefficient. For (C<q) no
nonnegative (a) is furnished directly. For (Cge
ho) the inverse
is attained and the positive-slack guarantee applies.

| (C) | Gaussian inverse (limiting for Gaussian) | Sparse inverse (attained) | Flat inverse (attained) | Winning branch |
|--:|--:|--:|--:|:--|
| 3 | (53460284189/41165122592) | (685251/387796) | (225/128) | sparse |
| 5 | (102822181179/41165122592) | (4055753/1163388) | (465/128) | flat |

Indeed (
ho<3<sigma<5), and substituting the winning coefficients
gives (S(685251/387796)=3) and (F(465/128)=5).
Approximately the resulting leading counts in units of (sqrt{x}) are
(1.767039887) and (3.6328125). Because of the unknown slack, there
exists a larger good population coefficient at the same width (take,
for instance, (A+delta/2) from half-open slack (delta)). Thus
“largest” is about the explicit direct inversion, not an optimality
statement about primes.

For a limitation of inference from monotonicity and the three curves,
consider a proxy count (lfloorsqrt{x},H_eta(C)
floor) for (x>1),
where (H_eta(C)=max(0,g(C),s(C)+eta,f(C)+eta)), (eta>0).
It is monotone in (C); its normalized limit is (H_eta(C)). Each
of the three premises holds with positive slack for this proxy: at
(G(a)+epsilon) the surplus is at least (epsilon/(2q)), and at
(S(a)) or (F(a)) it is at least (eta) in the limit.
For each fixed (0le a<u) choose (eta) smaller than the positive
differences (a-s(G(a))), (a-f(G(a))). Its limit at (G(a)) is
then (a), with no positive slack. For (a>0) the floor even makes
the bound at (a) fail at arbitrarily large real (x). At 3 and 5
the limit is exactly (A(C)+eta), with (eta) arbitrarily small.
This is only a proxy for the curve/monotonicity abstraction, not a
model of primes or a claim of independence from all the hypotheses.

## Exact comparison with the preserved octic baseline

Under its **separate** RH+Green+Nicolas+BPT package, put
[
 B(C)=(8/9)C-18203/20000,qquad
 O(a)=(9/8)(a+18203/20000).
]
The actual strict-open claim is (M(C,x)>(B(C)+(21/5)/log x)sqrt{x})
for (xge e^{24}) and (103/100le Cle16). This gives the
limiting leading-width comparison (O(a)) only for
(973/180000le ale2396173/180000) (invert the exact domain
endpoints). It does not by itself assert positive limiting slack
at (C=O(a)); the logarithmic correction there tends to zero.

| (C) | (B(C)) | Count gain (A(C)-B(C)) | Width saving (O(A(C))-C) |
|--:|--:|--:|--:|
| 3 | (105391/60000) | (61212941/5816940000) | (183638823/15511840000) |
| 5 | (636173/180000) | (70933/720000) | (70933/640000) |

These are differences of certified **leading bounds**, not differences
of observed prime counts. The width savings are (9/8) times the
count gains by inversion of (B); both (O(A(C))) are in the
baseline width domain. A comparison at all matching populations in the
octic domain is given by the exact differences
[
 O(a)-E(a)=
 egin{cases}
 (163827/160000-q)+(9/8-2q)a & a<u,\
 318687/4000000-(9597/250000)a & ule a<v,\
 -16173/160000+(7/120)a & vle a.
 end{cases}
]
The first two decrease and the last increases. The branches agree at
the switches, so the minimum on the stated domain is at (v), with
value (13152201/1658080000>0). On the Gaussian branch this is an
infimum-width comparison; every (0<epsilon<O(a)-E(a)) gives an
actual furnished width strictly smaller than (O(a)). Only (O(a))
needs to be in the baseline domain for this comparison. For a
same-width comparison throughout (103/100le Cle16), the exact
leading gain is (max(g(C),s(C),f(C))-B(C)>0): apply the width
inequality at (a=B(C)) and use strict increase of (E).
Two sample comparisons of *individual* lines go the other way:
the flat inverse at 3 has only a small positive gain (311/240000);
the sparse inverse at 5 loses (840041177/17450820000) to the old
leading count. The Gaussian inverse loses at both widths.

At (C=3,5), the leading gain exceeds the old logarithmic correction
if (log x) is strictly larger than (24431148000/61212941) and
(3024000/70933), respectively. This compares the formulae, not
their onsets, and can only compare guarantees where both theorems
apply. The original leading count (1) at (343827/160000)
retains its own explicit onset (e^{24}); (E(1)=421527/200000)
((=2.107635)) by the sparse curve, an attained eventual width
saving of (33027/800000). The latter has no such explicit onset.
There is no claim about best-known bounds, superiority under
identical assumptions, or dominance at finite (x) throughout the
octic range.

## Prime ranks

For (x>1) let (b=pi_{mathbb R}(x)). The strictly increasing
enumeration of all primes, indexed from (p_0=2), has exactly the
indices (0,dots,b-1) at or below (x). The next (M=M(C,x))
indices (b,dots,b+M-1), if any, are exactly the primes strictly
below (y_C) and above (x); any intervening prime below one of
them would also be in this interval, and an endpoint prime (y_C)
is not included. Hence for any (0le m<M),
(x<p_{b+m}<y_C). The positive slack at 3 and 5 gives
(M>Asqrt{x}), so one may take (m=lfloor Asqrt{x}
floor).
For (x=p_n), (b=n+1), giving
[
 0<p_{n+1+lfloor Asqrt{p_n}
floor}-p_n
   < Csqrt{p_n}log p_n
 quad	ext{for all sufficiently large }n.
]
The index substitution is eventual since a strictly increasing
sequence of integers beginning at 2 satisfies (p_nge n+2).
No strict bound follows just from keeping the largest index of
the original half-open interval without an endpoint check.

## Verification levels

* Written derivation above takes the three supplied coordinator
  statements as explicit mathematical premises with their stated
  RH and named analytic dependencies. See `sources.md` for exact
  locators. The curves are not claimed to be literal paper theorems.
* `Transfer.lean` imports only generic Mathlib. It restates the
  matching definitions and takes the three curve propositions as
  theorem **arguments**. It checks the conditional transfer, not
  the application-level import or the analytic premises. No new
  axiom/declaration standing in for a curve is used.
* The supplied Gaussian is kernel-verified, not source-first PV.
  Supplied coordinator BR results have both kernel-only numerical
  routes and separate actual C source/AST/execution routes. The
  flat assignment does not expose their proof objects for replay
  here, so this submission does not certify its own source-first
  route. This distinction is independent of the exact rational
  comparisons above. No explicit onset, original large FFT PV,
  or broader optimization is established.
