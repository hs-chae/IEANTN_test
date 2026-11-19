# Sharper density layer (B0 and D02)

Use the definitions and inherited hypotheses in spectral.md, in particular
Dusart2018 original PDF p.5, Theorem 2.3 and the count and smoothing
proofs there. Write b=7/8 in B0, b=27/32 in D02, a=1-b,
s_j=j/800, 616<=j<=800b. The latter cap, including its usefulness
below exp(200), is the consequence of the additional direct-psi input
proved in spectral.md. The improvements below do not impose RH.

## Improved layer estimates

With the notation p,q,G_s,C,ell from spectral.md, stop the density
linearization one step earlier. For y>=0 the twice-count divided by
H exp(y) is at most
```
K_s(y) = G_s exp(-(1-p)y)(1+y/ell)^q
       + C exp(-y)(1+y/ell)^2.
```
This follows by log(1+z)<=z, without replacing (1+y/ell)^q by an
exponential. For the unweighted layer let D*(s)=integral K_s(y)dy
over [0,infinity). For width h fixed let D*_h(s) be the integral with
the nonnegative multiplier m_A(y)=1 for 0<=y<log A when A>1, and
2A exp(-y) otherwise, A=2/(Hh). This is the derivative measure in
partial summation with min(1/t,2/(ht²)); the weight itself is
continuous at the split. These are upper majorants for the weighted
counts in the proof of (S), not estimates from zero samples.

For each fixed y, K_s(y) is a decreasing exponential in s plus a
constant, because its first term is proportional to
(3H exp(y))^p (ell+y)^q. Hence both true integrals are decreasing
and convex in s. At a node use the degree-four Taylor polynomial
at 0 for (1+Y)^q, Y=y/ell: the derivative of order five is negative
for 3<q<4, so this bounds the integrand above on the whole
positive axis. This gives five elementary gamma moments in addition
to the three from the second term; the unweighted moment with
rate d=1-p is n!/d^(n+1). On a damped tail starting at z=log A,
the moment with any rate d'>0 is
```
exp(-d'z) sum_(i=0)^n binom(n,i) z^(n-i) i!/(d')^(i+1).
```
When A>1 the damped total is unweighted total minus the tail at d
plus 2A times the tail at d+1; when A<=1 it is just the rate d+1
total times 2A. Use these formulas also at rate 1 in the second
density term. At undamped nodes we may take the old D(s) minimum
as well. This proves every node enclosure in repair_spectral.py.

Let M_j be the upper endpoints of these numerical node bounds.
Use piecewise-linear chords M(s) between M_j. Convexity of D* or
D*_h proves domination between nodes; one does not assert that an
upper Taylor enclosure must itself be convex. The script checks the
node bounds are nonincreasing. For fixed h one can also use a constant
upper bound W for the full high weight A_h. If initial nodes exceed W,
replace them and the first remaining node by W. The constant panels
are valid by the full weight bound, and subsequent chords are valid
by convexity including their endpoints. Clipping *all* the nodes at
W without accounting for the transition panel would not prove a
bound inside that panel. For the default width h=e^(-u/4), take
full high weight majorant A=U(u) and use the undamped nodes.
For fixed widths take A=W. All fixed-width uses below are in
0<h<=.1 and u>=100. Default secant uses below are on u>=140.

Layer integration of the right-hand exponential in (S) now uses
M(s) on [s_0,b]. After division by e^(-au), integration by parts
gives
```
M(b) + (A-M(s_0)) e^(-(b-s_0)u)
     + integral_(s_0)^b [-M'(s)] e^(-(b-s)u) ds.
```
The remaining high base term is A exp(-(s_0-a)u), and the
low term is 116 exp(-(.5-a)u). Equivalently, with f=exp(-u/800),
the integral is (1-f)/(u/800) times the polynomial with coefficients
M_j-M_(j+1), in descending j order of powers (highest power for
j=616). Add the pole bias and the constant/trivial terms by the
same smoothing proof as before. Call the **unnormalized** result
E_sec(u;b,h), or E_sec(u;b) for the default width. The use of a
convex interpolant here is not a presumption that samples of
an arithmetic function control the entire interval.

For the default, U(140)>2M(s_0) and U'/U<=2/u give the same
4/u logarithmic-derivative control for U-M(s_0) as in spectral.md.
The integral is a nonnegative mixture of exponentials independent
of u, with rates b-s after normalization. Thus E_sec/e^(-au)
is nonincreasing for u>=140, and u^m E_sec is nonincreasing for
u>=max(140,(m+4)/a), for m>=0 used here. Verify the latter directly
with the unnormalized rates at least a, including the 4/u loss
for the two coefficients involving U; the factor 1+2h decreases.
For fixed h the normalized bound is instead convex in u: it is
a nonnegative mixture of real exponentials, including the increasing
bias term (constant before normalization). Its unnormalized value
is nonincreasing. The same convexity holds for the old fixed-h
step bound. The nonincreasing default coefficient has limit M(b).
In the unnormalized formula the default layer only improves by
reducing the cap: the node bounds on the common range are identical
and the integrated excess from any extra panels is nonnegative.

## Power constants for Mertens

The definitions and signs of all four errors are exactly those in
mertens.md. A new explicit all-point choice on u>=140 is the
default E_sec plus the unchanged primitive (P), transferred
by (M1)-(M2) with their signed endpoints. Take its minimum with
all applicable prior branches and, for D02, the fixed widths in
repair_spectral.py (on u>=140). The full default coefficient common to the four
components, before exponential conversion, is bounded by
```
 z(u)=exp(au) E_sec(u;b)+1.212 exp(-(.5-a)u)+21/H+3 exp(-(1-a)u).
```
This is the same primitive and prime-power allowance proved
in mertens.md. A single safe coefficient for the four is
z(u) exp(z(u)e^(-au)/u), which is decreasing for u>=140.
The first three errors are bounded by the coefficient times
x^(-a)/u, the fourth times x^(-a). This coefficient approaches
at most .006665 on B0 and .11625 on D02 (including the 21/H
allowance; the exact node bounds are in the receipt). This is
a limit estimate for the *majorant*, not a claim about a limit
of observed arithmetic errors.

Every nonempty entry gives a strict bound on the corresponding closed
real ray; an earlier still-valid old branch need not be dropped.

| log onset | B0 coefficient | D02 coefficient |
|---:|---:|---:|
|166.4|—|.235|
|170|.01444|.235|
|184|.0134|.234|
|190|.01285|.2265|
|200|.01228|.21614|
|250|.01051|.18432|
|300|.00959|.16793|
|400|.00865|.15116|
|600|.00787|.13746|
|1000|.00734|.12817|
|2000|.006990|.12198|
|10000|.006729|.11739|

The early D02 .235 row uses closed intervals [166.4,167], [167,168],
and every quarter-log interval from 168 to 184. On each we choose
one and the same width at both ends (and one layer formula); the
normalized estimate plus the displayed allowance is convex. We use
the maximal upper endpoint and exponentiate with the left log endpoint,
which suffices on the entire slab. The .234 default ray covers the
right join. The rigorous receipt names every chosen width. This is
a different bridge from the old .277, not an interpolation of
pointwise optimized endpoint values at differing widths.

On the matched refined simple rays from u=200 the D02/B0 ratio
is (.21614/.01228)e^(-u/32)<.0341, decreasing. The original-source
and within-method comparisons and their scope are in sources.md and
mertens.md. For the refined **pointwise** comparison, the previous
B0 uncertainty barrier continues to apply to the new B0 default secant
estimate because M(b)>.0066; the new fixed-width branch is used only
for D02 in this comparison. The additional B0 power rows are above
the barrier too (their coefficients exceed .0017). On 166.4<=u<=168
the old split at h=2.1e-12 still proves the psi/weighted B0 floor
pi/H: the last-bin comparison was checked at 168 and does not weaken
as u decreases. The two fixed secant choices for D02 on those slabs
are <1.042e-12 after allowances and conversion (in units 1 or 1/u),
by monotonicity of the unnormalized estimate and the enclosures
at their left endpoints. From 168 onward the new .235 ray sits
strictly below both B0 barrier pieces, with ratios bounded by
.95 in the constant regime and .0016/.0017 in the power regime,
using their comparisons at 168 and the decreasing power ratios.
As in mertens.md, in the selected B0 signed theta/pi transfers the
endpoint uncertainty can be diminished by the explicitly bounded
prime-power subtractions, at most O(e^(-u/2)), but not by the
nonnegative error-tail allowance. In particular use the old explicit
theta and pi upper subtractions bounded by 3e^(-u/2) in normalized
units and the product continuous correction by 2e^(-u)/u;
these are <1e-35 after scaling to the endpoint units at 166.4,
and their ratios to the barrier decrease. They cannot absorb the
strict gaps here. Conversion of the small log-product widths is
monotone on both signed endpoints; alternatively 1-e^(-t)>=t-t²/2
makes the corresponding lower comparison for the estimating
formula. This comparison is of explicit envelopes, not lower
bounds for any actual errors, nor a limit on all possible proofs.
