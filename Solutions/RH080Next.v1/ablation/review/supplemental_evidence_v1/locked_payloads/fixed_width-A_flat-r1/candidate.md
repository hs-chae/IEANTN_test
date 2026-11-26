# Conditional population transfer (A-flat)

Let (q=20582561296/24680948495), (G(a)=q(1+2a)),
(S(a)=(944247+1163388a)/10^6), and (F(a)=9/8+(16/15)a).
The analytic hypotheses are ordinary zeta RH, with
`CMSFunctionalInput.v1.population_reduction` for (G);
and with both `BRFourierInput.v1.norm_identity` and
`BRFourierInput.v1.uniform_population_q1` for (S,F).
The joint envelope uses the union of these hypotheses; the two fixed-width
winners need only RH and the two BR inputs.

**Width 3:** the sparse line gives
(mathrm{GoodCoefficient}(685251/387796,3)).
**Width 5:** the flat line gives
(mathrm{GoodCoefficient}(465/128,5)).
These equalities of widths follow by substitution into the affine lines.
Both statements have a positive, unspecified eventual margin. They also
hold for the strict-open count in place of the half-open count, with
possibly smaller margin and later threshold: at most one upper endpoint
prime is lost and (1/\sqrt{x}) eventually falls below half the margin.
The Gaussian and the other affine line give smaller leading targets at
each of those widths.

## Lower width envelope

The exact minimum of the three leading lines on (a\ge0) is
[
E(a)=\begin{cases}
G(a)&0\le a<u,\
S(a)&u\le a<v,\
F(a)&v\le a,
\end{cases}\qquad
u=\frac{544470055511653}{2490320656859788},\quad
v=\frac{542259}{290164}.
]
Indeed (u=(S(0)-G(0))/(G'-S')) and
(v=(F(0)-S(0))/(S'-F')), with strictly decreasing slopes and
(0<u<v). Before (u), (G<S<F); between, (S\le G) and
(S\le F); after (v), (F\le S<G).
The two ties have the common widths
(3731134672774344/3112900821074735) and (9048441/2901640).
For (a<u), every width strictly larger than (E(a)) is certified
by taking Gaussian epsilon equal to the difference; no assertion at
the endpoint follows from that route. Starting at (u), including both
ties, the minimum itself is certified by an affine theorem.
Monotonicity extends these certifications upward: for eventually (x\ge1),
the upper endpoint is increasing in the width, so prime counts and their
positive-denominator normalizations are nondecreasing.

## Octic comparison

The separate supplied RH+Green+Nicolas+BPT octic leading rates at
widths 3 and 5 are (105391/60000) and (636173/180000). The gains
in leading population constants are respectively
(61212941/5816940000) and (70933/720000).
This is not a pointwise comparison with the full explicit octic lower
bound, which has an additional ((21/5)/\log x) in the normalized count.
It holds for real (x\ge e^{24}) and (103/100\le C\le16) under
its own assumptions; in particular its strict-open leading count 1 at
(343827/160000=2.14891875) keeps that onset. The new thresholds are
eventual only. No literature-optimality or general superiority claim.
