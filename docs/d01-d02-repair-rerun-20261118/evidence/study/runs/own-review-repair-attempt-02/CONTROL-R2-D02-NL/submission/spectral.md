# A common spectral majorant (proof)

Write H = 3000000000000 and b_0=7/8, b_1=27/32. Throughout, B0 means the
seven packet sources, with their own hypotheses and inherited numerical
trust; D02 means B0 and the additional real, right-continuous psi bound in
the input contract. With B0 use b=b_0; with D02 use b=b_1. Put a=1-b,
u=log x, and g(u)=e^(-u) psi(e^u)-1. In particular all complementary
exponents used below are positive. No form of full RH is assumed.

## How the extra input is used below its stated x threshold

For Re s>1 Euler's product, absolute convergence, and Stieltjes integration give
[
 -\zeta'/\zeta(s)
   ={s\over s-1}+s\int_1^\infty (\psi(t)-t)t^{-s-1}dt.
]
The integral up to e^200 is entire and the remaining integral is locally
normally convergent for Re s>27/32 under D02. For example on a compact set
with Re s >= 27/32+epsilon, its integrand is dominated by a constant times
t^(-1-epsilon) (log t)^2. By uniqueness of meromorphic continuation, the
log derivative has no pole in this open half-plane other than s=1. A
zero of any positive multiplicity would give a pole there. Thus D02
implies Re rho <= 27/32. This is more information than plugging in the
pointwise bound only on u>=200. It does not prove anything about the line
Re s=27/32 itself. B0 independently gives Re rho <=7/8 (OpenAIQRH,
Theorem 1.1, original PDF p.4). Symmetry gives 1-b <= Re rho <= b.
FiniteRH Theorem 1 (original PDF p.2, height 3000175332800), or
Platt–Trudgian Lemma 4 (p.4), puts the zeros up to H on the critical line.
Nontrivial zeros are counted with multiplicity. No real zero lies in
(0,1): the convergent alternating eta series is positive there and
equals (1-2^(1-s)) zeta(s) by continuation.

## Bounds for frequency weights

The following uses Dusart, §2.2.2 Theorem 2.3, original PDF p.5, as
stated there (positive ordinates, beta >= s). For s>=.77 and t>=H define
[
 \ell=\log H,\quad p={8\over3}(1-s),\quad q=5-2s,\quad
 d=1-p-q/\ell,\quad d_2=1-2/\ell,
]
[
 G_s=9.8 \,3^p \ell^q H^{p-1},\qquad C=103\ell^2/H .
]
Using log(1+z)<=z and (1+y/ell)^q<=exp(qy/ell), the number N_s(t)
of positive-ordinate zeros with real part >=s satisfies
[
 2N_s(He^y)/(He^y)\le G_s e^{-dy}+C e^{-d_2y}\qquad(y\ge0).
]
Both d,d_2 are positive. As N_s has no contribution at or below H, integrate
against -w'(t). For w=1/t the bound on 2 sum w is
D(s)=G_s/d+C/d_2. For w=1/t^2 it is
D_2(s)=(2/H)(G_s/(1+d)+C/(1+d_2)). For
w=min(1/t,2/(ht^2)), replace each factor 1/d by f(A,d), A=2/(Hh), where
[
 f(A,d)=\begin{cases}2A/(1+d),&A\le1,\\
 (1-A^{-d})/d+2A^{-d}/(1+d),&A\ge1.
 \end{cases}
]
This follows by splitting at y=log A; one can also take the minimum with
the undamped D(s). These bounds decrease as s increases: before any
linearization the majorants with p and q are monotone in s, and the
linearized count bound remains monotone at each y. For a fixed s the
undamped integral majorant for w=1/t also bounds the damped one.

For all positive ordinates >=H, the full count N(t) is at most
t log(t)/6 for t>=H. Indeed FKS Lemma 2.1 and Remark 2.2 (original
PDF pp.4–5, Rosser constants) bound the discrepancy from
(t/(2pi))log(t/(2pi e))+7/8 by .137 log t+.443 log log t+1.588.
Using the larger full count instead of the count above H in -w' integrals,
the bound on sum w (not twice the sum) is
[
 A_h=\begin{cases}
 A(\ell+1)/3,& A\le1,\\
 [\ell v+v^2/2+2(\ell+v+1)]/6,& A\ge1,\ v=\log A .
 \end{cases}
]
For the square weight use A_2=10/H, by the same integration with
2/t^3: the integral is (ell+1)/(3H)<10/H. For the default h=e^(-u/4)
we can use the simpler
[
 U(u)=((u/4)^2/2+32(u/4)+64)/6
]
in place of A_h (ell<29, log A<=u/4). For low ordinates twice the
sum of 1/gamma is <116: use FKS Table 1 and Lemma 2.1 with
T0=30610046000 and H. For twice the sum of 1/gamma^2 use .1: the first
ordinate exceeds 14 (CH2 §B.1, original PDF p.43), FKS Table 1 at
100 gives a reciprocal sum <.5922435112, and CH2 Lemma B.5 (p.44)
bounds the tail above 100. The strict numerical inequalities are in
certify.py. Endpoint ordinates, if present in these statements, can
be handled by including the equality in the high bin and by taking a
one-sided limit in the count bound.

## A layer bound and the real psi estimates

Let s_0=.77, with grid s_j=j/800 starting at j=616 and ending at
j=800b, an integer in both cases. If A is the chosen bound for all
high ordinates and D_j a bound for twice the sum of their weights at
Re rho >=s_j, use
[
 F_b(u)=C_{lo}e^{-u/2}+A(e^{-s_0u}+e^{-(1-s_0)u})+
 \sum_{j=616}^{800b-1}\min(A,D_j)
 (e^{-(1-s_{j+1})u}-e^{-(1-s_j)u}).                      \tag{S}
]
To prove it, pair beta and 1-beta at each positive ordinate.
Their normalized exponential sum is at most e^(-s0 u)+e^(-(1-s0)u)
if beta<=s0 on the right of the pair, by convexity. Above s0 the
excess is at most the increase in the right-hand exponential
(the left-hand exponential decreases). Layer integration, or its
left-bin upper sum in (S), counts each right-hand zero twice after
including negative ordinates. This extra weighted count is at most
A as well as D_j. Zeros on the critical line obey the same base bound.
Thus (S) bounds the sum over both signs with weights w; no
independence of terms in an explicit formula is used. One may also
use the weighted layer integral instead of the upper grid sum.
The code collects coefficients: the base at exponent 1-s0 has
coefficient A-min(A,D_616), the intermediate coefficients are
successive nonnegative differences, and the last coefficient is
min(A,D_(800b-1)).

Dusart (2.1), original PDF pp.3–4, gives the classical explicit
formula with midpoint values at jumps. Its use here is only under
integration. For clarity, the series also converges in L^2 on every
compact interval of u>0. Choose a smooth nonnegative bump at least
1 on the interval. In a unit frequency bin the sum of absolute
coefficients is O(log(2+|j|)/(1+|j|)) by the count bound (the local
count is O(log t)). Integration of each product against the bump
twice by parts bounds its cross-bin integral by a constant times
(1+|j-k|)^(-2); the real parts of the exponentials range in a compact
set. The inequality 2 a_j a_k <=a_j^2+a_k^2 proves the Cauchy
statement. The L^2 limit agrees almost everywhere with (2.1) by
an almost-everywhere convergent subsequence and the given pointwise
formula off prime powers. This justifies averaging term by term.
The arguments below with finite integrals followed by limits are
also legitimate: the integrated coefficients are absolutely
summable by the square-frequency count bound.

For u>=100, use monotonicity to squeeze psi(e^u) between the
backward and forward uniform log averages of width h (0<h<=.1).
In each direction the pole term differs from e^u by at most
e^u h e^h/2. The coefficient of a zero acquires a factor at most
e^h min(1,2/(h gamma)) from integrating e^(rho v). The trivial-zero
and constant term together have absolute value <2 before
normalization. Consequently, for **right-continuous psi at all real
x**, not a midpoint convention,
[
 E_h(u)=(1+2h)(h/2+F_b(u))+2e^{-u}, \qquad |g(u)|\le E_h(u).
]
Use C_lo=116. For h=e^(-u/4) one can take U(u) and D(s) undamped
in (S). Fixed h uses A_h and the damped density. Taking the infimum
over admissible h is valid; the executable uses the default h plus a
finite width menu. Set E_b(u) to the minimum of these, the common
source half-widths (sources.md), and, for D02 and u>=200, u^2 e^(-5u/32)/64.
Every entry is an upper bound, so endpoints can use any applicable entry.

An explicit continuous-layer alternative for u>=140 is
[
 E_{\rm cont}(u)=(1+2h)\{h/2+116 e^{-u/2}
       +U(u)(e^{-s_0u}+e^{-(1-s_0)u})
       +D(b){u\over u-97}e^{-a u}\}+2e^{-u}.
]
Indeed |(log(G_s/d))'|<= (8/3)(ell+log 3)+2 log ell
+ (8/3+2/ell)/d(s0)<97; the other term in D is constant. Thus
D(s)<=D(b)e^(97(b-s)), and direct integration proves the formula.
The limit of this coefficient after division by e^(-a u) is D(b).
Numerically D(7/8)<.006740 and D(27/32)<.118073 (direct interval
evaluation of dat in profiles.py); these are coefficients of a
proved majorant, not lower bounds on the arithmetic error.

For the default E_h and E_cont, their quotients by e^(-a u) decrease
on u>=140. For the grid version, U(140)>2D(s0), and U'/U<=2/u, so
(U-D(s0))'/ (U-D(s0))<=4/u. The base exponents after factoring are
>=.23-a, and 4/140<.23-a for both caps. The remaining coefficients
are nonnegative constants (including the last); the factors
1+2h and u/(u-97) in the respective bounds are decreasing.
More generally multiplying the unnormalized bounds by u^m preserves
monotonic decrease on u>=max(140,(m+4)/a); this follows by applying
the logarithmic derivative estimate to each positive term. These
are whole-ray checks, not extrapolations from tabulated points.

## Primitive and finite cut integrals

Define S_b(u) to be (S) with C_lo=.1, A=A_2, D_j=D_2(s_j), plus
2e^(-u). For u>=log 2,
[
 |\int_u^\infty g(v)dv|\le S_b(u)
 \le .1 e^{-u/2}+(20/H)e^{-au}+2e^{-u}.                 \tag{P}
]
Integration of a zero gives the extra denominator 1-rho, whose
modulus is at least |gamma|, and the trivial terms obey the
displayed exponential bound. Finite sums of integrated coefficients
are dominated by the same convergent square-weight series as the
upper endpoint goes to infinity. In later use of (P) the square
series also bounds |sum e^((rho-1)u)/rho^2| and the corresponding
denominators |1-rho|^2; no pointwise convergence of a new
undifferentiated series at the jumps is needed.

On generic boxes of log width in these proofs the monotone endpoints
are literal real endpoints. The decimal interval replay (correctly
rounded Decimal exp and ln bracketed by neighbors, directed algebra)
only checks numerical inequalities after the analytic bounds are in
place. No finite proof here is advertised as source-first PV or Lean.
