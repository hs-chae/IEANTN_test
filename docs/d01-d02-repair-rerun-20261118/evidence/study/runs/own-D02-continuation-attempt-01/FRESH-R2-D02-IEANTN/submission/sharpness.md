# What would improve the power? Spectral converses

These equivalences are for bounds on an eventual **whole real ray**,
with an unspecified finite constant and onset. They explain a
remaining analytic bottleneck; they are not a lower bound on
the actual errors and not a proof of logical independence from (B_0).

Fix (1/2<b<1) and write (eta=1-b). For (b=27/32), each of
the following alone, in the presence of the common originals, implies
zero-freeness of (zeta) in (Re s>b):

1. Any one of the three separate bounds (O(x^{-eta}/log x))
   for the two relative product errors or (|S|), or the bound
   (O(x^{-eta})) for (|W|).
2. The **one-sided** exact-Li gap bound
   (G(t)gemathcal L(t)-O(t^4e^{-eta t})).

Conversely, at (b=27/32) the zero restriction gives all these
bounds, with explicit constants, by the spectral proof in
`d02-proof.md`; it also recovers the exact D02 hypothesis on
(tge200). Thus in these power-shape classes, not just the
direct-(psi) estimate, a proof from the common originals alone
would suffice to prove the added premise. The same necessary
zero restriction holds for any (1/2<b<1) in (1)–(2); a strictly
larger exponent for these shape bounds would require a stronger
zero restriction than the one proved here. This does not rule out
smaller numerical constants or better elementary-polynomial profiles.

## Mertens converse

For (|W|) use (F=W-J_0); for (|S|) use (U=S-J_1).
For either product, take the logarithm (the normalized product
tends to 1, so (|log(1+v)|le 2|v|) for (|v|le1/2)), then
(U=Z-J_{1,c}). All prime-power tails are of smaller order by
(PP), since (eta<1/2). For (U=O(e^{-eta t}/t)), recover
(F(e^t)=t U(e^t)+int_t^infty U(e^u),du) by integration by
parts using (dF=t,dU) in log coordinates and the limits at infinity.
Thus (F(x)=O(x^{-eta})) in every case. For (Re z>0),
Stieltjes summation or the absolutely convergent Euler product gives
[
 -zeta'(1+z)/zeta(1+z)
   = zint_1^infty Big(sum_{nle x}rac{Lambda(n)}nBig)x^{-z-1},dx
   = 1/z-gamma+zint_1^infty F(x)x^{-z-1},dx .
]
The last integral is holomorphic for (Re z>-eta).
A zeta zero in the indicated half-plane would give a nonremovable pole
there, other than the displayed pole belonging to (zeta(1+z)).

## One-sided Ramanujan converse

Use (q(t)=t e^{-t}[pi(e^t)-operatorname{li}(e^t)]).
By original-input bounds (q(t)	o0), and (tf(t)	o1) by
the inherited Li barriers. Expand exactly:
[
 (G(t)-mathcal L(t))/t^4 =
 rac{t}{t-1}q(t-1)-q(t)ig(2tf(t)+q(t)ig).
]
On a sufficiently late real ray the divisor (2tf(t)+q(t)) is
positive, and the ratio (t/((t-1)(2tf(t)+q(t)))) lies in
((0,3/5]). Therefore a one-sided bound as in (2) gives
(q(t)^+le(3/5)q(t-1)^++C e^{-eta t}) for some constant (C).
There is a uniform finite anchor on the first unit interval,
since the prime count is locally bounded; iteration after multiplying
by (e^{eta t}) has geometric ratio ((3/5)e^eta<1)
((eta<1/2)). Consequently
[
 pi(x)-operatorname{li}(x)le C' x^b/log x
]
on an eventual real ray. Only an upper bound has been proved,
so one must not use an absolute-value prime-number-theorem
converse directly.

Choose (X>1) in this ray and use
(D(s)=sint_X^infty(pi(x)-operatorname{li}(x))x^{-s-1},dx)
initially on (Re s>1). There (D(s)) is the sum of a holomorphic
anchor term ((pi(X)-operatorname{li}(X))X^{-s}), the prime
zeta sum over (p>X), and (-int_X^infty x^{-s}/log x,dx).
On differentiating, the main two singular terms are
[
 D'(s) = zeta'(s)/zeta(s)+X^{1-s}/(s-1)+H(s)
]
where (H) is holomorphic for (Re s>1/2).
Indeed the prime-zeta decomposition in (Re s>1)
is (logzeta(s)-sum_{p,kge2}p^{-ks}/k); that double
sum and its derivative converge locally uniformly for
(Re s>1/2) by elementary geometric and integer sums.
The singularities at (s=1) cancel, and along the real
interval ((b,1)) there are no zeta zeros, by the paired
eta-series argument in `density.md`. Hence (D) admits
holomorphic continuation to a neighborhood of any real
segment contained in ((b,infty)), by integrating the
derivative starting at (s>1).

For completeness, if (g(x)ge0) on ([X,infty)) and its Mellin
integral (int_X^infty g(x)x^{-s-1},dx) has a finite abscissa
(sigma_c), it cannot extend holomorphically across the real
point (sigma_c). If it did, take a real (s_1>sigma_c)
sufficiently close that a Taylor disc at (s_1) extends to some
(s_2<sigma_c). The Taylor terms of the integral at (s_2)
are nonnegative: the (k)-th includes
((s_1-s_2)^kint_X^infty g(x)(log x)^k x^{-s_1-1},dx/k!).
The differentiated integrals exist by interior convergence.
Monotone convergence of the Taylor integrands gives convergence
at (s_2), a contradiction. If the integral instead converges
for all real (s), use its holomorphy there directly.
Apply this observation to (g(x)=C' x^b/log x
-(pi(x)-operatorname{li}(x))). Its Mellin integral has
holomorphic continuation along that same real ray (divide (D)
by (s) and add the known holomorphic transform of the majorant).
The convergence abscissa is therefore at most (b).
Consequently (D(s)) is holomorphic in (Re s>b);
the logarithmic derivative identity excludes zeros there.
This proof does not presume global boundedness of a chosen
branch of (logzeta) across a possible zero.
