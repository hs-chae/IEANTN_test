# D02 secondary consequences (not separate application trials)

These are additional to, not substitutions for, the D01 secondary
portfolio. Use D02.md's A and source inputs. Each threshold is real
and inclusive. Replay `/usr/bin/python3.10 -B d02secondary.py`
and the primorial test in `d02m.py`.

**A specified primorial.** For $n_x=\prod_{p\le x}p$ and $L\ge155$,
$$
 \left|\frac{n_x/\varphi(n_x)}{e^{\gamma} \log \log n_x}-1\right|
                  < 6\cdot 10^{-13}\,x^{-a}/L ,
 \qquad
 \limsup_{x\to \infty} Lx^a
 \left|\frac{n_x/\varphi(n_x)}{e^{\gamma} \log \log n_x}-1\right|
                  <2.506\cdot10^{-14}.
$$
Indeed $w=\theta(x)/x-1$, and $\delta_Q$ with the direct
theta transfer has the term $w/L$. Euler's inclusion-exclusion
product for $\varphi$ and $\log n_x=\theta(x)$ show that the
logarithm of the displayed normalized factor is
$\delta_Q-\log(1+\log(1+w)/L)$.
The difference $w/L-\log(1+\log(1+w)/L)$ is bounded by
$2w^2/L$ for $|w|\le1/2, L\ge155$, using the logarithm
series twice. Thus the log envelope is
$$
 J_K + (2\cdot1.000000147\, e^{-L/2}+2.67e^{-2L/3})/L
         +1/(2\lfloor x\rfloor) +2w^2/L.
$$
This uses $P_c\le1.000000147e^{-L/2}+1.78e^{-2L/3}$
and its positive integrated kernel from the inherited proofs,
and the new smoothed $J_K$.
Multiply by $Le^{aL}$; aside from the quadratic, all terms
decrease from 155. Use $|w|\le A_0+117e^{-L/2}$ up to
167.656; the normalized square is a positive sum of
exponentials, hence convex, so its maximum is at an endpoint.
Thereafter use $|w|<.25e^{-aL}$, with decreasing normalized
quadratic. Convert back from log by the usual exponential
guard. The quadratic and prime-power terms vanish in the
limsup after scaling and the remaining coefficient is the
reciprocal-square terminal bound. This improves the historical
D02 .0069 coefficient and earlier threshold $e^{200}$ by
using the exact integrated formula rather than its unsmoothed
cutoff remainder. The distinct B0 $1/8$ estimate in
`secondary.md` can still be kept in the min.
No sign about primorials is claimed.

**Extremal totient ratio.** For real $N$ with
$\log \log N\ge169$,
$$
 \left|e^{-\gamma}\max_{1\le n\le N, n\in\mathbb N}
                  n/\varphi(n)-\log \log N\right|
             <.4982(\log N)^{-a}.
$$
Use $Y=\log N, u=Y^{-a}$ and
$t_\pm=Y(1\pm.2491u)$. These have $\log t_\pm \ge168$.
The theta inequalities with coefficient .249 and exponent $b$
give $\theta(t_-)<Y<\theta(t_+)$ by the concave tangent
for the $b$th power $or ((1+v)^b\le1+v)$.
The available primorial at $t_-$ and the upper bound on
the number of distinct primes from $t_+$ sandwich the
maximum between $Q(t_-)$ and $Q(t_+)$: at fixed
cardinality the smallest primes both minimize their product
and maximize the totient ratio. Normalize, and apply the .249
envelope for $Q$ valid since $L\ge168$, the bound
$|\log(1\pm.2491u)|\le.2491u/(1-.2491u)$, and
$t_\pm^{-a}\le u/(1-.2491u)$. It also bounds $sigma(n)/n$
from above via the finite geometric products.
The .4982 comparison with the old .02635 in the $1/8$
exponent holds on their entire common ray by the ratio at
181 and monotonicity.

**Simple interval lengths.** For $(L_0,C,g_0,m)$ equal to
$$
 (168,.249,.499,.000999),\quad
 (180,.232384,.465,.00023),\quad
 (200,.212654,.426,.00069)
$$
and $y=x+g_0 x^b, L\ge L_0$,
$\pi(y)-\pi(x)>m x^b/\log y$.
Subtract the normalized theta bounds with coefficient $C$
and use $y^b\le x^b(1+b g_0x^{-a})$. Then the difference
in theta is at least
$x^b[g_0-C(2+bg_0x^{-a})]>m x^b$ by the point test
and monotonicity. The earlier .465 interval from $e^{200}$
is improved in onset; the later .426 conversion gives
shorter lengths. Keep the B0 premise tradeoffs and the
shorter exponent below.

**Correlated endpoints, improved logarithmic factor.** For
every real $x\ge e^{100000}$, let
$$
 g=x^{5/8}L^{207/20},\qquad y=x+g .
$$
Then $\pi(y)-\pi(x)>.81g/\log y$.
This replaces the inherited exponent 14 of $L$ at the same
onset by 10.35, and raises the constant in units of the
new shorter length (not a comparison of absolute counts
in two different intervals).

Here are analytic and numerical details. Put
$k=207/20, \delta=g/x, Z=3/\delta, z=\log Z
=3L/8-k\log L+\log3$, $s_0=5/8+1/L$.
For $L\ge100000$ we have $0<\delta<1, L/3<z<2L/5, Z>H$.
Use the FKS signed formula at each endpoint $v=x,y$,
with $T_v=v^{2/5}$. Its cutoff is at least $Z$, and is
below $v$; the admissibility inequalities follow at these
heights as in D02.md §3. For $\beta \ge s_0$,
$$
 |(y^{\rho}-x^{\rho})/\rho|
       \le x^{\beta} \min(\delta,3/|\gamma|).
$$
Use the integral of the derivative for the first bound
and $1+(y/x)^{\beta} \le3$ for the second. For $s\ge s_0$
the density sums converge absolutely since $p(s)<1$.
In passing from the truncated to the full high sums the
two omitted endpoint tails together cost at most **one
more** absolute sum of the same positive weights: for each
omitted ordinate $\gamma>Z$ the weight is $3x^{\beta}/\gamma$,
and $x^{\beta}+y^{\beta} \le3x^{\beta}$.
The high cost is thus at most twice the full absolute
difference bound.

In the union of the relevant FKS Table 8 intervals
$5/8\le s\le b$ one can take $c\le12,d\le6$.
Set $\lambda=1-p, p=(8/3)(1-s), q=3+3p/4$.
The two-sided mass for (min(delta,3/gamma)) in the
tail above $s$ is at most $3V(s,z)$, where
$$
 V(s,z)=\frac{2c e^{-\lambda z}z^q}{\lambda}
            \sum_{j=0}^4(4)_j/(\lambda z)^j
                  +2d e^{-z}(z^2+2z+2).
$$
Indeed integrate $2 N(s,t)$ with $dt/t^2$ from $Z$,
since $3/Z=\delta$; and use
$(1+w/z)^q\le(1+w/z)^4$ with $t=Ze^w$.
Here $(4)_j=4!/(4-j)!$.
Using $\lambda z\ge8/9$, the sum is $<100$,
and for (sge.75) it is $<2$ using $\lambda z\ge L/9$.
The first term is respectively
$\le900 L z^q e^{-\lambda z}$ and
$\le144 z^q e^{-\lambda z}$.

Rather than summing independent unit log-bins, integrate
the **layer-cake** tail. On each substrip $[u,v]$ from
$s_0$ to .75 or from .75 to $b$ the bound is
$$
 3x^u V(u,z)+3L\int_u^v x^s V(s,z)\,ds.
$$
Endpoint atoms can be assigned to either piece, or use a
closed-bin cumulative bound by continuity from the left.
The density integral at any fixed numerical table join
is bounded by either one-sided continuous table majorant,
so no assumption about zeros on such joins is used.
The identity $x^s e^{-\lambda z}/g=3^{-\lambda}L^{-kp}$
simplifies this integral. Use $z^q\le(.4)^3 L^q$.
For the substrip below .75 use $p\ge2/3$ and its length
at most $1/8$. For the upper substrip integrate the affine
exponent exactly:
$$
 \int_{.75}^b L^{3-(k-.75)p(s)}\,ds
 \le L^{3-(k-.75)p(b)} /[(8/3)(k-.75)\log L].
$$
Now $p(b)=5/12$ and $(k-.75)p(b)=4$.
The resulting upper bound for the high contribution
divided by $g$, **before** doubling, is
$$
 172.8(1+L/8)L^{-12/5}
 +27.648(L^{-17/5}+1/(25.6\log L))
 +12(L^2+2L+2)(2+L)e^{-aL}.
$$
The last term includes both substrips' second terms
using $x^s,3e^{-z}/g\le e^{-aL}$.

By the total reciprocal bound in D02.md §3 the low portion,
FKS truncation and prime powers at both endpoints together
cost at most
$$
 L^{-k}\{4e[(L+1)^2/6+3]+8.364(L+1)e^{-L/40}+9e^{-L/8}\}
$$
in units of $g$, using $\log y\le L+1$,
$y^{s_0}\le2e x^{5/8}$, $y^{.6}\le2x^{.6}$.
Each term bounding these losses decreases from $L=100000$.
The exact arithmetic guard there gives sum of the doubled
high and other terms $<.19$. Thus $\theta(y)-\theta(x)>.81g$,
and each counted prime weighs at most $\log y$.
The cutoff cancellation and the new cap, not subtraction of
two unsigned estimates, are necessary in this proof.
