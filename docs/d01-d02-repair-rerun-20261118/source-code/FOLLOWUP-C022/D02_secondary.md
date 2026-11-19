# D02 secondary consequences (not separate application trials)

These are additional to, not substitutions for, the D01 secondary
portfolio. Use D02.md's A and source inputs. Each threshold is real
and inclusive. Replay `/usr/bin/python3.10 -B d02secondary.py`
and the primorial test in `d02m.py`.

**A specified primorial.** For $n_x=\prod_{p\le x}p$ and $L\ge155$,
$$
 \left|\frac{n_x/\varphi(n_x)}{e^{\gamma} \log \log n_x}-1\right|
                  < 3.273\cdot 10^{-13}\,x^{-a}/L ,
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
For $|w|\le.01,L\ge155$ the difference
$w/L-\log(1+\log(1+w)/L)$ is bounded by $w^2/L$.
Indeed the first log remainder is at most $w^2/(2\cdot.99)$;
with $z=\log(1+w)/L$, $|z|\le |w|/(.99L)$ and the second
remainder is at most $z^2/[2(1-|z|)]$. After normalization
by $w^2/L$ the two allowances sum to less than 1, checked
at the extremal parameters. Thus the log envelope is
$$
 J_K + (2\cdot1.000000147\, e^{-L/2}+2.67e^{-2L/3})/L
         +1/(2\lfloor x\rfloor) +w^2/L.
$$
This uses $P_c\le1.000000147e^{-L/2}+1.78e^{-2L/3}$
and its positive integrated kernel from the inherited proofs,
and the new smoothed $J_K$.
Multiply by $Le^{aL}$; aside from the quadratic, all terms
decrease from 155. Use $|w|\le A_0+117e^{-L/2}$ up to
167.84; the normalized square is a positive sum of
exponentials, hence convex, so its maximum is at an endpoint.
Thereafter use $|w|<.257e^{-aL}$, with decreasing normalized
quadratic. Convert back from log by the usual exponential
guard. The quadratic and prime-power terms vanish in the
limsup after scaling and the remaining coefficient is the
reciprocal-square terminal bound. This improves the historical
D02 .0069 coefficient and earlier threshold $e^{200}$ by
using the exact integrated formula rather than its unsmoothed
cutoff remainder. The distinct B0 $1/8$ estimate in
`secondary.md` can still be kept in the min.
No sign about primorials is claimed.

**Extremal totient ratio.** For $(L_0,c)=(169,.513)$ or
$(174,.4982)$ and every real $N$ with $\log\log N\ge L_0$,
$$
\left|e^{-\gamma}\max_{1\le n\le N,\ n\in\mathbb N}
     n/\varphi(n)-\log\log N\right|<c(\log N)^{-a}.
$$
Set $Y=\log N,u=Y^{-a}$ and $t_\pm=Y(1\pm d u)$.
For $L_0=169$ use cap $C=.256418$ and $d=.2565$; for
$174$ use $C=.249,d=.2491$. Then $\log t_\pm\ge L_0-1$.
The certified theta inequalities with coefficient $C$
at exponent $b$ imply $\theta(t_-)<Y<\theta(t_+)$ by
$(1+v)^b\le1+v$ for $v\ge0$ and $C(1+du)<d$.
The primorial through $t_-$ is available and the one
through $t_+$ is not. At fixed cardinality the smallest
primes minimize the product and maximize the totient
ratio, so the extremum lies between $Q(t_-)$ and $Q(t_+)$.
Using Mertens' cap $C$ on the same domain and
$|\log(1\pm du)|\le du/(1-du)$, $t_\pm^{-a}\le u/(1-du)$,
the normalized additive error is at most $(C+d)u/(1-du)<cu$.
It also bounds $\sigma(n)/n$ from above via finite geometric
sums. Both new shapes improve the old .02635 bound at
the $1/8$ exponent from the common loglog start 181 by the
ratio test, retaining earlier or weaker-premise tradeoffs.

**Simple interval lengths.** For the following rows, if
$L\ge L_0$ and $y=x+g_0x^b$, then
$\pi(y)-\pi(x)>m x^b/\log y$.

| $L_0$ | theta cap $C$ | $g_0$ | $m$ |
|---:|---:|---:|---:|
|168|.256418|.514|.0011|
|180|.237637|.476|.0007|
|200|.215402|.432|.0011|
|173|.248838|.499|.000999|
|185|.232384|.465|.00023|
|204|.212|.426|.00069|

Subtract the theta bounds with coefficient $C$ and use
$y^b\le x^b(1+bg_0x^{-a})$. The reserve in $x^b$ units is
$g_0-C(2+bg_0x^{-a})>m$, checked at each start and increasing
thereafter. Thus we keep the old lengths at later starts and
prove slightly longer lengths at the original onsets; the old
shorter-length claims with those early starts are not used.
Keep B0 premise tradeoffs and the shorter exponent below.

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

In the union of the relevant FKS Table 8 first-panel intervals
$5/8\le s\le b$ one can take $c\le12,d\le6$.
Set $\lambda=1-p, p=(8/3)(1-s), q=3+3p/4$.
The two-sided mass for $\min(\delta,3/\gamma)$ in the
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
and for $s\ge.75$ it is $<2$ using $\lambda z\ge L/9$.
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
using $3x^s e^{-z}/g\le e^{-aL}$.

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
