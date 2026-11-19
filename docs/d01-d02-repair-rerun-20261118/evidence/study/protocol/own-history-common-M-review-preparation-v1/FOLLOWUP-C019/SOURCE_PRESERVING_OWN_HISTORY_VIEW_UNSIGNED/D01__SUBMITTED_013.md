# Strongest analytic refinements and downstream consequences

These refinements have the same assumptions and conventions as candidate.md.
They keep the earlier, density-free quantitative Ramanujan result as a
separate route. The check script is `refine.py`; integrations and
monotonicity reduce the numerical obligations to finitely many directed
interval inequalities. The long finite Mertens sieve is not an input to
this file.

## A. Finer power envelope and quantitative Ramanujan inequality

Put $b=379/2$. Replace the grid of Section 1 by
$s_i=.77+i/10000$ $(0\le i\le1050)$. Replace (W) by
$$
 W_*(s,z)=2c,\frac{e^{-\lambda z} z^q}{\lambda}
 \sum_{j=0}^3\binom3j
 \le ft(\frac{j!}{(\lambda z)^j}+
       (q-3)\frac{(j+1)!}{(\lambda z)^{j+1}}\right)
 +2d e^{-z}(z^2+2z+2).
$$
This is a bound for the same integral, by
$(1+v/z)^q\le(1+v/z)^3[1+(q-3)v/z]$ for $v\ge0, 3\le q\le4$
(concavity), followed by integrating each power of $v$ against
$e^{-\lambda v}$. For the discrete summation use
$w_i^*=\min_{0\le j\le i}W_*(s_j,h)$ for $i<1050$, and
$w_{1050}^*=0$; this running minimum is valid because the **actual**
cumulative masses are decreasing. It is important at a table boundary:
raw upper constants from adjoining intervals need not be ordered.
Use $B_*,J_*$ defined as (B,J) with these substitutions, including
$W_*(s_0,L/3)$ in $J_*$. The original argument now gives, for all
(Lge b),
$$
 \frac{|psi(x)-x|}{x}\le B_*(L)+J_*(L)<.021 x^{-1/8}.          \tag{A1}
$$
Indeed each term of the scaled envelope decreases as before. In $W_*$
all $z$-powers times the exponential are decreasing for (zge h),
since $\lambda>q/h$. The value at $b$ is $<.021$ and its limiting
coefficient $w^*_{1049}<.01055$. The estimate (A1) starts 10.5
logarithmic units before the hypothetical input and is better on
its entire ray (compare the input at $L=200$ and use monotonicity).
Pointwise minima with other bounds remain valid.

There is a tighter prime-count transfer when switching bounds at $b$.
The proof of $D_c$ bounds the **signed residual after the theta boundary
term**, at $b$, by
$$
 \frac{A}{.9b}+\frac{117e^{-b/2}}{.4b}+\frac{40 b e^{10-b}}{8\pi}
 <7\cdot10^{-15}
$$
in normalized units, not by twice the total error. To see this,
subtract the exact signed theta boundary term at $b$ before applying
absolute values to the anchored formula from $a=20$. Applying the
same exact anchored formula from $b$ thereafter with (A1) yields
$$
 D_*(L)=.021e^{-L/8}!\le ft(1+\frac1{L(7/8-2/b)}\right)
    +3e^{-L/2}!\le ft(1+\frac1{L(1/2-2/b)}\right)
    +7\cdot10^{-15}\frac{L}{b}e^{b-L}, \qquad L\ge b.
$$
Add this to the minimum defining (D) in (R). In particular for
every $L\ge58$ we get the following **uniform strengthened margin**:
$$
 \boxed{ R(x)>\frac{x^2}{L^6}\le ft(1+\frac{14}{L}
                                       +\frac{4.25}{L^2}\right). }       \tag{A2}
$$
For optional simpler asymptotic polynomials, the parenthesis can be
replaced on the following nested domains:
$$
\begin{array}{c|l}
L\ge225&1+14/L+145/L^2\\
L\ge260&1+14/L+145/L^2+1412/L^3\\
L\ge330&1+14/L+145/L^2+1412/L^3+13985/L^4\\
L\ge400&1+14/L+145/L^2+1412/L^3+13985/L^4+145450/L^5 .
\end{array}
$$
These and the shaped (R) are correlated lower bounds and may be
maximized, not separate independent candidates.

For (A2), after subtracting $1+14/L$ in the $L^4$-scaled proof of
(R), multiply by $L^2$. The omitted-term bound $L^2\varepsilon(L)$
decreases and is $<.001$ on $L\ge58$. The factorial-polynomial
remainder after scaling consists of positive terms, starts at 145,
and decreases. For $58\le L\le180$ and $180\le L\le188$, use $D_c$
at both arguments and bound the scaled loss by 125 and 143, respectively.
For a block ([a,z]) with those endpoints the bound is
$$
 (2u(a)+D_c(a)+a/(a-1))
 [z^6 A(1+1/(.9(a-1)))+a^6{D_c(a-1)-A(1+1/(.9(a-1)))}].
$$
For the second block one can use this bound 143 **together with**
the remaining positive main $1412/188$, not merely 145. On
$[188,191.5]$ the checker covers 3500 **closed** cells of length .001:
use increasing $L^6$ at the right endpoint, all decreasing error
factors at the left endpoint, and the main polynomial at the right
endpoint. This verifies a normalized reserve $>4.251$ before the
omitted-term bound. For $L\ge191.5$ use $D_*$ also at $L-1$;
the $L^6$-scaled loss decreases and is $<141$ there. For such
monotonicity, expand the positive factors; shifted powers are
bounded by their logarithmic derivatives $j/(L-1)$, strictly
smaller than their exponential decay rates at the stated thresholds.
The same argument works for the four higher-polynomial corollaries,
scaling until the next positive coefficient is constant: the tested
total losses are below $1412,13985,145450,1610021$, respectively.
This quantitative result strictly strengthens (R2) on the common
whole ray, not just at the transition.

**Stability of the Ramanujan comparison to shrinking its argument.**
For $L\ge58$ put $z=x/e$ and $y=z(1-(1+12/L)/L^4)$. Then
$$
 \frac{ex}{L}\pi(y)-\pi(x)^2>\frac{.10 x^2}{L^7}.                  \tag{A3}
$$
In fact $\log y\ge L-1.001$ by the endpoint inequality in the checker.
The li difference is at most ((z-y)/log y). After scaling its cost
in the gap by $L^6/x^2$, this is at most
$(1+12/L)L/(L-1.001)<1+13.25/L$.
The sum of the two possible normalized prime-count errors costs
at most $2L^5D(L-1.001)/(L-1.001)$, since the minimum of the
admissible $D_c,D_*$ decreases and (y,zle x/e).
Bound this by $.65/L$: on $[58,191]$ bound the constant component
of $D_c$ after scaling at 191 and its scaled decreasing tails at
58, with $L/(L-1.001)\le58/(58-1.001)$. After 191 use $D_*$, with
all scaled terms decreasing from the checked value at 191.
Subtract from (A2). The unshifted baseline gives no such stability.

## B. Smoother Mertens errors and directional refinements

Improve $j$ in Section 3 to
$$
 j_*(L)=.04620e^{-L/2}+2e^{-L}
        +\min{7\cdot10^{-12}e^{-L/8},
                     7\cdot10^{-12}e^{-.23 L}+B_*(L)/H_0}.
$$
Here $B_*(L)$ is a bound for the full high-strip sum for $L\ge0$,
not just where $J_*$ is applicable. Indeed comparison of $B.9$ in CH2
at $s=0$ and $s\to1$, with the simple pole removed, gives the
identity
$$
 \sum_\rho\frac1{\rho(1-\rho)}=2+\gamma-\log(4\pi).
$$
Details: the constant of $\zeta(s)-1/(s-1)$ is $\gamma$, which
follows by uniform convergence near 1 of
$\sum_{n\ge1}[n^{-s}-\int_n^{n+1}t^{-s}dt]$. Thus the constant
of $\zeta'/\zeta(s)+1/(s-1)$ is $\gamma$. At zero
$\zeta'/\zeta(0)=\log(2\pi)$ is used explicitly in CH2 p. 35.
Subtracting $B.9$ at 0 from the regularized limit at 1 gives
$1+\gamma-\log(2\pi)+\frac12(\digamma(3/2)-\digamma(1))$.
The digamma difference is
$\sum_{n\ge0}(1/(n+1)-1/(n+3/2))=2-2\log2$, by grouping the even
and odd harmonic terms. For the series, the elementary beta-integral
identity obtained by integrations by parts gives
$\Gamma(z)=\lim_{m\toinfty} m^z m!/[z(z+1)\cdot s(z+m)]$
on $\Re z>0$ (substitute $t=u/m$ in the beta integral and
dominate by $u^{\Re z-1}e^{-u}$); local uniform convergence justifies
logarithmic differentiation at the required positive arguments.
The zero sum in the identity is absolutely convergent. Each term
has positive real part, since
$\Re(\rho(1-\rho))=\beta(1-\beta)+\gamma_\rho^2>0$.
For the critical-line zeros each term equals the absolute weight.
Their total is therefore $<.04620$ (harmonic certificate in
`refine.py`). For the off-line zeros $|\gamma_\rho|>H_0$ use the
old bound, or split .77: below .77 their contribution is at most
$7\cdot10^{-12}e^{-.23L}$; at or above .77 use the extra
$1/|\rho-1|\le1/H_0$ times $B_*(L)$. This proves the stated
$j_*$ in (J).

Use $E_*=\min(E,J_*+B_*)$ when (Lge b) and the old admissible
minimum otherwise; optionally add the CH2 weighted estimate
$$
 |U_1-L+\gamma|\le A+113.67e^{-L/2}
$$
for all $L\ge21$. Thus put
$$
  w_*=\min(E_*+j_*,A+113.67e^{-L/2}),\qquad
  v_*=\min\le ft{ E_*/L+2K_0j_*,
          \frac{w_*(L)}L+\int_L^\infty\frac{w_*(t)}{t^2},dt\right}.
$$
The second alternative follows by partial summation of $U_1$ against
$1/\log x$; one may use just the first alternative to avoid this integral. Any term (c e^{-
u L}) of $j_*$ can
replace its multiplier $2K_0$ by
(K_0+min(K_0,|K_0'|/
u)), by using the monotonicity of
$|K_0'|$ in the tail proof. These are explicit, pointwise
improvements over the original curves of candidate.md.

In fact use the following **asymmetric** power corrections. Put $u=e^{-L/2}$.
For $L\ge21$
$$
 \begin{split}
 .78u&\le D_1\le1.41u,\qquad
 (.78-1.98/L)u/L\le D_0\le1.41u/L,\\
 \max(0,(.78-1.98/L)u/L-1/(2\lfloor x
floor)) &\le
          \sum_{p\le x, p^k>x, k\ge2}\frac1{kp^k}\le1.41u/L.
 \end{split}
$$
These follow using $.99\sqrt t<psi(t)-\theta(t)<1.2\sqrt t$
as before, and
$\int_L^\infty e^{-t/2}K_0(t)dt=2u/L-\int_L^\infty e^{-t/2}dt/t^2$,
whose negative term is between $-2u/L^2$ and 0.
The omitted $p>x$ terms are at most (1/(2lfloor x
floor))
by the telescoping all-integer bound. For each of the three cases,
add the lower and upper corrections to the respective symmetric
errors $\pm w_*$ or $\pm v_*$. For (P) and (Q), exponentiate
the two ends (negate and reverse them for (P)); this retains the
different directional errors instead of forcing a common symmetric
envelope. These new inequalities imply (M) and improve it over the
same domain. For example at $L\ge26$ all three absolute scaled
errors have upper constant .044 until infinity, verified for the
finite-RH branch at 26 and by the original full-ray comparisons
past 58. On (Lge b), both absolute relative products and the
reciprocal-prime-sum error are $O(x^{-1/8}/L)$ with *log-error*
majorant $<.02101x^{-1/8}/L$ (for the reciprocal sum, this is
an ordinary additive error). The latter follows from (A1) and
termwise decreasing scaled bounds using (j_*le .04620e^{-L/2}
+2e^{-L}+7cdot10^{-12}e^{-L/8}); hence the two absolute relative
Euler-product errors are $<.0211x^{-1/8}/L$. The full finite
curves in finite.md can be minimized against these whenever applicable.

## C. Tertiary arithmetic consequences

**Primorial extrema.** For every real (N) with $\log\log N\ge190$,
$$
 \le ft|e^{-\gamma}\max_{substack{n\le N\ ninmathbb N}}
             \frac{n}{phi(n)}
          -\log\log N\right|<.0424(\log N)^{-1/8}.              \tag{A4}
$$
In particular every (sigma$n$/n) on this range is bounded above
by $e^\gamma{\log\log n+.0424(\log n)^{-1/8}}$, since
(sigma$n$/nle n/phi$n$) by the finite geometric series for
each prime power. No strict Robin or Nicolas comparison to the
zero-error main term is asserted.

Proof: put $Y=\log N$, $u=Y^{-1/8}$ and $t_\pm=Y(1\pm .0212u)$.
Then $\log t_\pm\ge b$, since $u<.001$ and
$|\log(1\pm .0212u)|<.02121u$. By (A1) and the prime-power bound,
$|\theta(t)-t|<.02101 t^{7/8}$ there. Consequently
$\theta(t_-)<Y<\theta(t_+)$; for the upper endpoint use
$(1+.0212u)^{7/8}\le1+.0212u$.
The primorial at $t_-$ is admissible. No (nle N) has as many
distinct primes as the primorial at $t_+$, because the smallest
product of that many distinct primes is the primorial.
The product $\prod_{\pmid n}(1-1/p)^{-1}=n/phi(n)$
(inclusion-exclusion) is greatest for a given cardinality when
using the smallest primes. Thus the maximum is between
$Q(t_-)$ and $Q(t_+)$. Apply the Euler-product error above and
$t_\pm^{-1/8}\le1.0001u$; the total error is
$(.0211\cdot1.0001+.02121)u<.0424u$.
For comparison the raw product-baseline error after the same
normalization is of order $ .2/(\log\log N)^2$; our additive
error is strictly less even than that term throughout the ray
(as checked at 190 and by monotonicity). The extremal statement
is new to this study, not a claimed globally best theorem.

**Primes in short intervals.** First, for $L\ge190$, if
$y=x+.0421x^{7/8}$ then
$\pi(y)-\pi(x)>.00007x^{7/8}/\log y$.
This follows by differencing the two theta majorants just used
and bounding $(y/x)^{7/8}\le y/x$. The interval is strictly
shorter than Dusart Prop. 5.4 and Cor. 5.5 on this entire ray:
$.0421L^2e^{-L/8}<1/5000$ and $.0421L^3e^{-L/8}<1$
by the endpoint and monotonicity tests.

There is a stronger exponent via cancellation of the **same zeros**
at the two endpoints. For every real $x\ge e^{100000}$, put
$$
 g=x^{5/8}(\log x)^{14},\quad y=x+g .
$$
Then
$$
 \boxed{ \pi(y)-\pi(x)>\frac{.6g}{\log y}. }                  \tag{A5}
$$
This interval is shorter on the whole stated ray than the preceding
power interval $(L^{14}e^{-L/4}<.0421)$. It is not obtained by
subtracting absolute theta bounds at (x,y).

Proof with explicit bounds. Set $\delta=g/x<1$, $U=3/\delta$,
$u=\log U=3L/8-14\log L+\log3$. Then $L/3<u<2L/5$
and $U>H_0$. Set $s_0=5/8+1/L$, divide $[s_0,7/8]$ into
at most $L/4$ bins with mesh $\le1/L$ (equal bins, ceiling of
$L(7/8-s_0)$), and write (s,t) for the left and right ends of
one bin. At shared endpoints assign the zero to either neighboring
bin. All high-strip estimates may use uniform $c\le12,d\le6$
from FKS Table 8 on $[5/8,7/8]$; write
$p=8(1-s)/3, \lambda=1-p, q=3+3p/4$.
For any $z\ge L/3$ the tail integral times two for this bin is
bounded by
$$
 V(s,z)=2c, e^{-\lambda z}z^q\lambda^{-1}
             \sum_{j=0}^4(4)_j/(\lambda z)^j
                 +2d e^{-z}(z^2+2z+2),
$$
with $(4)_j=4!/(4-j)!$, by the domination
$(1+v/z)^q\le(1+v/z)^4$. This is a bound for
$2\int_{e^z}^\infty N(s,v),dv/v^2$.
The bin's two-endpoint zero sum is bounded by $3x^t V(s,u)$.
Indeed each conjugate pair uses
$\le ft|(y^\rho-x^\rho)/\rho\right|\le x^t\min(\delta,3/|\gamma_\rho|)$
from the integral of the derivative or from the endpoint triangle
inequality. Summing the minimum gives exactly
(3int_U^infty N_{
m bin}$v$,dv/v^2) on the positive side.

To realize this full high-strip sum in the signed explicit formula,
use FKS Thm. 3.2 at $v=x,y$ with $T_v=v^{2/5}$. Since
$T_v\ge U$, the tails omitted at the two endpoints together
cost at most $3x^t V(s,u)$ per bin
$(x^t+y^t\le3x^t)$. Full high-strip sums are absolutely convergent
because $p<1$ for every bin, even the first one. Thus total
high-strip cost is at most (2sum_{
m bins}3x^tV(s,u)).

For clarity, divide this cost by $g$. Since $\lambda\ge8/(3L)$,
the polynomial sum in (V) is $<100$, and for $s\ge.75$
it is $<2$ $there (\lambda\ge1/3)$. Accordingly its first
term is bounded by $900 L u^q e^{-\lambda u}$ for $s<.75$
and $144 u^q e^{-\lambda u}$ for $s\ge.75$.
Use $u^q\le(2/5)^3L^q$ and
$$
 \frac{x^t e^{-\lambda u}}g
 \le e,L^{-14p}
$$
by cancellation of the (L) exponent and $t-s\le1/L$.
After the factor 3 and the number of bins, the first term
of $\sum 3x^t V/g$ is bounded by
$120 L^{-23/6}+20 L^{-5/12}<.166$; here use
$p\ge2/3$ below .75 and $p\ge1/3$ otherwise.
The second term is at most $3L(L^2+2L+2)e^{-L/8}<.001$
using $3e^{-u}=\delta$. Thus the whole high-strip cost is
$<.334g$.

Finally at each endpoint the explicit formula, with cutoff at most
$2.45T_v$, has low-strip costs bounded by
$((L+1)^2/6+3)\sqrt v + ((L+1)^2/12+1)v^{s_0}$ by the
FKS reciprocal-sum bounds used in Section 1 $\log cutoff (<\log v)$.
The truncation cost is $\le2.1(L+1)v^{.6}$.
Together those costs and $3\sqrt y$ to pass to theta are
$<.001g$: use $v^{s_0}\le2e,x^{5/8}$,
$\sqrt v\le2\sqrt x$, and $v^{.6}\le2x^{.6}$, then the
scaled expressions decrease from the tested onset.
Thus $\theta(y)-\theta(x)>.665g>.6g$ and each counted prime
weighs at most (log y). All thresholds and comparisons here
use piecewise monotonic analytic bounds, not an exhaustive
numerical range in $x$.
