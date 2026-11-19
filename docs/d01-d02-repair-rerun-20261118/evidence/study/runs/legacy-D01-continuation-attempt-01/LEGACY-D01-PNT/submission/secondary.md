# Secondary original-input consequences

These results are not attributed to the added $\psi$ assumption.
Their prerequisites are the same original QRH and magnitude
estimates used in the primary portfolio. They are not extra trials.

For every $L\ge180$, $|\theta(e^L)e^{-L}-1|<.01317 e^{-L/8}$.
Indeed on $[180,186.03]$ scale CH2 plus Dusart by $e^{L/8}$
and bound $A_0e^{L/8}$ at 186.03 and $117e^{-3L/8}$ at 180.
After 186.03 use the spectral ceiling .0131624 and
$3e^{-3L/8}$. Even .0131652 for Dusart-only gives .01317.
These comparisons are checked below. It follows for every
$x\ge e^{180}$ that $(x,x+.02635 x^{7/8}]$ contains primes,
with count $>.0000099 x^{7/8}/\log(x+.02635x^{7/8})$.
Subtract the bounds for theta at both endpoints, and upper-bound
the $(7/8)$th power at the right by its concave tangent.
The right-hand error plus the left-hand error has combined
coefficient at most $.01317(2+(7/8).02635x^{-1/8})$.
This improves the original own D01 simpler power-length
.0421 coefficient and moves the onset from $e^{190}$ to $e^{180}$.
The more intricate interval with exponent $5/8$, log power 14,
and onset $e^{100000}$ is retained in historical_d01_refined.md
§C with its analytic and arithmetic proof (use the QRH strip
in place of the historical deduction of that strip from the
contract). It is not inferred by subtracting the unsigned
endpoint errors, and the two interval results are different
onset/length tradeoffs.

For real $N$ with $\log\log N\ge181$ put $Y=\log N$, $u=Y^{-1/8}$,
$t_\pm=Y(1\pm .01318 u)$. Then $\log t_\pm\ge180$ and
$\theta(t_-)<Y<\theta(t_+)$. Use the theta bound just proved
and the concavity/tangent estimate at the upper endpoint
(or $(1+.01318u)^{7/8}\le1+.01318u$).
The primorial up to $t_-$ is admissible; no integer up to $N$
can have as many distinct prime factors as the primorial up
to $t_+$, since the smallest product of that many distinct
primes is the primorial. For a given cardinality using the
smallest primes maximizes the totient ratio
$n/\varphi(n)=\prod_{p\mid n}(1-1/p)^{-1}$ by inclusion–exclusion.
Thus the maximum normalized by $e^{-\gamma}$ is between
$e^{-\gamma}Q(t_-)$ and $e^{-\gamma}Q(t_+)$.
The strong product power envelope gives
\[
 \left|e^{-\gamma}\max_{1\le n\le N,\ n\in\mathbb N}
           n/\varphi(n)-\log\log N\right|<.02635(\log N)^{-1/8}.
\]
For the numeric constants use $u<10^{-9}$ and
$|\log(1\pm .01318u)|\le .013180001u$,
$t_\pm^{-1/8}\le1.00000001u$. The sum of the shift and
product error, even with .013166 for the latter, is
strictly less than .02635 in these units.
This improves the original own D01 A4 (.0424 from 190).
It also bounds $\sigma(n)/n$ from above since
$\sigma(n)/n\le n/\varphi(n)$ by the finite geometric sums.

There is a sharper comparison for a **specified primorial**
$n_x=\prod_{p\le x}p$, $L\ge180$. With the notation of
mertens_current.md, and $w=\theta(x)/x-1$,
\[
 \left|\log\frac{n_x/\varphi(n_x)}{e^\gamma\log\log n_x}\right|
 \le J_K(L) +\frac{2a e^{-L/2}+1.5b e^{-2L/3}}{L}
        +\tau+\frac{2w^2}{L}.
\]
In the exact theta transfer for $\delta_Q$ the boundary term
$w/L$ cancels to first order against
$\log(\log\theta(x)/L)=\log(1+\log(1+w)/L)$.
The logarithm series for $|w|\le1/2$ and $L\ge180$ bounds
the difference by $2w^2/L$. The remaining theta tail is
the smoothed $\psi$ tail plus the power difference bounded
by the elementary upper integrals already proved.
For an explicit unsigned curve one may replace $w^2$ by
$\min(d_U^2,\ldots)$ or simply by $.01317^2 e^{-L/4}$ and
$\tau$ by $1/(2\lfloor x\rfloor)$, then apply $e^z-1$
to the displayed bound. By the refined $k(L)$ in §2 of
mertens_current.md, the limsup of $L x^{1/8}$ times
the absolute relative error here is at most
$.00673/(3\cdot10^{12})<2.25\cdot10^{-15}$.
None of these magnitude conclusions asserts a Robin or
Nicolas zero-error sign.
