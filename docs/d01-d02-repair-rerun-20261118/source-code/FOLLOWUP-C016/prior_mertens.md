# Mertens products and prime sums

All variables $x$ and $L=\log  x$ are real, and the sums include $p=x$ when $x$ is prime. Use the two nested premise sets B0 and B1 from spectral.md. Define
$$
\begin{aligned}
 P&=\prod_{p\le x}(1-1/p),\qquad Q=1/P,\\
 \mathcal R&=\sum_{p\le x}1/p-(\log L+M),\\
 \mathcal G&=\sum_{p\le x}(\log p)/p-(L-B_3),\\
 M&=\gamma+\sum_p(\log(1-1/p)+1/p),\qquad
 B_3=\gamma+\sum_p\frac{\log p}{p(p-1)}.
\end{aligned}
$$
These are the exact constants of Dusart2018 PDF pp.17–19 Thms.5.6 and 5.7. We bound $|e^\gamma  LP-1|, |e^{-\gamma }Q/L-1|, |\mathcal  R|, |\mathcal  G|$. The two reciprocal product errors are not independent.

## 1. Connected early rays on B0, retained on B1

The entries below are **inclusive real** $x$-cutoffs. Each error has the stated non-strict bound for every real $x$ on its ray. The product columns both use $c/L^3$, as does $\mathcal  R$; $\mathcal  G$ uses $c/L^2$. The authoritative list of cutoffs, including finer decimals, is also in sieve_receipt.txt (divide the last column by 1000). Retain the original Dusart bounds on their stated domains $0.2 starting at 2278382 for both \prod ucts, 0.2 at 2278383 for (\mathcal  R), and 0.3 at 912560 for (\mathcal  G)$.

| $c$ | Both products | Reciprocal sum error | Weighted sum error |
|---:|---:|---:|---:|
| 0.3 | — | — | 912559.998 |
| 0.2 | 2278381.712 | 2278382.186 | 3452145.120 |
| 0.15 | 5001781.288 | 5001781.860 | 7105254.412 |
| 0.12 | 8789120.250 | 8789120.961 | see receipt |
| 0.10 | 12911557.738 | see receipt | see receipt |
| 0.09 | 18337496.514 | see receipt | see receipt |
| 0.08 | 30971659.699 | see receipt | see receipt |
| 0.075 | 33930138.152 | see receipt | see receipt |
| 0.06 | 47002931.913 | see receipt | see receipt |
| 0.05 | 110218995.360 | see receipt | see receipt |
| 0.045, 0.043, 0.04 | see receipt | see receipt | see receipt |
| 0.034 | 195195676.271 | 195195711.565 | 263262632.451 |
| 0.03 | 266326905.243 | 266326946.083 | 311041303.943 |
| 0.025 | 498758570.918 | 498758746.837 | 604884240.642 |
| 0.023 | 604951339.455 | 604951501.515 | 615960608.991 |
| 0.0223 | 605428341.914 | 613281295.904 | 696295627.425 |

Use the pointwise minimum of applicable rows. These advances are input-independent: in particular the smaller fixed coefficients and gaps between cutoff integers come from arithmetic plus a B0 analytic join, not B1. A failed certificate endpoint in the receipt is not asserted to be an actual counterexample, nor the listed onset optimal.

## 2. Stronger power and logarithmic factors; matched B0/B1 comparison

For every (Lge62), there is an explicit polynomial-exponential envelope $\mathcal  B_b(x)$ below (equation M6) with $b=7/8$ on B0 and $b=27/32$ on B1. Both product errors and $|\mathcal  R|$ are bounded by its first component; $|\mathcal  G|$ by its second. This includes the following simpler rays: for $L\ge  L_0$,
$$
 \max (|e^\gamma  LP-1|,|e^{-\gamma }Q/L-1|,|\mathcal  R|)\le C\,x^{-a}/L,\qquad 
 |\mathcal  G|\le C\,x^{-a}.
 \tag {M0}
$$

| B0: $a=1/8$, $L_0$ | $C$ | B1: $a=5/32$, $L_0$ | $C$ |
|--:|--:|--:|--:|
| 155 | .224 | 155 | .517 |
| 180 | .026 | 169 | .327 |
| 190 | .02053 | 180 | .289 |
| 200 | .01880 | 200 | .260 |
| 240 | .01650 | 240 | .231 |
| 300 | .01491 | 300 | .209 |
| 500 | .01292 | 500 | .181 |
| 1000 | .01174 | 1000 | .165 |
| 5000 | .01097 | 5000 | .153 |

At fixed $L=200$, bounds from the nonuniform spectral curve, verified with outward rounding, are $1.305\cdot 10^{-15}$ on B0 versus $3.482\cdot 10^{-17}$ on B1 for each of the two relative errors and $|\mathcal  R|$, and $2.610\cdot 10^{-13}$ versus $6.964\cdot 10^{-15}$ for $|\mathcal  G|$. At fixed bound $10^{-14}$ for the first group, sufficient $L_0$'s are 186 and 167 respectively. At fixed bound $10^{-12}$ for $|\mathcal  G|$ they are 190 and 170. These absolute thresholds are whole rays, not grid extrapolations. For the clean $L_0=200$ rows the ratio of the B1 and B0 error envelopes is $(.260/.01880)x^{-1/32}$, strictly less than 1 throughout the common domain. In general the crossover for two constants is $L=32\log (C_1/C_0)$, with the B1 branch better to its right on the overlap. At (Lge200), the B0 and B1 power bounds also improve all fixed inverse-log rows above, by monotonicity of $L^2e^{-aL}$ there and its checked value at 200. The exact curve (M6) is tighter than the constant-on-ray substitutions (M0).

## 3. Transfer formulae and signs

Define
$$
 U(L)=\sum _{n\le  e^L}\frac {\Lambda (n)}n-(L-\gamma ),\qquad 
 W(L)=\sum _{n\le  e^L}\frac {\Lambda (n)}{n\log  n}-\log  L-\gamma 
$$
$the (n=1) term in the \log -weighted \sum  is omitted$. Integration by parts gives
$$
 U(L)=E(L)-\int _L^\infty  E(v)\,dv,\qquad 
 W(L)=\frac {E(L)}L-\int _L^\infty  E(v)(1/v+1/v^2)\,dv
       =\frac {U(L)}L-\int _L^\infty  U(v)/v^2\,dv. \tag {M1}
$$
To see the constants if deriving these identities from scratch: the spectral bounds ensure the integrable error and hence the existence of $lim (\sum \Lambda (n)/n-L)$. Its value is the constant Laurent term $-\gamma $ of $-\zeta '/\zeta (1+h)$ by the Abelian integral with kernel $h e^{-hv}$. The Laurent term follows from $\zeta (1+h)-1/h\to\gamma $, obtained by subtracting $\int _n^{n+1}t^{-1-h}dt$ termwise from $n^{-1-h}$; the remainder is holomorphic near $h=0$. For $W$, the limit of the error is 0 by Dusart Thm.5.6 and the convergent prime-power series $\gamma -M$. Thus integration on a finite interval followed by a limit proves (M1), with correct signs.

Use positive tails
$$
 T_w=\sum _{m\ge 2,p^m>x}\frac {\log  p}{p^m},\quad 
 T_l=\sum _{m\ge 2,p^m>x}\frac {1}{mp^m},\quad 
 T_p=\sum _{p>x,m\ge 2}\frac {1}{mp^m}.
$$
Exactly
$$
 \mathcal  G=U+T_w,\quad  \mathcal  R=W+T_l,\quad 
 Y:=\log (e^{-\gamma }Q/L)=W+T_l-T_p=\mathcal  R-T_p.
 \tag {M2}
$$
In particular $0\le  T_l-T_p\le  T_l$. Also $0\le  T_p\le 1/(2\lfloor  x\rfloor )$, by $1/m\le 1/2$ and summing $1/(n(n-1))$ over integers $n>x$. Let $c_*=1.000000147, d(L)=166.64/L^3$. For (Lgelog 4), with $D(x)=\psi (x)-\theta (x)$, Dusart Cor.4.5 and Thm.4.2 $global (k=3,eta_3=20.83)$ give
$$
 (1-d(L))\sqrt {x}\le \theta (\sqrt {x})\le  D(x)\le  c_*\sqrt {x}+1.78x^{1/3}.
$$
The lower bound may be intersected with 0. Apply the elementary Stieltjes formula
$\int _{(x,\infty )}f,dD=-f(x)D(x)-\int _x^\infty  D(t)f'(t)dt$
with $f=1/x,1/(x\log  x)$ to bound $T_w,T_l$. In particular for (Lge18),
$$
 \begin {split}
 t_w(L)&=(2c_*-1+d(L))e^{-L/2}+2.67e^{-2L/3},\\
 t_l(L)&={[2c_*(1+1/L)-1+d(L)]e^{-L/2}
                +2.67(1+1/L)e^{-2L/3}}/L
 \end{split}\tag {M3}
$$
are upper bounds. Lower tail bounds can be kept by using the upper bound for (D$x$) at the boundary, lower $\max (0,1-d(v))e^{v/2}$ in the integrals, and intersecting with 0. For an even tighter pointwise upper bound keep the exact positive integrals in place of the factor $1/L+1/L^2$ used to simplify $t_l$.

For any positive absolute $\psi $ envelope $E_b^*$, (M1) gives a (|U|) bound $E_b^*(L)+\int _L^\infty  E_b^*$ and a (|W|) bound $E_b^*(L)/L+\int _L^\infty  E_b^*(v)(1/v+1/v^2)dv$. CH2 Cor.1.2 and 1.3 additionally give direct (|U|) bounds, so also propagate their minimum with the former bound through the last identity of (M1). These integrals can be taken over **pointwise** minima; this includes improvements to earlier $L$ from the far tail when a tail route governs. Alternatively use Dusart's exact $\theta $-identities (PDF pp.17–19): $\mathcal  G$ and $\mathcal  R$ have the first and second formula in (M1) with (E) replaced by $E_\theta =e^{-v}\theta (e^v)-1$. These offer independent tighter choices on some domains. Larger-tail nonintegrable floors (e.g. CH2 alone for the first identity) are not integrated to infinity for that purpose: switch to an integrable branch.

## 4. Unweight the high-zero contribution *before* taking absolute values

Inserting the absolutely convergent decomposition $A$ of spectral.md into (M1), a high zero contributes $-e^{(\rho -1)L}/(\rho -1)$ to $U$. Thus
$$
 |U(L)|\le  Z_b(L)+D_b(L)+\int _L^\infty  D_b(v)dv. \tag {M4}
$$
For $W$ use the same spectral term of $U$ in the last identity of (M1), and the remainder $\mathcal  E_b$ in the direct formula of (M1). For $\lambda =\rho -1$, integration by parts gives
$$
 \left |\int _L^\infty  e^{\lambda  v}/v^2\,dv\right |
 \le  \frac {2e^{\Re \lambda  L}}{|\lambda | L^2}.
$$
In fact the boundary contributes $e^{\Re \lambda  L}/(|\lambda |L^2)$ and the derivative integral is bounded by the same quantity. Since $|\lambda |\ge |\Im \rho |>H$, we obtain
$$
 |W(L)|\le  \frac {Z_b(L)}L\left (1+\frac {2}{HL}\right )
           +\frac {D_b(L)}L+\int _L^\infty  D_b(v)(1/v+1/v^2)dv. \tag {M5}
$$
The leading zero contribution does *not* pay $1+1/(1-b)$, as it would in a direct positive-kernel transfer of (|E|). This removes both the logarithms of D02's direct majorant and the main integral multiplier. With $J_D=\int _L^\infty  D_b$, define
$$
 B_w=Z_b+D_b+J_D+t_w,\qquad 
 B_l={(1+2/(HL))Z_b+D_b+(1+1/L)J_D}/L+t_l,\qquad 
 \mathcal  B_b=(e^{B_l}-1, B_w). \tag {M6}
$$
These are positive explicit functions on (Lge62). The envelope in the code safely replaces $e^{B_l}-1$ by $B_l/(1-B_l)$ where $B_l<1$; (M6) itself can always be used. Every integral of $v^k e^{-av}$ here has the exact value $e^{-aL}\sum _{j=0}^k (k!/(k-j)!) L^{k-j}/a^{j+1}$. At all onsets in the table $e^{aL}B_w, e^{aL} L B_l$ are nonincreasing because each term is a positive exponential polynomial times decreasing inverse powers, and any excess polynomial degrees are outweighed by their strictly larger exponential rates. More explicitly: the $Z_b$ rates are (ge a) and its degree is 0; $V$'s slow rate is $1/4$, giving $L^2e^{-(1/4-a)L}$ decreasing for (Lge62); the $D_b$ tail degrees at most 4 and 2 are paired with rate excess $1/6,1/2$; all prime-power rate excesses exceed $1/3$. $B_l$ is decreasing and $1/(1-B_l)$ is decreasing where used. The absolute-error cutoffs use the same monotonicity verified at the cutoffs. This proves the full analytic rays from point endpoint checks with rigorous monotonic bounds.

Both $Z_b,D_b$ are pointwise smaller with $b=27/32$ than at $7/8$, with strict $Z_b$ gain. Consequently (M4)–(M6) give strictly smaller bounds everywhere on their common branch, *before* intersecting with other locally better bounds. Coincident finite-sieve and CH2 bounds are not given new premise credit. Compared with the original-input spectral approach using (M1) alone, (M5) materially improves even on B0. The simpler raw B1 majorant is dominated by $S_{27/32}$ for all (Lge200): $S_{27/32}\le 0.3 e^{-5L/32}$ by the monotonic rescaling check, whereas $L^2/64\ge 625$. It remains valid and is included as an allowed seed. For example its direct transfer to $U$ gives
$$
 e^{-aL}\{(1+1/a)L^2+2L/a^2+2/a^3\}/64
$$
before the prime-power correction, and to $W$ gives
$$
 e^{-aL}\{(1+1/a)L+1/a+1/a^2\}/64
$$
with $a=5/32$. This is substantially worse than the oscillation-preserving spectral branch on the whole legal overlap, not just at sampled abscissae.

There is also a comparison against the exact B0 spectral curve, not just its rounded table: the last coefficient of $Z_{7/8}$ exceeds .01 (checked in mertens.py), so its contributions alone in (M4) and (M5) exceed $.01 x^{-1/8}$ and $.01x^{-1/8}/L$. These are lower floors on the **budgets**, not on the true error. The corresponding clean B1 bounds are already strictly below those floors on $L\ge200$ since $.260e^{-200/32}<.01$. Every same-operator B0 transport using the minimum of $S_{7/8}$ and CH2 likewise retains these endpoint floors there; the original inverse-log estimates also exceed them. The combined prescription remains non-worse even when a different source estimate is locally best.

## 5. Pointwise combination of old and new bounds

For each of (U,W), keep the minimum of all applicable non-spectral transfers of the pointwise original-plus-new seeds, direct CH2 weighted bounds for $U$, and (M4) and (M5). These give absolute bounds $K_U,K_W$. A representative full pointwise prescription is:
* For $\mathcal  R$ and $\mathcal  G$, take the intersections of $[-K_W,K_W]+[T_l^-,T_l^+]$ and $[-K_U,K_U]+[T_w^-,T_w^+]$, respectively, with the direct $\theta $ intervals, all valid direct original estimates, and the finite intervals/rows below. Here $T^pm$ are the lower and upper tail bounds from Section 3; one can always use (0,t). This is shorthand for a separate intersection per observable, not for intersecting the two different observables with each other.
* For $Y$, intersect $[-K_W,K_W]+[T_l^-,T_l^+]-[0,T_p^+]$, $[-K_W,K_W]+[0,T_l^+]$, and the resulting $\mathcal  R$ interval minus $[0,T_p^+]$. One can propagate the $Y$-interval back to the $\mathcal  R$-interval using (M2). This preserves sign information.
* If the resulting $Y$-interval is $[y_-,y_+]$, the two relative errors are bounded respectively by $\max (e^{-y_-}-1,1-e^{-y_+})$, $\max (e^{y_+}-1,1-e^{y_-})$. Take minima separately with Dusart Thm.5.9, the finite certificates and simple whole-ray rows. A direct bound $\delta<1$ on a relative error can also be propagated to the $Y$-interval by taking $[\log(1-\delta),\log(1+\delta)]$ for $Q$ or its negative for $P$, and crossed back to $\mathcal R$ via (M2). Do not use the inverse branch with the same two signed errors without this conversion.

All ingredients and domains are specified; the integrations are of explicit real functions (with the analytic tails above). This describes an envelope also in ranges where the simple power menu is not active and allows smaller pointwise bounds than any one row. Its B0 version is obtained by removing the $27/32$ consequences, not by reverting to just $0.2/L^3$. A comparison to an unknown optimum among deductions from B0 is not claimed.

## 6. Certified finite and intermediate joins for the early rows

For the analytic continuation of the finite sieve, use a simple switched $\psi $ seed (phi): for (21.41le vle29.9) use $0.791e^{-v/2}$ (CH2 Lemma 9.2); from 29.9 to 58 use $v^2e^{-v/2}/25$ (finite RH); from 58 to 190 use (J_{
m CH}); then $S_{7/8}$. Either neighboring estimate is valid at the switch if needed. In mertens.py, for the finite region (21.41le Lle200), integrate these piecewise positive majorants exactly for $U$. In the $W$ tail use $1/L+1/L^2$ to weight the part up to 29.9 and $1/29.9+1/29.9^2$ on the rest whenever (Lle29.9); for (Lge29.9) use $1/L+1/L^2$ on its whole tail. On each block with endpoints (l,u) within a piece the unscaled positive budgets decrease, so use $l$ for the unscaled error and $u$ for the $L^2$ or $L^3$ multiplier. This gives a certified envelope with constant .05 for all three types; the power tail dominates this on (Lge200). The fact $e^{21.41}<2\cdot 10^9$ supplies an overlap.

A stronger anchored bridge and smaller RH height for the weighted route give **.0223**, and hence all of the larger table coefficients. Let $N=2\cdot 10^9, L_N=\log  N, T=E_\theta (L_N)$. The sieve gives enclosures of $\theta (N),\mathcal  R(L_N),\mathcal  G(L_N)$. Use the exact anchored formulae
$$
 \begin {split}
 \mathcal  G(L)&=\mathcal  G(L_N)-T+ E_\theta (L)+\int _{L_N}^L E_\theta (v)\,dv,\\
 \mathcal  R(L)&=\mathcal  R(L_N)-T/L_N+E_\theta (L)/L+
                    \int _{L_N}^L E_\theta (v)(1/v+1/v^2)\,dv.
 \end{split}
$$
For $L_N\le  v\le 23.3$, CH2 Lemma 9.2 and the prime-power estimates above imply
$$
 -(1.791001 e^{-v/2}+1.78e^{-2v/3})\le  E_\theta (v)\le -0.19e^{-v/2}.
$$
In anchor.py, for a block ([l,u]) bound the negative endpoint error by the upper negative envelope at $u$ and by the lower negative envelope at $l$, using $1/u,1/l$ in the $\mathcal  R$ bound. For the integral use the interval to $u$ with weight $1/L_N+1/L_N^2$ for the lower side and the interval to $l$ (or zero on the first block) with weight $1/u+1/u^2$ for the upper side. The integrals of the two exponentials are exact. For $Y$ subtract $T_pin[0,1/(2N)]$. At the far join $K=29.9$, and for every $L\ge K$, CH2 p.3 Cor.1.2 at the **smaller** admissible height $10^7$ gives
$$
 |U(L)|\le J_s(L):=3.15\cdot10^{-7}+33e^{-L/2},
 \qquad |W(L)|\le W_s(L):=\frac{2(3.15\cdot10^{-7})+33(1+2/L)e^{-L/2}}{L}.
$$
The second inequality is (M1) applied to $J_s$; here the floor is integrable against $1/v^2$. The coefficient $33$ pads the explicit CH2 ordinate factor. At $23.3\le L<K$, instead of integrating the looser $\psi$ envelope past $K$, anchor the identities (M1) at $K$. Thus
$$
\begin{aligned}
 |U(L)|&\le J_s(K)+\phi(L)+\phi(K)+\int_L^K\phi,\\
 |W(L)|&\le W_s(K)+\phi(L)/L+\phi(K)/K
                     +(1/L+1/L^2)\int_L^K\phi ,
\end{aligned}
$$
where $\phi=0.791e^{-v/2}$ on this interval including both endpoints. Add the same power tails. Each unscaled bound is nonincreasing on that interval. Use the minimum with the switched $\phi$ check, continue with the minimum of $J_s,W_s$ and the $\phi$ check through 58, and then use the switched pointwise checks from 58 to 200 and (M6) afterward. The interval multipliers are again bounded at the right endpoints. The final checked maximum normalized constants are below 0.0223 in each of these intervals and in the preceding anchor. This supplies all joins, with no extension of the finite computation beyond its terminal $N$.

### Fixed-point certificate up to $N$

mertens.cpp uses the ordinary Eratosthenes sieve, marking all $p^2,p^2+p,\ldots $ for each unmarked $p\le \sqrt  N$. Every composite has a least prime factor $\le \sqrt  N$, so the unmarked integers (ge2) are exactly primes. All arithmetic for the tests is integer, with scale $F=2^{62}$, unsigned input sizes and signed 128-bit fixed-point intermediates. In the reduced logarithm calculation $1\le  n/d\le 2$, set $z=(n-d)/(n+d)\le 1/3$. Use the lower rounded powers and sum for $2\sum _{j=1,3,dots,41} z^j/j$. The discarded analytic tail is $<1/F$; the rounded $z^2$ has fixed-point error $<5/3$ units, and each rounded odd power error is $<3$ units $one multiplication uses a fac\to r at most (1/9) and the rounding of the fac\to r and \prod uct adds \le ss than (5/3+1)$. Dividing by an odd integer adds at most another unit to the error. Hence the overall lower estimate is within 210 units. Undo powers of two using the same lower bound for $\log  2$; all high logs here use at most 30 shifts, giving total error $\le 6510$ units. For (loglog x) on tested endpoints (xge11), the input error divided by the lower $\log  x>2$, plus the log error with at most four shifts, is below 6511 units. All products fit, including the reduction for (loglog x): when $d=16F$, $n-d<6F$ since $\log  N<22$, and otherwise (dle8F) and $n-d<8F$. Thus $F(n-d)<2^{127}$. Other products (powers, fixed bounds (le F), summands and rational argument numerator at most $1000N$) have smaller widths.

For $\gamma $, use $H_m-\log  m-1/(2m)$ at $m=10^6$ with error $<1/(m-1)^2$ by comparing the integral of $1/t$ to its trapezoidal sums $per unit \int erval error at most (1/(6j^3))$. Fixed-point divisions, summations and rounding pads are explicit in the code. For $M$, add the tail in $[0,1/(2N)]$ of the positive logarithmic prime powers. For $B_3$, the tail of $\sum  \log  p/(p(p-1))$ is in $[.997/N,1.004/N]$: integrate $w(t)=1/(t(t-1))$ against $\theta $, using $|\theta (t)-t|\le 0.0002t$ for $t\ge  N$ from Dusart Thm.4.2 with $k=3,eta_3=.78$. The integral of the main term is $\log (N/(N-1))$ and the error is at most $0.0002(2/(N-1)+\log (N/(N-1)))$. The stated rational bounds hold also at the earlier trial $N=4\cdot 10^8$.

The sieve tests both sides of every relevant prime jump and the terminal endpoint $N$. For product error $\le  q=c/L^3$ it suffices to certify $|Y|\le  q-q^2/2\le \log (1+q)$, since (P,Q) are mutual reciprocals after normalization. All tested bounds are rounded in the adverse direction. Between prime jumps the residual is a constant minus $\log  L$ $\prod ucts and (\mathcal  R)$ or $L$ $(\mathcal  G)$; the absolute value of the slope of its pertinent error budget is smaller than $1/L$ or 1 respectively for (xge11) and these coefficients. Thus the difference from either moving boundary is decreasing, proving the signed bounds from the two endpoints of each interval. To repair the last failed prime interval, the code stores its post-prime sums and tests a subinterval start with denominator 1000; the next prime's left limit is known good. Bisection is only a search for a successful tested point, not a proof of optimality. This verifies every real argument after the recorded start and up to $N$. The same finite data give the enclosures at $N$ used in the anchored analytic proof.

## 7. Attribution and remaining comparison limits

D02 introduces the stricter cap in the absolutely convergent high-zero sum, even before direct onset; (M4) and (M5) preserve that gain in the final weights. All improvements on the early inverse-log table and the anchor are B0 work; here the bottleneck is finite-prime fluctuation and a moderate-$x$ analytic/finite join, not the large-$x$ hypothetical Chebyshev power. The $\theta $- and $\psi $-transfers alone would retain large nonoscillatory tail losses. The stronger spectral branches and the finite arithmetic should both be retained rather than ranking products from the coefficient at one $x$. See notes.md for other attempted improvements.
