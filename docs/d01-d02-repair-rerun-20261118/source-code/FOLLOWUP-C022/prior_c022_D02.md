# D02 continuation: quantitative arithmetic portfolio

**Premises and main results.** Write $L=\log x$. B0 consists of the seven
bound originals, including OpenAI QRH Theorem 1.1 and the literature's
finite computation at its stated trust tier; no full RH is assumed.
The added hypothesis A is **exactly**
$$
|\psi(x)-x|\le x^{27/32}(\log x)^2/64\qquad(\text{every real }x\ge e^{200}).
$$
It implies D01, but the inherited D01 proof that B0 implies the **$7/8$**
hypothesis does not prove A. Denote $b=27/32, a=5/32$.

* **Ramanujan:** $R(x)>0$ on the sharp open ray inherited from D01
  (the noninteger endpoint is unchanged). A new independent-of-A
  argument advances the .01 normalized margin from $L=28.15$ to 27.8,
  and the margin 1 from 30.8 to 30.45. **With A**, from $L=49.5$ the
  strict margin is $1+14/L+83/L^2$, in units $x^2/L^6$; the full
  $1+14/L+145/L^2$ holds from 185.5. Higher polynomial onsets,
  the arbitrary-order theorem, exact shaped bounds and strengthened
  shifted-argument estimates are in `D02_R.md`.
* **Mertens:** **With A**, the original $1/8$ power shape now has a
  coefficient .001324 (with separately certified finite real joins
  below (1.81cdot 10^8)), and stronger power shapes $x^{-9/64}$
  and $x^{-5/32}$ start at 300000. The latter has coefficient
  .212654 at $L=200$ and limiting upper coefficient .116297.
  At $L=60.98$ the coefficient in log powers 3, 3, 2 (products,
  reciprocal sum, weighted sum) is $2.944\cdot10^{-8}$, versus
  $2\cdot10^{-7}$ in the inherited simple B0 row from $L=59.5$.
  See `D02_M.md` for the full signed and power/log frontiers, finite
  tapes, and the matched-domain comparison.

**How to take the envelope.** Keep every supported inherited
entry on its stated domain and premise set (the registry is
`OWN_D01_VALIDATED_FLOOR.json`; main proofs `ramanujan.md`,
`mertens_current.md`, `candidate.md`, `finite.md`, `secondary.md`).
The exact old mathematical distinctions/withdrawals in the review
are preserved. The name `candidate.md` is the byte-preserved D01
paper, not this stage's contract. `D01_STAGE_STATUS.json` is historical.
Take the **maximum** of valid lower bounds, **minimum** of valid
upper bounds or intersections of signed intervals. All newly certified
branches below are additions, not replacements of better inherited
pieces. In particular, an older onset at a weaker coefficient is not
deleted by a later, stronger coefficient. Inherited QRH-free
alternatives are retained. No other run or arm is used; the B0
comparison is a within-method comparator, not a blind baseline.
No claim is made of global best-known status or of the optimality of
our sufficient thresholds (except the named, proved sharp benchmarks).

## 1. The actual use of A: a smaller strip

For $\Re s>1$, absolute convergence and unique factorization give
$$
-\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(t)-t)t^{-s-1}\,dt.
$$
The compact part before $e^{200}$ is harmless; the rest is normally
convergent on every compact subset of $\Re s>b$ by A. Thus the
right side continues holomorphically there except at 1. The identity
theorem and the nonzero residue of the logarithmic derivative at a zero
give $\beta \le b$ for each nontrivial zero. This is a **closed upper
cap**, not a proof of exclusion at $b$. The zeta continuation and
symmetries are the standard ones used in the allowed FKS §2 and CH2
Appendices A/B. No real zero in $0<s<1$ occurs: the alternating
Dirichlet series for $(1-2^{1-s})\zeta(s)$ is positive by pairing.
Count multiplicities throughout. This is why several improvements
start before $e^{200}$: the hypothesis controls an analytic
continuation globally; it is not directly evaluated below its threshold.
B0 QRH by itself supplies only the cap $7/8$ in these steps.

## 2. Two reciprocal-moment density screens

Let $H=3000175332800, h=\log H$. By Platt–Trudgian FiniteRH
Theorem 1 (original PDF p.2; announcement p.1), off-line zeros
of positive ordinate have ordinate at least $H$. Below we use
$H$ as a lower integration limit, so also allowing equality causes
no issue. Put $s_* =.72$. For $s\ge s_*$ in our screens let
$p=8(1-s)/3, q=5-2s$. Use either of the two FKS Table 8 panels
(PDF p.26, Cor. 2.9 and (2.17), pp.7–8) on its own interval, or
Dusart Theorem 2.3 (PDF p.5), to write a density bound
$$
N(s,t)\le c t^p(\log t)^q+d(\log t)^2\quad(t\ge H).
$$
For Dusart use $c=4.9,3^p,d=51.5$ by $\log(1+v)\le v$.
Table constants are rounded **up** in `d02screen.py`; bounds are
minimized as whole bounds, not mixing coefficients. Changing the
integration limit does not change the $H_0=3\cdot10^{12}$ of the
FKS Table 8 parameters. The density results need not be reoptimized
at unmatched parameters. Whether an original includes $\beta=s$
does not matter; the cumulative mass below uses $\beta>s$.

For $m=1,2$ bound the two-sided mass
$2\sum_{\gamma>0, \beta>s}\gamma^{-m}$ by
$2\min t_H^\infty N(s,t)t^{-m-1}dt$. Put $\lambda=m-p>0,z=\lambda h$,
$$
A_z=\sum_{j=0}^3{3\choose j}j!/z^j,\qquad
B_z=\sum_{j=0}^3{3\choose j}(j+1)!/z^{j+1}.
$$
The bound per source is
$$
W_m(s;c,d)=
\frac{2mc e^{-z}h^q}{\lambda} A_z(1+B_z/A_z)^{q-3}
+2d e^{-mh}(h^2+2h/m+2/m^2).
$$
Indeed $t=H e^v$; with weight $e^{-\lambda v}(1+v/h)^3\,dv$,
the mean of $v/h$ is $B_z/A_z$. Concavity of
$(1+v/h)^{q-3}$ (here (3<q<4)) gives the displayed Jensen
upper bound. This also applies to the $m=2$ integral, instead of
merely dividing the $m=1$ bound by $H$.

Take nodes from $s_*$ to $b$ of step .00025. At each node below the
last one take the upward rounding of the min of the source values,
then the running minimum $w_j$ to preserve monotonicity. A preceding
upper bound for the tail is still valid later. For all but the last bin
use the left cumulative bound $w_j$; equivalently assign mass
$w_j-w_{j+1}$ at the right endpoint for estimating increasing
weights. For the last bin, from $s_{J-1}$ to $b$, use the
**linear chord** of the Dusart integral between its two upper endpoint
values $w_{J-1}$ and $w_b$. The checker verifies that at the left
it is indeed the selected upper value, and that it decreases. This
chord bounds the true Dusart majorant: each integrand in its first
term is a positive constant times an exponential of an affine
function of $s$ $because (p,q) are affine$; the second term is
constant. Hence the actual integrated majorant is convex. Avoid
an artificial atom of size $w_{J-1}-w_b$ at $b$: spread it
uniformly over this last bin, retaining $w_b$ at $b$.
Define $B_m(L)$ as the sum of the masses just specified times
$e^{-(b-s)L}$, with the uniform mass term integrated:
$$
 B_m(L)=\sum_{j<J-1}(w_j-w_{j+1})e^{-(b-s_{j+1})L}
 +w_b+(w_{J-1}-w_b)\frac{1-e^{-(b-s_{J-1})L}}{(b-s_{J-1})L}.
$$
This dominates the exponentially weighted actual mass by layer-cake
integration in $s$. At nodes any jump conventions in the auxiliary
majorant can be taken right-continuous; the true **strict** tail and
the value at $s_*$ are bounded. The $w_b$ term is an upper
allowance for a possible boundary atom, not an assertion it exists.
All terms are nonnegative and nonincreasing in $L$.
The chord is materially relevant to the limiting coefficient.
The limiting allowances satisfy $w_b<.116297$ for $m=1$ and
$w_b<2.506\cdot10^{-14}$ for $m=2$ (both strict). The same
routine with cap $7/8$ is an optional within-method B0 comparison,
not a replacement of any stronger inherited B0 branch.

## 3. Unsmoothed and smoothed input curves

Let $T=e^{c_*L}$ with $c_*=7/20$, $y=c_*L+1$. From $L=155$
use FKS Thm. 3.2 (PDF p.8) with the row
$(\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)$.
The two admissibility inequalities $T>\max(51,L)$ and
$5T+2<e^{L/2}$ hold at 155 and persist (the ratios of
the exponential to each competing term increase).
The formula gives a possibly different $T^*$ at every
argument; $T\le T^*\le2.45T<e^y$. No prime-power midpoint
convention is substituted for this original signed formula
on its real domain. See FKS Remark 3.3 for the stated provenance;
we do not invoke the version with known errors in earlier papers.
From FKS Lemma 2.1, Remark 2.2, Cor. 2.3 and Table 1
(PDF pp.4–5), two elementary bounds are
$$
2\sum_{0<\gamma \le T^*}1/\gamma \le y^2/6+3,\qquad
2\sum_{\beta>1/2,\,0<\gamma \le T^*}1/\gamma
\le (y^2-h^2)/12+.1.
$$
For the first use $U=100$, $S_0<.593$; for the second
use reflection at each positive ordinate, exclude ordinates
below $H$, and use $U=H$. In both cases the coefficient
in $2.1$ is $<1/6$, the remainder $2R(U)/U<.1$, and
the logarithm product is at most
$(y^2-(\log U)^2)/2$. The upper limit $e^y>T^*$ avoids
inclusive-endpoint issues.

Split at $1/2$ and $s_*$ and use $|\rho|\ge|\gamma|$.
The **normalized** bound is
$$
 |e_{\psi}(L)|\le e^{-aL} C(L),\quad e_{\psi}(L)=e^{-L}\psi(e^L)-1,
\quad
 C=B_1(L)+[(y^2-h^2)/12+.1]e^{-(b-s_*)L}
 +(y^2/6+3)e^{-(b-1/2)L}+2.091Le^{-(c_*-a)L}.
$$
There is **no additional high-cutoff error** to add to this estimate:
the finite sum is already bounded by the unrestricted positive mass.
The coefficient is nonincreasing from 155 (for the quadratic log
factor subtracting (h^2), the log derivative is (le4/L) since
(y^2>2h^2); the other quadratic has log derivative (le2/L)).
The limit is $w_b$. Dusart Cor. 4.5 (PDF p.13) adds at most
$3e^{-L/2}$ to bound $|\theta(e^L)e^{-L}-1|$.
At $L=168$ the new error is already smaller than the CH2
constant term, $A_0=\pi/(3\cdot10^{12})$; the actual CH2
handoff for a common Mertens bound is certified in `D02_M.md`.
At $L=200$, $C<.213$, whereas the raw contract's
scaled coefficient is $200^2/64=625$ and increasing. This
uses the cap inferred from A, rather than inserting that much
larger raw coefficient into the endpoint errors.

**Without a density theorem:** the same FKS formula with
$T=e^{.19L}$ and only the two reciprocal-sum bounds gives
$$
 |e_{\psi}(L)|\le e^{-aL} \bigl([(y^2-h^2)/12+.1]
 +(y^2/6+3)e^{-(b-1/2)L}+2.091Le^{-(.19-a)L}\bigr),\quad y=.19L+1 .
$$
The same cutoff inequalities and $y>h$ hold from 155.
After dropping $-h^2/12$ and dividing by $L^2$,
all terms decrease and the result is $<.0034$ at 155.
This is a weaker shape but gives a density-free branch, even
before A's direct threshold. Omitting only FKS Table 8 and
using Dusart density instead preserves the log-free power shape;
see the numerical tradeoffs in `D02_M.md`.

For the smoothed formulas let $J_1(L)=\int_L^\infty e_{\psi}(t)dt$.
Use the exact absolutely convergent formula derived in
`mertens_current.md`, §2, with residues as specified there:
$$
 J_1(L)=\sum_{\rho}\frac{e^{(\rho-1)L}}{\rho(\rho-1)}
        -\log(2\pi)e^{-L}+\sum_{k\ge1}\frac{e^{-(2k+1)L}}{2k(2k+1)} .
$$
The derivation uses the integrated Mellin kernel; it does not
interchange an unsmoothed conditional zero sum and integration.
Let $J_2$ be its termwise primitive with $J_2'=-J_1$;
this entails one more inverse $\rho-1$ in absolute value.
The trivial terms cost at most $2e^{-L}$ in each at the
arguments used. The line spectral weight is $<.04620$, by the
identity and exact gamma trim in the inherited proof (CH2 (B.9)
and `refine.py:test_M`); ordinates on the line exceed 14.
Using CH2 Cor. B.2 (PDF p.43) and partial summation,
$2\sum_{\gamma>H}1/\gamma^2<7\cdot10^{-12}$ (inclusion at
(H) obeys the same integral upper bound). Thus on the
analytic Mertens domain $L\ge18.42$ put
$$
 j=.04620e^{-L/2}+2e^{-L}+e^{-aL}k,\qquad
 j_2=.04620e^{-L/2}/14+2e^{-L}+e^{-aL}k/H,
$$
with $k=7\cdot10^{-12}$ below 155 and, from 155, the minimum
of that constant and $B_2(L)+7\cdot10^{-12}e^{-(b-s_*)L}$.
Then $|J_1|\le j, |J_2|\le j_2$. In the high-strip bound
use $|\rho-1|\ge \gamma$, and off-line below $s_*$ use the
full reciprocal-square cap. These bounds only decrease, including
at the join. For the prime-count prefix at 20 use instead the
coarser $k=7\cdot10^{-12}$ everywhere (QRH-free alternative:
drop (e^{-aL}) from the off-line term). This is a second,
independent use of A's strip, including in signed Mertens bounds
below the unsmoothed handoff.

## Reproduction

From this directory with non-login /bin/bash:
`/usr/bin/python3.10 -B d02ram.py`,
`/usr/bin/python3.10 -B d02m.py`,
`/usr/bin/python3.10 -B endpoint_check.py`.
For the new finite tape,
`/usr/bin/g++ -O3 -std=c++17 d02finite.cpp -o /work/d02finite`,
then `/work/d02finite > d02finite_results.txt` (default arguments).
The supplied text receipts reflect actual runs. Checkers must be run
with assertions enabled. They use positive finite sums, exact
integer intervals, and interval covering, never extrapolation
from samples. `d02rigor.py` is a 512-fraction-bit version of the
inherited `rigor.py`: use atanh range reduction and 270 terms
$error (<2^{-512}) for (|z|<1/2)$; for the exponential halve
until the argument is in ([-1,1]) and truncate at degree 99
$tail (\le(101/100)/100!<2^{-512})$, then square outwards.
Machin's identity with exact alternating rational sums encloses
the fixed $\pi$ bracket. Rational constants and comparisons are
exact; displayed interval reports convert to decimals only to aid
reading. No full Lean theorem or source-first PV is asserted.
