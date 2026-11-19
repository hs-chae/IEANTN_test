# Mertens products and prime sums: signed envelopes and sharp finite joins

All bounds include real $x$ and are right-continuous at primes.
Write $L=\log x$, $P=\prod_{p\le x}(1-1/p)$, $Q=1/P$.
Use the exact constants
$$M=\gamma+\sum_p(\log(1-1/p)+1/p),\qquad
 B_3=\gamma+\sum_p\sum_{k\ge2}\log p/p^k$$
from Dusart Thms 5.6 and 5.7 (original PDF pp.17–18, printed
pp.243–244). Work with
$\delta_Q=\log Q-\gamma-\log L$,
$\delta_S=\sum_{p\le x}1/p-\log L-M$,
$\delta_V=\sum_{p\le x}(\log p)/p-L+B_3$.
For any certified $\delta_Q\in[l,u]$ the two normalized product
factors are in $[e^l,e^u]$ (for $Q$) and $[e^{-u},e^{-l}]$ (for $P$).
Take the best endpoint separately in each direction. The maximum
of their two absolute relative errors is exactly $e^{|\delta_Q|}-1$.

## 1. Whole rays and tradeoffs

In the tables, $c$ means a strict bound $c/L^3$ for the two
absolute relative product errors and $|\delta_S|$, and $c/L^2$
for $|\delta_V|$. Exceptions using non-strict inequalities are stated
where appropriate. Take minima of all applicable certified branches.

| onset | common $c$ | additional premises beyond the original non-QRH premises? |
|:---|:---|:---|
|$10^8$|.0671|none (dominated by the next row, which also uses a finite tape)|
|$5\cdot10^7$|.061|none|
|$2\cdot10^{10}$ (also $e^{23.7}$)|.0077|none|
|$e^{26}$|.0029|none|
|$e^{28}$|.00124|none|
|$e^{29.9}$|.00061|none|
|$e^{43.7}$|.00021|none|
|$e^{43.7}$|.000042|uses original QRH for the very large continuation|
|$e^{47}$|.000012|same|
|$e^{59.5}$|$2\cdot10^{-7}$|same|

For all real $x\ge300000$ the two relative product errors and
$|\delta_S|$ are strictly less than $.0149 x^{-1/8}/L$ and
$|\delta_V|<.0149 x^{-1/8}$. From $x=500000$ the common coefficient
is .013163. The following additional **whole-ray** coefficients in
the same power shapes reduce it:

| log onset | coefficient |
|---:|---:|
|190|.012903|
|200|.01233|
|250|.01055|
|300|.009626|
|400|.008677|
|1000|.007371|

In the Dusart-only spectral variant (no FKS density table) use
.013166 from 500000, .012905 from $L=190$ and the same other
power coefficients. These are B0 bounds; none uses the contract as an extra premise.
The finer pointwise analytic spectral branch has limsup of the
scaled errors at most .00673. In particular, the earlier D01 .0211
product power envelope is strictly dominated on its entire domain,
with a real-onset improvement from $e^{189.5}$ to 300000 at
the stronger common coefficient .0149. This does not imply
that the **power** branch beats the finite or polynomial envelopes
at every small $x$; use their minimum. For matched comparison to
the original Dusart constants, the power form at $L\ge180$
beats $.2/L^3$ and $.3/L^2$ by monotone $L^2e^{-L/8}$.
On smaller domains the precise finite and analytic comparisons
are made below. No global optimality claim about shapes or
coefficients is made.

**Finite pointwise branches and whole-ray onset rows.**
Use each C++ output finite100m.txt, finite20b.txt and finite26.txt
with the rules in finite.md. The columns are ceilings in units
of $10^{-9}$ for the scaled product, reciprocal-sum and weighted-sum
errors, respectively. A band is real **half open on its right**,
except that the terminal endpoint is included in the last band.
Each reported last-failed cell endpoint gives an inclusive sufficient
start for $k/100$ in the respective scaling, provided it is below the
last tape endpoint and the larger analytic ray(s) meet $k/100$.
In finite20b and finite26 every valid such nonzero row connects to
the analytic estimate by .0077 or .0029 respectively. In finite100m
the .0671 bound suffices for $k\ge7$; for lower $k$ use a longer tape
only if it certifies the rest. For instance .01 is valid from
10099524684 for products and $S$, from 10148219812 for $V$,
by finite20b plus the .0077 bridge. The .02 coefficient for all
four is valid from 1133202783 by the same tape, rather than
the earlier .044 from $e^{26}$. The weighted-sum .07 coefficient
is valid from 40890944 by finite100m plus .0671, and product/sum
.09 is valid from 18337513 for products and $S$ using finite100m.
These onsets are sufficient, not generally sharp.

In addition, take all valid whole-ray rows of mertens_results.txt
(the Python finite certificate from C014, restricted to its no-A
results), in units of millionths with inclusive starts; see
historical_d02_mertens.md section U. These start as early as 10000.
Against the **original full domains**, convenient coefficients
for $P,Q$, $S$, $V$ are .199972897, .199928568, .299999703,
beginning at 2278382, 2278383, 912560, respectively. This follows
by the maximum of the finite band ceilings on the matched domains
of finite20b and the .0077 analytic join. These strict improvements
in the coefficients do not arise by rounding down a literature
bound. For early starts where a stronger original estimate
or a different envelope applies, retain it: in particular Dusart
Thm 5.9 (PDF pp.19–20) gives $.2/L^3$ for both products from
2278382; Thms 5.6 and 5.7 give $.2/L^3$ and $.3/L^2$ for the
two sums on the domains just stated. Their partial-summation
proof bounds, e.g. Dusart (5.7) and the analogous weighted
formula, may also be taken pointwise; see §4 below.

**Exact real benchmark onsets.** In the original simultaneous
.2 product envelope, the earliest inclusive ray starts at the
unique root in $(2278381,2278382)$ of
$L^2(e^{-\gamma}Q(2278382)-L)=.2$.
It lies strictly between 2278381.711141839 and 2278381.711141843.
For the original reciprocal-sum .2 coefficient and weighted-sum
.3 coefficient, the earliest inclusive starts are the unique
solutions of $L^3\delta_S=.2$ and $L^2\delta_V=.3$ on the
respective fixed prime states. They lie strictly in
$(2278382.1129,2278382.1130)$ and
$(912559.9973,912559.9974)$. Each root has equality, and
failure occurs arbitrarily close on the left. The integer onset
does not improve for these three comparisons. The exact
derivative/sign and numerical proofs are in
historical_d02_mertens.md §U-sharp with mertens_check.py,
rerun in mertens_sieve_replay.txt. At and beyond the right
integer endpoint of each unit interval use the published
theorem or the stronger finite-and-analytic ray. The
aggressive weighted coefficient .299999 on the original ray
is false already at $x=912560$ (same certificate).

## 2. Analytic signed bounds

Set $u=e^{-L/2}$, $v=e^{-2L/3}$, $m=.9999$, $a=1.000000147$,
$b=1.78$, $K(L)=(1+L)/L^2$ and $P_c(L)=(\psi(x)-\theta(x))/x$.
For $x\ge121$, Dusart Prop. 4.3 and Cor. 4.5 (PDF pp.12–13)
give $m u\le P_c\le a u+b v$. Below, $L\ge18.42$;
the analogous symbolic formulas work farther down with
suitable $\psi$ estimates.

Let $(E_-(L),E_+(L))$ be bounds for the negative/positive
sides of $e_\psi(L)=(\psi(e^L)-e^L)e^{-L}$.
Select minima independently on each side of the following entries:

* Both signs: CH2 Cor. 1.3 $A_0+113.67u$; FiniteRH Cor. 1
  $L^2u/(8\pi)$ up to $x=2.169\cdot10^{25}$ when $x>59$;
  FKS Cor. 1.4 $9.22022 L^{3/2}e^{-.8476836\sqrt L}$ for $x>2$.
* CH2 Lemma 9.2 (PDF p.35 or p.36 across the page break),
  its computed **unweighted** small-range bound gives
  $(.751u,.791u)$ for $10^4\le x\le10^{13}$.
  These are upward roundings of its stated extrema; we make
  no scaling inference from its separate weighted display.
* For $18.42\le L\le43.7$, use
  $( (g(L)-m)u+(7L+2)e^{-L},\, a u+b v)$,
  where $g(L)=1.95+3.9/L+19.5/L^2$. This new branch is
  much better than the finite-RH log-squared branch immediately
  beyond the CH2 small-range end.
  To prove it, put $F(t)=\pi(t)-\operatorname{Li}_2(t)$.
  The sign $\theta(t)<t$ in §2 of ramanujan.md gives $F(t)\le3$
  on $[2,10^{19}]$ by partial summation. Also the finite $\pi$
  comparison quoted in PT2021 p.8 gives
  $L F(x)\ge-g(L)\sqrt{x}-4L$ using the normalization guard
  of that section. Now inverse partial summation gives
  $\theta(x)-x=L F(x)-\int_2^x F(t)dt/t-2$.
  Thus its lower bound is $-g(L)\sqrt{x}-7L-2$,
  whereas its upper bound is zero. Add the allowed power bounds.
* For $34\le L\le59.5$, CH2 Cor. 9.3 (PDF p.36, eq. (9.4))
  gives both sides at most
  $u[(L-2\log(L/(\pi e)))^2-4]/(8\pi)$.
  Its chosen height $2\pi^2e^{L/2}/L$ is increasing and
  in $[10^7,3000175332800]$ by directed checks at both ends.
  More generally one may minimize the elementary CH2 Cor. 1.2
  comparison over all $10^7\le T\le3000175332800$ with
  $x>\max(T,10^9)$: both sides are bounded by
  $$\frac{\pi}{T-1}+\frac{(\pi/T)^2}{3}
       +\frac{q^2-q/3}{2\pi}\,u,\qquad q=\log(T/(2\pi)).$$
  The extra term uses $z\coth z\le1+z^2/3$ as in the proof
  of CH2 Cor. 1.3.
* From 180 use $e^{-L/8}C(L)$ from candidate.md (original QRH).
  Older lawful PS and A1 functions are optional minimum
  branches with the same substitute strip. The direct original
  contract is already dominated on its entire domain.

### Smoothed tail and improvement over repeated absolute integration

Let $J_1(L)=\int_L^\infty e_\psi(t)dt$, using log variables
inside the integral. The smoothed explicit formula is
$$J_1(L)=\sum_\rho\frac{e^{(\rho-1)L}}{\rho(\rho-1)}
        -\log(2\pi)e^{-L}
        +\sum_{k\ge1}\frac{e^{-(2k+1)L}}{2k(2k+1)}.$$
This holds also without QRH (FKS Cor. 1.4 gives convergence).
For details, apply the Mellin kernel $(y-1)_+$ on $\Re s=2$ to
$(-\zeta'/\zeta)(s)e^{(s-1)L}/[s(s-1)]$ and shift to negative
odd integers. The kernel yields $\int_1^x \psi(t)dt/t^2$,
not a half-weighted unsmoothed prime-power sum. Along a sequence
of heights skipping all ordinates by $\gg1/\log T$ (FKS
Lemma 2.1 and Remark 2.2 count $O(\log T)$ local zeros),
CH2 (B.9) subtracted at $2+iT$ gives $O_m(\log^2 T)$ on every
fixed-width strip; the far terms use the summable squared
distances. CH2 (A.3) gives $O(\log(2+|s|))$ on the left odd
lines by the digamma estimate and the absolutely convergent
series on the reflected line. The residue at 1 is $L+\text{constant}$;
at 0 it is $\log(2\pi)/x$; the zero and trivial-zero
terms enter with the opposite sign from the displayed tail.
The left integral vanishes in the limit. Absolute domination
of the zero series by the reciprocal-square sum and limit
as $x\to\infty$ fix the single constant (every nontrivial
$\beta<1$). This is the proof in historical_d01_candidate.md §3
without requiring the new hypothesis or exchanging a
conditionally convergent unsmoothed series with an integral.

The sum of the absolute weights on $\beta=1/2$ is $<.04620$:
take the regularized value at 1 **minus** the value at 0 in
CH2 (B.9). The resulting identity
is $\sum_\rho 1/(\rho(1-\rho))=2+\gamma-\log(4\pi)$.
Indeed the finite part at 1 is $\gamma$, the value at 0 is
$\log(2\pi)$, and $\digamma(3/2)-\digamma(1)=2-2\log2$ by the
series for the log derivative of the gamma function. Each
summand has positive real part, and line summands are positive
reals. The explicit harmonic interval check is in refine.py
(test_M's gamma comparison). CH2 Cor. B.2 (PDF p.43) gives
$2\sum_{\gamma\ge H}\gamma^{-2}\le
2(\log(H/(2\pi))+1)/(\pi H)<7\cdot10^{-12}$.
All off-line zeros are above this height; every ordinate in
absolute value exceeds 14 (CH2 p.43).
   
A pair of bounds for $J_1$ and for the termwise primitive of
its spectral expression, denoted $J_2$ (one further inverse
$\rho-1$), is
\[
 j=.04620u+2e^{-L}+k(L),\qquad
 j_2=(.04620/14)u+2e^{-L}+k(L)/H.
\]
Here $k(L)=7\cdot10^{-12}e^{-L/8}$ with QRH and
$k(L)=7\cdot10^{-12}$ without it. With QRH one may replace
$k$ for $L\ge180$ by
$$e^{-L/8}\min\{7\cdot10^{-12},
         7\cdot10^{-12}e^{-.175L}+B(L)/H\}.$$
The series for $J_2$ is well defined even in the QRH-free case,
by one more inverse ordinate; its derivative is $-J_1$.
This is not an interchange premised on an integrable
constant majorant. All these positive majorants decrease.
The trivial-zero and residue terms jointly cost at most
$2e^{-L}$, also in the primitive. Integrate twice by parts:
$$\left|\int_L^\infty e_\psi(t)K(t)dt\right|
        \le K(L)j(L)+2|K'(L)|j_2(L)=J_K(L).$$
The first part is the boundary term; the remainder uses
$\int_L^\infty K''=|K'(L)|$ after the second integration.
Endpoint terms vanish as $K,K'\to0$ and $J_1,J_2$ bounded.
One may minimize this with the single-integration or absolute
estimate. It improves $2Kj$ on the stated domain: $j_2\le j$
and $2|K'|<K$ there. At large $L$ the off-line coefficient in
the smoothed term is smaller by an explicit factor $1/H$.
The limiting scaled error from the power curve is at most
$w_{1749}(1+1/H)<.00673$, using the sharpened $k$.

### Exact normalization and directions

Put $U_1=\sum_{n\le x}\Lambda(n)/n$,
$U_0=\sum_{2\le n\le x}\Lambda(n)/(n\log n)$.
By Abel summation
$$U_1-L+\gamma=e_\psi(L)-J_1(L),\qquad
 U_0-\log L-\gamma=e_\psi(L)/L-\int_L^\infty e_\psi(t)K(t)dt.$$
The constant identification follows from Dusart Thms 5.6–5.7
and the absolutely convergent prime-power corrections; no
unproved normalization is used. The formulas are invariant
under finite endpoint jumps with inclusive boundary and strict
tail. Add
$$D_1=\sum_{p^k>x,\,k\ge2}\log p/p^k,\quad
 D_0=\sum_{p^k>x,\,k\ge2}1/(kp^k),\quad
 D_Q=D_0-\tau,\quad \tau=\sum_{p>x,\,k\ge2}1/(kp^k)$$
to these two centered errors to get $\delta_V,\delta_S,\delta_Q$,
respectively. All three corrections are nonnegative and
$0\le\tau\le1/(2\lfloor x\rfloor)\le e^{-L}$.
Partial summation over the strictly omitted prime powers
gives $D_1=\int_L^\infty P_c(t)dt-P_c(L)$ and
$D_0=\int_L^\infty P_c(t)K(t)dt-P_c(L)/L$.
Consequently rigorous lower and upper endpoints are
\[
\begin{split}
 (D_1^-,D_1^+)&=((2m-a)u-bv,\ (2a-m)u+1.5b v),\\
 (D_0^-,D_0^+)&=(((2m-a)-2m/L)u/L-bv/L,\
           [a(2-2/L+8/L^2)-m]u/L+1.5b v/L).
\end{split}
\]
For the square-root kernel these follow by twice integrating
$\int_L^\infty e^{-t/2}/t\,dt$: $\int_L^\infty e^{-t/2}K(t)dt$
is between $u(2/L-2/L^2)$ and $u(2/L-2/L^2+8/L^3)$.
For the cubic power use the upper bound $1.5v/L$
by dropping a negative contribution. Clamp lower endpoints
at 0, and take $(\max(0,D_0^- -1/(2\lfloor x\rfloor)),D_0^+)$
for $D_Q$. Add the respective intervals to
$[-E_- -j,E_+ +j]$ or
$[-E_-/L-J_K,E_+/L+J_K]$. This is the signed analytic envelope
for all four requested quantities. If desired also bound the
$U_1$ centered error by CH2's independent $A_0+113.67u$ and
use Abel transfer against $1/\log x$ to $U_0$. The new proof
retains separately the absolute, signed observed-boundary,
and weighted branches: a center $e_\psi(L)$ computed by any
valid method removes its boundary uncertainty entirely.

## 3. Whole-domain checks and the finite joins

mertens_new.py uses exact outward-rounded interval arithmetic.
On each finite log-time cell, it covers every factor by
its interval range and uses the right endpoint for the scale
$L^2$ or $e^{L/8}$. The only elementary approximations are
bounded Taylor series with directed rounding. In the upper
tests it drops the positive lower correction and uses
$e^z-1\le z/(1-z)$ for a nonnegative log error bound;
the actual pointwise signed endpoints above are stronger.
The cuts are 29.9, 43.7 and 59.5. Up to the first cut it
uses CH2 Lemma 9.2, then the new inverse prime-count branch,
then the smaller of finite RH and CH2 Cor. 9.3 (the CH2
Cor. 9.3 entry alone suffices above the finite-RH limit;
on this portion the displayed CH2 expression is smaller than
$L^2u/(8\pi)$, since $0<2\log(L/(\pi e))<L$).
The grid bounds through 59.5 do not need QRH (the off-line
term is bounded without a power of $x$). At $L=28$ and
$26$ the finite comparison margins are reported in
mertens_replay.txt. The .061 ray joins the finite100m bounds from
50000000 and the finite20b bounds through 150000000 to the analytic
.061 proof from $L=18.8$ (so the last finite interval overlaps).

For $L$ between 59.5 and 180, use CH2 and bound the constant
contribution after multiplication by $L^2$ at 180 and the
decreasing scaled exponential terms at 59.5. For the power
bridge use CH2 on $[59.5,186.03]$, scaling the constant
at the right and every exponential decay at the left.
The harmless $1+10^{-9}$ multiplier covers conversion since
the tested log argument is $< 10^{-10}$ on these bridges.
At and above 180 (polynomial), or 186.03 and onward (power),
use the decreasing scaled spectral envelopes, bounding the
two prime-power corrections by $2u,2u/L$. In polynomial
scale every term is bounded by a positive power of $L$ at
most 3 times a decaying exponential of rate at least $1/8$,
along with decreasing reciprocal factors. In power scale
$C(L)$ and all remaining corrections decrease. These
comparisons include the whole analytic tail. To join the
.0149 power curve down to 300000 note that
$e^{L/8}/L^2$ decreases up to 16 and increases thereafter.
Check each finite26 band's maximum by its two ends and
its largest certified coefficient for all three columns
up to the $10^8$ join; the same check with .013163 is performed
for all such bands from 500000. This does not rely on the baseline
constant envelopes being valid below their domains.

For the QRH-free coarser rays in the table,
the remaining interval $[59.5,3000]$ uses the same CH2
bridge, now with the constant $7\cdot10^{-12}$ for the
off-line terms; their $L^2$ scaling is largest at 3000.
The resulting common coefficient is $<.00021$ there.
Beyond 3000 use FKS Cor. 1.4 and Dusart Cor. 4.5, giving
$d(L)=|\theta(e^L)e^{-L}-1|\le .0003/L^3$;
ray_check.py proves this by checking at 3000 and
differentiating positive scaled terms.
The direct theta formula in §4 yields the scaled
weighted error at most $.0003(1/L+1/2)$, and the
scaled reciprocal-sum at most
$.0003(1/L+(1+1/L)/2)$. Conversion and the product tail
fit in the certified common coefficient .00021.
The finite handoffs to the rows marked none are therefore
QRH-free as well, including all finite20b/finite26
threshold rows. No $x^{-1/8}$ claim without the spectral
strip is inferred from this argument.

For the C++ proof see finite.md and finite_opt.cpp.
Current executions at rates 200000 and 1000000 make
smaller cells, in particular resolving a competing
source of error in the finite coefficients: ordinary
monotone bracketing by bin endpoints can substantially
overestimate nonmonotone centered errors when the log
reference changes noticeably across a bin. These programs
mark every composite by its least prime; all interval
arithmetic uses exact signed wide integers and controlled
outward rounding. The sharp-real proofs in the Python
program make both pre- and post-jump tests when needed.
They are elementary computation certificates under the
specified compiler/interpreter semantics and do not
constitute source-first PV. Original finite-height RH,
the quoted Büt​he estimates and published numerical bounds
are retained as literature trust, not recreated by the tape.
The finite and analytic envelopes overlap on closed intervals
or at included terminal endpoints; none depends on extrapolating
a last observed coefficient past the tape.

## 4. Comparison with the original-source and weaker-premise frontiers

The raw Dusart bounds are taken literally as stated (and kept as
minima); the sharp benchmark onsets and the finite matched-domain
improvements are in §1. The additional strong original ingredients
are CH2, FiniteRH, FKS, and QRH as detailed above. Any available
theta envelope $d$ from them or from Dusart can be integrated
directly:
\[
  \delta_V=u_\theta(L)-\int_L^\infty u_\theta(t)dt,\qquad
  \delta_S=u_\theta(L)/L-\int_L^\infty u_\theta(t)K(t)dt,\quad
  \delta_Q=\delta_S-\tau,\quad
  u_\theta(t)=\theta(e^t)e^{-t}-1.
\]
These exact identities follow by the same Abel summation and
fixing constants at infinity. Integrate the pointwise minimum
of all legal $d$, and on ranges with $\theta< x$ use that
sign; the $e^{43.7}$ sign cutoff is available from FiniteRH.
This contains Dusart's eta/log-polynomial transfers when their
thresholds apply, and the QRH-free signed $d_U$ analytic envelope
of historical_d02_mertens.md. For example that document's
.125/.135 rays propagate with no A; both are strictly improved
by the .0671 common coefficient at the same $10^8$ onset.
Its finite results at earlier onsets are preserved in the
pointwise minimum. The direct theta and smoothed psi branches
need not dominate one another at every transition; retain
both, rather than compare just a sample grid. The new
twice-smoothed branch beats the older smoothed kernel multiplier
as proved above, and the new finite theta recovery strictly
improves the middle finite-RH psi comparison (there is no
log-squared factor in its square-root coefficient).

Since B0 implies the exact mounted premise, replacing it by
that premise at any occurrence cannot change the lawful
original-input envelope. This logical tie is on **all** matched
domains and holds also for any untried proof using the mounted
premise. Without access to a stronger spectral restriction,
the boundary jump error, not the absolutely convergent
tail, limits the stronger power/log asymptotic. In fact an
$o(x^{-1/8})$ result for $\delta_V$, or
$o(x^{-1/8}/\log x)$ for $\delta_S$ or either normalized product
error, would imply $\psi(x)-x=o(x^{7/8})$ by reverse partial
summation on $U_1$ or $U_0$ (prime-power and elementary tails
are smaller). Setting $s=\rho+\epsilon$ in the Mellin formula
in candidate.md then yields
$\epsilon\int_1^\infty o(t^{7/8})t^{-s-1}dt\to0$
if $\Re\rho=7/8$, contradicting a pole there. An improvement
of the exponent with a fixed log loss would similarly
force a smaller strip. This is a mathematical bottleneck
of the known strip, not a claim that there are boundary
zeros or that no stronger bound can ever be proved.
