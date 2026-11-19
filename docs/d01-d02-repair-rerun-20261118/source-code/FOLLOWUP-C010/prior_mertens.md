# Mertens products and both prime sums

All endpoints in this file are for **reals**, inclusive unless
specified, with sums over \(p\le x\). Write \(\gamma_{\!E}\) for Euler's
constant and take the constants of Dusart Theorems 5.6 and 5.7 exactly:
\[
 M=\gamma_{\!E}+\sum_p(\log(1-1/p)+1/p),\qquad
 B_3=\gamma_{\!E}+\sum_{m\ge2}\sum_p(\log p)p^{-m}.
\]
Set \(Z_{\rm raw}=\log Q_{\rm raw}-\gamma_{\!E}-\log L\),
\(E_1=\sum1/p-\log L-M\), and \(E_\ell=\sum(\log p)/p-L+B_3\).
The two relative product errors are \(|e^{-Z_{\rm raw}}-1|\)
and \(|e^{Z_{\rm raw}}-1|\).

## 1. Explicit power/logarithm tradeoffs

In the following table let \(a=1/8\) for B0 and \(a=5/32\) for B1.
Each entry \(C\) on \(L\ge u\) proves simultaneously
\[
 \max(|e^{-Z_{\rm raw}}-1|,|e^{Z_{\rm raw}}-1|,|E_1|)
      \le C\,x^{-a}/L,\qquad |E_\ell|\le C\,x^{-a}.           \tag{M1}
\]
The envelope takes the pointwise minimum, also with the signed
branches below, not just a single row.

| \(u\) | B0 \(C\) | B1 \(C\) |
|---:|---:|---:|
|170|.021014|.295890|
|175|.020438|.287504|
|180|.019923|.280038|
|185|.019459|.273345|
|190|.019041|.267310|
|200|.018312|.256857|
|225|.016947|.237375|
|250|.015996|.223871|
|300|.014759|.206366|
|400|.013463|.188160|
|500|.012790|.178806|
|600|.012377|.173108|
|800|.011893|.166482|
|1000|.011616|.162708|

The replay prints unrounded upper endpoints for all rows (separately
for the weighted sum, log envelope and relative envelope), and also
for \(u=1500,2500,5000,10000\). The continuously parametrized family
is given in the proof below. The refined limiting upper constants
from S5 and S8 are \(.010444096(1+1/H)\) and \(.146302424(1+1/H)\) in
the two treatments, for the sup limits after scaling by \(Lx^a\)
for the first three errors and by \(x^a\) for the weighted sum.
The larger new coefficient does not imply a larger error bound:
the different powers matter. Each paired row in M1 is strictly
smaller under B1 throughout its entire stated ray. The ratio for
a pair is \(C_1 e^{-L/32}/C_0\), decreasing, so checking its left
endpoint suffices. All B1 rows retain the better exponent and
the factor \(1/L\) for the product and \(1/p\) channels.

For robustness independently of the density table, for \(L\ge300\)
one has the same errors bounded by \(.0626 Lx^{-a}\) and
\(.0626 L^2 x^{-a}\), respectively, under the same two exponents.
This uses S1 and S8 only. It is weaker than the main portfolio
but still transmits the new power.

## 2. Original and earlier domains, and independent improvements

Retain Dusart Thm. 5.6 (PDF pp.17–18), Thm. 5.7 (pp.18–19) and
Thm. 5.9 (pp.19–20): respectively \(.2/L^3\) for \(E_1\) from
2278383, \(.3/L^2\) for \(E_\ell\) from 912560, and \(.2/L^3\)
for both normalized products from 2278382. Remark 5.8 is not an
additional unconditional bound. An independent earlier-onset
calculation gives the **least real onsets** for these very same
coefficients, with equality at the new onset:

| error / original coefficient | least real onset, given by its local equality | bracket for increment over the indicated integer |
|---|---:|---:|
| \(|e^{Z_{\rm raw}}-1|\), .2 | \(2278379+t\) | \(2.710<t<2.713\) |
| \(|e^{-Z_{\rm raw}}-1|\), .2 | \(2278379+t\) | \(2.574<t<2.577\) |
| \(|E_1|\), .2 | \(2278379+t\) | \(3.111<t<3.115\) |
| \(|E_\ell|\), .3 | \(912559+t\) | \(.997<t<.998\) |

Here the equality is for \(L^3\) times each of the first three
errors and \(L^2\) times the fourth. The sieve verifies no new
prime occurs from each indicated integer prime through its old
Dusart endpoint (through 2278383 for the reciprocal sum).
Throughout each resulting local interval \(Z_{\rm raw},E_1,E_\ell\)
in the relevant channels are positive, small, with fixed prime
data. For example \(L^3(e^{Z_{\rm raw}}-1)\) has derivative in
\(L\) equal to \(L^2(3(e^{Z_{\rm raw}}-1)-e^{Z_{\rm raw}})<0\);
for \(1-e^{-Z_{\rm raw}}\) substitute
\(3(1-e^{-Z_{\rm raw}})-e^{-Z_{\rm raw}}\).
The reciprocal derivative is \(L^2(3E_1-1)<0\), and the weighted
one \(L(2E_\ell-L)<0\). All required signs follow from the
directed local intervals in finite_m.py (their errors are
positive and <.01). The checked bracket is strictly on both
sides; any earlier onset includes a failure just below the root.
Join at the old Dusart endpoint, using the original-source
ray thereafter. These improvements do not use the new input.

Other B0 tradeoffs (also inherited by B1) are as follows. In the
analytic table the same \(c\) bounds the first three errors by
\(c/L^3\) and the last by \(c/L^2\), for all \(L\ge u\).

| \(u\) | \(c\) |
|---:|---:|
|17.8|.1|
|19.5|.05|
|22|.02|
|24|.01|
|32|.005|
|37|.001|
|46|.0001|

Extending the first row **backwards** with the exact sieve and real
cells also gives product and prime reciprocal .1 from 12922000,
and weighted .1 from 18338000. The analogous finite-to-infinite
joins give the following conservative integer-valued **real**
onsets for the shown \(c\). Redundant entries (e.g. the .2 product
onset) need not be used in the pointwise min.

| \(c\) | both products | prime recips | weighted prime log |
|---:|---:|---:|---:|
|.3|625000|625000|912600|
|.25|1515000|1515000|1521000|
|.2|3446000|3446000|3458000|
|.18|3460000|3460000|3471000|
|.15|5385000|5385000|7117000|
|.12|12874000|12874000|12895000|
|.1|12922000|12922000|18338000|

Finite proof and arithmetic: finite_m.py uses the ordinary
Eratosthenes sieve through 54000000, larger than \(e^{17.8}\).
It accumulates interval sums at integer mesh endpoints \(n\)
with next increment \(\lfloor n/80000\rfloor\) (last endpoint
clipped). Every sum is monotone, so between endpoints it lies
in the interval from the left sum's lower end to the right sum's
upper. Subtract the smooth log term with its entire cell image,
and multiply the error magnitude by the **right** endpoint log
power. This proves the full finite intervals including nonintegers.
For a tighter numerical envelope the exact sums and bracketing
values in this check can be used instead of the constant table.

The sums use signed integer fixed point of scale \(2^{80}\).
For integer \(p=2^k m,\ 1\le m<2\), take \(j=\lfloor4096m\rfloor\)
and evaluate \(\log p=k\log2+\log(j/4096)+\log(1+r)\) with
\(0\le r<1/4096\). Three series terms and the next alternating
remainder bound \(2^{-50}\) suffice. Individual floor/ceil losses
are included. For \(-\log(1-1/p)-1/p\), use the exact outward log
for \(p\le1024\), else orders 2 through 5 with remainder \(<2/p^6\).
The code also checks the smaller local endpoints above, with no
cell-width penalty. For gamma it uses
\(\gamma_{\!E}\in[H_n-\log n-1/(2n),\,H_n-\log n-1/(2n)+1/n^2]\).
Indeed subtract the trapezoidal rule on each interval
\([m,m+1]\) from the integral of \(1/t\) and sum for \(m\ge n\);
the positive trapezoid errors have sum at most
\(\sum_{m\ge n}1/(6m^3)<1/n^2\).
For the tails in \(M,B_3\), use the Dusart \(\theta\) relative
error \(\delta=.2/(\log N)^2\) on \(t\ge N=54000000\)
(Thm. 4.2, row \(k=2,\eta=.2\)). For \(M\)'s square term the
main integral is \(\frac12\int_N^\infty t^{-2}/\log t\,dt\),
bracketed by two adjacent integrated geometric polynomials in
\(1/(1+v/\log N)\) after \(t=N e^v\). Its error is at most
\(\delta(3+1/\log N)/(2N\log N)\); higher powers have total
\(\le1/N^2\) by the integer sum. For \(B_3\) the weight for
\(\theta\) is \(1/[t(t-1)]\); its main integral is
\(w=-\log(1-1/N)\), error at most \(\delta(2/(N-1)+w)\).
These inequalities follow from the tail integration rule in §4.
Thus the normalization is independently enclosed, without
rounding a literature decimal to an allegedly exact constant.

## 3. Why the powers and the constants hold

Let
\[
 A=\sum_{n\le x}\Lambda(n)/n-L+\gamma_{\!E},\qquad
 Z=\sum_{n\le x}\Lambda(n)/(n\log n)-\log L-\gamma_{\!E},
 \qquad W(u)=1/u+1/u^2 .
\]
The limits after subtracting \(L\) and \(\log L\) follow from
Dusart 5.7 and 5.6 by adding the appropriate absolutely convergent
prime-power sums. Stieltjes partial summation, followed by
integration by parts with the absolutely continuous \(K\) of S7,
gives
\[
 A=e(L)-K(L),\quad Z=e(L)/L-\int_L^\infty e(u)W(u)\,du,\quad
 \int_L^\infty e(u)W(u)\,du=W(L)K(L)+\int_L^\infty K(u)W'(u)\,du .
                                                               \tag{M2}
\]
These formulas hold with jumps at \(x\) included in the endpoint
sums. Crucially the integral costs \(k_j\), not a new multiple
of the principal bound \(d\) for \(|e|\). The naive approach
\(\int |e|\le d/a\) would cost a factor close to \(1+1/a\).

The prime-power additions are
\[
 E_\ell=A+C_\ell,\quad E_1=Z+C_1,\quad Z_{\rm raw}=Z+C_P .
\]
Here \(C_\ell=\sum_{m\ge2,p^m>x}(\log p)p^{-m}\);
\(C_1=\sum_{m\ge2,p^m>x}p^{-m}/m\); \(C_P\) is \(C_1\)
restricted to \(p\le x\). All are nonnegative.
For \(L\ge18\),
\[
 C_\ell\le1.34e^{-L/2},\qquad C_P\le C_1\le1.34e^{-L/2}/L.
                                                               \tag{M3}
\]
The same bounds with 1.37 work for \(L\ge17.8\).
For the square term use \(\theta(y)=y+O(3.965\,y/\log^2 y)\)
at \(y=e^{L/2}\) (Dusart Thm. 4.2), and the tail integration
rule in §4. Relative to \(e^{-L/2}\), or \(e^{-L/2}/L\) for
\(C_1\), the bound is \(1+(4\cdot3.965/L^2)(3+2/L)\)
(the weighted case needs only 3). For \(3\le m\le M'=\lfloor L/\log2\rfloor\)
use the bound \(\theta(t)\le1.000081t\) stated in Dusart's proof
of Prop. 4.4 (PDF p.13). Discarding the nonpositive endpoint
in the integral, the coefficient at \(e^{-(1-1/m)L}\)
for the weighted sum, or at \(e^{-(1-1/m)L}/L\) for \(C_1\),
is at most \(1.000081\,(m/(m-1))(1+1/L)\).
Sum \(m=3,\ldots,7\) individually and bound all \(m\ge8\)
through \(M'\) by \(L/\log 2\) terms with relative exponential
\(e^{-3L/8}\). For \(m>M'\) use the same \(\theta\) upper bound
integrated from \(2^{-}\), giving total weighted
\(\le3.001\,2^{-M'}<6.002/x\). For \(C_1\) each is further
divided by \(m\log2>L\). This gives pp_check in bounds.py;
every summand in the scaled bound decreases on the stated
rays, so its directed check at the left endpoint suffices.

With \(J_k(L)=\int_L^\infty k_j(u)\,du\), \(p(L)=C_{\rm pp}e^{-L/2}\)
from (M3), and any valid \(d\ge|e(L)|\), define
\[
 U=d+k_j+p,\qquad
 V=\big[d+(1+1/L)k_j+(1/L+2/L^2)J_k+p\big]/L.                 \tag{M4}
\]
Then \(|E_\ell|\le U,\ |E_1|,|Z_{\rm raw}|\le V\).
This uses that \(|W'|\) decreases. For the products take
\(e^V-1\) or the convenient \(V/(1-V)\) when \(V<1\).
For (M1) use \(d=D_j\) and \(C_{\rm pp}=1.34\).
Each component of \(e^{a_jL}U\), \(e^{a_jL}LV\) and
\(1/(1-V)\) is nonincreasing for \(L\ge170\): S4 is a positive
exponential mixture, and the low terms with degrees 1 or 2
still decay after scaling. Thus the code's endpoint expression
\(e^{a_j u}uV(u)/(1-V(u))\) gives the **full ray** for any real
\(u\ge170\). The density-free alternative follows identically
after dividing by the extra \(L^2\), using S1 and \(u=300\).

For the early analytic table use M4 with the B0 \(K\).
Use .791 times \(e^{-L/2}\) through \(\log(10^{13})\);
use the applicable CH2 symmetric bounds thereafter (choose
\(T=10^7\) and \(T=H\), with the strict \(x\)-domains in S3).
From the sheet's \(u\) through 220 take certificate cells
arranged at the branch boundaries. Within a cell use \(d,k_j,J_k,p\)
and inverse powers at the left; \(L^2,L^3\) at the right.
After 220 use \(D_0\) and the same analytically decreasing
terms in \(L^2 U,L^3V/(1-V)\). The last finite sieve cell
overlaps the analytic ray at \(e^{17.8}\); no gap is left.
The weak .1 bound from the analytic join is of course enough
for all finite-table coefficients \(c\ge.1\).

## 4. Full pointwise envelope (including both signs)

This is a functional specification, not a grid: at each real
\(x>1\), retain all branches on their specified domains. For
\(1<x<2\) the sums are empty and products 1 exactly.
For \(x\ge2\), use interval addition, subtraction, and integration
(componentwise after multiplying out signs), and intersect
every valid enclosure of the same quantity.

* \(I_e\): the intervals in spectral.md (including continuous S5,
  S1, the CH2 Cor. 1.3 all-domain bound and all applicable signed
  CH2 Cor. 1.2 parameters). In B1 also retain the exact direct
  majorant for \(L\ge200\), though redundant there. The old
  explicit source bounds are available here too: Dusart
  Proposition 3.2/Table 1 and Theorem 3.3, PT 2021 Theorem 1/Table 1,
  FKS Cor. 1.4 and its Lemma 5.2 domain, and FKS's published
  admissible table instances of Theorems 1.1/1.2 (Tables 5/6;
  not the unconfirmed alternative in Remark 1.5). All enter
  only at their own original thresholds.
* \(I_K\): S8 and its signed-center and tighter high-term variants
  described there. \(I_f\) for \((\theta-x)/x\): subtract from \(I_e\)
  the prime-power drift in \([V_\theta,U_\theta]\), with upper from
  Dusart Cor. 4.5 and lower 0 or the larger of the applicable
  Dusart Prop. 4.3 lower bounds \(.9999e^{-L/2}\) and
  \((1-4/L^3)e^{-L/2}\) for \(x\ge121\).
  Intersect with Dusart Thm. 4.2, PT 2021 Cor. 1, PT 2021
  Lemma 6 and FiniteRH Cor. 1 as applicable. On early domains
  the finite values/cell intervals may be retained too.
* For \(A\) use \(I_e-I_K\) and intersect with the direct
  CH2 Cor. 1.2 (all admissible \(T\)) and Cor. 1.3 weighted
  bounds, and with the direct absolute-tail form
  \(I_e(L)-\int_L^\infty I_e(u)du\).
  For \(Z\) use all of (M2), the scalar radius (M4) without the
  prime-power addition, and the two additional forms
  \(A(L)/L-\int_L^\infty A(u)du/u^2\) and
  \(A(L)/L+\int_L^\infty e(u)(1/L-W(u))du\).
  They follow by partial summation in \(\Lambda(n)/n\),
  or elimination of the endpoint \(e(L)\) in M2.
* Intersect the corrected \(Z+C_1,\ A+C_\ell\) intervals
  for \(E_1,E_\ell\) with the direct \(\theta\) intervals
  \(I_f(L)/L-\int_L^\infty W(u) I_f(u)du\) and
  \(I_f(L)-\int_L^\infty I_f(u)du\). These identities use
  the constant normalizations in Dusart formulas preceding
  (5.7) and following Thm. 5.7, or follow by tail partial
  summation. For the log product use \(Z+C_P\) intersected
  with \(E_1-\sum_{m\ge2,p>x}p^{-m}/m\).
* Prime-power additions can use M3, but also the following
  whole-domain interval rule. For decreasing weight \(w(t)\),
  \(\sum_{p>y}(\log p)w(p)=\int_y^\infty w(t)dt-yf(\log y)w(y)
       -\int_y^\infty t f(\log t)w'(t)dt\) for \(y\ge2\).
  Use \(w=t^{-m}\) or \(t^{-m}/\log t\), intersect with
  positivity, and apply at \(y=x^{1/m}\) (and \(y=x\) when
  needed to enforce \(p\le x\)). If \(y<2\), use \(y=2\) and
  add the term at 2. Include any finite number of powers and
  bound the rest as in M3: the weighted remainder after \(m=m_0\ge2\)
  is \(\le3.001\,2^{-m_0}\); divide by \((m_0+1)\log2\) for
  the \(1/m\) tails. Absolute convergence guarantees validity
  of all these interval intersections.
* For log-product interval \([\ell,u]\), the relative envelopes
  for \(Q\) and \(P\) respectively are
  \(\max(e^u-1,1-e^\ell)\) and \(\max(e^{-\ell}-1,1-e^{-u})\).
  For sums take the larger endpoint magnitude. Minimize each
  with the applicable old Dusart, M1/M4, early and finite
  bounds (and tighter one-sided versions if already available).
  The minima are done **pointwise**, not by comparing average
  performance on a test grid. The integrals in this specification
  converge; one can integrate only up to any chosen large
  endpoint and enclose the rest by the positive exponential
  tails of S4, S8, and M3.


### Independent signed interval in the early range
There is a useful additional B0 branch (hence also B1), not
dependent on asymptotic power improvements:
\[
 E_\ell>.054\,x^{-1/2}\quad(18\le L\le\log10^{13}),\qquad
 E_1,\ Z_{\rm raw}>.06\,x^{-1/2}/L\quad(20.8\le L\le\log10^{13}).
\]
In particular on the latter interval the two normalized products
are on opposite specified sides of 1. For the raw \(P\) error one
can now use \(1-e^{-u}\), not \(e^u-1\), from any valid log upper
endpoint \(u\).

Proof: CH2 Lemma 9.2 permits \(e(L)\ge-.751e^{-L/2}\).
From S8, throughout \(18\le L\le\log10^{13}\) we have
\(k_0\le.048e^{-L/2}\), \(J_k\le.096e^{-L/2}\): after division by
\(e^{-L/2}\), evaluate the increasing high term at 30 and the
remaining decreasing terms at 18. The square correction in
\(C_\ell\) alone is at least \((1-3\cdot 4\cdot3.965/L^2)e^{-L/2}\)
by the same tail rule as in M3. For \(C_1\) use the sharper square
error \(\delta=80/L^3\) from Dusart Thm. 4.2, \(k=3,\eta=10\),
since \(e^{20.8/2}>32321\). Its weighted main integral is bounded
below in \(e^{-L/2}/L\) units by \(1-2/L\) (the first two terms of
the integrated geometric series); its error in these units is at
most \(\delta(3+2/L)\). For \(C_P\) remove at most \(1/x\) by the
telescoping integer tail for all \(p>x\). Insert these inequalities
in M2. In the scaled comparison the negative terms all decrease,
including \(Le^{-L/2}\) for the excluded tail. The directed
inequalities at 18 and 20.8 in bounds.py prove the two constants
above. This is a whole compact interval proof, not a sample of
signs.

## 5. Whole-ray comparison

B1 preserves the entire B0 envelope; its new component
intervals are nested wherever used. There is **strict** improvement
throughout \(L\ge168.82\) against the matched B0 constructions
and the listed explicit original-source branches. Here is one
way to prove it without looking for pairwise sampled crossovers.

On that ray the old endpoint intervals contain the symmetric
interval of radius \(f_0(L)=\min(1.046\cdot10^{-12},.0104e^{-L/8})\).
For the CH2 intervals the radius minus center is at least
\(\pi/T-4/T^2\) for \(10^7\le T\le H\), hence \(>1.046\cdot10^{-12}\).
For old density S4 use its final coefficient, and for S5
use \(B_{\rm int}(s)>.0104\) on every row through \(7/8\)
(order-3 lower checks at each right edge). The density-free
bound is larger as well. The much older power-of-log shapes
are larger than \(f_0\): for the \(\theta\) table one may use
the minimum coefficient for each fixed power, and for FKS and
PT the exponential-\(\sqrt L\) shapes have increasing ratio
to \(e^{-L/8}\) on \(L\ge170\). For clarity on the step values:
Dusart Table 1 through \(b<1500\) uses constants \(\ge8.743\cdot10^{-12}\);
from \(b=1500\) its smallest is \(2.358\cdot10^{-20}\).
PT Table 1 starts at 1000 and has all constants \(\ge6.78\cdot10^{-29}\).
FKS Table 5 before 10000 has all constants \(\ge9\cdot10^{-29}\);
the later constants are all at least \(3.95\cdot10^{-359}\).
Compare each group at its left edge against the *decreasing*
\(f_0\). FKS Table 6 instances have \(A>1,R<6\) and exponent
coefficient \(2/\sqrt R<1\); this suffices already at the
first applicable onset. The remaining applicable source shapes
are checked directly by their monotonic ratios. No claim is
made about an uncomputed optimized instantiation of an arbitrary
parameter formula, or about all conceivable B0 theorems.

The old \(I_K\) intervals contain 0 for \(L\ge170\), even with
the deterministic center. The old intervals for raw-log and
sum errors contain the symmetric radii \(F(L)/L,F(L)\) as
appropriate, where \(F=\min(1.045\cdot10^{-12},.01e^{-L/8})\).
Indeed their endpoint terms preserve \(f_0\) or \(f_0/L\);
integral terms in §4 contain 0, and any lost radius from signed
prime powers, including the tail over \(p>x\), is bounded
by \(3e^{-L/2}\) in scaled units. This allowance is
less than both \( .001\cdot10^{-12}\) and \( .0004 e^{-L/8}\)
at 168.82 and thereafter. In the \(A/L\) formulas the direct
old weighted CH2 bound contains the same symmetric radius.
Independent original relative and early analytic bounds are
larger than these comparison radii as well (their ratios
against the power floor increase; the short \(\min\) plateau
poses no restriction). Thus converting either old log interval
still leaves relative envelopes at least \(F/L\).

In contrast, use \(d=D_1\) in M4. The code checks \(LV/(1-V)\)
at 168.82 below both \(1.045\cdot10^{-12}\) and \(.01e^{-168.82/8}\).
Its ratios against those two functions decrease thereafter,
by the positive mixture argument (now scale by 0 or by \(1/8\),
both at most \(a_1\)); also \(U\le LV\). This proves strict
improvement in every channel on the entire ray. In particular
the new input enables the old exponent with a much smaller
coefficient, e.g. \(.002\,x^{-1/8}/L\) and \(.002\,x^{-1/8}\)
from 170, already using the 170 power row and the decreasing
ratio \(e^{-L/32}\). The matched old density floor alone
prevents such a coefficient on any whole ray within this
envelope, not in the actual arithmetic quantities. Earlier
finite and logarithmic branches do not need the input, and
are retained, including their better small-x domains.

All products and sums here are correlated consequences of the
same endpoint estimates and integrated identity, not independent
experimental successes.
