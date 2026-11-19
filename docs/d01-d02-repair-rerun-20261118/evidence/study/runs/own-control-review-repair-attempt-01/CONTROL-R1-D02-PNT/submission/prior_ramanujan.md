# Ramanujan gap

Define \(R(x)=(ex/\log x)\pi(x/e)-\pi(x)^2\), and \(G=L^6R(x)/x^2\).
Premises B0 and B1 are as in spectral.md. The following strict bounds
are for **real** \(x\). In a table of log-onsets \(u\) the endpoint
\(x=e^u\) is included.

## Exact last real failure (input-independent)

Put \(n=38358837682,\ A=1644673232,\ B=632207037\).
The last real failure is the unique root \(r\) in \((n,n+1)\) of
\[
    e\,r B/\log r=A^2.
\]
The independently certified bracket is
\[
 38358837682.217926<r<38358837682.217927.
\]
In particular \(R(x)>0\) for **all real \(x>r\)**, and this strict
ray cannot start at or to the left of \(r\). The last integer
failure is \(n\); the closed integer ray starts at \(n+1\).
Equality holds at \(r\).

Evidence: bounds.py endpoint uses exact falling-floor prime counting.
Start with counts \(s(v)=v-1\) for the distinct positive
\(v=\lfloor N/i\rfloor\). On detecting a prime \(p\) by
\(s(p)>s(p-1)\), for descending \(v\ge p^2\) subtract
\(s(\lfloor v/p\rfloor)-s(p-1)\). These are the remaining integers
with least prime factor \(p\), of the form \(p k\), \(k\ge p\).
Closure of the quotient set under \(v\mapsto\lfloor v/p\rfloor\)
and the decreasing update order make this an exact sieve; at the
end only primes remain. It gives \(\pi(n)=A\) and
\(\pi(14111427770)=B\). Both \(n/e\) and \((n+1)/e\) have floor
14111427770. Thus both counts on \([n,n+1)\) are as specified,
and there the coefficient \(ex/\log x\) is continuous strictly
increasing. Directed computation gives \(R(n)<-14736927\) and the
strict sign tests at the displayed bracket.

The inherited finite integer input is the integer portion of PT
2021, Theorem 2 (arXiv:1809.03134v2 PDF p.3, lines 229–236):
from \(n+1\) through the last integer at most \(e^{58}\).
Its printed lower-range statement, if read literally as **real**
\(n<x\le e^{58}\), is false: the left bracket endpoint above is an
explicit counterexample. Its finite integer portion, not the
incorrect real endpoint, is used here at original literature trust.
For \(x\ge n+1\) through \(e^{58}\), \(\pi(x)=\pi(\lfloor x\rfloor)\),
while \(ex/\log x\) and \(\pi(x/e)\) are nondecreasing, so the integer
claim extends to these reals. At \(e^{58}\) the new analytic ray
already applies and there is no upper join gap. Dudek–Platt
(arXiv:1407.1901v1) gives the same last integer candidate (intro,
PDF p.2, lines 45–55; computation, p.8, lines 591–594); its
Theorem 1.3 for all integers is conditional on full RH and is not
used as such. The new proof replaces the old analytic thresholds
\(e^{3915}\) (PT 2021) and \(e^{9658}\) (Dudek–Platt Thm. 1.2).
The input-independent sign onset is already sharp, so the extra
assumption cannot improve it.

## Quantitative statements

The column \(k,m\) means
\[
 G>\sum_{i=0}^{k-1}c_i L^{-i}+m L^{-k}.
                                                               \tag{R1}
\]
The first coefficients are \(c_0=1,c_1=14,c_2=145,c_3=1412,
c_4=13985,c_5=145450,c_6=1610021,c_7=19063832\). Rows compare
proven sufficient onsets; they are not asserted to be globally
optimal, even under B0 or B1 separately.

| k | m | B0 log-onset | B1 log-onset |
|---:|---:|---:|---:|
|0|0|39.15|39.15|
|0|.25|39.8|39.8|
|0|.5|40.5|40.5|
|0|.75|41.4|41.4|
|0|.9|42.1|42.1|
|0|1|42.6|42.6|
|1|10|45.2|45.2|
|1|13|46.6|46.6|
|1|14|47.25|47.25|
|2|7.8|47.5|47.5|
|2|8.6|48|48|
|2|75|196|48.9|
|2|80|196.65|49.05|
|2|80.7|197|49|
|2|100|200|171.8|
|2|130|208.65|178.35|
|2|140|214.9|182.8|
|2|145|220.55|186.7|
|3|1300|242.65|203.5|
|3|1400|251.8|209.95|
|3|1412|253.65|211.11|
|4|10000|265.9|220.6|
|4|13000|277.1|229.05|
|4|13985|287.93|236.52|
|5|100000|299.35|245.45|
|5|140000|315.4|257.45|
|5|145450|322.85|262.45|
|6|1000000|332.5|270|
|6|1600000|356.5|287.7|

Take the pointwise maximum of applicable rows, as well as the full
profiles below. An early onset with a smaller coefficient is
retained when useful. Examples fixing an onset instead:

| \(k\) | log-onset | B0 certified \(m\) | B1 certified \(m\) |
|---:|---:|---:|---:|
|2|50|8.6|80.7|
|2|170|7.8|86.7|
|2|180|7.8|134.5|
|2|190|14.9|145|
|2|200|100.6|145|
|3|211.25|−2100|1412|
|4|237|−56066|13985|

(The 8.6 B0 bound is good throughout \(L\ge48\), hence on the 170
and 180 rays too; their table entries are the checks for the
symmetric profile alone.) The high-order improvement matters:
for \(m<1,k=0\) the bottleneck is the much earlier finite-height
comparison; \(G\to1\), so no whole-ray \(k=0\) margin above 1
could follow or be true. Certificates also test points where the
symmetric B0 profile falls short; these tests are **not upper
bounds on the actual gap**. This is a matched-method B0
reconstruction, not an independent blind baseline run.

Additional early results, under B0 already: using the finite
\(\pi(x)<\operatorname{li}(x)\) check quoted in the proof of
Dudek–Platt Lemma 3.2 (PDF p.8, text 561–563; only its stated
finite range through \(1.2\cdot10^{17}\)), one has these closed rays:
\[
 G>0\ (L\ge36.55),\quad G>.05\ (L\ge36.64),\
 G>.1\ (L\ge36.75),\quad G>.16\ (L\ge36.88).
\]
Also \(G>.2\) on \(36.98\le L\le\log(1.2\cdot10^{17})\)
and \(G>.8\) on \(39\le L\le\log(1.2\cdot10^{17})\).
The signed check is a finite input independent of full RH in that
proof; the conditional conclusion of Lemma 3.2 is not imported.
There is no need to apply its lower li bound outside finite RH.

The following separate fallback does not use FKS's density
corollary: \(k=0,m=0\) from 39.25 in both treatments and, after
switching to \(D_j^*\), \(k=2,m=145\) from 360 versus 275 and
\(k=3,m=1412\) from 405 versus 326 (B0 versus B1).

## Pointwise profile and proof

Let \(P(L)=\sum_{q=0}^{20}q!/L^q\), \(\Xi(L)=L e^{-L}\pi(e^L)\), and
\(F(x)=2/\log 2+\int_2^x dt/\log t\). This last reference avoids
any ambiguity about the normalization of li. For \(L\ge30\),
\[
 P(L)\le Le^{-L}F(e^L)\le P(L)+v(L),\quad
 v(L)=10Le^{-L}+\tfrac{15}4\,21!\,L^{-21}.                    \tag{R2}
\]
At 30, \(F(e^{30})-e^{30}P(30)/30\) is in (0,10): integrate
the positive series for \(e^u/u\) starting at \(\log2\) and
bound its tail geometrically after term 180. It is about 9.124.
The derivative of the difference is \(21!e^L/L^{22}\), and the
log derivative of \(e^L/L^{22}\) is at least \(1-22/30=4/15\)
on this ray. Integrating proves R2. No asymptotic expansion is
being used as a convergent infinite series.

For \(x\ge2\) Stieltjes partial summation, including the atom
at 2, gives
\[
 \Xi(L)-Le^{-L}F(e^L)
 =f(L)+Le^{-L}\!\int_{\log2}^L {e^u f(u)\over u^2}du,
 \qquad f(u)=\theta(e^u)e^{-u}-1.                             \tag{R3}
\]
The following constants and functions give bounds on its absolute
value (use a minimum of all available terms):
* For \(20\le L\le58\), put \(d_F=L^2/(8\pi)\).
  If \(34\le L\le58\), also take the min of \(d_F\) and
  \(e^{L/2}F_\psi(L)+1.000001+1.78e^{-L/6}\).
  Then \(b_F=(d_F+2L/(8\pi))e^{-L/2}+1250Le^{-L}\).
  Indeed the finite \(\theta\) bound from PT 2021 Lemma 6 applies
  above 599; below it, Dusart Theorem 4.2 at \(k=0\) bounds the
  initial absolute integral by \(599/(\log2)^2<1250\).
  The alternative endpoint follows from S6 and Dusart Cor. 4.5.
* For \(L\ge20\) take
\[
 b_C=\lambda(1+10/(9L))+
      114.671001(1+2.5/L)e^{-L/2}
      +1.78(1+30/(7L))e^{-2L/3}+3100Le^{-L}.
\]
  Through \(\log H\) the finite \(\theta\) bound is stronger
  than the endpoint used here. Thereafter use \(C(L)\) plus
  \(U(L)=1.000001 e^{-L/2}+1.78 e^{-2L/3}\) from Cor. 4.5.
* For \(L\ge40\) take
\[
 b_{D,j}=(1+1.63/L)D_j(L)+
      1.000001(1+2.23/L)e^{-L/2}
      +1.78(1+3.53/L)e^{-2L/3}+4\cdot10^7 Le^{-L}.
\]
  The identical formula works with \(D_j^*\) or the continuous upper
  bound S5. For the analytic monotonicity checks use the positive
  mixture S4 or S1.

For the integral in the second and third cases, start at \(v=20\)
or 40, respectively. The early absolute integral is bounded by
\(1250+e^{v/2}/(4\pi)\), smaller than 3100 or \(4\cdot10^7\).
For each later positive term \(u^p e^{-a u}\) the integrand has
log derivative at least \(1-a-2/v\) (here \(p\ge0\)).
This bounds its integral by its terminal value divided by
\(1-a-2/v\), and gives the displayed constants. In the D branch
\(a\le1/3\) for its own terms. Let \(b_j\) denote the min of the
applicable bounds \(b_F,b_C,b_{D,j}\) in this paragraph only
(distinct from the spectral cutoff notation).

**Signed refinement.** At \(L\ge34\) use
\[
 d_j=\min\{C,\ F_\psi\ (34\le L\le58),\ D_j\ (L\ge40)\},
\]
and \(V=.9999e^{-L/2}\le(\psi(e^L)-\theta(e^L))e^{-L}\)
from Dusart Prop. 4.3. Integration by parts using \(e(u)=-K'(u)\)
a.e. bounds the contribution of the \(\psi\) error to the part of
the R3 integral from 20 onwards by the terminal \(k_j(L)/L\),
a term from the endpoint 20, and
\[
 Le^{-L}\int_{20}^L e^u(1/u^2-2/u^3) k_j(u)\,du.
\]
Together with the initial **theta** integral through 20 this is
bounded in absolute value by
\[
 J_j(L)=\frac{.1645e^{-L/2}
      +8\cdot10^{-12}(1+1/(.9-a_j))e^{-a_jL}
      +1.838e^{-L}+e^{-3L}}{L}+3104Le^{-L}.
\]
For \(a=.5,a_j\) use the log-derivative bound just proved;
the two other integrated terms and the endpoint at 20 are
bounded by \(Le^{-L}\) times
\(1.838/20+e^{-40}/800+e^{20}k_j(20)/400<4\).
In (R3) the drift is **subtracted** at the endpoint and in the
remaining integral. For an upper bound keep just its lower
endpoint \(V\); for a lower bound bound both pieces by
\(U_2=1.000001(1+2.5/L)e^{-L/2}+1.78(1+30/(7L))e^{-2L/3}\).
Thus the positive upper error and lower-error magnitude can be
taken as
\[
 u_j=\max(0,\min(b_j,d_j+J_j-V)),\qquad
 w_j=\min(b_j,d_j+J_j+U_2).                                  \tag{R4}
\]
The signed finite \(\pi<\operatorname{li}\) input furthermore
allows \(u_j=0\) through \(x=1.2\cdot10^{17}\).
For the usual principal-value normalization,
\(\operatorname{li}(2)<2/\log2\): substitute \(t=\log x\),
pair \([-\log2,\log2]\), bound the integral of \(2\sinh(t)/t\)
by \(2-.5\), and note the negative unpaired remainder.
For the normalization starting at 2 the inequality with \(F\)
is automatic.

Set, for \(0\le i\le36\), \(q=i+4\) and
\[
 c_i=\sum_{k=0}^{\min(20,q)}k!\binom{q}{k}
       -\sum_{k=\max(0,q-20)}^{\min(20,q)}k!(q-k)! .
\]
For all \(L\ge35\) a strict profile is
\[
 G>\sum_{i=0}^{36}c_i L^{-i}
       -L^4\left[{L\over L-1}w_j(L-1)
              +z_j(L)(2P(L)+z_j(L))\right],\qquad z_j=v+u_j.  \tag{R5}
\]
One can also use \(u_j=w_j=b_j\) and take the max with that result,
or use continuous S5 in the pointwise formulas. Indeed
\(G=L^4[(L/(L-1))\Xi(L-1)-\Xi(L)^2]\). In the main-term
difference involving \(P\), the coefficients at degrees 0–3
in \(1/L\) cancel exactly; the displayed formula computes through
degree 40. The omitted terms in the first summand are all
positive, and the square has degree 40, proving strictness
without relying on strictly rounded prime error bounds. For a
still tighter pointwise result one can use the exact rational
main expression \(L^4[(L/(L-1))P(L-1)-P(L)^2]\), using R5 as
the convenient strict certificate. These profiles retain the
higher-order terms even where an individual constant-margin
row does not apply.

**Whole-domain certification.** For R1 multiply (R5) after
subtracting the prefix by \(L^k\). On each certificate cell
\([l,r]\) bound positive main coefficients at \(r\) and negative
ones at \(l\); for the loss take the powers of \(L\) at \(r\),
the factor \(L/(L-1)\), \(P,v\), and decreasing errors at \(l\)
(with \(l-1\) where appropriate). In the signed upper error
use the subtractive \(V\) at \(r\). All decreasing factors are
positive exponential polynomials, or inverse powers, except
the finite S6 expression: its log derivative is negative
on \([34,58]\) since the polynomial factor has log derivative
less than .1, as seen from \(L-2\log(L/(\pi e))>30\) and
its derivative \(1-2/L\). The cells split at applicability
boundaries, including their shifts by 1. At 58 and 59 the
following cell may simply use the bounds not needing the
finite branch. The finite signed bridge is checked slightly
past its last log endpoint for the numerical expression only,
then used just up to the allowed original \(x\). It overlaps
the analytic .16 ray starting at 39.32. Every accepted cell
is a proof, not a test at a sample point.

For \(L\ge450\), use \(b_D\) (or the corresponding fallback).
Each term of the scaled loss, and the dropped negative
coefficients, is nonincreasing there: for the exponent power
\(d=k+4\) or \(k+5\), use \((d+2)/(L-1)<1/8\), and
\(d<21\) for the inverse-power remainder; \(L/(L-1)\) and
\(P\) are decreasing. The code verifies at 450 that this
loss plus all absolute negative terms is below \(c_k-m\).
When \(m=c_k\), instead scale by one extra \(L\) and compare
to \(c_{k+1}\). No finite-ray check is substituted for this
tail argument; all onsets and finite joins are inclusive.

The assumption changes only the spectral cutoff and error
bounds downstream of it. A positive leading margin and the
exact connected sign ray already hold under B0. The important
new improvement is elimination of the dip from the old
finite-height plateau near log 189, which is decisive for
several higher-order ray margins starting near log 49.

## Comparison with additional original prime-counting branches

For reuse as a single pointwise portfolio, one may also intersect
the upper/lower \(\pi\) bounds with the original directly applicable
ones before inserting them in the definition of \(R\).
In particular retain Dusart Thm. 5.1 and Cor. 5.2–5.3 at their separate
real endpoints, PT 2021 Cor. 2 on \(L\ge2000\), and the original
PT 2021 §5 bounds with its \((19),(20)\) applied separately at
\(x\) and \(x/e\) on their common domain. Use the normalization
\(\int_2^x\) for PT's \(\operatorname{li}\) (its §5, PDF p.8),
and add the constant \(2/\log2\) when comparing with \(F\).
A positive lower integer/real sign result is retained outright
without any substitution. The log-onset tables above use
stronger explicit matched B0 transfers rather than using only
the nonquantitative sign theorem as the control.

More specifically, R4–R5, using the matched minimums (also with
S5 if desired), are nested everywhere. They are strictly stronger
under B1 for \(L\ge168.82\). To verify strictness, use the B0
floor \(f_0(L)\) of mertens.md, §5, for \(D_0,C\) and the
continuous branch. The symmetric \(b_0\) is at least \(f_0\);
the signed upper-error option is at least \(f_0-V\), which is
above \(F(L)\) as defined there for the comparison radius.
Under B1, \(D_1+J_1<F(L)\) by the directed check at 168.82
and monotonicity of the ratios to both defining functions of
that radius (all terms are positive exponential mixtures with
at most quadratic factors, and decay after rescaling).
Thus \(u_1<u_0\). The other error \(w_1(L-1)\le w_0(L-1)\),
so the loss in R5 strictly decreases. The statement concerns
the constructed profiles, not an upper bound on what can be
proved with B0. The symbol \(F(L)\) in this paragraph alone
refers to the Mertens comparison radius, not the smooth
prime-counting main term \(F(x)\) in R2.
