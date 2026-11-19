# Own-review repair: domain, source and numerical obligations

This is FOLLOWUP-C010, same D02 input and same B0 originals, not a
new trial. The archive files named prior_* are exact locked
pre-repair bytes; the unchanged original files and the old replays
are also retained. Own review /task/OWN_REVIEW_INDEX.json identifies
the prior bundle and the exact review read. Defect dispositions:

* S-slope-R/M: spectral.md now uses \(10^{-7}\) rather than
  \(10^{-8}\). The magnitude is \(113.67 e^{-L/2}/(2C(L))\),
  strictly decreasing; repair.py brackets its value at 100.
  This retains the original crossing brackets, uniqueness on
  \(L\ge100\), and all original downstream rows.
* R-PT-real: the concrete counterexample and its correctly limited
  integer premise stay visible; the false literal real statement
  remains excluded. The same exact last-real-failure result is
  retained, without appealing to the false statement.
* R-PT-theta-intermediate: correct the small-input bound and prove
  the retained PT published-anchor formulas separately below.
* M-envel-fks5.2 / M-envelope-literal: the false small-\(x\)
  branch is removed, replaced by the exact restricted branch
  below. All other intersections retain their own domains;
  no headline numerical row used the offending region. The
  \(1<x<2\) conventions remain exact.
* M-conversion-code: the positive-denominator conditions are now
  explicit runtime assertions in bounds.py, finite_m.py and the
  new checks. The monotone/left endpoint controls in the proofs
  govern the denominators between certified points and on tails.
  No conversion via \(V/(1-V)\) is used when \(V\ge1\); the full
  pointwise prescription uses exact exponentials instead.

Text-line locators use physical LF in the supplied .txt files.
In particular the CH2 Cor. 1.2 coefficient reads
\((\log^2(T/(2\pi))-\log(T/(2\pi))/3)/(2\pi)\) (PDF p.3,
text 190–222), as in the portfolio, not a third of the square term.

## FKS Lemma 5.2 valid segment, with least real onset

Let \(g(L)=2L^{3/2}e^{-c\sqrt L}\), \(c=.8476836\).
The original Lemma 5.2 (PDF p.17, text 1928–1942) cannot be
invoked on its full printed domain. At 2 and at 2.1, the
actual relative error \(1-\log 2/x\) exceeds \(g(\log x)\)
(directed signs in repair.py). On \([2,3)\) the error has this
exact formula. Its difference subtracted from \(g\) increases
strictly in \(L\): \(g'(L)=\sqrt L e^{-c\sqrt L}(3-c\sqrt L)\)
is at least the product formed from the minimum of each factor
on \([\log2,\log3]\), which exceeds \((\log2)/2\).
Therefore there is a unique root \(r_\psi\) of
\(g(\log x)=1-\log2/x\) in \((2,3)\), with
\(2.29012<r_\psi<2.29014\). The inequality holds on
\([r_\psi,3)\) and fails in a left neighborhood of the root.

On \(3\le x\le e^{40}\) use Dusart Theorem 3.3
(PDF p.8, text 458–475): its .77 bound is below both endpoint
values of \(g\), and \(g\) has just one critical point, a maximum.
On \(40<L\le1000\) use \(1.93378\cdot10^{-8}<g(1000)\),
and on \(1000<L\le2100\) use \(1.94751\cdot10^{-12}<g(2100)\).
These literature-trust step bounds are stated explicitly on the
corresponding strict lower domains in the lemma's original proof;
\(g\) decreases throughout these log intervals. This proves the
repaired enclosed segment, including equality at the left end.
The weaker FKS Cor. 1.4 constant 9.22022 does not need the faulty
small-\(x\) step: on \(2<x<r_\psi\) it already exceeds the
Dusart .77 bound (monotonic \(g\), checked at \(\log 2\)).
The other portions of that source corollary are unchanged.

## PT auxiliary and preservation of its published-anchor bounds

For \(2<x\le599\), PT §5(18) (PDF p.10, text 813–884)
prints \((2-\log2)/2\) as an upper bound for
\(|\theta(x)/x-1|\); at 2.9 this fails. A sharp replacement on
this compact range is \(1-\log2/3\): on each constant-\(\theta\)
interval, \(\theta(x)/x\) decreases, so the endpoints and left
limits suffice. repair.py uses exact prime trial division through
599 and outward logs on both sides of every jump; all the endpoint
tests are strict except the left limit at 3, which equals the
supremum. This auxiliary is not needed to deduce the new
Ramanujan bounds.

More strongly, retain the actual numerical functions of PT
(19),(20) at its published anchor \(U=\log x_a=3914\) (PDF
pp.10–11, text 889–985), i.e., the originally printed coefficients
\(M_a(L),m_a(L)\). For this comparison \(a\) is just the numerical
piecewise function of their (18), including its false first
piece: **do not** use it as a \(\theta\) estimate at small input.
Let \(P_4(L)=\sum_{i=0}^4 i!/L^i\). The existing density-free
R2–R3 and \(b_D^*\) of ramanujan.md prove
\[
 120 < L^5(\Xi(L)-P_4(L)) <120+.19\qquad(L\ge U).
\]
For the lower bound use \(L^6 b_D^*<720\); for the upper use
\(\sum_{i=6}^{20}i!L^{5-i}+L^5(b_D^*+v)<.19\).
All needed terms after scaling are decreasing on this ray
(positive powers in exponentials are dominated by their decay),
and the checks at \(U\) appear in repair.py. The same
upper bound holds for the smooth \(Le^{-L}F(e^L)\) without \(b_D^*\).
Write \(B=1/U+196/U^2\); the bracket in (19),(20) is at least
\(B\) (also under the power-of-two reading in the flattened text).
Clearly \(M_a\ge120+720B>120+.19\), since \(C_1,a\ge0\).

To handle \(m_a\), bound
\[
 -C_2\le U^6 e^{-U}\int_{\log2}^{U}e^u\,a(e^u)/u^7\,du
 \ < 1100 U^6 e^{-114}+\frac{a(x_a)}{.99 U}
 \ < a(x_a)B .
\]
For \(u\le3800\), each printed \(a(e^u)/u^5\) is less than
500: the first piece is <1; maximize \(u^2e^{-u/2}\) at 4 for
the second; for the third use \(u/6.455<1169/6.455<500\)
(with the fourth-root and decaying factors); for the remaining
pieces maximize \(v^{3.04}e^{-1.89v}\) over \(v>0\) at
\(v=3.04/1.89\), using coefficient at most 462. Divide by
\(u^2\) and use \(500/(\log2)^2<1100\).
For \(3800\le u\le U\), the log derivative of the integrand is
\(1-.48/u-1.89/(2\sqrt{5.573412u})\), which is \(>.99\)
(the .48/u allowance is needed in this test).
The final comparison is directed in repair.py. Thus \(m_a\le120\),
since \(C_3,a\ge0\). This validates the actual optional interval
with coefficients \(m_a,M_a\) on log-domain \([3914,\infty)\)
without relying on the false auxiliary estimate. It does not
assert a theorem for arbitrary anchors/formulas. For use at
both Ramanujan arguments its common log-onset is 3915.
