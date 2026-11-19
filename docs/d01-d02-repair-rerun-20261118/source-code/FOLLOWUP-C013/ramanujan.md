# Ramanujan: real onset and lower profiles (B0, hence also B0+D01)

For \(L=\log x\) let \(R(x)=(ex/L)\pi(x/e)-\pi(x)^2\).
Put \(G(L)=L^6e^{-2L}R(e^L)\). The following results refer to the count
\(\pi (x)=\#\{p\le  x\}\) at every real argument. Endpoints of every bounded
domain in the profile table are included; inequalities for \(G\) are strict.

## Exact strict-positivity onset

Let \(n=38358837682\). There is a unique \(r\) in
\[
 n+.21792636<r<n+.21792637
\]
satisfying \(e r\cdot632207037/\log r=1644673232^2\).
Then \(R(x)>0\) for **all real \(x>r\)**, and \(R(r)=0\).
In particular \(R\ge 0\) on \([r,\infty)\). This strict-positivity ray
cannot start anywhere smaller; the integer onset is \(n+1\).

Proof of the finite join. `verify.py root` checks both prime counts,
that \(x/e\) stays in \([14111427770,14111427771)\) for all \(x\in [n,n+1]\),
and both strict signs of the root bracket. The counts are constant on
\([n,n+1)\). The function \(ex/\log x\) is strictly increasing for \(x>e\),
so the zero and the sign on \([n,n+1)\) are as stated. At integer \(m\ge  n+1\)
through \(10^{11}\) use the computational statement at the start of
Dudek--Platt §3.1 (arXiv:1407.1901v1, PDF p.8: largest **integer**
counterexample through \(10^{11}\)). On \([m,m+1)\), \(\pi (x)\) is constant
and the other product is increasing. For real \(x\in [10^{11},1.15\cdot10^{16}]\)
use their Lemma 3.4, PDF p.10. These are inherited computations, not new
sieves of that full range. The analytic certificate starts at \(e^{36.6}
<1.15\cdot10^{16}\). The successive positivity joins below continue through
400 in log coordinates and then to infinity. Neither this argument nor the
inherited finite assertion uses the full RH assumed in Dudek--Platt
Theorem 1.3. Their Theorem 1.2 is the unconditional \(e^{9658}\) tail.

Platt--Trudgian 1809.03134v2, Theorem 2 (PDF p.3), prints
\(n<x\le  e^{58}\) and \(x\ge  e^{3915}\). The near-\(n\) statement cannot
literally hold for all noninteger reals: the root test proves failure
on \((n,r)\). We do not import that reading or infer any near-\(n\)
margins from it. Its integer early range and positivity on \([n+1,e^{58}]\)
are retained by our joined result. This does not assess the original
computation at other points. No use of its truncated explicit formula
is required here (see FKS Remark 3.3).

## Quantitative portfolio

The profile table in `gap-results.md` gives both connected-ray and
finite-window tradeoffs. An additional stronger, non-polynomial pointwise
lower envelope \(\mathscr G\) is defined below: take the **maximum** of its
branches, the table on its specified domains, and 0 when the root theorem
applies. The finite-window curves are not asserted past their caps
(convert any bound \(G>m\) to \(R>x^2m/L^6\)). The all-ray high-order
entries use the exact Li coefficients, not a fitted asymptotic expansion.

## Analytic construction

Let \(f(t)=e^{-t}\operatorname{Ei}(t)\),
\(S(t)=\sum_{j=0}^{24}j!/t^{j+1}\), \(U(t)=S(t)+5\cdot25!/t^{26}\).
Here \(\operatorname{Ei}(t)=\mathrm{li}(e^t)\) with the principal-value
normalization in Dusart §5.1, PDF p.13. At \(t=35\) the exact-interval
calculation from the convergent series
\(\gamma+\log t+\sum_{j\ge 1} t^j/(j\,j!)\) gives \(S<f<U\)
(the very coarse \(|\gamma|\le 1\) suffices). The series follows by
differentiation and the normalization at zero; alternatively
\(\mathrm{li}(e^t)-\log t-\sum_{j\ge 1}t^j/(j j!)\) is the constant
\(\int_{-\infty}^{-1}e^s/s\,ds+\int_{-1}^{0}(e^s-1)/s\,ds\),
which is between \(-1\) and 1 by \(1-e^s\le -s\).
As \(f'+f=1/t\), \(S'+S=1/t-25!/t^{26}\), and
\(U'+U-1/t=(25!/t^{26})(4-130/t)>0\) for \(t\ge 35\), the barriers hold on
the entire ray by the integrating factor. Also \(tU(t)<1.04\) for
\(t\ge 36\): all terms other than the constant decrease and the endpoint
is checked.

### Directional counting bounds

Write \(v_-(t),v_+(t)\) for bounds on the negative and positive parts of
\(t e^{-t}(\pi (e^t)-\mathrm{li}(e^t))\). The following branches are to be
minimized, separately by direction. In the code `side='1.06'` is the
negative part and `side='-.97'` the positive. For computing \(G\), set
\(v_+(t)=0\) on \([36.6,39.47]\), by Dusart p.15 (proof of Theorem 5.1,
quote of [26], \(\pi (x)<\mathrm{li}(x)\) below \(1.39\cdot10^{17}\) in
the needed range). The chosen upper log endpoint is strictly below it.
This is a source-sign premise, not an extrapolation.

Let \(V_\theta(u)=e^{-u}(\theta(e^u)-e^u)\).
For \(x=e^t\ge 600\), partial summation gives
\[
 {t\over  x}(\pi (x)-\mathrm{li}(x))
  =V_\theta(t)+ t e^{-t}\left(K_b+\int_b^t {e^u V_\theta(u)\over u^2}\,du\right)
 \quad  (b\le  t)
\]
with \(K_b=\pi (e^b)-\mathrm{li}(e^b)-e^b V_\theta(b)/b\).
If \(V_\theta\) is bounded directionally by \(C e^{-(1-a)u}\) and
\(a>2/b\), the integral magnitude (in that direction) is bounded
by \(C e^{at}/((a-2/b)t^2)\), by differentiating \(e^{au}/u^2\).

* For \(\log600\le  t\le 58\), FiniteRH Corollary 1, PDF p.4,
  gives \(|V_\theta|\le  k t^2e^{-t/2}\), \(k=.039789>1/(8\pi )\).
  `verify.py` checks \(|K_{\log600}|<5\) by the elementary prime
  count/log sum and convergent li computation at 600. Integrating
  directly gives \(v_1=k(t^2+2t)e^{-t/2}+5te^{-t}\).
* For \(t\ge 58\) use CH2 Corollary 1.3 (PDF p.3) and Dusart Corollary
  4.5 (PDF p.13):
  \(|V_\theta|<1.05\cdot10^{-12}+115e^{-t/2}\). Here and below the
  quote of Dusart is \(\psi-\theta<(1+1.47\cdot10^{-7})\sqrt{x}
  +1.78x^{1/3}\). At \(b=58\),
  \(b e^{-b}|K_b|\le  v_1(58)+1.05\cdot10^{-12}+115e^{-29}<7\cdot10^{-11}\).
  The derivative rule gives `v2` with factors 1.04 and \(248/115\)
  for the two integrals, respectively.
* At \(t\ge 200\), (D) and the same prime-power correction give
  \(|V_\theta|<.022e^{-t/8}\). With \(b=200\), the new anchor is
  at most \(v_2(200)+.022e^{-25}<1.5\cdot10^{-12}\) in the same
  scaling. At \(b=300\), use \(.0161e^{-t/8}\) and
  \(v_3(300)+.0161e^{-37.5}<2\cdot10^{-18}\).
  These give `v3`, `v4` with factor 1.16 for the integral.
* CH2 Corollary 1.2 (PDF p.3) provides smaller-height alternatives
  for \(t\ge 21\). Put \(A=\pi /(T-1)+3.3/T^2\) and
  \(C=(\log^2(T/(2\pi ))-\frac13\log(T/(2\pi )))/(2\pi )\) for any of
  the ten heights in `Ts`. These heights are verified and less than
  \(e^{21}\); \(e^{21}>10^9\). The coth offset costs at most
  \(\pi ^2/(3T^2)<3.3/T^2\) (CH2 \(7.2\), PDF p.22, or its partial
  fractions for coth). Dusart Proposition 4.3, Corollary 4.5,
  PDF pp.12–13, bound the theta correction between
  \(.9999\sqrt{x}\) and \(1.06\sqrt{x}\) for \(t\ge 21\).
  The resulting negative/positive constants in the square-root term
  can be taken as \(C+1.06, C-.97\). The anchors for both are bounded
  by \(v_1(21)+A+(C+1.06)e^{-21/2}\). The derivative rule with
  \(b=21\) gives the two factors 1.11, 2.48 in `vc`.
  The certificate uses this branch only for \(21\le  t\le 75\).

### An improved branch by averaging in the weight parameter

Use the *uniform in \(\sigma\)* CH2 Proposition 9.1, PDF pp.34–36,
at \(x\) and at \(y=e^{21}\). Write \(J(x)=\sum_{p^k\le  x}1/k\)
and \(J_{1/2}(x)=\sum_{n\le  x}\Lambda(n)n^{-1/2}/\log n\) (sum
starts at 2). For \(0\le \sigma \le 1/2\), the main term, after
subtracting \(x^{1-\sigma}/(1-\sigma)\), is
\(-\zeta'(\sigma)/\zeta(\sigma)\) up to error \(x^{1-\sigma}
(A+C/\sqrt{x})\), with the same (A,C) as above. Use the version
retaining the term at \(\sigma=0\); a singleton does not affect the
integral. Subtract the same expression at \(y\), then integrate
in \(\sigma\) to cancel the zeta term. Indeed the first weighted
sum integrates to \(J(x)-J_{1/2}(x)\) and the pole main term to
\(\mathrm{li}(x)-\mathrm{li}(\sqrt{x})\). The integrated errors
are at most \(x(A+C/\sqrt{x})/t+y(A+C/\sqrt{y})/21\).

For \(35\le  t\le 58\), the change from \(y\) to \(x\) in
\(J_{1/2}-\mathrm{li}(\sqrt{\cdot})\) is bounded absolutely by
\(k(t+21+(t^2-21^2)/4+t-21)<50\): integrate
\(d(\psi(z)-z)/(\sqrt z\log z)\), using the finite RH bound including
the two endpoint terms. Finally the correction from \(J\) to
(pi) is at least \(\sqrt{x}/t\) and at most
\[
 {\sqrt{x}\over  t}\left(1+{2\over  t}+{10.15264\over  t^2}
           +1.2551(e^{-t/6}+(t/.69)e^{-t/4})\right).
\]
Apply Dusart Corollary 5.2, PDF pp.15–16, to the square term and the
basic \(1.2551\) upper bound to all others, separating the cube and
counting \(k\ge 4\) by \(t/\log 2\). The bracket decreases for \(t\ge 21\);
it is \(<1.4\) at 21, \(<1.08\) at 35. Thus the anchor
\(|J(y)-\mathrm{li}(y)|\) is bounded by
\(y(v_1(21)+1.4/\sqrt y)/21\). These are exactly the
`vJ` branches, with square-root constants \(C+1.08\) and \(C-1\).
They avoid the \(1+O(1/t)\) inflation on \(C\) in the previous
theta integration. All branches of each minimum decrease on their
use intervals.

### Envelope and certification of profiles

With these one-sided errors, a strict pointwise lower branch for (G\(t\)) is
\[
 \mathscr G(t)=t^6(S(t-1)/t-U(t)^2)
  -{t^5\over  t-1}v_-(t-1)-t^4v_+(t)(2tU(t)+v_+(t)).
\]
The certified comparisons use the slightly smaller polynomial minorant (P\(t\)) for the first term (and use 2.08 instead of \(2tU\)).
If \(l_i=(i-1)!\) for \(1\le  i\le 25\) and \(u_i=l_i\) there,
\(u_{26}=5\cdot25!\), and coefficients outside their ranges are zero, then
\[
 P(t)=\sum_{k=2}^{52}t^{6-k}
 \left(\sum_{i=1}^{\min(25,k-1)} l_i {k-2\choose i-1}
       -\sum_i u_i u_{k-i}\right).
\]
Truncate the convergent series in \(1/t\) for \(S(t-1)/t\):
every omitted coefficient is positive. Degrees \(k<6\) cancel.
This polynomial both improves over crude leading-order subtraction
and defines the exact higher coefficients used in the table.
The cutoff of 24 Li terms is not a global optimality claim.

For each asserted finite interval, cut at the mesh and at every change
of component bounds (including each point shifted by 1). In a closed
cell ([l,r]), use \(v_-(l-1),v_+(l)\) from branches valid across that
cell. All variation of \(t\) in the error term is covered by powers of
\(r\) and \(1/(l-1)\); set the second term to zero only if the entire
cell is in the sign domain. To test against a target polynomial, subtract
it exactly from \(P\) first, then multiply by \(t^k\) if testing order
\(k\). Bound each signed monomial by its smaller endpoint. The strict
positive residuals are rigorous interval checks. This includes joins
at left and right endpoints; it is not a grid of samples of \(G\).

For a high-order tail \([a,\infty)\), \(a>301\), bound the two errors
using \(v_4\) and
\(t/(t-1)\le  a/(a-1)\). After multiplying by \(t^k\), both errors are
bounded by their caps at \(a\): products \(t^{k+4}v_4(t-1)\) and
\(t^{k+4}v_4(t)\) decrease for \(t>8(k+5)+1\), termwise by the
power-exponential form; \(v_4\) itself decreases. In \(t^k(P-\text{target})\),
terms of degree \(j<k\) in \(1/t\) are nonnegative after subtraction;
use their minima at \(a\). Terms \(j>k\) of positive coefficient may
be discarded, those of negative coefficient have minima at \(a\).
The resulting tail checks prove the stated covers on the full infinite
rays. No abstract asymptotic remainder with an unknown constant is used.

These improvements are secondary B0 results. The input cannot improve
any given profile at any onset: its full real-domain premise is proved
in `density.md`. Earlier candidates based on independently bounded
Pi errors lost most of the margin, especially around the source-sign
cut. The averaged branch repairs much of that loss. For high orders
near \(L=100\)–200 the finite-height CH2 \(x/T\) floor dominates; the
absolute zero-density estimate is not yet competitive there.
