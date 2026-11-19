# Ramanujan gap (B0; hence also B0+D01)

Let \(L=\log x\), \(R(x)=e x\pi(x/e)/L-\pi(x)^2\), and use profile units \(x^2/L^6\). Domains are real and left-closed unless indicated otherwise.

## Portfolio

1. Put \(B=38358837682\). The **last real failure** of \(R(x)>0\) is the unique \(\xi\in(B,B+1)\) satisfying
\[
        632207037\, e\xi/\log\xi=1644673232^2.
\]
In fact \(B+7141/32768<\xi<B+57129/262144\). There is strict positivity for \(x>\xi\), equality at \(\xi\), and strict failure on \([B,\xi)\). The integer onset \(B+1\) is retained and is sharp. This uses the published *integer* outcome for the early range, an independent exact endpoint computation, and a new analytic continuation. Without the published early checks the standalone analytic theorem starts at \(e^{36.85}\).
2. The following are whole rays of **strict** bounds \(R(x)>(x^2/L^6)p(1/L)\); “first m” is the first m coefficients of \(Z\), where
\[
 Z_i=(i+4)!\sum_{j=0}^{i+4}1/j!-\sum_{k=0}^{i+4} k!(i+4-k)!.
\]
   
   | \(L\ge\) | \(p(z)\) |
   |---:|:---|
   |36.85|.03|
   |37|.09|
   |37.15|.10|
   |39.5|.12|
   |39.6|.16|
   |40|.32|
   |40.5|.50|
   |41|.65|
   |42.2|.90|
   |42.85|1|
   |45.4|\(1+10z\)|
   |46.2|\(1+12z\)|
   |46.8|\(1+13z\)|
   |47.4|\(1+14z\)|
   |48|\(1+14z+5z^2\)|
   |217|\(1+14z+140z^2\)|
   |222|\(1+14z+145z^2\)|
   |270|\(1+14z+145z^2+1412z^3\)|
   |420|first 8|
   |510|first 10|
   |620|first 13|
   |840|first 16|

   On closed bounded L intervals there are also .28 on [37.5,39.47], .50 on [38.1,39.47], .74 on [39,39.47], \(1+14z+100z^2\) on [50,150], \(1+14z+130z^2\) on [52,135], and \(1+14z+145z^2\) on [55,119]. Take the pointwise maximum of applicable rows. For example at fixed onset \(e^{38.1}\) the whole-ray .10 becomes .50 through \(e^{39.47}\); at fixed margin .50 a connected ray starts by \(e^{40.5}\) and there is the separate earlier window. At \(e^{48}\) the next coefficient 5 improves the onset at the price of a weaker margin than 140. gap_envelope.txt records rational checks; PASS entries are valid, FAIL is a certificate failure only. Onsets are sufficient, not asserted optimal.
3. A further explicit non-polynomial bound on \(L\ge36.85\) is
\[
 \frac{R(x)L^6}{x^2}\ge
 L^4\left[\frac{L}{L-1}\{A(L-1)-q(L-1)\}-\{A(L)+q_+(L)\}^2\right],
 \qquad A(u)=u e^{-u}\operatorname{li}(e^u).
\tag{2}
\]
It can be kept in the pointwise maximum (at equality with a strict branch, retain strictness). \(q,q_+\) below are explicit. This profile differs from the exact logarithmic-integral model by an exponentially decaying error up to powers of L. It need not be positive when a different branch certifies positivity.

**Source comparison.** Dudek–Platt Theorem 1.2 p. 2 proves \(R>0\) for \(L\ge9658\); Theorem 1.3 there specifies the last *integer* failure under full RH, with their RH argument used beyond a finite range (Lemmas 3.2, 3.4, pp. 7–10). Platt–Trudgian (*The error term in the prime number theorem*) Theorem 2 p. 3 prints \(B<x\le e^{58}\) and \(x\ge e^{3915}\). Its literal real left endpoint is incorrect by the calculation below; retain the reported integer part of its early range at literature trust. We bridge \(58<L<3915\) and give strict quantitative improvements over their sign-only bounds on matched domains, not just a new later sign bound. The exact B0 versus B0+D01 consequence-envelope comparison is an equality by common.md, so none of these improvements is attributable to D01. We do not claim a blind independent baseline, or optimal margins.

## Proof at the real left edge

edge.py gives \(\lfloor x/e\rfloor=14111427770\) throughout \([B,B+1]\) by directed rational bounds on e. For \(x<B+1\) also \(\pi(x)=\pi(B)\). The code also checks the integer sign at B+1 independently. The two key exact prime counts are \(\pi(B)=1644673232\), \(\pi(14111427770)=632207037\). For its quotient algorithm, start by counting every integer from 2 through each quotient y. At a prime p reject those \(pk\le y\) with \(k\ge p\) having no smaller prime factor. Their count is the difference of preceding counts at \(\lfloor y/p\rfloor\) and \(p-1\). Every composite is removed at its least prime factor. The set of floor quotients is closed under the floor divisions and contains all needed small arguments; descending updates preserve the preceding counts. The count difference at p and p−1 tests whether p survives and is prime before its turn. Processing through \(\lfloor\sqrt n\rfloor\) suffices. The sign tests use exact rational exp bounds and \(\log r=2\sum_{j\ge0}z^{2j+1}/(2j+1)\) for \(z=(r-1)/(r+1)\), \(1\le r\le2\), plus a geometric remainder and range reduction by powers of two. The monotone function \(x/\log x\) yields the unique crossing and all signs on the unit interval.

For \(x\in[B+1,e^{58}]\), take \(n=\lfloor x\rfloor\). Apply the published integer sign there, \(\pi(x)=\pi(n)\), and monotonicity of \(x/\log x\) and \(\pi(x/e)\), so \(R(x)\ge R(n)>0\). No use is made of an invalid bound \(\pi(y+h)-\pi(y)\le h\) at arbitrary noninteger endpoints. The new analytic bound overlaps. A small explicit profile here is \(R(x)>(ex/\log x-en/\log n)\pi(n/e)\); one may lower the right side by substituting \((n/e)/\log(n/e)\) for the count (Dusart Cor. 5.2, p. 15). It vanishes at the integers, where the published strict sign is used. The early large-range sieve is not independently replayed.

## Transfer from θ

Use the original principal-value normalization of \(\operatorname{li}\). At \(\log y=J\) partial summation gives
\[
 \pi(e^u)-\operatorname{li}(e^u)
 =e^u\eta(u)/u+\int_J^u e^v\eta(v)/v^2\,dv+K_J,\qquad
 K_J=\pi(e^J)-\operatorname{li}(e^J)-e^J\eta(J)/J.
\tag{3}
\]
Normalize by \(u e^{-u}\). A bound \(b u^m e^{-cu}\) for \(|\eta(u)|\) from J, \(m\le2\), contributes at most \(b u^m e^{-cu}(1+1/(\delta u))\), \(\delta=1-c-(2-m)/J>0\), because the log-derivative of the integrand's majorant is at least \(\delta\). At J=20, the finite RH π and θ bounds give \(|K_J|\le(20^2+20)e^{10}/25<400000\). The candidate q_c (qc in the script) uses (3) via the CH bound plus P and anchor \(400000u e^{-u}\). At J=150, (3) and the CH+P and q_c bounds at J bound the new anchor, giving candidate q_a via DEN+P. Via G+P it gives q_l: the log slope for the layer integrand is bounded below by \(1-1/8-2/J-91.2/[J(J-91.2)]\). The two-slope bound of common.md gives q_lt (qlt): use a separate tr slope for each positive term. For the first, substitute \(M_2\) for 91.2 above; for the second, the log slope of the integrand is bounded below by \(1-1/8-d_0-1/J-1/(J-M_1)-1/(J-M_2)\). These are all bounds for normalized absolute π error.

For \(34\le u\le58\), use adaptive CH Cor. 1.2 at \(T=.65e^{u/2}\), so \(10^7\le T\le H\) and \(e^u>\max(T,10^9)\). Its first two relative error terms are \(\le3.15/T\). With \(w=\log(2\pi/.65)\in(2.26,2.27)\), \(3.1415<\pi<3.142\), expansion of \(C_T\) yields a coefficient of \(e^{-u/2}\) bounded by \(.0398u^2-.385u+5.80\), including the \(3.15/T\) term. In fact the linear coefficient is \(-w/(2\pi)-1/(12\pi)\), and the constant is at most \(w^2/(2\pi)+w/(6\pi)+3.15/.65\). Prime powers contribute \(\le1.02e^{-u/2}\) for \(u\ge34\). For the integral in (3) the finite RH θ estimate bounds the integrand by \(e^{v/2}/25\) throughout \([20,u]\). Thus a candidate is \((.0398u^2-.305u+6.82)e^{-u/2}+400000u e^{-u}\). Another is the printed finite RH π bound \(u^3 e^{-u/2}/25\) for \(20\le u\le58\). The elementary bounds on π as a constant can, for instance, be checked from the alternating arctangent series in Machin's formula. The given right endpoint of finite RH covers \(e^{58}\).

Define q as the minimum of available candidates, and \(q_+(u)=0\) in the range where \(\pi(e^u)<\operatorname{li}(e^u)\) is used (here \(36\le u\le39.47\)), \(q_+(u)=q(u)\) otherwise. Substituting into the normalized gap gives (2); each upper endpoint being squared bounds a nonnegative quantity. On a cell, each *individually* decreasing q bound can be used if valid on that whole cell. The minimum need not be globally monotone across changes in domains.

## Entire-domain polynomial certificates

Put \(S(u)=\sum_{k=0}^{20} k!/u^k,\ f(u)=\operatorname{li}(e^u)\). At the anchor V=24, \(|f(V)-e^VS(V)/V|<10\): in the logarithmic variable the principal value is \(\kappa+\log V+\sum_{i\ge1}V^i/(i i!)\), where \(\kappa=\int_{-\infty}^{-1} e^t/t\,dt+\int_{-1}^0(e^t-1)/t\,dt\) has absolute value at most 1. The exact series check uses the first 199 terms and a geometric tail, and bounds the distance from \(e^VS(V)/V\), before adding \(\kappa+\log V\), by 3. Differentiation gives
\[
 f(u)-e^uS(u)/u=f(V)-e^VS(V)/V+21!\int_V^u e^v/v^{22}\,dv.
\]
For \(u\ge V\) the integral is nonnegative and at most \(12e^u/u^{22}\) by its log slope ≥1/12. The upper normalized residual is \(r(u)=12\cdot21!/u^{21}+10u e^{-u}\), the lower at least \(-10u e^{-u}\).

Write \(t=r+q_+\). Expand \((L/(L-1))S(L-1)=\sum_{k=0}^{20} k!L^{-k}(1-1/L)^{-k-1}\); dropping all terms above degree 20 in \(1/L\) gives a lower bound with coefficients \(B_j=\sum_{k=0}^j\binom{j}{k}k!\). The coefficients \(C_j\) of \(S(L)^2\) are the truncated factorial convolution. The first four cancel and the next 17 differences are \(Z_i\). The penalty to subtract from \(\sum_{i=0}^{16}Z_i/L^i\) is bounded by
\[
 P_R(L)=\sum_{j=21}^{40} C_j/L^{j-4}
 +L^4\{2S(L)t(L)+t(L)^2+10L e^{-(L-1)}+[L/(L-1)]q(L-1)\}.
\tag{4}
\]
certify.py checks on every closed cell \([l,h]\) that the lower bound for \(\sum_i(Z_i-p_i)L^{-i}\) exceeds an upper bound on (4). Positive coefficients use h, negative ones l. In (4) bound the factor \(L^4\) by \(h^4\) and all decreasing factors at l (use shifted cells for q at L−1). The split at 39.47 and the entire domain checks on q candidates implement the one-sided region exactly. This is not a sampled inequality.

For the analytic tail L≥J, force q_a regardless of which candidate was used in the cells. For j the first positive residual coefficient, all other residuals are nonnegative. Each constituent of \(L^jP_R(L)\) decreases using this forced penalty: exponential terms and their shifts satisfy \(j+4+m\le c(J-1)\) for each \((b,m,c)\), anchors satisfy \(j+5\le J-1\), and all remaining powers and multiplying factors decrease. The code compares the forced penalty at J with \(Z_j-p_j\) after scaling. Strict rational slack proves every strict profile including all joins.

Any fixed number m of \(Z\) coefficients can be retained on an effectively determined ray: use truncation \(N\ge m+4\), anchor \(2(N+2)\), and the same tail tests. For \(j\ge4\), the full convolution coefficient divided by \(j!\) is \(\le2+2/j+2(j-3)/(j(j-1))\le8/3\), using the binomial coefficients at the two edges and then \(\binom{j}{2}\) for the interior. The corresponding \(B_j/j!\ge65/24\). Thus the first omitted coefficient is positive. After multiplying the penalty by \(L^m\) it tends to zero, and the monotonicity tests eventually hold. One may take an integer search at J, replacing exponential terms in its check by \(r!/[c(J-1)]^r\) with \(r>m+8\) (positive exponential series); this also ensures effective termination even if fixed-scale exp rounding would be too coarse.

## Bottlenecks and unsuccessful improvements

Adaptive CH plus a finite-RH integral replaced an attempted direct π bound (which initially even used one log too few in the normalized finite-RH π error); this improved whole-ray margins from the log-42 vicinity to below log 37 after correction. The favorable earlier signed interval cannot be extended blindly because its upper π error becomes two-sided. Further near-onset improvements need localized π lower error at \(x/e\), or exact quantitative prime-count data on a large range. The original finite sign data alone do not supply a uniform positive normalized margin there. At intermediate L≈184–191 the CH floor a followed by the high-zero density estimate limits the available slack when multiplied by \(L^6\); attempts from L=48 or 49 at third coefficients 6, 25, 30 did not certify even with continuous layering. The bounded stronger profiles are kept separately. Near log 780 deep expansions similarly exhaust slack; at 840, finer cells gave success where the coarse cells did not. These failures are not arithmetic counterexamples. D01 is unavailable at the early onsets and smaller errors already follow from B0 wherever D01 applies.

