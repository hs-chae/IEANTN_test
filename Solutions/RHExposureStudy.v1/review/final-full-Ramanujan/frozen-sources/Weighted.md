# Weighted errors by retaining the integrated spectral intermediate

All results assume the specified RH; endpoints are inclusive. Write
\(L=\log x\), \(m=\psi(x)-x\), \(a=1/(8\pi)\), and
\(P(x)=\prod_{p\le x}(1-1/p)^{-1}\).
Put
\[
 M_1=\sum_{p\le x}\frac{\log p}{p}-\log x-E,\quad
 M_2=\sum_{p\le x}\frac1p-\log\log x-B,\quad
 M_P=\log\frac{P(x)}{e^\gamma\log x},
\]
where the Lee–Nosal Cor. 1.3 constants are
\(E=-\gamma-\sum_{p,k\ge2}(\log p)/p^k\) and
\(B=\gamma+\sum_p(\log(1-1/p)+1/p)\), with \(\gamma\) Euler's constant.
For all real \(x\ge e^{34}\)
one has the signed bands
\[
\begin{aligned}
 .75/\sqrt x&\le M_1-m/x\le1.29/\sqrt x,\\
 .68/(\sqrt xL)&\le M_P-m/(xL)\le1.39/(\sqrt xL),\\
 .68/(\sqrt xL)&\le M_2-m/(xL)\le1.40/(\sqrt xL).
\end{aligned}
\]
The stronger bands appear below. Already these imply
\(\lvert M_1\rvert\le1.04\,aL^2/\sqrt x\),
\(\lvert M_2\rvert\le1.04\,aL/\sqrt x\), and
\(\max(\lvert P/(e^\gamma L)-1\rvert,\lvert e^\gamma L/P-1\rvert)
\le1.05\,aL/\sqrt x\), compared with the factor 3 in Lee–Nosal
Cor. 1.3 on the common ray. Their earlier onsets are not improved.
Lamzouri arXiv:1410.3777v2 Lemma 2.3 and Cor. 2.2 already identify
the square-induced shift asymptotically.

## Proof with only the primitive estimate

Grenié–Molteni arXiv:1312.4465 Thm 1.1 for \(K=\mathbf Q\) gives
\[
 B_0(t)=\int_0^t(\psi(u)-u)\,du,\qquad
 |B_0(t)|\le ct^{3/2}+bt\quad(t\ge3),
 \qquad (c,b)=(.0462,1.838).
\]
Only ordinary RH is used. Let \(g_0(t)=t^{-2}\) and
\(g_1(t)=t^{-2}(1/\log t+1/(\log t)^2)\); write
\(T_i=\int_x^\infty(\psi(t)-t)g_i(t)\,dt\).
Integration by parts and \(\log t\ge L\) give
\[
 |T_0|\le5c/\sqrt x+3b/x<.232/\sqrt x,\quad
 \sqrt xL|T_1|\le c(5+7/L+4/L^2)+b x^{-1/2}(3+4/L+2/L^2)<.241 .
\]
For the second estimate,
\(-g_1'=t^{-3}(2/\log t+3/(\log t)^2+2/(\log t)^3)\).
All scalar upper bounds occur at \(x=e^{34}\).

Stieltjes partial summation gives the normalized Mangoldt sums
\(\sum_{n\le x}\Lambda(n)/n-\log x+\gamma=m/x-T_0\),
and \(\sum_{2\le n\le x}\Lambda(n)/(n\log n)-\log\log x-\gamma
=m/(xL)-T_1\). Use CH2.v1.corollary_1_2_lambda_sum at
\(T=\sqrt x\) for the first limiting constant and the classical
Mertens product for the second (the correction below is \(o(1)\)).
Measure atoms are retained in the endpoints with no half-weights.

For \(M_P\) add \(\sum_{p\le x,k\ge2,p^k>x}1/(kp^k)\),
as in Lamzouri Eq. (2.4). Let \(z=\sqrt x\).
The square contribution \(S=\tfrac12\sum_{z<p\le x}1/p^2\)
differs from \(\tfrac12\int_z^x dt/(t^2\log t)\) by at most
\[
 (a/2)\{z^{-3/2}[(7/3)\log z+8/9]+x^{-3/2}L\},
\]
from partial summation and Schoenfeld on \(\pi-\operatorname{li}\).
After scaling by \(\sqrt x L\), the error is \(<.006\).
The main integral after scaling is between \(1-2/L-1/(2\sqrt x)\)
and \(1\), by integration by parts from \(z\) and subtracting
the \(x\) tail. Thus the lower square allowance is \(>.935\).
For exponents \(k\ge3\), let \(v=x^{1/3}\). For \(p\le v\) the first
allowed exponent is \(\ge4\), tail \(<1/(2x)\) per prime; at \(p>v\)
sum at most \((2/3)\sum_{n>v}n^{-3}\le1/(3\lfloor v\rfloor^2)\).
Total \(<x^{-2/3}\) since \(v>10\), hence \(<.118\) in scaled units.
The whole positive correction is between .935 and 1.124 scaled.
For \(M_2\) add also \(\sum_{p>x,k\ge2}1/(kp^k)\le1/(2\lfloor x\rfloor)\),
by geometric series and telescoping, costing \(<.001\) scaled.

For \(M_1\) add \(\sum_{p,k\ge2,p^k>x}(\log p)/p^k\);
\(E=-\gamma-\sum_{p,k\ge2}(\log p)/p^k\).
The square term differs from \(1/z\) by at most
\[
 z^{-1}a z^{-1/2}\{(7/3)\log^2 z+(16/9)\log z+32/27\}
 <.01/z
\]
by Schoenfeld for \(\theta\) and partial summation.
Higher powers with \(p\le v\) give \(\le2\theta(v)/x\le4v/x\);
those with \(p>v\) give \(\le2\sum_{p>v}\log p/p^3\le6/v^2\)
using \(\theta(t)\le2t\) on this ray. Total after scaling by \(z\)
is \(\le10e^{-34/6}<.035\). These bounds and the tail estimates
give the displayed bands. For absolute bounds use
\(|m|\le a\sqrt x L^2\), \(\pi<22/7\) in the scalar comparison,
and \(|e^{\pm M_P}-1|\le e^{|M_P|}-1\), with
\(|M_P|<.000002\) so a factor 1.001 suffices before rounding to 1.05.

## Quantitative primorial cancellation

Schoenfeld gives \(\theta(x)>1\) on this ray. Concavity of
\(\log\log t\) for \(t>1\) gives, by subtracting its tangent at \(x\),
\[
 \log\frac{P(x)}{e^\gamma\log\theta(x)}
 \ge M_P-\frac{\theta(x)-x}{xL}
 \ge \frac{.68+.99}{\sqrt xL}.
\]
Here \(\psi-\theta\ge\theta(\sqrt x)\ge.99\sqrt x\).
For the primorial \(N=\prod_{p\le x}p\), \(P=N/\varphi(N)\)
and \(\log N=\theta(x)\). This gives a quantitative margin, not a
new Nicolas equivalence or a consequence of the package's elementary
primorial growth contract alone.

FullRH.adaptive_lambda consumes the actual CH2 weighted normalization
contract. Its pointwise remainder does not retain the primitive;
the GM input provides that intermediate. The Stieltjes proof
is written mathematics, not a formal replay of GM.

## Stronger tail route: integrate the spectral terms before the modulus

The primitive route above is robust even when only a bound on \(B_0\) is
available. Keeping its actual signed spectral decomposition strengthens
the same statements. With the same definitions and \(x\ge e^{34}\):
\[
\begin{array}{ll}
 .942 \le \sqrt x(M_1-m/x)\le1.094,\\
 .886 \le \sqrt x L(M_P-m/(xL))\le1.173,\\
 .886 \le \sqrt x L(M_2-m/(xL))\le1.174.
\end{array}
\]
In particular the quantitative primorial lower margin \(1.67\) can be
replaced by \(1.876\) on the same ray, using just the earlier .99 bound on
\(\theta(\sqrt x)/\sqrt x\). This is not an asymptotic O-symbol or a claim
that the product normalized by \(\log x\) is always positive.

To prove this, use Grenié–Molteni arXiv:1312.4465 Eq. (1.3a) and Lemma 3.3
at \(K=\mathbf Q\). Their unweighted primitive has zero term
\(-\sum_\rho t^{\rho+1}/[\rho(\rho+1)]\), real terms
\(-t\log(2\pi)+r'\), and trivial-zero term
\(-\sum_{k\ge1}t^{1-2k}/[2k(2k-1)]\). For any \(s\ge0,\ x\ge3\), integrate
the primitive by parts (weight \(t^{-2-s}\)) on \([x,\infty)\):
\[
 I_s(x)=\int_x^\infty m(t)t^{-2-s}\,dt
 =-\sum_\rho\frac{x^{\rho-1-s}}{\rho(1+s-\rho)}
   -\frac{\log(2\pi)}{(1+s)x^{1+s}}+
       \int_x^\infty\frac{-\log(1-t^{-2})}{2t^{2+s}}\,dt.
\]
The constant \(r'\) cancels. The signed boundary term and integral
combine into the displayed resolvent. For a single zero this is just
\(\int t^{\rho-2-s}\), but absolute interchange is justified by first
working with the absolutely convergent primitive, whose terms are
dominated after integration by a constant times \(1/|\rho|^2\).
The prime-power half-weight issue is absent in an ordinary \(dt\) integral.

On RH \(1-\rho=\bar\rho\), whence \( |\rho(1+s-\rho)|\ge|\rho|^2\).
The **analytic** inverse-square mass is
\(\sum_\rho |\rho|^{-2}=2+\gamma-\log(4\pi)<.047\).
Indeed subtract the Hadamard logarithmic-derivative identities
of \(\xi\) at 1 and 0: their difference is the absolutely convergent
\(\sum_\rho1/[\rho(1-\rho)]\). The functional equation doubles
\(\xi'/\xi(1)=1+\gamma/2-\log(4\pi)/2\), found from the Laurent
expansion at 1 and \(\Gamma'/\Gamma(1/2)=-\gamma-2\log2\).
The paired form is the same cancellation as the repository's
ZetaHadamard.v1.logDeriv_partial_fractions, here on the completed
function at two off-zero points. This calculation needs no list of
numerical ordinates. The scalar bound follows from \(\gamma<.578\)
and \(\log(4\pi)>2.531\). The final trivial term in \(I_s\) is
nonnegative and smaller than the absolute \(\log(2\pi)\) contribution:
use \(-\log(1-t^{-2})/2\le(9/16)t^{-2}\) for \(t\ge3\).
Thus
\[
 |I_s(x)|\le .047 x^{-1/2-s}+
             \frac{2x^{-1-s}}{1+s}.
\]
For the log-weight kernel use
\(1/\log t+1/\log^2 t=\int_0^\infty(1+s)t^{-s}ds\).
Exchange with the actual \(m(t)\) integral by absolute integrability
(Schoenfeld's pointwise estimate). This gives \(\sqrt x L|T_1|
\le .047(1+1/L)+2/\sqrt x<.049\), and
\(\sqrt x|T_0|\le .047+2/\sqrt x<.048\).
Combining with the same prime-power bounds proves the sharper bands.
The exact tail route recovers the correlation discarded if one takes
absolute values separately before integration by parts. It is a
written analytic derivation, not a new Lean proof of the explicit formula.

For a concrete signed consequence: on a Büthe Table 1 row entirely
above \(e^{34}\) with upper deficit \(M\le .88\), the Mertens product
satisfies
\[
 \log(P(x)/(e^\gamma\log x))\ge .006/(\sqrt x L)
\]
throughout that row (or its intersection with the admitted range).
For example, \(10^{16}\le x\le2\cdot10^{16}\) has \(M=.74\),
so there the lower constant can be .146. This is a deduction from
a published signed \(\psi\) computation and RH, not a new native Mertens
sieve or a claim of full finite-interval sign coverage.

### Checked downstream consumer and adaptive endpoint

WeightedConsumer.log_primorial_margin checks the \(\log\log\) tangent
cancellation using two applications of \(\log u\le u-1\), establishes
\(\theta(x)>1\), and consumes the actual lower \(.99\sqrt x\)
prime-power relay of ThetaSigned. The exact \(.886\) weighted band
and positivity of \(P\) are explicit inputs; the Lean theorem does
not claim to derive that band from the integrated explicit formula.

Alternatively, transferring the adaptive endpoint of PNT.md through
the strongest written bands gives
\[
 |M_1|\le \frac{A(L)+1.094}{\sqrt x},\quad
 |M_2|\le\frac{A(L)+1.174}{\sqrt xL},\quad
 |M_P|\le\frac{A(L)+1.173}{\sqrt xL}.
\]
For a provider set without the separate numerical reciprocal-ordinate
bound, replace \(A(L)\) by the checked \(A(L)+.821\) from PNTClosed.
The endpoint provider changes the absolute error envelope, not the
positive endpoint-subtracted bands.
