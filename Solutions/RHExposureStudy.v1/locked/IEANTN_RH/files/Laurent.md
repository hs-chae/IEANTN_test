# Recover the Laurent-sign input without coefficient sampling

Written proof of the exact target ZetaLogDerivValues.v1.logDeriv_laurent_alternating,
given the usual Hadamard/logarithmic-derivative and low-count inputs.
This particular recovery is unconditional; RH remains a hypothesis of
the PNT/weighted/direct-interval results that consume it. The Lean
providers for the full Laurent identity are not yet composed.

Compare Chirre–Helfgott arXiv:2512.15709v1 Appendix A, Lemma A.7.
There the proof uses a rectangle boundary bound checked in FLINT/Arb,
then a Cauchy bound and computations of the first coefficients. Here
the nearest trivial zero supplies a termwise margin for every coefficient.

## A summable spectral budget from existing RvM bounds

Use the existing ZeroCount.v1.rvm_error_small and rvm_error_bound
inputs (CH2 Lemma B.1). Let \(a=2\pi\), \(M(t)=(t/a)
(\log(t/a)-1)+7/8\); \(N(t)\) counts positive ordinates including \(t\)
with multiplicity. At \(a\), \(M=-1/8\) and \(|N-M|<1\), so \(N(a)=0\)
by integrality. The conjugate side is the same. There are no
nontrivial real zeros in \(0<\Re s<1\): for real \(0<s<1\), the
alternating Dirichlet eta series is positive by pairing and
\(\zeta(s)=\eta(s)/(1-2^{1-s})<0\). The Hadamard contract already
sums over the open critical strip. Thus its ordinates satisfy \(|\gamma|>a\).
For the analytic disc below one also uses the standard boundary exclusion
of zeta zeros on \(\Re s=0,1\) and classification of trivial zeros.

Partial summation using \(N(a)=0\), \(N(T)/T^2\to0\) gives
\(\sum_\rho\gamma^{-2}=4\int_a^\infty N(t)t^{-3}dt\).
Use \(M(t)+1\) through 280 and \(M(t)+1+(1+\log(t)/5)\) afterwards.
The term \((t/a)(\log(t/a)-1)\) integrates to zero, and the \(7/8+1\)
term gives \((15/4)/a^2\). The extra tail is
\((2/280^2)(1+(\log 280)/5+1/10)\). Thus
\[
 \sum_{\rho} |1-\rho|^{-2}
 \le \sum_\rho \gamma^{-2}
 \le \frac{15}{4(2\pi)^2}
      +\frac{2}{280^2}\left(1+\frac{\log280}{5}+\frac1{10}\right)
 <\frac1{10},
\]
using \(\pi>3.14\) and \(\log280<6\).
This supplies summability; no formal tsum junk value can enter.
LooseLowSum.count_zero verifies the low-count ingredient in Lean,
using the actual inherited finite-support proof.

## Recover the analytic coefficient contract

Let \(z=s-1,\ |z|<3,\ z\ne0\). From the paired Hadamard
logarithmic derivative for \(\zeta\) (ZetaHadamard.v1's exact input),
subtract the regularized limit at \(s=1\). This limit is \(-\gamma\)
for \(-\zeta'/\zeta(s)-1/(s-1)\), by the usual Laurent expansion
\(\zeta(1+z)=1/z+\gamma+O(z)\).
The digamma difference
\(\tfrac12\psi_{\Gamma}(3/2+z/2)-\tfrac12\psi_{\Gamma}(3/2)\)
is given by the convergent Gauss series at those points,
both in the right half-plane (the actual closed GammaAsymptotics.v2 proof
uses the same series). It follows that
\[
-\frac{\zeta'}{\zeta}(1+z)-\frac1z =
-\gamma+\sum_{k\ge0}\frac{z}{(2k+3)(2k+3+z)}
        +\sum_\rho\frac{z}{(1-\rho)(1-\rho+z)}.
\]
The use at 1 concerns the **pole-subtracted** expression; absolute
local-uniform convergence justifies the limit. No junk pole value is used.

Expand the rational terms geometrically. The iterated series commute
absolutely: on \(|z|\le r<3\), total absolute mass is at most
\(r(1-r/3)^{-1}[\sum (2k+3)^{-2}+\sum |1-\rho|^{-2}]\).
Thus the sign convention is \((-1)^{n+1}a_n\), with \(a_0=\gamma\) and
\[
 a_n=\sum_{k\ge0}\frac1{(2k+3)^{n+1}}
       +\sum_\rho\frac1{(1-\rho)^{n+1}}\quad(n\ge1).
\]
The second sum is real by conjugation. For \(n\ge1\),
\[
 a_n\ge 3^{-n-1}-(1/10)(2\pi)^{1-n}
 \ge (1/10)\,3^{-n-1}>0,
\]
since \(2\pi>3\); \(a_0=\gamma>0\).
This proves the entire coefficient sign contract with exact radius
restriction and no numerical sign sampling. The mathematical use of the
input no longer requires a separate Arb verification of the coefficients;
it still requires the paired Hadamard identity, standard normalization,
and the RvM bounds. The full identity/sign replacement has **not** been
supplied to the checked PNTReduced.lean statement.
