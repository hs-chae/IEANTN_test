# RH reciprocal-zeta transfer through the zero-count intermediate

Status: complete written continuation derivation, independently mathematically reviewed by Root and Ram. The actual scalar, finite smoothing, uniform strip and downstream conditional consumers have a seven-module kernel-checked package. The full complex-analytic and zero-Stieltjes-to-reciprocal Lean chain remains open; this is not a completed RH-to-M Lean theorem. No new numerical zero list or quadrature input is assumed. This is not source-first PV.

## Objective and actual source consumer

Simonič, arXiv:2201.10771v1, Theorem5(43), PDFp17, exposes the actual coefficient

    I(T)=integral_0^T |zeta(.98+it)|^(-1) dt.

The proof of Theorem2 uses T=26000000 and (50)/(51), PDFp18, to bound I by5.95e14. The low11520 segment is an ordinary Romberg computation, explicitly described in Remark3, while the high segment is bounded with a very loose pointwise analytic envelope. The new route seeks an entirely analytic whole-compact upper I<4.68e9. Actual finite scalar constants and actual conditional M(x)/m(x) consumers are now kernel checked. The complete written analytic chain passed independent mathematical review; the corresponding complex-analytic Lean obligations remain open.

## 1. Precise zero count and the paired product

Let N(u) count positive imaginary ordinates of the actual nontrivial zeros, with multiplicity, ordinarily inclusive at u. Use the current canonical ZeroCount.v1 predicate

    m(u)=u/(2pi)*(log(u/(2pi))-1)+7/8,
    |N(u)-m(u)| <= .2 log u+2   (u>=1).

RH places these zeros at1/2+iγ. Real nontrivial zeros are absent by the already compiled actual IEANTN theorem CH2ZetaReal.riemannZeta_ne_zero_Ico, Solutions/CH2.v1/ZetaReal01.lean:182, for every real0<=s<1. Its fresh source-built object is in the campaign shared36-module bank; this fact need not be introduced as a new literature predicate. It is not a simple-zero assumption. Set E=N-m. On0<u<1, monotonicity, the u=1 bound and integrality imply N(u)<=N(1)<=2; m(u) lies between m(1)>0 and7/8. Therefore the convenient global bound

    |E(u)| <= R(u)=.2 log(u+2)+3  (u>0)

is valid. The extra1 is a deliberate conservative allowance, not a new numerical hypothesis.

For a=.48,b=.55 define

    k(v)=log((v*v+b*b)/(v*v+a*a)),
    f_t(u)=k(t-u)+k(t+u),
    Q(t)=sum_{γ>0} multiplicity(γ)*f_t(γ).

This series converges absolutely from N(u)=O(u logu), since k(v)=O(v^-2). The canonical existing ZetaHadamard.v1.logDeriv_partial_fractions is enough to recover the paired modulus identity, without adding a new opaque Hadamard-product predicate. It states the actual HasSum of multiplicity-weighted[1/(s−rho)−1/(w−rho)] as the difference of zeta logarithmic derivatives plus half the digamma(s/2+1) difference plus1/(s−1)−1/(w−1). Take w=1/2, legitimate by RealZeroAdapter.at_half. Since

    xi_prime(s)/xi(s)=zeta_prime(s)/zeta(s)+digamma(s/2+1)/2+1/(s−1)−log(pi)/2,

and the exact functional equation xi(1−s)=xi(s) gives xi_prime(1/2)=0, the HasSum value is precisely xi_prime(s)/xi(s). Under RH, grouping the positive and negative ordinate terms yields2(s−1/2)/[(s−1/2)^2+gamma^2]. This regrouping is legitimate for the absolutely convergent subtracted family. On a compact horizontal interval strictly right of1/2, the paired family is uniformly O(1/gamma²), and RvM proves the dominating series summable. Integrating its real part horizontally gives exactly

    log|xi(1.05+it)/xi(.98+it)|=.5 Q(t).

No generator is substituted for an actual zeta function. The canonical subtracted identity fixes the logarithmic derivative after normalization at the center; hence there is no unaccounted exponential factor. At t=0 and a contour passing through sigma=1, prove the identity first for t>0 and pass to the continuous completed-xi limit, rather than substituting a totalized pole value of zeta into the product formula at s=1. The primary attribution carried by the existing node is Montgomery–Vaughan2007 Corollary10.14; The original primary textbook has now been retrieved from author Vaughan's PSU site and checked: Corollary10.14 Eq10.28/29, printedp349/chapterPDFp24; the exact shifted-digamma restatement is printedp350. The exact multiplicity sentence is printedp349. DLMF25.4.E3/E4 independently provide the exact functional equation and completed-xi normalization.

## 2. Stieltjes evaluation and the7/8 boundary

Ordinary endpoint counts and absolute convergence give

    Q(t) = - integral_0^infty N(u) f_t'(u) du
         = (7/4)k(t)
           + (1/(2pi))*integral_R k(t-u) log(|u|/(2pi)) du
           - integral_0^infty E(u) f_t'(u) du.

The boundary at0 is m(0)=7/8 and f_t(0)=2k(t), hence the displayed7/4. The boundary at infinity vanishes. This coefficient must not be dropped or doubled by switching between positive and both-sign counts.

The real Poisson integral for log|u|, equivalently integration first in v of the Poisson kernel, gives

    (1/(2pi))*integral_R k(t-u) log(|u|/(2pi)) du
      = integral_a^b log(sqrt(t*t+v*v)/(2pi)) dv =: J(t).

For completeness, the needed Poisson formula is an elementary contour calculation, so it need not be hidden in an unnamed analytic premise. For eta>0 integrate

    Log(z+i*eta)*v/[(z−t)^2+v^2]

over the upper semicircle of radiusR. The branch is analytic above the real axis because z+i*eta stays in the open upper half-plane. Only z=t+i*v is a pole. Its residue is Log(t+i*(v+eta))/(2i), so the real-axis integral tends to pi*Log(t+i*(v+eta)); the arc is O(logR/R) and tends to zero. Taking real parts gives

    (1/pi) integral_R v*log(sqrt(u²+eta²))/[(u−t)²+v²]du
      =log(sqrt(t²+(v+eta)²)).

Let eta decrease to zero. On a bounded neighborhood ofu=0, absolute values are dominated by a constant plus|log|u||; on the tails they are bounded by a constant timeslog(2+|u|)/u² after multiplying by the kernel. Dominated convergence therefore gives the claimed log|u| formula with its exact1/pi factor. Finally k(y)=integral_a^b 2v/(y²+v²)dv and absolute Fubini givesJ, including the subtraction oflog(2pi). This explicitly supplies the normalization, singular-point treatment and interchange justification.

For fixed0<=t<=T=26000000 take U=2*(T+1)=52000002. The kernel is even, positive and decreasing on[0,infty). Its two translates satisfy

    integral_0^infty |f_t'(u)| du <= 2k(0),
    k(0)=2log(55/48).

For u>U, u-t>=u/2 and u+t>=u; with d=b²-a²,

    |f_t'(u)| <= 2d*((u-t)^(-3)+(u+t)^(-3)) <=18d/u³.

Since log((u+2)/(U+2)) <= (u-U)/(U+2), splitting the R bound at U proves

    .5*|integral E f_t'|
      <= R(U)k(0) + .9*d/[U*(U+2)].

Indeed integral_U^infty (u-U)/u³ du=1/(2U). Consequently

    .5 Q(t) <= .5 J(t) + [R(U)+7/8]k(0) + .9*d/[U*(U+2)].

This is a whole-compact theorem; there is no sample-based assertion about the zeta function.

## 3. Gamma cancellation with a uniform elementary remainder

Use xi(s)=G(s)zeta(s),

    G(s)=.5*s*(s-1)*pi^(-s/2)*Gamma(s/2).

DLMF5.9.13, valid for Re z>0, is the exact identity

    digamma(z)-log(z)
      = integral_0^infty [1/v-1/(1-exp(-v))]*exp(-vz) dv.

For v>0, the absolute value of the real square-bracket factor is at most1: the two needed scalar inequalities follow from1-exp(-v)<v and exp(v)-1>v. Thus

    |digamma(z)-log(z)| <= integral_0^infty exp(-v Re z)dv =1/Re z.

Integrating the real part along σ from.98 to1.05 gives

    log|Gamma((.98+it)/2)/Gamma((1.05+it)/2)|
      <= -.5*integral_.98^1.05 log(sqrt(σ²+t²)/2)dσ +log(1.05/.98).

The polynomial factor obeys |(.98+it)(-.02+it)| <= |(1.05+it)(.05+it)| for all realt. The pi factor adds .5*(1.05-.98)logpi. Since v=σ-.5 has v²<σ², the Poisson main cancels favorably:

    log|G(.98+it)/G(1.05+it)| +.5J(t) <=log(15/14).

This also holds at t=0; a direct endpoint ratio or continuity avoids integrating through the pole of zeta at σ=1.

## 4. A fully analytic uniform reciprocal bound

On Re s=1.05, absolute convergence of the actual Euler product gives

    |1/zeta(1.05+it)| <= zeta(1.05)/zeta(2.10) <=21.

Combining the preceding identities yields, for all0<=t<=26000000,

    |1/zeta(.98+it)|
      <= (45/2)*exp( [R(U)+7/8]*2log(55/48)+.9*d/[U*(U+2)] ) <180.

The final strict scalar inequality has generous exact slack: log(52000004)<17.8, so R(U)<6.56;2log(55/48)<.273; the final tail is below1e-12. The exponent is below2.03, which is below3log2. Hence exp(exponent)<8 and (45/2)*8=180. These scalar facts are proved in ReciprocalScalars.compact_budget_lt_180 using elementary exponential Taylor inequalities and Mathlib's explicit exp(1)/log(2) bounds, without Arb or native evaluation.

The immediate numerical source consumer is therefore

    I(26000000) < 4680000000.

A 128-bit directed Arb scalar re-evaluation of the unrounded formula gives a safe uniform expression170.032640329..., but that sharper decimal is not needed or promoted to a kernel fact. This route eliminates the original Romberg leaf rather than certifying it.

## 5. Final M(x) conversion and a genuine onset issue

It is invalid to replace1.94e14 by the new coefficient in Simonič's all-x Theorem2 while keeping the old555.71 coefficient by fiat. For λ=2, Theorem5(44) only starts near10^711; the original below-onset proof used the enormous second coefficient and no longer applies after lowering it.

One valid route to a global Pareto result is to use a larger λ (for example10000), recompute the exact first coefficient using the actual ε0 of(42), and join the finite mathematical interval below(44) using |M(x)|<=x. The leading coefficient is then near3700, and a safe4000 is a candidate, while the second coefficient is below1.53e9. These constants are not accepted until their exact parameter inequalities and the all-x join are proved. Keep the original555.71 branch for the asymptotic tail where it is stronger.

A second, more ambitious route lets U depend on t. The same method gives a global polynomial reciprocal-zeta bound C(2t+constant)^epsilon with epsilon=.4log((σ1-.5)/(σ0-.5)), then redoes the Perron smoothing argument with that explicit C. This may allow substantially smaller M exponents, but it is not claimed here before full derivation and independent review.

## Verification boundary

The displayed zero-Stieltjes, Poisson and Gamma identities and the resulting reciprocal-zeta bound are a written derivation which has passed independent mathematical reviews by Root and Ram; full formal completion is still open. RvM, Hadamard, Gamma and Euler product source claims must remain exact and separately visible in any partial Lean theorem. A wrapper assuming the reciprocal inequality would not close this chain. The separate Mertens `.014` result remains fully kernel-checked at its original-five-source boundary.

## 6. A global reciprocal envelope and a substantially stronger M power

The preceding method works with general1/2<σ0<1<σ1. Put a=σ0−.5,b=σ1−.5, k0=2log(b/a), d=b²−a² and U=2(t+1). The polynomial factor in G has the uniform bound

    |s0(s0−1)|/|s1(s1−1)| <= max(1,(1−σ0)/(σ1−1))=:P0.

The Gamma argument is unchanged and contributes σ1/σ0. The same tail proof now has U>=2, so its final term is at most .9d/8. For all t>=0 the resulting analytic envelope is

    |1/zeta(σ0+it)|
      <= (1+1/(σ1−1))*P0*(σ1/σ0)
         *exp((31/8)k0+.9d/8)*(2t+4)^(k0/5).       (G)

Every factor and domain is explicit. RH is ordinary RH; this does not use GRH, simple zeros, ζ′ at zeros or a reciprocal-zero numerical table.

For σ0=.75,σ1=1.05, P0=5 and the first prefactor is147. Exact scalar bounds k0<1.58, exp(6.2)<500 and6^.32<2 give

    |1/zeta(.75+it)| <=150000                  (|t|<=1),
    |1/zeta(.75+it)| <=150000 |t|^.32         (|t|>=1).   (H)

The exponent k0/5 is below.316, and.32 is a conservative rational replacement. The exact same finite/nonfinite split covers t=1. `ReciprocalScalars.global_budget_le` kernel checks the all-t scalar reduction (actual analytic identity(G) still needs formal closure).

Here is a complete Perron smoothing deduction at the level of written mathematics. Let

    M(x)=sum_{1<=n<=x}mu(n),
    Mc(x)=sum_{1<=n<=x}(x−n)mu(n),
    σ=.75, ε=.32, κ=(σ+ε)/(1+ε)=107/132,
    h=x^κ, V=4x/h, x>=1.

Then1<=h<=x and V>=4. Use the exact ordinary-endpoint smoothing identity and Mellin formula Simonič(45)/(46), PDFp17. This is not an illegal evaluation of his final sigma=.98 theorem: the paper derives (45) by the elementary Mellin identity for every initial c>1, then moves the contour on RH. Here the contour move is re-established separately for sigma0=.75 as follows. For every sigma in[.75,1.05], the general envelope(G) is bounded by its sigma0=.75 envelope: b/a and b²−a² decrease with sigma; P0=max(1,(1−sigma)/.05) decreases; and1.05/sigma decreases. For1.05<=sigma<=c, the Euler bound is at most21. Thus the horizontal segments satisfy a uniform O(T^(.32−2)) bound and vanish as T tends to infinity. There are no poles crossed:1/zeta is analytic on Re s>.5 on RH, including its zero at s=1, while s(s+1) has no zero in the strip. Absolute convergence of the vertical line follows from the same exponent .32<1 and the t^−2 Mellin denominator. This supplies the sigma-domain and missing horizontal-edge obligations rather than importing (45) outside a proved domain. The smoothing difference differs from hM(x) by at most h(h+1). In the vertical integral, for |t|<=V use

    |((x+h)^(s+1)−x^(s+1))/(s+1)| <=h(x+h)^σ <=h(2x)^σ.

For |t|>V use |numerator|<=2(x+h)^(σ+1), and |s(s+1)|>=t². Split the low-height integral at |t|=1 and use(H). The three pieces, divided by2pi h and counting the two height signs, are bounded by

    2^σ C/(pi σ)*x^σ,
    2^σ C/(pi ε)*x^σ V^ε,
    2^(σ+2) C/[pi(1−ε)]*x^(σ+1)/h *V^(ε−1),

where C=150000. Since σ+(1−κ)ε=κ, combine these with1+h to obtain

    |M(x)| <=[2+(2^σ C/pi)*(1/σ+4^ε/ε+4^ε/(1−ε))]*x^κ.

Use 2^σ<2,pi>3,4^ε<2 and the exact rational(σ,ε) to bound the bracket strictly below1100000. Therefore the proposed new whole-real statement is

    RH => |M(x)| <1100000*x^(107/132)  for every real x>=1.   (M)

At integer endpoints the sums include that integer; the smoothing proof explicitly uses the ordinary floor convention. There is no finite numerical scan and no below-onset gap, because V>=4 and the reciprocal envelope(H) covers all heights. The strong constant is conservative; no optimality is asserted.

This is a new written theorem with the full analytic chain independently reviewed; exact scalar and actual conditional consumer components are kernel checked. The upstream analytic Lean obligations remain open. It is not a finished RH-to-M Lean theorem. It is dramatically stronger than Simonič's displayed fixed .99-profile on a large meaningful domain, but that alone does not establish best-known status: his parameterized Theorem2 in arXiv2109.11744v2, later literature and the original unconditional finite bounds must also be compared.

Additional prospective Pareto points: σ0=.6,σ1=1.05 with ε=.7 gives κ=13/17; generous scalar estimates suggest C<=710000000 and |M(x)|<=8000000000*x^(13/17). With σ1=1.01,ε=2/3, κ=19/25 and a candidate constant9e10. These prospective constants have not yet passed the exact scalar and independent review gates and are not accepted results merely because the general mechanism is the same.


## 7. A distinct weighted-Mobius consumer and matched comparisons

Let m(x)=sum_{1<=n<=x}mu(n)/n; this is not the first-Mertens prime sum A(x). Simonič2201.10771v1, proof of Theorem2, PDFp18 (the displayed equation immediately after(51)), states under RH for Re s>1/2:

    |sum_{n<=x}mu(n)/n^s−1/zeta(s)|
      <=|M(x)|/x^Re(s)+|s| integral_x^infty |M(u)|/u^(1+Re(s))du.

For s=1 the reciprocal zeta value is zero, via its removable continuation. Applying the proposed bound(M) with kappa=107/132<1 gives

    |m(x)| <1100000*(1+1/(1−107/132))*x^(107/132−1)
           =6908000*x^(−25/132), every realx>=1.

The improper integral converges absolutely. This is a genuinely different arithmetic consumer, with the same written-analytic verification boundary as(M); it is not a new premise on m. The actual finite smoothing step was independently compiled as MobiusSmoothing.smoothing_discrepancy.

Preserve pointwise minima, including |M(x)|<=x and existing finite unconditional controls. At x=exp100 the proposed M branch gives approximately |M(x)|/x<.00654815 and the weighted branch gives |m(x)|<.0411224. Stronger checked unconditional functions already win there, so this is not an improvement point. At x=exp200 the new normalized M function is3.898020585e-11 and is strictly smaller than every eligible function in the explicit checked catalog. Simonič2022's .99 function is vastly larger at this point (and is legitimately all-x); his 2021 Table1 power bounds have double-exponential onsets and cannot be used here. Its stronger subpower full function eventually beats every fixed-power candidate, so no asymptotic frontier replacement is claimed. The exact full-function source catalog is MATHEMATICAL_FRONTIER.json; 256-bit directed formula evaluations and the kernel whole-ray comparisons are preserved separately. Native Arb formula evaluation is not source-first PV and does not close the actual M analytic proof.


The double-exponential notation in the2021 source must also be translated quantitatively: x>=10^(10^4.487) means logx>about70600, not an unavailable bound at every imaginable logarithmic argument. The full subpower function, after division byx and writingL=logx, is

    .6*L*exp(-L/2+5.2251*L/log(L/2+log(3e/2))).

It is therefore essential to keep this branch. Its eventual crossing with the proposed .810606... power occurs at L of order4e7, not at an unexplained infinite cutoff. Directed formula evaluations are recorded separately; no universal dominance or best-known claim follows from the new fixed power.
