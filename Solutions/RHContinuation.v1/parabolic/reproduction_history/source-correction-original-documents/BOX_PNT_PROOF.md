# One logarithmic box gives a stronger pointwise RH envelope

New continuation written mathematics. The exact rational moment certificates
are accepted; the analytic Fourier/zero-density proof below is written and its
Lean interface remains explicit in PsiSmoothing.lean. This is not a complete
analytic Lean formalization or source-first program verification.

For every realx>=exp35, under RH and the same classical integrated explicit
formula and positive-ordinate zero-count theorem used by frozenB5, put
L=logx andv=L/2-logL. Then

    |psi(x)-x| <=sqrt(x)*Bbox(L),
    Bbox(L)=[v^2+1.402v+1.5+L]/(2*pi)+.14.

The new function is strictly smaller than the frozen B5 function by more than
.5 at everyL>=35. Both have leading termL²/(8*pi); this is a useful uniform
lower-order improvement, not an improvement of the leading coefficient.
The applicable finite Büthe estimates must remain in the pointwise minimum.

## Why a box is legitimate here

LetU be uniform on[-1,1], δ=L/(2*pi*sqrtx), and average
psi(x*exp(sδ+δU)) for s=-1 and+1. Monotonicity of actual right-continuous
psi bracketspsi(x), including at prime powers. The normalized Fourier kernel is

    phi(y)=sin(y)/y, phi(0)=1.

The exact zero multiplier is exp(s*rho*δ)*phi(δ*(gamma-i/2)) underRH.
The box has only1/y decay, so its absolute Fourier mass diverges and it is
unsuitable for the direct prime-count window in QUARTIC_PROOF.md. Here the
extra factor1/rho in the explicit formula makes the smoothed zero sum
absolutely summable. Thus a rougher window can give a better pointwise bound
while the flatter quartic is better suited to the different count observable.

The averaging is justified by integration by parts againstPsi1, whose zero
series converges locally uniformly absolutely. The log-box's finite endpoint
jumps are included. The resulting averaged zero series has1/gamma² decay;
no unjustified pointwise differentiation or conditional zero summation occurs.

## Actual absolute Mellin moments

For0<s<1,

    int_0^infty phi(y)y^(s-1)dy
      =Gamma(s)*cos(pi*s/2)/(1-s).

Subtract1/s and expand at0. The signed regularized moments are

    J0_signed=1-gamma_E,
    J1_signed=((1-gamma_E)^2+1-pi²/12)/2.

The absolute moments add twice the negative parts:

    J0=J0_signed+2 int_2^infty max(0,-siny)/y² dy,
    J1=J1_signed+2 int_2^infty max(0,-siny)*logy/y² dy.

There is no omitted negative contribution below2, since siny>=0 on[0,2].
For the negative-part integrand the total variation on[2,infty) is at most
`int_2^infty(1/y²+2/y³)dy=.75`.
For its log-weight the variation is bounded by

    int_2^infty [logy/y²+(1+2logy)/y³]dy <1.3.

`box_quadrature.py` covers[2,256] with width.002 (128,000 cells overall),
exact256-bit dyadic Taylor/rotation enclosures, and midpoint variation errors
(h/2)*.75 and(h/2)*1.3. At each1000-cell boundary it resets the enclosing
sine/cosine values using Taylor on a dyadically reduced argument followed by
exact angle doubling. This avoids long-interval rotation dependency inflation.
The tail upper bounds are1/H and(logH+1)/H, respectively.
Euler's constant uses exact harmonic/log enclosures at1024.
The accepted upper expressions are

    J0 <.699972014 <.701,
    J1 <.746162784 <.75.

The two earlier naive long-rotation attempts rejected their gates; their exact
sources and failure notes are retained. No failed quadrature was promoted.

## Real-axis zero density and the imaginary displacement

LetA=12. The count theorem givesN(A)=0, |R(t)|<=.28logt for t>=A,
andM(t)=t/(2*pi)log(t/(2*pi*e))+7/8. For the real-axis sum

    S=sum_rho |phi(δ*gamma)|/|gamma|,

Stieltjes integration by parts gives the density main integral
`[v²+2J0*v+2J1-log(A/(2*pi))²]/(2*pi)` plus the removed near-zero
regularization error. The latter is<1e-10, since|phi(y)-1|<=y²/6.
The remaining constant boundary/variation terms are bounded by

    2M(A)/A +.56*(logA+1)/A
      -log(A/(2*pi))²/(2*pi) <.130.

The derivative discrepancy is at most

    .56*δ*[log(1/δ)*H0+H1],
    H0=int_0^infty |phi'(y)|/y dy <1.3,
    H1=int_0^infty |phi'(y)|log^+(y)/y dy <1.2.

For y<=2 use|phi'|<=y/3, obtained from the second moment of uniformU.
For y>=2 use|phi'|<=1/y+1/y². Elementary power/log integration proves
bothH bounds. This contribution is<.000003 onL>=35.

For |z-y|<=δ/2 in the imaginary direction, the integral representation gives
|phi'(z)|<=exp(δ/2)/2. Its sine quotient also gives
|phi'(z)|<=exp(δ/2)*(1/|y|+1/y²), hence the unified bound

    |phi'(y+it)| <= exp(δ/2)/2 *min(1,3/|y|).

Integrating the imaginary displacement and summing costs at most

    δ/4*exp(δ/2)*sum_rho min(1,3/(δ*|gamma|))/|gamma|.

WithT=3/δ, the same count theorem implies

    sum_{|gamma|<=T}1/|gamma|
      <=log²(T/(2*pi))/(2*pi)+.131,
    T*sum_{|gamma|>T}|gamma|^-2
      <=[log(T/(2*pi))+1]/pi+(1.12logT+.28)/T.

Thus the clipped sum is<L² forL>=35, and the imaginary displacement costs
<.000046. The external factor exp(s*δ/2) costs<.000181 using the same
L² majorant. Therefore the actual complex zero packet in
PsiSmoothing.zeroAverage is bounded, after division bysqrtx, by

    [v²+1.402v+1.5]/(2*pi)+.131.

All constants include both signs and zero multiplicities. No individual zero
list, spacing assumption, zero table or unverified reciprocal-zero numerical
cap has been supplied.

## Main and trivial terms; whole domain

Symmetry andE(U)=0 give main-average error<=xδexp(2δ).
Its normalized value isL/(2*pi) plus<.001 onL>=35.
For t in the support, the trivial term is
b(t)=-log(1-t^-2)/2; t>=xexp(-2δ)>exp34.
Consequently0<=average(b)<log(2*pi)<1.9, and
|average(b)-log(2*pi)|/sqrtx<.001.

The zero, main and trivial budgets sum to .133, strictly less than the retained
.14 allowance. The two monotone averages therefore prove the actualpsi
inequality for every realx>=exp35. No integer-only or sampled extension is used.

Sincev increases andv(35)>13.5,

    B5(L)-Bbox(L)=(.26*v-.352)/(2*pi)>.5

throughout the ray; exact scalar anchors and monotonicity signs are in
box_scalars.py. This comparison is against the complete displayed B5 function.
The coordinator's stronger-source frontier comparison remains a separate task;
no strongest-in-literature conclusion follows from this comparison alone.

## Formal boundary

PsiSmoothing.psi_B5, psi_box and psi_box_actual_x are compiled conditional
actual-Chebyshev consumers. Kernel positivity, normalization, integrability,
monotone bracketing, real-x coverage and final error algebra are proved.
The main and trivial averaged estimates are now unconditionally discharged by
PsiElementary and instantiated by PsiClosedElementary. Remaining PNT analytic
inputs are the precisely defined averaged explicit identity with actual zeta
multiplicity/summability and the actual zero-density/moment estimate. The
original parabola provider still retains its actual integral moment bounds.
The stronger box provider closes its numerical moment cap through the source-first
C logarithm component and kernel aggregation in CLogMomentNetwork, retaining
three exact Mellin/Stieltjes analytic identities rather than the desired moment
bound as a premise. See BOX_MELLIN_EXACT.md and CLAIMS_AND_GAPS.json.

The earlier directed quadrature scripts remain written continuous-integral-tier
evidence. Their Python execution and pure Lean arithmetic alone are not
source-first PV. The separately completed C-source component has a narrower,
explicit source/AST/execution/actual-consumer scope.

The classical nonvanishing of zeta on the real interval(0,1) is part of the analytic source justification: alternating eta is positive and zeta(s)=eta(s)/(1-2^(1-s)) there. Thus gamma=0 has not been discarded merely fromRH. See the original frozenPNT.md derivation.

Primary zero-count input: Brent--Platt--Trudgian, Accurate estimation of sums over zeros of the Riemann zeta-function, Corollary1, publishedp743 (arXiv2008.06140v1 PDFp4), https://arxiv.org/pdf/2008.06140v1#page=4. It centersN(T) atT/(2pi)log(T/(2pi e))+7/8 and gives|R(T)|<=.28logT forT>=2pi. The opposite sign printed locally in Lee--Nosalv4 Eq8 is a historical source typo already audited; it is not the contract used here. The integrated formula is Dudek--Grenie--Molteni arXiv1503.05403v2 PDFp2, https://arxiv.org/pdf/1503.05403v2#page=2.
