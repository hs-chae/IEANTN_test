# Exact smoothing of the explicit formula
This new route uses Dusart (2.1), CH2 Appendix B.1, PT finite RH, and the admitted OpenAIQRH Theorem 1.1 (PDF p.4, ζ explicitly included). For conditional strengthening, A-D02 implies no zeros of ζ in Re(s)>27/32: for Re(s)>1 the logarithmic derivative is s/(s-1)+s*integral_1^infty (psi(t)-t)t^(-s-1)dt, by unique factorization and partial summation. The latter integral is holomorphic on Re(s)>27/32 by local uniform absolute convergence (including its derivatives). Uniqueness of meromorphic functions and the nonzero residues of logarithmic derivatives at zeros prove the implication. Write δ=1/8 unconditionally at the admitted original trust, or δ=5/32 with A-D02.

## Termwise integration is justified
Let eψ(v)=(ψ(e^v)-e^v)/e^v, H=3*10^12. Dusart (2.1) (printed pp.229–230; PDF pp.3–4), with symmetric summation over ordinates, makes eψ(v) equal a.e. on v>0 to
  -sum_ρ exp((ρ-1)v)/ρ - exp(-v)*[log(2π)+log(1-exp(-2v))/2].
The half-jump convention is immaterial to integrals. Here is a direct L² justification for integration. On a compact interval in (0,∞), dominate the indicator by a nonnegative smooth compactly supported weight equal to 1 there. Two integrations by parts show that the Gram entry for modes exp((ρ-1)v) and exp((ρ'-1)v), with this weight, is O((1+|γ−γ'|)^−2), uniformly in both real parts in [0,1]. From CH2 B.1 the number in each unit ordinate bin n is O(log(2+|n|)). If D_n is the sum of |1/ρ| in this bin, then D_n=O(log(2+|n|)/(1+|n|)); the quadratic form is at most C sum_n D_n² since the kernel (1+|n-m|)^−2 is summable (apply 2ab≤a²+b²). Thus tails converge to zero in local L². The pointwise explicit formula away from jumps identifies the L² limit (take an a.e.-converging subsequence). This proves termwise integration on compact intervals, and zero sums after integration are absolutely convergent by the same zero count.

## Reciprocal-square sums
Let B_all=sum over conjugate pairs and multiplicities (i.e. sum over BOTH signs) of 1/γ², and B_high the same sum restricted to |γ|>H. CH2 Corollary B.2 and no ordinates <=14 give
B_all <= 2/(14π)*(log(14/(2π))+1) < .083.
For the high tail subtract N(H)/H² before integrating by parts:
B_high = 2*(-N(H)/H²+2∫_H^∞N(t)/t³ dt)
 <= (log(H/(2π))+3)/(πH)+ (2/H²)*(.2 log H+2)
 < 3.2e-12.
In the last inequality we used the B.1 lower bound and B.2 upper bound, dropping the +7/8 in the former. The finite-RH theorem in PlattTrudgianFiniteRH.pdf p.2 makes real parts 1/2 for |γ|<=H. PT PNT paper Lemma 2 gives sum_{0<|γ|<=H}1/|γ|<118 (notation 0<|γ| includes both signs).

## Pointwise deduced ψ envelope
For any real x>=exp(18) put L=log x, r=3.6e-6*exp(-δL/2), h=xr.
By monotonicity, eψ(L) lies between the average error on [x−h,x] minus h/2 and that on [x,x+h] plus h/2, divided by x. Integrate the explicit formula with weight dt, using the finite-RH low-frequency bound at the points of the interval, and integrate the high ordinates exactly via antiderivatives t^(1+ρ)/(ρ(1+ρ)).
This yields, since r<0.000004,
  |eψ(L)| <= 119 exp(-L/2) + 3.6e-6*exp(-δ L/2) + 2 exp(-L).
Indeed the low-zero term is at most 118*sqrt(1+r)*exp(-L/2);
the high term in that normalized average is at most
(3.2e-12)*(1+(1+r)^2)*exp(-δL)/r. Adding r/2 gives strictly
less than 3.6e-6 exp(-δL/2).
The trivial part of the formula, in ψ(t) rather than relative error,
has absolute value <2 for t>=e^18(1-r). This smoothing argument retains the exact inclusive ψ value via inequalities on one-sided averages.

## Truncated PNT bound improving the hypothetical majorant
For L>=200 and the same two choices of δ, define
  pδ(L) = .15916*((δ L+3.22)^2-26.89^2)+3.7284+2.091 L/64.
Then
  |eψ(L)| <= 118 exp(-L/2)+pδ(L) exp(-δL).
Use FKS Theorem 3.2 (PDF p.8), with its listed parameters (40,1/2,0,2.091)
and T=64 exp(δL). These satisfy max(51,L)<T<(exp(L/2)−2)/5.
The low-zero terms are <=118 exp(-L/2); if T*>=H, the signed difference
of reciprocal sums (PT Lemma 2) for H<|γ|<=T* is at most
  (log²(T*/(2π))-log²(H/(2π)))/(2π)+3.7284.
Now T*<=2.45T, log(2.45*64/(2π))<3.22, log(H/(2π))>26.89,
and 1/(2π)<.15916. The rational upper expression is positive
on this ray for both δ; the T*<H case contributes no high zeros.
This uses the signed formula (3.2), and not the older truncation criticized
for proof errors by FKS Remark 3.3. At δ=5/32 the coefficient
of L² is .15916*(5/32)^2 < .003886, a factor >4 over the contract's
.015625 asymptotically. All envelopes can be intersected with the originals.

## Integrated tail envelopes
For w1(v)=(v+1)/v² and w2(v)=1, write I_j(L)=∫_L^∞ eψ(v)w_j(v)dv.
For L>=18, simultaneous bounds are
 |I_1(L)| <= w1(L)*(.085 exp(-L/2)+3.3e-12 exp(-δL)+2 exp(-L)),
 |I_2(L)| <= .083 exp(-L/2)+3.2e-12 exp(-δL)+2 exp(-L).
For w1, integrate each exponential by parts twice. Its contribution before
division by |ρ| is bounded by
 exp(-(1-Re ρ)*L)*(w1(L)/|1−ρ|+2 |w1'(L)|/|1−ρ|²).
Because |w1'|/w1<=2/L and |γ|>14, the factor over the leading term is
<=1+4/(14 L); .083*(1+4/(14*18))<.085, and the analogous
high bound is <3.3e-12. For w2 integrate exactly. The trivial term
costs <2w_j(L) exp(-L). Integrability of eψ itself follows from the
pointwise smoothed bound. The absolute majorants justify passage from finite
intervals (boundary terms at U controlled by exp(-δU), times bounded w,w')
to the improper integrals. This also permits precise Mertens centering.
