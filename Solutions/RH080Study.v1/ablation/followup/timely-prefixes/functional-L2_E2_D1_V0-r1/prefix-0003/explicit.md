# Explicit bounds by retuning the compact Fourier window

## Source premises and conclusion

The analytic inputs are ordinary RH; the general Guinand–Weil/Mellin formula, CMS Lemma 6, in the form of Blanquer Robles (BR) §4.1, (15); the zero counting estimate and first-zero fact cited in BR §4.2 (CMS Lemma 9, Trudgian bound with the correction discussion in BR); and the general Montgomery–Vaughan Brun–Titchmarsh bound, CMS (6.8) and BR §4.3. For the finite bridge down to x=4, also use the historical prime-gap computation CMS (1.15), 11 ≤ p ≤ 4·10^18: next gap < (log p)^2. The last is a separate finite computational input, not reverified here. These are written source consumers, not a Lean RH-only closure. No GRH, Green, Nicolas, BPT, or θ estimates enter these bounds.

The **strict** interval (x, x+c√x log x) contains a prime for every real 4 ≤ x ≤ exp(174) at c=0.8. This is a bounded slab, not an eventual result with coefficient 0.8. For the ray, use the different witness and threshold in candidate.md. The general calculation below covers both.

## Window and proof

Use the Fourier convention exp(-2πiuv). Given the rational nodes a_j at j/m, extend evenly, with a_N=0 and outside [-R,R] zero, R=N/m. Let W be the continuous affine interpolant and F its inverse Fourier transform. BR Lemma 5 gives the actual pair: F(u)=sinc²(u/m) P(u/m)/m, P(t)=a_0+2Σ a_j cos(2πjt); the full L1 norm is ∫_0^1 |P|. The inverse of one triangular hat gives this formula, and the periodization of sinc² is 1 by its Fourier coefficients. The strip decay and F′ decay are quadratic on fixed strips. Define:
- U = upper bound on ∥F∥₁, M = max|W|, F0 = F(0), J = ∫_{|v|>1}(W(v))_+.
- A0 = (|a_0|+2Σ|a_j|)/m ≥ ∥W∥₁, V0 = Var(W), V1 = Var(W′) including the support boundaries and the slope jump at zero; μ2 ≥ ∫v²|W(v)|dv from the chord of absolute node values.
- H = (a_m)_+ + Σ_{j=m}^{N-1} ((a_{j+1})_+ − (a_j)_+)_+. This integrates the number of positive-level components on the right wing, by the boundary entrance and upward crossings. Reflect for the left wing.

Let t=log x≥42, z=c t/√x, d=log(1+z)/2, a=x exp d, λ=R d, Δ=d/(2π). Write Y±=a exp(±λ). The window for primes in BR (15) is w(y)=W(log(y/a)/d)/√y. For clarity (15) asserts under RH that Σ_n Λ(n)w(n) equals
[
 dsqrt aint W(v)e^{dv/2},dv-dsum_gamma a^{igamma}F(Deltagamma)
 -int_{Y_-}^{Y_+} w(y)/(y(y^2-1)),dy .
]
The general source formula applies by the same entire function dF(Δr)e^{ir log a}, continuous piecewise linear W, and compact support in the positive Mellin frequencies; see also the smoothing justification in BR §4.1. Both signs of γ and multiplicity are used.

**Scalars.** Here 1/2≤c≤1, R≤10 and d≤d*=2·10^-8, using decreasing t e^-t/2 and e^21>1.05·10^9. Log(1+z)≥z−z²/2 gives d√a≥ct/2−10^-6, since t² e^-t/2 decreases here. Also d√a≤ct/2: putting q=log(1+z), e^q−1=2e^{q/2}sinh(q/2)≥qe^{q/4}. Further log(1/d) ≤ t/2−log(ct/2)+10^-6 follows from d≥z(1−z/2)/2, z<4.2·10^-8 and −log(1−z/2)≤(z/2)/(1−z/2). The pole differs downwards from d√a F0 by at most d√a A0(cosh(λ/2)−1); this is <10^-10 using cosh r−1≤r²/(1−r) for 0≤r<1 and monotonicity of t³ e^-t bounding t d² at t=42. Since Y_->x/2, the trivial term is <10^-8 from d A0/(√Y_-(Y_-²−1)). These bounds and all uses of exp here can be checked using the positive exponential series for lower endpoints and exp(r)≤1/(1−r) for 0≤r<1. The tests use A0≤2, M≤2, U≤2, V0≤10, V1≤50.

**Zero term.** Following BR §4.2: let Q(T)=T log(T/(2πe))/(2π)+7/8. The root T0∈(9,10) has Nζ(T0)=0. For |Nζ−Q|≤0.15 log T+3, partial integration of 2d∫ |F(ΔT)|dNζ over [T0,∞) gives the main term 2∫_{ΔT0}^∞ |F(u)|log(u/d) du. The error is bounded by
[
 dig[0.30g_1+(3+0.15log(1/Delta)),2(2pi R A_0+g_1)ig],
 qquad g_1=(R V_1+2V_0)/(2pi).
]
Use |F′|≤2πRA0 everywhere, |F′(u)|≤g1/u² for |u|≥1 by integration by parts against (vW)″, and ∫_1^∞ log u/u²=1. The vanishing boundary at T0 and quadratic decay at infinity justify partial integration even with |F|. The error <10^-4 is checked with d*, since d log(2π/d) increases throughout this range and log(2π/d*)<20.

Retain the *signed* log moment, instead of dropping its negative portion. Extending its integral to u=0 costs at most 2 A0 u*(1−log u*)<10^-5, where u*=10d*/(2π). For τ∈(0,1), F(u)≥F0−2π²μ2 u² on [0,τ] from 1−cos v≤v²/2 and |W| (even for signed W). Also |F(u)|≤V1/(4π²u²) on |u|≥1. Thus the signed moment is at most
[
 L=rac{V_1}{2pi^2}
 -2F_0	au(1-log	au)+4pi^2mu_2	au^3(1/9-log	au/3).
]
On [τ,1] discard only a nonpositive contribution. The main term plus error is therefore ≤ U[t/2−log(ct/2)+10^-6]+L+0.00011. The norm multiplier is positive; no downward replacement of U in the combined expression is needed.

**Prime terms.** On the exterior, take blocks of length ℓ=√a/k, where 1≤k≤16. A level component of length s in the prime variable is covered by at most floor(s/ℓ)+1 semi-open blocks, shifting the start left as needed to include endpoints since the total covering length exceeds s. Each block contains ≤2ℓ/log ℓ primes by MV. Multiply by (log a+λ)e^{λ/2}/√a to upper-bound each weighted contribution. After layer cake and pullback lengths dy/dv≤a d e^λ, this proves the exterior sum ≤
[
 rac{B}{1-2log k/t}left(dsqrt a J+rac{2H}{k}
ight),qquad B=4.00001:
]
indeed log a≥t and 4(1+λ/t)e^{3λ/2}<B. Both endpoints v=−1,1 can be charged to the exterior, using the entrance H on each wing. No prime endpoint loss from strict counting inside. Inside, log y/√y decreases, so the sum over actual primes strictly inside is ≤ M t K_x/√x for K_x their number.

For powers q^j, j≥2, sum absolute weights: at most 1+λ√Y+ integer j-th powers in [Y−,Y+] for each j, integrating y^{1/j}/j against d log y; weight ≤ M log Y+/(2√Y−), with at most log Y+/log 2 possible exponents. This yields the same bound as BR (19) with R replacing 5, which is <0.001 by the test in the code: use Y+≤x exp(11d*), Y−≥x exp(−9d*), then t^j e^-t/2 decreasing for 0≤j≤3. The bound may overcount the same integer; the overcount is safe.

**Assemble.** Let D=F0−BJ>0, a0≥42 the lower endpoint of the t-domain, q0=1−2 log k/a0. Bound the extra multiplication over B by
(B/(1−2log k/t)−B) J d√a≤ B J c log k/q0, using d√a≤ct/2. The entire bound becomes
[
 rac{M t}{sqrt x}K_x ge rac{cD-U}{2}t+Ulog(ct/2)
 -L-rac{BJclog k}{q_0}-rac{2BH}{kq_0}-0.0012 .
]
The constant covers the preceding additive errors, including ≤2·10^-6 each from the lower bound on d√a (since D≤2) and from the log upper bound (since U≤2). For a finite slab the right side is concave and hence has minimum at an endpoint. On a ray with cD≥U it increases. These are continuum arguments, not interpolation between a few tested x values.

For the 0.8 slab take k=16, τ=3/8 and the supplied BR rational witness-ap (the shape is used for ordinary RH, without any GRH). Tests give right side >0.00699 throughout 42≤t≤174. For x≤exp(42)<4·10^18, CMS (1.15) gives the finite bridge: (log p)^2 < c√p log p for every p≥11 since log p/√p≤2/e<0.8. If p≤x<q with consecutive primes and p≥11, strict inclusion of q follows by the increasing endpoint function. For 4≤x<11 check x=4, 5, 7 with next primes 5, 7, 11, respectively (at 7 use log 7>1.94 and √7>2.64). This also covers a larger c for a ray. One can verify exp(42)<4·10^18 by e<11/4 and (11/4)^42<4·10^18.

## Directed norm, reproducibility

The fixed-point FFT is that of BR §2.1, with twiddle bounds and recurrence from the pinned supplement, certificates/certify_integer.py. A computed sample is within `checked_eps` of true real sample: twiddle error ≤12G/UNIT, exact stage norm ≤input absolute sum B0, stage recurrence E'≤(2+ε)E+ε B0+2/UNIT, and (2+ε)^s<2G. For even indices i a two-cell panel of width 2/G is handled as follows. Run an additional transform for the even vector −j² a_j to enclose samples of Q=P″/(4π²). On each cell Q differs from its linear chord by ≤10Σ j⁴ |a_j|/G² (uniform bound for Q″ and chord error 1/8). Thus the three nodes of a panel bound |P″| via a local curvature budget. Use that curvature allowance once more to check that P has the same definite sign on both cells; then integrate signed P by Simpson, error ≤sup|P''''|/(90G⁵) on the panel, with sup|P''''| ≤3200Σ j⁴ |a_j|. On other panels use the absolute-value chord upper bound and integrate its pointwise error: sup|P″|/(6G³) for two cells. The Simpson and two-cell trapezoid weights are positive, so one uniform P sample error suffices in the global integral. Argument logs use a positive atanh series with rational geometric remainder; no floating point comparison is used for validity. The displayed decimals are for readability, not predicates. Run from submission:
```
/usr/bin/python3.10 window_cert.py slab /corpus/literature/Blanquer_supplement/certificates/witness-ap.json 32768 .8 42 174 16
```
The entire code path is a reproducible directed-arithmetic check of a written proof, not source-first verification or a Lean kernel proof.
