# Explicit prime intervals (distinct from the fixed-A asymptotic reduction)

With ordinary RH, the general Guinand–Weil formula and quantitative zeta-zero count, the Montgomery–Vaughan Brun–Titchmarsh bound, and the historical finite gap input below, there is a prime in **(x, x+c√x log x]** throughout each of the following ranges:
* c=0.85113, every real x≥4;
* c=0.8, every real 4≤x≤exp(174);
* c=0.74, every real 11≤x≤exp(63); c=0.75, every real 11≤x≤exp(70).

In particular the first result gives the normalized consecutive-prime-gap upper bound 0.85113 from p≥5, with no asymptotic epsilon. The finite-range improvements do not give any limsup bound at their coefficients. This is a B-source/E-written and rational numerical result, not a Lean proof of the analytic predicates and not program verification of the historical computation. No Schoenfeld, Büthe, GRH, or octic source is used.

## Source predicates and witness

Use Blanquer Robles, *Rational Fourier certificates for prime gaps*, assigned `Blanquer_Robles_2026.pdf`, Lemma 5, Table 1 (integer column, Fap), §4.1 (15) and the general inputs of §§4.2–4.3: ordinary RH Guinand–Weil in the stated normalization, Nζ(10)=0 and |Nζ(T)−Q(T)|≤0.15 log T+3 for T≥e (see that section for Bellotti–Wong correction and CMS Lemma 9), and Montgomery–Vaughan [4, Theorem 2] for modulus 1 (at most 2L/log L primes in a left-open right-closed block of real length L>1). Neither the GRH prime application nor the particular numerical inequalities for FGRH in §4 are used. Use the historical bound quoted in CMS1708.04122v2, Eq. (1.15), from Oliveira e Silva–Herzog–Pardi §2.2: consecutive gap <(log p)^2 whenever 11≤p≤4·10^18. This is a separate literature computational input, included in the allowed CMS paper.

Take the even hat W of Lemma 5 from the assigned supplement `certificates/witness-ap.json` (m=80, support [−5,5]); F=check W. Set J=∫_{|v|>1} W(v)_+, A0=sum |a_j|/m (both signs), V0=Var(W), V1=Var(W') with zero exterior slopes, MW=max|a_j|, and H=W(1)_++Σ_{j=m}^{5m-1}((a_{j+1})_+−(a_j)_+)_+. The integer verifier in that supplement (`certify_integer.py` with 2^20 points) gives M=||F||_1≤U=0.781772 using the exact denominator F(0)−4J and its directed quotient upper endpoint. Our checker re-runs it by default (or explicitly trusts the Table 1 entry with --cached), checks the geometry, and certifies the inequalities below with rational arithmetic.

## Derivation

Put X=4·10^18. For x≥X take t=log x, h=c√x t with the stated c, d=(1/2)log(1+h/x), a=x exp(d), Δ=d/(2π), λ=5d, Y_−=x exp(−4d), Y_+=x exp(6d). Then t≥42, log X<43, 0<d≤d0=10^-8 and Δ≤2·10^-9 because t exp(−t/2) decreases. The interior is (a exp(−d),a exp(d)] and the complete support lies in [Y_−,Y_+]. Let w(y)=y^(-1/2)W(log(y/a)/d). In (15) the polynomial-growth strip conditions hold by Lemma 5, and Y_−>1. The pole term is ≥d√a[F(0)−A0(cosh(λ/2)−1)] by evenness. The absolute trivial-zero term is smaller than 10^-8, from dA0/[√Y_−(Y_−²−1)] with Y_−>10^18. All interior primes contribute at most MW K_x t/√x, where K_x=π(x+h)−π(x); here log y/√y decreases.

**Zeros, retaining a negative logarithmic moment.** By twice integrating by parts, |F(u)|≤g0/u² and |F'(u)|≤g1/u² for u≥1, with g0=V1/(4π²), g1=(5V1+2V0)/(2π); also |F'|≤10π A0. Start the zero-count Stieltjes integral at the root T0∈(9,10) of Q(T)=T/(2π)log(T/(2πe))+7/8. Both Q and Nζ vanish there. The zero sum on the RHS of the prime lower bound is bounded above by dΣ_γ|F(Δγ)| (both signs, with multiplicity). Its Q-density contribution is 2∫_{ΔT0}^∞ |F(u)|log(u/d)du. Extending down to zero costs at most 2A0 d, because the omitted negative part is confined to [0,d] and ∫_0^d log(d/u)du=d. The zero-count remainder is at most
`d[0.30 g1 + (3+0.15 log(1/Δ))·2(10π A0+g1)]`;
this follows by parts as in §4.2 using ∫_1^∞ log u/u² du=1. Noting that Δlog(1/Δ) increases in the range, the rational checker bounds this error plus 2A0 d and 2g0 by 0.207.

For 0≤u≤r=0.45, the cosine inequality gives |F(u)|≥F(u)≥F(0)−B u² with B=2π²∫v²|W(v)|dv. The checker bounds B via π²<10 and the second moments of the individual absolute-coefficient hats: the unit-height hat centered at j/m has area 1/m and variance 1/(6m²). Thus 2∫_0^1|F(u)|log(u)du is at most
`-2[F(0)r(1−log r) − B r³(1/3−log r)/3] < −1.277`.
For u>1 the positive logarithmic moment is bounded by 2g0, counted above. Since log(1/d)>0, the final bound on the zero term is U log(1/d)+0.207−1.277. Dropping the negative moment would substantially weaken the finite ranges.

**Exterior primes, with shorter blocks.** Cover each positive-level component of W on either exterior wing by ⌊s/L⌋+1 consecutive blocks of length L=√a/12, where s is its image length under y=a exp(dv). The cover can be shifted left slightly to include both endpoints, since its total length exceeds s. In particular p=x is charged to the exterior, not the interior; charging the other endpoint twice is unnecessary and harmless for upper bounds. Multiply the Brun–Titchmarsh bound by (log a+λ)e^(λ/2)/√a, a weight bound on [Y_−,Y_+]. The exterior sum is at most
`A_q e^λ d√a J + 2 A_q H/q`
with q=12 and A_q=4(1+λ/log a)e^(λ/2)/(1−2log(q)/log a). Indeed integrated component count per wing is H (affine upward crossings, as in (17)), and integrated image length is ≤a d e^λ J. For t≥42, A_q e^λ≤ 4.000001/(1−4.97/t), and d√a≤0.431t. Splitting off the multiplier 4.000001 shows the bound is at most 4.000001 d√a J+0.285. This is an explicit finite-x tradeoff; it does not purport to reduce the asymptotic penalty below 4.

**Higher powers.** For each k≥2 there are ≤1+λ√Y_+ integer kth powers in the support (integrate y^(1/k)/k against d(log y)), and there are ≤log Y_+/log 2 exponents. Each contributes in absolute value ≤MW log Y_+/(2√Y_−). Their total is <0.00005 by the rational bound in the checker, using decrease of t^j exp(−t/2) for j≤3. No count of primes is inferred from a floating-point sample.

**Margin.** Combining the preceding bounds with (15) gives
`MW K_x t/√x ≥ d√a D − U log(1/d) + 1.277 − 0.207 − 0.285 − 0.00005 − 10^-8`
with D=0.91851379, because the pole minus base exterior coefficient exceeds D. The elementary inequalities log(1+z)≥z−z²/2, z=h/x<2·10^-8, imply d√a≥ct/2−0.001 and log(1/d)≤t/2−log(0.49999999 ct). Since D<1, the RHS is bounded below by
`R_c(t)=(cD−U)t/2 + U log(0.49999999 ct) + 0.7839`.
For c=0.85113 the function is increasing for t≥42, and R_c(42)>0. For the three finite ranges it is concave, so it suffices to check the two endpoints at 42 and the stated upper log bound. The checker certifies those strict margins by an atanh-series log bracket. It also checks all small-prime gaps required below.

For x<X with preceding prime p≥11, (log p)/√p≤2/e<0.74 and the historical gap bound plus monotonicity of x+c√x log x suffice. For 4≤x<11 and c≥0.8, directly use left endpoints 4,5,7 and next primes 5,7,11; the same monotonicity propagates to all real x. This covers the bridge including endpoint conventions. We do not turn a closed-left interval theorem into a consecutive-gap theorem, and do not use a finite-x result as evidence for all real x.

Reproduce: `/usr/bin/python3.10 explicit_cert.py` from submission; `--cached` separately checks the new rational margins with the primary Table 1 norm input. The proof is written and the scalar checks executed; it is neither a Lean closure nor a C source verification.
