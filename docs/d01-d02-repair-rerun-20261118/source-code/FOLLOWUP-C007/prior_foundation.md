# Shared analytic arithmetic (B0 = pinned originals only)

Write L=log x, E(x)=ψ(x)−x, H=3·10^12, H*=3000175332800. All prime counts/sums include the right endpoint. Source locators below use original PDF page numbers, not journal pagination. Both application reports use B0; the explicit variants marked basic do not require the FKS density table.

## The extra premise already follows from B0 (even with slack)

QRH, Theorem 1.1 (PDF p.4; explicit ζ conclusion), gives β≤7/8 for all nontrivial ζ zeros. Platt–Trudgian FiniteRH, Theorem 1 (p.2), gives β=1/2 up to H*. Use FKS, Theorem 3.2 (p.8), with its stated (log x_M,α,ω,M)=(40,1/2,0,2.091), not the older Dudek truncated formula criticized in its Remark 3.3. For L≥200 put T=exp(L/8+8). Then max(51,L)<T<(√x−2)/5 (check at 200, and the relevant exponential ratios increase). The theorem permits T* in [T,2.45T]; here and below the star on this variable means an adjusted truncation, not the verification height H*. By Platt–Trudgian PNT Lemma 2 (p.4, reciprocal-ordinate sum), the total reciprocal absolute ordinate weight below H is <118, and the total up to the adjusted truncation is ≤(L/8+8)^2/(2π)+1.8642 since 2.45<2π. There are no real nontrivial zeros (CH2 Appendix B, discussion preceding Lemma B.1). Hence
[
 |E(x)|/xle e^{-L/8}{118 e^{-3L/8}+(L/8+8)^2/(2pi)+1.8642+2.091L e^{-8}}
 < .005 L^2 e^{-L/8}.
]
After division of the braces by L² each term decreases, and the upper bound at 200 is checked in check.py. No older truncated-formula or older density constant is used here. The normalized bound is at most 32% of the stipulated 1/64 bound on the *entire* stipulated real ray. Thus B0 and B0+PsiMajorant have precisely the same mathematical consequences under the premise policy. In particular there cannot be an onset, a profile or an envelope for which the extra assumption is logically needed. This is a derivation inside the same research trajectory, not an independent blind baseline run.

## Stronger B0 tail using an original density corollary

For L≥110 use instead FKS 3.2 at T=exp(L/4); the inequalities on T hold at 110 and persist (check.py). Put h=log H. By FKS Corollary 2.9, eq. (2.17) and Table 8 (pp.7–8,26, the a1=.77 table), for .8≤s≤.875, t≥H,
[
 N(s,t)le 11.076,t^{p}(log t)^j+4(log t)^2,quad p=8(1-s)/3,quad j=5-2s.
]
The constants round up the relevant eight rows [.80,.81] through [.87,.88]. This invokes the tabulated corollary as stated, not a re-evaluation of its subconvexity or optimization. The text displays a mismatch between the δ≥1 in Theorem 2.7 and the δ≈.309 in the table; the basic variant explicitly avoids dependence on this tabulated assertion. Likewise we do not use the old PNT article's Lemma 5 in view of FKS Remark 1.5(2).

Let W_s=2∑_{γ>H,β>s}1/γ (positive ordinates). Partial integration and absence of any such zeros at H give
[
 W_sle F(s)+8(h^2+2h+2)/H,quad
 F(s)=2(11.076)H^{p-1}h^j/(1-p-j/h).
]
Indeed (log t/h)^j≤(t/H)^{j/h}. Throughout that s interval, −(log F)'≤(8/3)h+2log h+(8/3+2/h)/(1-8/15-3.4/h)<92. The bound at 7/8 is <.01057, including the additive term. The same bound applies to the left limit at 7/8, needed if zeros lie on the edge. The layer-cake identity for exp((β−7/8)L) over β>.8 then bounds their total weight by
[
 e^{-.075 L} W_{.8}+Lint_{.8}^{.875}e^{-(.875-s)L}W_s,ds
 le .01057 L/(L-92).
]
Here one uses exp(−(L−92)(.075))≤1 and combines the two terms before dropping it. Symmetry of ζ zeros (functional equation CH2 (A.2) and conjugation) means β>1/2 uses at most half the positive-ordinate weight above H, including multiplicities. If H is below the adjusted truncation, Platt–Trudgian Lemma 2 bounds its half-weight by
[
 [(log(T^*/2pi))^2-(log(H/2pi))^2]/(4pi)+1.8642
 < .005 L^2,
]
since log(T*/2π)≤L/4−.9 and (log(H/2π))²/(4π)>1.8642. Thus zeros with 1/2<β≤.8 contribute at most .005 L²x^(-.2). All β≤1/2 together contribute at most (.01 L²+118)x^(-.5). Adding the FKS remainder yields the real bound b_q(L)=e^(-L/8)q(L), where
[
 q(L)=.01057 L/(L-92)+.005 L^2 e^{-.075 L}+(.01 L^2+118)e^{-3L/8}
          +2.091 L e^{-L/8}.
]
This function q decreases after 110. In basic mode replace b_q by .005 L²e^(-L/8) available only from L=200.

## Integrated error with small constants, independent of density table

Put A(s)=−ζ'/ζ(s) and let D(x)=∫_0^x E(t)dt, where ψ(t)=0 on (0,1). The absolutely convergent smoothed formula is
[
 D(x)=-sum_
ho {x^{1+
ho}over
ho(1+
ho)}
       -xlog(2pi)-A(-1)
       -sum_{kge1}{x^{1-2k}over (-2k)(1-2k)},qquad x>1 .
]
For details, integrate A(s)x^(s+1)/(s(s+1)) on Re s=2. The Euler product expansion follows by unique factorization and absolute convergence, and integrating the elementary kernel (close to either side) gives ∑_n Λ(n)(x−n)_+. The kernel at x=n is zero by continuity. Move the contour left across s=1,0,−1 and the nontrivial and trivial zeros; the residue at 1 is x²/2 before subtracting the main term. For fixed left line Re s=−2k−1, choose symmetric heights in [j,j+1] at distance ≫1/log j from every ordinate: CH2 Corollary B.3 gives O(log j) ordinates in the enlarged interval, and intervals of sufficiently small radii around them cannot fill a unit interval. CH2 Proposition B.8 gives A(s)=O(log² j) uniformly on the horizontal part in [−2,2], and (A.4) gives O(log j) on the remaining fixed segment. Thus the horizontal integrals tend to zero. The left vertical integral tends to zero as k→∞: (A.3) bounds A by O(1+log(2k+2+|t|)); cot is bounded on the odd lines, ζ'/ζ(1−s) is bounded by absolute convergence, and the digamma bound follows from CH2 Lemma A.1 or its series on the right half-plane. Dividing by |s(s+1)| gives a convergent integral O(log(k+2)/(k+1)), times x^(-2k). At s=0, ζ'/ζ(0)=log(2π) as used on CH2 p.35. The nontrivial series convergence follows from CH2 B.5; the real residue series converges geometrically. These same bounds justify termwise integration below.

For x≥2, L=log x define
[
 d(L)=.094e^{-L/2}+3cdot10^{-12} e^{-L/8}+2e^{-L}.
]
Then |D(x)|≤x²d(L), and for every a≥0
[
 left|int_x^infty E(t)t^{-2-a}dt
ight|le x^{-a}d(L).
]
For the first bound the zero denominators have modulus at least γ². For the second, integrate by parts in D, using D(t)/t²→0. A term b t^v in D contributes b v x^(v−2−a)/(2+a−v). In particular the zero denominator becomes ρ(1+a−ρ), again ≥γ². Apply CH2 Lemma B.5 (p.44) at 14 (there are no zeros with 0<γ≤14) and at H: twice its right hand sides are respectively <.094 and <3·10^-12, see check.py. Use β=1/2 below H and β≤7/8 above H. The real contributions to D have absolute value ≤2x: 0<−A(−1)<3 by (A.3) and the Dirichlet series at 2 (∑_{n≥2}log(n)/n²<1.1 by an integral comparison, and the digamma at 2 is 1−γ); the negative trivial-zero correction has absolute size ≤x^-1/(2(1−x^-2)) and log(2π)<1.84. More precisely the upper bound D_real≤3 and the lower bound ≥−1.84x−x^-1/(2(1−x^-2)); for x≥2 both are within ±2x. In the weighted tail the constant −A(−1) vanishes, the s=0 term has abs ≤log(2π)x^(-1−a), and the trivial terms together are bounded by x^(-1−a) x^-2/[6(1−x^-2)].
Finally with G(t)=(1+log t)/log²t, use G(t)=∫_0^∞(1+a)t^-a da to get
[
 |int_x^infty E(t)t^{-2}G(t)dt|le d(L)(1+1/L)/L.
]
The interchange follows from absolute convergence, e.g. the basic original bound above on the tail.

## Pointwise source functions shared by both reports

CH2 Corollary 1.3 gives Gas(L)=π/(3·10^12)+113.67 e^(−L/2) for |E|/x and also for the centered weighted Λ sum. With T∈[10^7,H*], x>max(T,10^9), CH2 Corollary 1.2 and y coth y≤1+y²/3 give
[
 C_T(L)=pi/(T-1)+pi^2/(3T^2)
       +(log^2(T/(2pi))/(2pi)-log(T/(2pi))/(6pi))e^{-L/2}
]
for |E|/x, with π²/(3T²) removable for the weighted Λ sum. In applications Ch is C_T at T=min(H*,2π²e^(L/2)/L). The range in the gap certificate is L≥34; T≥10^7 and T<x there by monotonicity, and the other constraints are immediate. For Mertens it is also lawful to minimize over every admissible T, retaining the original exact coth centering as a signed interval. CH2 Lemma 9.2 (p.35), *its ψ bound only*, gives |E|/x≤.791e^(−L/2) on [10^4,10^13]. We do not use its weighted line, whose extraction of the normalization is ambiguous. FiniteRH Corollary 1 (p.4) supplies finite-RH ψ, θ and π estimates on the printed intervals; Dusart Theorem 4.2 and Corollary 4.5 (pp.11,13) give θ relative-error bounds and the sharper prime-power subtraction. FKS Corollary 1.4 gives the smooth bound 9.22022 L^(3/2)exp(−.8476836√L), and its Theorems 1.1/1.2 with Tables 5/6 give additional original step/smooth alternatives at their stated parameters. None expire when B0 is enlarged.
