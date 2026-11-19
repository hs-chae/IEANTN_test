# D02 input, ablation, and shared analytic lemmas

**B0** denotes all seven originals, including OpenAIQRH, at their stipulated original-result trust. **D02** is exactly
\[
 |\psi(x)-x|\le x^{27/32}(\log x)^2/64\qquad(\text{every real }x\ge e^{200}).
\]
Write \(t=\log x,\ u(t)=e^{-t}\psi(e^t)-1,\ b_0=7/8,\ b_2=27/32,\ r_i=1-b_i\). CAP0 and CAP2 in code are these caps; lower-case c is the separate constant \(1.048\cdot10^{-12}\). D02 implies D01 on the exact D01 ray (same coefficient, log power and threshold, smaller power of \(x>1\)). All 199 accepted D01 consequences are retained. D01 already followed from B0; see common.md and the D01 review.

## 1. Exact premise propagation

For \(\Re s>1\) the Euler product and partial summation give
\[
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(x)-x)x^{-s-1}\,dx.
\]
D02 makes the integral holomorphic on \(\Re s>27/32\) by locally uniform convergence of it and its derivatives; the finite initial part is entire. By meromorphic identity any zero strictly to the right of the boundary would give a pole with nonzero residue on the left but not the right. Thus \(\beta\le b_2\) for all nontrivial zeros, allowing equality. The real alternating eta series is positive on \(0<s<1\) and equals \((1-2^{1-s})\zeta(s)\) by continuation from \(s>1\) (summation by parts proves locally uniform convergence in \(\Re s>0\)), so there is no unpaired real nontrivial zero.

Conversely the cap \(b_2\) implies the **exact** D02 premise even over the six originals omitting QRH. Take \(T=e^{t/4}\) in FKS 3.2, apply Platt–Trudgian PNT Lemma 2 at \(T^*\in[T,2.45T]\), use \(2.45<2\pi\) and bound the reciprocal sum over the two signs by \(.0142t^2\) for \(t\ge100\). The density-free local branch for either cap is therefore
\[
 |u(t)|\le D_b^{\rm df}(t)=.0142 t^2e^{-(1-b)t}+2.091t e^{-t/4}\qquad(t\ge100).
\]
At \(b=b_2,t=200\), \(.0142+(2.091/200)e^{-(1/4-r_2)200}<1/64\); the second term decreases thereafter. The same calculation at \(b_0\) proves the inherited redundancy of D01. D02 is equivalent to the stronger *zeta* exclusion, not to a stronger Hecke or Dirichlet result, and no logical independence from B0 is asserted. Below \(t=200\) consequences are through the global spectral exclusion, not by extrapolating the numerical premise.

## 2. Continuous density interpolation

Take \(H=3\cdot10^{12},\ h=\log H\). For each closed bin in FKS Cor. 2.9 / Table 8 use the upward-rounded \(A,B\) in BINS (d02_cert.py). For \(s\ge.75\) in such a bin the sum of \(1/\gamma_\rho\) over \(\beta\ge s,\gamma_\rho>0\), even without upper ordinate truncation, is at most
\[
 F(s)=\int_H^\infty [A v^{\frac83(1-s)}(\log v)^{5-2s}+B(\log v)^2]\frac{dv}{v^2}.
\]
Indeed the count at \(H\) is zero by finite RH; partial summation leaves the integral and the upper boundary vanishes since \(\frac83(1-s)<1\). For \(d=(8s-5)/3,\ q=5-2s\), put
\[
 W(s)= A e^{-dh}h^q d^{-1}\sum_{j=0}^4
    \frac{q(q-1)\cdots(q-j+1)}{(dh)^j}+B(h^2+2h+2)/H.
\]
Substitute \(v=e^{h+w}\); \(W\ge F\) follows from the degree-4 Taylor majorant of \((1+w/h)^q\) for \(w\ge0,3<q<4\) (nonpositive remainder) and the moments of \(e^{-dw}\). Order zero contributes 1. The two integrands on a disjoint union of two copies of \([H,\infty)\) are positive exponentials of affine functions of \(s\); Hölder gives log-convexity within each bin. At each exact knot of KNOTS take \(W(s)\), or the maximum of the two adjacent formulas at bin boundaries. Join these upper values by log-linear interpolation to get \(w(s)\) on \([.75,.875]\). Both caps are knots. Each interpolation subinterval lies in a single bin, so \(F\le w\). Directed checks verify negative slopes despite jumps in the coefficient rows.

For \(k\) in RT and \(t\ge100\), take \(T=e^{kt}\) in FKS 3.2. The tests at 100 and monotonicity give \(T>51,t,\ 5T+2<e^{t/2},\ T^*>2\pi e\). This formula includes real \(x\) and jumps, unlike adjacent Theorem 3.1. Platt–Trudgian Lemma 2 gives positive-ordinate reciprocal weight at most \(a_k t^2,\ a_k=k^2/(4\pi)+.9321/10^4\). Fix \(s_0\) in SIG. Critical-line symmetry implies the zeros with \(1/2<\beta<s_0\) cost at most \(a_k t^2e^{-(1-s_0)t}\) after including both signs: at most half the positive-ordinate weight is strictly right of the line. The other zeros below \(s_0\) cost \(2a_k t^2e^{-t/2}\). For \(\beta\ge s_0\), use \(e^{(\beta-1)t}=e^{(s_0-1)t}+t\int_{s_0}^{\beta}e^{(s-1)t}ds\), sum and insert \(w\) in the cumulative bound, then integrate by parts. Thus
\[
 |u(t)|\le D_b(t;s_0,k)=a_k t^2(e^{-(1-s_0)t}+2e^{-t/2})+2.091t e^{-kt}
 +2w(b)e^{-(1-b)t}+2\int_{s_0}^b[-w'(s)]e^{-(1-s)t}ds . \tag{A}
\]
At a subinterval \([v,v+\ell]\) with \(w(s)=w(v)e^{-\kappa(s-v)}\), the integral contribution before factor 2 is \(\kappa w(v)\ell e^{-(1-v)t}\operatorname{exprel}((t-\kappa)\ell)\), where \(\operatorname{exprel}(z)=\int_0^1 e^{u z}du=(e^z-1)/z\), continued at 0. If the argument's enclosure contains 0, bound by the exponential of its two endpoints. No sampling of the prime error is used.

The last two terms of (A) form a positive exponential mixture with rates at least \(1-b\). For the other terms \(t^p e^{-dt}\), scaling by \(e^{zt}\) preserves decrease from \(a\) if \(p/a\le d-z\). The pre-integration-by-parts expression shows the matched local bound decreases strictly:
\[
 D_{b_0}(t;s_0,k)-D_{b_2}(t;s_0,k)=2t\int_{b_2}^{b_0}w(s)e^{(s-1)t}ds>0.
\]

## 3. Signed primitives with smaller critical-line weight

For \(t\ge1\), for \(k(s)=1\) or \(K(s)=s^{-1}+s^{-2}\),
\[
 \int_t^\infty u(s)k(s)ds\in k(t)[-Z_b(t)-2e^{-t},Z_b(t)],
 \qquad Z_b(t)=.0462 e^{-t/2}+4\cdot10^{-12}e^{-(1-b)t}. \tag{B}
\]
Let \(B_1(t)=\int_t^\infty u,\ B_2(t)=\int_t^\infty B_1\). Also \(|B_2(t)|\le Z_b(t)/14+2e^{-t}\). Ordinary pointwise prime errors remain end-inclusive.

On a compact interval inside \(t>0\), Dusart (2.1)'s symmetric zero series converges in \(L^2\), as in mertens.md: integrate each product of two exponentials by parts for a bound \(O((1+|\gamma-\gamma'|)^{-1})\). FKS counts \(O(\log(2+|n|))\) ordinates per unit bin; the coefficients are \(O((1+|n|)^{-1})\). Comparable bins give a summable \(O(\log^3(n)/n^2)\) after harmonic summation in the separation, noncomparable bins \(O(\log^2(n)/n^2)\). This proves Cauchy convergence in \(L^2\) and identifies the a.e. limit via (2.1). Integrate first on compact intervals, then use domination by summable \(\gamma^{-2}\) weights (factor 2 suffices for both endpoints). For \(K\) its positive Laplace density is \(1+v\) on \(v\ge0\); the divisor \(1-\rho+v\) has modulus at least \(|1-\rho|\). The absolutely convergent first primitive can be integrated again, using another divisor of modulus \(>14\). The residual is \(-e^{-t}[\log(2\pi)+\tfrac12\log(1-e^{-2t})]\), nonpositive of magnitude at most \(2e^{-t}\) on \(t\ge1\). The sum of the \(\gamma^{-2}\) weights over both signs \(|\gamma|\ge H\) is \(<4\cdot10^{-12}\) by the explicit count, equation (3) of spectral_repair.md and its replay, without Cor. 2.9.

For the low weight, \(A(t)=\sum_{n\le e^t}\Lambda(n)/n-t+\gamma\) tends to zero by Dusart 5.7: its difference from the weighted prime error is the negative omitted tail of \(\sum_p\log p/[p(p-1)]\), a convergent series. The CH2 floor alone is not used to infer a limit. Partial summation gives \(A(t)=1+\gamma+u(t)+\int_0^t u\). Since \(u(t)\to0\) and is absolutely integrable, \(B_1(0+)=-1-\gamma\) and \(A=u-B_1\). Take \(t\downarrow0\) in the integrated explicit formula by absolute domination of the integrated zero weights and the integrability of the elementary residual. The residual integral is
\(-\log(2\pi)-\tfrac12\int_0^1\log(1-v^2)dv=1-\log(4\pi)\).
Therefore \(\sum_\rho 1/(\rho(1-\rho))=2+\gamma-\log(4\pi)\). Each reciprocal has positive real part because the denominator has real part \(\gamma_\rho^2+\beta(1-\beta)>0\); critical-line terms are positive real. Thus the critical-line absolute weight is at most \(2+\gamma-\log(4\pi)<.0462\), checked via the Euler-constant bracket. Below \(H\) use this weight and finite RH, and above \(H\) use the separate high-ordinate weight with cap \(b\). This proves (B) and the bound for \(B_2\). Improvement .1 to .0462 is B0; D02 changes exactly the high-ordinate factor.

## Exact source locators and trust

* OpenAIQRH Theorem 1.1 (PDF p.4, extraction LF255–262) supplies \(b_0\). Its Part II signal equality ties \(C_{\rm II}(7/8)=3/16=\ell_x/2+b/12\) to its estimates (LF8121–8124, final use LF14676–14683). The contour/bin hypotheses are tied to that boundary; merely substituting \(27/32\) is not justified.
* Platt–Trudgian Finite RH Theorem 1 (p.2, LF48–49) is inclusive through \(3,000,175,332,800>H\). Their PNT Lemma 2 (p.4, LF236–246) is the **positive** inclusive reciprocal sum.
* FKS 3.2 (p.8, LF631–642, tuple \(40,1/2,0,2.091\)), Cor. 2.9 (pp.7–8, LF586–608), first part of Table 8 (p.26, LF3178–3258, \(a_1=.77\)), and Lemma 2.1 / Remark 2.2 (pp.4–5) are used as stated. As in the D01 review, Thm 2.7 prints \(\delta\ge1\), while the table uses approximately .309. We use the **stated corollary**, not invalid parameters in Thm 2.7. Density-free alternatives do not assume the corollary.
* Dusart (2.1) (pp.3–4, LF169–188) uses the half jump. CH2 Appendix B.1 (p.43, LF6133–6143) gives first ordinate \(>14\). CH2 Cor.1.3 (p.3, LF226–239) is a competing local bound, not a vanishing bound by itself.
* Arithmetic is ordinary Python 3.10 outward Decimal and exact integers, not Lean or source-first PV. Decimal exp and ln are correctly rounded; their adjacent neighbors enclose the exact values. verify.py includes the Machin enclosure for \(\pi\). Published finite prime and zero computations remain at the original trust tier.
