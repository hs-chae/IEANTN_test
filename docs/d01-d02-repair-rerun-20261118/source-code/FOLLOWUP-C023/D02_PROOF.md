# Shared D02 analytic engine

## Exact premises and reversible strip transfer

B0 means the seven exact originals listed by SOURCE_INDEX.json, with their published hypotheses and literature-computation trust. No full RH. The added premise is the exact real inclusive bound
\[
 |\psi(x)-x|\le x^{27/32}(\log x)^2/64\quad(x\ge e^{200}).
\]
Write \(b=27/32,\ d=1-b=5/32\). Initially for Re s>1, absolute convergence of the differentiated Euler product and partial summation give
\[
 -\frac{\zeta'}{\zeta}(s)=\frac{s}{s-1}+s\int_1^\infty (\psi(t)-t)t^{-s-1}\,dt.
\]
The finite interval through \(e^{200}\) is harmless, and the hypothesis makes the integral holomorphic on Re s>b (convergence locally uniform there also after differentiation). The pole-subtracted logarithmic derivative agrees by uniqueness of meromorphic continuation; it could not have the nonzero pole of a zero of any multiplicity in that open half-plane. Thus every nontrivial zero has \(\beta\le b\), not necessarily \(<b\). No zero has real ordinate zero: on the real interval (0,1) pair the positive alternating eta-series terms, and use its holomorphic relation to ζ. The first positive ordinate exceeds 14 (CH2 Appendix B.1, PDF p.43). Conjugate zeros and multiplicities are counted.

For the B0 parallel calculation use \(d_0=1/8\), from OpenAIQRH Theorem 1.1 (PDF p.4, explicitly ζ). Finite RH is separately used: Platt–Trudgian finite RH Thm.1 (PDF p.2) gives the exact height \(H=3000175332800\) and includes its endpoint. QRH is not removed from any premise list. Conversely, the estimate proved below with \(b=27/32\) implies the exact supplied hypothesis: \(F_d(200)<.260\), \(F_d\) decreases thereafter and \(200^2/64=625\). So *relative to B0*, this contract and the improved closed ζ strip are equivalent. This does not prove that the strip or the contract is independent of B0. The old 7/8 contract was redundant, as proved in the inherited comparison.md.

## Reciprocal moment enclosure with a near-height subtraction

Use FKS arXiv:2204.02588v3, Cor.2.9 and (2.17) (PDF p.7), Table 8 first block (PDF p.26; \(a_1=.77,H_0=3\cdot10^{12},k=1\)), at \(s\in[.70,.875]\) and \(t\ge H\). The cap is
\[
 D_s(t)=c_s t^{p}(\log t)^{q_s}+d_s(\log t)^2,\quad p=8(1-s)/3,\quad q_s=5-2s.
\]
The table bounds are rounded upwards in d01_cert.bracket. Table endpoints use a containing closed row. The ordinate count here is for positive ordinates and includes \(\beta\ge s\); the precise convention at \(\gamma=t\) does not affect integrals. We did not substitute the conditional \(a_1=.618\) rows.

For m=1,2 the desired weight is \(H^{m-1}\sum_{|\gamma|>H,\,\beta\ge s}|\gamma|^{-m}\). By Tonelli it is at most \(2m H^{m-1}\int_H^\infty D_s(t)t^{-m-1}dt\), each zero contributing \(\int_{|\gamma|}^\infty mt^{-m-1}dt\). Put \(z=\log H,r_1=1-p,r=m-p\). After dividing out \(2m\), substituting \(t=He^v\), an upper bound is
\[
 c_s e^{-r_1 z}z^{q_s}\sum_{j=0}^{4}\frac{(q_s)_j}{z^j r^{j+1}}
   +\frac{d_s}{H}\left(\frac{z^2}{m}+\frac{2z}{m^2}+\frac{2}{m^3}\right).
\]
The falling factorial formula follows by integrating the degree-four Taylor polynomial for \((1+v/z)^{q_s}\); since \(3<q_s<4\) the fifth derivative is negative. This quadrature is an upper bound on the entire improper tail.

**New subtraction:** since \(s>1/2\), in the initial band \([H,He^\eta]\) the count is bounded instead by \(N(t)-N(H)\). By CH2 (B.1), Lemma B.1 (PDF p.43), it is at most
\[
 (t-H)\frac{z+\eta-\log(2\pi)}{2\pi}+\tfrac25z+\tfrac15\eta+4.
\]
The integrated cost of this upper bound, including the \(H^{m-1}\) but not \(2m\), is at most
\[
 B_\eta=\frac{z+\eta-\log(2\pi)}{2\pi}\frac{\eta^2}{2}
       +\frac{.4z+.2\eta+4}{H}\eta,
\]
using \((e^v-1)e^{-mv}\le v\) and \(e^{-mv}\le1\). The integral of the **discarded** density cap on that band is at least
\[
 A_\eta=c_s e^{-r_1z} z^{q_s}(1-e^{-r\eta})/r
\]
(by keeping only its first term and replacing \(z+v\) by z). We can therefore subtract \(2m\max(0,\max_\eta(A_\eta-B_\eta))\) from the full density upper bound, using any finite list of bands. The checker uses \(\eta=2^j,-16\le j\le1\), directed lower bounds on the savings, and rounds the result up in units \(10^{-11}\). Neither the bands nor their choice require that the two count majorants be ordered at every point.

Let \(s_0=.70<s_1<\cdots<s_m=b\) be the mesh in nodes(d); here the subscript m on the mesh terminal is not the moment order. Take running minima \(w_{i,k}\) of the bounds for moment \(k=1,2\). For either k define
\[
 B_k(L)=w_{m,k}+\sum_{i=0}^{m-1}(w_{i,k}-w_{i+1,k})e^{(s_{i+1}-b)L}.
\]
For measure on zeros of mass \(H^{k-1}|\gamma|^{-k}\), integrate its cumulative tail M(s) against \(L e^{-(1-s)L}ds\), adding \(M(s_0)e^{-(1-s_0)L}\). On each step use \(M(s)\le w_{i,k}\). Telescoping gives \(B_k(L)e^{-dL}\) for the moment weighted by \(e^{-(1-\beta)L}\). This treats zeros even on b, and no differentiation of a numeric bound is used. The two meshes agree up to b=27/32 and the B0 mesh adds nodes above it. In the *absolute*, not the factored, functions, clipping the B0 integral at b keeps the part through b identical and removes a positive integral above b. In particular the subtraction from the B0 method is rigorous at every real L>0; it is not a crossing inferred from samples. The limiting step coefficient is the weight at the **last node below** b (the last two terms share the exponent zero).

## Endpoint and primitive envelopes

For L≥40,
\[
 |d_\psi(L)|\le F_d(L)e^{-dL},\quad d_\psi(L)=\psi(e^L)e^{-L}-1,qquad
 F_d(L)=\left((L/3+1)^2/6+2\right)e^{-(.3-d)L}
        +2.091 L e^{-(1/3-d)L}+B_1(L).
\]
Use FKS Theorem 3.2 (PDF p.8), parameters \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\), \(T=e^{L/3}\), real x and \(T^*\in[T,2.45T]\). Both height conditions hold at L=40 and persist: \(e^{L/3}/L\) and \(e^{L/6}\) increase while \(5+2e^{-L/3}\) decreases. For zeros with \(\beta<.70\), bound the both-sign reciprocal sum via PT PNT paper Lemma 2 (arXiv:1809.03134v2, PDF p.4), using \(\log(T^*/(2\pi))\le L/3+1\) and \(1/(2\pi)<1/6\). Zeros at or above .70 all have \(|\gamma|>H\); their full reciprocal moment is bounded above as just proved. The FKS formula error is \(2.091L e^{-L/3}\). The factored coefficient F decreases on L≥40 by positive exponential coefficients and the elementary log derivatives of the two polynomial prefactors.

Use also CH2 Cor.1.2 (PDF p.3), now with T=H, for all L≥40:
\[
 |d_\psi(L)|\le q+C_T e^{-L/2},\qquad
 q=1.047136353\cdot10^{-12},\quad C_T=113.669378.
\]
Indeed \(t\coth t-1\le t^2\) for t≥0 by differentiating \((1+t^2)\sinh t-t\cosh t\), and CH2 gives the bound centered at \(t\coth t\) with t=π/H. Drop the favorable \(-e^{-L}\) term from the radius for the symmetric bound. Keep the original asymmetric bound too. Only this small numerical refinement uses exact H in CH2 rather than 3·10^12. The important change in the plateau join is from the added strip, not this numerical refinement.

For \(U_\psi(L)=\int_L^\infty d_\psi(v)dv\) use the absolutely convergent explicit formula (S1) in d01_smooth.md §1, from CH2 (B.9), (A.2), with the Laplace-transform proof there (or Dusart (2.1) and justified compact L² integration as in d02_smoothing.md; use the current d). The contribution for \(|\gamma|\le H\) is bounded by \(.0463 e^{-L/2}\): (B.9) and expansion at 1 give \(\sum_\rho [\rho(1-\rho)]^{-1}=2+\gamma-\log(4\pi)<.0463\); all terms have positive real part and low terms are positive real by finite RH. The high terms have \(|\rho(1-\rho)|\ge\gamma_\rho^2\). An upper bound on the full high reciprocal-square sum, multiplied by H, is 13: use PT Lemma 2 to bound the *difference* of both-sign reciprocal sums from H to t by
\[
 \frac{\log^2(t/(2\pi))-\log^2(H/(2\pi))}{2\pi}+3.7284.
\]
Integrate against \(Ht^{-2}dt\) on [H,∞), obtaining \((2\log(H/(2\pi))+2)/(2\pi)+3.7284<13\). Thus, with \(J_d(L)=(13e^{-(.3-d)L}+B_2(L))/H\),
\[
 |U_\psi(L)|\le .0463e^{-L/2}+J_d(L)e^{-dL}+2e^{-L}.
\]
The factored high coefficient is nonincreasing. The mathematical unfactored J is a positive sum of exponentials of rates between d and .30; this extra property is used for π. The high term can always be intersected with \(3.2\cdot10^{-12}e^{-dL}\) from CH2 B.1/B.2 and the integration in d02_smoothing.md §“Reciprocal-square sums”. Trivial terms in (S1) cost \(2e^{-L}\) and the non-primitive elementary term in Dusart (2.1) also costs \(2e^{-L}\) for L≥18.

## Evidence and caution

Run d02_density_new.py; it imports only the exact arithmetic helpers and Table 8 from the bound own floor. The arithmetic is directed rational (Taylor plus positive tail for exp and atanh series for log), including the subtraction, reciprocal totals, Machin π and left endpoints. Printed floats are rounded descriptions of verified rational intervals. The analytical formulas extend to every real argument in their claimed domains. All pointwise expressions used in the claims refer to the displayed mathematical exp/log and rational weight constants, not to rounded sampled function values.

A potentially stronger variant using FKS (2.13) inside the density integral was investigated. The logarithm rather than its linear upper bound would help around H, but the printed Theorem 2.7 parameters (including the displayed condition on δ versus the values in Table 8) and its leaf constants referring to an unsupplied paper are not silently substituted for the standalone published Cor.2.9. The independent count subtraction above requires neither that step nor a sharper unpublished subconvexity input. CH2 Thm.1.1 with T>H would require controlling non-critical zero weights AND contour terms; the critical-line Cor.1.2 cannot simply be extended to that T. No larger unproved finite RH height is used.
