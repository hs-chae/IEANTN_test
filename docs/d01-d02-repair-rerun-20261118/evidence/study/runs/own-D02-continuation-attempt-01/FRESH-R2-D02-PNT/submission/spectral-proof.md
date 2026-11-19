# Analytic input and the two spectral portfolios

Let B0 be the seven originals at their allowed trust and the common foundations. OpenAIQRH Theorem 1.1 (PDF p. 4) gives a zeta zero cap \(b_0=7/8\), not exclusion at equality. Use Platt–Trudgian FiniteRH Theorem 1 (PDF p. 2; also CH2 p. 3) up to at least \(H=3\cdot10^{12}\). The new premise is
\[
 |\psi(x)-x|\le x^{27/32}(\log x)^2/64 \quad(x\text{ real},\ x\ge e^{200}).
\]
D02 implies D01; B0 independently proves D01, as in d01-candidate.md. We neither assume full RH nor alter any original hypothesis.

## Where the assumption changes the argument

For \(\Re s>1\), logarithmic differentiation of the absolutely convergent Euler product and Stieltjes summation give
\[
 -\zeta'(s)/\zeta(s)-s/(s-1)=s\int_1^\infty(\psi(t)-t)t^{-s-1}\,dt .
\]
On compact subsets of \(\Re s>27/32\) the D02 tail and each differentiated integral converge normally (a decaying power wins against any fixed log power). The finite initial integral is entire. Meromorphic uniqueness implies that the left side is holomorphic there. A zero would give a pole of the log derivative with nonzero residue, with no cancellation by \(s/(s-1)\). Hence every nontrivial zero has \(\beta\le b_2=27/32\). Equality is allowed. This conclusion concerns all heights; its arithmetic effects can begin below \(e^{200}\). No smaller cap follows from this argument. In the other direction, on B0 the cap \(b_2\) implies the exact D02 input: use the bound \(.221e^{-5L/32}\) for \(|e^{-L}\psi(e^L)-1|\), \(L\ge200\), proved below and in mertens-d02.md; \(.264<L^2/64\) there. Thus **over B0 the exact input is equivalent to this zeta cap**. This is not a proof that B0 cannot imply that cap.

## Spectral envelope

Put \(E(L)=e^{-L}\psi(e^L)-1\) and \(g=1-b\), \(b=b_2\) or \(b_0\). FKS Theorem 3.2 (PDF p. 8) with \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\) applies with \(T=e^{hL}\), \(V=e^{hL+1}\) for the \(h,a\) in spectral02.py and \(L\ge a\). It gives a truncation cost \(2.091Le^{-hL}\). The code checks \(T>\max(51,L)\), \(5T<e^{L/2}-2\), \(V>2.45T\), \(V>10^6\) at \(a\). Ratios \(T/L,(e^{L/2}-2)/T\) increase (respectively \(h>1/L\), \(h<1/2\)), and the other guards persist. This uses the result stated in FKS, not the older formula discussed in their Remark 3.3.

For \(.75\le\sigma<b\), FKS Cor. 2.9 and Table 8 (PDF pp. 7–8, 26) give
\(N(\sigma,t)\le c_1t^{8(1-\sigma)/3}(\log t)^{5-2\sigma}+c_2(\log t)^2\).
Use the printed interval upper constants at inherited trust, not a rederivation of the table (the parameter-printing issue identified in D01 is not assumed resolved). For these real parts the count is zero below \(H\). With \(u=\log H,\ d=1-8(1-\sigma)/3,\ q=5-2\sigma\), summation by parts (the upper terminal term vanishes) yields
\[
 2\sum_{\beta\ge\sigma,\ \gamma_\rho>0}\frac1{\gamma_\rho}
 \le 2\left[c_1u^q e^{-du}\sum_{j=0}^4\frac{q^{\underline j}}{d^{j+1}u^j}
       +c_2(u^2+2u+2)/H\right].
\]
Indeed \(3<q<4\); the fourth Taylor polynomial for \((1+z)^q\) is an upper bound for \(z\ge0\), by the fifth derivative, and polynomial integration gives the displayed powers of \(d^{-1}\). Round up and take the running minima \(D_i\), legal since actual masses decrease. On \(\sigma_0<\cdots<\sigma_m=b\) let \(w_i=e^{-(1-\sigma_{i+1})L}\), \(0\le i<m\). A zero exactly at a grid node goes in the upper bin, except that \(b\) belongs to the last bin. Abel summation bounds this part of the truncated explicit formula by
\[
 D_0w_0+\sum_{i=1}^{m-1}D_i(w_i-w_{i-1})
 =\sum_{i=0}^{m-1}(D_i-D_{i+1})w_i,\qquad D_m=0.
\]
The final zero padding is algebra, not zero exclusion at \(b\). The paired calculations include the D02 cap as a grid node of the B0 grid, so the B0 expression adds precisely the positive increments above that node with the same \(D_i\)'s. The increase is strict at \(L>0\). We use multiplicities, conjugation and \(|\rho|\ge|\Im\rho|\).


A separate original-source improvement is essential numerically. Dusart Theorem 2.3 (PDF p. 5, physical LF 252–259 of Dusart2018.txt) uses the same ordinate and real-part count and gives
\[
 N(\sigma,t)\le t\log\left(1+\frac{9.8}{2t}(3t)^{8(1-\sigma)/3}(\log t)^{5-2\sigma}\right)
             +\frac{103}{2}(\log t)^2.
\]
Use the printed 1/2 factors, not another halving. For \(v=\log t\ge u\), put \(y(v)=4.9\,3^{1-d} v^q e^{-dv}\); then \(y\) decreases since \(d>q/u\), verified at the used nodes. The correction
\[
 \log(1+y)\le y-\frac{y^2}{2(1+y)}
\]
follows by integrating \(t/(1+t)\) from 0 to \(y\). In the mass integral use the previous Taylor upper estimate for \(\int_u^\infty y(v)\,dv\). In the subtracted term replace \(1+y(v)\) by \(1+y(u)\) and bound \(\int y(v)^2\,dv\) **below** by
\[
 y(u)^2\sum_{j=0}^6 \frac{(2q)^{\underline j}}{(2d)^{j+1}u^j}.
\]
The degree-6 truncation of \((1+z)^{2q}\) is a lower bound because \(6<2q\le7\) and its seventh derivative is nonnegative. Integrate the \(51.5v^2e^{-v}\) part exactly. Take the smaller of the two mass bounds (Dusart and FKS) before rounding and taking running minima. This is a B0 improvement included in both computations, not attributed to D02. The terminal masses on the used grids are approximately .115567509 and .006667034; these decimals are not used as inputs. The amplitude factors do not describe actual zero mass.

For the low bucket the basic variant uses FKS Lemma 2.1, Remark 2.2, Cor. 2.3/Table 1 (PDF pp. 4–5). As in repair.md the total reciprocal sum with factor 2 is \(<.16(\log V)^2\) for \(\log V\ge26\); for smaller \(V\) use the bound at \(e^{26}\). Take \(w=\max(h+1/a,26/a)\); this gives \(.16w^2 L^2e^{-L/5}\). The split variant has \(V>H\). Below \(H\) the total reciprocal sum with factor 2 is \(<128\), using Cor. 2.3 at \(H\), \(U=30610046000,\ S_0=39.5797647802\); its rate is \(1/2\). Above \(H\) Lemma 2.1 gives
\[
 S(V)=2c(v-u)((v+u)/2-p)+4R(H)/H,\quad
 v=hL+1,\ u=\log H,\ p=\log(2\pi),\quad
 c=(2\pi)^{-1}+\frac{.137u+.443}{Hu(u-p)}.
\]
It bounds \(2\sum_{H\le\gamma_\rho<V}1/\gamma_\rho\). Expand in powers of \(L-a\); all coefficients are positive. For low cutoff \(s=\sigma_0\) one may add \(S(V)e^{-(1-s)L}\) to the density layer sum; this is valid even though the upper bounds overcount.

The symmetric refinement uses the functional-equation symmetry (as in FKS Prop. 3.6, PDF pp. 9–10): at most half the above-\(H\) reciprocal weight is at \(\beta>1/2\). Writing \(u_0=e^{-L/2}, w=e^{-(1-s)L}\), the upper bound for the above-\(H\) part is
\[
 (S(V)/2)(w+u_0)+\sum_{i=0}^{m-1}D_i(w_i-w_{i-1}),\qquad w_{-1}=w.
\]
First assign \(u_0\) to all zeros, then \((w-u_0)\) to those with \(\beta>1/2\), then add the high increments. Line zeros are allowed and need not be split equally. Use the original layer sum plus \((S(V)/2-D_0)w+(S(V)/2)u_0\), retaining a shape only if the constant in \(S(V)/2-D_0\) at its anchor is certified nonnegative. Add \(128u_0\) and the FKS truncation cost. All shapes may be minimized on their domains (the code uses a fast subset for finite coverage). Keep the old branches and, for \(L\ge200\), the exact direct D02 boundary as well. This last leaf is never necessary on its own ray, by the proved .221 bound.

## Integrated error

Use the reciprocal-square estimates from d01-candidate.md and analytic.py, \(\sum_\rho|\gamma_\rho|^{-2}<.12\), and above \(H\) a sum \(<8\cdot10^{-12}\). Define
\[
 J_b(L)=.12e^{-L/2}+8\cdot10^{-12}e^{-(1-b)L}.
\]
Dusart (2.1), PDF pp. 3–4, gives \(E(v)=-\sum_\rho e^{(\rho-1)v}/\rho+e^{-v}G(v)\), \(|G(v)|<1.84\) for \(v\ge\log 2\), at ordinary non-jumps, with mid-values at jumps. The compact \(L^2\) proof in mertens-proof.md (“Oscillatory integration”) justifies integrating the series: FKS unit-interval counts control square-summable local reciprocal masses, two integrations by parts under a smooth cutoff give a summable kernel, and the local limit agrees almost everywhere. After integration the grouped infinite sums converge absolutely by the reciprocal-square bound. Boundary values are still right-continuous. The integrated Mertens errors are bounded by \(J_b+1.84e^{-L}\) for kernel \(1\), and \([(1+1/L)J_b+1.84e^{-L}]/L\) for kernel \(1/v+1/v^2\). For the second, use \(1/v+1/v^2=\int_0^\infty(1+t)e^{-tv}dt\) and \(|1+t-\rho|\ge|\Im\rho|\). The reciprocal-square estimate also makes the upper-end tails vanish. The cap in \(J_b\) is a second, distinct effect of D02; the Ramanujan version is in ramanujan-d02.md.

We do not exclude zeros at or arbitrarily close to \(b_2\). Under this method a fixed final density upper mass controls the eventual coefficient. Better asymptotic powers would require further information, not provided by that mass.
