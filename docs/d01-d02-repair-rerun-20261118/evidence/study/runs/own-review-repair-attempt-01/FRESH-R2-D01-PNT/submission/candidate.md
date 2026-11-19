# D01 portfolio: conclusions and premise comparison

Let B0 denote the seven original sources at their packet trust tiers, with their original hypotheses, and the common foundations. In particular B0 includes **OpenAIQRH Theorem 1.1 (PDF p. 4)**, explicitly including its conclusion for ζ. B0 does not include full RH. D01 assumes
\[
 |\psi(x)-x|\le \tfrac1{64}x^{7/8}(\log x)^2
 \quad(x\ge e^{200},\ x\text{ real})
\]
for the right-continuous counting convention. **B0 already proves D01**, with \(1/160\) instead of \(1/64\). Consequently both families have **no D01-only improvement**: in every lawful derivation using B0+D01, the extra assumption can be replaced by the B0 proof below, point for point on its exact domain. This compares against even the strongest lawful B0 envelope (not just one selected PNT conversion). The new application results are improvements in what is explicitly derived from B0, not an effect of adding the redundant assumption. This is not an independent blind baseline run.

* **Ramanujan** (ramanujan-proof.md): with \(L=\log x\) and \(R=e x\,\pi(x/e)/L-\pi(x)^2\), the last real counterexample is the root \(r=38358837682.217926365\ldots\) specified there. The strict sign holds for every point of the open ray \(x>r\), and the first integer of the connected positive ray is 38358837683. Quantitative whole rays include \(R>0.1x^2/L^6\) from \(L=36.74\), \(R>0.5x^2/L^6\) from \(37.77\), \(R>x^2/L^6\) from \(40\), and \(R>(1+14/L)x^2/L^6\) from \(47.2\). The repair certifies profiles of arbitrary degree, for example degree 40 from \(L=1612\). Take the maximum of all applicable lower profiles.
* **Mertens** (mertens-proof.md): a common bound for both relative product errors and the reciprocal-prime-sum error is \(0.185/L^3\) from \(L=16\). Power profiles \(Cx^{-1/8}/L\) hold, for example, with \(C=.0215,.0196,.011\) from \(L=13,200,5000\), respectively. The analogous fourth (log-weighted prime-sum) errors have power profiles \(Cx^{-1/8}\) and their own log-power profiles. There are signed pointwise bounds and finite early-onset improvements, including improved real onsets at the original Dusart coefficients. The repair gives cap-free .160 and .167 coefficients respectively for the first three and fourth log-power bounds at \(L=16\), and a .0199 power coefficient from \(L=13\). Keep the pointwise minimum (or intersect signed intervals), preserving applicable original branches.

**Repair continuation (same D01 stage).** See [repair.md](repair.md) for the source-normalization correction, cap-free Mertens certificates and stronger finite/asymptotic envelopes, and earlier Ramanujan onsets and arbitrary-order profiles. The main claim is still redundancy, not a treatment gain. Take the new pointwise envelope together with all previously valid branches.

## Redundancy proof without the density table

Use \(H=3\cdot10^{12}\), \(L=\log x\), with zeros counted with multiplicity. OpenAIQRH Thm. 1.1 gives \(\beta\le7/8\), including the non-excluded boundary. Nontrivial zeros are not real: on \(0<s<1\) the alternating eta series is positive (pair terms), and equals \((1-2^{1-s})\zeta(s)\) by the even/odd identity for \(s>1\) and locally convergent Dirichlet summation on \(\Re s>0\).

FKS Lemma 2.1, Remark 2.2 (Rosser constants), and Cor. 2.3, Table 1, PDF pp. 4–5, give, with \(U=10^6\), for \(V>U\),
\[
 2\sum_{0<\gamma<V}1/\gamma < 23+0.16(\log V)^2 .
\]
Indeed, writing \(u=\log U,\ v=\log V,\ p=\log(2\pi)\), the product of logs in (2.1) is \((v^2-u^2)/2-(v-u)p\). The coefficient before the product is \(c<.16\) and the doubled initial constant is \(<23\); analytic.py checks both. At \(L\ge200\), take \(T=4e^{L/8}\), \(V=10e^{L/8}\). Then \(\max(51,L)<T<(\sqrt x-2)/5\) and \(2.45T<V\) (check at 200, then use the exponential growth ratios). FKS Thm. 3.2, PDF p. 8, with \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\), bounds \(\psi-x\) by the zero sum up to \(T^\star\le2.45T\) plus \(2.091xL/T\). It follows that
\[
 \frac{e^{L/8}}{L^2}\,\frac{|\psi(e^L)-e^L|}{e^L}
 \le \frac{23}{L^2}+.16\left(\frac18+\frac{\log10}{L}\right)^2+\frac{2.091}{4L}
 <\frac1{160}.
\]
Every term decreases and the last test is at 200. The bound is for real \(x\); even if one used the formula off jumps, a right-hand limit gives the stated raw values. No half-prime-power endpoint convention is used for the resulting theorem.

## Stronger spectral envelopes for the applications

FiniteRH Thm. 1 (PDF p. 2) verifies RH through a height exceeding \(H\). FKS Cor. 2.9, Eq. (2.17), and Table 8 (PDF pp. 7–8, 26) give \(N(\sigma,t)\le c_1 t^p(\log t)^q+c_2(\log t)^2\) for \(t\ge H\), with \(p=8(1-\sigma)/3,\ q=5-2\sigma\). Use the published table at its inherited trust, rounding its constants up as in analytic.py. For \(\sigma\ge.80\), put \(h=\log H,\ a=1-p\). Partial summation, no such zeros below \(H\), and \(v^q\le h^q e^{q(v-h)/h}\) for \(v\ge h\) give
\[
 2\sum_{\beta\ge\sigma,\gamma>0}1/\gamma
 \le D(\sigma)=2\left[
 \frac{c_1 h^q e^{-ah}}{a-q/h}+\frac{c_2(h^2+2h+2)}{H}\right].
\]
Here \(a-q/h>0\), and there is no terminal term at infinity. On the grid \(\sigma_0=.80<\cdots<\sigma_m=7/8\) in analytic.py, bound a zero in band \(i\) by weight \(w_i=e^{-(1-\sigma_{i+1})L}\) (assign a boundary to the upper band, and \(7/8\) to the last). The weighted sum is at most \(D_0w_0+\sum_{i\ge1}D_i(w_i-w_{i-1})\), with \(D_i=D(\sigma_i)\). Thus it is bounded by
\[
 G(L)=\sum_{i=0}^{m-1}(D_i-D_{i+1})e^{-(1-\sigma_{i+1})L},\qquad D_m=0.
\]
All the rearranged coefficients are certified positive. A second, coarser bound is obtained from the separate bands in analytic.py, using each mass bound independently.

For \(L\ge100\), take \(T=e^{L/2}/6\) in FKS Thm. 3.2. Its admissibility follows at 100 and from monotone ratios; \(T^\star<e^{L/2}\). In the preceding reciprocal sum estimate retain the negative terms \(-vp-u^2/2+up\) with \(v=L/2\); their contribution more than absorbs 23 already at 100. Thus \(2\sum_{0<\gamma<e^{L/2}}1/\gamma<.04 L^2\). Treat \(\beta<.80\) by this estimate and the others by the band weights. The two bounds on \(|\psi(e^L)-e^L|/e^L\) are \(\mathcal F(L)=.04L^2e^{-L/5}+13Le^{-L/2}+G(L)\), and \(\mathcal S(L)\) with the coarser band sum instead. Both are positive sums of modes. Multiplied by \(e^{L/8}\) they are nonincreasing for \(L\ge200\); for instance \(\mathcal S(L)<.1e^{-L/8}\). The finer profile and the mertens.py tests give \(\mathcal F(L)<.0196e^{-L/8}\) there. This dominates D01 on its whole ray, with a gain over 31,000 in the error bound at \(L=200\).

We also use
\[
 \sum_\rho |\Im\rho|^{-2}<.12,\qquad
 \sum_{|\Im\rho|>H}|\Im\rho|^{-2}<8\cdot10^{-12}.
\]
The first ordinate is \(>14\) (CH2 PDF p. 43), and FKS Table 1 controls the reciprocal sum up to 100. From there use \(4\int_{100}^\infty N(t)t^{-3}dt\). FKS Lemma 2.1 and Remark 2.2 give \(N(t)\le t(\log t-\log(2\pi)-1)/(2\pi)+2\log t\) for \(t\ge100\), since the last term exceeds \(R(t)+7/8\) at 100 and thereafter. Also \(N(t)\le t\log t/5\) there: compare the leading coefficient slack times \(t\log t\) with \(R(t)+7/8\) at 100 and thereafter (the quotient of the latter by \(t\log t\) decreases). Integration from \(H\) proves the second estimate. Values and required margin checks are in analytic.py.

## Status

The other files give exact application statements, derivations, source locators, evidence and limitations. Original analytic results and published finite verifications are reused at inherited trust; the three Ramanujan endpoint prime counts and the new Mertens sieve are replayed. No full Lean formalization, source-first PV, independent verification of the QRH source, or claim of global optimality.

