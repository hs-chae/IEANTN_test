# Premises and shared explicit prime-number estimate

Write B0 for the seven pinned originals, with inherited analytic/literature-computation trust, and B1 for B0 plus FOLLOWUP-D02. No full RH is assumed. Put \(v=\log x\), \(\delta(v)=e^{-v}\psi(e^v)-1\), \(H_0=3\cdot10^{12}\). For B0 let \(b=7/8\); for B1 let \(b=27/32\). All arithmetic functions use inclusive cutoffs. Unless explicitly excluded, all intervals are real and endpoints included.

## Exactly how the hypothesis is used

B0 supplies \(\Re\rho\le7/8\) (OpenAIQRH, PDF p. 4, Theorem 1.1 and following paragraph). B1 implies \(\Re\rho\le27/32\) without needing any additional zero-free theorem. For \(\Re s>1\) the Euler product, logarithmic differentiation and integration by parts give
\[
 -\zeta'/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(t)-t)t^{-s-1}dt.
\]
The integral is analytic on \(\Re s>27/32\): its finite part has compact integration range, and on compact substrips the supplied \((1/64)t^{27/32}\log^2t\) majorant gives a uniform integrable bound even after differentiation. Meromorphic uniqueness excludes every zero there (a zero contributes a pole with nonzero residue). The boundary is not excluded. There is no nontrivial real zero: the alternating eta series is positive by pairing on \(0<s<1\), and equals \((1-2^{1-s})\zeta(s)\) by continuation (Dirichlet summation gives local uniform convergence on \(\Re s>0\)). This deduction affects estimates even for \(\log x<200\); the direct bound is not used at such \(x\).

## A convergent density envelope, with real cutoffs

For \(v\ge40\) take \(T=e^{v/2}/6\) in FKS, original PDF p. 8, Theorem 3.2 with the explicit parameters in the sentence immediately after (3.2). Then \(\max(51,v)<T<(e^{v/2}-2)/5\); the truncation uses \(T^*\le2.45T\) and relative remainder \(\le13ve^{-v/2}\). This is not reuse of the questionable Dudek constant (FKS Remark 3.3). The theorem as recorded by FKS has an all-real-\(x\) domain. Platt–Trudgian 1809 Lemma 2 bounds the absolute reciprocal ordinate mass of both signs through \(T^*\) by \(v^2/24+2\), since \(T^*>2\pi\), \(0<\log(T^*/(2\pi))<v/2\) and \(\pi>3\). Zeros on or below the half-line contribute at most this mass times \(e^{-v/2}\). The mass above the line is at most half the total by the zero symmetry used in FKS Proposition 3.6. The finite RH height is from Platt–Trudgian 2004, Theorem 1.

For \(s\in[.77,b)\) put \(p=8(1-s)/3,\ q=5-2s,\ a=1-p,\ h=\log H_0\). Dusart, PDF p. 5, Theorem 2.3 and \(\log(1+u)\le u\) give \(N(s,t)\le 4.9\,3^p t^p(\log t)^q+51.5(\log t)^2\) for \(t\ge H_0\), counting positive ordinates with multiplicities and \(\beta\ge s\). Partial summation to infinity bounds \(2\sum_{\beta\ge s,\ \gamma>H_0}1/\gamma\) by
\[
 D(s)=2\left(\frac{4.9\,3^p h^q e^{-ah}}{a-q/h}
       +51.5\frac{h^2+2h+2}{H_0}\right).
\]
The upper boundary term tends to zero, the lower boundary term is nonpositive, and \((h+w)^q\le h^q\exp(qw/h)\) in the density integral. Here \(a-q/h>0\), and \(D(s)\) decreases with \(s\), by its formula. There are no off-line zeros at the lower boundary \(H_0\).

Let \(s_0=.77\), and let \(s_0<s_1<\cdots<s_n=b\) use spacing .001 until the final possibly shorter interval. Set \(D_i=D(s_i)\) for \(i<n\), \(D_n=0\). Then \(|\delta(v)|\le G_b(v)\) for \(v\ge40\), where
\[
 G_b(v)=(2+13v+v^2/24)e^{-v/2}
      +(1+v^2/48)e^{-(1-s_0)v}
      +\sum_{i=0}^{n-1}(D_i-D_{i+1})e^{-(1-s_{i+1})v}.
\]
In fact for the zeros on the right of the half-line first use a single half-mass bound times \(e^{-(1-s_0)v}\); then add the integral of \(v e^{-(1-s)v}\) times the cumulative mass to the right of \(s\) for \(s_0\le s\le b\). This integral is at most \(\sum_i D_i[e^{-(1-s_{i+1})v}-e^{-(1-s_i)v}]\), bounded by the last sum in \(G_b\) after dropping \(-D_0 e^{-(1-s_0)v}\). Zeros with \(\Re\rho=b\) are covered. Alternative cutoffs/spacings are valid wherever \(a-q/h>0\), but the named numeric results use this grid. B1 clips the nonnegative spectral mixture of B0 by moving each mass to the lesser of its assigned endpoint and \(27/32\), combining the final partial bin accordingly. The gain is strict for \(v>0\).

Refining this partition moves nonnegative masses leftward in \(s\), so every nested refinement improves the pointwise majorant. The exponent-constant Mertens replay uses the finer mesh .000125, aligned with .001. A useful symbolic strengthening is to retain the exact layer integral
\(\int_{s_0}^{b} v e^{-(1-s)v}D(s)\,ds\)
in place of the sum (not drop its negative lower-end term). Equivalently the positive mixture limit is
\(\int_{s_0}^{b} e^{-(1-s)v}(-D'(s))\,ds+D(b)e^{-(1-b)v}\),
minus \(D(s_0)e^{-(1-s_0)v}\). The identity follows by integration by parts and gives a pointwise envelope without arbitrary grid loss. The finer constants were certified using a finite positive mixture so that all-ray monotonic rescaling is immediate.

The direct estimate is never active in this reconstruction. The replay checks \(e^{5v/32}G_{27/32}(v)<1\) at 200 and hence beyond: each weighted term \(v^d e^{-cv}\) is nonincreasing there. In contrast \(v^2/64\ge625\) there. The difference comes from finite RH and the density integral, not from changing the assumed coefficient or threshold.

## Other valid majorants to retain

Use pointwise extrema only where inputs are valid. For \(\psi\) these include:
* CH2 Corollary 1.3, PDF p. 3: \(C(v)=\pi/(3\cdot10^{12})+113.67e^{-v/2}\), all \(x\ge1\). The executable uses the slightly larger exact rational 1.047198e-12 (e.g. \(\pi<3.141594\) from the Machin formula). CH2 Corollary 1.2 permits every \(10^7\le T\le3000175332800\), \(x>\max(T,10^9)\); use its centered signed interval. Corollary 9.3 is another option under its stated height condition. The computations for \(\psi\) in Lemma 9.2, PDF p. 35, are inherited; rounded enclosure \([-1.415,.791]/\sqrt x\) on \(1\le x\le10^{13}\), improved lower endpoint \(-.751/\sqrt x\) on \(10^4\le x\le10^{13}\).
* Platt–Trudgian finite RH, Corollary 1, PDF p. 4: \(|\delta(v)|\le v^2 e^{-v/2}/(8\pi)\) for \(59<x\le2.169\cdot10^{25}\), same relative bound for \(\theta\) for \(599<x\) through that upper limit. Its \(\pi\) estimate is against the usual PV \(\mathrm{li}\), with \(2657<x\) and the same upper limit. The separate sign \(\theta(x)<x,\ \pi(x)<\mathrm{li}(x)\) for \(2\le x\le10^{19}\) is reported on PDF p. 5, §3.3.
* FKS Theorems 1.1–1.2 and Corollary 1.4, Tables 5–6 (PDF pp. 22–23; use upper-enlarged tabulated constants if approximated); Platt–Trudgian 1809 PDF pp. 2–3 Theorem 1 and Table 1, both constant and functional bounds; Dusart Proposition 3.2/Table 1 and Theorem 3.3, PDF pp. 7–9. The \(\theta\) options also include Dusart Theorem 4.2 (PDF p. 11, each stated domain) and Platt–Trudgian 1809 Corollary 1. For direct \(\pi\) also retain Dusart §5.1 and Platt–Trudgian 1809 Corollary 2 on their stated domains. The latter uses its \(\int_2^x dt/\log t\) convention (a fixed \(\mathrm{li}(2)\) offset from PV).
* Dusart Corollary 4.5, PDF p. 13, gives \(0\le(\psi(x)-\theta(x))/x<1.000000147x^{-1/2}+1.78x^{-2/3}\). Its lower endpoint can be improved to \(\theta(\sqrt x)/x\) using any lower \(\theta\) bound. Intersections preserve signed information.

All are reusable in the transport/envelope formulas. The main numerical comparisons are to the strong within-method B0 reconstruction using \(G_{7/8}\), finite-source comparisons and CH2, not a blind baseline. No exhaustiveness over all possible original-source deductions is asserted.
