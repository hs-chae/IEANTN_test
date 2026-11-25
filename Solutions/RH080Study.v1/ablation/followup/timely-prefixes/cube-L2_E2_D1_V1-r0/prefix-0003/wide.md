# Whole-cube smoothing: written derivations

## Strict-open normalization and explicit formula

Let \(n\ge1250,\ a=n^3,\ b=(n+1)^3,\ l=\log n,\ L=(\log a+\log b)/2,\ d=(\log b-\log a)/2\). The inequalities \(1-1/u\le\log u\le u-1\) give \(1.5/(n+1)\le d\le1.5/n\). In particular \(0<d\le.0012,\ e^{L-2d}\ge2,\ b\le3a,\ \log a>2,\ e^{L/2}\ge n\sqrt n\). Take an even continuous kernel \(0\le K\le1\) supported on \([-1,1]\), zero at both endpoints; put \(H(v)=\int K(u)\cos(vu)\,du\) (radian convention). A prime in the weighted sum has weight at most \(3l/(n\sqrt n)\) because \(\log t/\sqrt t\) decreases for \(\log t>2\). A lower bound \(3c\sqrt n\) on the weighted prime sum therefore gives the claimed normalized count. No endpoint prime enters.

Under RH the Green source formula gives the exact identity
\[
 \sum_{a<m<b}\Lambda(m)K((\log m-L)/d)/\sqrt m
 = d e^{L/2}\int K(u)\cosh(du/2)\,du
 -\Re\sum_{\rho}m_\rho d e^{i\gamma L}H(d\gamma)
 -\int_a^b\frac{K((\log t-L)/d)}{\sqrt t\,t(t^2-1)}\,dt.
\]
Here \(\rho\) runs over nontrivial zeros with multiplicities \(m_\rho\) and \(\gamma=\Im\rho\). Derivation with the exact *smooth* Green predicate: convolve \(K\) with nonnegative even smooth probability bumps of radii at most 1 tending to 0. For the resulting \(K_j\), apply the formula at \(X=2\) to \(W(t)=K_j((\log(2t)-L)/d)/\sqrt{2t}\) on \(t>0\) and zero otherwise. It is smooth, compactly supported in \(t\ge1\) since \(e^{L-2d}\ge2\). Substituting \(2t=e^{L+du}\) gives the pole term by evenness and gives the critical packet with the extra bump cosine multiplier (absolute value at most 1 and tends to 1). The simple trivial zeros at \(-2,-4,\ldots\) give the displayed integral with a minus sign, by geometric summation uniformly on the fixed enlarged support. These are the same all-zero conventions as OcticZeroDecomposition.lean, OcticTrivialSeries.lean and OcticMellinNormalize.lean. For the limit of the weighted sum only finitely many integers occur; the integrals pass by bounded convergence, and the zero series is dominated by a summable \(O(\gamma^{-2})\) envelope at fixed \(d\) (BPT gives \(N_+(T)=O(T\log T)\)); for the octic one may directly use the inherited Nicolas summability bound. There are no nontrivial \(\gamma=0\) terms by the assigned real-zeta nonvanishing result used in OcticZeroPairing.lean. Conjugate pairing preserves multiplicities. The nonnegative trivial integral is less than .001: its integrand is at most \(1/(2300a)\) for \(t\ge a\ge24\), and \(b-a\le2a\).

For \(k\ge2\) the number of eligible integer prime-power bases is at most \(b^{1/k}-a^{1/k}+1\le2d\sqrt b/k+1\) by the mean-value bound for exp and \(b^{1/k}\le\sqrt b\). Each weight is at most \(\log b/(k\sqrt a)\), and no powers occur for \(k>J=\lfloor\log b/\log2\rfloor\). Sum \(k^{-2}\) and \(k^{-1}\) from 2 to \(J\) using upper bounds 1 and \(\log J\), respectively. Thus the prime-power correction is
\[
 P\le (3\log(n+1)/(n\sqrt n))(2d\sqrt b+\log J)<10l/n.
\]
Indeed \(\sqrt b\le(n+2)\sqrt n\) by squaring, \(\log(n+1)\le l+1/n,\ \log2>1/2\), and \(J\le6(l+1/n)\le n\): use \(l/n\le7.14/1250\) on \(n\ge1250\). Both this ratio and \(l/\sqrt n\le7.14/35.35<.203\) decrease there by differentiation (\(l>7\)). Therefore \(2d\sqrt b<3.005\sqrt n,\ 3\log(n+1)\le3.001l\). In particular \(P<.06\), and \(P<.03\) from 2980, where \(\log2980<8\).

## Octic: the unchanged package

Take \(K(u)=\max(0,1-u^8)\), mass \(16/9\). Apply the inherited zero estimate **before** specialization to \(1.03\le C\le16\): /representation/source/OcticMomentTransport.lean, full_zero_bound_in_terms_of_moments; OcticOptimizedCertified.lean, optimized_moment_caps; OcticFamilyMoments.lean, family_augmented_residual_lt. Set \(C=2(de^{L/2}+1)/L\), so the inherited \(\delta\) is \(d\). The hypotheses at these locators require \(0<d,12d\le1,d\le3/2500\) but no \(C\le16\). Since \(2\pi d<1\), both moment caps enter with nonnegative coefficients and the *augmented residual* is less than .15. Thus the absolute zero sum is strictly less than
\[
 1.8203\log(1/(2\pi d))+1.457+.15 .
\]
The count proof does **not** substitute a disallowed \(C\) into the inherited count family. It aligns the original weight to both cube endpoints and separately bounds the losses.

Use \(\log(1/(2\pi d))\le l+1/n-\log(3\pi)\) and \(\log(3\pi)>2.24\). Adding prime-power and trivial estimates, the total error is less than \(1.8203l-2.408\) for \(n\ge1250\), or \(1.8203l-2.438\) for \(n\ge2980\). Since \(\cosh\ge1\), the main term divided by \(3\sqrt n\) is at least \((8/9)n/(n+1)\). The functions \((1.8203l-B)e^{-l/2}\) for the two constants \(B\) decrease on \(l\ge7\) by differentiation. At each onset use \((n_0,T,U)=(1250,35.35,7.14),(2000,44.72,7.601),(2980,54.58,8)\), where \(T\le\sqrt{n_0}, U\ge\log n_0\). Rational checks in exact.py prove that \((8/9)n_0/(n_0+1)-(1.8203U-B)/(3T)\) is above .788, .802, .8145, respectively. This proves the three real rays.

## Trapezoid: stronger large ray and hybrid with Büthe

Let \(\eta=.003\). Convolve the indicators of \([-(1-\eta),1-\eta]\) and \([-\eta,\eta]\), divided by \(2\eta\). This kernel is an intersection length divided by \(2\eta\): it is continuous, supported on \([-1,1]\), zero at the endpoints, takes values in \([0,1]\), and has mass \(2(1-\eta)\). Its radian transform is \(2\sin((1-\eta)v)\sin(\eta v)/(\eta v^2)\) for \(v\ne0\). Hence \(|H(v)|\le g(|v|)\), where \(g(v)=2,\ 2/v,\ 2/(\eta v^2)\) on \([0,1], [1,1/\eta], [1/\eta,\infty)\), respectively.

Let \(n\ge n_0=2154000\). The BPT bound for the closed positive count (publishedBound_of_offOrdinate, OcticBPTSourceEndpoint.lean; BPT, JNT 238 (2022), Cor.1 p.743) gives
\[
 N_+(T)\le T/(2\pi)\big(\log(T/(2\pi))-.9\big)\quad (T\ge1/d).
\]
Here \(1/d\ge2n/3>10^6\), and \(7/8+.28\log T\le T/(20\pi)\) there by \(\log T\le\sqrt T,\ \pi<4\). The BPT \(T\log T\) growth itself gives spectral convergence without Nicolas. Pairing and nonnegative summation/integration with \(g(y)=\int_y^\infty(-g'(v))\,dv\) bound the zero sum by
\[
 2d\int_1^\infty(-g'(v))N_+(v/d)\,dv
 \le (2/\pi)\{(q+2)h+h^2/2+2q+2\},
\]
where \(h=\log(1/\eta), q=\log(1/(2\pi d))-.9\). Indeed \(-vg'(v)=2/v\) on \([1,1/\eta]\) and \(4/(\eta v^2)\) afterwards; integrate against \(q+\log v\) with outer factor \(1/\pi\). Small ordinates were not discarded: they are included in the cumulative count under the integral.

We have \(q\le l-3.139,\ h<5.81,\ \pi>3.1415\). Thus the total error is bounded by
\[
 A(l)=(2/3.1415)\big((l-3.139+2)5.81+5.81^2/2+2(l-3.139)+2\big)+.031 .
\]
This majorization is increasing in \(q\) and \(h\) at the upper bound for \(q\), which is positive. The function \(A(l)e^{-l/2}\) decreases for \(l\ge14\) since \(A(14)>2A'(l)>0\). The normalized main term is at least \(.997n/(n+1)\). Use \(14<\log n_0<14.583,\ \sqrt{n_0}>1467\); the exact strict comparison \(.997 n_0/(n_0+1)-A(14.583)/(3\cdot1467)>.9796\) is checked in exact.py. On the left slab \(1024\le n\le n_0\), Büthe gives a bound above \((1-(19/30)/32)/(1+1/(1024\cdot6))>.9796\), by the next section. The domains meet, and no Schoenfeld assumption is used for this hybrid.

## Secondary endpoints and earlier tradeoffs

For \(y<b\) sufficiently near \(b\), all integers \(p<b\) satisfy \(p\le\lceil b\rceil-1\le y\), so \(\theta(y)-\theta(a)=\sum_{a<p<b}\log p\le N(a,b)\log b\). The continuous lower bound for \(\theta(y)\) passes non-strictly to the left limit; the strict other endpoint bound at \(a\) preserves strictness. The resulting right sides for \(N(a,b)\log b\) are \(b-a-1.95\sqrt b+.05\sqrt a\) and \(b-a-E(a)-E(b)\), respectively, where \(E(x)=\sqrt x(\log x-2)\log x/(8\pi)\).

With the cube substitutions, Büthe's numerator is at least \(3n^2-1.9n\sqrt n\) for \(n\ge11\): use \(\sqrt b\le(n+2)\sqrt n\) and \(3n-3.9\sqrt n\ge0\). Its normalized count then exceeds \((1-(19/30)/\sqrt n)/(1+1/(nl))\). At integer onsets \(11,25,49,169,400,1024\), respectively, this gives .75, .86, .90, .95, .9669, .9796 on the finite slab to 2154000 (exact.py). For Schoenfeld, the geometry gives \(3n^2\log(n+1)/l\le b-a\) for \(l\ge1\), while the total normalized error is at most \((2+2r)l(3l-2+3r)/(8\pi\sqrt n)\) for fixed \(r\ge1/n\), by \(\sqrt b\le(n+2)\sqrt n\) and \(\log(n+1)\le l+r\). The function \(l(3l-2+3r)e^{-l/2}\) decreases from \(l=5\) by differentiation; see CubeSecondary.lean for the quadratic/Taylor proof. The secondary hybrid uses the minimum of the finite-slab and tail coefficients, preserving both domains.
