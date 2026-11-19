# Common premises; D01 is redundant

Let B0 be the exact cumulative seven-paper input, not full RH. Decimals in statements and certificates are exact rationals. The variable x is real except where integer source data are specified. Counts include their right-hand endpoint. Trust tiers: published results (including their published finite computations), new analytic proofs, and reproducible exact arithmetic checks. No Lean or source-first PV is claimed.

## Premise comparison

**B0 alone proves** \(|\psi(x)-x|<.0045\,x^{7/8}(\log x)^2\) for \(\log x\ge200\). This is strictly stronger than D01 at its exact domain. Substitution into any proof from B0+D01 gives a proof from B0; thus the lawful original-assumption and augmented-assumption consequence envelopes are equal on every matched domain in both families. This does not identify a globally optimal bound, nor is it an independent blind baseline run. The new conclusions are input-independent secondary improvements over particular published bounds.

## Exact sources used

* OpenAIQRH, Thm. 1.1 and following paragraph, PDF p. 4: nontrivial zeta zeros have real part at most 7/8, including a possible boundary.
* Platt–Trudgian, *The error term in the prime number theorem*, Lemma 2, p. 4: for \(T\ge2\pi e\) the sum of \(1/\gamma\) over positive ordinates \(\gamma\le T\), with multiplicity, is \((\log(T/(2\pi)))^2/(4\pi)\) with absolute error at most .9321. Lemma 4 there and *The Riemann hypothesis is true up to 3·10¹²*, Thm. 1 p. 2, give finite RH at \(H=3\cdot10^{12}\). The latter's Cor. 1 p. 4 gives the real finite-range estimates, including \(|\theta(x)-x|\le\sqrt{x}(\log x)^2/(8\pi)\) for \(599<x\le2.169\cdot10^{25}\). We only need the printed, possibly loose, π row with log², not a sharper π row.
* FKS, Thm. 3.2, p. 8, with their admissible parameters \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\): for \(u\ge40\) and \(\max(51,u)<T<(e^{u/2}-2)/5\), some \(T\le T^*\le2.45T\) gives
\[
 v(u):=e^{-u}\psi(e^u)-1=-\sum_{|\gamma|\le T^*}e^{(\rho-1)u}/\rho+O^*(2.091u/T).
\]
This is the all-real input, not the older truncated formula discussed in their Remark 3.3. Nontrivial zeros occur in conjugate pairs (for real \(0<s<1\), the paired alternating Dirichlet series is positive and \(\zeta(s)=\eta_{\rm Dir}(s)/(1-2^{1-s})\ne0\)).
* FKS, Cor. 2.9 (2.17), p. 7, Table 8 pp. 26–27, gives \(N(s,V)\le c_1 V^{8(1-s)/3}(\log V)^{5-2s}+c_2(\log V)^2\) at \(V\ge H\) for the tabulated intervals, for \(0<\gamma<V,\ \beta\ge s\). The same expression bounds the count restricted to \(\beta>s,\ 0<\gamma\le V\), by a right limit in V. Lemma 2.1 (2.1), pp. 4–5, and Remark 2.2 give the strip sum for Mertens below.
* CH2, Cor. 1.2, 1.3 p. 3, proof (9.2) p. 36: for finite RH up to \(T\ge10^7\) and \(x>\max(T,10^9)\), the relative ψ bound is \(\pi/(T-1)+\pi^2/(3T^2)+C_T/\sqrt{x}\), where \(C_T=(\log(T/(2\pi)))^2/(2\pi)-\log(T/(2\pi))/(6\pi)\). In particular for \(x\ge1\), the relative bound is \(a+113.67/\sqrt{x}\), \(a=1.048\cdot10^{-12}\), and this also bounds \(|\sum_{n\le x}\Lambda(n)/n-(\log x-\gamma_E)|\). Here \(\gamma_E\) is Euler's constant. Lemma 9.2 p. 35 gives \(-.751\sqrt{x}\le\psi(x)-x\le.791\sqrt{x}\) on \(10^4\le x\le10^{13}\). We do not use the potentially ambiguous normalization in the extracted weighted numerical assertion (9.1).
* Dusart 2018, Prop. 4.3 p. 12, Cor. 4.5 p. 13: \(D(x)=\psi(x)-\theta(x)>.9999\sqrt{x}\) for \(x\ge121\); \(0\le D(x)<1.000001\sqrt{x}+1.78x^{1/3}\) for \(x>0\) (upper first coefficient rounded out). The proof of Cor. 4.5 quotes \(\theta(x)<x\) up to \(1.39\cdot10^{17}\); proof of Thm. 5.1 p. 15 uses \(\pi(x)<\operatorname{li}(x)\) below that endpoint. We only use the signs at \(x\ge e^{20}\), and for π at \(x\ge e^{36}\), through \(\log x=39.47\).

## Proof of redundancy

In FKS 3.2 set \(T=e^{u/6}\) for \(u\ge200\). It exceeds \(u,51\) and \(5T+2<e^{u/2}\); the exponential-to-linear ratios increase there. Since \(2.45<2\pi\) and \(T^*\ge2\pi e\), the zero sum bound and QRH give
\[
 |v(u)|e^{u/8}/u^2
 \le 1/(72\pi)+1.8642/u^2+(2.091/u)e^{-u/24}<.0045.
\]
The last two summands decrease and \(\pi>25/8\) suffices at 200, as checked in certify.py.

## Stronger original-input ψ and θ majorants

For \(u\ge150\), take \(T=e^{u/3}\) (same admissibility tests). Zeros with \(\beta\le.80\) contribute at most \(.018u^2e^{-u/5}\), since \(u^2/(18\pi)+1.8642\le .018u^2\). The rest have \(|\gamma|>H\). Put \(d=1-8(1-s)/3,\ r=5-2s,\ \lambda=\log H\). Partial summation of \(N(s,t)\), zero at H by finite RH, gives
\[
 b(s):=2\sum_{\beta>s,\ \gamma>H}1/\gamma
 \le 2\left[\frac{c_1H^{-d}\lambda^r}{d-r/\lambda}
       +\frac{c_2H^{-1}\lambda^2}{1-2/\lambda}\right].
\tag{1}
\]
Indeed \(N(s,V)/V\to0\); integrate \(N(s,t)/t^2\) and use \(z=\log t\), bounding the two integrals by their endpoint integrands divided by lower bounds for their negative logarithmic slopes. For every tabulated subinterval \([s,s']\) in certify.py, use the left threshold in (1) and multiply by \(e^{-(1-s')u}\) to bound the group \(s<\beta\le s'\). Together with the low zeros and Perron error this gives DEN. Each triple (b,m,c) in the script represents \(b u^m e^{-cu}\); a list represents a sum.

A stronger continuous layering bound uses the uniform \(c_1,c_2=11.077,3.693\) on \([.80,.875]\). The magnitude of the log derivative of the first term of (1) is
\[
 (8/3)\lambda+2\log\lambda+(8/3+2/\lambda)/(d-r/\lambda)<91.2
\]
(the last summand is maximal at .80); the second term is constant. At .875 the RHS of (1) is <.01058. The checks use \(28.7296<\lambda<28.7297\), \(3.3579<\log\lambda<3.36\) with outward rounding. So \(b(s)\le .01058 e^{91.2(.875-s)}\). For β>.80 expand \(e^{(\beta-1)u}=e^{-.20u}+u\int_{.80}^{.875}{\bf1}_{s<\beta}e^{-(1-s)u}ds\). Summing and integrating the bound on b yields at most \(.01058 u e^{-u/8}/(u-91.2)\), discarding a negative term. Hence
\[
 G(u)=.018u^2e^{-u/5}+2.091u e^{-u/3}
             +.01058\,\frac{u}{u-91.2}e^{-u/8}
\]
bounds \(|v(u)|\) for \(u\ge150\); retain its minimum with DEN and the CH bound (the CH bound is available already at u=0). Write \(\eta(u)=e^{-u}\theta(e^u)-1\); it equals \(v(u)-e^{-u}D(e^u)\). The upper bound for the subtracted term is \(P(u)=1.000001 e^{-u/2}+1.78 e^{-2u/3}\). In particular \(|\eta(u)|\le K(u)e^{-u/8}\) for \(K(u)=e^{u/8}(G(u)+P(u))\), decreasing for \(u\ge150\). This removes the entire log² loss of the quick bound, using original density results and QRH, not D01.

For all exp checks, certify.py halves the positive argument until ≤1, bounds \(e^{-q}\) by alternating sums of orders 37 and 38, rounds out at scale \(10^{72}\) and squares back with directed integer rounding. E and EP respectively bound \(e^{-q}\) and \(e^q\) above (the latter is used only with positive denominator). Numerical inequality checks use rationals, not floating samples.



For the refined Ramanujan transfer, also use a two-slope layer. On \([.855,.875]\) the same log-derivative test with left .855 yields \(88.9\); on \([.80,.855]\) use \(91.2\). Set \(M_1=91.2,M_2=88.9,d_0=.02\). After factoring out \(.01058 e^{-u/8}\) the layer bound can be reduced to
\[
 \frac{u}{u-M_2}+
 \frac{(M_1-M_2)u\,e^{-d_0(u-M_2)}}{(u-M_1)(u-M_2)}.
\]
Indeed in the layer integral use the upper slope \(M_2\) up to distance \(d_0\) from .875, and then continue continuously with slope \(M_1\) in the distance variable; bound the second integral up to infinity. The initial term at distance .075 is absorbed by the positive continuation beyond .075 (the latter contributes a factor \(u/(u-M_1)>1\)). The displayed expression is the resulting integral times u. The two terms are positive and decreasing; the certificate keeps the simpler one-slope branch as well.
