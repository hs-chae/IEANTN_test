# Common analytic engine

Put \(v=\log x,\ e_\psi(v)=\psi(e^v)e^{-v}-1,\ H=3\cdot10^{12},\ H_* =3000175332800\). B0 is the complete common original-paper foundation, including OpenAIQRH Theorem 1.1 (PDF p. 4) and Platt–Trudgian FiniteRH Theorem 1 (PDF p. 2). Put \(b_0=7/8\). B1 adds exactly FOLLOWUP-D02, with \(b_1=27/32\). Bounds below include nonintegers. Functions counting primes and prime powers take their right-hand values.

## Using FOLLOWUP-D02 before its numerical threshold

For \({\rm Re}\,s>1\), the Euler product and summation by parts give
\[
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(t)-t)t^{-s-1}\,dt.
\]
The finite initial integral through \(e^{200}\) is harmless; beyond it the **exact** extra majorant gives locally uniform convergence, also under differentiation, for \({\rm Re}\,s>27/32\). The identity extends there meromorphically (e.g. \(\zeta(s)=s/(s-1)-s\int_1^\infty\{t\}t^{-s-1}dt\) for \({\rm Re}\,s>0\)). Any zero in that half-plane would produce a nonremovable log-derivative pole. Thus \(\beta\le b_1\), including possible equality. This deduction is how the added input strengthens estimates even below \(e^{200}\), not a numerical extrapolation. Its power, not the particular finite coefficient, suffices for this deduction. The exact coefficient and threshold are also used in the direct branch. For real \(0<s<1\) the alternating Dirichlet series \((1-2^{1-s})\zeta(s)\) is positive by grouping pairs; hence no real nontrivial zero was omitted. Nonreal zeros are counted with multiplicity and conjugation symmetry.

## Real explicit formula: avoiding a disputed truncation

FKS Theorem 3.2 (PDF p. 8) gives the signed Cully-Hugill–Johnston form with admissible parameters \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\). For real \(x=e^v,\ v\ge61\), use \(T=\sqrt x/6\). It satisfies \(\max(51,\log x)<T<(\sqrt x-2)/5\), and gives a height \(T^*\in[T,2.45T]\) such that
\[
 e_\psi(v)=-\sum_{|\gamma|\le T^*}\exp((\rho-1)v)/\rho+r(v),
 \qquad |r(v)|\le 12.546\,v e^{-v/2}<3v^2e^{-v/2}. \tag{1}
\]
The upper height is below \(\sqrt x\). PT 1809.03134v2 Lemma 2 (PDF p. 4) says \(\sum_{0<\gamma\le t}1/\gamma\le (\log(t/(2\pi)))^2/(4\pi)+0.9321\) for \(t\ge2\pi e\). Thus the two-sided reciprocal mass through \(T^*\) is at most \(.04v^2+2\), and through \(H\) it is less than 117 (certificate.py). All zeros through \(H\) are on \(\beta=1/2\). Equation (1) is only used **pointwise**, with no differentiation or integration of its variable cutoff. In particular it avoids relying on the error-marked Dudek truncation proof discussed in FKS Remark 3.3. The signed integral is proved separately.

## Density compression (main version)

Use FKS Corollary 2.9, (2.17), and Table 8 (PDF pp. 7–8, 26) **at original-paper trust**. For \(3/4\le s\le7/8,\ t\ge H\), the table gives \(N(s,t)\le12t^{8(1-s)/3}(\log t)^{5-2s}+5(\log t)^2\) by rounding upwards. This is reuse of the stated corollary, not regeneration of its optimized table. There is an apparent notation/hypothesis discrepancy: Theorem 2.7 says \(\delta\ge1\) while the table labels a parameter \(\delta\) near .31. We do not use this table as an *independently* proved density result. The fallback below is independent of it.

With \(h=\log H,\ \alpha=(8s-5)/3,\ q=5-2s\), put
\[
 Z(s)=24h^q e^{-\alpha h}/(\alpha-q/h)+10(h^2+2h+2)/H .
\]
Partial summation bounds \(\sum_{\beta>s,|\gamma|>H}1/|\gamma|\) by \(Z(s)\), since \((h+t)^q\le h^q e^{qt/h}\), the denominator is positive, and the second density integral is elementary. If the count uses \(\beta\ge s\) it still bounds this sum. This estimate does not add fictitious off-line mass at \(H\).

Take the grid \(s_0=3/4\), \(3/4+j/2000<b\), the additional point \(27/32\) if \(b=b_0\), and last point \(s_m=b\). Write \(d=1-b\). Layering the high-zero weights gives
\[
 L_b(v)=(.04v^2+2)e^{-v/4}+(3v^2+117)e^{-v/2}
 +\sum_{j<m}Z(s_j)\big(e^{-(1-s_{j+1})v}-e^{-(1-s_j)v}\big).
 \tag{2}
\]
A zero above \(s_0\) is covered up to the next grid point; one exactly at a grid point is covered through that point. The base layer covers all high zeros and the second term covers low zeros and the remainder. Thus \(|e_\psi(v)|\le L_b(v)\). Put \(E_b(v)=L_b(v)+Z(s_0)e^{-v/4}\): the sum in this positive version is \(\sum_{j<m}(Z(s_j)-Z(s_{j+1}))e^{-(1-s_{j+1})v}\), with \(Z(s_m)=0\) **only in that sum**. Coefficient positivity is checked on both grids (and also follows from monotonicity of the displayed \(Z\)). The grids coincide below \(b_1\), so \(L_{b_1}(v)<L_{b_0}(v)\) on their entire common domain.

Dusart Cor. 4.5 (PDF p. 13) gives \(0\le\psi(x)-\theta(x)<(1+1.47\cdot10^{-7})\sqrt x+1.78x^{1/3}\). For \(v\ge24\) the relative cost is at most \(2e^{-v/2}\). Let \(E_b^\theta=E_b+2e^{-v/2}\) (certificate.py: ts). For any \(a\ge160\), \(e^{dv}E_b^\theta(v)\) decreases termwise; write \(C_b(a)=e^{da}E_b^\theta(a)\). This is an entire-ray bound. Refining the *zero-level* grid is harmless; no finite sample of x-values proves a ray.

**Local-constant refinement.** Use the same proof with grid \(3/4+j/4000\) and an extra shared split at \(b_1\). In each Table 8 interval the two local constants are rounded upwards to the values in refine.py, replacing \(12,5\) in \(Z\). Because the count of high zeros decreases with \(s\), for each \(s\) one may take the minimum of this new majorant at \(s\) and the earlier interval endpoints. This is a nonincreasing valid function (each row majorant decreases inside its interval). It handles upward row jumps without negative coefficients. The same positive-sum and monotonicity arguments apply, with empty or zero-weight layers harmless. The original uniform construction is retained as a simpler independently replayable variant.

## Density-free alternatives and signed moments

Dropping density entirely, (1) yields for \(v\ge61\)
\[
 |e_\psi(v)|\le(.04v^2+2)e^{-dv}+(3v^2+117)e^{-v/2}. \tag{3}
\]
B1 can also use \(v^2e^{-5v/32}/64\) for \(v\ge200\) exactly.

For \(k(v)=1\) or \(v^{-1}+v^{-2}\), a signed tail bound valid for \(L\ge61\) is
\[
 \left|\int_L^\infty k(v)e_\psi(v)\,dv\right|
 \le k(L)\left[6e^{-L/2}+(400/H)e^{-dL}\right]\le k(L)B_d(L),
 \quad B_d(L)=[4+6(L^2+4L+8)]e^{-L/2}+(400/H)e^{-dL}. \tag{4}
\]
The larger \(B_d\) is deliberately retained in the table certificates. This result does not use the density corollary and does not assume a regular cutoff in (1).

**Proof of (4).** For \(F(s)=-\zeta'(s)/\zeta(s)\), integrate the elementary Perron kernel:
\[
 \int_1^x \psi(t)t^{-2}dt
 =\frac1{2\pi i}\int_{2-i\infty}^{2+i\infty}\frac{F(s)x^{s-1}}{s(s-1)}\,ds .
\]
The scalar kernel applied to \(x/n\) gives \(n^{-1}(1-n/x)\) if \(n\le x\), zero otherwise, by closing to the left or right; at equality the continuous kernel is zero. Absolute convergence on 2 justifies the interchange. By functional-equation reflection (also used in FKS (3.10)), every zero has \(\beta\ge1-b\ge1/8\). Shift to \({\rm Re}\,s=1/10\), crossing the double pole at 1 and the nontrivial zeros only. CH2 Prop. B.8, (B.8) (PDF pp. 46–47) with \(\sigma_+=2,\ a=1\) and the zero count in FKS Lemma 2.1 and Remark 2.2 justify horizontal limits: choose heights in \([N,N+1]\) at distance \(\gg1/\log N\) from all ordinates there or within 1 of that interval, possible by the \(O(\log N)\) count. Then \(F\) is \(O(\log^2 N)\) across the strip at these heights, and the horizontal integrals vanish. Citing (B.8) here requires no finite RH at the chosen heights.

Here are ample explicit vertical bounds for the remainder. For \(|t|\le1000\), subtract CH2 (B.9) at \(s=.1+it\) and \(2+it\). For \(|\gamma|\le2000\) use at most 20000 zeros by PT Lemma 2, each reciprocal difference bounded by \(40+1\) from the horizontal separations. For \(|\gamma|>2000\) the difference is \(\le8/\gamma^2\). The digamma difference costs less than 2 by its convergent partial-fraction difference on \({\rm Re}\,z\ge1\) (or the Euler product for \(\Gamma\)); the pole difference costs less than 3, and \(|F(2+it)|\le\sum_{n\ge2}\log n/n^2<3\). Thus \(|F(.1+it)|<10^6\) there. For \(|t|\ge1000\), (B.8) yields \(|F(.1+it)|<1000\log |t|\): the nearby count is \(<20\log|t|\) by FKS Lemma 2.1 and its Rosser constants in Remark 2.2, each denominator costs at most 40, and the remaining explicit terms with \(\sigma=.1,\sigma_+=2,\ a=1\) are \(<20\log|t|\). Integrate \(1/|s(s-1)|\le 100/9\) for \(|t|\le1\) and \(\le1/t^2\) elsewhere. The resulting vertical integral is \(<5\cdot10^6 e^{-.9L}\).

The residue at 1 is \(L-1-\gamma\), by the Laurent expansion (the constant term of \(\zeta\) is Euler's constant by summation of the defining series against the integral). Each zero contributes \(-e^{(\rho-1)L}/(\rho(\rho-1))\), with multiplicity. For \(0<\gamma<100\) FKS Cor. 2.3 Table 1 (PDF p. 5) gives reciprocal sum \(<.593\), so the square sum there is \(<.593^2\). For \(t\ge100\), \(A(t)=\sum_{0<\gamma\le t}1/\gamma\le(\log t)^2/12+1\) by PT Lemma 2. Partial summation bounds \(\sum_{\gamma\ge Y}1/\gamma^2\) by \(((\log Y)^2+2\log Y+2)/(12Y)+1/Y\) for \(Y\ge100\). The total positive-ordinate square sum including the low zeros is \(<1\); twice its tail above \(H\) is \(<200/H\). Thus the residue sum is absolutely convergent and tends to zero at infinity. Subtract its limit from the formula to get
\[
 \left|\int_L^\infty e_\psi(v)dv\right|
 \le 2e^{-L/2}+(200/H)e^{-dL}+5\cdot10^6 e^{-.9L}
 \le 3e^{-L/2}+(200/H)e^{-dL}.
\]
For decreasing \(k\), integrate by parts against this primitive and use the same decreasing upper majorant inside the integral: the endpoint and the integral together cost at most twice that majorant times \(k(L)\). This proves (4), including the stronger displayed version.

## Other original controls and trust

The comparison retains published direct results on their exact domains. CH2 Cor. 1.2, 1.3 (PDF p. 3), Prop. 9.1 (p. 34), and Cor. 9.3 (p. 36) are important: Cor. 1.2 applies for **every** \(10^7\le T\le H_*\) and \(x>\max(T,10^9)\). Write
\[
 A=1.048\cdot10^{-12},\quad
 C_T=(\log(T/(2\pi)))^2/(2\pi)-\log(T/(2\pi))/(6\pi).
\]
The all-domain CH2 bound is at most \(A+114e^{-v/2}\) for both relative ψ and the centered von Mangoldt weighted sum. The Cor. 1.2 ψ bound may use \(a_T+C_Te^{-v/2}\) with \(a_T=\pi/(T-1)+\pi^2/(3T^2)\), by their inequality \(t\coth t-1\le t^2/3\) in (9.2). The weighted companion uses \(\pi/(T-1)\), no coth correction. PT FiniteRH Cor. 1 (PDF p. 4) gives its ψ, θ and π bounds through \(2.169\cdot10^{25}\); all transfers of its π bound use the PV logarithmic integral (Dusart PDF p. 13; Dudek–Platt Thm. 3.1). PT 1809.03134v2 also uses a shifted integral starting at 2; when using its Cor. 2, include the constant \(|\operatorname{li}(2)|<2\) as a safe normalization allowance.

This portfolio is written proof with ordinary reproducible interval checks, using the named literature tiers, not formal Lean or source-first PV. Comparisons use a within-method reconstruction, not an independent blind baseline run.
