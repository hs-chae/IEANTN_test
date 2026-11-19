# A stronger direct psi majorant from B0

Put \(v=\log x\), \(b=7/8\), \(H=3\cdot10^{12}\), and \(h=\log H\). We use OpenAIQRH, PDF p.4 Theorem 1.1 (also the transfer in Proposition 11.3, pp.84–85), only for \(\beta\le b\) for the nontrivial zeros of zeta. Boundary zeros are included. Platt–Trudgian finite RH, PDF p.2 Theorem 1, gives RH through \(H\), inclusive. Ordinates and zeros are counted with multiplicity. The standard symmetry used below is also used explicitly in FKS Proposition 3.6 (pp.9–10). There are no real nontrivial zeros: for \(0<s<1\) the alternating Dirichlet series is positive by pairing, and equals \((1-2^{1-s})\zeta(s)\) by continuation (locally uniform convergence in \(\Re s>0\) by summation by parts).

## Exponential density majorant

Use FKS, Corollary 2.9 (PDF p.7), equation (2.17) and Table 8 (the first block with \(a_1=0.77\), PDF p.26). With \(\alpha(s)=(8s-5)/3,\ q(s)=5-2s\), one has \(N(s,Y)\le cY^{1-\alpha(s)}(\log Y)^{q(s)}+d(\log Y)^2\) for \(Y\ge H\). For all \(.8\le s\le b\) the uniform \(c=11.076,\ d=3.694\) work (roundings upward). Also at the following specific \(s\), the respective \(c,d\) work:
\[
\begin{array}{c|rrrrrr}
s&.78&.80&.82&.84&.86&.87\\
c&7.798&8.162&8.928&9.747&10.620&11.076\\
d&4.101&3.694&3.534&3.373&3.213&3.133
\end{array}
\]
The row for \(.78\) is the row for \([.75,.80]\). The others use the row starting at the displayed \(s\). No improved subconvexity variant from the second block of Table 8 is required.

For \(y\ge h\), summation by parts using density gives
\[
 2\sum_{\beta\ge s,\ \gamma\ge e^y}\gamma^{-1}
 \le 2c\int_y^\infty u^{q(s)}e^{-\alpha(s)u}du
       +2d\int_y^\infty u^2 e^{-u}du .
\]
The upper boundary contribution tends to zero; drop the nonpositive lower boundary contribution using the count with \(\gamma<e^y\). This includes a zero exactly at the cutoff. Write \(W(s,y;c,d)\) for the bound obtained by replacing the first integral with \(y^qe^{-\alpha y}/(\alpha-q/y)\) (when the denominator is positive), the second with \(e^{-y}(y^2+2y+2)\). The first replacement uses \(u^q\le y^q e^{q(u-y)/y}\).

At \(y=h\) let \(B(s)\) instead be the integral bound with uniform \(c,d\) and without the tangent replacement. Its logarithmic rate of decrease in \(s\) on \([.8,b]\) is at most 92: for the first integral the logarithmic derivative in magnitude is the mean of \((8/3)u+2\log u\) under the density \(f(u)=u^q e^{-\alpha u}\) on \(u\ge h\). Since \(f(u+z)\le f(u)e^{-(\alpha-q/h)z}\), the mean of \(u-h\) is at most \(1/(\alpha-q/h)\). Use \(\log u\le\log h+(u-h)/h\), \(\alpha\ge7/15,\ q\le3.4\). The constant second integral can only reduce this derivative. The inequality at these constants is checked in cert.py density(). At \(s=b\), the order-four Taylor polynomial of \(u^{13/4}\) about \(h\) is an upper bound for \(u\ge h\) (negative fifth derivative). Integrating it yields
\[
 B(b)\le 2c h^q e^{-\alpha h}\sum_{j=0}^4
   {q^{\underline j}\over h^j\alpha^{j+1}}
  +2d e^{-h}(h^2+2h+2)<0.010445 .
\]
Here \(q^{\underline 0}=1\). Therefore \(B(s)\le 0.010445\,e^{92(b-s)}\).

For \(v\ge100\), summing by layers on the high zeros gives
\[
 2\sum_{\beta\ge.8,\ \gamma>0}{e^{(\beta-b)v}\over\gamma}
 \le 0.010445\Big[1+\frac{92}{v-92}(1-e^{-(v-92)(b-.8)})\Big]
 \le 0.010445\,\frac{v}{v-92}.
\]
Indeed, write \(e^{(\beta-b)v}=e^{(.8-b)v}+\int_{.8}^{\beta}v e^{(s-b)v}\,ds\), then apply \(B(s)\) to the nonnegative sums. These bounds also hold with \(1/|\rho|\).

## Explicit formula and low zeros

Use FKS Theorem 3.2, PDF p.8, equation (3.2), with its **stated admissible tuple** \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\), a result reported there from Cully-Hugill–Johnston. This is source reuse, not independent certification of that result. We do not use the disputed earlier truncation discussed in FKS Remark 3.3. For \(v\ge100\), \(T=e^{v/4}\) and \(T=e^{v/3}\) each satisfy \(\max(51,v)<T<(e^{v/2}-2)/5\). The formula has a cutoff \(T^\star\in[T,2.45T]\) and relative remainder at most \(2.091\,v/T\), for every real \(x\) in the stated range. The actual cutoff can depend on \(x\).

For \(2\sum_{0<\gamma\le T^\star}1/\gamma\), use FKS Corollary 2.3, Table 1 row \(T_0=100,S_0=0.5922435112\), and (2.1) with Remark 2.2's first constants (PDF p.5). For \(Y\) just above the cutoff, \(z=\log Y\), the bound is less than \(0.16 z^2-0.58 z+1.40\): expand (2.1) as \((z-\log100)((z+\log100)/2-\log(2\pi))\) times a prefactor less than .160, use positivity and \(\log(2\pi)>1.83\), discarding the negative constant from the product. See mcert.py basics(). Let \(Y\) tend to the cutoff from above to include possible equality. Then \(z<v/4+1\) or \(z<v/3+1\), respectively. The quadratic is increasing here and bounded by \(v^2/100\) or \(.018v^2\), respectively, by expansion at these upper endpoints. Symmetry pairs each \(\beta>1/2\) with a \(\beta<1/2\) at the same ordinate, permitting only half the total absolute ordinate sum for such zeros.

The resulting direct majorant for \(v\ge100\) is
\[
 q_\psi(v)= \frac{v^2}{100}e^{-v/2}
    +\frac{v^2}{200}e^{-v/5}
    +0.010445\,\frac{v}{v-92}e^{-v/8}
    +2.091\,v e^{-v/4}.
\]
The summands come from \(\beta\le1/2\), \(1/2<\beta<.8\), \(.8\le\beta\le b\), and the remainder. Thus \(|\psi(e^v)/e^v-1|\le q_\psi(v)\).

For subsequent use write \(p(v)=1.000000147e^{-v/2}+1.78e^{-2v/3}\). Dusart Corollary 4.5 (PDF p.13), also explicitly in PT (5) (PDF p.2), gives \(0\le(\psi-\theta)(e^v)/e^v<p(v)\). Proposition 4.3 (Dusart PDF p.12) gives the lower bound \(.9999e^{-v/2}\) at \(e^v\ge121\). The function \(e^{v/8}(q_\psi(v)+p(v))\) is decreasing for \(v\ge200\) term by term; its value at 200 is certified \(<.020\). Both psi and theta consequently have relative error \(<.020e^{-v/8}\) there. This proves the D01 implication, with factor \(625/.020=31250\) even at its left endpoint. No D01 use at earlier arguments than \(e^{200}\) is lawful or made.

## Limits and attempts

The crude approach applying only \(\beta\le7/8\) and summing all truncated \(1/|\gamma|\) gives a log-squared factor and a much poorer medium-range join. Finite RH alone leaves a plateau in the CH2 bounds (or an unlawful increase of verified height if used beyond its domain). The density split, ordinate total and integrated high-zero count remove both defects. CH2 Theorem 1.1 would require mixed-spectrum estimates if used beyond the verified height; applying its RH-specialized Proposition 9.1 there would be invalid. The weighted spectral splitting in the Mertens proof bypasses that difficulty. These constants are not optimal: uniform density constants and a triangle inequality in the pointwise spectral sum leave room, and QRH does not exclude \(\beta=7/8\).
