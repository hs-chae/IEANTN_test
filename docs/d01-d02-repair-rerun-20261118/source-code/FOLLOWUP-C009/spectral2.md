# Common lemma: the D02 boundary and the explicit spectral estimates

Write \(v=\log x\), \(H=3000175332800\), \(b_0=7/8,\ b_2=27/32,\ \delta=1-b\).
**B0** denotes the seven originals at their stated hypotheses, including QRH; **B2** is B0 plus the exact D02 contract. Arithmetic sums are inclusive. Neither full RH nor an unreported extension of finite RH is used.

## The additional implication

For \(\Re s>1\) the Euler product and summation by parts give
\[
-\zeta'(s)/\zeta(s) = s/(s-1) +s\int_1^\infty(\psi(t)-t)t^{-s-1}\,dt .
\]
The Euler product follows by absolute convergence and unique factorization; its logarithmic derivative converges locally uniformly there. With D02 the integral is holomorphic in \(\Re s>27/32\): the below-\(e^{200}\) integral is entire, and on compact subsets the remaining integrand and all fixed-order derivatives have an integrable majorant \(C t^{-1-\epsilon}(1+\log^{2+j}t)\). Continue the identity meromorphically in this half-plane. A zero of any multiplicity gives a pole of the log derivative with nonzero residue, whereas the right side has no pole other than at 1. Thus \(\beta\le b_2\) for every nontrivial zero \(\rho=\beta+i\gamma\), with equality not excluded. This is how D02 enters the proofs, including for \(100\le v<200\). The \(\psi\) inequality itself is not used below its threshold. For B0 replace this implication by QRH, original PDF p.4 Theorem 1.1 and pp.84–85 Proposition 11.3, giving \(b_0\). D02 implies D01, and B0 itself implies D01 by the inherited \(.020x^{7/8}\) majorant.

Platt–Trudgian finite RH, original PDF p.2 Theorem 1, gives \(\beta=1/2\) for \(|\gamma|\le H\). Use multiplicities and the conjugation and critical-line reflection used also in FKS Proposition 3.6, pp.9–10. There are no real zeros in \(0<s<1\): the alternating Dirichlet series is positive by pairing, and equals \((1-2^{1-s})\zeta(s)\) by summation by parts and continuation.

## Density and the common cap

Use Fiori–Kadiri–Swidinsky (FKS) Corollary 2.9, equation (2.17), original PDF p.7, and the **first block** of Table 8, p.26. In a row \([s_0,s_1]\), with its printed \(c,d\), write \(\alpha=(8s-5)/3,\ q=5-2s\). For s in the row and \(Y\ge H\),
\[
 N(s,Y)\le cY^{1-\alpha}(\log Y)^q+d(\log Y)^2 .
\]
The ten rows and parameters are in spectral.py, rs. The alternative subconvexity block is not used. Partial summation gives for \(y\ge h=\log H\)
\[
 2\sum_{\beta\ge s,\gamma\ge e^y}\gamma^{-1}\ \le\
 D_{c,d}(s,y):=2c\int_y^\infty u^q e^{-\alpha u}du
    +2d e^{-y}(y^2+2y+2).                                      \tag{1}
\]
Drop the nonpositive lower boundary using the count strictly below \(e^y\); the upper boundary tends to zero. When \(\alpha-q/y>0\), the first integral is at most \(y^q e^{-\alpha y}/(\alpha-q/y)\), by \(\log(u/y)\le(u-y)/y\).

Put \(s_* = .70\), and \(A(s)=2\sum_{\beta\ge s,\gamma>0}1/\gamma\). Build a single cap \(\mathcal B(s)\) for \(A(s)\) on \([s_*,b_0]\). For fixed \(c,d\), \(D_{c,d}(s,h)\) is convex in \(s\) since its first integrand has the form \(f(u)e^{-s[(8/3)u+2\log u]}\). In each subinterval of length \(\le .002\) within a row (exact partition in parts()), form the chord joining rational upper bounds at the endpoints. Use Taylor degree 4 about \(h\) for \(u^q\) (fifth derivative negative) and round up to \(10^{-10}\). The expression before rounding is
\[
 2c\,h^q e^{-\alpha h}\sum_{i=0}^4\frac{q^{\underline i}}{\alpha^{i+1}h^i}
 +2d e^{-h}(h^2+2h+2).
\]
Clip each chord by the previously certified right-end cap, valid by monotonicity of \(A\). The code checks descending chords and continuity at each join (the new left bound is at least the previous cap). The result is continuous nonincreasing. Use exactly the same cap for both b, clipped at b. Let
\[
 Z_b(v)=\mathcal B(b)+\int_{s_*}^b e^{-(b-s)v}(-d\mathcal B(s)),\qquad
 V(v)=-2\Re\sum_{\beta\ge s_*,\gamma>0}\frac{e^{(\rho-1)v}}{\rho}.
\]
The coefficient \(Z_b(v)\) decreases to \(K_b=\mathcal B(b)\), since the measure has no mass at b. The receipts give \(K_{b_0}=.0104436237,\ K_{b_2}=.146555285475\). The series converges absolutely by (1), and has uniform exponential domination for \(v\ge100\). Summing by layers, then integrating by parts in \(s\), gives
\[
2\sum_{\beta\ge s_*,\gamma>0}\frac{e^{(\beta-1)v}}{\gamma}
 \le e^{-\delta v}Z_b(v)
 =e^{(s_*-1)v}\mathcal B(s_*)+\int_{s_*}^{b}v e^{(s-1)v}\mathcal B(s)\,ds.      \tag{2}
\]
The last form is strictly smaller at \(b_2\) for every \(v\ge100\), not just at sampled arguments. This concerns bounding functions, not the presence of actual boundary zeros.

## Remainder from the actual cutoff

For \(v\ge100\) use FKS Theorem 3.2, equation (3.2), original PDF p.8, with its stated \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\); here that \(\alpha\) is the truncation parameter. Use this at published trust, not the earlier formula cautioned about in FKS Remark 3.3. The four choices \(T=\exp(y)\), \(y=\kappa v-j\), are \((\kappa,j)=(1/3,0),(2/5,0),(9/20,0),(1/2,2)\). Then \(\max(51,v)<T<(e^{v/2}-2)/5\) and \(T>H\): check at 100, and \(T/v,(e^{v/2}-2)/T,T\) increase. The actual \(T^\star\) is in \([T,2.45T]\).

Write \(\psi(e^v)/e^v-1=V(v)+E_{\rm res}(v)\). For each cutoff
\[
 |E_{\rm res}(v)|\le e^{-\delta v}\sum_i d_i(v).
\]
The positive normalized terms \(d_i\) are:
* \(C_\kappa v^2e^{(1/2-b)v}\) and \((C_\kappa/2)v^2e^{(s_*-b)v}\), where \(C_\kappa=.018,.026,.033,.040\) in cutoff order. These bound the truncated zeros on/below \(1/2\) and strictly above \(1/2\) but below .70. The total reciprocal-ordinate bound is \(0.16z^2-0.58z+1.40\) at \(z=\log T^\star\), from FKS Corollary 2.3, Table 1 row 100 and (2.1), first constants of Remark 2.2 (PDF pp.4–5); derivation in psi.md and checks in mcert.py basics(). Take the limit from above at the endpoint. Reflection permits half the total in the second range. For \(z\le\kappa v+1\) the increasing quadratic is at most \(.16\kappa^2v^2\), since \(-.26\kappa v+.98<0\).
* \(2.091v e^{(1-b-\kappa)v+j}\), from truncation.
* For the omitted high modes split each row into the parts of length \(\le .01\) in parts(), trimming at b. For \([l,u]\) use \(e^{(u-b)v}D_{c,d}(l,y)\), with the tangent bound after (1) for its first integral. All omitted zeros lie above \(T\). Include the endpoint b in the last bin. Separate the two summands when bounding their rates.

The same \(E_{\rm res}\) comes from every comparison to \(V\); taking a minimum over estimates is valid. No derivative of the actual cutoff is taken.

**Rates.** For each term \(d_i(t)\le d_i(v)e^{-\lambda_i(v)(t-v)}\) for \(t\ge v\ge100\), and \(e^{bt}d_i(t)/t^2\) has logarithmic derivative at least \(\mu_i\) on \([100,\infty)\). In list order:
\[
\begin{array}{c|c|c}
 &\lambda_i(v)&\mu_i\\ \hline
\text{low at }w=1/2,\ s_* & b-w-2/v & w\\
\text{truncation error} & b+\kappa-1-1/v & 1-\kappa-1/100\\
\text{first bin term} & b-u+\kappa(\alpha-q/y) &
 u-\kappa\alpha-2/100-\kappa q/[y_0^2(\alpha-q/y_0)]\\
\text{second bin term} & b-u+\kappa(1-2/y) & u-\kappa-2/100 .
\end{array}
\]
\(y_0=100\kappa-j\). Differentiate the powers, exponentials and tangent denominator; \(d\log(y^2+2y+2)/dy\le2/y\). All \(\lambda_i(v)\) increase and are positive at 100, and all \(\mu_i>0\), certified by basic(). Notably a second-bin past rate need not be \(1/4\); the final implementation treats it separately. These rates are used before taking minima.

The direct relative \(\psi\) error bound is \(e^{-\delta v}(Z_b(v)+\min\sum_i d_i(v))\). Each minimum in this dossier is over the four parameter pairs unless specified. The inherited prime-power corrections are
\[
 .9999e^{-v/2}\le (\psi-\theta)(e^v)/e^v
 \le p(v)=1.000000147e^{-v/2}+1.78e^{-2v/3}\quad(e^v\ge121).
\]
Dusart 2018 original PDF pp.12–13 Prop. 4.3 and Cor. 4.5, and PT 2021 (5), p.2, for the upper bound.

## Exact integral and paired refinements

One may replace the rational cap by the running infimum of \(D_{c,d}(s,h)\) over all previous \(s\) and applicable rows, including the current s. This is nonincreasing and no larger than the chord caps. Use (2) in layer form (any intervening downward jumps enter the Stieltjes integral). At both b endpoints it is continuous from the left and equals the integral expression of its own row. The exact-integral K values are enclosed in \([.010443618317,.010443618318]\) and \([.146288736863,.146288736866]\): refine2.py uses degree 15 lower / 16 upper Taylor bounds and checks that every preceding row's right-end degree-3 lower bound exceeds the final upper bound. On the last row the integral is continuous and decreasing. The optional fine chord uses subdivisions \(\le .001\) including \(b_2\) as a node, Taylor degree 12 and \(10^{-12}\) rounding. The proof is otherwise unchanged. All these limits concern bounding coefficients, not the arithmetic errors.

For each bin one can likewise retain the exact first integral in (1): for \(g(y)=\int_y^\infty u^q e^{-\alpha u}du\), one has \(\alpha-q/y\le -g'(y)/g(y)\le\alpha\) by comparison with exponentials times the integrand at y. The same rates remain valid, so this replacement is a whole-domain improvement. Nothing here uses sampled interpolation of arithmetic data.

In comparing \(b_0,b_2\), use the physical \(e^{-\delta v}d_i(v)\). Common terms agree, shortened bins at \(b_2\) have smaller terms, and removed bins disappear. Tail and past integration preserve the resulting order if evaluated with the same kernels, and the upper factors in the rate formulas also improve in physical units (the tail rate \(\delta+\lambda_i\) and past rate \(\mu_i\) are unchanged for common bins and increase or stay unchanged for the tail rate when the right endpoint decreases; for the past transfer of a shortened bin \(\mu_i\) may decrease, but exact integration preserves the order). The high contribution improves strictly by (2). In particular a clipped variant of inherited repair.md at cutoff .78 keeps its original cap and both cutoffs, shortens the .84–.86 bin and deletes later bins. Its monotonic-tail constants can be left unchanged in physical form; its fixed past rate \(1/4\) still holds: the shortened tangent bin has \(u=b_2\), and the proof in repair.md still applies to all its bins since \(b_0-u\le.095\) in all original or shortened bins and \(\kappa\le.4\). Thus this directly improves the inherited spectral R and M branches on their exact domains. Other retained baseline branches can win at a given x. Comparisons are to the reported original-source portfolio, not to an unproved optimum over arbitrary B0 deductions.
