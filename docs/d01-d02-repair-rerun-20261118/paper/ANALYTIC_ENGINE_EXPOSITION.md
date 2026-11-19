# How the added tail assumption changes the final mathematics

This is an exposition of assessed mechanisms in the D01/D02 follow-up, not an additional discovery trial. The numerical examples below come from assessed portfolios at their explicitly qualified domains. Full analytic Lean proofs and source-first program verification are not claimed. Clean numerical reproduction and final publication have separate receipts.

## The input and the baseline are different things

Put \(L=\log x\). The supplied assumption is

\[
D_\beta:\quad |\psi(x)-x|\le \frac{x^\beta(\log x)^2}{64},\qquad x\ge e^{200}.
\]

Its quantifier is over every real argument in that range. D01 has \(\beta=7/8\); D02 has \(\beta=27/32\). These are hypothetical inputs, not theorems proved by the experiment or new claims attributed to OpenAI. Both are added to B0, the common seven-paper corpus including its pinned original QRH result. Here the corpus specifies the available sources: B0 uses the named analytic and published-computation inputs at their stated, audited domains. It does not mean assuming every printed sentence in those papers, including identified false formulations, as an unrestricted axiom. Those formulations are excluded or restricted with an explicit source-correct argument.

D02 implies D01 because the coefficient and domain are identical and the exponent is smaller. The completed fresh D01 stages also prove that B0 already implies D01. Their new baseline deductions are useful secondary mathematics, but the extra D01 hypothesis does not logically strengthen B0. Comparing an author's reconstructed B0 and D02 proofs is a within-method assumption ablation. It is not an independent blind B0 discovery experiment.

## A local tail hypothesis gives global zero information

For \(\operatorname{Re}s>1\), the absolutely convergent Euler product and partial summation give

\[
-\frac{\zeta'(s)}{\zeta(s)}=\frac{s}{s-1}+s\int_1^\infty (\psi(t)-t)t^{-s-1}\,dt.
\]

The integral over the finite interval ending at \(e^{200}\) is entire in \(s\). On each compact subset of \(\operatorname{Re}s>\beta\), the remaining integrand and each fixed derivative are bounded by an integrable function: a negative power strictly below \(t^{-1}\), times a fixed power of \(\log t\). Thus the tail is holomorphic there. Uniqueness of meromorphic continuation excludes a zeta zero in that open half-plane, since its logarithmic derivative would have a pole with a nonzero residue.

The conclusion is

\[
\operatorname{Re}\rho\le\beta.
\]

The boundary remains allowed. This is a global conclusion about zeros; it can improve explicit-formula estimates even when the arithmetic argument is below \(e^{200}\). It never extends the original pointwise bound to a smaller argument. Every shifted application still checks its own domain, particularly \(x/e\).

This distinction is essential to the experiment. A late hypothesis can change earlier bounds through an analytic consequence, while an unjustified substitution into the original inequality would be an error.

## Compressing the high-zero contribution

The finite-RH input controls low zeros through its stated verified height. For a fixed usable height \(H\) at or below that endpoint, and \(s>1/2\), the right-hand off-line zeros have ordinates above \(H\). Let \(N(s,t)\) count positive ordinates, with multiplicity and real part at least \(s\). A source-valid density bound gives

\[
N(s,t)\le A_s t^{p_s}(\log t)^{q_s}+B_s(\log t)^2.
\]

For example, the permitted Dusart Theorem 2.3 yields \(p_s=8(1-s)/3\), \(q_s=5-2s\), \(A_s=4.9\,3^{p_s}\), and \(B_s=51.5\) on the used domains, after the elementary inequality \(\log(1+u)\le u\). Some portfolios also use FKS Corollary 2.9 and Table 8 at the explicitly stated literature tier. That published-table tier is separate from independently proving the optimizer behind it.

Partial summation bounds the two-sided reciprocal mass by

\[
2\sum_{\operatorname{Re}\rho\ge s,\,\operatorname{Im}\rho>H}\frac1{\operatorname{Im}\rho}
\le 2\int_H^\infty\frac{N(s,t)}{t^2}\,dt.
\]

The omitted lower boundary term is nonpositive; it is not an extra positive error. Here \(p_s<1\), so the integral converges. This is why the relevant high-zero sums, unlike an unrestricted sum of reciprocal ordinates, can be controlled absolutely.

One reusable sharpening is entirely elementary. Put \(h=\log H\), \(\alpha=1-p_s>0\), and \(q=q_s\). On the strips used for this refinement, \(3<q<4\). The degree-four Taylor polynomial of \((h+w)^q\) is an upper bound for all \(w\ge0\), since its fifth derivative is negative. Consequently

\[
\int_H^\infty t^{p_s-2}(\log t)^q\,dt
\le \frac{e^{-\alpha h}h^q}{\alpha}
\sum_{k=0}^4\frac{(q)_k}{(\alpha h)^k}.
\]

Here \((q)_k=q(q-1)\cdots(q-k+1)\), with empty product one. The factorial from integrating \(w^k e^{-\alpha w}\) cancels the Taylor factorial. All terms in this upper bound are positive. The older exponential majorant remains a valid branch; the refinement need not discard it or change any premise.

For a nonincreasing reciprocal-mass bound \(C(s)\), use a finite mesh

\[
s_0<s_1<\cdots<s_m=\beta.
\]

A telescoped positive mixture assigns the mass of each strip to its right endpoint:

\[
Z_\beta(L)=\sum_{i=0}^{m-1}(C_i-C_{i+1})e^{-(1-s_{i+1})L}.
\]

The final \(C_m=0\) in this notation is a bookkeeping device, not a claim that there are no zeros on the cap. The final interval still covers boundary zeros. Exact source-row domains, running minima and positivity of coefficient differences matter. A density coefficient smaller than the paper's coefficient cannot be justified by a successful replay.

Reducing the cap from \(7/8\) to \(27/32\) moves the last spectral mass to faster-decaying exponentials. In positive representations this reduces the constructed endpoint bound. Finite-height, truncation and prime-power terms must still be retained; the cap alone is not a complete numerical proof.

## Why signed integration improves the Mertens constants

Write \(F(L)=e^{-L}\psi(e^L)-1\), and use the inclusive prime-power cutoff in

\[
W_0(L)=\sum_{2\le n\le e^L}\frac{\Lambda(n)}n-L+\gamma,
\]

\[
W_1(L)=\sum_{2\le n\le e^L}\frac{\Lambda(n)}{n\log n}-\log L-\gamma.
\]

With the limiting constants supplied or derived at the stated source tier, partial summation gives

\[
W_j(L)=L^{-j}F(L)-\int_L^\infty k_j(u)F(u)\,du,
\qquad k_j(u)=u^{-j}(1+j/u),\quad j=0,1.
\]

This exact formula includes jumps in its endpoint term. Changing an ordinary integral at one prime or prime-power point has no effect on that integral.

Taking the absolute value before integration loses cancellation. A separately justified convergent spectral representation or integrated explicit formula can retain it. For a high zero, integration by parts and the decreasing kernel give

\[
\left|\int_L^\infty k_j(u)e^{(\rho-1)u}\,du\right|
\le \frac{2k_j(L)e^{-(1-\operatorname{Re}\rho)L}}{|\rho-1|}.
\]

The large ordinate supplies an extra denominator. The convergence and the remainder must be proved for the representation actually integrated. A pointwise truncation height depending on \(u\) cannot simply be differentiated or integrated as though its zero set were fixed. The assessed portfolios explicitly use convergent replacements or separately bounded omitted tails.

Prime-power corrections then connect these weighted quantities to the reciprocal-prime and weighted-prime sums and to the logarithm of the normalized products. The tails are positive and run strictly above the current cutoff. They have to be included with the correct sign.

Define the final observables by

\[
S(x)=\sum_{p\le x}\frac1p-\log L-M,
\qquad W(x)=\sum_{p\le x}\frac{\log p}p-L+B_3,
\]

\[
P(x)=e^\gamma L\prod_{p\le x}(1-1/p),
\qquad Q(x)=\frac{e^{-\gamma}}L\prod_{p\le x}(1-1/p)^{-1}.
\]

The exact constants are the source's prime-series constants; \(P Q=1\). If \(z=\log Q\), then the product errors are \(|e^z-1|\) and \(|e^{-z}-1|\). A bound on \(|z|\) must be converted by exponentiation; it is not already a relative-error bound.

A common comparison scale is

\[
G_M(x)=\max\{|W(x)|,\ L|S(x)|,\ L|P(x)-1|,\ L|Q(x)-1|\}.
\]

Thus a bound \(G_M(x)\le Cx^{-a}\) has no extra logarithm for the weighted sum and has a factor \(1/L\) for the other three errors. These four consequences are correlated outputs, not four independent experiments.

## Ramanujan: retain the coefficient vector and both arguments

The actual gap and its normalized profile are

\[
R(x)=\frac{ex}{L}\pi(x/e)-\pi(x)^2,
\qquad G_R(L)=L^6e^{-2L}R(e^L).
\]

Finite expansions of the exponential integral, with proved remainder barriers, yield polynomial lower profiles whose full initial coefficients are \(1,14,145,1412,13985,145450\). Their exact convolution can be written

\[
a_j=(j+4)!\sum_{r=0}^{j+4}\frac1{r!}
-\sum_{h=0}^{j+4}h!(j+4-h)!.
\]

A named order in one submission may differ from another author's order. Comparisons therefore use the actual coefficient vector, degree and remainder coefficient. A finite island is kept as a finite island; a later successful asymptotic ray does not fill the gap between them.

A lower prime-counting bound is needed at \(x/e\), and a nonnegative upper bound at \(x\). The latter is squared. This is why both source domains, both normalization constants and both shifted transition points must be checked. The constant difference between the principal-value logarithmic integral and the integral starting at two cannot be silently omitted.

The final strict-sign endpoint is different from a quantitative-margin onset. The independently checked local counts give an exact equation for a real root between the last failing integer and the next integer. Equality excludes that root from a strict positivity ray. The very large integer-to-analytic bridge remains at the declared published-computation tier; recomputing three local prime counts does not independently reproduce that whole bridge. D02 cannot move an actual arithmetic counterexample.

## Examples already finalized in this follow-up

In the repaired first NL control, the same complete degree-two Ramanujan target has sufficient log onsets 217 under B0 and 186 with D02. Its degree-fourteen target has onsets 646 and 506. Its four Mertens errors obey \(G_M(x)\le0.21726x^{-5/32}\) on \(L\ge200\). All older finite, signed, logarithmic and slower-power branches remain eligible.

In the repaired first IEANTN control, the complete degree-43 target has sufficient log onsets 1717.38 and 1310.73 at the published density-table tier. Separate density-free arguments give 1882.82 and 1410.23. Its density-free D02 Mertens result has the different shape \(G_M(x)<0.015625000000005L^2x^{-5/32}\) on \(L\ge200\). The coefficient is close to the supplied coefficient 1/64 because this branch keeps the literal endpoint input and separately controls the signed tail; its logarithmic loss must remain visible.

The same IEANTN control also proves the input-independent quantitative ray \(G_R(L)>1\) from 30.75, with earlier bounded windows for stronger profiles. That is a B0 advance, not D02 propagation. Comparing just one newly displayed late ray would miss these branches.

The repaired second IEANTN control gives a useful example of propagation through a later bottleneck. For every real \(L\ge49.1\), it proves

\[
G_R(L)>1+14/L+c/L^2,
\qquad c=7.5\text{ under B0},\quad c=79.9\text{ under B0+D02}.
\]

The initial CH2 interval calculation is the same in both conditions. D02 reduces the later spectral loss, allowing the stronger early profile to connect to the entire remaining ray. This does not apply the raw assumption at 49.1. Its higher profile \(H_{69}\), with the exact coefficient convention in that submission, has sufficient onsets \(5037/2\) and \(1907\). Here the source index 69 means canonical inverse-log degree 65 in the normalized Ramanujan gap; comparisons use that exact coefficient vector.

That control also closes three previously missing Mertens finite joins using a newly enclosed Mertens constant and exact prime-free intervals. The reciprocal-sum coefficients \(0.2,0.15,0.12\), multiplying \(L^{-3}\), hold from the respective inclusive real starts \(2278382.113,5001781.694,8789120.657\). These arithmetic repairs use B0 alone. Its later common-scale bounds at \(L\ge200\) are \(0.018791x^{-1/8}\) and \(0.25973x^{-5/32}\); the latter is smaller throughout that common ray by the decreasing exponential ratio. The early repairs and the later input-dependent gain are separate mechanisms.

These are valid examples at their stated tiers, not global best-known or optimality claims, and not a conclusion that one exposure arm is superior. The full comparison must include both fresh replications, fresh controls and legacy continuations separately.

## A stronger repaired control: stratified tails and exact pole cancellation

The second native-PNT control restored all twelve of its previously incomplete stronger Mertens rows. Correcting an omitted-tail constant alone did not recover them: the decisive additional step was to divide the omitted zeros by real part, and apply the appropriate density tail separately in each strip. The complete tail proof uses the actual finite-RH height, the terminal atom allowed at the closed zero cap, and the exact outer integral. The optimized rows also have a proof using Dusart density without the FKS density table. They still use the FKS explicit formula; this is not a density-free argument.

A second improvement combines the spectral terms before taking absolute values. For the unweighted primitive the zero contribution in the derivative and its primitive cancels its factor of the zero:

\[
 -\frac{e^{(\rho-1)L}}{\rho}
 -\frac{e^{(\rho-1)L}}{\rho(\rho-1)}
 =-\frac{e^{(\rho-1)L}}{\rho-1}.
\]

Thus bounding the endpoint and primitive separately can pay an avoidable extra moment. For a weighted tail, integration by parts gives the corresponding integral kernel before absolute values are taken. Finite-height extra factors must be retained and their limiting passage proved; a factor slightly greater than one cannot simply be replaced by one. The repaired proof explicitly uses bounded convergence in the summable tail.

In the common Mertens scale already defined above, the accepted whole-ray pair is

\[
 G_M(x)\le0.01256x^{-1/8}\quad\text{under B0},\qquad
 G_M(x)\le0.221x^{-5/32}\quad\text{under B0+D02},\qquad L\ge200.
\]

The ratio of these two particular certified bounds is less than 0.035 throughout the common ray. This compares constructed upper bounds, not the actual prime errors or every proof possible under B0. The target coefficient thresholds also move: the same proof reaches the common error target of one part in one hundred trillion from log argument 197 with D02 versus 223 under B0. Shared products and prime sums remain correlated receivers of one analytic calculation.

## A scope error that the continuation actually discovered

The later IEANTN D02 author found an error in its inherited D01 summary, after the earlier independent review and Root admission had missed it. The original exact program certified the constant Ramanujan margin 1.03 on the closed interval from 30.75 to 191, but the summary and review had promoted it to an unbounded ray. The accepted D01 record has an explicit additive correction; original source and review bytes remain available.

This is a mathematical defect, not an execution-resource failure. With the already available power-saving prime number theorem, write

\[
 A(L)=Le^{-L}\pi(e^L)
 =1+L^{-1}+2L^{-2}+6L^{-3}+24L^{-4}+O(L^{-5}).
\]

Then

\[
 G_R(L)=L^4\left(\frac{L}{L-1}A(L-1)-A(L)^2\right)
 =1+O(L^{-1}).
\]

A constant margin strictly above one therefore cannot hold on an unbounded final ray. The earlier finite certificate and every other independently valid lower profile remain useful. The later author's larger finite interval is a new D02-stage B0 discovery, not retroactive D01 credit. Source-scope corrections must change the complete frontier representation, the inherited floor and every affected comparison; preserving old bytes does not justify continuing to plot a known false ray.

## How a whole-frontier comparison is proved

For two bound shapes \(C_i x^{-a_i}L^{q_i}\), with \(a_1-a_0=1/32\), the ratio is

\[
\frac{C_1}{C_0}e^{-L/32}L^{q_1-q_0}.
\]

Its logarithmic derivative is \(-1/32+(q_1-q_0)/L\). Beyond its turning point an enclosed left-end comparison proves the whole common remaining ray. Different starts, finite components and competing source branches need separate checks. The minimum of valid error bounds and the maximum of valid lower-gap bounds preserve all useful branches. Strict gain in one branch can disappear after intersecting with a stronger unchanged branch.

Finite numerical checks cover all real cells by interval enclosures and checked source applicability throughout each closed cell. Infinite rays require analytic monotonicity or tail proofs. Floating suggestions, numerical plots and failed sufficient tests are useful diagnostics; none alone establishes a universal inequality or a counterexample to the arithmetic statement.

## Three further improvements to the density calculation

These refinements improve the constructed upper bounds themselves. None assumes that a numerical density upper bound is the actual zero distribution.

The fresh NL control C017, in its second repair, retains more of Dusart Theorem 2.3 (Ramaré), PDF page 5, physical LF250–257, rather than immediately replacing its logarithm by its argument. The paper's actual statement, for \(\sigma\ge0.52\) and \(t\ge2000\), is

\[
 N(\sigma,t)\le t\log\!\left(1+\frac{9.8}{2t}(3t)^{8(1-\sigma)/3}(\log t)^{5-2\sigma}\right)
 +\frac{103}{2}(\log t)^2.
\]

This counts positive ordinates; the factor two for both conjugates is paid once. With \(t=He^y\), the used strip has \(p=8(1-\sigma)/3\), \(q=5-2\sigma\), \(ℓ=\log H\), and

\[
 G=9.8\,3^p H^{p-1}ℓ^q.
\]

Put

\[
 Z(y)=\frac G2 e^{-(1-p)y}(1+y/ℓ)^q.
\]

On the actual domains \(1-p-q/ℓ>0\), so \(0\le Z(y)\le G/2\). Integrating \(z/(1+z)\) on the interval from zero to \(Z\) gives

\[
 2\log(1+Z)\le 2Z-\frac{Z^2}{1+G/2}.
\]

The improvement is obtained by subtracting a **lower** integral enclosure of this positive correction from an **upper** enclosure of the old linearized integral. Here \(3<q<4\); its fourth-order Taylor bound is upper, while the sixth-order Taylor bound for exponent \(2q\), between six and seven, is lower. These opposite signs are essential. The integrated logarithm is convex in the strip parameter because it is an integral, with a nonnegative weight, of the logarithm of one plus an exponential of an affine function. Chords therefore bound the true integral from above. This does not require convexity of a rounded approximation. The final boundary mass remains present.

For example, C017's common Mertens error radius from \(L\ge200\) improves from \(0.01218x^{-1/8}\) to \(0.21150x^{-5/32}\). The radius is \(L\) times either relative product error or the reciprocal-prime error, and is the unmultiplied weighted-prime error. The ratio is

\[
 \frac{0.21150}{0.01218}e^{-L/32}<0.03353,
 \qquad L\ge200.
\]

The inequality follows at the left endpoint by directed arithmetic and persists because the ratio decreases. This is a comparison of those matched constructed branches, not a claim to beat every other B0 branch on every range. Exact statements and source correspondence are in C017's own_repair.md, physical LF72–144, and its final source audit.

The legacy native PNT+ continuation C022 uses many smaller chords over the same source-valid density integrals. Its repaired source removes the previously unlicensed sharper FKS panel. A chord over each small interval bounds the convex true integral only when both endpoints belong to the same valid convex source majorant and coefficient bin; otherwise the retained constant envelope applies. Positive derivative weights then turn the resulting decreasing upper envelope into a dominating measure. Uniform interval masses and endpoint atoms are bookkeeping for that majorant, not recovered zero counts. The allowed FKS input is Corollary 2.9, equation (2.17), PDF pages 7–8, and the first Table 8 panel, PDF page 26, at the explicitly disclosed published-table tier. The unconfirmed sharper panel announced in Remark 1.5(2), PDF page 3, is not a premise.

The legal replacement recovers substantial improvements, while some earlier tight targets remain unresolved. In particular, the new common slow-power coefficient is \(0.001354\) from \(x=180223318\), using a newly executed exact finite tape and complete analytic joins. The smaller old coefficients \(0.001324\)–\(0.001350\) retain their supported finite and later pieces; these pieces do not prove the missing whole interval. Likewise the old shrink-by-68 construction does not prove unit margin everywhere: the supported whole-ray alternative shrinks by 67.7, while shrink-by-68 has the smaller margin 0.74. These are real limitations, not counterexamples to the underlying prime inequality.

The legacy IEANTN continuation C023 makes a different improvement near the verified height. Let \(N_\sigma(t)\) count positive-ordinate zeros to the right of a strip edge, and let \(D_\sigma(t)\) be its permitted density majorant. Finite RH gives \(N_\sigma(H)=0\) for \(\sigma>1/2\). The selected count on a short initial band is consequently also bounded by the total zero count increment \(N(t)-N(H)\). CH2 Lemma B.1, PDF page 43, supplies an explicit upper bound for that increment, including the remainder at both endpoints.

For reciprocal moment order \(m=1,2\), the old upper bound is

\[
 U_m=2mH^{m-1}\int_H^\infty D_\sigma(t)t^{-m-1}\,dt.
\]

Choose a fixed \(\eta>0\). If \(A_m\) is a lower bound on the same density integral restricted to \([H,He^\eta]\), and \(B_m\) is an upper bound on the replacement count-increment integral there, then

\[
 2H^{m-1}\sum_{\operatorname{Im}\rho>H,\,\operatorname{Re}\rho\ge\sigma}
   (\operatorname{Im}\rho)^{-m}
 \le U_m-2m\max(0,A_m-B_m).
\]

Here both restricted integrals defining \(A_m,B_m\) include the same factor \(H^{m-1}\). This follows by splitting the integral into the initial band and its complement; it requires no pointwise ordering of the two majorants. A finite grid of widths selects the largest rigorously enclosed saving. The full tail and the cap atom are still paid. The improvement is implemented in d02_density_new.py, physical LF38–83, with the derivation in D02_PROOF.md, LF19–51. The source use is qualified by the explicit CH2 correction below; the raw favorable missing term is not adopted.

## Two scope corrections that matter to the proof

CH2 Corollary 1.2, PDF page 3, gives the relative psi radius and center

\[
 \frac{\pi}{H-1}+\frac{C_H}{\sqrt{x}},
 \qquad \frac{\pi}{H}\operatorname{coth}\!\left(\frac\pi H\right).
\]

The weighted von Mangoldt sum has the corresponding radius about \(\log x-\gamma\). There is no favorable additional term \(-1/x\). C023's original explanatory wording invented that term and replaced the radius denominator by \(H\); the original text remains as rejected history. The adopted proof instead pays the center displacement by \((\pi/H)^2\), and the independent supplemental calculation proves

\[
 \frac\pi{H-1}+\left(\frac\pi H\right)^2
 <1.047136353\cdot10^{-12}.
\]

Thus the same numerical constant, algorithms, parameters and final bounds are supported by the authentic source formula. The correction is to the proof's source use, not a new analytic assumption or a silent edit of the original evidence.

C022's optional general kernel lemma originally assumed that \(f\) is nonnegative, decreasing and differentiable, with \(tf(t)\) tending to zero. Those conditions alone do not imply convergence of \(I_f(y)=\int_y^\infty f(t)\,dt\): \(f(t)=1/(t\log t)\) is a counterexample. The admitted statement explicitly requires the finite integral. Positive Stieltjes integration then proves

\[
 \left|\sum_{p>y}\log p\,f(p)-I_f(y)\right|
 \le d(y)\bigl(2yf(y)+I_f(y)\bigr),
\]

provided \(|\theta(t)-t|\le d(y)t\) on the entire future ray. Every actual kernel used in its degree-two and degree-three applications has a finite integral; the qualification changes no numerical output or actual downstream premise. The unrestricted raw generic wording remains incomplete. The complete Stieltjes proof and independent readback are preserved separately.

## What remains trusted

The original analytic theorems and published computations remain named literature inputs. In particular, the density optimizer's printed parameter issue is not resolved merely by quoting its corollary; density-free conclusions are kept separately. The inherited enormous integer sign verification and finite-RH verification have not been reproduced by the new small numerical programs.

New ordinary numerical replays trust their pinned source, compiler where used, Python/runtime arithmetic contracts, operating system and hardware. Exact integer arithmetic and directed enclosures are different from formally proving execution of the source. Historical programs using assertions require the stated normal assertion-enabled execution; the new acceptance wrappers use explicit checks and are tested under normal Python, -O and -OO.

A source-first PV claim would additionally require correspondence between actual executable source and a formal execution model, arithmetic and execution correctness, and a connection of its verified outputs to the actual endpoint theorem. This campaign does not supply that full chain or a complete analytic Lean endpoint. Its accepted written results are not inserted as verified IEANTN nodes.
