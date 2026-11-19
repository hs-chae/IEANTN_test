# Main result: D01 is redundant over the cumulative originals

Let B0 mean the seven originals at their stated trust tiers, with the packet's foundational permissions. In particular this includes the **conclusion** of OpenAIQRH, not full RH. Put L=log x. The following stronger estimate is a new consequence of B0:
\[
 |\psi(x)-x| < 0.02\, x^{7/8}\qquad(x\ge e^{200},\ x\text{ real}).
\]
Details below give a more informative multi-exponential majorant and all intermediate constants. Since \(L^2/64\ge625\), this implies every instance of D01, with a factor greater than 31,000 to spare at the limiting endpoint. Thus B0 and B0+D01 entail exactly the same statements in **both** families (indeed in any application of these premises). This compares with the full lawful original-source envelope, not just someone else's choice of a weak original bound. It gives equality even if a stronger original-input consequence remains undiscovered. No independent blind baseline run is represented here. The improved explicit arithmetic in the companion files is **input-independent** relative to D01.

## Source premises and computation trust

Locators are PDF pages of the bound originals (and where useful numbered results). OpenAIQRH Theorem 1.1, PDF p.4, gives \(\beta\le7/8\) for zeta zeros, including the boundary as a possible zero location. PlattTrudgianFiniteRH Theorem 1, PDF p.2, puts all nontrivial zeros up to absolute height 3,000,175,332,800 on the critical line. Use \(H=3\cdot10^{12}\). The original papers' published zero and prime computations are inherited, not reverified. New replay uses Python 3.10 standard library integers, fractions and outward Decimal intervals. Decimal exp and ln are specified correctly rounded to nearest; taking both adjacent representable neighbors encloses the exact value (and all arguments here remain in the safe exponent range). Other operations use directed basic arithmetic, integer powers via multiplications, and positive nonintegral powers via exp and ln. Machin's formula and alternating arctangent series enclose the circular constant pi. No sampling is used as proof of an interval or ray. None of this is a Lean or source-first PV claim.

## Explicit density majorant

Write \(u(t)=e^{-t}\psi(e^t)-1\). Define the following list \(\mathcal D\) of triples \((r,a,k)\), with terms \(a t^k e^{-rt}\). Its sum is denoted \(D(t)\).
* Include \((.22,.0071,2),(.5,.0142,2),(.25,2.091,1)\).
* Use ordered cuts .780,.781,...,.874,.8745,.8749,.87495,.87499,.874999,.875. Let the cuts be \(s_0,\ldots,s_m\). For each \(s=s_i,\ i<m\), take \((A,B)\) from this list by its left .01 bin (.780 through .799 use the first row, .800 through .809 the second, and so on):
\[
(7.8,4.11),(8.17,3.70),(8.54,3.62),(8.93,3.54),
(9.34,3.46),(9.75,3.38),(10.18,3.30),(10.62,3.22),(11.08,3.14).
\]
These round up the values in FKS Cor. 2.9/Table 8 (PDF pp.7–8,26–27).
With \(h=\log H,\ d=1-\frac83(1-s),\ q=5-2s\), set
\[
 W_i=A e^{-dh}h^q d^{-1}\sum_{j=0}^4\frac{q(q-1)\cdots(q-j+1)}{(d h)^j}
       +B(h^2+2h+2)/H.
\]
Empty falling product is one. Include \((1-s_i,2(W_{i-1}-W_i),0)\) for \(1\le i<m\), and \((1/8,2W_{m-1},0)\). The interval tests show positive differences.

**Proof.** FKS Theorem 3.2 (PDF p.8, explicitly reproducing the truncation theorem with the admissible tuple (40,1/2,0,2.091)) with \(x=e^t\) and \(T=e^{t/4}\), \(t\ge100\), applies to real x, including prime-power jumps. Indeed \(T>51,t\), and \(e^{t/2}-5e^{t/4}-2>0\), from the endpoint inequalities and monotonicity of \(e^{t/4}/t\). The upper truncation height is in \([T,2.45T]\); the normalized remainder is \(2.091t e^{-t/4}\). There are no real zeros in \(0<s<1\): the alternating eta series has positive value there, and equals \((1-2^{1-s})\zeta(s)\) by continuation from \(s>1\) (summation by parts gives locally uniform Dirichlet convergence on \(\Re s>0\)). For the zeros of positive ordinate up to this height, PlattTrudgian2021 Lemma 2 (PDF p.4) bounds the sum of \(1/\gamma_\rho\) by
\[
 (t/4)^2/(4\pi)+.9321 < .0071\,t^2.
\]
Here the logarithm of the upper height divided by \(2\pi\) is positive and at most \(t/4\). Critical-line symmetry controls the \(\beta<s_0\) band: for each pair off the line at most one has \(\beta>1/2\); after conjugation its contribution in this band is bounded using \(.0071 t^2 e^{-.22t}\) for such members and \(2(.0071)t^2 e^{-t/2}\) for the others. No replacement of an actual signed zero sum by a signed density estimate is made.

For \(\beta\ge s\) there are no positive ordinates up to H. The **positive-ordinate**, all-height sum of \(1/\gamma_\rho\) in this band is at most \(W_i\): integrate the counting-function density from FKS by parts, with vanishing upper boundary \(N(s,V)/V\), so the bound is the integral from H to infinity of \((A v^{1-d}(\log v)^q+B(\log v)^2)/v^2\). Substitution \(v=e^{h+w}\) gives the displayed bound, since \(3<q<4\) and the fifth derivative of \((1+w/h)^q\) is negative (degree-4 Taylor majorant for all \(w\ge0\)). Then integrate \(w^j e^{-dw}\) exactly. Count endpoints by upward limits; no use of exclusion at \(\beta=7/8\). Bound each strip by \(e^{(s_{i+1}-1)t}\) and telescope via cumulative tails: the coefficient of each cumulative tail before regrouping is nonnegative. Conjugation supplies the factor **2**. This proves \(|u(t)|\le D(t)\) for every real \(t\ge100\).

Each \(a t^k e^{-(r-1/8)t}\) in \(e^{t/8}D(t)\) is nonincreasing on \([100,\infty)\): \(k/t\le r-1/8\) for every triple, including the constant last-bin term. Directed checks at t=200 give \(e^{25}D(200)<.019<.02\) (the weaker .02 check is also in the certificate). This is an entire-ray proof. The analytical mechanism improving on the hypothetical input is the summability of \(1/\gamma_\rho\) for zeros sufficiently far right of 5/8 using FKS density, while the less-right region has a faster power. A density-free argument that attaches a log-square factor to all zeros at 7/8 discards this information.

## Scope and limits of comparison

The pointwise envelopes below incorporate new B0 consequences, literal original branches and sufficient-domain tradeoffs. They need not exhaust all possible B0 proofs. Equality of the B0 and B0+D01 best *lawful* envelopes does not require enumeration of B0 consequences. It also prevents an honest D01-specific improvement at an earlier onset, in a crossover interval, at a real-endpoint join, or at arbitrarily high order: replace any D01 invocation by the proof above. Enlarging the optional finite ranges or reducing absolute density constants could improve both sides equally. There is no claim of global optimality of any margin or bound constant.


## Independent density-free implication of the exact additional premise

The conclusion B0 implies D01 does not depend on the density table.
With the same truncated explicit formula and ordinate-sum estimate as above,
assign **all** zeros the uniform upper exponent \(\beta\le7/8\). The absolute relative
psi error is at most
\[
 .0142 L^2 e^{-L/8}+2.091 L e^{-L/4}
       < (1/64)L^2 e^{-L/8}\qquad(L\ge200).
\]
Indeed after extracting \(L^2e^{-L/8}\) the remainder decreases, and the endpoint
comparison is checked in spectral_repair.py. This weaker proof needs neither finite
RH nor the far-right FKS Corollary 2.9. The stronger absolute-constant estimates
above do use Corollary 2.9 as **stated**, with Table 8. FKS PDF p.7
Theorem 2.7 prints \(\delta\ge1\), whereas Table 8 (PDF p.26) uses
\(\delta\approx.309\) in relevant rows. We neither substitute these parameters into
Theorem 2.7 nor claim to have independently proved the corollary from that
theorem's printed conditions. At the packet's stipulated original-result trust
the stated corollary is a premise; under a stricter tier that withholds it, the
density list and dependent constants would need different applicable coefficients.
The density-free redundancy and the independent finite branches do not inherit
this sensitivity.
