# Mertens products and prime sums

Results use B0 alone. Put \(L=\log x\) and
\[
\begin{split}
 D_1(x)&=\sum_{p\le x}p^{-1}-\log L-M,
 &M&=\gamma+\sum_p\big(\log(1-1/p)+1/p\big),\\
 D_2(x)&=\sum_{p\le x}(\log p)/p-L+B_3,
 &B_3&=\gamma+\sum_{m\ge2}\sum_p(\log p)/p^m,\\
 Z(x)&=\log Q_{\rm raw}(x)-\gamma-\log L .
\end{split}
\]
These are the constants of Dusart Theorems 5.6–5.7 (PDF pp.17–19). The two product errors are \(|e^{-Z}-1|\) and \(|e^Z-1|\); they are correlated and are not separate experiments. All onsets below are real, include their endpoint for non-strict bounds, and count a prime at the right-continuous jump.

## Explicit portfolio

* In addition to retaining the original direct Dusart envelopes, the join columns of **mertens.out** give whole-ray bounds
  \[
   |D_1(x)|\le c/L^3,\quad |e^{\pm Z(x)}-1|\le c/L^3,\quad |D_2(x)|\le c/L^2,
  \]
  in that column order. Here are selected entries (the receipt gives each of the 24 tested coefficients with exact endpoints).

  |\(c\)|\(D_1\) onset|both products onset|\(D_2\) onset|
  |---:|---:|---:|---:|
  |0.100|12914903|12911611|18002111|
  |0.110|12894487|12894433|12902077|
  |0.120|8789189|8789189|12878431|
  |0.150|5001809|5001809|7105289|
  |0.160|3474797|3474797|5001907|
  |0.190|3451829|3451829|3459541|
  |0.197|3446081|3446081|3457513|
  |0.199|2278421|2278421|3455719|
  |0.200|2278383|2278382|3452179|
  |0.220|1526687|1526521|2275993|
  |0.270|1195361|1195361|1513777|
  |0.280|910307|910307|1198583|
  |0.299|624917|624917|912581|
  |0.300|624917|624917|912560|

  At fixed original coefficients, there are earlier **real** onsets. The exact first point of the final ray is the single root of the indicated normalized magnitude equaling the coefficient in each open bracket:
  
  |Error|Coefficient|Root bracket (right endpoint is a sufficient onset)|
  |---|---:|---:|
  |\(L^3|D_1|\)|.2|\((2278382.111,2278382.115)\)|
  |\(L^3|e^Z-1|\) (reciprocal product)|.2|\((2278381.70,2278381.73)\)|
  |\(L^3|e^{-Z}-1|\) (product)|.2|\((2278381.56,2278381.59)\)|
  |\(L^2|D_2|\)|.3|\((912559.996,912559.998)\)|

  There is no violation at the root (non-strict inequality), but there are violations immediately to its left. The claim of exact onset refers to that coefficient, not to the best onset of a different envelope. In particular, actual certified witnesses obstruct carrying coefficient .199 back to the original \(D_1,Q\) integer onsets, or .299 back to the original \(D_2\) integer onset.
* A plateau-shaped branch: for \(L\ge100\), the reciprocal sum and both products have errors \(<2.10\cdot10^{-12}/L\), and \(|D_2|<1.05\cdot10^{-12}\).
* For each row \((v_0,c)\) below and all \(L\ge v_0\), the reciprocal sum and both products have errors \(<c\,e^{-L/8}/L\); \(|D_2|<c\,e^{-L/8}\). These spectral bounds have no log-squared loss, and have stronger constants than simply integrating a pointwise psi majorant.

  |\(v_0\)|\(c\)|
  |---:|---:|
  |130|.065|
  |150|.031|
  |175|.023|
  |190|.021|
  |200|.0195|
  |250|.0166|
  |400|.0136|
  |1000|.01151|
  |5000|.01065|
  |20000|.0105|

Use the **pointwise minimum**, also with the non-rounded and signed branches below; no equality between the P and Q envelopes is required. For \(1<x<2\) the empty products and sums are exact; for \(2\le x\le250000000\) there is also the direct finite pointwise enclosure using the certified constants and finite prime sums, as described below.

### Matched-domain comparisons

Dusart 5.6 gives .2 from 2278383 for \(D_1\), 5.7 gives .3 from 912560 for \(D_2\), and 5.9 gives .2 from 2278382 for both relative products. On every matched domain a smaller table coefficient of the same shape is genuinely stronger; larger coefficients with earlier onsets have distinct domains and are not replacements. Use the real-root improvements for the fixed original coefficients. The spectral branches at \(L\ge200\) strictly dominate these polynomial branches and the displayed CH2-weighted plateau, for both shapes: \(c e^{-L/8}\) decreases, and \(L^2e^{-L/8}\) decreases there. Checking at 200 suffices (e.g. \(.0195e^{-25}<1.05\cdot10^{-12}\), and \(.0195\cdot200^2e^{-25}<.10\)). A plateau and an inverse-log branch alone are incomparable on unbounded overlapping domains if the plateau is smaller at the left: for example the plateau \(2.10\cdot10^{-12}/L\) meets \(.10/L^3\) at \(L=\sqrt{.10/(2.10\cdot10^{-12})}\), and the spectral bound is stronger by then. This comparison is about the stated bounds, not exact arithmetic errors.

The pointwise construction preserves strong available original transfers, not just the direct Dusart coefficients. Incorporate **all** available psi or theta envelopes at their exact arguments before transferring, including CH2, finite RH, all applicable rows of Dusart and PT, and FKS Theorems 1.1–1.2 and Corollary 1.4. It is not asserted that this lists every possible new consequence of the originals. Equality of the strongest lawful B0 and B0+D01 envelopes follows for *every* branch from the exact implication in psi.md. In this transfer specifically, \(q_\psi(v)\) is already below the D01 input everywhere it could be inserted, and D01 is unavailable earlier. The additional assumption does not improve a power, log factor, onset, constant or envelope here.

## Signed envelopes and transfers

These formulas specify a pointwise envelope on whole domains, including intermediate transitions. All integrals are ordinary real integrals of explicit envelopes (piecewise when validity starts or ends). Let \([\ell(v),u(v)]\) be an interval for \(E(v)=(\theta(e^v)-e^v)/e^v\). Intersect:
1. The original theta bounds: Dusart Theorem 4.2 (each row, PDF p.11), PT Corollary 1 (all rows, pp.2–3), PT Lemma 6 (p.9) and PT finite RH Corollary 1 (p.4) within their finite domains.
2. For each applicable psi bound, shift its lower endpoint by \(-p(v)\) and its upper by \(-.9999e^{-v/2}\) at \(e^v\ge121\), or by zero otherwise. Psi bounds here include CH2 Corollaries 1.2, 1.3, 9.3 and Lemma 9.2 (PDF pp.3,35–36) on their exact domains, Dusart Theorem 3.3 (PDF p.7) and its bounds, FKS Corollary 1.4 and applicable (1.6)/Table 5 and 6, PT Theorem 1 (Table 1), PT finite RH Corollary 1, and \(q_\psi(v)\) from psi.md for \(v\ge100\). For example, in CH2 Corollary 1.2 choose the infimum over permissible \(T\le3000175332800\), with \(T\ge10^7\) and \(e^v>\max(T,10^9)\), retaining the precise center \((\pi/T)\coth(\pi/T)\). In using CH2 Corollary 9.3 require its finite-RH hypothesis with the stated \(T(v)\); it is never extended beyond verified height. Include \(|E(v)|<.020e^{-v/8}\) from 200 onward, or sharper exact forms.
3. Additional estimates may be intersected whenever proved from B0. In particular, any legitimate original-parameter variant can be used without weakening any of these branches. The coarse bound \(|E|\le1\) at \(e^v\ge1\) (Dusart Theorem 4.2 \(k=0\) plus nonnegativity) can always be retained.

By partial summation and the limits in Dusart 5.6–5.7,
\[
 D_1(x)=E(L)/L-\int_L^\infty E(v) w(v)\,dv,\quad w(v)=(v+1)/v^2;\qquad
 D_2(x)=E(L)-\int_L^\infty E(v)\,dv.
\]
For each of these the lower endpoint is obtained with \(\ell(L)\) in the endpoint and \(u(v)\) under the subtracted integral, and vice versa for the upper endpoint. The negative sign matters, e.g. the CH2 small-\(x\) upper bound for theta relative error is actually negative after the prime power subtraction. With
\[
 J(x)=\sum_{p>x}\left[-\log(1-1/p)-1/p\right]
\]
one has \(Z=D_1-J\). In particular \(0\le J\le2/[L(x-1)]\) for \(x\ge2\): bound each summand by \(1/[2p(p-1)]\), then use \(\sum_{p>x}(\log p)/p^2\le4/x\) by partial summation with \(\theta(t)\le2t\). For a sharper signed interval let \(j(t)=[-\log(1-1/t)-1/t]/\log t\), positive and decreasing. Use \(J=-\theta(x)j(x)-\int_x^\infty\theta(t)j'(t)dt\) and the theta intervals above, intersecting with the cheap bound. Whichever \(Z\) interval \([l,u]\) results after intersections, the separate envelopes for Q and P are respectively \(\max(e^u-1,1-e^l)\), \(\max(e^{-l}-1,1-e^{-u})\).

There is a stronger transfer of the CH2 weighted branch. Write \(S_\Lambda(v)=\sum_{n\le e^v}\Lambda(n)/n-(v-\gamma)\), and \(B(x)=\sum_{m\ge2,\ p^m>x}(\log p)/p^m\). Then \(D_2=S_\Lambda(L)+B(x)\). If \(A(t)=\psi(t)-\theta(t)\), partial summation gives \(B(x)=-A(x)/x+\int_x^\infty A(t)t^{-2}dt\). Using the power corrections in psi.md gives
\[
 0\le B(x)\le 1.000100294 e^{-L/2}+2.67e^{-2L/3}\quad(x\ge121).
\]
For \(F_\Lambda(x)=\sum_{2\le n\le x}\Lambda(n)/(n\log n)\), the normalization is
\[
  F_\Lambda(x)-\log L-\gamma
    = S_\Lambda(L)/L-\int_L^\infty S_\Lambda(v)/v^2\,dv.
\]
Partial summation proves this since \(S_\Lambda\) is bounded and the left side tends to zero by Dusart 5.6 and the convergent prime-power correction: \(\sum_{p,m\ge2}1/(mp^m)=\gamma-M\). If \(C(x)=\sum_{m\ge2,\ p^m>x}1/(mp^m)\), then \(D_1=F_\Lambda-\log L-\gamma+C\) and \(Z=F_\Lambda-\log L-\gamma+C-J\). In these formulas \(0\le C-J\le C\le B(x)/L\). More precise signed intervals for \(B,C\) follow from \(dA\) and the corresponding decreasing weights \(t^{-1},(t\log t)^{-1}\), as above for \(J\). Obtain \(S_\Lambda\) from CH2 Corollaries 1.2 and 1.3 (or Proposition 9.1 at \(\sigma=1\) on its original domain), intersecting with the endpoint-minus-tail formula like \(D_2\) but with \(\psi\) (or use \(S_\Lambda=D_2-B\)). This yields additional branches for all four outputs. For the simplified plateau, use \(a+113.67e^{-v/2}\) for \(|S_\Lambda(v)|\), \(a=1.048\cdot10^{-12}\); monotonicity bounds the transfer by \(2(a+113.67e^{-L/2})/L\) before adding \(C\). Check the rounded constants at 100 as in mcert.py. We did not use the potentially ambiguous normalization in the extraction of CH2 Lemma 9.2's separate weighted sum line (9.1).

Intersect the direct polynomial, signed transfer, weighted transfer, and spectral envelopes; the absolute envelope is the minimum of each valid absolute bound and that obtained from each signed intersection. For fixed positive small \(x\) the finite sums plus the computed intervals for \(\gamma,M,B_3\) can be included directly without any grid on \(x\). This prescription specifies the whole-domain pointwise combination, rather than selecting a branch by sampled crossovers.

## Spectral improvement: remove the factor 9 in the leading tail coefficient

We use an absolutely convergent subset of zeros, not a full without-truncation explicit formula. Let
\[
 V(v)=-2\Re\sum_{\beta\ge.78,\ \gamma>0} e^{(\rho-1)v}/\rho .
\]
All these zeros have \(\gamma>H\) and \(\beta\le b=7/8\). The estimates of psi.md give \(|V(v)|\le e^{-v/8}Z_c(v)\), where
\[
 Z_c(v)=.010445\,v/(v-92)+W(.78,h;7.798,4.101)e^{-3v/40}.
\]
For \(v\ge100\) use the explicit formula with \(T=e^{v/3}\) and compare to \(V(v)\):
\[
 E(v)=V(v)+\mathcal D(v),\qquad |\mathcal D(v)|\le e^{-v/8}d_c(v).
\]
The same bound suffices if \(E\) here is replaced by the relative psi error. Specifically
\[
 d_c(v)=.018v^2e^{-3v/8}+.009v^2e^{-.095v}
       +2.091v e^{-5v/24}+e^{v/8}p(v)
       +\sum_{i=0}^5 W(s_i,v/3;c_i,d_i)e^{(s_{i+1}-b)v}.
\]
Take \(s_i=.78,.80,.82,.84,.86,.87\), \(s_6=b\), and the corresponding density coefficients in psi.md. The first two terms bound the contribution \(\beta\le1/2\) and \(1/2<\beta<.78\) by the symmetric ordinate estimate for \(T=e^{v/3}\). The last sum bounds omitted high zeros (those above the *actual* cutoff \(T^\star\) are a subset of those with \(\gamma\ge T\)); the last bin includes \(\beta=b\). The errors retain all prime powers and the explicit truncation remainder. Every summand in \(d_c\) is decreasing for \(v\ge100\) (for \(W\), use \(q/(v/3)<\alpha\) and the increasing positive denominator \(\alpha-q/(v/3)\)). Likewise \(Z_c(v)\) is decreasing. The functions are fully given in mcert.py. Absolute convergence from the fixed density at \(.78\) permits integration term by term with the exponential tail domination.

For a nonincreasing differentiable weight \(w(v)>0\) (use \(w=1\) or \((v+1)/v^2\)), integration by parts of \(e^{i\gamma v}\) against \(e^{(\beta-1)v}w(v)\) bounds the absolute value of each integrated term by \(2e^{(\beta-1)L}w(L)/\gamma\): its boundary and total variation are each \(e^{(\beta-1)L}w(L)\). Thus the integrated \(V\) contributes at most \((2/H)e^{-L/8}Z_c(L)w(L)\), not an integral of the pointwise absolute majorant. The integrated remainder contributes at most \(8e^{-L/8}d_c(L)w(L)\). This proves
\[
\begin{split}
 |D_2|&\le e^{-L/8}\big[(1+2/H)Z_c+9d_c\big](L),\\
 |D_1|&\le (e^{-L/8}/L)\big[(1+(2/H)(1+1/L))Z_c+(9+8/L)d_c\big](L).
\end{split}
\]
For \(Z\) use the same second normalized coefficient with \(3e^{-7L/8}\) added for \(J\), since \(LJ e^{L/8}\le 3e^{-7L/8}\). If \(d\) is an upper bound on \(|Z|\) with \(d<1\), then the envelopes for both products are at most \(d/(1-d)\) by the exponential series. The resulting normalized coefficients decrease on the admitted ray. mcert.py checks each spectral onset, including the conversion slack. The exact limit of each of these normalized coefficients is \((1+2/H)\,.010445=3133500000002089/300000000000000000\), not \(.010445\); the extra factor survives even as \(L\to\infty\). Here \(H=3\cdot10^{12}\) as in the original formulas and code. All ten rounded rows remain valid; see [repair](repair.md) for a *different* and smaller spectral envelope, with a genuinely smaller exact coefficient limit. These are upper-envelope limits, not asymptotic formulas for the errors.

## Finite and analytic certificates for the polynomial rays

**Analytic joins.** It suffices to prove the smallest coefficient .10 for \(L\ge19.3\); \(e^{19.3}<250000000\). Let \(b_0=29.9\). For \(19.3\le v\le b_0\), CH2 Lemma 9.2 and the signed power correction imply
\[
 -1.83e^{-v/2}\le E(v)\le-.2089e^{-v/2}.
\]
Specifically \(-.751\sqrt{x}<\psi-x\le.791\sqrt x\) on \([10^4,10^{13}]\), and the upper power error has coefficient at most \(1.000000147+1.78e^{-19.3/6}\). At \(b_0\le v\le58\) use the standard finite-RH theta bound \(v^2 e^{-v/2}/(8\pi)\) (the domain in PT finite RH Corollary 1 covers this, or PT Lemma 6). From 58 through 200 use the CH2 theta bound \(a+115e^{-v/2}\); thereafter use \(.020e^{-v/8}\). Thus the absolute integral after 58 is \(<2.1\cdot10^{-10}=T_{58}\); after \(b_0\) it is bounded by \(B=2(b_0^2+4b_0+8)e^{-b_0/2}/(8\pi)+T_{58}\). For the weighted kernel after a cutoff multiply its absolute integral bound by the kernel at that cutoff.

On \([19.3,b_0]\) one gets
\[
\begin{split}
 D_2&\le 3.4511e^{-L/2}+B-3.66e^{-b_0/2},&
 -D_2&\le1.83e^{-L/2}+B,\\
 D_1&\le (3.4511+3.66/L)e^{-L/2}/L+w(b_0)B,&
 -D_1&\le1.83e^{-L/2}/L+w(b_0)B.
\end{split}
\]
For the upper side of \(Z\) use the upper side of \(D_1\) (subtract \(J\ge0\)); for its negative side add \(2/[L(e^L-1)]\). The sufficient product condition is \(|Z|\le .1/(L^3+.1)\). mcert.py uses small rational cells here with each decreasing bound at the left and the multiplying increasing power or \(L^3+.1\) at the right. On \([b_0,58]\) bound the endpoint plus finite-RH tail by integrating the corresponding exponential polynomial all the way to infinity and adding \(T_{58}\) with its kernel. The polynomial-times-\(e^{-L/2}\) scaled contribution is decreasing there; bound the added constant tail with the upper \(L=58\). On \([58,200]\) bound the endpoint at 58, the entire integral by \(T_{58}\), and use the upper \(L=200\) for the polynomial factor. On \([200,\infty)\) use the .020 theta exponential: the scaled envelope for \(D_2\) is \(.18 L^2 e^{-L/8}\) and the one for \(D_1\) is \((.18+.16/L)L^2e^{-L/8}\) (before using \(L^3+.1\) instead of \(L^3\) for the product and adding \(J\)). Each required normalized expression decreases there. These steps, with numeric checks in mcert.py, prove the analytic rays, not just checks to a finite upper cutoff.

**Finite constants and prime sums.** mertens.cc implements an exact Eratosthenes sieve through \(N=250000000\), with fixed-point interval sums at scale \(D=2^{56}\). The sieve marks every composite from the square of its least prime factor, and never a prime. Reciprocals are bounded by a quotient floor and its successor; a log interval is used for \(\log p/p\). For \(\log Q_{\rm raw}\), add \(\sum_{m\ge2}1/(mp^m)\) at each prime up to \(p^m\le D\), with remaining tail less than \(2/D\) by the geometric series. Accumulate both ends, and apply these same routines to the constants up to \(N_0=10^7\). The Euler constant lies between \(H_{N_0}-\log N_0-1/(2N_0)\) and that value plus \(1/(6N_0^2)\): telescope the trapezoid differences of \(1/t\) on the unit cells from \(N_0\) to infinity. Each trapezoid excess is between zero and \(\max(2/t^3)/12=1/(6n^3)\) on \([n,n+1]\), by the integral interpolation error, and \(\sum_{n\ge N_0}n^{-3}\le N_0^{-2}\). The harmonic sum uses scale \(2^{84}\) before outward conversion.

For the tails of \(\gamma-M\) and \(B_3-\gamma\), use \(|\theta(t)/t-1|\le\eta=.2/\log^2 N_0\) for all \(t\ge N_0\) (Dusart Theorem 4.2). The B tail is \(1/N_0\) with lower error at most \(3\eta/N_0\) and upper error at most \(3\eta/N_0+4/[N_0(N_0-1)]\): first sum \((\log p)/p^2\) by parts, then use the geometric factor. The correction tail for \(M\) has main term \(\tfrac12\int_{N_0}^\infty dt/(t^2\log t)\), weighted theta error at most \(\eta(3+1/\log N_0)/(2N_0\log N_0)\) on either side, and higher powers contributing between 0 and \(1/(3N_0^2)\). For the latter bound sum \(1/[3n^2(n-1)]\) over integers \(n>N_0\), using \(n-1\ge N_0\) and \(\sum n^{-2}\le1/N_0\). Evaluate the main integral by the finite geometric identity for \((\log N_0+u)^{-1}\) against \(N_0^{-1}e^{-u}du\). Truncation through degree 10 has negative remainder of absolute value at most the next factorial term. mcert.py constants() reproduces the exact dyadic endpoints embedded in the C++ source.

For log intervals in C++, reduce a positive argument to \(2^k\) times its mantissa in \([1,2)\), with that mantissa rounded down within \(1/D\). Use the nearest lower table point \(1+i/256\) and the ratio for the residual. The log series is \(2\operatorname{atanh} z=2\sum_{j\ge0}z^{2j+1}/(2j+1)\). Use 32 terms with \(z\le1/3\) for table/constant and four with \(z\le1/512\) for the residual. Both tails are \(<1/D\). All recurrences round down; the error in a power, in dyadic units, is \(<4\) inductively using \(z^2\le1/9\), the floor errors, and initial \(z\) error \(<1\) unit. Thus the log sum error is at most \(2\cdot5\) units per term plus one tail unit; add the mantissa reduction error and at most 32 multiples of the log 2 error. The source allowance of 16384 units exceeds this total. All divisions and comparisons are integer (128-bit intermediates); unsigned ranges follow from \(D=2^{56},p\le N\), \(\log N<20\), and \(\theta(t)\le2t\) giving \(\sum_{p\le N}\log p/p\le2+2\log N\), while harmonic/product sums are smaller than \(2+2\log N\). The correction term denominators \(mp^m\) under the loop are at most \(56D\); the power update is guarded. The squared/cubed log bounds use 128-bit multiplication with at most 126 bits, and threshold comparisons use divisions to avoid multiplying a large log cube by a large sum.

**Finite joins and real roots.** Check both sides of every prime jump and the two finite cut boundaries. Between events the sums \(\sum p^{-1},\sum\log p/p,\log Q\) are constant. Their admissible interval endpoints as functions of \(x\), e.g. \(\log L+M\pm c/L^3\) or \(\log L+\gamma\pm c/(L^3+c)\), are increasing for \(x\ge1000\) at all tested coefficients. Thus success at both adjoining endpoints proves the entire open cell (and each included endpoint uses its own count). The point recorded as the integer onset is the first checked endpoint strictly after the last flagged test; a flag is not in itself a certified counterexample. Using \(|Z|\le c/(L^3+c)\) gives both product errors \(\le c/L^3\). The finite-high endpoint overlaps the analytic joins. The source's original onsets are checked independently here at the direct computation tier.

For the finer fixed-coefficient joins, witness.py replays the enclosures at two rational offsets in one non-jumping cell using the right sums at its left integer. The tested errors are positive in magnitude there, \(D_1,D_2,Z>0\), with all signs fixed on each tiny cell through its right integer (by their unscaled monotonicity and endpoint values, or directly from the constant sums). The derivatives with respect to \(L\) of the normalized positive errors divided by \(L^2\) are \(3D_1-1,\ 2e^Z-3,\ 3-4e^{-Z}\) for \(D_1,Q,P\) respectively, and the normalized weighted sum derivative is \(2L D_2-L^2\). They are strictly negative on the relevant unit cells, using the small errors there. This proves uniqueness and the claimed exact non-strict real onsets, joined at the following integer to the already checked ray. Certified actual violations at the indicated early values distinguish real coefficients from merely conservative test flags.

## Attempts and remaining bottlenecks

A single absolute theta bound transferred mechanically to the tails incurs a factor roughly 9; transferring a direct majorant with a log-squared term also loses the stronger log power at the boundary. The mixed weighted CH2 branch improves the finite plateau, and the absolutely summable high spectrum plus integration by parts removes the factor from the leading asymptotic coefficient. Treating the whole zero sum as absolutely convergent at the boundary would be invalid. The split at .78, nonuniform omission bins, and the sharper Taylor upper bound for the density tail improve the earlier spectral coefficients; using only a single omitted tail at .8 is substantially worse at \(L=130\)–175. Near original polynomial onsets the exact certificates find real obstructions to fixed-onset coefficient reductions of the sizes quoted above; they are not inferred from sample spikes or from interval flags. The stronger later-onset table and separate real joins preserve the useful tradeoffs. Further reduction of spectral leading constants would need sharper high-zero density/phase information or tighter coefficient bounds; no zero-free strip to the left of 7/8 or sharp lower obstruction to the exponent is claimed.
