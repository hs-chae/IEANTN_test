# Secondary B0-only improvement: small inverse-log coefficients

Keep the complete D01 finite envelope and exact old real onsets. The new table gives additional tradeoffs for the same shapes: \(|D_1|,E_P,E_Q\le c/L^3,\ |D_2|\le c/L^2\). Each onset is an inclusive **real** x. Larger coefficients or exact lower onsets from the inherited table may dominate before a new onset. None of these rows needs D02.

| c | D1 and both products | D2 |
|---:|---:|---:|
|.0378|187513357|190405273|
|.0380|187511879|190400939|
|.0381|187511393|190400827|
|.0382|187510369|189449081|
|.0383|187510327|189448933|
|.0385|187499419|189448201|
|.0390|180639383|188200153|

The last row improves the inherited .0391 at only slightly later onsets. At larger matched x the smaller coefficients improve the bound strictly. The .0375 row in the scan is **not** asserted beyond its finite cutoff: the first analytic interval fails the sufficient test.

## Finite and analytic evidence

Use lowpoly2.cc, exactly repair_mpoly.cc with the trial list changed. Its pre/post-event proof (including monotonicity of the admissible state intervals, integer range and directed arithmetic) is in repair_poly.md and D01_M_REVIEW_review.md; it applies verbatim to the new coefficient range. State bounds are compared to rational thresholds scaled by \(2^{56}\); assertions were enabled. The new scan covers the inclusive cutoff \(4\cdot10^9\), and each listed join in lowpoly2_scan.out has no subsequent flag. A flag is failure of a sufficient state test, not necessarily failure of the true inequality. Thus the table gives sufficient onsets, not automatically optimal ones.

For the analytic join \(L\ge22.109\), check \(e^{22.109}<4\cdot10^9\). Extend the signed CH2 Lemma 9.2 (PDF pp.35–36) plus prime powers to \(b=29.933\), with \(e^b<10^{13}\). Instead of freezing a coefficient 1.83 for the negative theta error, use the actual two powers
\[
 -A e^{-v/2}-Qe^{-2v/3}\le E(v)\le -D e^{-v/2},
 \quad A=1.751000147,\ Q=1.78,\ D=.2089 .
\]
Set \(I_L=2A(e^{-L/2}-e^{-b/2})+(3/2)Q(e^{-2L/3}-e^{-2b/3})\).
On \([b,58]\) integrate the signed theta bounds of early2.py ca() over full cells with the appropriate decreasing kernels: for each cell use its coefficient interval times \(e^{-l/2}\) and (for the weighted version) \(w(l)\), times the cell length. To these sums add the inherited \(2.1\cdot10^{-10}\) after 58 and \(w(58)\) times that bound, respectively. Let the resulting upper bounds for the positive and negative signed tails be \(T_+,T_-\) without weight and \(H_+,H_-\) with weight. These are each **upper** bounds on the corresponding signed integral, not lower bounds on the actual integral. Using endpoint-minus-tail gives, for \(22.109\le L\le b\),
\[
\begin{split}
 D_2&\le -D e^{-L/2}+I_L+T_- ,\\
 -D_2&\le A e^{-L/2}+Qe^{-2L/3}-2D(e^{-L/2}-e^{-b/2})+T_+,\\
 LD_1&\le -D e^{-L/2}+(1+1/L)I_L+LH_-,\\
 -LD_1&\le A e^{-L/2}+Qe^{-2L/3}-2LDw(b)(e^{-L/2}-e^{-b/2})+LH_+ .
\end{split}
\]
Use the same upper bound for \(LZ\), and add \(2/(e^L-1)\) to the bound for \(-LD_1\) to get the bound for \(-LZ\). The code encloses each full cell by directed evaluation. For products the sufficient mixed threshold is \((L^2+c/L)L|Z|<c\), which implies \(E_P,E_Q<c/L^3\) via the exponential-series bound. The analogous check for \(|D_1|\) also then passes. Finite joins use steps at most .001. From b through 58, 58 through 200, and 200 onward keep the prior full-interval and decreasing-tail estimates from repair_mpoly.py, with b changed and all obligations rechecked by lowpoly2.py. This completes the entire ray including overlap. The older .039-at-22.1 failure and current .0375 failure are insufficient-method outcomes, not arithmetic counterexamples.

This branch uses extra precision in small-\(x\) signed arithmetic, not the new strip. Replacing only the post-58 tail with the D02-based narrowing is lawful but acts on the tiny remote-tail term; it is not credited with the improvement from the connected finite scan or the local two-power refinement.
