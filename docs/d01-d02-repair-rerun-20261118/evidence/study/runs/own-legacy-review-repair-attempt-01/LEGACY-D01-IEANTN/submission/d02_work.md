# Work record
The exact hypothesis used is the A-D02 PsiMajorant. Initial source review identified CH2 Corollary 1.3 (finite RH, unconditional at original trust) and Dusart 4.3–4.5 and 5.6–5.9. Candidate routes: transfer the one-sided psi estimate through prime-power corrections; use signed integration and cancellation for Euler products; use high-order analytic approximants for the Ramanujan gap and bridge the two thresholds with finite RH. No new computations taken as premises.

Initial Mertens identity: for E(t)=ψ(t)−t and J=∑_{p^k≤x}1/(kp^k),
J(x)−log log x−γ = E(x)/(x log x) − ∫_x^∞ E(t)(log t+1)/(t² log²t)dt.
The constant follows from Dusart 5.9 since J−log Q→0 by convergence of all k≥2 terms. Direct absolute integration of PsiMajorant gives leading coefficient 37/320 in the L*x^(−5/32) Mertens error, before tiny prime-power terms. The later integrated explicit formula avoids this leading integral loss.

Some recorded dead ends: the original real endpoint in PT Theorem 2 cannot literally be used (exact sign computation shows a short counterinterval). Direct uncentered Schoenfeld estimates are too large to resolve the tight analytic transition at L≈37; the one-sided π<li citation and high-order li bounds are essential there for that route. The first bridge executable had a uint64 log-scale overflow; its output was discarded as evidence. The corrected certificate uses 128-bit storage for the full logarithm. Coarse mesh Mertens checks may fail even when the actual assertions hold; exact prime-jump checking addresses this.

75% bundle: the alternatives not using FKS numerical density tables are
the baseline of the submission. The unconditional smoothing argument
uses the supplied OpenAIQRH Theorem 1.1, not a strip assumed from memory.
Independent analytic certificates completed. The ordinary finite checks
do not replicate DP Lemma 3.4 or the finite RH source. A deeper use of
the explicit formula also removes the large absolute tail-integration
loss for the Mertens products and prime sums.
