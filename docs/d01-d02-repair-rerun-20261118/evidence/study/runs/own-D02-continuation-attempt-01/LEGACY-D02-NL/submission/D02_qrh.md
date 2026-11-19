# Using the admitted QRH theorem: Ramanujan without PsiMajorant, and explicit power tails

This supplement uses OpenAIQRH (pinned original, PDF p. 4, Theorem 1.1, derivation ends p. 197) at its original trust status, not as a new proof/verification of that paper. It implies (etale7/8) for all zeta zeros in the critical strip, **including allowance of equality**. No claim of full RH is made.

## The bridge made unconditional relative to the original-source packet

For all reals (x>X_*) of ramanujan.md, (R(x)>0) **without PsiMajorant**, when the admitted QRH result is used. This holds strictly only above the unique last real failure (X_*). Further,
[
 R(x)>rac{x^2}{(log x)^6}left(1+rac{10.9}{log x}
ight)qquad(log xge48.25).
]
These make the QRH-based onset, the higher-margin A-D02 estimate in ramanujan.md, and the independent non-QRH result in that file three trade-offs. The margin increase to 13 (and the better exponential-power error at very large (x)) can still use PsiMajorant. The full-ray positivity here subsumes the original (e^{3915}) ray without changing the admitted input status.

## Explicit power bound

For (t=log xge258), define
[
 W(t)=rac{(t/8+2.94)^2-(26.88)^2}{6.28}+3.7284+rac{2.091}{48}t,qquad
 d_Q(t)=W(t)e^{-t/8}+117.5e^{-t/2}.
]
Then (|psi(x)-x|le xd_Q(t)). Apply FKS Theorem 3.2 (PDF p. 8, quoted Cully-Hugill–Johnston formula) with (T=48e^{t/8}), (T^starle2.45T), and ((log x_M,alpha,omega,M)=(40,1/2,0,2.091)). Its height bounds hold at 258 and thereafter by growth rates. For zeros up to height (H_0=3cdot10^{12}) use the finite-height RH of PlattTrudgianFiniteRH, Theorem 1 (p. 2). The reciprocal sum lemma is PlattTrudgian1809.03134v2, Lemma 2, PDF p. 4:
[
  left|2sum_{0<gammale U}rac1gamma-rac{(log (U/(2pi)))^2}{2pi}
ight|le1.8642
 quad(Uge2pi e).
]
At (H_0) the sum in this formula with prefactor 2 is (<117.5). For (H_0<gammale2.45T), subtract the lower bound at (H_0) from the upper bound at (2.45T). The result is (le W(t)-2.091t/48) by the elementary log bounds in cert.py. Use (|
ho|ge|Im
ho|), (etale7/8) on the upper group, (eta=1/2) below (H_0), and the truncation remainder. This proves the two-term bound for every real argument in the ray.

Since (W(258)e^{-258/8}<a) and (W'/W<1/40) on this ray, (W(t)e^{-t/8}le a e^{-(t-258)/10}) for (tge258). The logarithmic-derivative bound follows from (W/40-W'>0) and (W'/40-W''>0) at 258 and positive quadratic/linear leading coefficients. Below 258 use CH2. Thus in (1) of ramanujan.md replace (B) by 119 and (D) by (a e^{-(t-258)_+/10}), obtaining (r_Q). The proof of (1) works without change (the rate even decreases), and (3)–(4) hold with this radius. The code certifies the 10.9 margin on ([48.25,300]), and for (tge300) the decreasing loss (t{cal E}_Q(t)) is (<3). Together with the repaired source range this proves the full real ray. The gap's expansion through (t^{-4}) also holds with this radius.

## Explicit Mertens tails without PsiMajorant

For (tge258), put
[
 I_Q(t)=e^{-t/8}(8W(t)+64W'(t)+512W''(t))+235e^{-t/2}.
]
This is exactly the integral of (d_Q) from (t) to infinity. In the notation of mertens.md the unweighted (Lambda)-prime-power harmonic error is bounded by (d_Q(t)+I_Q(t)) (the function (H) there), and the logarithmic one ((K)) by (d_Q(t)/t+(t+1)I_Q(t)/t^2), since the weight ((s+1)/s^2) is decreasing. Add the same nonnegative spill bounds as in mertens.md before exponentiating. All four resulting whole-ray error envelopes are power-saving. On (tge258) their scaled errors are already (<0.001) (product/reciprocals times (t^3); logarithmically weighted prime sum times (t^2)), by the QRH endpoint test in mertens_tail.py and termwise monotonicity: (W'/W<1/40), also (W''/W'<1/40), so their products with (t^4) and (e^{-t/8}) decrease. Apply the bound at 258 and use the geometric-series inequality in mertens.md for conversion to relative errors. These results are independent of A-D02, but the smaller A-D02 majorant is superior eventually; the two valid bounds can always be intersected.
