# FOLLOWUP-D02: both-family research portfolio

The exact input
[
 |psi(x)-x|le x^{27/32}(log x)^2/64 qquad(xge e^{200}, x 	ext{real})
]
implies that (zeta) has no zeros with (Re s>27/32).
The common original QRH bound is (Re
hole7/8), and is
fully retained. Using the stronger boundary for (zeta)
alone, FKS and finite RH give a log-free zero-strip majorant
valid even before the stated input threshold. Integrating
the oscillating high-strip term *before* taking its absolute
value sharply improves both Mertens weights. The same proof
with (7/8) gives a strengthened, matched original-only
(B0) control. This is not an independent blind B0 run.

## Main results

* **Ramanujan.** The early exact real strict-positivity ray
  remains (x>r), where
  (38358837682.21792636<r<38358837682.21792637) and (R(r)=0).
  No hypothesis can move the onset earlier for the same
  function. B0 already improves many early quantitative
  margins: for (G=(log x)^6 R(x)/x^2), (G>1) on
  (log xge42.5), before the previous 43.16, and
  (G>.50) from 40.23 instead of 40.5.
  D02 strengthens the exact-Li lower envelope of the
  furnished B0 error bounds from (log xge171).
  It improves connected polynomial rays even at some earlier
  starts: from (log xge49), for example, the new certified
  coefficient of (1/(log x)^2) in (1+14/log x+c/(log x)^2)
  is 64 versus the exhibited B0 coefficient 2.
  The true Li polynomial (M_2) begins at log 188 (matched
  B0: 222); (M_{19}) at log 642 (B0: 830).
  For every (jge35), the explicit linear onset
  (28(j+5)) gives (M_j+.07(j+5)!/(log x)^{j+1})
  with D02, versus that margin at (37(j+5)) with B0.
  At the same later onset (37(j+5)) the margins .14 (B0)
  and .18 (D02) are certified.
* **Mertens.** On all real (xge e^{169}), use
  (.300x^{-5/32}/log x) for both relative product errors
  and the reciprocal-prime-sum residual, and
  (.300x^{-5/32}) for the log-weighted prime-sum residual.
  The coefficients can be reduced to .2582 from log 200,
  .2071 from 300, and .160 from 1250.
  At log 200 the matched new B0 coefficient is .01831 in
  the weaker (x^{-1/8}) units; the D02 cap is less than
  .028 times that cap on the whole common ray.
  The log-power coefficient (10^{-9}) is certified from
  log 192 versus log 220 in the matched B0 proof.
  There are signed pointwise bounds and additional finite,
  original, and analytic branches, giving a joined envelope
  throughout (x>1). New finite cells extend to (x=2)
  without D02.

An exact whole-ray power bound of the D02 strength in
**any one** of these four Mertens errors, or even a one-sided
Ramanujan Li-discrepancy bound of the D02 power shape, implies
the stronger zeta zero restriction. This identifies a
structural bottleneck for improving the exponent, without
asserting that B0 cannot prove D02 or that the known
constants/onsets are optimal. See `sharpness.md`.

## Review map

* `d02-proof.md` proves the spectral restriction and both
  analytic transfers, with source locators and explicit formulas.
* `ramanujan-d02.md`, `mertens-d02.md` contain exact statements,
  joins, table comparisons, and the whole-domain envelopes.
* `sharpness.md` gives the converses.
* `research-notes.md` gives replay commands, evidence, and
  limitations including failed attempts.
* `D01-candidate.md`, `ramanujan.md`, `gap-results.md`,
  `orders.md`, `mertens.md`, `density.md` and their associated
  files are the inherited reviewed floor, not claims
  of a new D01 run. D02 implies D01 directly, and under
  cumulative premises D01 was already redundant.
  The own claim registry and review provenance are retained.

Trust: original papers and their reported computations at the
permitted trust, written proofs, and independently replayable
ordinary exact arithmetic certificates. No full analytic Lean,
source-first PV, or new independent D02 review is claimed.
