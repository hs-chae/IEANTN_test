# FOLLOWUP-D02 — research portfolio

**Both families are ready for independent mathematical review.**
Original-source trust is retained throughout; full RH is not assumed.
B0 is the original corpus, B1 adds exactly the packet hypothesis.
The B0 comparator is a matched reconstruction, not a blind run.

* **Ramanujan.** The original inputs already give a connected strict
  ray after the exact last real failure in
  (38358837682.217926, 38358837682.217927), repairing a real-endpoint
  issue in the printed PT theorem. The extra hypothesis instead
  improves higher-order margins. For example the bound
  R > (x²/L⁶)(1+14/L+80.7/L²) is certified from L=49 under B1
  versus L=197 for the displayed B0 certificate. The coefficient
  1412 in the next full order is certified from 211.11 rather than
  253.65. See ramanujan.md for the functional profile, margin and
  onset tables, density-free fallback, exact endpoint proof and
  finite-to-analytic joins.
* **Mertens.** With B1, both relative product errors and the
  reciprocal-prime sum error are at most .256857 x^(-5/32)/L
  and the weighted prime-sum error is at most .256857 x^(-5/32)
  for L≥200. The matched B0 row has .018312 at exponent 1/8;
  B1 wins throughout the matched ray. The full constructed envelope
  improves strictly for L≥168.82. There are also independent
  improvements at small x, including least real onsets for the
  original Dusart coefficients. See mertens.md.
* **Method.** spectral.md proves the extra zero cutoff, the absolute
  endpoint estimate, and the absolutely convergent once-integrated
  formula that keeps the leading Mertens constant from acquiring
  a partial-summation factor. Original FKS density-corollary use
  and a no-density fallback are distinguished.

## Replay
Run from this directory with the offline Python interpreter:

    /usr/bin/python3.10 -B bounds.py all
    /usr/bin/python3.10 -B finite_m.py

For separate checks use modes ram, mertens, endpoint for bounds.py.
The outputs are reproduced in replay.txt and finite_replay.txt.
The directed arithmetic uses Decimal with 48 significant digits:
ordinary operations round outwards, exp/ln are correctly rounded
in their Decimal implementation and enclosed by adjacent Decimal
numbers. Pi uses Machin's identity and alternating arctangent
series; the integer counting parts use exact integers. The proofs
of the inequalities over the checked cells and of the decreasing
analytic tails are in the claim files; the computation is not
merely a sample. No Lean or source-first PV is claimed.

sources.txt gives the actual SHA-256 receipts of all seven originals
and text extractions, checked against SOURCE_INDEX.json. attempts.md
records completed and remaining work. LOCK.json binds the payload.
