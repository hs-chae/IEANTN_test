# Reproduction, scope, and factual work record

Run in the submission directory, using only Python 3.10:
\`\`\`
/usr/bin/python3.10 -B ray_check.py
/usr/bin/python3.10 -B endpoint_check.py
/usr/bin/python3.10 -B mertens_check.py
/usr/bin/python3.10 -B extra_check.py
\`\`\`
The largest individual sieve is through 10^8, 100 MB for flags plus
scratch and grid state. The Ramanujan endpoint uses a quotient sieve,
not a table up to 3.8·10^10. The calculations are deterministic exact
integer/rational checks, not certified by an external proof kernel.
See the captured text results and proofs for which assertions are
used. The weighted sum uses the unrounded narrow constant intervals,
not printed decimal approximations in the paper. No source identities
beyond the enumerated cited inputs and the proved elementary
calculus/arithmetic are asserted here.

**Candidate selection.**
* Ramanujan: sharp real onset and pointwise A-dependent margin in
  candidate.md; the unconditional ray/intermediate margins in
  extensions.md (a trade-off in assumptions, not a weaker result
  advertised as an improvement). The large-ray baseline is subsumed
  unconditionally. The literal low real interval has a documented
  local counterexample; only its integer restriction is employed.
* Mertens: (i) unconditional pointwise envelope including the finite
  coefficient frontier, (ii) sharp onsets for the benchmark fixed
  coefficient bounds, (iii) A-dependent oscillation-aware high ray.
  Reciprocal products and both prime sums in a candidate are
  correlated consequences, not independent evidence.
* Primorial normalization and short prime intervals are tertiary
  deductions, not assertions of best known bounds.

**Unsuccessful or superseded work.**
* The first plan (draft.md) targeted a bridge at log x near 200 by
  assuming the normalized Ramanujan main term began at log^(-5).
  Coefficient convolution shows it actually begins at log^(-4)
  after taking out x²/log²x. This eliminated the supposed bridge
  obstacle. Zero density remained useful for removing log² in
  PsiMajorant and the later oscillation/primorial bounds.
* We did not use the FKS Table 8 density constants: displayed δ
  values there are <1 while the extraction of Thm 2.7 states δ≥1.
  Rather than resolve that apparent mismatch, all uses of density
  are from Dusart Thm 2.3. FKS 3.2, 2.1/2.3 and 1.4 are used as
  separate stated source inputs. There is no claim that their
  literature dependencies were reverified.
* Bounding the theta integral by its absolute pointwise envelope
  loses a factor about 1+1/a in the high Mertens range. Near 10^8
  even .05/log² alone from Dusart does not beat .2/log³ after
  integration. The signed theta interval and CH2 Lemma 9.2 are
  essential to our shorter unconditional tail splice. The later
  absolutely summable high spectral expansion removes this loss
  on the A-ray and reaches a stronger primorial conclusion.
* A coarse finite cell grid and elementary all-integer tails for
  M, B3 gave much worse onsets (e.g. 12,877,232 for the .125 product
  error) and missed precision near the original weighted-sum onset.
  Replaced by prime-step guards and separately proven constant tails.
  Floating point sweeps were used only to select constants, never
  as certificates. The attempted .299999 at the first original weighted-sum
  point was proved false; .2999995 passes (see mertens.md).
* The initial 80-bit log interval sufficed for large-region bounds
  but not a 10^(-13)-wide Ramanujan root bracket. A rational
  60-term atanh tail was used for the exact local root instead.
* The interval [169,753] nearly uses up the fixed CH2 majorant;
  continuing it to 754 fails the simple positive-margin estimate.
  No unconditional bridge for 753<L<2840 is claimed.
* None of the high error estimates implies an eventual sign for
  the primorial normalized ratio; the remaining term can oscillate.
  Nontrivial zeros exactly on Re s=27/32 have not been excluded.

**Artifacts and checkpoints.** An early draft was saved, then analytic
and finite certificates were completed and locked. The 75% locked
version was preserved byte-for-byte in private scratch before further
improvements; subsequent versions use exact SHA-256 manifests.
No external searches, delegation, native tables or earlier-session
artifacts were used. Earlier mathematical claims have not been
silently repurposed: in particular the corrected noninteger endpoint
replaces the initially quoted literal source interval for actual use.
