# Primal frontier and weighted population search

This additive study preserves every original RH080Study experiment and source.
**Numerical scouting, exact-rational review, Lean-kernel proofs, and source-first
PV are different verification tiers.** This directory's Python and floating C
scouts are not source-first PV. The separate numerical-source lane owns the
actual source-first `population_norm.c` implementation and its formal execution.

## Mathematical results and pending boundaries

- The 18-case Gaussian–Laguerre screen varied degree28/56/112/224 and physical
  scale1/2,3/4,1,5/4,3/2 where recorded. It did not approach0.8339. The plateau
  near0.8339453 is a family-search observation, not a proof of optimality.
- The best completed fine-grid Gaussian candidate has Laguerre degree40,
  physical degree80 and scale5/4. Exact F(0)=1. Independent exact Sturm isolation
  and768-bit Arb give quotient0.833945311503705300010779583742... . The development Lean-proved
  kernel cap is20582561296/24680948495<0.833945313, compared with the previous
 82325773717/98718416336<0.833945448. The source Fourier transform and scaling
  are kernel-proved; all1124 exact integral cells and actual CMS gap/population
  consumers pass the development typed/axiom audit. The complete92-source cold
  replay also passes, including19 typed theorem roots and12 required proof
  edges. See evidence/GAUSSIAN_V4_COLD_RESULT.json; this is kernel-only
  verification, not source-first PV. **The Arb result alone is not a Lean
  theorem or an explicit-onset prime theorem.**
- Rational exponential–Laguerre, translated-Gaussian, and compact affine gap
  scouts did not beat the new Gaussian candidate. Significant negative outputs
  and all exact candidate inputs remain preserved.
- Directly optimizing the population objective `(N+2αM)/(F(0)-AJ)` atα=1 gave
  floating values2.04595338 (A=36/11) and2.06333452 (A=4.00001), both atmesh128.
  These are numerical candidates. They do not establish a new prime theorem.
- A much smallermesh8/support2/16-node candidate atA=4.00001 has independent
  rational bounds `N≤0.887621072901276`, `M=0.5468717131133098`,
  `J=0.014965734076441725`, and weighted quotient<2.12 on the256-node grid.
  Its exact input is `evidence/POPULATION_M8_R2_EXACT.json`. Zero-padding to40
  nodes places it literally in the primary support5 Fourier class. The
  source-first C lane computes the norm cap0.887721072633027910 with its own
  trigonometric error allowance. Its actual Fourier/norm and weighted ANT
  bridges are now complete under the explicit published norm identity and
  ordinary-RH q=1 population source proposition. A second zero-leakage C
  packet supplies the large-population slope16/15. The complete91-source cold
  replay and18-root axiom/source/control audit pass, proving the two whole
  eventual curves and their minimum. See population/README.md and
  evidence/POPULATION_CANONICAL_COLD_RESULT.json. The old explicit onsetexp24
  is not inherited; the matched kernel-only control proves the same result.

`ChordQuadrature.lean` proves the real analytic quadrature bound from actual
finite cosine coefficients, including absolute values at sign changes. It uses
convexity ofcos(x)+x²/2 and-cos(x)+x²/2, integrates the exact local chord error,
and sums every cell. There is no FFT hypothesis, certificate validity premise,
RH assumption or source execution in this analytic theorem.
`GaussianDilation.lean` proves the actual Mathlib Fourier scaling identity and
whole-line norm rescaling. All displayed audit closures use onlypropext,
Classical.choice andQuot.sound.

## Reproduction

Use Lean4.34.0-rc2 and mathlibcommit71a80585ee495fc24472fd0eaffc89d94e4fd8d6,
plus the dependency versions recorded by the campaign's generic context.
Build or retrieve only those pinned generic packages, then run:

```
python3 Solutions/RH080Next.v1/primal/reproduce_analytic.py \
  --compiler /path/to/lean \
  --generic-lean-path /path/to/mathlib/.lake/build/lib/lean:/other/generic/dependencies \
  --out /fresh/scratch/analytic
```

This fresh source replay strictly checks every requested axiom audit. It has no
application-object fallback and rejects missing or failed checks under normal,
`-O`, and`-OO` Python execution.

Search reproduction uses Python3.11.14, NumPy/SciPy versions in each receipt,
SciPy1.17.1 bundled HiGHS, deterministic seed0, and bounded solver threads.
For example:

```
python3 Solutions/RH080Next.v1/primal/run_population_screen.py \
  --out /fresh/scratch/population --workers 4
python3 Solutions/RH080Next.v1/primal/certify_population_chord.py \
  --candidate Solutions/RH080Next.v1/primal/evidence/POPULATION_M8_R2_EXACT.json \
  --grid 256 --A 4.00001 --alpha 1 --width 2.12 \
  --out /fresh/scratch/population-independent
```

`generate_scaled_gaussian.py`, `generate_scaled_fourier.py`, and
`generate_scaled_assembly.py` regenerate the new Gaussian input/transform/cell
sources using the unchanged generic rational arithmetic fromRH080Study.v1.
`compile_scaled_cells.py` snapshots exact selected sources, uses eight workers
with explicit `lean -j1`, records peakRSS/time/source/object hashes, and rejects
any nonstandard proof axiom. Development prerequisite-object reuse is disclosed
in those receipts; the campaign's complete cold closure is a separate gate.

The first eight-worker attempt inherited Lean's host-wide default thread count
and hit thread-creation failures, not OOM. It was cleanly terminated and retained
as an infrastructure interruption; unchanged mathematical cells were rerun with
`-j1`. See`MISTAKES.md`. No failed or interrupted run is promoted to success.
