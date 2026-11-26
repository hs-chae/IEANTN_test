# Source and verification record

* /task/COMMON_FACTS.md, facts (1)–(3), definitions and Original comparison:
  inputs for the written theorems. /source_pv/EXPOSURE.json identifies
  A_flat, with no application modules and no source-first added modules.
* /source_pv/FLAT_FACTS.txt: declaration headings
  IEANTN.CMSFunctional.GoodCoefficient, piReal, normalizedPopulation and
  halfOpenCount (the latter at lines 29076–29084);
  RH080Exposure.Estimates.flat, .gaussian and .sparse (58793–58803);
  RHAsymptoticGaussian.v4.population_curve; and
  RHWeightedPopulation.v1.sparseLine, .flatLine, .sparse_curve, .flat_curve.
  The exact typed terms in FLAT_FACTS.json control. Checked the display
  of the definitions against the standalone Lean restatements, including
  the natural subtraction and the association in the right endpoint.
  No application binary was linked. Existing types alone do not constitute
  replay of their proofs.
* CMS1708.04122v2.pdf §1.1, admissible-class and objective definitions,
  and §1.3, Theorem 3, (1.13) with B in (1.11) and its bound in (1.12);
  proof in §5 (especially §5.2). Frozen text companion lines 74ff,
  258–275, 996ff and 1056ff. The precise named assumption in the flat
  export is CMSFunctionalInput.v1.population_reduction, defined as
  IEANTN.CMSFunctional.SourceCMSPopulation (at 29007ff), in the form
  of a nonempty good-width set with its infimum bounded by the objective.
* Blanquer_Robles_2026.pdf §2.1, Lemma 5, (4), including the
  periodization argument, is the norm identity locator. The uniform
  estimate is §3, Proposition 6, (6), specialized to modulus one,
  with the combination in §3.4. Frozen text companion lines 128–157,
  336–349, 469–483. In the typed inputs, the first ranges over rational
  nodal lists with degree parameter m>0, length 5m+1 and zero endpoint;
  the second uses a positive attained sup bound M, positive D4 and c,
  and under RH has an eventual inequality with vanishing logarithmic
  remainder. This is not a derivation of either input from Mathlib RH.
* Octic: packet's preserved coordinator baseline, not a BR or CMS
  paper theorem. BASELINE_THEOREM_MATRIX.md lines 418–432 identify the
  corresponding strict quantile statement (a consumer not used here).
* C: /source_pv/population_norm.c and /source_pv/flat_population_norm.c
  are the assigned small fixed-point programs, not the original
  large FFT. In each file inspect coefficient from line 5, sine/sample
  and correction routines in the middle, and main at 91/90 respectively.
  Source-first scope supplied by the coordinator is the actual
  C-source-to-AST, execution model and numerical-to-ANT chain, under
  its supported C fragment/port semantics (integer operations and
  program interface as modeled), not a verified unrestricted compiler,
  runtime/library, OS, or hardware. No C++/CUDA extrapolation. This
  arm did not rerun or independently establish that chain; a native
  execution or source hash would not establish it either.

## Byte pins (SHA-256)

a2af3dac823957df76571c6031f149da3012e7507d4c5eac69e3a3f7c3ace394  /source_pv/FLAT_FACTS.json
f3a103e88bc9e0536ac84a8b8b7be6ecba9b4bbc530e877b53252f951cf0c138  /source_pv/FLAT_FACTS.txt
92c5832d3ecfdd08d7c4143ac155e47e61ee9f58700634cf4f04e7cf8fc84b09  /source_pv/population_norm.c
2556f5eddca7d218a5e6565b4defed53aab957063ffbfadf5104f511a5fc82d9  /source_pv/flat_population_norm.c
45b6c7f991831a2dc456c10285206cb17a53ef46c6ae15e43cfa5671554b0dce  /corpus/literature/CMS1708.04122v2.pdf
2f15da8545766012902e6dcc46f9bc4daa9951661dae2cc4809b97fd729dc380  /corpus/literature/Blanquer_Robles_2026.pdf

## Replay

Run with the assigned non-login /bin/bash executor:
    /bin/lean /work/submission/Transfer.lean
    /usr/bin/python3.10 /work/submission/arithmetic.py

The standalone Lean proof addresses the transfer conditional on the
curve propositions. The written proof identifies them with the given
premises; there is no application theorem import in A_flat. The Python
checks are exact rational tests of stated constants, not prime samples,
analytic verification, or source-first transfer. 

## Negative work record

A first Lean attempt used a nonexistent StrictMono.min lemma; the
replacement uses lt_min twice and separate comparisons. The endpoint
membership proof initially failed propositional automation until not_le
was exposed. Rewriting the prime successor count by primality directly
also failed; it needs the if-then reduction. The corrected proof is in
Transfer.lean. Neither the Gaussian limiting frontier without epsilon,
nor an application import/PV link in A_flat, is claimed proved.
