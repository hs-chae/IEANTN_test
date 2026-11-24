# Gaussian witness: actual kernel numerical closure

This directory proves numerical bounds for the fixed degree-12 Laguerre candidate, represented as two rational degree-24 polynomials. This is **kernel-only verification**, not source-first PV. The Python generators supply untrusted rational suggestions; the Lean kernel checks their connection to the actual mathematical integrals.

The accepted numerical consumers are in `GaussianWings.lean`:

- `physical_norm_upper`: the actual integral of the absolute value of `physicalF` over the real line is at most **0.74899**.
- `physical_full_wings_upper`: the actual integral of the positive part of `physicalG` outside the closed unit interval is at most **0.031152**.
- `physicalF_zero_lower`: the value of `physicalF` at zero is at least **0.999999999**.
- `physical_full_objective_upper`: the norm divided by the value at zero minus **(36/11)** times the exterior positive-wing integral is at most **0.834021**.
- `physical_full_objective_lt_printed_2026`: this ratio is strictly below the printed **0.834050619151** comparison constant.

`physicalF` and `physicalG` are defined explicitly in `GaussianPhysical.lean`: evaluate `normSource` or `wingSource` at the argument multiplied by the square root of pi, then multiply by the Gaussian exponential of minus the square of that scaled argument. Their exact coefficients are in `GaussianSources.lean`. No floating point result appears as a mathematical premise.

## What the proof consumes

`GaussianCertificate.cellValid_integral_upper` proves general soundness of the numerical checker. Acceptance checks the source polynomial's exact affine substitution; a pointwise absolute-value or positive-part majorant; its actual Taylor-polynomial product; exact polynomial integration; exponential range reduction and a proved Taylor remainder; and the final rational inequality. Uncertain sign cells use a proved constant majorant; no unproved root certificate is needed.

There are **310 norm cells and 254 wing cells**, checked with `decide +kernel` in **eight modules**, `GaussianCells00` through `GaussianCells07`. Every accepted cell is used by `GaussianAssembly.cells_integral_upper`. `GaussianTail` proves a genuine infinite-tail integral bound for every polynomial of degree at most 24. `GaussianRays` proves integrability and combines the finite intervals and infinite tails. `GaussianFullRays` checks the tail constants and the scale involving pi. `GaussianPhysical` and `GaussianWings` prove the actual full-line norm and exterior-wing identities before deriving the final ratio.

All selected numerical consumers have only the usual `propext`, `Classical.choice`, and `Quot.sound` axiom closure. No `native_decide`, native execution axiom, new axiom or admitted proof is used in this numerical chain.

## Remaining mathematical boundary

The numerical theorems themselves have no Fourier or prime-distribution hypothesis. They do not alone assert that `physicalG` is the Fourier transform of `physicalF`, or conclude a prime-gap theorem. That association has now been proved separately by `RHOnePrime.GaussianFourier.fourier_actual_physical` in `../gaussian_fourier/GaussianActualFourier.lean`, together with actual integrability, continuity and evenness. The subsequent analytic prime-gap reduction remains a separate consumer in `../gaussian_gap/`; consult its completed proofs and receipts before claiming an ANT conclusion. This directory never substitutes an assumed Fourier identification or an observed numerical output for either step.

The published comparison is Rafael Blanquer Robles, *Rational Fourier certificates for prime gaps, explicit intervals, and arithmetic progressions*, version 2, Theorem 4, equation (3), and Section 2, page 3, where the exact norm/positive-Fourier-wing quotient is defined. The actual primary PDF is `../sources/Blanquer_Robles_2026.pdf`; its version is dated 2026-11-21. The printed constant is an upper bound, not a proved optimum. Our loose proved ratio does not claim global optimality or a best-known prime-gap theorem. There is no standalone Blueprint label or canonical IEANTN node for this isolated numerical experiment.

## Reproduce

From a clean checkout with the pinned Lean 4.34.0-rc2 and Mathlib commit recorded in `../scripts/LOCAL_CONTEXT.json`:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/reproduce.py \
  --run /absolute/new/experiment-directory --jobs 2
```

The command regenerates the partition and all nine generated Lean source files from the original thirteen exact rational coefficients, requires byte-for-byte source equality, freshly compiles the complete selected transitive source closure, and checks all nine final axiom audits. It reuses only pinned generic Lean/Mathlib dependency objects. It does not reuse predecessor application proof objects. Where the local dependency paths differ, supply `--compiler` and `--generic-lean-path` as described by `../scripts/rebuild_closure.py --help`.

Use `--regenerate-only` to check deterministic certificate regeneration without claiming Lean proof acceptance. No random seed, SciPy, FFT, Arb or external prime data is needed to regenerate the numerical certificate. The archived exploratory Arb result is corroboration only.

The Lean compiler/kernel and generic library source, and the usual operating-system and hardware execution assumptions, remain the trust boundary. A successful compiler invocation alone is not a source-first C/C++/CUDA verification result.

After a successful run, remove the redundant regenerated suggestions with:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/cleanup_completed.py \
  --run /absolute/completed/experiment-directory
```

The cleanup requires a successful reproduction receipt, verifies every duplicate generated Lean source against its recorded cryptographic hash, records its exact targets before deletion, and removes only that run's `regenerated` directory. Original inputs, accepted proof sources and objects, source snapshots, dependency information, execution receipts and audit logs are retained.
