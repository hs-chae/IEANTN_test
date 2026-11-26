# Fixed64 analytic RH population improvement

This is a **kernel-only analytic result**, not source-first program verification (PV). No numerical source program is introduced. The new mathematical consumer is `RH080Next.AnalyticFlat64.actual_population_curve` in `AnalyticFlat64Population.lean`.

For every real α ≥ 0, under RH and the two explicit BR mathematical input propositions below, the coefficient

**c(α) = 2.1 + (128/127)α**

has a strict eventual positive population margin: some δ > 0 satisfies, for every sufficiently large real x,

**π(x + c(α)√x log x) − π(x) ≥ (α + δ)√x.**

The Lean count is the exact half-open interval (x, x + c(α)√x log x], with natural floors as recorded by `IEANTN.CMSFunctional.halfOpenCount`. No explicit finite onset is asserted. The existing mathematical inputs and original experimental outcomes are unchanged.

At α = 40 the coefficient is exactly **53867/1270 ≈ 42.41496063**, compared with the previously completed flat16 line's **43.79166667**. The exact new line improves that particular old flat16 line for α > 14859/896. This comparison does not establish optimality or a best-known-result claim, and does not assert superiority over Lee at every density.

## Exact witness and proof

The fixed rational witness has mesh m = 64 and 321 stored nodes: aⱼ = 1 for 0 ≤ j < 64 and aⱼ = 0 for 64 ≤ j ≤ 320. Its actual even affine interpolant has maximum M = 1, zero positive leakage beyond |v| = 1, and inverse Fourier value F(0) = 127/64. The actual Fourier relation and CMS eligibility are proved by the existing general affine theorems, instantiated to these precise nodes.

Its periodic polynomial is the real Dirichlet polynomial

**P(t) = 1 + 2 Σⱼ₌₁⁶³ cos(2πjt).**

The exact identity sin(πt) P(t) = sin(127πt), the bound |P| ≤ 127, and reflection P(1−t) = P(t) are proved in Lean. Split the half interval at a = 1/(127π). On [0,a], the integral is at most 127a = 1/π. On [a,1/2], positivity of sin(πt) and the identity give |P(t)| ≤ 1/sin(πt). The derivative of log(tan(πt/2))/π is proved to be 1/sin(πt), including all nonzero denominator and domain obligations. The fundamental theorem of calculus and tan(1/254) ≥ 1/254 then give the second integral at most log(254)/π. Consequently,

**∫₀¹ |P(t)| dt ≤ (2/π)(1 + log 254).**

`AnalyticFlat64Log254.log254_lt` is a kernel proof that log(254) < 277/50, using a finite positive exponential series. With the existing kernel proof π > 3.14, this makes the normalized intercept strictly smaller than 2.1. The strict margin is retained in the actual prime-count consumer; no equality endpoint is inferred from an upper bound.

## Explicit source inputs and remaining trust

The theorem has exactly these mathematical hypotheses:

- `SourceBRFourierNormFive`: the general arbitrary-rational-node norm identity in BR v2 Lemma 5, equation (4), printed page 3. It identifies the actual whole-line inverse Fourier norm with the periodic polynomial integral. The source class requires N = 5m; here N = 320 and m = 64 exactly.
- `SourceBRUniformPopulationQ1`: BR v2 Proposition 6, displayed equation (6), printed page 7, with the explicitly treated conductor-one q = 1 specialization on printed page 10. The published remainder is retained and its eventual decay is proved; no finite onset is transferred.
- `RiemannHypothesis`.

These are explicit literature propositions, not newly assumed numerical facts or newly formalized proofs of those published propositions. Their exact source/Lean/Blueprint mapping is already in `FINAL_NAMED_INPUT_SOURCE_AUDIT.json` and `SUPPLEMENTAL_NAMED_INPUT_SOURCE_AUDIT.json`. There is no added window-specific norm premise, final-bound premise, native execution axiom, `sorry`, or new axiom. The theorem dependencies use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. Generic pinned Lean/compiler/runtime/OS/hardware infrastructure remains trusted.

## Reproduce from a clean application environment

The application modules are rebuilt from source; no previously compiled IEANTN application object is on the search path. Provide a JSON context containing the pinned compiler and the eight generic dependency object roots, following the schema of the campaign's `clean_proof_context.json`. Paths may be relocated; the script verifies the compiler hash, the exact dependency commits, and the actual generic repository commits.

- Lean: 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Compiler SHA256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib: `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
- Other seven generic dependency commits are fixed in the script and copied into each replay plan.
- No random seeds, numerical data downloads, prime lists, numerical arrays, C compilation, or external numerical observations are required.

From the repository root:

```sh
python3 Solutions/RH080Next.v1/explicit/reproduce_analytic_flat64.py \
  --context /absolute/path/to/clean_proof_context.json \
  --run /absolute/path/to/a/new/experiment-owned/run \
  --memory-gib 32
```

The fresh run directory contains exact source snapshots, complete source hashes, compiler commands, individual resource/time receipts, objects, the exact 21-root typed/dependency/axiom audit, and an atomic result receipt. The script leaves at least 256 GiB available for the host and refuses a pre-existing output directory. Resource measurements are actual per-compiler process maxima; they are not claimed to be aggregate cgroup peaks.

The accepted replay is recorded in `ANALYTIC_FLAT64_MANIFEST.json`. All original frozen sources and canonical nodes remain unchanged. The accepted proof objects, small source snapshots, and receipts are retained; this experiment creates no large regenerable numerical datasets requiring deletion.
