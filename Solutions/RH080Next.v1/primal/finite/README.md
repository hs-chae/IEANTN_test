# Canonical finite Fap prime intervals

This additive integration preserves the original fixed Fap400-node data and the exact finite claims. Under ordinary RH and the explicitly named analytic/historical inputs, a prime lies strictly between x and x+c sqrt(x)log(x) for c=0.8 on4≤x≤exp174, c=0.74 on11≤x≤exp63, and c=0.75 on11≤x≤exp70. The elementary c=0.777 branch on4≤x<11 uses the actual primes5,7,11 and needs no imported hypothesis.

Three canonical nodes separate the trust boundary:

* `CMSExplicitInputs.v1` records eight literal source inputs, with exact domains, convergence conditions and primary locators in its metadata. Its zero-partial-summation proposition explicitly specializes a published proof scheme; it is not misrepresented as a printed universal theorem.
* `FapFourierNorm.v1` contains the original400-node data and the original0.7817960157900848 norm cap. Its Solution proves the cap using the actual131072-point integer FFT trace, true DFT roundoff and global chord quadrature. The literal general BR Fourier-norm identity remains its input.
* `RHFiniteAffineIntervals.v1` consumes that norm provider, the eight named source inputs and ordinary RH. Each claim preserves real-valued x and both strict prime endpoints. Its small0.777 branch is unconditional.

`FapSourceInterfaces.lean` proves the eight input propositions and original data definitionally equal to the frozen analytic development. `FiniteCanonicalAudit.lean` checks actual theorem types, source-input consumption, numerical/analytic dependency closure and standard axioms. It also composes the norm provider with all three finite consumers, so the composed statements have no additional numerical-norm premise.

The FFT provider is **kernel-only**, not source-first verification of the C FFT. The standalone C helper contracts elsewhere in this project do not establish the remaining complete C caller→FFT→ANT connection. No Comparator receipt, optimality claim, or retroactive experimental success is asserted.

## Reproduce from a clean checkout

Use the pinned `lean-toolchain` and pinned Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6. Prepare a generic-only dependency context as documented by `../FAP_KERNEL_CONTROL.md`; no historical application `.olean` cache is accepted. The compiler and generic dependency hashes are checked by the public controllers.

First regenerate the deterministic proof-library sources:

```
python Solutions/RH080Next.v1/primal/finite/prepare_fap_library.py
python Solutions/RH080Next.v1/primal/finite/prepare_fap_library.py --verify
```

The ignored `generated/fap17` directory contains37 Lean files and34 CSV inputs, about104MB. Every byte must match `FAP17_REGEN_EXPECTED.json`, the original fixed-input hash and the reviewed generator hash. Preparation is not proof acceptance. Keep the CSV files beside the generated Lean sources during compilation: the data-only macro reads them relative to the source file.

Run the complete numerical/analytic and canonical verification pipeline:

```
python Solutions/RH080Next.v1/primal/finite/reproduce_finite_nodes.py \
  --context /path/to/clean_proof_context.json --run /fresh/run
```

This default regenerates and kernel-checks the entire N17 FFT, recompiles the complete numerical and finite mathematical consumers, then compiles the new canonical consumers. The generous default per-process memory ceiling is128GiB, with256GiB available host reserve required. Use a persistent user supervisor for the longer exact-kernel steps; closing a tool session must not terminate the job.

A previously completed source-cold math run can be supplied with `--math-base /accepted/math/run`. The controller rechecks every original/frozen source hash, all184 object hashes, source-associated compilation receipts/logs, all forest data, the final typed14-root gate and any interrupted123+19 lineage. This is reported as a fresh canonical extension of a validated base, not a fresh uninterrupted re-execution of the inherited math.

For standalone Solution/Lake builds, run the preparation command first, and register the reviewed additive library block `LAKE_ADDITIVE_BLOCK.toml` in the shared RH080Next Lake project. The two Solution projects require that project. This file is an additive proposal until the parent maintainer integrates it; no shared Lake file was silently changed by this worker.

Each accepted run saves a frozen PLAN, exact commands, per-module compiler logs, timing/peak-RAM records, object hashes, typed axiom/dependency audit and final atomic RESULT. The generated library may be deleted and deterministically regenerated after its accepted proof artifacts and reproduction recipe are preserved; do not delete an accepted run or the only copy of essential evidence.
