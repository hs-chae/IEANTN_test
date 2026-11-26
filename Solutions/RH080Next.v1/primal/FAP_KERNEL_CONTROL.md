# Original Fap FFT: kernel-only numerical control and complete consumers

This is a kernel-only numerical verification control. It does **not** prove the C FFT program correct and must not be described as source-first PV. The C-helper migration is a separate unfinished development.

## Fixed mathematical object

The input is the original `Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/witness-ap.json`, SHA-256 `9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a`. Its 400 signed coefficients, normalization, support radius, algorithm and original norm cap are unchanged. Appending the original terminal zero gives the 401 nodal values used by the finite ANT consumers.

The exact integer FFT has 131072 points, 17 recursive stages, base-billion arithmetic and real/imaginary scale 10³⁶. Its full execution trace gives:

- Sum of absolute real output coordinates: `102468342420806369668447945569060309170116`.
- Exact curvature numerator: `12681061983660556400000`.
- Exact ceiling-based numerical numerator: `781796015790084776`, denominator 10¹⁸.
- Original downstream norm cap: `0.7817960157900848`.

The proof establishes the original cosine-polynomial embedding, actual input mass at most 81, the complete 17-stage rounded integer FFT, its error against the true complex DFT, periodic chord quadrature and the actual whole-line Fourier norm. The norm transfer consumes the literal BR Fourier norm identity (`SourceBRFourierNormFive`). The separate strip-regularity input is not used as an undocumented substitute for this identity.

## Final mathematical consumers

`FapFFTAntConsumers.lean` proves, conditionally on the explicitly named original analytic inputs, RH and the historical finite-range input:

- `kernel_fap_08_full`: every real 4 ≤ x ≤ exp(174) has a prime p with x < p < x + 0.8√x log(x).
- `kernel_fap_074_full`: every real 11 ≤ x ≤ exp(63) has such a prime with coefficient 0.74.
- `kernel_fap_075_full`: every real 11 ≤ x ≤ exp(70) has such a prime with coefficient 0.75.
- `kernel_fap_strict_slab`: the original locked logarithmic slabs and strict endpoints.

There is no remaining numerical norm premise in these theorem types. `FapFFTKernelAudit.lean` checks their exact types and the connected numerical, Fourier, analytic and arithmetic dependency chain. All audited axioms must belong to `propext`, `Classical.choice`, `Quot.sound`.

The retained source inputs are BR Fourier norm and strip statements, CMS Guinand–Weil/zero partial-summation/zero-count statements, DLMF digamma and real-eta identities, Montgomery–Vaughan, RH and the historical finite gap theorem. These are explicit hypotheses rather than new verified paper proofs. The independent scalar source-verified providers in the analytic closure remain separate from the kernel-only FFT.

## Reproduction from a clean application-object environment

Use a Linux environment with Python 3.11, `prlimit` and `/usr/bin/time`. Use the repository's pinned Lean 4.34.0-rc2 and Mathlib commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The compiler SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Only the eight pinned generic dependency libraries may be prebuilt; no previous IEANTN application objects are required.

Prepare the context JSON accepted by `dual/reproduce_dual.py`: `compiler`, `compiler_sha256`, `generic_lean_path` and pinned dependency identities, using the same generic-context procedure as the other RH080Next reproductions. Then run from the repository root:

```sh
python Solutions/RH080Next.v1/primal/reproduce_fap_fft_math.py \
  --context /absolute/path/to/clean_proof_context.json \
  --run /absolute/path/to/fresh-fap-run \
  --memory-gib 128 --forest-workers 4
```

The driver generates all numerical data deterministically, kernel-checks the full integer FFT forest, independently checks the fixed input and output metadata, compiles the additional mathematical closure from source in one application bank, runs the typed fourteen-root axiom/dependency audit, and writes atomic receipts and hashes. No random seeds are used. CPU, elapsed time, peak RSS and disk usage are reported separately; a nonzero compiler exit or an exit-zero PANIC/error diagnostic is rejected.

For a long unattended run, use a persistent process supervisor (for example, a user-owned `systemd-run --user` unit) so a transient tool/session lifetime cannot terminate the compiler. This changes process supervision only; the mathematical sources and compiler checks remain identical.

A separately accepted forest may be reused only through `--forest-base /absolute/path/to/accepted-run`. This is explicitly a validated source-associated base plus fresh additional source compilation, not a claim that the base was rebuilt during that invocation. Source snapshots, all object hashes, all compilation receipts/log hashes, the executed controller/producer and the fixed N17 input/numerator must pass validation before any object is imported.

Use a new run directory each time. The old rejected forest v1 evidence (exit-zero compiler IR PANIC) is retained for diagnosis and must not be used as a base. The corrected accepted forests mark generated data definitions noncomputable and reject PANIC diagnostics.

## Remaining trust boundary and storage

The numerical mathematical certificate is checked by Lean's kernel; no `native_decide` execution axiom is permitted in these final numerical roots. The pinned compiler/core runtime, operating system and hardware remain trusted infrastructure. The numerical C implementation's source-to-execution correspondence is **not** supplied by this kernel-only control.

Generated CSV files, proof modules and objects are reproducible, but accepted evidence must be retained until the complete public regeneration procedure has itself been checked. Clean only experiment-owned temporary paths after validating deterministic byte-for-byte regeneration; never remove original locked inputs, paper sources, accepted receipts or the only evidence copy.

The historical first combined source run was interrupted by SIGTERM after 123 of its 142 additional modules. Its completed source/object/log receipts were independently revalidated and preserved. `reproduce_fap_fft_resume.py` continues precisely that recorded lineage in a new directory: 123 inherited source-cold modules, 19 newly compiled modules, plus the original 42-module forest. It explicitly refuses to call this a fresh uninterrupted 142-module run. Clean-environment reproduction uses the full driver above and does not require reproducing the interruption.
