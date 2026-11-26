# Search implementation corrections

-2026-11-25: Initial unpublished search source omitted lexical spaces in two conditional expressions (`else2`, `else60`); Python rejected before any computation. Corrected and AST-checked; no result or mathematical claim existed.
-2026-11-25: Floating DCT sign suggestions near tiny polynomial values did not always bracket a root under the independent long-double Clenshaw evaluator. Brent correctly rejected both the oldw4 diagnostic and the second m16 LP iteration. Preserve partial logs, verify direct endpoint signs before refinement, and retain exploratory-only status; no rigorous bound or accepted theorem was produced.
-2026-11-25: First unpublished scaled-Arb adaptation reused variable pi for the scaled leakage threshold, incorrectly scaling the final 2/sqrt(pi) multiplier. Source review caught it before any claim; stopped exact checker PID, preserved source/output directory as withdrawn, and separated cutoff=pi/scale² from pi itself. Only norm has1/scale; positive spectral leakage retains2/sqrt(pi).

- 2026-11-25: generated scaled-cell wrapper initially failed syntax checking because `else1` lacked whitespace; corrected before any numerical execution.

- 2026-11-25: copied old cell compiler inherited Lean default thread count; eight simultaneous compilers hit thread-creation resource failure (exit134, not OOM). Terminated only owned controller/children and preserved interruption. Fixed controller to invoke `lean -j1` before a fresh unchanged-cell run.

- 2026-11-25: initial FullRays template replacement changed a denominator before matching two old ray caps. Source inspection caught both stale caps before compilation or claim; replaced exact new caps.

- 2026-11-25: the large-alpha comparison initially emphasized gain over the weaker written w4 line. Root recovered the stronger accepted octic population line1.02391875+1.125alpha (limited c<=16), which beats the alpha1-optimized packet at alpha10. Reports must compare the exact strongest matched population frontier; no blanket large-population gain is claimed for that packet. A fresh separate alpha2/5/10/20 scout preserves the original C input.

- 2026-11-25: the global official fingerprint helper started a full unrelated Mathlib/core Lake rebuild with default parallelism. Inspection found33 owned processes and33.2GB aggregate RSS; stopped only that build, preserving interruption evidence. New92-module proof replay was independent and continued. A bounded scoped import frontend must preserve the official structural-hash algorithm exactly.

## 2026-11-25: Cold Fourier transform address-space admission
The complete 92-source cold replay compiled 80 modules but Scaled40CoefficientTransform threw std::bad_alloc under 16 GiB RLIMIT_AS, with 8,151,132 KiB measured RSS. This is an address-space resource failure, not a mathematical rejection or observed OOM kill. Preserve failed evidence and rerun fresh at four workers ×32 GiB, unchanged aggregate128 GiB policy and unchanged proof sources.

- Population envelope algebra first draft (2026-11-26): real-valued rational definitions lacked a noncomputable section. The compiler rejected code generation despite Std3 theorem proofs; receipt population-envelope-algebra-v1 remains failed. Added the required declaration annotation and reran in a fresh bank; no failed run is promoted.
