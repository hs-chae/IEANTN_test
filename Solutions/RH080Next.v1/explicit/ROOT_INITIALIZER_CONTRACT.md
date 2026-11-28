# Actual root initializer contract

`ExplicitFFTRootSource.lean` proves the complete `initialize_root` helper in
all four unchanged original Fap/w4 iterative/recursive C programs. The current
accepted receipt is a **source-associated** replay; the separate fresh 212-source
replay is still running. See `ROOT_INITIALIZER_MANIFEST.json` for exact identities.

The public `RootSource.initialize_root_total` accepts an actual typed caller
array, its live-allocation proof, a safe `Layout`, and `OriginalGrid n` specifying
exactly 131072 or 16777216. It constructs an actual successful C-AST `Call`, proves
that **every permitted execution** returns the same zero status and final state,
and proves that the twelve final root words represent `FFT.IntegerModel.root n`.
This consumes the original pi limbs and all ten Taylor iterations, including
floor multiplication/division, signed accumulation, actual zero/copy calls,
temporary-variable births, nested scopes and the final negative-imaginary
canonicalization. No precomputed root output or successful effect is a premise.
The intermediate finite guard bounds are checked by the Lean kernel.

`originalLayout object` is the actual 512-word allocation with root at word128
and work at word0. The general theorem supports any disjoint root12/work80 slices
of one allocation. It proves physical words outside those two slices remain
unchanged, in addition to restoring caller names/scope, preserving foreign state
and other old objects, and proving allocation/scope-clock monotonicity. A whole
object frame alone is never substituted for this physical slice property.

The four source wrappers consume the independent source-grammar proofs for the
actual complete C files. `ExplicitFFTRootAudit.lean` checks that every wrapper
actually consumes initialization, all arithmetic helpers, the ten-iteration
loop, the universal evaluation-order proof and the exact integer-root model.
All four final roots use only `propext`, `Classical.choice`, `Quot.sound`.

## Reproduce

Use the pinned Lean/mathlib/dependency context recorded in the campaign README
and the manifest's original compiler receipts. To perform a fresh source-cold
proof replay, run:

```
python Solutions/RH080Next.v1/pv/reproduce_lean.py \
  --context /path/to/clean_proof_context.json --run /fresh/owned/root-cold \
  --root ExplicitFFTRootAudit
python Solutions/RH080Next.v1/explicit/reproduce_fft_root_native.py \
  --out /fresh/owned/root-native
python Solutions/RH080Next.v1/explicit/verify_fft_root_result.py \
  --context /path/to/clean_proof_context.json --run /fresh/owned/root-cold \
  --native /fresh/owned/root-native --out /fresh/owned/root-validation
```

The cold controller regenerates the complete selected import closure using only
the pinned eight generic libraries, and records every compiler command, source,
object, timing and hash. The independent final validator rejects incomplete
children, source changes, wrong compiler routes, PANIC/error/sorry diagnostics,
missing resource evidence and absent consumed-proof audit markers, even if an
individual compiler exits zero. It uses explicit checks under normal Python,
`-O`, and `-OO`.

Native corroboration uses seed `0x080B007`, both original grids, four disjoint
shared512 layouts and two arbitrary full-uint64 initial arrays per layout:16
cases per original source,64 total. Four deliberately wrong source changes per
file (pi high limb, root divisor, imaginary sign, cosine initialization) must
compile and fail the independent integer-model/slice checks normally. These
finite tests supplement the general Lean proof and are not the proof themselves.

## Remaining boundary

This is a completed **source-to-AST/execution/correctness helper contract** with
a pending complete FFT/main/ANT connection. Under the owner's definition it is
not yet a completed source-first PV result for the final norm/ANT theorem.
The restricted C operational model/LP64 and ULL64 ABI, pinned compiler/core
runtime, OS and hardware remain the documented infrastructure trust boundary.
The proof does not establish full C-standard semantic adequacy or full FFT
correctness. Caller array/layout prerequisites must be discharged by the actual
application initialization path.
