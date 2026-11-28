# Actual quad stage: source execution and original integer model

`QuadSource.source_quad_stage_total` in `ExplicitFFTQuadSource.lean` proves the
complete actual quadrature stage in both preserved recursive C programs. Fap
executes source items 34–35: its 400-row loop and the additional multiplication
of quad by 100. W4 executes source item 35: its 2520-row loop. The source syntax
and exact main-list locator are consumed by the theorem. No C source, nodal
input, grid, integration algorithm or normalization has been changed.

Each actual seven-instruction row calls the real `encoded_node`, declares e and
value, computes the unsigned absolute difference from 10000000000000000, calls
`magnitude_into(temp,value)`, adds the actual multiplication status from
`multiply_small(temp,5,20*j*j)`, adds the status from
`add_magnitude(quad,temp,6)`, and increments j. The proof constructs all real
local births and scopes and proves the same output for every permitted
execution, including both operand orders and all argument permutations.

The source output is an actual normalized six-word integer at work[208..213].
Its magnitude is exactly the old `FFT.IntegerModel` quadrature fold, multiplied
by 100 for Fap, or the old `FFT.IntegerModel.W4.quad` for W4. Source-returned
carry and status are proved zero from exact integer conservation and capacity
bounds. Factor zero at j=0 is included. All arithmetic guards and intermediate
64-bit products are discharged; the result is not supplied as a hardcoded
output or certificate premise.

The caller supplies actual typed data/work buffers, real borrowed main locals
`data`, `n`, `j=0`, `temp=work+160`, `quad=work+208`, `status=0`, normalized zero
quad, and distinct live scalar objects. These are application initialization
obligations. They are not platform assumptions. The stage preserves data,
restores caller names/scopes, proves clock monotonicity, preserves foreign state
and all old objects except the work allocation and j cell, and preserves every
physical work word outside temp[0..5] and quad[0..5].

The general source theorem takes `QuadSource.LoopView` at j=0 and the exact
profile-program identity. `QuadSource.Correct` exposes the actual stage
`ExecList`, every-execution theorem, data/work representations, real caller
locals, caller frame, normalized output, exact original integer magnitude and
physical word preservation. This is ready for composition with the actual
main initialization/reset and C's common upward quad divisions by 3, n and n.

`QUAD_STAGE_MANIFEST.json` records the exact frozen source/receipt closure and
actual resource measurements. The recorded replay is source-associated, with
only the eight pinned generic libraries and exact previously accepted
source-associated application objects. It is not a new source-cold replay.
The final full-main/FFT/norm/ANT connection is pending; therefore this segment
alone is not completed source-first PV under the owner's definition.

From a clean pinned Lean/dependency environment, regenerate and compile the
whole selected import closure with:

```
python Solutions/RH080Next.v1/pv/reproduce_lean.py \
  --context /path/to/clean_proof_context.json \
  --run /fresh/owned/quad-source-cold --root ExplicitFFTQuadAudit
```

Regenerate the separate native corroboration and adversarial controls with:

```
python Solutions/RH080Next.v1/explicit/reproduce_fft_quad_native.py \
  --out /fresh/owned/quad-native
python -O Solutions/RH080Next.v1/explicit/reproduce_fft_quad_native.py \
  --out /fresh/owned/quad-native-O
python -OO Solutions/RH080Next.v1/explicit/reproduce_fft_quad_native.py \
  --out /fresh/owned/quad-native-OO
```

The native script checks exact concrete/formal source bytes and exact pinned
nodal inputs, extracts the actual main quad segment without changing it,
executes the original C helpers, and compares every result with independent
Python integers and saved physical words. It also tests intentionally wrong
factor, negative branch, add width, loop bound, and Fap scaling. These tests
corroborate the formal proof; they are not the proof. Both recursive sources
are formally covered. The two preserved iterative sources are additional
native corroboration routes only.

Remaining trust is the pinned Lean kernel/compiler/core runtime and host
OS/hardware, plus the disclosed adequacy of the existing restricted C/typed
memory model and selected LP64/64-bit unsigned ABI. This contract does not
claim verification of arbitrary C or of the native compiler itself. No new
axiom, `sorry`, `native_decide` or native numerical leaf is introduced; the
consumed-path audit permits only propext, Classical.choice and Quot.sound.
