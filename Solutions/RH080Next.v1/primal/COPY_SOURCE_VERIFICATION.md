# Actual C copy helper verification

This verifies the unchanged `copy_words` function in
`../pv/fft/w4_fft_recursive.c`. It is a helper of the original numerical FFT,
not a completed source-first verification of that entire numerical program.
Its body also agrees definitionally with the iterative FFT source AST.

The final theorem is
`RH080Next.FFTPV.CopyLoop.source_copy_words_total`
in `../pv/lean/FFTCopySourceFinal.lean`.
It combines independent source syntax correspondence, constructive termination
and an actual full source `Call`, and functional correctness of **every**
permitted full `Call`. Thus it does not select a favorable execution order.
`FFTCopyAudit.lean` checks twelve theorem roots, permits only `propext`,
`Classical.choice`, and `Quot.sound`, and requires the actual syntax, grammar
soundness, parameter initialization, typed stores, loops, universal full-call
proof, and pure-expression soundness in the final dependency closure.

The precondition is actual typed host memory for both arrays, a well-scoped
caller state, valid slice bounds, and a length smaller than 2^64. Different
allocations, disjoint slices of one allocation, and identical slices are
supported. Other overlapping slices are outside the proved contract. All
input-slice values survive. The output object contains exactly the copied
prefix and its original values elsewhere. The constructive call also proves
restoration of caller environment, scope and foreign state, and preservation
of every old allocation except the destination. Every loop execution has the
corresponding arbitrary-caller object frame.

The source's three parameters and local counter are actually declared by the
formal semantics; they are not supplied as an initialization oracle. The
caller must establish the real typed array preconditions at each FFT call
site. This remains an application-integration obligation in the full FFT.
No new axioms, admitted proofs, native execution facts, output certificates,
or answer constants are used by this helper theorem.

`FFTPureDeterminism.lean` is reusable: it derives unique values and states
from the original pure `Eval`/`Place` rules, including both binary operand
orders. It also proves uniqueness of pure straight-line instructions,
including actual declarations, instruction lists, and block scopes.
`FFTWordSlices.lean` supplies genuine offset-pointer/load/store rules and
same-object disjoint slice preservation for other numerical helpers.

## Reproduce from a clean environment

Use Linux x86-64, Python 3, GNU `time`/`prlimit`, a C11 compiler, and the pinned
Lean 4.34.0-rc2 Linux release (compiler SHA-256 is enforced). Obtain Mathlib
commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` and its pinned dependencies.
Generic Mathlib cache objects are allowed. Build or obtain the generic cache
from the **Mathlib checkout**, rather than building the whole IEANTN project.
`create_copy_context.py` checks every generic checkout revision and constructs
a path containing only those generic libraries. It never includes an IEANTN,
FFT, Goldbach, or other application object cache.

From this repository root, with paths to those clean generic dependencies:

```sh
python3 Solutions/RH080Next.v1/primal/create_copy_context.py \
  --compiler /path/to/lean-4.34.0-rc2/bin/lean \
  --mathlib /path/to/mathlib \
  --output /tmp/rh080-copy-context.json
python3 Solutions/RH080Next.v1/primal/reproduce_copy.py \
  --context /tmp/rh080-copy-context.json \
  --run /tmp/rh080-copy-fresh
```

The run directory must be fresh. The script reconstructs and checks exact C
bytes from the Lean source string, compiles the unchanged C through the
provided harness, and executes 1,032 deterministic cases. These runtime tests
exercise separate allocations, disjoint slices in both directions, identical
slices, zero lengths, and 64-bit boundary values, checking untouched words.
They are runtime evidence, not the correctness proof. The fixed xorshift
seed is `4f1bbcdc7135a9e7` and the final seed is `b00bdb9447718ea7`.

The same script snapshots and recompiles the complete application import
closure from source, runs the final theorem/dependency/axiom audit, records
compiler and dependency identity, exact commands, source/object/log hashes,
per-module time and peak RAM, disk usage and any SIGKILL event. It uses one
Lean worker per compilation and a generous 256 GiB address-space ceiling;
actual usage is measured. There is no 4 GiB cap and no application-object
fallback. The complete run must finish with the final audit marker and a
fresh `RESULT.json`; an interrupted run is not a successful verification.

## Remaining trust boundary

The proved syntax relation is for the checker's documented supported C
fragment. It does not verify a production C compiler or the entirety of ISO C.
Semantic adequacy of the chosen typed source execution model and the pinned
compiler/runtime/OS/hardware contracts remains the documented platform trust
boundary. Native harness compilation/execution trusts that infrastructure.
The Lean theorem itself has only the three standard axioms listed above.
The full numerical FFT still needs its other arithmetic/control helpers,
call-site memory applicability, source execution/output association, numerical
error proof, and connection to the ANT consumer. This helper alone does not
establish a new numerical bound or a full-program PV success.

## Typed subrange zero resets

The same actual C source calls `zero_words` on a proper part of its larger
workspace, including offset 36 with length 10, and base offset 0 with length
80. `FFTZeroSlices.lean` and `FFTZeroSliceCall.lean` close that applicability
case. They preserve the original raw-byte/full-extent initializer and add a
contract for an already initialized full typed allocation at an arbitrary
valid offset. `zeroData_inside` and `zeroData_outside` expose the exact reset
and complement values for callers.

The final theorem is
`RH080Next.FFTPV.ZeroSlice.source_zero_slice_total`.
It proves independent source syntax, a total actual full Call with caller
restoration, and the functional correctness of **every** full Call. Its
preconditions are the actual typed caller allocation, well-scoped state,
`start + length <= size`, and `length < 2^64`. It does not assume initialized
application locals or a successful numerical result. The strict ten-root
axiom/source-consumption gate is `FFTZeroSliceAudit.lean`.

A clean combined replay of both helpers is:

```sh
python3 Solutions/RH080Next.v1/primal/reproduce_zero_slices.py \
  --context /tmp/rh080-copy-context.json \
  --run /tmp/rh080-copy-zero-fresh
```

For an already accepted run of the exact 47-source copy audit, an optional
`--base /path/to/accepted-copy-run` validates every base source snapshot,
current source, object, all compilation-log hashes, controller snapshot,
generic dependency pins and actual C bytes, both before and after compiling
the three new zero-slice modules. This is explicitly recorded as a validated
47-source base plus a three-source extension, **not** a fresh 50-source replay.
Historical or unvalidated application object caches are rejected.

The separate native zero-reset exercise executes 326 cases against the
unchanged actual source. It includes the real workspace subranges, complete
512-word resets and a one-past pointer with zero length; it checks every
untouched word and copies boundary values into the initialized reset slice
before the call. Seed: `58234dd618c34a19`; final seed: `faf2f5458e3c02b1`.
As with the copy exercise, these finite tests support reproducibility and
are not substituted for the universal correctness proof.
