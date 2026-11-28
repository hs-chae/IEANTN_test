# Actual multiplication suffix: completed source-first helper contracts

This work verifies a source helper/subprogram contract. The complete numerical C FFT caller and its ANT consumer still require further composition. These results alone are **not** completed source-first PV under the project's definition.

The numerical C source is unchanged: `pv/fft/w4_fft_recursive.c`, SHA-256 `0c9e29db9bbfacd8ed049dc8e4b2a2f18d8ae146c1d0e4dd47a93cd89b80e22b`. The independent supported-language syntax proof covers the full program. `MultiplySuffix.actual_suffix` establishes exact equality between the twelve remaining statements of its actual `fixed_multiply` AST and the interpreted suffix; this is not merely a comparison of token lists.

## What is proved

- Real sign/lost/overflow declarations, true sixth-word sign loads, both source loops, i resets, retained-word/sign stores, the actual optional `increment_words` Call, the actual `canonical_sign` Call and returned status.
- Total selected execution and correctness of **every** permitted suffix execution, including both binary operand orders and every permitted argument order. The proof uses the actual helper frame to show that evaluating the increment Call first preserves the overflow slot. It does not assume an invalid global determinism property when the destination can alias that slot.
- Arbitrary object IDs, scope owners, array sizes and base offsets. Output/work may share one allocation when their six-word and ten-word slices are disjoint. Input/output aliasing is permitted by the complete caller's separate input constraints. Persistent and temporary local owners remain distinct.
- Full old-object frame, monotone allocation/scope counters, mode and foreign-state preservation. The suffix may change output and its persistent i slot; its sign/lost/overflow locals and the real helper-call locals are allocated above the entry cutoff.
- Exact positional mathematics with base B = 10⁹ and fixed-point scale U = B⁴ = 10³⁶. The source sums the four low product digits, retains digits four through eight, adds one for a negative nonzero discarded part, and returns the true top digit plus any increment carry. When this computed status is zero, the canonicalized signed output is the Euclidean floor of the signed ten-word product divided by U. The top-digit-zero and retained-magnitude-plus-one range condition force that status to zero; the complete caller discharges these from its bounded normalized inputs.

Main interfaces are `suffix_total`, `suffix_framed`, `source_suffix_total`, `finalData_successful`, and `finalStatus_eq_zero` in `pv/lean/FFTFixedMultiplySuffix*.lean`. `FFTFixedMultiplySuffixAudit.lean` checks fifteen actual theorem roots, their standard axioms and the required source/parser, execution, frame and positional-mathematics dependencies. Its audited closure contains 3089 declarations. All accepted audited axioms are among `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, native execution leaf or new axiom is accepted.

`FFTFixedMultiplyBeginFrame.begin_execution_framed` separately exposes the real callee entry, four actual parameter births, zero initialization and all twenty-five product steps, with the original caller cutoff/frame. It supplements the original frozen prefix/core proofs without editing them.

## Reproduction

Use Linux, Python 3.11, `/usr/bin/time`, `prlimit`, the pinned Lean 4.34.0-rc2 compiler and the eight generic libraries in the project's clean dependency context. No IEANTN application object cache is used by the following source-cold route:

```sh
python Solutions/RH080Next.v1/primal/reproduce_suffix.py \
  --context /absolute/path/to/clean_proof_context.json \
  --run /absolute/path/to/fresh-suffix-run --memory-gib 128
```

A persistent user process supervisor is appropriate for this long compilation, for example `systemd-run --user`. The driver independently matches actual C bytes to the source syntax representation, freezes the complete selected source closure, compiles it into an empty application-object bank, rejects nonzero exits **and** exit-zero PANIC/error diagnostics, and checks the final fifteen-root audit before publishing its atomic result. Its inherited native copy-helper exercise is explicitly a separate runtime exercise, not a multiplication correctness proof. Nine actual CLI rejection controls across normal, `-O` and `-OO` confirm that the acceptance guards remain active under Python optimization.

The compiler SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; Mathlib is pinned to `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Exact commands, original/frozen source hashes, object hashes, compiler and native-exercise receipts, peak process RSS, execution time and disk usage are recorded per run. The source-associated development extensions retain their original receipts and are not described as a fresh replay of the entire closure.

## Remaining boundary

These proofs use the existing formal unsigned-word, pointer, allocation, scope and C-call model and the independently specified supported syntax. Their semantic adequacy relative to the approved C compiler/runtime/OS/hardware contract remains a documented infrastructure trust boundary. Actual application buffer applicability is supplied by the caller contracts, not assumed as a generic platform fact. The complete FFT C execution, its final numerical output and the downstream ANT theorem must still be connected before claiming full source-first PV. The separate Fap FFT-to-ANT control is kernel-only numerical verification.
