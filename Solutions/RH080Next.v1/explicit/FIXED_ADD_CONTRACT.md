# Actual fixed_add source contract

The complete contract for the unchanged `fixed_add` helper now has three fresh
109-module source replays (ordinary Python, `-O`, and `-OO`), followed by strict
evidence validation and deliberately wrong-source controls. This is a completed
source-to-AST/execution/integer-correctness **helper contract**. Its consumption
by the complete numerical FFT and final ANT theorem remains pending; it is not
an independently completed source-first PV result under the owner's definition.

## Proved contract

`RH080Next.FFTPV.AddSource.fixed_add_total` in
[`ExplicitFFTAddSource.lean`](ExplicitFFTAddSource.lean) constructs the actual
terminating `Call` and proves that **every** permitted call has the same return
and final state. It covers both five-iteration arithmetic loops, both operand
evaluation orders, every permitted argument order, actual local declarations,
block exit/lifetimes, unsigned arithmetic guards, comparison, canonicalization,
and the caller frame.

Inputs have five normalized base-billion digits, a sign bit, and a subtraction
flag in `{0,1}`. The output may exactly alias either input, or occupy a disjoint
six-word slice, including slices in one allocation. Unsafe partial overlap is
excluded explicitly by `SafeAlias`. The actual source returns an overflow
status in `{0,1}`; its represented signed integer equals the requested sum or
difference when that actual status is zero. The consumed mathematical theorem
`rawStatus_zero_of_sum_lt` proves zero status from a sum-of-magnitudes bound.
Overflow cases are tested and are not silently assumed absent.

Four source wrappers consume the independently parsed unchanged iterative and
recursive w4/Fap source strings. `ExplicitFFTAddAudit.lean` checks their proof
closures, including the genuine signed arithmetic theorem and source syntax.
Only `propext`, `Classical.choice`, and `Quot.sound` remain; there are no new
axioms, `sorry`, native execution axioms, or `native_decide` leaves in these roots.

[`ExplicitFFTAddSlice.lean`](ExplicitFFTAddSlice.lean) additionally proves that
an actual call preserves every word outside the six-word output slice. This
same-allocation result is derived from the actual full output data, rather than
inferred from a whole-object frame. It has a separate accepted source-associated
replay; it was added after the frozen 109-module replays and is labeled as such.

## Reproduction

Use Lean `4.34.0-rc2` and mathlib commit
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Follow
[`../pv/README.md`](../pv/README.md)'s clean-context instructions, including
`make_context.py`; the context contains only the eight pinned generic libraries,
not application proof objects. The scripts validate the compiler hash and source
identities. Run from this directory, with `CTX` set to that generated JSON:

```sh
python reproduce_fft_fixed_add_full.py --context "$CTX" --out /absolute/fresh/add-normal
python -O reproduce_fft_fixed_add_full.py --context "$CTX" --out /absolute/fresh/add-O
python -OO reproduce_fft_fixed_add_full.py --context "$CTX" --out /absolute/fresh/add-OO
```

Each command compiles and executes all four actual C files against 264 exact
integer/alias cases, compiles the complete 109-module Lean closure from source,
revalidates all source, compiler-command, object, log and timing hashes, reruns
all four original native executables, and executes 16 wrong-source controls.
The deterministic seed is `0x080A55`. Each wrong source compiles and exits
normally but produces a numerical mismatch; these supplementary native tests
are separate from the general Lean soundness/correctness proof.

The preserved runs first executed `reproduce_fft_fixed_add.py` and then the
combined controller with `--reuse-run`. The final receipts explicitly identify
this continuation; they do not claim that the final validation invocation itself
recompiled the sources. The default command above executes both phases freshly.
Normal and both optimized Python modes actually completed both phases.

The resource policy probes actual available RAM, allows a justified 256 GiB
per replay with at least 256 GiB host reserve, and does not impose the obsolete
4 GiB cap. The observed maximum child RSS was about 37.1 GiB. Each full replay
used about 0.77 GiB of files; all three recorded zero OOM events. Exact time,
peak RSS, byte counts, sources and receipt hashes are in
[`FIXED_ADD_MANIFEST.json`](FIXED_ADD_MANIFEST.json) and `evidence/fixed-add/`.

Generated mutant sources, harness copies and executables were removed only from
owned control fixture directories after verification. Original C sources, frozen
proof-source snapshots, accepted proof objects, baseline observations, concise
mutation observations, and hashes remain. Failed validator-development runs and
superseded successful validation versions are preserved separately, with their
original executed scripts; the manifest identifies the final v4 receipts.

## Trust and remaining connection

The proofs use the existing restricted C operational semantics, its documented
LP64/ULL64 ABI and source syntax fragment. Compiled execution still trusts the
pinned compiler/core runtime, OS and hardware. Tests do not prove adequacy to the
entire C standard. No successful application effect or initial application-array
state is imported as a platform fact: the explicit caller array/digit conditions
must be established by the calling application proof. The full initializer,
complex FFT execution, accepted numerical trace correspondence and final FFT-to-
ANT connection remain separately tracked work.
