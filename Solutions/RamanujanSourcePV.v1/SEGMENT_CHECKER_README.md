# Reproduce the source-verified segmented checker

This component verifies the actual `c/verified_segment_checker.c` function.
The whole source body, including initialization, sieving, comparisons, rejection,
and counting, has Lean correctness proofs. This is a function-level source-first
proof. It does not claim that the separate C++ benchmarking caller, or a physical
process's output, has been formally verified.

## Mathematical contract

For integer inputs `2 ≤ lo ≤ hi ≤ 2,000,000,000,000`, put
`length = hi − lo + 1`. The input `claims` contains arbitrary uint64 words.
The scratch buffer `flags` may contain arbitrary old contents. Both buffers must
be valid for `length` words and disjoint; `capacity ≥ length`.

The source initializes every scratch word to one, then visits **every integer
divisor** from 2 through `floor(sqrt(hi))`. It erases multiples starting at
`max(ceil(lo/d)·d, d²)`. It does not receive a prime list or a primality oracle.
It compares every claimed word with its computed flag, returning zero at the
first mismatch. Otherwise it returns the number of primes in the inclusive
segment, plus one.

`RamanujanPV.SegmentCFunction.positive_output_sound` proves, for **any** completed
run of that actual source returning a positive uint64 `output`:

- Every `claims[i]` is exactly one when `lo+i` is prime and zero otherwise.
- `output = number of primes in [lo, hi] + 1`.
- `Nat.primeCounting hi = Nat.primeCounting (lo−1) + (output−1)`.

Correct classifications and the expected count are conclusions of this theorem,
not assumed platform facts. The explicit return conversion accounts for the
source's signed `int` error literal zero converting to uint64 zero.

`correct_claims_execution` constructs the complete successful source execution
when an independent mathematical table proof supplies the matching flags.
`incorrect_claims_execution` constructs the source's actual mismatch rejection
execution. Determinism connects either constructed run to every other completed
run of the same source and input state.

## Proof organization

| File | What it establishes |
|---|---|
| `SegmentCheckerSource.lean` | Exact source bytes/structured AST correspondence, lexical admissibility, expression-depth bound |
| `SegmentCheckerMath.lean` | All-divisor sieve classification, stride coverage, inclusive prime-count increment |
| `SegmentMemory.lean` | Actual typed stores, valid reads, ownership, disjoint-buffer frames |
| `SegmentCInit.lean` | Actual initialization loop from arbitrary old scratch contents |
| `SegmentCMark.lean` | Actual stride loop and all machine arithmetic/index bounds |
| `SegmentCDivisors.lean` | Actual first-multiple setup and complete divisor loop |
| `SegmentCClaims.lean` | Actual comparison/count loop and first-mismatch rejection |
| `SegmentCFunctionPrefix.lean` | Actual guards and length/capacity computation, composed initialization and sieve |
| `SegmentCounts.lean` | Source flag sum equals the inclusive mathematical count |
| `SegmentCFunction.lean` | Complete actual source function and universal positive-output soundness |
| `SegmentTableAdapter.lean` | Independent ordinary table proofs connected to this source function |
| `SegmentLocal1000.lean` | Concrete source execution results for the accepted P/Q control windows |
| `SegmentNetwork.lean` | Every intermediate count derived from accepted actual source execution |
| `SegmentWindowCells.lean` | Original network certificate using source-derived endpoint providers |
| `SegmentTableProvider.lean` | Explicit valid input memory and checker executions for every required prefix |
| `SegmentRamanujan1000.lean` | Unconditional Ramanujan inequality on the first1,001-wide real interval |
| `SegmentDependencyAudit.lean` | Actual proof-constant inspection requiring the checker and excluding old local-cardinality shortcuts |

The concrete checked windows are:

| Inclusive integers | Width | Primes | Source return |
|---|---:|---:|---:|
| 38,358,837,684 through 38,358,838,683 | 1,000 | 32 | 33 |
| 14,111,427,771 through 14,111,428,139 | 369 | 17 | 18 |

These statements consume the actual accepted `LocalWindow1000B` table proofs.
Their 49 local primes have ordinary kernel Lucas primality proofs; composite
entries have checked proper divisors. Those ordinary certificates alone are not
called PV. The separate source correctness proof independently executes every
sieve loop and connects those inputs and exact counts to the actual C function.

The new selected `SegmentRamanujan1000.first_1001_real_interval` theorem proves the
original Ramanujan inequality at **every real point** in
`[38,358,837,683, 38,358,838,684)`. Its path is the actual segmented checker,
`positive_output_sound`, every P/Q prefix count, the eight original checked
rows/enclosures, and the unchanged IEANTN `CompleteCertificate`. The unchanged
two base source counts are fully proved. No finite positivity premise is added.
The executed dependency audit inspected all53,495 transitive proof/type constants
and found the required actual source-checker path; the old local cardinality
`PrimeWindow.count_at`, old `WindowCells.row_counts`, and old final-consumer
shortcuts are absent. This count includes existing library constants, not new
modules or new mathematical claims.

## Clean source replay

Use Python 3.11 or newer, Lean 4.34.0-rc2, and the generic dependency revisions in
`BUILD_CONTEXT.json`. The Lean binary SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
the Mathlib commit is `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
On another machine, make a context file with the same revisions and compiler
hash, changing only filesystem locations for the compiler and dependencies,
including each dependency's `library` path. Build those pinned generic libraries.
The replay refuses dirty tracked dependency sources or different commits.

From this directory, rebuild every application import of the generic checker:

```sh
python3 scripts/reproduce_segment_checker.py \
  --context BUILD_CONTEXT.json --out /fresh/owned/segment-replay --cpus 8,9,10,11
```

Choose CPUs actually available to the process. The replay uses one worker with a
48 GiB address-space ceiling, checks actual available RAM, and reserves512 GiB
for the host and other processes. It reuses only the pinned **generic** libraries,
never old application objects. It records exact source/payload/object hashes,
compiler commands, per-module time and peak RAM, disk use, and OOM/SIGKILL events.
A failed attempt remains on disk and cannot produce a passing final receipt.

To regenerate the small accepted local table source from scratch, use the exact
deterministic proposal parameters below. Proposal generation is untrusted; the
next source replay compiles and checks all of its mathematical proof terms.
No random seed is used.

```sh
python3 scripts/generate_local_prime_window.py \
  --width 1000 --name LocalWindow1000B --prime-chunk 128 \
  --check-chunk 256 --data-chunk 256 --out /fresh/owned/local1000
python3 scripts/reproduce_segment_checker.py \
  --context BUILD_CONTEXT.json --out /fresh/owned/segment-local-replay \
  --local-table-root /fresh/owned/local1000/source --cpus 8,9,10,11
```

Do not reuse an existing output directory. The second replay rebuilds the entire
selected application closure, including all local Lucas, divisor and cumulative
count proofs, and prints the actual axiom sets of the final five source theorems.
It accepts only subsets of `propext`, `Classical.choice`, and `Quot.sound`; no
native execution axiom, new axiom, or `sorry` is accepted. Read-only receipt
validation also works under Python optimization:

```sh
python3 scripts/reproduce_segment_checker.py --check /fresh/owned/segment-local-replay
python3 -O scripts/reproduce_segment_checker.py --check /fresh/owned/segment-local-replay
python3 -OO scripts/reproduce_segment_checker.py --check /fresh/owned/segment-local-replay
```

To replay the new **final Ramanujan consumer** too, additionally supply the exact
generated sources for the eight scalar cells and the already completed critical
count pair. These retain their original deterministic regeneration/verification
instructions and receipts. Choose only one source version of each namespace;
the accepted critical-pair source is `demand-critical-pair-v3/source`.

```sh
python3 scripts/reproduce_segment_checker.py \
  --context BUILD_CONTEXT.json --out /fresh/owned/segment-consumer-replay \
  --local-table-root /owned/local-window-1000-b-v1/source \
  --application-source-root /owned/local-cells-1000-v1/source \
  --application-source-root /owned/demand-critical-pair-v3/source \
  --ramanujan-consumer --jobs 4 --cpus 8,9,10,11
```

This rebuilds the critical numerical proofs as well as all actual source and
network consumers. Four workers have separate48 GiB ceilings,192 GiB aggregate;
the controller requires at least1 TiB of actual available RAM and preserves the
512 GiB host reserve. Source, parameters, algorithms and mathematical assumptions
remain unchanged. `--plan-only` resolves and hashes the entire selected source
universe without launching any proof workers. Every replay uses a fresh directory.

`generate_segment_checker_source.py` deterministically regenerates the C/AST
proposal. The Lean source-byte theorem, not that generator, accepts the binding.

## Native numerical cross-checks

Build the pinned untrusted primesieve proposal dependency with the existing
`scripts/reproduce_numerics.py` instructions. Its primecount repository commit is
`9eb78bc0d1c98129f464db287699532376f52950`. Then run:

```sh
python3 scripts/benchmark_segment_checker.py --scratch /owned/scratch \
  --out /fresh/owned/native-local --cpu 9 \
  --case 38358837684 38358838683 --case 14111427771 14111428139
```

The native program executes the actual checker C source, compares its count with
two independently implemented quotient-counter calls, flips a classification
bit to test rejection, and tests insufficient capacity. It streams input words
to Python for hashing instead of saving large flag arrays. With no `--case`,
three million-word differential cases cover low integers, the critical region,
and the analytic transition near1.49 trillion. Exact compiler/library/executable/
source hashes and actual resource measurements are recorded in `RESULT.json`.

These are ordinary native differential receipts. Neither the untrusted proposal
library nor successful native output is promoted to a Lean axiom or a verified
network claim. The native C++ caller's vector allocation, input loading and I/O
remain outside the source-function proof; matching counts alone do not close
that caller boundary.

## Limits and storage

This component does **not** establish complete finite coverage from
38,358,837,683 to1.49 trillion. It supplies a sound executable source checker and
two concrete source-function applications. The original finite certificate
coverage obligation and any remaining full application/run association must be
reported separately.

Preserve the C/Lean/Python sources, generated accepted local proof sources,
parameters and dependency pins, exact proof receipts and artifact hashes.
Proposal and benchmark scripts deterministically regenerate temporary arrays;
the benchmark retains no large prime lists or flag arrays. Only experiment-owned
regenerable scratch files may be removed after successful reproduction checks.
Do not delete original sources, accepted proof artifacts, or the only copy of
any required certificate. This replay performs no cleanup automatically.
