# Reproduce the complete generic C program proof

The portable entry point rebuilds all 491 pinned application source modules,
including the complete actual norm-function proof and `FFTSourceOutput`.
It uses only the eight pinned generic Lean/Mathlib object libraries. It does
not load application proof objects and does not duplicate the separately
verified large literal N17/N24 numerical traces.

The full 491-module source-cold replay passed in 1,032.51 seconds, followed
by three actual validator successes and twelve mutation rejections across
normal Python, `-O`, and `-OO`. Exact per-compiler peak RSS was 39,568,330,752
bytes; the 0.5-second sampled aggregate peak was 79,113,412,608 bytes. No
compiler failed or received SIGKILL. The whole source
function contracts also have completed source-associated compiler receipts;
the separate fixed numerical-certificate and ANT applications have their own
receipts and must not be inferred from this generic replay.

Use the exact toolchain and dependency revisions in [DEPENDENCIES.json](DEPENDENCIES.json).
Create the generic context using `make_context.py` as described in the main
[README](README.md#reproduce). From this directory, in a clean repository copy:

```sh
python3 reproduce_main_source.py \
  --context /absolute/clean_proof_context.json \
  --run /absolute/fresh/main-source-cold \
  --scratch-root /absolute/experiment-root \
  --workers 4 --worker-memory-gib 64
python3 check_main_source_cold.py \
  --run /absolute/fresh/main-source-cold \
  --out /absolute/fresh/main-source-cold-controls
```

[MAIN_SOURCE_COLD_INPUTS.json](evidence/MAIN_SOURCE_COLD_INPUTS.json) records
module identities, repository-relative paths and exact source hashes. The
portable wrapper verifies each source byte and regenerates absolute paths for
the chosen clean checkout. No private object-bank path is needed. Preparation
was tested using an independent temporary source tree, without application
objects, under normal Python, `-O`, and `-OO`; that regenerable duplicate tree
was deleted after its source hashes and all preparation results were checked.
This preparation test is not a second Lean proof replay.

The default high-resource replay requires genuinely available 1 TiB RAM,
independently free 1 TiB disk, a 256 GiB host memory reserve, and campaign
scratch below 290 GiB. Four compilers each receive a 64 GiB address-space
allowance. Use an outer service or job scheduler with a 300 GiB aggregate RAM
limit and appropriate CPU allocation. The controller samples its own descendant
RSS, available host RAM and campaign scratch, and stops only its own children
if its resource reserve fails. Its resource receipts distinguish sampled
aggregate RSS from exact per-child GNU-time maxima.

Each actual compile produces source, object, command, exit-code, diagnostic,
time and hash receipts. Strict checks reject a nonzero compiler exit, a missing
proof object, `PANIC`, compiler errors, unverified printed axioms or incomplete
printed axiom audits. A final check verifies the entire requested source
population against the external pinned inventory. Acceptance never depends on
Python `assert` or `__debug__`.

The control script runs the actual completed-run validator under normal
Python, `-O`, and `-OO`. In each mode it also requires rejection of an exit-zero
panic diagnostic with an updated log hash, a changed proof object, a missing
compiler receipt, and omitted source coverage with an updated plan hash.
Mutation fixtures use isolated links and copied mutation targets; accepted
source/proof artifacts are never edited. The regenerable fixture directories
are removed after their commands, hashes and rejection results are preserved.

Keep the completed source snapshots, proof objects, exact source inventory,
compiler/context/dependency pins, receipts, diagnostic logs, resource records
and validator-control receipts. This generic replay creates no large prime
list, FFT sample array or numerical certificate dataset to clean up. The
separate literal trace studies retain their own regeneration and cleanup rules.
