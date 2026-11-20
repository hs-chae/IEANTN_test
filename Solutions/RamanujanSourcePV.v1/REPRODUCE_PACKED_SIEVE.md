# Deterministic packed sieve and source-count provider

The generic proofs classify every integer in a segment using exact integer
bitsets. No list of primes, probabilistic primality test, supplied classification
or numerical count is assumed. A geometric-series identity proves each stride
mask; finite ORs and least prime divisors prove the full classification. An
independently proved 256-entry byte table counts the bits. The accumulator
version has the same mathematical output, and masked prefixes reuse a single
proved segment bitset.

The resulting claims are represented in an explicit heap built from the
existing source-owned static-array layout. Ownership, allocation extents, word
ranges and argument bindings are proved. The complete actual segmented C
checker initializes scratch storage, sieves, compares the claims and returns a
count. Its existing positive-output soundness theorem supplies the count objects
used by the IEANTN consumers. The exact same C AST is linked to the unchanged
`c/verified_segment_checker.c` bytes. No application initialization or correct
output is trusted as a generic platform fact.

`PackedSieveProvider.source_bound_provider` is the strongest generic interface.
It requires the previously verified source count immediately before the segment,
the segment's exact range, and a length fitting the fixed source storage. Every
in-segment prefix count follows. Numerical instances require separately accepted
kernel equalities for the segment bitset and its prefix counts. Consult their
actual final receipts; the generic theorem does not certify a proposed number
merely because a native program printed it.

The numerical packed-bitset arithmetic is kernel verification, not source-first
PV of a new C bitset implementation. There is no new C bitset implementation in
this stage. The source-first part is the separately verified, source-linked C
segmented checker and the existing C counter consumed by the provider. A
physical loader, native caller or process/output association is not proved by
these function-level contracts; generic compiler, ABI, runtime and hardware
boundaries retain their stated separate scope. The experimental `swarCount`
function is not used on the proved byte-count provider path.

## Accepted generic components

`evidence/packed-sieve-generic-v1/RESULT.json` records eleven current source and
proof-object identities and 43 actual theorem axiom reports. Only the standard
Lean axioms occur. The compact accepted receipts include commands, compiler and
dependency pins, execution times, actual peak RSS, output logs and source hashes.
Failed development attempts remain in the original audit directories.

The exact generic provider closure contains 56 application modules, as recorded
by the tested plan in the experiment's `packed-provider-plan-v1` directory. A
plan is not completed cold verification. Use the final separate replay receipt
when a full clean run has completed.

The actual clean generic replay subsequently passed: 56 application modules
plus a fresh selected audit, 378.742 seconds, maximum observed worker RSS
32,291,819,520 bytes, and 58,656,932 bytes of replay storage. No old application
objects were reused; there were no OOM events, failures or resource pauses.
All three actual normal/`-O`/`-OO` complete readbacks passed. The source-only
receipt packet is `evidence/packed-provider-cold-v1/`; its final result SHA-256
is `82630d7222962077971fae327c0c780504c212be0ede2256c97a4fc03a0e9cff`.
This completed replay proves the generic provider, with its explicit anchor and
range inputs. It does not supply a pending numerical million-window instance.

## Clean application replay

Use Linux x86-64 and the pinned Lean 4.34.0-rc2 / Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6` context. Obtain the pinned generic
libraries with `lake exe cache get` at the repository root, and create a fresh
context using `scripts/bootstrap_context.py` as described in
`REPRODUCE_COUPLED_ANALYTIC.md`. Then run from this solution directory, choosing
available cores and fresh experiment-owned paths:

```sh
python3 scripts/reproduce_guarded_coupled_closure.py \
  --context /data/ivy-ramanujan-source-pv-20261119/packed-clean-context.json \
  --out /data/ivy-ramanujan-source-pv-20261119/packed-clean-replay \
  --root RamanujanPV.PackedSieveProvider \
  --theorem RamanujanPV.PackedSieveProvider.source_bound_provider \
  --theorem RamanujanPV.PackedSieveSource.source_execution \
  --theorem RamanujanPV.PackedSieveSource.primeCounting_increment \
  --jobs 2 --cpus 10,11 --memory-gib 48 --aggregate-gib 96 \
  --host-reserve-gib 512
python3 -OO scripts/reproduce_guarded_coupled_closure.py \
  --check /data/ivy-ramanujan-source-pv-20261119/packed-clean-replay
```

The guarded helper checks separate actual RAM and disk allowances, reserves
resources before dispatch, and drains running children on a signal or failure.
It reuses only pinned generic libraries and creates fresh application objects.
Its final atomic acceptance requires every selected module and a new theorem
axiom audit. A partial checkpoint is not a successful run.
