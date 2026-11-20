# Completed fresh packed-million replay

The entire default pipeline finished successfully: it regenerated the original
source data and both packed proposals, rebuilt all 549 selected application
modules plus the final audit in a fresh application object bank, and passed
three actual completed-run readbacks under normal Python, `-O` and `-OO`.
Neither an old application object bank nor a prepared-source tree was reused.

This reproduces the existing source-linked result for every real input from
38,358,837,683 inclusive to 38,359,837,684 exclusive, with Ramanujan gap strictly
greater than 501,901. All original 285 rows and six C source bindings are
unchanged. It is the original 549-source packed provider, not the separate new
554-source certified-list/balanced-data variant. The latter has accepted
incremental proofs and source-plan controls, but no new full cold proof replay.

The source-first part uses the actual C checker/counter/e/log/cell source,
AST semantics and mathematical consumers. Packed-mask and byte-count arithmetic
are ordinary Lean-kernel computations. This does not prove a new native C
bitset/codec, physical loading of modeled input words, an unverified caller, or
physical native-output association. The exact compiler/core-runtime and other
previously documented platform boundaries remain. The selected final theorems
have only `propext`, `Classical.choice` and `Quot.sound` dependencies, with no
native execution axiom or admitted proof.

Measured times are 9,285.671 seconds for the complete default frontend,
including 125.521 seconds for original source regeneration and 0.204 seconds
for packed-proposal generation. The guarded-backend invocation took 9,136.740
seconds including planning; its proof-scheduler receipt records 8,957.427
seconds. There were 550 successful compiler executions, zero compiler failures
and zero recorded compiler OOM/SIGKILL events. The largest measured compiler
worker RSS was 32,291,508,224 bytes, for `QuotientCSourceV2`. Peak aggregate RSS
or PSS was not measured. Address-space reservations are not actual RAM usage.

The proof-replay directory held 5,879,483,597 logical bytes at completion.
The whole default pipeline held 10,280,724,279 logical bytes and 10,305,310,720
allocated bytes when this packet was collected. A separate sampled peak of
145,467,936,768 allocated bytes covers the **entire shared experiment root**,
including other work; it is not attributed to this replay. The run's resource
observations and reservation journal are preserved. Two dispatch pauses were
transient disk-usage measurement errors; no memory exhaustion was observed in
those samples. The scheduler recovered and drained every started compiler.
No machine-wide OOM-monitoring claim is made.

`frontend/` and `backend/` preserve the exact final results, plans, source
preparation commands and executed controller copies. `compilers/` contains all
550 original `RUN.json`, `stdout`, `stderr` and GNU-time `rusage` files.
`COMPILER_INDEX.json` binds every receipt, source snapshot and compiled object
hash. `OMITTED_REGENERABLE_ARTIFACTS.json` records the hashes and sizes of large
source/object duplicates omitted from this packet; the original accepted
artifacts remain intact. The small generated final audit source is included.
All files in this packet are hashed by `PACKET.json`.

The positive readback originally resides at
`/data/ivy-ramanujan-source-pv-20261119/packed-default-replay-launch-v1/INDEPENDENT_POSITIVE_ALLMODE_READBACK.json`.
Its exact copy is under `readback/`. These are actual completed-run commands,
not plan-only acceptance or merely a pending watcher. The old historical
replays and the separate analytic/high-count experiments retain their own
receipts and scopes.

To regenerate from a clean checkout, use the owner publication receipt's exact
commit and the existing `packed-numerical-source-v1` source supplement. Follow
`REPRODUCE_PACKED_MILLION.md`, with the fresh-clone context/root relocation
instructions in `REPRODUCE_PRIME_BASE_COMBINED_CLEAN.md`: bootstrap the pinned
compiler/generic paths, save the pristine metadata, and set both the supplied
context and clean clone's canonical `BUILD_CONTEXT.json` to one chosen shared
experiment root. All outputs must remain beneath that root for complete disk
accounting. Do not modify the original active research checkout or any pins.
The pins are Lean 4.34.0-rc2 and Mathlib commit
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Required reproduction scripts are
copied under `scripts/` and individually hashed. Then, from the solution:

```sh
python3 scripts/reproduce_packed_million.py \
  --context /data/ieantn-ramanujan-reproduction/context.json \
  --out /data/ieantn-ramanujan-reproduction/fresh-packed \
  --bound-result --jobs 6 --cpus 84,85,86,87,88,89
python3 scripts/reproduce_packed_million.py \
  --check /data/ieantn-ramanujan-reproduction/fresh-packed
python3 -O scripts/reproduce_packed_million.py \
  --check /data/ieantn-ramanujan-reproduction/fresh-packed
python3 -OO scripts/reproduce_packed_million.py \
  --check /data/ieantn-ramanujan-reproduction/fresh-packed
```

Choose available CPU cores and fresh output names. The guarded policy requires
genuinely available 1 TiB RAM, a 512 GiB host reserve, separately 1 TiB free
disk, and at most 300 GiB total owned scratch. Aggregate compiler reservations
are at most 300 GiB, with the existing 96/192 GiB profiles; the observed maximum
reservation was 288 GiB. Regeneration is deterministic and uses no random seed.
Native proposal generators remain untrusted until their kernel/source-linked
proof consumers succeed. The final receipt is published only after every
required compile and independent selected-theorem readback succeeds.
