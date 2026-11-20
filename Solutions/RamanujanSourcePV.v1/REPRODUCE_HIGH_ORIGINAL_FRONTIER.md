# Reproduce the original high-endpoint certificate frontier

This bounded study regenerated and kernel-compiled all 692 original packed-data modules for the proposed count at 1,490,000,000,000, compiled the original gap data and aggregate data, and accepted the first original numerical check. That check verifies entries 0 through 32,767 of the 90,670,946-entry demand certificate. Its exact Lean fact is `RamanujanPV.HighTransitionCount.part_0000`; it has no axioms. A separately compiled theorem checks its exact type.

**The proposed prime count 55,206,486,339 is still unverified.** The gap predicate, remaining 2,767 numerical chunks, unions and final count theorem were not completed in this bounded study. Data typing does not establish the numerical predicates. This stage is ordinary kernel certificate verification; it is not source-first PV by itself and does not complete the finite Ramanujan range.

## Clean prerequisites

Use the exact Lean 4.34.0-rc2 compiler and dependency commits in `BUILD_CONTEXT.json`. The compiler SHA-256 must be `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Build the pinned generic dependencies and make a clean-context JSON pointing to their clean-machine locations. Keep the revisions and compiler hash fixed. The replay checks generic dependency commits and tracked-source cleanliness. It rebuilds every selected application module into a new proof-object directory; it copies no historical application objects.

The full route requires Linux, Python 3, GNU time, genuinely available RAM of at least 1 TiB and independently free disk of at least 1 TiB. It preserves the configured host reserve, normally 512 GiB. It uses at most 300 GiB of simultaneously reserved worker address-space limits. Available RAM and free disk are checked separately. CPU IDs are configurable and must actually be available. No random seed is used.

## Original fixed target

From this directory, run:

```sh
python3 scripts/reproduce_high_original_frontier.py \
  --context /absolute/clean-context.json \
  --out /absolute/fresh-high-frontier \
  --cpus 96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127 \
  --jobs 32
```

The output directory must not exist; its parent must exist. The script first regenerates the unchanged original proposal with `generate_demand_certificate_resources.py`, using query 1,490,000,000,000, name `HighTransitionCount`, 131,072 entries per data page and 32,768 per numerical check. It hashes the actual packed data and every generated source file and compares all 3,464 original module identities with `evidence/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json`. These identity checks preserve the original unverified candidate and algorithms.

It then invokes the tested `reproduce_profiled_closure.py` on the first original check alone. Its dependency closure contains every original raw-data page, gap data, aggregate data and the numerical codec. Resource profiles are raw pages 9 GiB, gap data 24 GiB, aggregate data 128 GiB, first check and independent final audit 256 GiB. The scheduler reserves each cap before dispatch, limits their sum to 300 GiB and drains dependencies before starting the larger consumers. It never starts the other numerical checks or the final count theorem. The reported chunk fact must be axiom-free.

Read back a completed run with:

```sh
python3 scripts/reproduce_high_original_frontier.py --check /absolute/fresh-high-frontier
```

The reader checks the exact target, source population, fixed original identities, mandatory evidence files, fresh replay receipts, source/object/log hashes and the actual numerical fact's empty axiom set. It rejects a claim that this partial route proved the prime count.

## Small workflow controls

For a short test of the same orchestration, use `--smoke --cpus 0 --jobs 1` with an available CPU ID. This uses the separate fixed queries 1,000 and 367, a separate namespace and 190 demand entries. It is explicitly labelled a small control. A smaller clean machine can choose an appropriate explicit `--host-reserve-gib`, with minimum 8 GiB. The small route reserves 24 GiB for compilation.

Actual fresh small routes passed under normal Python, `-O` and `-OO`. Readbacks and 18 negative CLI controls also passed; see `evidence/HIGH_FRONTIER_REPRO_CONTROLS.json`. These controls establish operation of the portable driver. They do not claim that the new clean driver has already repeated the entire original high run. The recorded original high study used the same original numerical sources with the independently reviewed raw-stage controller and exact compilation commands retained in its receipts.

## Recorded measurements and trust

`evidence/HIGH_ORIGINAL_FIRST_CHECK_PROFILE.json` records the completed bounded study. All 692 raw pages passed in 2,689.02 seconds; the sampled parallel RSS peak was 101.88 GiB and proportional-set-size peak 86.27 GiB. Their actual objects total 41,460,494,904 bytes. The original gap data passed in 453.55 seconds with 11.90 GiB peak RSS. Aggregate data passed in 0.543 seconds with 0.633 GiB peak RSS, showing that total imported object size is not equal to resident RAM. The first original numerical check passed in 88.019 seconds with 13.22 GiB peak RSS. No actual compiler failure or OOM occurred in those stages.

The exact per-compiler GNU time receipts are complete. The first-check auxiliary sampler retained its samples through the terminal RSS drop but was stopped during tool-session cleanup before publishing its own final receipt. Its reconstructed maxima are labelled sampled-trace readback; they are not presented as a completed monitor run. Scheduler address-space limits and sampled sums are distinct from measured per-worker peak RSS.

The original proposer, packed words and gap lists are untrusted until their corresponding numerical checks succeed. Lean's kernel and pinned compiler/core runtime remain trusted. This bounded prefix does not assert a C execution result, a physical executable/output association or any new analytic premise. It could contribute to an actual source-counter theorem only after the complete count certificate and mathematical consumers are accepted.

## Evidence and storage

Keep the exact source, parameter and identity files, dependency pins, accepted proof artifacts, compiler receipts and hashes. `evidence/high-original-first-check-v1` preserves the small actual selected receipts and logs; large gap-data source is deterministically regenerated and its exact hash is retained. Original sources and accepted objects remain in the experiment-owned evidence bank. The scripts do not delete data. Remove only verified-regenerable experiment-owned scratch after checking reproduction, never original research inputs or the sole accepted evidence copy.
