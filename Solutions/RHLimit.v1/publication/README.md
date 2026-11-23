# RHLimit publication and verification

The frozen candidate completed the actual six-route, 620-command source replay.
The final publication adds a narrowly documented legacy receipt-check repair and
separate full final-consumer replays. Exact provenance and the final-archive
execution boundary are recorded in `../ledgers/REPRODUCIBILITY_FINAL.json`.
The helper controls below are toy CLI controls; they are separate from the real
mathematical runs. Every source freeze still requires an exact ROOT_FINAL_READY
receipt against the reviewed plan. The original candidate and its outcomes are
preserved.

The source plan includes all new `Solutions/RHLimit.v1` files except enumerated
private/runtime/paper exclusions, the exact reviewed canonical file whitelist,
and selected prerequisites from the previously published source archive. The old
archive SHA256 is pinned in `prepare_bundle.py`. No unrelated old reports or
entire old solution trees are copied. The complete baseline core, exact legacy
inventory gate, generic bootstrap recipe/metadata, old111 frozen modules and
46-source C-log route are included because active replayers consume them.
The report renderer's exact old latex2mathml package, STIX font and font license
are included. Application proof objects and downloaded papers are excluded.

`archive_tools.py` is the unchanged earlier publication helper. `join_bundle.py`
reuses the previous split/join implementation with distinct RH_LIMIT_SOURCE
part names, exact part membership, and explicit extraction-helper hashes.
Every part is at most6MiB. `prepare_bundle.py` adds current-source and resource
identity gates, all340 unique source modules, the reviewed canonical whitelist,
and the explicit final-root approval gate. `REPRODUCE_RH_LIMIT.py` runs the clean
π-complete controller, spectral append, box/C-log route, finite analytic bridge,
octic route, and final24-source canonical extension. The raw source count is
not a count of newly invented numerical programs.

## Before final readiness

Verify and reconstruct the prior archive from its original parts into owned
scratch, using the prior join helper. Then supply a reviewed canonical file list:

```
{"schema":"RH_LIMIT_REVIEWED_CANONICAL_FILES_V1",
 "files":[{"path":"IEANTN/Nodes.lean","sha256":"...64hex..."}, ...]}
```

Generate a fresh plan; this inventories source bytes without copying or freezing
the research tree:

```
python Solutions/RHLimit.v1/publication/prepare_bundle.py plan \
  --network /absolute/network \
  --prior-archive /absolute/prior-source.tar.gz \
  --canonical /absolute/reviewed-canonical-files.json \
  --out /absolute/scratch/FINAL_SOURCE_PLAN.json
```

Without `--canonical`, the command emits an explicitly incomplete draft.
`pending_canonical_paths` lists required current canonical associations that the
whitelist has not yet supplied. A final freeze rejects either condition.
The plan must be regenerated after any source, report, controller, receipt, or
selected canonical file changes. Root must inspect and approve the actual plan.

## Final root gate and archive

Only after root sends ROOT_FINAL_READY, provide this exact receipt shape:

```
{"schema":"RH_LIMIT_ROOT_FINAL_READY_V1","status":"ROOT_FINAL_READY",
 "approved_plan_sha256":"...SHA256 of final plan...",
 "network_HEAD":"...exact plan network_HEAD...",
 "canonical_files":[...exact sorted canonical_files from plan...],
 "canonical_replay":{
   "script":"network/Solutions/RHLimit.v1/scripts/reproduce_integration.py",
   "argv":["--basis","{pi}","--spectral","{spectral}","--out","{out}"],
   "receipt":"RESULT.json",
   "expected_status":"PASS_COMPLETE_340_SOURCE_NETWORK_EVOLUTION_CONSUMERS"}}
```

`PROPOSED_CANONICAL_REPLAY.json` supplies only the route object, not approval.
The default clean π controller captures the C resource itself. The recorded
initial π run plus explicit preparation/fresh23 replay remains separate history;
that historical route's optional resource argument is not required by the clean
bundle default.

Use fresh scratch outside the mathematical checkout:

```
python Solutions/RHLimit.v1/publication/prepare_bundle.py freeze \
  --plan /absolute/scratch/FINAL_SOURCE_PLAN.json \
  --ready /absolute/ROOT_FINAL_READY.json --out /absolute/scratch/source-tree
python Solutions/RHLimit.v1/publication/prepare_bundle.py pack \
  --tree /absolute/scratch/source-tree --out /absolute/scratch/RH_LIMIT_SOURCE.tar.gz
python Solutions/RHLimit.v1/publication/join_bundle.py \
  --split /absolute/scratch/RH_LIMIT_SOURCE.tar.gz --out /absolute/scratch/parts
python /absolute/scratch/parts/join_bundle.py --parts-dir /absolute/scratch/parts --check
```

The packer verifies every archived member's source SHA, size and membership after
packing, in addition to source-tree checks. Joining checks the delivered join and
extract helpers as well as parts and the whole archive. Restore to another fresh
owned directory and run the restored source/dependency preflight before reporting
bundle completion. Preserve exact receipts, commands, hashes, file membership and
source/controller identities. Do not claim file delivery from local existence;
root owns actual upload and downloaded-byte verification.

`BUNDLE_README.md` becomes the download's top-level README. It gives the clean
source checkout, exact generic bootstrap and proof replay commands without a CDN.
`FETCH_GENERIC_SOURCES.py --check` has been exercised against all nine existing
pinned source checkouts without writes. No generic download/build was restarted
for this packaging preparation.

## Controls and storage

```
python Solutions/RHLimit.v1/publication/exercise_controls.py --out /absolute/fresh/controls
```

The full replay uses at most three workers (or one with `--serial`), a 240 GiB
aggregate planning cap and a 512 GiB host reserve. It checks actual available RAM
before launch. Spectral waits for π; canonical waits for all five component
receipts. The main thread alone writes joined logs/receipts; workers execute only
the unchanged child commands. A rejected child stops future launches while
already running child routes finish and retain evidence.

The controls exercise real toy pack/seal/verify/extract/split/join CLIs, rejection
of changed/extra bytes and invalid metadata, and final-ready refusal paths under
normal Python, -O and -OO. They also execute the actual orchestrator toy CLI,
measuring real toy-child overlap (three parallel or one serial), dependency order,
nonzero exit, wrong status, missing receipt and low-memory refusal. Toy results
are explicitly marked as having performed no mathematical replay. No acceptance
uses assert or __debug__. The executed
controllers are frozen in each accepted controls directory. Consult the current
receipt for its exact count and tool hashes; older prototype receipts are not a
claim about a subsequently changed helper.

Scratch is confined to `/data/ivy-rh-limit-20261122/publication`. The reconstructed
prior archive is regenerable from retained original parts, but is still an active
packing prerequisite until final freeze. After final restore/reproduction checks,
preview and remove only experiment-owned regenerable intermediate archives and
toy fixture data. Keep accepted receipts, exact source/controller copies, original
parts, final verified downloads and essential evidence. No Git commit/push is
performed by this worker.
