# Required source-layout step for the final evidence bundle

The primary archive and all 53 delivered parts are unchanged. Before running the seven-stage analysis from that extracted archive, use the supplementary `reproduction/prepare_locked_source_view_v2.py` helper below. The canonical report, paper, original numerical runs and mathematical conclusions are unchanged.

## Why the extra step is needed

Reconstruction deliberately retains a compressed transport member such as `review.json.gz` and restores its exact original `review.json`. The source collector correctly requires the physical contents of each locked source directory to equal its original `LOCK.json` inventory. The additional transport file is absent from that original inventory, so the first analysis run from the complete delivered bundle stopped at this strict membership check. Archive reconstruction, report rendering, paper regeneration and the resource ledger had already passed; that initial analysis failure is preserved. The earlier successful clean source-only mirror contained no transport extras, so it did not exercise this final archive-layout interaction.

The checked preparation plan identifies 71 transport copies totaling 2,787,265 bytes inside 45 of the 60 distinct locked directories reached by the frozen collector. The helper verifies every original locked payload and both compressed/restored hashes before moving any file. It moves only manifest-declared gzip transport extras that are not `PUBLIC_SOURCE_MAP.json` destinations into a fresh sibling directory. Original JSON, LOCK files, code, assumptions and mathematical data stay byte-identical. Nothing is deleted and no strict check is weakened.

V2 covers all 86 actual LOCK-validation call routes, which resolve to 60 distinct directories, including assessment/finalization views and the explicit C021 closed view. Its route set is checked against all mapped LOCK markers. The first helper correctly moved 42 copies in the 48 direct source/review directories, but the next analysis stopped at the additional view routes. Those 42 moves were hash-verified and reversed before testing V2 against the original fresh-primary layout. Both failed analysis attempts and the first helper’s partial preparation remain historical evidence.

## Prepare the source view

Use the full reconstructed primary bundle and the separately downloaded supplement. The helper is pinned to the delivered primary manifest SHA-256 `665f6b37153f2fc145c50b0008d300cbb450b09d04aabf20b09ac461880e2608`; its source SHA-256 is `03c5e279963a0f2c0230232c99a105c5bcc8e06e2f57ae31314a0bf7b43d5c62`. Choose a fresh sibling transport directory and fresh receipt filenames:

```sh
BUNDLE=/absolute/path/extracted-evidence
DOWNLOADS=/absolute/path/downloaded-primary-parts
SUPPLEMENT=/absolute/path/extracted-supplement
BUNDLE_PARENT="$(dirname "$BUNDLE")"
python3 -I -B "$SUPPLEMENT/reproduction/prepare_locked_source_view_v2.py" \
  --bundle-root "$BUNDLE" --manifest "$DOWNLOADS/PUBLIC_MANIFEST.json" \
  --transport-root "$BUNDLE_PARENT/separated-transport-copies-v2" \
  --receipt "$BUNDLE_PARENT/TRANSPORT_PLAN.json"
python3 -I -B "$SUPPLEMENT/reproduction/prepare_locked_source_view_v2.py" \
  --bundle-root "$BUNDLE" --manifest "$DOWNLOADS/PUBLIC_MANIFEST.json" \
  --transport-root "$BUNDLE_PARENT/separated-transport-copies-v2" \
  --receipt "$BUNDLE_PARENT/TRANSPORT_APPLIED.json" \
  --apply-from "$BUNDLE_PARENT/TRANSPORT_PLAN.json"
```

The first command produces a plan without moving files. The second recomputes that exact plan before moving the verified transport copies and checks all 60 original physical LOCK memberships afterwards. Keep the sibling directory and both receipts. To restore the initial extracted layout, reverse only the recorded file moves, checking the compressed hashes; this also restores the known extra-file condition. Re-extracting the unchanged primary archive is another exact reset.

## Run the existing analysis

Run the original seven-stage recipe after the source-layout step. Use a fresh `reproduction-work-after-transport-v2/frontiers` destination; preserve any previous failed work directory and its logs separately.

```sh
cd "$BUNDLE"
export IEANTN_SOURCE_ROOT="$BUNDLE"
export IEANTN_SOURCE_MAP="$BUNDLE/PUBLIC_SOURCE_MAP.json"
export PYTHONDONTWRITEBYTECODE=1
mkdir "$BUNDLE/reproduction-work-after-transport-v2"
cp -a "$BUNDLE/frontiers" "$BUNDLE/reproduction-work-after-transport-v2/frontiers"
python3.11 -B "$BUNDLE/reproduction-work-after-transport-v2/frontiers/reproduce_analysis.py"
```

This is the existing collection → premise policy → normalization → comparison data → paired ratios → interface checks → source coverage pipeline. It does not rerun model research or the 24 numerical workloads. The supplement is a post-delivery reproduction correction, not a replacement primary result, new mathematical experiment, complete analytic Lean proof or source-first PV.

## Actual replay status

After V2 preparation, the actual seven-stage analysis completed all seven commands with exit code 0. Its 11,411-object source collection and all 15,861 complete function bodies are byte-identical to the accepted data (15,822 actual branches and 39 excluded counterfactual branches). The separately completed report and paper retain identical mathematical content, including 259 and 138 MathML expressions and the main report’s three SVGs; the all-24 resource-ledger JSON is identical. Both earlier failed analysis attempts remain preserved.

[Actual final replay receipt](evidence/final24-actual-final-bundle-reproduction-v1/ACTUAL_FINAL_BUNDLE_CLEAN_PIPELINES_AFTER_TRANSPORT_VIEW_FIX.json), SHA-256 `7cb868e8cb8f2c81e29cdbd8901b652c4c73fe57639f7c1859cacb00e39352a3`.

The final supplement retains both initial analysis failures, V1 preparation/restoration history, the complete V2 plan/application receipts, the subsequent actual analysis receipt and independent equality readback. The original primary archive SHA-256 remains `a332f37373cfe5afb0c5800b5b62fa426671d42c3ed1370dcd26d0d99dca9b3d`.
