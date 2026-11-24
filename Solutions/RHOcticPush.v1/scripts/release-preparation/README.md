# Final RH release preparation

This directory prepares explicit release inventories and synthesizes status
from real receipts. It does not run new mathematics, approve publication, change
Git or upload files. Original analytical/numerical results and immutable source
packets are preserved.

`prepare_inventory.py` joins explicit publication manifests in chronological
order. Every changed same-path entry is recorded in `COLLISIONS.json`; only the
final selected bytes are checked against the publication tree. It additionally
checks every immutable analytic2577/finite130 packet member and adds their exact
outer metadata. It does not choose source scope by recursively scanning a
workspace. `ramanujan/RESULTS.json` is an explicit mandatory report input.
The output is a **review-required candidate**, never a self-approved bundle spec.

The already executed candidate uses historical source commit4f54 as an identity
argument only. It is not the final source publication or a claim that later
additive files were already present at that historical commit. Root must supply
the actual reviewed final source commit when preparing the release inventory.

`assemble_status.py` reads all eight result receipts and exact independently
provided SHA pins in `GATES_PENDING_V3.json`. Missing receipts or missing pins stay
pending. Changed or malformed pinned receipts fail. Its checks follow the real
schemas: the warm count is `[N,count]`; earlier arithmetic is preserved through
origin provenance, not conflated with the number of new records; the24
IEANTN controls have individual nested receipts and eight exact cases per mode.
The original nine controls and prior configs are preserved as history.
The assembler is status
synthesis, not a replacement for the original validators and independent review.

The completed core source identities, new theorem and byte-lemma locators, and
two C source hashes must be filled from compiler-accepted source before final
assembly. A physical line is checked against the actual named declaration. The
numerical witness is kernel-derived; no new native check, physical trace, whole
ISO-C adequacy, canonical point node or full finite Ramanujan coverage is claimed.

Only the three `captured_sources` core identities may name a module command.
The audit source has no theorem declaration: its truthful identity is the exact
published `final-completion-v1/source/CountSourceAudit.lean` path, declaration
`run_cmd`, kind `module_command`, physical LF5, and the accepted source hash.
That variant requires the four normal identity fields plus `kind`, and the
located line must start `run_cmd do`. It is not permitted for the final IEANTN
theorem or byte lemma, whose identities remain exactly the four original fields
and must locate an actual theorem, lemma or definition. The frozen audit source
is unchanged; no Lean declaration is invented for an elaborator command.

Run a current pending snapshot (a fresh output directory is mandatory):

```sh
python3 -B assemble_status.py --base /path/to/preserved/report-status-v18.json \
  --config GATES_PENDING_V3.json --source-root /path/to/actual/source \
  --out /path/to/fresh/pending-snapshot
```

Once all receipts, public captured-source identities and Root's reviewed pushed
source commit really exist, use the same command with `--final` and
`--source-commit ACTUAL_40_HEX_COMMIT`. It rejects any pending gate. Copy the
generated `FINAL_STATUS.json` into the reviewed publication/report input set.
Historical statuses, failures, drafts and receipts remain unchanged.
The config's `source_publication` is the exact independently read-back remote
source receipt `{path,sha256}`. Its commit must match the CLI argument and its
row identities must contain every cited final theorem, byte lemma and C source.
The final report artifact itself still requires Root's separate content/browser
review; status synthesis is not that review.

Pending snapshots preserve the dated base-status worker observation; they do not
claim that current source workers have stopped. Release follow-up belongs to
separate dated artifact receipts rather than a stale final theorem-gap list.
The actual high-result route composes current-campaign warm arithmetic with the
fresh cold complement and later append. The monolithic clean full-high portable
recipe remains prepared, with a separately executed bounded smoke; do not claim
that every portable full-high/new-append procedure has actually run.

Root must independently approve the exact candidate inventory before using the
existing `build_evidence_bundle.py`; its reviewed spec status is
`REVIEWED_EXPLICIT_PUBLICATION_BUNDLE_INPUTS`. Neither preparation script flips
that approval flag. Root also owns source publication and final report/browser
review. The renderer's complete input graph, package pins and source files must
be included in the final publication inventory, along with the final count and
IEANTN append concise evidence. Never add object caches, raw8GB data or private
context to compensate for a missing reproduction recipe.

`finalize_bundle.py` takes that independently reviewed spec, exact existing
archive-builder source, generic context, accepted bounded finite run and locked
KaTeX directory. It builds the archive, checks every extracted member under
normal/-O/-OO, splits into6,000,000-byte parts, actually reassembles all parts
under all three Python modes, exercises extracted analytic/finite read-only
frontdoors, reproduces the three final HTML files byte for byte, and runs the
frozen128-source/three-proposal regeneration recipe. It requires the actual
accepted final IEANTN status and the exact published source commit in the
extracted bundle. The delivered reader files, declared closure/context metadata and both actual bank-engine providers are first byte-associated with the original accepted source root. The unchanged original-location IEANTN reader then checks the actual accepted four-source append and complete inherited basis; the association is checked again afterward. This is source-bound historical readback, not relocated/portable verification of the old run or a fresh monolithic high computation. The clean portable full-high recipe and separately executed bounded N1000 run remain distinct. It performs no Lean
compilation. The scientific completion
receipts and actual clean reproduction route remain separately attributed.

The finalizer also compiles and runs the unchanged actual C counter/high driver
from the extracted publication source, using the supplied GCC11 and an available
CPU. It checks the original two source hashes, successful exits and the eight-byte
output55206486339, and records compiler/executable/output identities, actual time
and GNU peak RAM. This is an ordinary native observation, not a proof, source-first
PV by itself or a formal physical trace. The frozen observer's historical labels
apply only to that observation and do not replace the separate Lean proof status.

```sh
python3 -B finalize_bundle.py --spec /path/to/ROOT_REVIEWED_SPEC.json \
  --builder /path/to/publication/Solutions/RHOcticPush.v1/scripts/build_evidence_bundle.py \
  --context /path/to/GENERIC_CONTEXT.json \
  --finite-smoke /path/to/actual/portable-source-smoke-v1 \
  --ieantn-run /path/to/actual/ieantn-count-consumer-v2 \
  --accepted-source-root /path/to/original/accepted/source/network \
  --native-cc /usr/bin/gcc-11 --native-cpu 64 \
  --katex /path/to/locked/node_modules/katex --out /path/to/fresh/final-validation
```

Only after these real checks, final report review and Root approval should Root
publish or deliver. This directory contains no credentials or delivery code.

The standalone `source_association.py` CLI exercises only the byte association, without loading a historical validator or compiling proofs. Supply `--accepted-source-root`, `--delivered-root` and `--ieantn-run`, then either a fresh `--out receipt.json` or `--check-receipt receipt.json`. Its metadata receipt is not mathematical or source-first PV acceptance. The normal/`-O`/`-OO` controls use owned delivered-file fixtures; accepted sources, plans, contexts, proof objects and bank engines are preserved. No ROOT/context monkeypatch or historical receipt rewrite is used.
