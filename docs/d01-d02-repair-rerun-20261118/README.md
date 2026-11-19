# Repository reading copy

This checkout does not contain the paper library or paper-containing source/evidence archives. The full offline bundle is supplied separately to the study owner; [PUBLIC_MANIFEST.json](PUBLIC_MANIFEST.json) records every part and hash. The instructions below concern that complete extracted bundle, not a bare Git clone. See [SOURCE_LIBRARY_MANIFEST.json](SOURCE_LIBRARY_MANIFEST.json) for the exact original-paper URLs and identities.

# Reproduce the D01/D02 follow-up study

The package contains the complete mathematical and numerical follow-up for 24 canonical stages, with 48 application-family summaries. Its 11,411 qualified written-source objects and 595 required numerical command routes are not independent trials or theorem counts. Original experimental outcomes, withdrawn claims and failed attempts remain preserved.

## Read the results

Open `report.html` from the extracted package. Its mathematical notation, font, tables and figures work offline. The same human content is available as `report.md`. The `accepted-floors/` files preserve each complete current mathematical portfolio, assumptions, exact real domains, strictness, source identity and qualifications. The `original-papers/` folder contains the exact seven frozen PDF/text pairs. The separate accepted paper is `paper/ANALYTIC_ENGINE_EXPOSITION.html`; its historical review filename is retained only as an exact reproduction-comparison identity.

The results use written mathematical proofs, named literature inputs and ordinary exact or outward numerical execution. Full analytic Lean formalization, source-first program verification, new verified IEANTN nodes, global optimality and an overall exposure advantage are not established. D01 and D02 are supplied hypothetical inputs; the common corpus already implies D01.

## Reconstruct the evidence download

Keep every numbered part together with `PUBLIC_MANIFEST.json` and `verify_and_reconstruct.py`. Use Python 3 from an empty working directory and choose fresh output paths:

```sh
python3 -I -B verify_and_reconstruct.py \
  --manifest PUBLIC_MANIFEST.json --parts /absolute/path/downloaded-parts \
  --out /absolute/path/evidence.tar.gz --extract /absolute/path/evidence
```

The command verifies every part and the complete archive, rejects unexpected members and restores all selected bytes. Large ancillary JSON remains compressed for direct download and is also restored to its exact original JSON path during extraction. A successful reconstruction verifies archived bytes; it does not by itself rerun a numerical program or prove a mathematical theorem.

## Regenerate the numerical workloads

Start with `reproduction/README_PORTABLE_FINAL24.md`. The immutable numerical source archive is at `evidence/study/coordinator-private/portable-relocation-v2/portable-final24-source-review-v4.tar.gz`; its adjacent receipt ends in `.tar.gz.RECEIPT.json`. The extractor checks all 7,303 members. The documented coordinator then checks, prepares or runs the exact 24 case plans without hand-editing authority JSON, authenticating to a model, or changing mathematical parameters. Every final consumer output is checked.

Actual recorded numerical runs used distinct clean roots; the final archive collects their byte-equivalent source and exact command recipes. It is not a claim that every case was run at one later source root. The all-24 resource ledger lists the selected actual success per case, with the first failed C022 replay separately preserved.

The reproduction prerequisites include the precise Linux namespace/cgroup/systemd setup, pinned Python/compiler/runtime dependencies and resource registry in that README. Retain the original 64 GiB/8 CPU/25 GiB private-scratch policy, zero swap and host reserves. Do not treat disk space as RAM, reinstate a 4 GiB limit, lower numerical parameters or replace a full workload with saved outputs.

## Regenerate accounting, comparison and presentation

**Prerequisite for the delivered primary bundle:** follow [the reproduction addendum](REPRODUCTION_ADDENDUM.html) before the seven-stage analysis below. Reconstruction retains compressed transport copies beside restored original JSON. The original collector correctly rejects those extra files inside exact LOCK directories. The supplementary `prepare_locked_source_view_v2.py` plans and reversibly moves only verified transport extras from all 60 collector-reached locked directories to a fresh sibling directory, preserving every original payload and LOCK byte. Keep both receipts and the moved copies. Use the fresh `reproduction-work-after-transport-v2` directory below; preserve earlier failed work separately. The [actual corrected full-bundle replay](evidence/final24-actual-final-bundle-reproduction-v1/ACTUAL_FINAL_BUNDLE_CLEAN_PIPELINES_AFTER_TRANSPORT_VIEW_FIX.json) passed all seven analysis commands with unchanged source collection and complete function bodies. The canonical report and original experimental outcomes are unchanged.

`PUBLIC_SOURCE_MAP.json` maps each exact original file identity to its location in this package, with SHA-256 and length. The ledger and comparison helpers accept this explicit source map and a package root; mapped-only checks reject access to the old workspace. This preserves historical evidence identities without requiring those original absolute paths to exist. Numerical algorithms are unchanged by source addressing. See the corresponding reproduction scripts and their saved CLI receipts for exact commands and pinned inputs.

To regenerate all seven analysis stages from the restored source bytes, start at the extracted package root and keep the accepted `frontiers/` evidence unchanged:

```sh
cd /absolute/path/evidence
export IEANTN_SOURCE_ROOT="$(pwd)"
export IEANTN_SOURCE_MAP="$IEANTN_SOURCE_ROOT/PUBLIC_SOURCE_MAP.json"
export PYTHONDONTWRITEBYTECODE=1
mkdir "$IEANTN_SOURCE_ROOT/reproduction-work-after-transport-v2"
cp -a "$IEANTN_SOURCE_ROOT/frontiers" "$IEANTN_SOURCE_ROOT/reproduction-work-after-transport-v2/frontiers"
python3.11 -B "$IEANTN_SOURCE_ROOT/reproduction-work-after-transport-v2/frontiers/reproduce_analysis.py"
```

This executes collection, premise policy, normalization, comparison data, paired ratios, interface checks and source coverage. The actual clean seven-step run denied reads of the old workspace, regenerated the collection exactly and preserved all 15,861 stored function bodies: 15,822 actual B0/D02 branches plus 39 explicitly excluded counterfactual branches. Fresh provenance paths and their file hashes may differ after relocation.

To regenerate the three figures in two separate offline dependency directories, use the eleven hash-pinned wheels shipped under `frontiers/plot-wheels/`:

```sh
export IEANTN_PLOT_WORK="$IEANTN_SOURCE_ROOT/reproduction-work-after-transport-v2/frontiers"
python3.11 -m pip install --isolated --no-index --no-cache-dir --no-compile --no-deps --require-hashes --only-binary=:all: \
  --find-links="$IEANTN_SOURCE_ROOT/frontiers/plot-wheels" \
  --target="$IEANTN_PLOT_WORK/plot-dependencies-1" \
  -r "$IEANTN_SOURCE_ROOT/frontiers/plot-requirements-with-hashes.lock"
python3.11 -m pip install --isolated --no-index --no-cache-dir --no-compile --no-deps --require-hashes --only-binary=:all: \
  --find-links="$IEANTN_SOURCE_ROOT/frontiers/plot-wheels" \
  --target="$IEANTN_PLOT_WORK/plot-dependencies-2" \
  -r "$IEANTN_SOURCE_ROOT/frontiers/plot-requirements-with-hashes.lock"
IEANTN_PLOT_DEPENDENCIES="$IEANTN_PLOT_WORK/plot-dependencies-1" python3.11 -B "$IEANTN_PLOT_WORK/compare.py"
IEANTN_PLOT_DEPENDENCIES="$IEANTN_PLOT_WORK/plot-dependencies-2" python3.11 -B "$IEANTN_PLOT_WORK/compare.py"
python3.11 -B "$IEANTN_PLOT_WORK/verify_plot_source_lineage.py"
python3.11 -B "$IEANTN_PLOT_WORK/report.py"
```

The recorded final plotting commands reused two separately verified environments and produced byte-identical SVG/CSV artifacts; all 53,415 plotted points passed source, domain and ordinate checks. The clean recipe uses the same pinned wheels without network access. See `frontiers/README_REPRODUCE_FINAL24.md` for exact dependency versions and the checked command receipts. These figures are finite scalar/vector projections; retained signed, root, integral and quantified operators have not been globally optimized.

The full report renderer uses only the selected data, static mathematical exposition, comparison contribution and licensed embedded font. The manifest records every script and artifact hash. Numerical reruns, analysis regeneration, static rendering and archive reconstruction are separate checks.

## Regenerate the recorded all-24 resource ledger

This recomputes the JSON/TSV accounting from the selected actual receipts and outputs; it does not rerun the numerical workloads. Set the extracted package root and a fresh ledger output directory:

```sh
BUNDLE=/absolute/path/evidence
LEDGER_OUT=/absolute/path/fresh-ledger-output
python3 -I -B "$BUNDLE/reproduction/build_final24_actual_ledger.py" \
  --selection "$BUNDLE/reproduction/FINAL24_ACTUAL_RESULT_SELECTION.json" \
  --source-map "$BUNDLE/PUBLIC_SOURCE_MAP.json" --public-root "$BUNDLE" \
  --require-mapped --out "$LEDGER_OUT"
```

The mapped-only gate requires every historical input identity to resolve through the selected public bytes. The checked normal, `-O` and `-OO` commands regenerated identical ledgers from all 2,194 referenced source/receipt files, with attempted reads of the original workspace denied.

## Regenerate the full human report

Use the exact byte-preserved comparison input, which retains original source identities, and the explicit source map. The renderer checks the corresponding public source copies before writing relative links. Choose a fresh output directory:

```sh
BUNDLE=/absolute/path/evidence
REPORT_OUT=/absolute/path/fresh-report-output
mkdir "$REPORT_OUT"
python3 -I -B "$BUNDLE/reproduction/report-tools/render_main_report_complete_v4.py" \
  --data "$BUNDLE/ALL24_PUBLIC_SCIENTIFIC_STATUS.json" \
  --font "$BUNDLE/fonts/STIXGeneral.ttf" \
  --exposition "$BUNDLE/paper/ANALYTIC_ENGINE_EXPOSITION.html" \
  --comparison-html "$BUNDLE/evidence/study/coordinator-private/twentyfour-normalized-frontiers-v1/REPORT.html" \
  --source-map "$BUNDLE/PUBLIC_SOURCE_MAP.json" --public-root "$BUNDLE" \
  --out "$REPORT_OUT/FINAL_REPORT.html"
```

The same human text is emitted as `FINAL_REPORT.md`, including readable mathematical notation and links to all three SVG figures. The report does not need a model, Markdown library, network connection or installed plotting environment. Source identities are checked separately from presentation; fresh regeneration receipts contain their actual local paths rather than pretending to be the historical run.

## Regenerate the paper offline

The exact Markdown source, unchanged static renderer/CSS and font are included. The two pure-Python dependency wheels have a combined size of 97,300 bytes. All 72 Python source files match the versions used for the accepted paper; their licenses and hashes are retained. No environment installation or network access is required. From the package root, choose a fresh output path:

```sh
python3 -I -B reproduction/reproduce_paper.py \
  --bundle-root /absolute/path/evidence \
  --out /absolute/path/fresh-paper-regeneration
```

This stages the original renderer layout, disables Python site packages in both producer children, imports only the two pinned wheels, renders the Markdown, embeds the licensed offline font and compares the whole mathematical article and all 138 MathML expressions with the accepted exposition. The source-footer relative link may reflect the new layout. Normal, `-O` and `-OO` runs produced identical output; an actual traced clean external copy recorded no reads from the original workspace, including child processes.

## Research design and limits of replication

The package preserves the exact frozen design, source corpus manifest, treatment commit pins, scientific identity routing, model/effort metadata and observed research/review resource receipts. Research stages, same-stage repairs, reviews and numerical replays remain separate. The requested model alias and effort setting are distinguished from the served metadata actually exposed. An immutable backend revision and provider sampling seeds were not exposed.

Exact experimental inputs are under `experiment-inputs/`: the packet manifests from all 80 recorded physical research/review results, explicitly selected common mathematical files, the identical common fresh-worker task, all three actual runtime descriptors and their exact source/compiler/dependency-tree manifests. Private or own-specific task context is not exported by that input selection. Generic inputs and public mathematical artifacts are distinguished from private prompts and reasoning traces.

The original baseline source-rebuild recipes and their hash-pinned compressed source/dependency manifest are in `reproduction/exposure-tools/`. They identify `teorth/IEANTN` at commit `ef21db9ba5dceffd976da71e24f8497b3a13f798` and the native cut of `AlexKontorovich/PrimeNumberTheoremAnd` at `a4fb6989b07e9c76b511807ae93e33e25b820e9b`. To check the preserved baseline pins without starting a build or a model:

```sh
python3 -I -B reproduction/exposure-tools/reproduce_baselines.py --validate-pins
```

For an optional public-source baseline rebuild, follow the two adjacent historical reproduction documents. They describe the different pinned Lean/compiler contexts and generic cache requirements. Those recipes and older baseline rebuild receipts are historical evidence; this follow-up freshly checked the preserved source bytes, schemas and runtime-tree hashes, and did not run a new cold Lean baseline build or a new model experiment. No installed toolchain or generic compilation cache is shipped.

The numerical and analysis pipelines can be regenerated from their preserved source and exact parameters. A new model research campaign would be a new stochastic experiment: the evidence does not promise identical rediscovery, session identities or sampling behavior. The numerical reproduction needs no model service. Full private coordinator prompts, native reasoning traces, authentication data and unrelated workspaces are excluded.

## Resource measurements and cleanup

The generic publication runtime is recorded in `evidence/study/evidence/FINAL_PUBLICATION_PROCESSING_RUNTIME.json`: Python 3.11.14 with its binary hash, zlib build/runtime 1.3.1 and the actual browser dependency context. This is distinct from the scientific Python 3.10/GCC contracts. Compressed bit identity requires the matching compression runtime; exact member hashes, source bytes and numerical conclusions do not depend on identical compression bytes.

Reported execution time, last observed OOM counters, sampled charged-RAM lower bounds, GNU-time process RSS and final retained disk usage are distinct quantities. The observed kernel had no aggregate `memory.peak` file, so no exact aggregate peak is invented. Original published large finite computations remain literature inputs unless explicitly rerun.

Keep original research sources, locked inputs, accepted proof/certificate artifacts, source archives, unique receipts and essential reproducibility evidence. Delete only experiment-owned temporary data after its deterministic regeneration and complete checked replacement have been established. No general host cleanup or deletion of another workspace is authorized by this package.
