# Reproduce the 24-stage source-bound comparison

This comparison uses 11,411 accepted written-source objects and 15,861 expanded receiving functions: 15,822 actual B0/D02 branches and 39 counterfactual branches excluded from the numerical subfrontiers. It does not execute a new ANT scientific program, prove the analytic theorems in Lean, or establish source-first program verification. The original experimental outcomes remain unchanged. The fixed source-defined density/kernel continuation is preserved but is not numerically optimized here.

Use the reconstructed evidence-bundle root, with its `PUBLIC_SOURCE_MAP.json`, original mathematical sources under `evidence/`, and accepted analysis under `frontiers/`. First run the bundle's hash-checking reconstruction command: the three large raw JSON files are restored from their deterministic gzip copies. Keep `frontiers/` immutable. The following commands use a separate working copy inside the source root, because accepted peer receipts intentionally refer to the accepted snapshot.

## Seven-step metadata regeneration

On Linux x86-64 with Python 3.11 (actual runs used CPython 3.11.14), start in the reconstructed bundle root:

```sh
export IEANTN_SOURCE_ROOT="$(pwd)"
export IEANTN_SOURCE_MAP="$IEANTN_SOURCE_ROOT/PUBLIC_SOURCE_MAP.json"
export PYTHONDONTWRITEBYTECODE=1
mkdir -p "$IEANTN_SOURCE_ROOT/reproduction-work"
cp -a "$IEANTN_SOURCE_ROOT/frontiers" "$IEANTN_SOURCE_ROOT/reproduction-work/frontiers"
python3.11 -B "$IEANTN_SOURCE_ROOT/reproduction-work/frontiers/reproduce_analysis.py"
```

The script sequentially executes `collect.py`, `build_premise_policy.py`, `normalize.py`, `compare.py --data-only`, `paired_ratios.py`, `check_interfaces.py --check`, and `build_coverage.py`. It stops on any failed step, retains stdout/stderr and partial receipts, and writes `ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json` only after all steps pass. Every mapped original source read verifies exact SHA256 and byte length; missing mappings cannot fall back to the old workspace. Source collection is byte-identical; all 15,861 function bodies reproduce exactly. Relocation changes outer output provenance paths, so relocated JSON file hashes need not match the immutable originals.

The recorded clean run additionally denied all opens beneath the original workspace, including subprocesses. See `ACTUAL_CLEAN_PORTABLE_ANALYSIS_REGENERATION.json`. This filesystem-read check establishes source independence of this metadata pipeline, not mathematical correctness of an ANT program.

## Offline figure regeneration

The bundle preserves all 11 exact binary wheels and their hash-locked requirements. No package index is required. On CPython 3.11 Linux x86-64, install them into two separate experiment-owned targets:

```sh
export IEANTN_PLOT_WORK="$IEANTN_SOURCE_ROOT/reproduction-work/frontiers"
python3.11 -m pip install --isolated --no-index --no-cache-dir --no-compile --no-deps --require-hashes --only-binary=:all: --find-links="$IEANTN_SOURCE_ROOT/frontiers/plot-wheels" --target="$IEANTN_PLOT_WORK/plot-dependencies-1" -r "$IEANTN_SOURCE_ROOT/frontiers/plot-requirements-with-hashes.lock"
python3.11 -m pip install --isolated --no-index --no-cache-dir --no-compile --no-deps --require-hashes --only-binary=:all: --find-links="$IEANTN_SOURCE_ROOT/frontiers/plot-wheels" --target="$IEANTN_PLOT_WORK/plot-dependencies-2" -r "$IEANTN_SOURCE_ROOT/frontiers/plot-requirements-with-hashes.lock"
IEANTN_PLOT_DEPENDENCIES="$IEANTN_PLOT_WORK/plot-dependencies-1" python3.11 -B "$IEANTN_PLOT_WORK/compare.py"
IEANTN_PLOT_DEPENDENCIES="$IEANTN_PLOT_WORK/plot-dependencies-2" python3.11 -B "$IEANTN_PLOT_WORK/compare.py"
python3.11 -B "$IEANTN_PLOT_WORK/verify_plot_source_lineage.py"
python3.11 -B "$IEANTN_PLOT_WORK/report.py"
```

The actual final study reused two separately cold-verified retained environments; it made no new install or network request. Both executions reproduced the three SVG files and the complete 53,415-point CSV byte-for-byte. Their exact commands, environment manifests and output hashes are preserved in `ACTUAL_PLOT_REGENERATION_RECEIPT.json` and the two individual command receipts. The earlier cold installations checked the same 11 bundled wheel hashes. Output labels are SVG paths, so no external font download is required. `report.py` copies the unchanged licensed offline font renderer and font from their exact mapped sources, embeds the font, and preserves static MathML.

## Coverage and corrections

`QUANTITATIVE_LITERAL_CLAUSE_COVERAGE.json` retains every accepted object. Independent readers checked all 2,252 originally unexpanded source objects; source-role heuristics did not determine inclusion. Fixed receiving clauses are expanded or explicitly mapped; signed lower constraints, sign/root predicates and the remaining exact source-defined operators retain their native contracts. Pending fixed numerical receiving clauses: zero. This does not claim that every retained operator has been numerically optimized.

The final extraction audit retains all 15,437 surviving original function bodies unchanged, adds 424 source-literal branches, and explicitly retires four old source-attribution records. One old weighted bound at 420,000 lacked its source's actual 550,000 guard; three other retired rows were redundant first-three-receiver restrictions attributed to the wrong object. The accepted mathematics and primary outcomes did not change. Exact domain queries in normal, `-O`, and `-OO` reject the weighted bound before 550,000 while retaining the three licensed receivers from 420,000. These are interface corrections, not arithmetic counterexamples.

All comparisons are source-bound sufficient-function diagnostics. The 284 exact paired monomial comparisons include 160 strict common-ray improvements; these are dependent function pairs, not 284 or 160 independent experiments. No overall exposure advantage, optimality, best-known bound, source-first PV, or complete analytic Lean result is claimed.
