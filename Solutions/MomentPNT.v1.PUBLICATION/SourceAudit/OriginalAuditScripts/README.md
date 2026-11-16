# Exact mathematical-input source audit

This audit compares the unchanged 14 mathematical input interfaces and all 45 instantiated source-owned definitions against nine original papers. The frozen universe uses (file, declaration line, Lean name), with 59 final rows: 50 externally verified contracts and nine explicitly internal parameter choices. No material contract mismatch was found. This is a mathematical source-contract comparison; it does not independently reprove the papers, formalize their literature computations, or establish source-first program verification.

Open PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html offline. All 83 formulas are static MathML. Long formulas have labelled, keyboard-focusable scroll panels. The CSV and actual PDF hashes are preserved alongside the report. The reader can follow every interface and supporting definition to its exact Lean, Blueprint/module and paper locator.

## Reproduce the evidence gate

From this directory, run Python 3 check_evidence_v1.py --out fresh-check.json. The destination must not exist. Repeat with python -O and python -OO; acceptance does not rely on assert. The script checks current exact source hashes, the frozen 59 identities, all nine primary PDFs, the report/ledger association and the installed lean-source-math-audit validator with --require-final. The skill is pinned by its SHA in each receipt.

To regenerate HTML, run render_review_v1.py with the pinned latex2mathml 3.81.1 installation documented in RENDER_RECEIPT_V4.json. Preserve historical outputs; use a separate copied experiment directory if a destination exists. check_report_v1.py performs the offline Playwright gate; see browser-v3/RECEIPT.json and its resource scope for the exact executed command, dependency paths and viewport metrics. PDF extracts use PyMuPDF; original papers and manifests are retained, not regenerated from extracts.

RECEIPT_V2.json is the latest exact evidence inventory. Prior receipt/report versions remain historical. No independent final-finding double-check was invoked because no material finding list was assembled; this qualification is explicit rather than a claim of independent peer review. The two original complete-main boundaries were separately read against actual source and recorded in frontend/proof/NUMERICS_BOTH_MAIN_BOUNDARY_REVIEW_V1.json; that review is not a fresh compilation.
