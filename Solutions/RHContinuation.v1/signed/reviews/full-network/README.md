# Independent final core and report review

The current report acceptance is `FINAL_REPORT_ACCEPTANCE.json`. It records the exact final EN/KO HTML hashes,63 static MathML displays per report, byte-for-byte regeneration in normal/-O/-OO, and24 checks against actual scientific source manifests, proof/resource ledgers and canonical metadata. Earlier report receipts remain historical and are explicitly separated from the final revision.

`CORE_REVIEW.json` records the bounded mathematical statement/binder review of the other tracks and separately labels self-authored signed results. `ROOT_BINDER_TYPES.json` and `RootBinderAudit.lean` instantiate all11 actual theorem types from the five stable root metadata files; `ROOT_BINDER_BUILD.json` and `ROOT_BINDER_AXIOMS.txt` record kernel acceptance with only the standard three axioms. No generated sorry-bearing Challenge module was imported into that proof.

`REPORT_REVIEW.json` preserves the original nine correction groups. The full box mathematical review and accepted documentary repairs are in `../box/REVIEW.json` and `../box/REPAIR_ACCEPTANCE.json`; the latter preserves the original review and withdraws a text-extraction error about the source endpoint.

To repeat HTML byte regeneration, run `review_reports.py --out /scratch/fresh-review.json` with Python normal, -O or -OO. It does not modify the report files. The ledger checks and previous primary reviews do not constitute an exhaustive source-claim audit of the whole repository, a new official Comparator run, or a claim that remaining analytic Lean contracts are closed.
