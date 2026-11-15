# Bounded independent review of the 768-cell height result

Read `REPORT.html` offline. Mathematics is rendered with static Unicode and HTML; no CDN or extension is required.

This is an independent mathematical-path review by the controls agent. It found no defect in the named conditional PNT and prime-rich path. It does not claim exhaustive original-paper attribution coverage, a fresh source-cold replay, or completed source-first program verification.

From the repository root, run:

```
python research/analytic/independent-review-controls-v1/reproduce_review.py
python research/analytic/independent-review-controls-v1/make_report.py
```

The script checks the two accepted Lean receipts against current source hashes, requires all four selected roots' printed complete Std3 axiom closures, enumerates the actual 96×8 height checks and 6×4×32 budget coverage, extracts the actual 24 integer caps, and independently recomputes the exact rational final upper bound and prime-rich transfer. It records source identities and anchors in `REVIEW.json`. All acceptance checks use explicit exceptions and were run successfully normally, under `-O`, and under `-OO`.

These finite checks supplement the manual review described in the report; they do not substitute string checks for proof verification. The reused Lean receipts explicitly document their warm kernel environment, source hashes, original commands and objects. To rebuild those theorem proofs, use the analytic owner's reproduction procedures; this bounded review does not claim to have repeated that build itself.

The report enumerates all eight fields of `PrimaryInputs` and all six separate original assumptions with their exact mathematical content and baseline correspondence. It preserves their conditional status. Actual C producer execution and output-to-ANT association remain separate unfinished source-first PV obligations.
