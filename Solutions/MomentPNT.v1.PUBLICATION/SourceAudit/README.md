# Source and mathematical-contract audit evidence

[Open the complete offline report](PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html).
It covers the fourteen actual mathematical input interfaces and all forty-five
instantiated source definitions. Every one of its eighty-three formulas is
statically rendered. Each row identifies the actual Lean declaration, module
correspondence and precise primary theorem, equation, proof passage or table.
This is the completed existing source audit, made accessible in this repository;
no mathematics or review verdict has been changed.

The publication changes only hyperlinks. `LINK_ONLY_MANIFEST.json` records every
replacement. Reversing those replacements recovers the exact original report
hash; every other byte and all MathML formula hashes remain unchanged. All fifteen
linked Lean sources are copied byte-for-byte under `SourceSnapshots`. The ledger
and inventories bind all fifty-nine written declaration identities to those
actual source hashes. `RECEIPT_V2.json` is the unchanged original audit receipt.

`PRIMARY_PAPERS.json` gives nine exact cached PDF identities, actual versions and
physical page counts. The report links directly to their primary sources with
precise page anchors. The PDFs are not republished here. In particular, KLN links
to the actual May 2018 author manuscript, whose pagination was audited; an arXiv
version is not silently substituted. The author's PDF server timed out during
this publication check. Its real primary directory lists the manuscript, and
the exact cached source remains preserved with its hash; current external server
availability is not claimed. That does not remove the source statement already
compared in the report.

## Recheck the publication

From the repository root, use a fresh output filename:

```sh
python3 Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/verify.py \
  --out Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/Checks/my-replay.json
python3 Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/verify_identities.py
```

These checks need only Python's standard library and work offline. Normal Python,
`-O` and `-OO` have all passed. They validate exact report recovery, all formula
hashes, every actual source snapshot, all fifty-nine source identities, all 134
hyperlinks, every local target and all primary URL/page identities. An optional
`--papers /path/to/downloaded-pdfs` also checks all nine cached primary PDF hashes.
The completed publication run used that option against the retained original
PDFs. `Checks` contains the actual receipts.

`check_browser.py` requires Playwright/Chromium. Its completed offline run checked
mobile and desktop layout, all eighty-three MathML formulas, all forty-five
expandable source-definition rows and keyboard access. Long mobile formulas
remain available in labelled, keyboard-focusable horizontal scroll panels.

`OriginalAuditScripts` preserves the exact historical renderer/checker source as
evidence. Those scripts expect the original research layout and are not the
portable publication commands above. The source audit compares paper contracts;
it does not reprove the papers or execute the numerical programs. Its receipt is
separate from the six conditional theorem proofs, source-first execution proofs,
source-cold replay and any official IEANTN Comparator receipt.
