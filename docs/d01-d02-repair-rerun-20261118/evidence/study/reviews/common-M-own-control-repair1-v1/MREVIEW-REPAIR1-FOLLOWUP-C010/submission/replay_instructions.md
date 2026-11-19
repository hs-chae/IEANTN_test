# Replay, checkpoints, and identity

Run these offline commands in non-login /bin/bash; use a fresh path if /work/exact_c010 already exists.

```sh
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/exact_c010
cd /work/exact_c010
/usr/bin/python3.10 -B bounds.py all
/usr/bin/python3.10 -B finite_m.py
/usr/bin/python3.10 -B repair.py
/usr/bin/python3.10 -B advance.py certify
/usr/bin/python3.10 -B /work/submission/audit.py /work/exact_c010
/usr/bin/python3.10 -B /work/submission/pdf_layout.py
```

To rerun the last identity comparison against fresh outputs, redirect the first four programs to bounds, finite, repair and advance .stdout/.stderr files in a directory with audit.py. The recorded run launched the four processes concurrently, waited for each, and recorded each exit status. The two optional failed reviewer diagnostics used the correspondingly named audit_attempt*.py script instead. Environment: Python 3.10.12, libmpdec 2.5.1, no third-party computational packages in the replays. Candidate internal imports: bounds.py imports standard-library decimal/functools/math/sys; finite_m.py imports bounds.py and standard-library isqrt/bisect; repair.py and advance.py import bounds.py. audit.py additionally reads repair.py and advance.py; it compares recorded outputs (so run after the four base scripts). Exact hashes in LOCK.json, audit.stdout, review.json and the pinned packet indices.

| Program | Checks and mathematical coverage (see review.md for adjoining analytic proofs) |
|---|---|
| bounds.py all | Constant and source anchors; quotient sieve at n and floor(n/e); R1 coarse symmetric/signed/fallback finite cells for each onset through 450 plus valid analytic tail anchor; separate six early signed cells up to upward enclosure of log(1.2e17), restricted back to source domain; crossover brackets; S8 constants and prime-power budgets; M1 anchors from 170, .0626 at 300, strict comparisons at 168.82, S5 integral brackets; seven early M cells to 220 and tail anchors. |
| finite_m.py | Exact sieve through 54,000,000; exact prime sums with 2^80 intervals and independent integral tails for constants; local root brackets and no intervening primes; every closed mesh cell from 500000 through 54000000, step floor(left/80000), last clipped. |
| repair.py | Actual small-input FKS counterexamples, root and join anchors to log 2100; actual PT theta counterexample and both sides of all jumps up to 599; dominance of PT published-anchor functions from 3914; corrected CH2 slope at 100. |
| advance.py certify | Signed finite anchors to log 10^13; admissible height and split derivative bounds; M scalar anchors at 300 and 170/200/250/300/1000, 440 split cells to 2500 and tail, both strict envelope onsets and original direct-pi anchors; refined/split R1 cells through 450, deep rows through 450 or 650 and analytic tails. |
| audit.py | Supplementary arithmetic anchors, formula diagnostics, all source/hash identities and byte comparisons. Its checks do not replace the analytic transfers or provide independent new theorems. |

First probe pwd succeeded; ls was not installed, and bash printed a locale warning. Readability of all three named inputs was separately confirmed with bash test. The initial broad directory dump attempted to include large history JSON and was truncated; targeted reads/diffs then used exact pinned sources, not the truncated display. Both PDFs and their supplied page-tagged text identities were checked. No standalone PDF rendering utility was needed: the two ambiguous locations were read from the original compressed vector content streams with pdf_layout.py. The first reviewer attempt mixed Unicode splitlines offsets with raw LF offsets and failed; the corrected readback confirms the raised 8 and the printed FKS delta condition. Neither missing utility was a mathematical blocker.

Checkpoint: complete review at literature/ordinary interval-arithmetic trust. All primary certificates and supplementary audit recorded. No context handoff needed. Remaining optional work is independent source/finite-table verification and formalization, not missing assessment of a candidate branch. History file hashes and the current/archived distinctions are retained; prior statuses were not used to compute the verdict.

Mechanical follow-up: the shared dependency rows now have one exact family identity each. The same evidence is referenced in the Ramanujan and Mertens copies, which carry the same shared obligation ID. Neither the candidate bytes nor the assessments or original replay receipts changed. To regenerate the inventory, run `/usr/bin/python3.10 -B /work/submission/build_inventory.py /work/exact_c010`.

Locator follow-up: each written and implemented source uses the exact relative packet filename under /task, an integer one-based physical LF anchor, and the SHA-256 of the exact bytes. The original restored filename and all reviewed LF spans are preserved separately. No claim or evidence was dropped.
