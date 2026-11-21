# Final IEANTN RH mathematical review

Open `REVIEW.html` offline. Mathematical expressions are static MathML with an
embedded licensed STIX font. Long equations scroll inside their own boxes.
`sources/` contains the exact primary PDFs; `frozen/` contains the relevant
unaltered final-arm files, and `node-statements/` the inherited literal contracts.

The requested PNT, weighted, primorial and interval derivations were reviewed.
The 87-file manifest identifies the exact frozen population; it is **not** a claim
that all declarations in those 87 files received a complete source audit.
Ramanujan610/640, their crossing/program verification, Laurent.md's sign recovery,
and Root's post-lock Mertens-positive synthesis are separate and excluded.

Two comparison errors were confirmed: the Lee–Nosal1.1 transcription and the
claimed global order between Lee–Nosal1.1/1.2. Correct comparisons preserve the
adaptive A, A+.821 and A+.332 improvements. Weighted and direct interval
derivations were mathematically validated with their cited numerical-source
inputs retained. The same-source CH2 Corollary9.3 qualification is recorded.

Formal limits stay explicit: PNTClosed retains RH and eight predicates; A+.332,
weighted spectral integration and CMS/DGM are written proofs; the Lean primorial
consumer retains hband and positive P. This review does not claim a new inherited
application compilation, RH-only Lean proof, source-first PV, or global novelty.

Reproduce the 51 finite exact-rational checks (Python standard library only):

```sh
python3 check_scalars.py SCALAR_CHECKS.json
python3 -O check_scalars.py SCALAR_CHECKS_O.json
python3 -OO check_scalars.py SCALAR_CHECKS_OO.json
```

Regenerate the report from the supplied frozen excerpts and bundled renderer:

```sh
python3 make_review.py --portable
```

The checked normal, `-O` and `-OO` renderer outputs have identical HTML bytes.
Optional desktop/mobile link and glyph checks require Playwright1.62.0 and its
Chromium installation, as already present in the recorded environment:

```sh
python3 verify_report.py
python3 -O verify_report.py
python3 -OO verify_report.py
```

The browser receipts bind the exact HTML hash and test all local report links,
17 focused cards, 87 rendered math expressions, the embedded font and horizontal
body fit at1240 and390 pixels. Actual critical-card screenshots were inspected.
Exact-rational scalar checks are ordinary arithmetic checks, not a kernel proof
of their checker implementation and not source-first program verification.

`PRIMARY_SOURCES.json`, `FROZEN_INPUT_MANIFEST.json`, `REVIEW.json`, and
`FINAL_RECEIPT.json` preserve source/claim identities, scope and final checks.
The original frozen87 files were rehashed at completion and were unchanged.
No worker contact, frozen edits, job edits or push occurred. Local file existence
does not establish external delivery; attachment/upload is handled separately.
