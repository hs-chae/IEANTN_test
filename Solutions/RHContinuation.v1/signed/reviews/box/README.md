# Independent review of the full box analytic derivation

`REVIEW.json` preserves the original Lean/canonical comparison, fourteen independent mathematical checks and two requested source repairs. `REPAIR_ACCEPTANCE.json` accepts both repairs in the six current live documents and independently verifies their archived originals. Both primary PDF images visibly print the non-strict domain T≥2π; the earlier strict extraction was wrong, and no endpoint mismatch is counted. This is a written mathematical review and does not close the five remaining Lean analytic inputs.

`PRIMARY_SOURCE_PINS.json` identifies the exact PDFs and their SHA-256 values. The necessary zero-count Corollary1 is in the **Mean square** paper, not the separately titled **Accurate estimation** paper. Both were inspected before that citation correction was requested. Original scientific copies remain in the experiment-owned local source archive; the pinned URLs regenerate them.

The optional native Arb cross-check runs with the hash-pinned Python-flint0.9.0 dependency already documented in `../../mobius/requirements-linux-x86_64.txt`:

```bash
python check_scalar_anchors.py --out /scratch/box-review-normal.json
python -O check_scalar_anchors.py --out /scratch/box-review-O.json
python -OO check_scalar_anchors.py --out /scratch/box-review-OO.json
```

Each output path must be fresh. All13 strict anchor checks passed in every mode. These computations are ordinary directed numerical review evidence. The whole-domain argument is given explicitly in `REVIEW.json`; it is not inferred from a grid, and this review makes no source-first PV claim.
