# Independent review of the November 2026 Fourier preprint

Start with `REVIEW.json`. It is structured input for the campaign's rendered reports, with exact primary locators, written Lean identities, proof hashes, numerical outputs, comparison limits and separate trust classifications. The review covers the specified theorems, tables, equations and programs; it is not an exhaustive census of every citation in the paper.

The original author archive is pinned to Zenodo record 24429650, version 2. Its SHA256 is recorded in `reproduce_published.py`. All 45 archive members matched the preserved original source before and after execution. The verifier programs were executed unchanged with their assertions enabled.

## Reproduce the numerical checks from a clean environment

Use Linux, Python 3.10 or newer, GNU time andprlimit. Run:

```
python3 reproduce_published.py --out /absolute/new/output
python3 postcheck.py --run-root /absolute/new/output --out /absolute/new/output/POSTCHECK.json
```

The first command downloads the pinned archive, verifies its SHA256 and original SHA256SUMS, extracts an experiment-owned source copy, creates a virtual environment, installs python-flint 0.9.0, and runs the three prioritized integer and Arb witnesses, the original explicit-constant verifier, and the separate retuned-margin comparison. Each numerical process has a 64 GiB address-space limit and 7200-second CPU limit. It records exact commands, source/output hashes, elapsed time and actual per-process GNU time evidence. No random seed is used.

For an offline original archive, add `--archive /absolute/path/ORIGINAL_SUPPLEMENT.zip`. An existing python-flint 0.9.0 environment may be selected with `--python-flint /absolute/path/venv/bin/python`. Do not resolve the virtual-environment executable's symbolic link into the system interpreter.

To reproduce the two remaining Table 1 rows, use the extracted original programs:

```
python3 /absolute/new/output/original-source/certificates/certify_integer.py /absolute/new/output/original-source/certificates/witness-rh.json /absolute/new/output/original-source/certificates/witness-grh-m80.json --grid-size 1048576
/absolute/new/output/venv/bin/python /absolute/new/output/original-source/certificates/certify.py /absolute/new/output/original-source/certificates/witness-rh.json /absolute/new/output/original-source/certificates/witness-grh-m80.json --grid-size 1048576
```

All five Table 1 rows were actually rerun with both methods in the saved study. The supplementary two-row commands and their resource evidence are under `evidence/remaining-Table 1-two`. The reproduction and postcheck are ordinary numerical procedures; they are not formally verified program checkers or source-first PV.

## Reproduce the Lean comparisons

The campaign uses Lean 4.34.0-rc2 and Mathlib 71a80585ee495fc24472fd0eaffc89d94e4fd8d6. Provide a context JSON containing the pinned compiler path/hash and compiled generic library paths, then run:

```
python3 compile_comparison.py --context /absolute/pinned/GENERIC_CONTEXT.json --out /absolute/new/curve-proof
python3 compile_comparison.py --context /absolute/pinned/GENERIC_CONTEXT.json --module RetunedPublishedScalar --out /absolute/new/scalar-proof
```

`WholePopulationComparison2026.lean` proves exact algebraic comparisons of the printed population-width curves. `RetunedPublishedScalar.lean` proves a conservative real-function lower bound over the complete closed slab by log concavity and kernel endpoint certificates. Both actual builds used only the standard three axioms. These proofs do not establish the paper's analytic source reductions or FFT correctness, and the scalar proof does not close the new variable-coefficient analytic extension.

The original paper's Lean version and scope are different and are recorded in `DEPENDENCIES.json` and `REVIEW.json`. Its native-assisted FFT facts and explicit analytic hypotheses must remain visible.

## Evidence and cleanup

Actual run receipts, original stdout/stderr, executed compiler sources and version metadata are preserved under `evidence/`. The pinned original paper, archive, rational witness files and source code are retained by the campaign. FFT arrays were held in memory and were not stored. After a successful clean numerical reproduction and three-mode postcheck, a second regenerable virtual environment was removed using a hash-verified cleanup preview. Its installation receipt and all numerical/proof evidence remain; one reusable environment was retained for ongoing work.

The final independent verdict and every comparison qualification are in `REVIEW.json`. No source or numerical result from this review has been promoted into the verified mathematical network.
