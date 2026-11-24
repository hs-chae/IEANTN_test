# Reproduce the RH one-prime and network evolution campaign

This directory adds source-conditional mathematical theorems, not a source-first C/C++/CUDA PV result. Read the four offline reports and the theorem matrix first. The CMS analytic inequality and the historical finite-gap computation are explicit assumptions. The existing octic Green/Nicolas/BPT package is unchanged.

## Exact environment

- Linux x86-64; Python3.11; GNU time and prlimit; Git; Node20 for report rendering only.
- Lean `leanprover/lean4:v4.34.0-rc2`.
- Mathlib `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`; all transitive generic revisions are in `scripts/LOCAL_CONTEXT.json` and the repository `lake-manifest.json`.
- Baseline repository3539bbba83db8345db1c43f37a9ddb6d8baf3ab0. The final source commit is recorded in SOURCE_PIN.json when published. No default-branch or historical-result replacement is intended.
- At the original launch RAM available and free disk were measured separately. Four source-build workers, each capped at64GiB address space, were used; actual measured RSS is in the execution receipts. A lower worker count is supported. This is not an obsolete4GiB rerun.

The compact evidence bundle contains a byte-identified selected source closure and a self-contained frontend under `portable/`. Generic toolchain/Mathlib packages are fetched at their exact pinned revisions rather than bundled as huge compilation caches. The portable frontend copies and hashes all application sources before executing Lean, and it never imports predecessor application objects.

## Clean-environment proof reproduction

1. Install the pinned Lean toolchain with elan. Obtain this exact Git revision or unpack the evidence bundle. The repository's checked-in `lake-manifest.json` must remain unchanged.
2. In the repository root, obtain the pinned generic dependencies and their Mathlib cache using the normal Lake cache procedure (`lake exe cache get`). This step reuses generic dependencies, not any IEANTN or campaign proof objects. Do not run `lake update` to silently change dependency revisions. To build generic libraries from source instead, use the pinned manifest and `lake build Mathlib`.
3. Run `python3 Solutions/RHOnePrimeEvolution.v1/portable/reproduce.py --help`. Supply the colon-separated generic library paths and the actual pinned Lean binary as shown by the help. The frontend validates generic revisions, the source manifest and imports, freezes the controller and sources, and rebuilds the complete selected transitive application closure in a fresh output directory.
4. The selected roots include the actual final consumer audit. Read its24headline exact-type/axiom/body/input-use checks in the generated compiler log; require a successful execution receipt and the matching source/object hashes. `FinalConsumerAudit.lean` is a checked audit of actual theorem values, not an assumption of their correctness.
5. The historical runtime reader and development helpers in `scripts/` are source-location-bound evidence tools. Use the portable frontend for relocated clean reproduction; do not edit a historical receipt or bypass its path/hash guards.

A full fresh portable replay is recorded separately from focused development builds. Its receipt states exactly which application modules were rebuilt and which generic objects were reused. The original execution receipt and source hashes remain unchanged.

## Reproduce the original research numerical experiments

The external experiments are E, not new verified-network numerical providers. They require Python packages pinned in the individual experiment receipts. Preserve the distinction between the Gaussian optimizer (untrusted witness generator), rational witness coefficients, and interval-checking scripts.

- `analytic/screen_kernels.py --help`: deterministic initial multi-kernel screen.
- `analytic/search_gaussian.py --help`: Fourier-eigenbasis optimization and exact rational witness output. Preserve recorded degrees, Fourier convention, parameters and seeds from ANALYTIC_HANDOFF.json.
- `analytic/certify_gaussian_objective.py --help`: exact polynomial identities, real-root isolation, Arb Gaussian moments and infinite tails. This is external interval verification, not Lean or source-first PV.
- `analytic/sample_hat_witness.py --help` and `analytic/certify_hat_witness.py --help`: rational piecewise-linear FOURIER windows and actual external sample/cell/tail checks. The Fourier window is not the physical-space function.
- `comparisons/Published2026Review/reproduce_published.py --help`: fetch the pinned public supplement, verify its archive SHA, create the pinned Python environment, and rerun all five printed Table1 rows plus Table3. The original source files stay unchanged. Assertion-based original upstream scripts are run with Python assertions enabled; their results are external computations, not an optimization-safe accepted Lean provider. The campaign's wrapper controls/receipts are separate.

The relevant exact small witness packets, parameters, commands, source hashes, rounding modes and receipts are in the evidence bundle. Historical source/run association failures and solver failures are preserved as failed/provisional runs; final accepted external runs use frozen source copies. Any newly developed Gaussian kernel lemmas are explicitly separated from a completed Fourier objective certificate.

## Reproduce the reports

Install build-time KaTeX0.16.47 in an owned Node directory. No reader-side CDN or JavaScript is used. From this directory run:

```sh
python3 reports/build_matrix.py
python3 reports/build_reports.py --katex /absolute/path/to/node_modules/katex --run /absolute/path/to/fresh-final-all-v1
```

The renderer uses strict KaTeX to emit static MathML, strips hidden raw-TeX annotations, and embeds the pinned STIX font. Font identity/license are supplied under reports/fonts/. The browser verification checks all four reports on desktop and mobile with network access disabled, compares the actual DOM prose to the generated source text, and checks internal links and horizontal overflow.

The exact primary-source versions, hashes and download URLs are recorded in sources/DOWNLOADS.json and the comparison review. Primary papers are kept as original research evidence; the public package supplies provenance/download instructions rather than assuming permission to republish entire papers. A fetch failure is not evidence for a source claim.

## Canonical IEANTN integration and limits

`python3 scripts/ieantn.py gen-challenges`, `check-graph`, and the genuine fingerprint/hash route are distinct from solution proof checking. The core generated Challenges deliberately contain the project's permanent proof placeholders. Accepted solution closures import Conclusions and mathematical proofs, not those Challenges. Node approval status remains local until an official workflow issues its own receipt. A locally constructed audit or report must never be called that official approval.

The selected root inventory is exactly the24headline theorem contracts in four new proved node versions, plus two explicitly external input nodes. It is not a source-claim census of the entire repository. The matrix contains the exact physical source identities, quantified statements, assumptions and limitations for each headline.

## Safe storage cleanup

Keep original sources, locked inputs, accepted proof banks, small rational certificates, parameter/seed files, execution commands, hashes, failure receipts and required evidence. Only previewed experiment-owned duplicate caches or regenerable scratch may be removed after the corresponding reproduction route actually passes. The cleanup receipt lists the exact path, hashes, retained copy and regeneration procedure. End-of-run disk measurements are not exact peak-disk measurements.
