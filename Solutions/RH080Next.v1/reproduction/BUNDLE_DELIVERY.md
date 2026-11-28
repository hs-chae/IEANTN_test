# Source/evidence bundle: build, verify and reproduce

The single offline HTML is the reading report. The compressed bundle contains
source code, proof statements, exact fixed inputs, regeneration recipes,
verification receipts, the paper PDF/TeX and Korean text summary. Packaging
checks artifact bytes; it never supplies a mathematical proof or source-first
PV approval.

## Build after the final proof/source review

`select_source_bundle.py --require-complete` must first succeed at the exact
reviewed source commit. Its manifest must have no unresolved families, source
identities or regeneration obligations. All selected source bytes must still
match, and that reviewed commit must be the repository's current HEAD when
building the archive. Do this before a subsequent report-only commit, or
rerun source selection at that later reviewed commit.

The bundle builder accepts explicit file manifests only. It does not archive a
workspace recursively. Source paths are put under `repo/`, exact evidence
paths under `evidence/`, and supplied PDF/TeX/text files under `supplement/`.
Do not supply private research prompts, transcripts, SDK payloads, memory,
credentials or upload helpers. Existing proof objects stay protected in the
research workspace; the clean source pipeline regenerates them.

```sh
python3 Solutions/RH080Next.v1/reproduction/build_bundle.py \
  --repository /absolute/reviewed/repository \
  --source-manifest /absolute/complete/SOURCE_BUNDLE_MANIFEST.json \
  --evidence-manifest /absolute/completed/EVIDENCE_SELECTION.json \
  --evidence-manifest /absolute/final/EVIDENCE_SELECTION.json \
  --supplement PAPER_EXPOSITION.pdf=/absolute/final/PAPER_EXPOSITION.pdf \
  --supplement PAPER_EXPOSITION.tex=/absolute/final/PAPER_EXPOSITION.tex \
  --supplement KOREAN_MATHEMATICAL_SUMMARY.txt=/absolute/final/KOREAN_MATHEMATICAL_SUMMARY.txt \
  --out /absolute/fresh/bundle-output
```

Use additional repeated `--evidence-manifest` arguments for independent checks
or the optional external interval tier. Duplicate archive destinations and
changed/missing source bytes fail. The single HTML is delivered separately;
it is not another HTML copy inside this archive.

The builder writes a deterministic XZ-compressed tar, pieces no larger than
8,000,000 bytes, `BUNDLE_PARTS.json`, the exact offline `verify_bundle.py`, and
an artifact acceptance receipt. Before writing that receipt it verifies every
member hash, reassembles the actual pieces through the delivered reader and
verifies the reconstructed archive again. Original research proof acceptance
and official Comparator acceptance remain separate questions.

## Verify downloaded files and extract them

Download every numbered part, `BUNDLE_PARTS.json` and `verify_bundle.py` into
one directory. From that directory run:

```sh
python3 verify_bundle.py --parts BUNDLE_PARTS.json \
  --out RH080_NEXT_REPRODUCIBLE_BUNDLE.tar.xz \
  --extract fresh-rh080-bundle
```

The command requires fresh output paths. It checks each piece, the ordered
complete archive, the member population, and every member's exact bytes before
extracting. It prints `PASS_ALL_ARCHIVE_MEMBER_BYTES` only after those checks.
A missing or changed piece fails; download that piece again and use fresh
output paths. No compiler or mathematical claim is established by this file
integrity check.

To verify an already reconstructed archive without extracting it:

```sh
python3 verify_bundle.py --archive RH080_NEXT_REPRODUCIBLE_BUNDLE.tar.xz
```

## Reproduce the mathematics and numerical data

Open `fresh-rh080-bundle/REPRODUCE_README.txt`, then
`repo/Solutions/RH080Next.v1/reproduction/README.md`. The latter gives the
pinned Lean/compiler/library setup, exact Python requirements, separate
resource admission, generation/check/compilation stages and their expected
result kinds. The source manifest identifies every included file and every
large deterministic output omitted in favor of checked regeneration. The
optional external dual tier has its own Python3.12.9/python-flint0.9.0 recipe;
it remains outside Lean/source-first PV and the verified theorem network.

The recorded posthoc process profile and exact outer bootstrap/pipeline
recipe are in `reproduction/PROCESS_RESOURCE_PROFILE.md`. Its process-only
THP/affinity observation is an explicit generic platform/resource boundary,
not source-first PV or a theorem. The associated evidence preserves earlier
allocation failures and the intentional memory-stall stop. No causal speedup
is inferred from the tiny diagnostic observations.

The archive preserves the recorded primary/censored/negative outcomes. A
later proof or resource continuation is supplemental evidence, not a change
to an original timed experiment's status.
