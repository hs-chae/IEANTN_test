# Evidence-bundle CLI controls

These are archive-integrity and reproduction controls, not mathematical proof
acceptance and not source-first program verification. The accepted test run
uses the exact builder hash recorded in `ACCEPTANCE.json`.

From `Solutions/RHOnePrimeEvolution.v1`, choose a fresh owned output directory:

```sh
python3 evidence/bundle-validation/test_bundle_cli.py \
  --script scripts/build_evidence_bundle.py \
  --out /absolute/path/to/fresh-bundle-controls
```

The script snapshots the builder bytes before execution. It invokes the real
build and verify CLIs in normal, `-O` and `-OO` modes: 87 cases in total, comprising
12 positive cases and 75 rejecting controls. Independent builds must be byte
identical; extraction must reproduce the exact source data and manifest. The
negative cases change source hashes and sizes, archive payloads, member
populations, relative paths, duplicate members, duplicate JSON keys and rows,
commit identities and README bytes/types. They also test existing destinations
and unsupported arguments. Every negative must reach its intended stderr guard,
return nonzero and emit no acceptance output; fresh rejected destinations must
remain absent. Acceptance checks use explicit errors, never Python assertions.

`CLI_CONTROL_LOGS.zip` preserves the actual stdout/stderr, builder snapshot and
run receipts. `CONTROL_EVIDENCE_MANIFEST.json` records every member hash. The
initial README counterexample is retained separately and in that archive: an
earlier verifier accepted changed README bytes while the embedded manifest
still stated the original guide. This was repaired before the final bundle was
built, and the corrected README regression rejects in all three modes. The
original counterexample receipt is historical failure evidence, not acceptance.

After checking the completed procedures and compressed logs, only the hashed,
previewed tiny fixture copies were removed. `CLEANUP_PREVIEW.json` and
`CLEANUP_RESULT.json` record the selection and deletion. They do not include any
mathematical source, proof object, locked input or irreplaceable certificate.
The test script deterministically regenerates all deleted fixtures.
