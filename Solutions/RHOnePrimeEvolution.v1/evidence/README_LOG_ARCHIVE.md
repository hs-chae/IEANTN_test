The copied compiler and audit logs are in
`reproduction/COMPILER_AUDIT_LOGS.zip`. It contains 1,814 stdout/stderr files and
the exact original 1,833-row `COPIED_FILES.json`, stored as
`COPIED_FILES.original.json`. The public `reproduction/COPIED_FILES.json` records
the original path, byte count and SHA-256 for every file, plus its current file
or ZIP-member location. Nineteen JSON, CSV and source-delta files remain directly
readable. Original accepted run directories and proof objects were not cleanup
targets. This is evidence storage verification, not new mathematical acceptance
or source-first program verification.

From `Solutions/RHOnePrimeEvolution.v1`, verify the delivered archive and every
retained file with Python 3.11 or newer:

```sh
python3 evidence/log_archive.py --study . --mode verify --receipt evidence/my-new-log-readback.json
```

Choose a receipt filename that does not already exist. Verification fully reads
every ZIP member, checks its bytes and SHA-256, checks the preserved original
manifest, validates the archive-member associations, and verifies that the
duplicated copied logs have been removed. It writes a fresh atomic receipt only
after all checks pass. The same command works with `python3 -O` or `python3 -OO`.

To reproduce the storage controls in a fresh scratch directory:

```sh
python3 evidence/test_log_archive.py --study . --out /path/to/new-owned-log-controls
```

This reconstructs disposable copies of all 1,833 original evidence files from
the delivered ZIP and retained files. It invokes the actual pack CLI in normal,
`-O` and `-OO` modes; all three must reproduce the delivered ZIP byte-for-byte.
It also runs 18 rejecting verification controls covering declared member
metadata, wrong storage associations, changed member payloads, duplicate ZIP
members and changed retained source evidence. Each must reject without writing
a success receipt. The test preserves commands, output hashes and receipts, then
removes only its previewed disposable copies after the complete test passes.

The ZIP uses lexicographically ordered names, a fixed 1980-01-01 timestamp,
regular Unix 0644 member modes and DEFLATE level 9. The build receipt records the
Python and zlib versions. `--mode pack` is for a fresh unarchived copied evidence
tree; ordinary users should use `--mode verify` on this delivered tree.
