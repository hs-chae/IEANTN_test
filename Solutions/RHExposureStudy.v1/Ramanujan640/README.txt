Actual640-billion Ramanujan theorem: post-lock kernel verification.
Read FINAL_STATUS.html for the exact8 source inputs and remaining li-definition
bridge boundary. This result is not source-first program verification.

Reproduce from an empty output directory on the original host:
  python3 REPRODUCE.py --out /absolute/fresh/output
Check all source/generic pins without building:
  python3 REPRODUCE.py --check
Validate the resulting complete receipt:
  python3 VERIFY.py --package . --replay /absolute/fresh/output/RESULT.json
Reproduce the full normal/-O/-OO acceptance controls in a fresh package-local directory:
  python3 EXERCISE_CONTROLS.py --package . --replay /absolute/fresh/output/RESULT.json --out validator-controls/my-fresh-run

On another prepared machine pass --compiler /toolchain/bin/lean and repeat
--generic-root NAME=PATH for every entry in SOURCE_MANIFEST.json: mathlib,
plausible,LeanSearchClient,importGraph,proofwidgets,aesop,Qq,batteries. Each PATH
is that package's .lake/build/lib/lean. Exact revisions and full file inventories
are included. The6+GiB generic binaries and exact Lean distribution are explicit
prerequisites, not bundled or downloaded. Every application/checker source is
included and rebuilt; no unknown inherited application object is needed.

The actual relocated complete source replay passed before packaging. The runner
regenerates the unchanged original19-node/eight-leaf witnesses, compiles every
selected source, and checks final standard-only axioms. Logs preserve exact
commands, source hashes, returns, dependency paths, time and maximumRSS. Failures
remain nonpassing. No model, network, credentials, sudo or host changes are used.

SOURCE_MANIFEST.json remains the immutable pre-run source selection identity;
FINAL_STATUS.json and evidence/ACCEPTED_REPLAY.json record actual success.
The full generic/library trust boundary and all8 mathematical source predicates
are explicit. Frozen900s/1800s and acceptedV1 artifacts were not edited.
