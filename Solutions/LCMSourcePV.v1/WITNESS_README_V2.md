# Witness: start with the corrected replay

Use `reproduce_v2.py` and `audit_replay_v2.py` for a new replay. The original
`README.md`, `reproduce.py` and `audit_replay.py` are preserved historical
evidence. The original producer omits the generated axiom auditor's Lean root
argument and can fail when its output directory is outside the source tree.
Do not use that producer for a fresh replay. `RECIPE_PATCH_V2.json` records the
precise correction; all Lean, C, certificate, parameter and `SOURCE_LOCK.json`
bytes remain unchanged.

## Prepare the public generic environment

From the extracted release root, use an already prepared, pinned public Lean
4.34.0-rc2/Mathlib installation:

```sh
python3 adaptive/source-only-v1/prepare_environment.py --component witness --toolchain /absolute/lean-4.34.0-rc2-linux --mathlib /absolute/mathlib --out /fresh/witness-environment.json
```

Witness requires eight exact generic dependencies. PrimeCover requires its
separate nine-entry metadata profile, including Cli. The components share a
public installation, but their environment JSON populations differ. No old
application object cache is an input to a fresh replay.

For a fresh public installation, first run the release's pinned bootstrap and
then give its actual toolchain and Mathlib paths to the preparer above:

```sh
python3 adaptive/source-only-v1/generic_environment/scripts/bootstrap.py --work /fresh/public-generic --receipt /fresh/public-bootstrap.json
```

## Run in the offline namespace

The distributed source project supplies the existing namespace helper through
`network/Solutions/LCMSourcePV.v1/reproduction/run_isolated_component.py`.
From the release root, run:

```sh
python3 network/Solutions/LCMSourcePV.v1/reproduction/run_isolated_component.py --component witness --capsule witness/source-only-final-v1 --environment /fresh/witness-environment.json --out /fresh/witness-isolated --jobs 16
```

This Linux launcher mounts the source read-only, creates fresh work and temporary
directories, exposes only the pinned generic compiler/dependencies, and disables
network access. It runs the corrected producer and the corrected strict auditor
in normal, `-O`, and `-OO` modes. A successful run writes the outer `RECEIPT.json`
and `work/NAMESPACE_PIPELINE_RECEIPT.json`; the three strict receipts must agree.
Adding `--preflight` checks the actual namespace setup and source/generic pins
without running the proofs or C constructor. A preflight receipt is not full
proof acceptance. The project wrapper and its original sandbox helper are
additional release files; they are not embedded in the preserved Witness ZIP.

The measured source stage used a 256 GiB limit, 24 CPU-affinity cores and 16
single-threaded Lean children. One source-binding child used about 24 GiB RSS.
Arrange adequate host resources before starting; this wrapper does not impose
those resource limits itself.

## Optional host replay

For a direct host replay, run from this capsule directory with fresh outputs
outside it:

```sh
python3 reproduce_v2.py --environment /fresh/witness-environment.json --out /fresh/witness-proof --jobs 16
python3 audit_replay_v2.py --replay /fresh/witness-proof --out /fresh/witness-strict
```

These commands rebuild all 1164 selected application modules, audit every
application theorem compiler identity, compile/run the actual C constructor,
and compare all 404 rows and 3232 output words with the kernel-bound source-main
output. Direct host execution is host evidence; it does not establish namespace
isolation.

## What the accepted evidence establishes

The accepted final run is an explicit composition of two actual namespace
stages. The original stage freshly compiled all 1164 application sources, then
the auxiliary axiom-audit launcher failed because its Lean root argument was
missing. The continuation verified every source/object/log hash and successful
child result, reused only that same-campaign checkpoint read-only, and ran the
corrected all-theorem audit, the actual C404 constructor and the original
immutable strict auditor. It is not a second fresh 1164-module compilation.
All 56282 selected application theorem compiler identities passed the standard
axiom gate. This count includes private/generated declarations; it is not a
count of new authored lemmas or an external-source attribution census.

The canonical component receipt is
`witness/final-continuation-namespace-v2/work/continuation/CONTINUATION_ACCEPTANCE.json`.
The independent review is
`publication/WITNESS_CONTINUATION_INDEPENDENT_REVIEW_V1.json`; its separate
read-only namespace ran the unchanged original strict auditor in all three
Python optimization modes with byte-identical acceptance receipts. The
component's final index, resource ledger and source selection preserve the
original failed stage, host evidence and continuation separately.

Kernel proofs cover the actual source/AST, application initialization, typed
memory, strict-rank source call trees, stored output, printed rows and unchanged
finite LCM consumer. Whole-ray conclusions retain the original explicit
Dusart 2018 Proposition 5.4 analytic input. Pinned compiler/runtime/unsigned ABI
and successful physical standard I/O remain the approved generic boundary.
No verified machine-code compiler, universal I/O success, optimality or new
numerical premise is claimed.

This README is an additive documentation correction. The original README,
accepted source lock, source selectors, component indexes and sealed ZIP bytes
are preserved.
