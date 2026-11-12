# LCM source-first program verification

This source-only solution preserves the original LCM mathematical conclusions and analytic premises while replacing their active native numerical proof dependencies with C-source execution proofs. It is research evidence, with no official Comparator/NanoDa receipt or node-metadata promotion.

The qualified scope is 91 primary mathematical roots plus 67 already kernel-only extension roots in 35 frozen contexts. The 14 original native owners lead to 11 direct fixed source executions: six prime-cover constructors, four Adaptive certificate-checker inputs, and the 404-block constructor. Three weaker historical constructions are bypassed by the proved stronger 404-block constructor. Their original execution propositions are retained historically, rather than claimed as same-algorithm source verification. Four such execution declarations are removed only from active mathematical modules; mathematical conclusion types remain identical.

`Solution.lean` proves the existing `Lcm.v1.challenge_lcmUpto_not_highlyAbundant` from its unchanged explicit Dusart premise by consuming the new source-main output, the finite LCM inequality, and the original analytic tail. The core Conclusions/Challenge files and verification metadata are unchanged. The unresolved upstream source premises for the separate conditional Lcm.v3 route are unchanged.

## Read the evidence

`CAPSULES.json` pins the four immutable source/evidence archives. The full-scope archive includes `audit/FINAL_LCM_CLOSURE_AUDIT.json`, the precise original/migrated theorem identities, the historical execution-proposition ledger, exact kernel-type comparisons, and reproduction qualifiers. The component archives include the actual namespace proof/C receipts and independent readbacks. There are no distributed application objects or executable binaries.

PrimeCover's original namespace wrapper finished its proof/C/strict stages, then failed on the final receipt filename. An independently reviewed additive finalizer retains that failure and binds the completed stages. Witness freshly compiled all 1,164 application sources in its first namespace, then hit a generated-audit root-directory flag error. Its accepted result explicitly composes that fresh source stage with a hash-verified read-only checkpoint continuation, the corrected all-theorem audit, actual C404 output, and independent three-mode namespace readbacks. It is not reported as a second one-shot source replay.

## Reproduce from source

Requirements: Linux with user/mount/PID namespaces, Python 3.10 for the existing namespace helper, Python 3.11 for the optional TOML metadata check, Git, GNU tar/zstd, a C23-capable pinned Clang, and adequate RAM/disk. Internet is needed for the pinned public generic bootstrap, then component verification runs offline. Resource settings should follow actual host capacity; the final proofs did not use the obsolete 4 GiB cap.

Extract the sealed source trees into a fresh directory:

```sh
python3 unpack_sources.py --out /absolute/fresh/sources
```

Prepare one public generic installation. The exact four bootstrap files and preparer are in the extracted Adaptive source tree:

```sh
cd /absolute/fresh/sources/adaptive/source-only-v1
python3 generic_environment/scripts/bootstrap.py \
  --work /absolute/fresh/shared-generic --receipt /absolute/fresh/bootstrap.json
python3 prepare_environment.py --toolchain /absolute/fresh/shared-generic/lean-4.34.0-rc2-linux \
  --mathlib /absolute/fresh/shared-generic/mathlib --component witness --out /absolute/fresh/ENV8.json
python3 prepare_environment.py --toolchain /absolute/fresh/shared-generic/lean-4.34.0-rc2-linux \
  --mathlib /absolute/fresh/shared-generic/mathlib --component primecover --out /absolute/fresh/ENV9.json
```

ENV8 serves Adaptive, Witness, and the mathematical consumer scripts. PrimeCover requires ENV9, including the pinned unused Cli source; its absent optional object cache is explicitly allowed. The public bootstrap recipe is preserved; a second fresh internet download was not performed during this migration.

From this solution directory, execute the three isolated component pipelines, always choosing fresh output paths:

```sh
python3 /absolute/fresh/sources/adaptive/source-only-v1/reproduce.py \
  --environment /absolute/fresh/ENV8.json --out /absolute/fresh/adaptive --jobs 16
python3 reproduction/run_isolated_component.py --component primecover \
  --capsule /absolute/fresh/sources/primecover/source-only-v2 \
  --environment /absolute/fresh/ENV9.json --out /absolute/fresh/primecover --jobs 8
python3 reproduction/run_isolated_component.py --component witness \
  --capsule /absolute/fresh/sources/witness/source-only-final-v1 \
  --environment /absolute/fresh/ENV8.json --out /absolute/fresh/witness --jobs 16
```

The fresh Witness pipeline explicitly uses `reproduce_v2.py` and `audit_replay_v2.py`. The preserved S1 `reproduce.py` remains historical and retains the old generated-audit root flag issue. See the additive `WITNESS_README_V2.md` beside this README.

For a bounded preparation test, add `--validate-only` to Adaptive or `--preflight` to the two other commands. A preflight proves no mathematical result. The portable launcher was actually preflighted for both components in normal, -O, and -OO modes; the original completed full component runs remain the authoritative proof evidence. It reuses the unchanged original namespace helper, read-only sources/compiler/public dependencies, fresh writable output, and offline execution. Full runs perform actual C execution and strict readback in all three Python optimization modes.

Then reproduce the complete mathematical scope using the extracted full-scope README. Its extension driver needs ENV8 only. Its primary driver takes the three completed component proof outputs:

```sh
cd /absolute/fresh/sources/audit/full-scope-source-only-v1
python3 reproduce.py --environment /absolute/fresh/ENV8.json --out /absolute/fresh/extensions --jobs 4
python3 reproduce_primary.py --environment /absolute/fresh/ENV8.json \
  --adaptive /absolute/fresh/adaptive/namespace/work/results \
  --primecover /absolute/fresh/primecover/work/proof \
  --witness /absolute/fresh/witness/work/proof --out /absolute/fresh/primary91
```

All 35 historical matched extension contexts were actually rebuilt and type/axiom checked. The new generic-only clean recipe was exercised for one context and preflighted across all source contexts. The new combined primary-complement driver was preflighted against all actual selected provider objects; its full 348-module combined rebuild was not additionally executed. These packaging checks do not replace or inflate the separately recorded completed source-cold and theorem-closure evidence.

## Optional Lake solution view

Run `python3 materialize.py` to extract the exact Witness proof source tree into ignored `proof/`. Then `lake build Solution` provides the usual solution-project view once the root project's pinned dependencies are prepared. The configuration declares 1,160 capsule modules and uses the four actual matching core modules from the root IEANTN project. The actual pinned Lake TOML loader and the existing-goal Solution wrapper were checked; a second complete Lake build was not run.

The application-source proofs use only the standard Lean axioms. The documented generic boundaries remain the pinned C23 compiler, unsigned word/runtime/ABI and CStdIO contracts, successful measured physical process I/O, and hardware. This does not claim a verified machine-code compiler or universal OS I/O success.
