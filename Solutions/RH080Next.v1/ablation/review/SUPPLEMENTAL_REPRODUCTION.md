# Exact locked exposure payloads: supplementary proof reproduction

There were16 original matched sessions. Three were admissible;13 stopped at the generated-output admission ceiling. All original primary outcomes remain unchanged. The13 later proof replays are supplementary, offline, use zero new model inference, and establish no causal advantage of network or source-first PV exposure.

`common` mathematical inputs were the same169 selected application modules in every arm. This is the exact experimental selection, not an exhaustive source-attribution census. The raw witness caps and executable C bytes were shared. The mathematical reading distinguishes rounded attained coefficients, unattained raw limiting caps, extra hypotheses and written specializations. Source-first PV adds provenance; these transfer payloads do not verify a new external numerical program.

## Preserved evidence

`supplemental_evidence_v1/locked_payloads` contains all13 exact original LOCK files and every listed payload:42 files, including15 Lean files. No file was replaced with a later stronger draft. Source/declaration/line identities are retained. Two exports had different Lean bytes from their locks; exact original snapshots or recorded literal write operations recovered the locked files. In particular, the8,329-byte locked D/r0 rank file is the fixed-cap draft, not the later adaptive implementation. Recovery provenance and failed attempts remain evidence.

`supplemental_evidence_v1/evidence/ALL16_MATHEMATICAL_INTERPRETATION.json` records exact strongest theorem types, hypotheses, endpoint/rank limits and source hashes for every original session. `REPORT_EXPOSURE_ROWS.json` is the compact report adapter; `ALL16_RESULTS.csv` is the corresponding table. Full-module exports count generated auxiliary constants too: they are not counts of new research theorems, and compilation counts are not mathematical strength scores.

The separate portable source-cold run is completed and independently checked:169 common sources,15 exact locked sources and15 full-module audit modules,199 real compiler calls,2678.76seconds. Actual child peak RSS was47.765GiB; sampled aggregate RSS reached98.684GiB (not an exact aggregate peak). Its retained accepted run uses1,210,064,896bytes. An independent observer captured absolute owned-cgroup counters at the completed RESULT:oom=0 andoom_kill=0;oom_group_kill was not available, and no initial-counter delta was invented. All1,235 exported declarations have identical types, axiom sets and direct dependencies between the original-runtime and portable replays. These results and all logs/receipts are in `portable_clean_evidence_v1`; its `REPORT_EXPOSURE_ROWS_V2.json` adds the new proof-replay status without changing primary outcomes or mathematical claims.

## Portable clean mathematical proof replay

This route needs this pinned repository and compiled *generic* dependencies only. It does not need the original offline executor, runtime archive, SDK, credentials or any model. It is separate from the original matched isolated study. Same-named submitted modules are compiled into separate per-trial source/object directories; original Lean bytes, namespaces and imports remain untouched.

Install the pinned Linux Lean4.34.0-rc2 compiler and Mathlib commit71a80585ee495fc24472fd0eaffc89d94e4fd8d6 with its seven dependencies. Their exact commits and compiler hash are enforced by the existing public context creator:

```sh
python3 Solutions/RH080Next.v1/primal/create_copy_context.py \
  --compiler /path/to/lean-4.34.0-rc2/bin/lean \
  --mathlib /path/to/mathlib --output /fresh/generic_context.json
python3 Solutions/RH080Next.v1/ablation/review/reproduce_clean_proofs.py \
  --context /fresh/generic_context.json --out /fresh/clean-exposure-proofs \
  --workers 4 --memory-gib 64 --scratch-root /owned/campaign --scratch-stop-gib 290
```

`COMMON169_SOURCE_INPUTS.json` pins the exact169 original-common source modules by repository-relative path, module identity, import list and SHA256. All151MB of these sources already exist in the repository; the894MB flat statement dump need not be stored again. The replay copies and rebuilds all169 modules from source with only the pinned generic libraries available, then compiles all15 locked Lean modules and15 independent full-module type/axiom audits. It fails on changed source, unknown imports, nonstandard axioms, compiler diagnostics, missing proof objects or incomplete coverage. The only allowed proof axioms are propext, Classical.choice and Quot.sound. No original application proof object is reused.

Run within an owned supervisor with aggregate memory at most300GiB. The script admits RAM and disk separately, preserves256GiB host RAM, uses four64GiB compiler limits, and stops its own children at290GiB total campaign scratch. These are additional proof runs, not retroactive changes to original trial budgets. The final result preserves commands, compiler/source/object/log hashes, actual child peak RSS, sampled group RSS, elapsed time and failure status. Sampled group RSS is not an exact peak; absent final cgroup counters are not reported as zero OOM counters.

After that run has produced its completed RESULT, check every actual compiler route and test the completion gate:

```sh
python3 Solutions/RH080Next.v1/ablation/review/check_clean_proofs.py \
  --run /fresh/clean-exposure-proofs --output /fresh/clean-accepted.json
python3 Solutions/RH080Next.v1/ablation/review/test_clean_proofs.py \
  --run /fresh/clean-exposure-proofs --out /fresh/clean-proof-controls
python3 Solutions/RH080Next.v1/ablation/review/compare_clean_exports.py \
  --clean /fresh/clean-exposure-proofs --output /fresh/export-equivalence.json
```

## Check the sealed evidence

```sh
python3 Solutions/RH080Next.v1/ablation/review/verify_supplemental_bundle.py \
  --bundle Solutions/RH080Next.v1/ablation/review/supplemental_evidence_v1 \
  --output /fresh/bundle-check.json
```

The actual acceptance CLI was tested normal, `-O` and `-OO`, with wrong runtime, missing second source file, nonstandard axiom and attempted primary reclassification controls. Receipt evidence is under `supplemental_evidence_v1/evidence`. Validators use explicit checks; Python optimization must not disable acceptance.

`supplemental_attempts_v1` preserves the failed audit pilot, metadata rejection logs and executed superseded scaffolds. Those harness failures are not mathematical failures and are not silently overwritten by the accepted later replay.

The exact8,329-byte locked D/r0 file can also be recovered without a private transcript or executing the recorded researcher commands: `replay_minimal_recovery.py --output /fresh/recovery-check.json` applies only the whitelisted string-data interpreter to the three preserved original tool-write records. This was checked normal, `-O` and `-OO`.

## Faithful original-runtime supplementary replay

This separate route preserves the original sandbox mechanism and exact runtime identity23c22ffbd40173ce027d945da1be3141def8e58103b7622f2ffd7dc3999c436a. Every one of the13 replays uses that same richest ORIGINAL D runtime,64GiB RAM,12GiB scratch,4CPUs and1200seconds. It requires the original runtime mount trees/manifests and pinned offline executor listed in `OFFLINE_DEPENDENCIES.json`; the small sealed directory alone is not the full runtime archive. `prepare_exposure.py` and `prepare_runtimes.py` document regeneration of those support trees from the two pinned accepted Gaussian/population source banks. The archive must retain the specified source and dependency pins, not silently use richer later proof support.

After restoring those original experiment paths and exact mount identities:

```sh
python3 Solutions/RH080Next.v1/ablation/review/recover_supplemental.py
python3 Solutions/RH080Next.v1/ablation/review/run_all_supplemental.py \
  --out /data/ivy-rh080-next-20261125/exposure-supplemental-replay-v2/FRESH_REPLAY \
  --workers 2
python3 Solutions/RH080Next.v1/ablation/review/test_supplemental.py \
  --runs /data/ivy-rh080-next-20261125/exposure-supplemental-replay-v2/FRESH_REPLAY/RUNS.json \
  --out /fresh/acceptance-controls
```

The historical recovery script deliberately uses the fixed archival output path `/data/ivy-rh080-next-20261125/exposure-supplemental-recovery-v1`; run it only in a clean restoration where that path does not exist, or reuse its already verified recovery result. Use fresh coordinator and validator output paths; all historical runs and failed harness attempts remain immutable. The new coordinator replays all13 rows rather than depending on an old pilot. `recover_supplemental.py` hashes every Lean and non-Lean locked artifact; the special write-trace recovery interprets only whitelisted literal data operations, without executing researcher Python on the host. Existing original3 review helpers and original outcomes are unchanged.

The all16 mathematical reading can be regenerated from the accepted archival review paths with `analyze_all16.py --out /fresh/interpretation.json`. This script carries an explicit human interpretation of the exact types; it does not infer mathematical success or novelty from proof counts. Do not replace its manual premise/endpoint judgments with a compile-only gate.
