# Reproduce all24 finalized numerical portfolios offline

Use `portable-final24-source-review-v4.tar.gz` and its `.RECEIPT.json`, plus the companion scripts in this directory. This final collection contains24 case plans and595 required top-level/nested routes. The immutable archive has7303 regular members (7300 manifest-listed source files plus three source-tree metadata files), with SHA-256 `1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a`. Its receipt SHA-256 is `6760619c22f46ce81163d8c7bc74cee6b3cb93dbd92b4720dda32bf6d2762670`.

The numerical replay needs no Codex installation, model account, credential, authentication file, network access or Lean installation. It regenerates the listed numerical computations and checks their exact output contracts. It does not supply source-first program verification, complete analytic Lean proofs, new verified IEANTN nodes, optimality or a general treatment advantage. Published finite computations that are only cited are still trusted at their stated source tier.

## Host prerequisites

Use x86-64 Linux with user namespaces, private mount/network namespaces, a running systemd user manager, and cgroup-v2 memory/CPU accounting. The pinned worker tools are CPython3.10.12 at `/usr/bin/python3.10`, GCC/G++11.4.0 (Ubuntu11.4.0-1ubuntu1~22.04.3), GNU assembler/linker, standard headers/libraries and libubsan where the exact job requests sanitization. The namespace template records every required generic tool/library path. The exact mpmath1.3.0 and sympy1.12 source trees and their manifests are vendored. The outer controller uses Python3.10 or newer and its standard library; it does not call a model. Changed compilers or libraries must be reported as changed environments, even if outputs match.

Production admission is unchanged: each case64GiB RAM,8CPUs,25GiB private scratch (24GiB work/root plus1GiB temporary), zero swap; at most6 registered plus pending scientific jobs, at most2 numerical jobs. The host preserves512GiB RAM and independently1TiB disk plus300GiB global scratch. CPU affinity must include the fixed eight-CPU slots in32–79. A laptop with fewer resources is not an equivalent host. Do not weaken these guards to run the package. Keep all other participants on one shared resource registry outside the source tree. On the original host, the existing registry is mandatory. No arbitrary numerical wall deadline, parameter reduction or cached-output shortcut is introduced.

## Verify and extract the complete immutable source

These steps execute no numerical program, compiler or scientific scope. Set `ARCHIVE` to the downloaded archive, `TREE` to a fresh absolute path whose parent exists, and `COMPANION` to this companion directory. Keep the source and execution directory private.

```sh
ARCHIVE=/absolute/path/portable-final24-source-review-v4.tar.gz
TREE=/absolute/path/private-new-source-tree
COMPANION=/absolute/path/reproduction
python3 -I -B "$COMPANION/verify_extract_final24.py" \
  --archive "$ARCHIVE" --receipt "$ARCHIVE.RECEIPT.json" --out "$TREE"
STUDY="$TREE/ieantn-d01-d02-repair-rerun-20261118"
python3 -I -B "$STUDY/scripts/portable_relocation_metadata_v2.py" \
  --source-root "$TREE" --config "$TREE/portable/RELOCATION_CONFIG.json" --check
```

The extractor rejects a changed archive, changed receipt, duplicate/path-traversal member, link, existing output directory, missing member or changed byte. Success checks all7303 member identities and all extracted bytes. The existing relocation checker then checks every manifest-listed source and reports24 ready and zero pending cases. Originals and embedded historical absolute paths are never edited: only their explicit source-root mapping changes.

## Emit every exact case command and workload

Choose one shared registry and a separate directory for new coordinator authority records. `NEW_AUTH` is a destination name; emitting this inventory does not create authority or start work.

```sh
REGISTRY=/absolute/path/shared-host-resource-registry
NEW_AUTH=/absolute/path/new-coordinator-authorities
python3 -I -B "$COMPANION/final24_command_inventory.py" \
  --source-root "$TREE" --registry "$REGISTRY" \
  --controller-python /usr/bin/python3 --new-authority-directory "$NEW_AUTH" \
  > FINAL24_COMMANDS_FOR_THIS_TREE.json
```

The JSON contains all24 literal metadata-check commands, all24 future run commands, all595 original top-level/nested argument lists, every exact source asset, parameters and output contracts. It reads and hashes sources only. `FINAL24_EXACT_REPRODUCTION_COMMAND_INVENTORY.json` is the saved inventory from our recorded final source root, not a claim that all24 were executed at that root. Generate a new inventory for your actual tree and registry.

Run a case's `literal_source_metadata_check_argv` as an argument list or copy its exact argument sequence into a shell. Create only the two shared evidence/resource parents if absent; each case leaf must remain absent. The positive status says metadata only, with zero scope/model calls. Validate the unchanged acceptance interface under normal Python, `-O` and `-OO`; the original numerical children always run normal Python with assertions enabled. The source preparation passed72 such case checks and three all24 original-workspace-file-open-denial controls. Those checks are not numerical runs.

## Run the complete offline pipeline without hand-editing JSON

Use the companion `reproduce_final24.py`, the shipped `ROOT_TEMPLATE_DELEGATION.json` and `ROOT_ORIGINAL_FINAL24_SOURCE_APPROVAL.json` together. The template is reviewed once by the study coordinator and pins this exact coordinator script, archive, configuration and unchanged executor. It preserves the original Root source/mathematical review as provenance. It delegates only creation of new local path/registry/output records and execution of these frozen numerical jobs. It performs no new mathematical review and permits no source, workload, output-contract or resource-guard change. No live Root session, Codex account, authentication or network service is required.

The `--check` command below validates the full source census and all selected original executor metadata without writing authority records or executing a compiler. `--prepare-only` writes exact source/job/execution records and a reviewable plan into a fresh directory outside the source tree; it starts no scientific job. The explicit `--run` command authorizes use of this host's resources and executes every selected complete case. There is no manual JSON creation step.

```sh
python3 -I -B "$COMPANION/reproduce_final24.py" \
  --source-root "$TREE" --registry "$REGISTRY" --authority-dir "$NEW_AUTH" \
  --cases all --check

python3 -I -B "$COMPANION/reproduce_final24.py" \
  --source-root "$TREE" --registry "$REGISTRY" --authority-dir "$NEW_AUTH" \
  --delegation "$COMPANION/ROOT_TEMPLATE_DELEGATION.json" \
  --cases all --prepare-only

python3 -I -B "$COMPANION/reproduce_final24.py" \
  --source-root "$TREE" --registry "$REGISTRY" --authority-dir "$NEW_AUTH" \
  --delegation "$COMPANION/ROOT_TEMPLATE_DELEGATION.json" \
  --cases all --run
```

Use `--cases FOLLOWUP-C022` for one full case or a comma-separated list of exact canonical case IDs. All24 cases are included by `--cases all`; no route or parameter is shortened. For a fresh extraction, `--run` may also create its records directly without a separate preparation step. On a source tree with previous attempted outputs, preserve that attempt and use a fresh extraction; no completed or interrupted case is overwritten or silently skipped.

The coordinator runs selected cases sequentially. It locks its shared registry coordinator file, checks the total/numerical admission counts under the existing allocations read lock before dispatch, and uses the unchanged registered executor for RAM/disk/CPU/zero-swap guards. Run one trusted scientific dispatcher for any other pending admissions on the host; do not race a separate unregistered launcher against this coordinator. Other registered jobs count toward the same maximum2 numerical/6 total policy. The numerical2 check is a consistent snapshot, not an atomic cross-controller reservation: the existing allocations lock must be released before f16 obtains its own exclusive reservation lock. Only the coordinator's own instances are serialized by its dispatch lock; use one trusted host dispatcher for all other pending admissions. The unchanged f16 resource guard enforces its global6/RAM/disk/CPU limits at reservation. An occupied or insufficient host fails closed rather than preempt another job or relax a guard.

Long full scans should use a detached systemd user driver so closing the terminal does not stop the controller. After the preparation command, run this equivalent driver command instead of the final foreground command above; set `RUN_LOG` to a fresh absolute file outside the source tree. Do not add a small ancestor `MemoryMax` or `RuntimeMaxSec`.

```sh
RUN_LOG=/absolute/path/final24-reproduction.log
systemd-run --user --collect --no-block --service-type=exec \
  --unit=ivy-final24-local-reproduction \
  --property=CPUQuota=100% --property=TasksMax=512 --property=KillMode=process \
  --property=StandardOutput=append:"$RUN_LOG" \
  --property=StandardError=append:"$RUN_LOG" \
  /usr/bin/python3 -I -B "$COMPANION/reproduce_final24.py" \
  --source-root "$TREE" --registry "$REGISTRY" --authority-dir "$NEW_AUTH" \
  --delegation "$COMPANION/ROOT_TEMPLATE_DELEGATION.json" \
  --cases all --run
```

For each case, the existing executor reserves resources, builds a fresh offline namespace, restores byte-checked inputs, compiles each required source, regenerates the whole numerical workloads, runs every verifier/consumer on the new data, compares complete output contracts, exports selected streams/artifacts, drains the scope and releases its lease. The coordinator then independently calls the unchanged full-output reader and verifies resource return0/errornull, inactive unit/PID0, absent cgroup and absent exact lease. Its final `ACTUAL_PIPELINE_COMPLETE.json` lists every actual case receipt. Missing completion or interruption remains incomplete; retain all partial files and do not use a weaker fallback or automatic overwrite. No source, archive or evidence is deleted.

## Whole-workload and qualification contracts

C007 retains all twelve modes, all824 parameters and seven whole surviving blocks plus all twelve exact artifact contracts; its lost historical combined stdout is not invented. C017 reproduces all27 original outcomes, including the recovered parser child failure1 with its shell parent0, then restores the corrected checker and supplies newly captured files to its final consumer. Its historical compound x-output is matched only at the documented complete prefix, not falsely as a whole combined stream. C023 reproduces all51 inherited children, eight compilers/groups, six whole new programs and five source checks, including the fresh same-q supplement. Both documented missing-path failures remain failures. C022 performs all22 original records and eight current wrapper children: full250million/default1million, full195729609429/26489122130/3584912847 finite ranges and17 whole-output matches. Its original wrong-cutoff ancillary failure1 is replayed at the exact historical ancillary.py path, then the exact corrected working source is restored; it precedes the corrected consumer of the newly generated Mertens output; all recorded compiler rows are0. No failing compilation is invented.

The final source collection separately includes C020's V2 qualification: the original unbounded1.03 assertion was false; the same original numerical cells establish only the closed30.75–191 interval. It does not import later C023 bounds into the old result. The authentic C023 CH2 source-only correction preserves the same q/constants/algorithm/endpoint premises. C022's optional general kernel allowance requires finite integral; its applied cases prove that condition. All three qualifications remain attached even when old numerical outputs match exactly. Full-RH comparisons remain conditional where their actual source antecedent is conditional. Main C018 results use Dusart density input; they are not density-free.

## Actual results and preservation

Our original runs occurred across several separately recorded /ryu and /data roots. They were not rerun in this final24 source tree. The final archive proves exact scientific job identity for the prior23 cases; the new C022 run alone uses the final24 actual tree. Keep each real run's own source root, execution authority and receipts. The first C022 attempt preserved20 matching full records but stopped on the saved-name traceback mismatch; it is not a successful replay. V4 binds the recovered public original command and private-working-copy overlay/restore, without normalizing stderr or changing numerical sources. The full corrected C022 retry passed all31 routes, all22 original outcomes and all17 fresh whole-output checks in1160.4412626698613s; its independent normal/-O/-OO output checks, drain/release and durable59-file record are pinned by evidence/C022_ACTUAL_DATA_FINAL24_PORTABLE_FULL_NUMERICAL_REPRODUCTION_AND_DRAIN_READBACK.json (SHA-256 6afdd4b5bee5898ddfb22a513e80ccfd93ad475fc7c19905fe4e79d24d999dd7). Across their separately recorded roots, all24 unique full cases are complete. A source collection or this README is not a new execution result.

Accept only `FINAL_REPRODUCTION_RECEIPT.json` with status `PASS_EXACT_NUMERICAL_REPRODUCTION_AND_ACTUAL_DRAIN`, exact whole-output verification, resource return0/errornull, drained scope, released lease, inactive unit/PID0 and absent cgroup/lease. Preserve full stdout/stderr and expected-failure histories, selected output manifest, compiled binaries/environment hashes, source/job/authority pins, wall/CPU time, OOM and scratch evidence in a durable hash-checked copy before cleanup. On kernel5.15 the actual `memory.peak` file was absent; sampled charged-RAM peaks are lower bounds and GNU time's per-process RSS is a different measurement. Do not label either as an exact aggregate peak.

Cleanup is a separate reviewed operation. Namespace tmpfs normally disappears only after full process/mount drain; this does not authorize deleting host source roots. Preview experiment-owned regenerable caches/scratch after regeneration and durable copies have been checked. Never remove original mathematical sources, locked inputs, accepted proofs/archives/certificates, unique receipts or another workspace. No deletion command is supplied here.

## Check the portable companion commands

After the fresh extraction above, the current companion CLI check verifies the accepted archive, emits all595 exact command routes, checks all24 coordinator source records and tests an invalid-receipt rejection in normal Python, `-O` and `-OO`. It disables site packages with `-S`. It starts no numerical job, compiler, scientific scope or model. Give `--out` a fresh directory whose parent already exists.

```sh
python3 -I -B "$COMPANION/check_final24_companions_v2.py" \
  --archive "$ARCHIVE" --receipt "$ARCHIVE.RECEIPT.json" \
  --source-root "$TREE" --registry "$REGISTRY" \
  --out /absolute/path/new-companion-check-output
```

Use the parameterized V2 checker. The historical V1 checker is retained as provenance and contains the obsolete preparation paths; it is not the current reproduction entry point. The accepted numerical coordinator, source extractor and frozen execution cores are unchanged.

## Rebuild the recorded result and resource ledger from the evidence bundle

This verifies preserved evidence without repeating the completed scientific computations. Reconstruct and extract the evidence bundle using its top-level README first. Set `BUNDLE` to that extracted root. The package's `PUBLIC_SOURCE_MAP.json` resolves the original execution-path identities to the exact downloaded bytes. The command below requires every one of2194 receipt/source references to use that map, verifies all1990 durable success files and keeps the failed first C022 attempt separate. `LEDGER_OUT` must be fresh and its parent must exist.

```sh
BUNDLE=/absolute/path/reconstructed-evidence-root
COMPANION="$BUNDLE/evidence/study/reproduction"
LEDGER_OUT=/absolute/path/new-ledger-output
python3 -I -B "$COMPANION/build_final24_actual_ledger.py" \
  --selection "$COMPANION/FINAL24_ACTUAL_RESULT_SELECTION.json" \
  --source-map "$BUNDLE/PUBLIC_SOURCE_MAP.json" \
  --public-root "$BUNDLE" --require-mapped --out "$LEDGER_OUT"
```

The output JSON and TSV preserve each actual source root, exact source/archive/job/receipt hashes, full command-route count, elapsed time, recorded host-output disk usage, sampled charged-RAM lower bound, separately captured GNU time CPU/RSS values, OOM observations, qualified mathematical status and drain/release evidence. Reserved RAM and scratch limits are not actual peaks; the exact aggregate memory and peak disk values remain unavailable. The three tested normal/optimized modes reproduced byte-identical ledgers from the mapped evidence with original-workspace file access denied. This does not rescore original outcomes or constitute source-first PV or a full analytic Lean proof.

## Case and route census

| Case | Canonical stage | Top | Nested | Whole |
|---|---|---:|---:|---:|
| FOLLOWUP-C001 | FRESH-R1-D01-PNT | 26 | 4 | 30 |
| FOLLOWUP-C002 | FRESH-R1-D01-IEANTN | 13 | 2 | 15 |
| FOLLOWUP-C003 | FRESH-R1-D01-NL | 16 | 0 | 16 |
| FOLLOWUP-C004 | FRESH-R2-D01-IEANTN | 11 | 1 | 12 |
| FOLLOWUP-C005 | FRESH-R2-D01-NL | 2 | 6 | 8 |
| FOLLOWUP-C006 | FRESH-R2-D01-PNT | 2 | 10 | 12 |
| FOLLOWUP-C007 | FRESH-R1-D02-PNT | 25 | 4 | 29 |
| FOLLOWUP-C008 | FRESH-R1-D02-IEANTN | 18 | 2 | 20 |
| FOLLOWUP-C009 | FRESH-R1-D02-NL | 33 | 0 | 33 |
| FOLLOWUP-C010 | CONTROL-R1-D02-PNT | 6 | 0 | 6 |
| FOLLOWUP-C011 | CONTROL-R1-D02-IEANTN | 9 | 0 | 9 |
| FOLLOWUP-C012 | CONTROL-R1-D02-NL | 11 | 0 | 11 |
| FOLLOWUP-C013 | FRESH-R2-D02-IEANTN | 13 | 0 | 13 |
| FOLLOWUP-C014 | FRESH-R2-D02-NL | 3 | 14 | 17 |
| FOLLOWUP-C015 | FRESH-R2-D02-PNT | 5 | 10 | 15 |
| FOLLOWUP-C016 | CONTROL-R2-D02-IEANTN | 40 | 7 | 47 |
| FOLLOWUP-C017 | CONTROL-R2-D02-NL | 1 | 27 | 28 |
| FOLLOWUP-C018 | CONTROL-R2-D02-PNT | 1 | 22 | 23 |
| FOLLOWUP-C019 | LEGACY-D01-PNT | 21 | 0 | 21 |
| FOLLOWUP-C020 | LEGACY-D01-IEANTN | 64 | 2 | 66 |
| FOLLOWUP-C021 | LEGACY-D01-NL | 20 | 0 | 20 |
| FOLLOWUP-C022 | LEGACY-D02-PNT | 1 | 30 | 31 |
| FOLLOWUP-C023 | LEGACY-D02-IEANTN | 1 | 78 | 79 |
| FOLLOWUP-C024 | LEGACY-D02-NL | 34 | 0 | 34 |

Counts describe required command routes, not independent experiments, strict issue counts or new mathematical discoveries.
