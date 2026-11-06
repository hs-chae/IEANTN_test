# PV node-split study, extended: index

Agent B, 2026-11-06. Continuation and adversarial audit of the first study (`agentB/pv-node-split` `5b59409`,
now [`../PV_NODE_SPLIT_DECISION_REPORT.md`](../PV_NODE_SPLIT_DECISION_REPORT.md) and its companions).
All experiments ran in disposable local worktrees whose branches were never pushed; `patches/` holds their commits.
The study itself was committed to `qrh-2pv_B` at the owner's request on 2026-11-06. Its scripts and the commands in
the reproducibility document assume the original workspace, where this repository is cloned as `network/` next to
`pv8_study/` (this directory) and the worktrees `pv8_wtA`, `pv8_wtB`, `pv8_wtC`, `pv8_wtU`.

## Deliverables (`docs/`)

| # | File | What it is |
|---|---|---|
| 1 | [PV_NODE_SPLIT_EXTENDED_STUDY.md](docs/PV_NODE_SPLIT_EXTENDED_STUDY.md) | verdict, what changed since the first study, numbered findings, claim ledger, answers to the eight stop-rule questions |
| 2 | [PV_NODE_SPLIT_CASEBOOK.md](docs/PV_NODE_SPLIT_CASEBOOK.md) | ten real cases C1–C10; deep traces C1, C2, C3, C4, C7 |
| 3 | [PV_NODE_SPLIT_MATCHED_EXPERIMENTS.md](docs/PV_NODE_SPLIT_MATCHED_EXPERIMENTS.md) | three matched A/B builds: Table 4 (M1), Ramanujan A→B′ (M2), a shared provider with two consumer families (M3) |
| 4 | [PV_NODE_SPLIT_PROVENANCE_MATRIX.csv](docs/PV_NODE_SPLIT_PROVENANCE_MATRIX.csv) | per-stage source hashes, contracts, proof roots, native facts, official and local status, consumers, change sensitivity, trust leaves |
| 5 | [PV_NODE_SPLIT_MUTATION_TESTS.md](docs/PV_NODE_SPLIT_MUTATION_TESTS.md) | controlled source/input/statement/route mutations, expected versus observed, restoration evidence |
| 6 | [PV_NODE_SPLIT_RULE_STRESS_TEST.md](docs/PV_NODE_SPLIT_RULE_STRESS_TEST.md) | counterexamples to R1–R4 and the shorter rule N1–N3 |
| 7 | [PV_NODE_SPLIT_REPRODUCIBILITY.md](docs/PV_NODE_SPLIT_REPRODUCIBILITY.md) | SHAs, environment, resource limits, commands, logs, what remains unverified |
| 8 | [PV_NODE_SPLIT_MAINTAINER_DECISION.md](docs/PV_NODE_SPLIT_MAINTAINER_DECISION.md) | four owner decisions, each against a do-nothing baseline |
| 9 | [PV_NODE_SPLIT_EXTENDED_SUMMARY.html](docs/PV_NODE_SPLIT_EXTENDED_SUMMARY.html) | short standalone summary for a decision-maker |

## Evidence (`evidence/`)

| Directory / file | Contents |
|---|---|
| `ENV_snapshot_*.txt` | refs, toolchain, host resources, Comparator availability |
| `OLD_CLAIMS.md` | the first study's claims: reproduced, corrected or qualified |
| `census/` | graph census of seven snapshots (upstream, PoC bases and branches, Agent A) |
| `rules/` | promotion-criteria audit per provider, with consumer evidence |
| `axioms/` | `#print axioms` outputs (consumers, matched layouts), the `Solution`-shadowing demonstration |
| `leafset/` | the leaf-set guard: upstream `diff`, leaf sets at six graph states, the one-line fix |
| `policy/` | `check-closure`, `check-graph`, `check-pins`, `check-receipts` under both tool versions |
| `blocker/` | the solution-type import probe (C3) |
| `builds/` | every build log with its `guarded_build.sh` summary line |
| `metrics/` | files/lines/graph deltas of each layout |
| `preview/` | NODES.md L323–340 local previews (type and axioms) |
| `trust/` | transitive unproved leaves per layout |
| `closures/` | static import closures |
| `mutation_specs/`, `mutations/` | mutation specifications and per-run records (`record.json`) with logs |
| `mt7_compiler/` | compiler-flag experiment on the five selected C programs |
| `remedy/` | the `solution_drift` patch, its tests, results before and after |

## Patches (`patches/`)

`layoutA/` and `layoutB/`: the experiment commits of the two disposable worktrees (`git format-patch 3280a3c..`),
applicable to `qrh-2pv_B` `3280a3c` with `git am`; `remedy/`: the `solution_drift` patch on upstream `466b41b`.
None of them is proposed for merging.

## Rendered (`rendered/`)

Not committed: the repository ignores `*.pdf`. `scripts/render_all.sh` regenerates the HTML and PDF copies.

## Scripts (`scripts/`)

`census.py`, `rules_audit.py`, `leafsets.py`, `trace_leaves.py`, `import_closure.py`, `layout_metrics.py`,
`mk_layouts.py`, `setup_world.sh`, `guarded_build.sh`, `build_round2.sh`, `preview.sh`, `print_axioms.sh`,
`build_round2b.sh`, `mutate.py`, `run_mutations.sh`, `mutation_table.py`, `mt7_compiler.sh`, `r2_input_file_test.sh`,
`render_all.sh`, `env_snapshot.sh`. None writes to an owner branch.

## Incomplete items

See the claim ledger in the extended study (§6) and `docs/PV_NODE_SPLIT_REPRODUCIBILITY.md` §6.
