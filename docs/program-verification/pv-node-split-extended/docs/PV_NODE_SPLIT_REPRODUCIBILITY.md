# Reproducibility

Everything below ran on one host between 2026-11-06 05:59 and 07:30 UTC. Paths are relative to
`agentB/` unless they start with `pv8_study/`.

## 1. Snapshots

| Name | Repository | Ref | SHA | Role |
|---|---|---|---|---|
| upstream | `teorth/IEANTN` | `main` | `466b41b28ecc224398cf53a99c5fe9618131398b` (2026-11-02) | policy, tooling, leaf-set guard; base of the remedy patch |
| upstream base of the PoC | `teorth/IEANTN` | — | `ef21db9` | leaf-set comparison |
| owner fork | `hs-chae/IEANTN_test` | `main` / `QRH_phase2` / `qrh-2pv` | `2a10e72` / `d85631a` / `ce12611` | census only |
| PoC | `hs-chae/IEANTN_test` | `qrh-2pv_B` | `3280a3c3e0268578f0dbd4a0d8385f4d36877327` | base of every experiment |
| first study | local | `agentB/pv-node-split` / `-exp` | `5b59409` / `16cddb6` | audited, not reused |
| Agent A, newest | local, read only | `poc/full-network-winners-a` | `091288df6ea333bf3fc5654493d659dbfae21498` (2026-11-06 05:50 UTC) | census, casebook C3 |
| Agent A, earlier | local, read only | `poc/three-stage-recovery` / `poc/maximal-pv-evolution-a` / `poc/scoped-winner-a` | `b9b2e3c` / `00128be` / `e0c1ceb` | casebook C3 |

`git ls-remote` at the start: upstream `main` and the fork's branches unchanged from the refs above.

**Disposable worktrees** (all local branches with no upstream; created by `pv8_study/scripts/setup_world.sh` or
`git worktree add`; never pushed):

| Worktree | Branch | Commits | Purpose |
|---|---|---|---|
| `pv8_wtA` | `agentB/pv8-A` | `1f78d30` (M1-A), `26dc23d` (M2-A), `6782ca1` (M3-A), `4b5b867` (M3-A fix + fingerprints) | layout A of the three pairs; mutations |
| `pv8_wtB` | `agentB/pv8-B` | `a23bc28` (M1-B), `5ceee2e` (M2-B), `26bc2c5` (fingerprints) | layout B; mutations |
| `pv8_wtC` | `agentB/pv8-C` | none (`3280a3c`) | YAML/Python-only audits: leaf sets, the one-line fix (reverted), blocker probe (deleted) |
| `pv8_wtU` | `agentB/pv8-U` | `1acc32e` on `466b41b` | the `solution_drift` remedy and its tests |

## 2. Environment

| Item | Value |
|---|---|
| Host | `narnia`, 128 cores, 1.5 TB RAM, Linux 5.15 |
| Lean / Lake | `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c`), Lake `5.0.0-src+6a10ac8` |
| Mathlib | `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` (cache shared from `agentB/network/.lake/packages`) |
| Python | 3.10.12, PyYAML 6.0.3 (`agentB/tools` venv); `unittest` (no pytest) |
| gcc | 11.4.0 (Ubuntu 22.04) |
| Comparator, nanoda, lean4export, landrun | **not installed** (`which` and a depth-6 search of `/` found none) |
| Snapshot files | `pv8_study/evidence/ENV_snapshot_start.txt` (+ `_end.txt`) |

## 3. Resource limits actually applied

- One Lean build at a time. Never two roots sharing a package concurrently.
- Every build through `pv8_study/scripts/guarded_build.sh`: GNU `time -v`; a sampler every 2 s records the
  number of `lean` processes in the build's process group, their summed RSS, `MemAvailable` and free disk; it
  kills the group if `MemAvailable` < 300 GB or free disk < 60 GB. The guard never fired.
- Lake 5 has no jobs flag (`lake build --help`), so per-build parallelism was not capped. Observed peaks: 56
  concurrent `lean` processes and about 99 GB summed RSS (core build); 14 processes and 40 GB (Table 4
  solution); largest single process 26 GB (`Table4Evolution.KernelOnly`).
- Minimum `MemAvailable` seen during any build: 1,054 GB. Disk used by the four worktrees: 3.0 GB (A 1.5 GB, B 1.5 GB, C 28 MB, U 14 MB); `/ryu` free 471 GB → 466 GB.
- Not run: anything heavier than the Table 4 kernel route; a cold build of `CH2.v6`'s density certificates (not in
  any closure used here; static closures and dry runs confirmed it).

## 4. Commands

From `agentB/` (Python = `tools/bin/python`):

```bash
# Phase 1: census, rules, leaf sets, policy checks
python pv8_study/scripts/census.py network <ref> pv8_study/evidence/census/census_<ref>.json        # 7 refs
python pv8_study/scripts/rules_audit.py network origin/qrh-2pv_B pv8_study/evidence/census/census_origin_qrh-2pv_B.json \
       pv8_study/evidence/rules/rules_3280a3c_checked.json pv8_study/evidence/axioms/consumer_axioms_checked.json
pv8_study/scripts/print_axioms.sh network/Solutions/<Node> <module> <decl>...                        # consumer axioms
(cd pv8_wtC && python scripts/ieantn_upstream.py diff --base ef21db9)                                  # leaf-set guard
(cd pv8_wtC && python ../pv8_study/scripts/leafsets.py ../pv8_study/evidence/leafset/L5_leafsets.json)
(cd pv8_wtC && python scripts/ieantn.py check-closure; python scripts/ieantn_upstream.py check-closure) # also graph/pins/receipts
# Matched experiments
pv8_study/scripts/setup_world.sh A; pv8_study/scripts/setup_world.sh B
(cd pv8_wt<X> && python scripts/ieantn.py new-node <Family> --kind <kind>)
python pv8_study/scripts/mk_layouts.py pv8_wt<X> <A|B> <T4|RAM|SHR>
(cd pv8_wt<X> && python scripts/ieantn.py gen-challenges)
pv8_study/scripts/guarded_build.sh <log> pv8_wt<X> lake build;  (cd pv8_wt<X> && python scripts/ieantn.py fingerprint)
pv8_study/scripts/guarded_build.sh <log> pv8_wt<X>/Solutions/<Node> lake build                       # cold, then warm
pv8_study/scripts/build_round2.sh; pv8_study/scripts/build_round2b.sh
pv8_study/scripts/preview.sh pv8_wt<X>/Solutions/<Node> <Node> <theorem> <out-prefix>                 # NODES.md L323-340
python pv8_study/scripts/layout_metrics.py pv8_wt<X> <base> <head> <paths>... --census-base ... --census-head ...
(cd pv8_wt<X> && python ../pv8_study/scripts/trace_leaves.py <commit> <out.json> <conclusion>...)
python pv8_study/scripts/import_closure.py pv8_wt<X>/Solutions/<Node> <root-module>
# Mutations
pv8_study/scripts/run_mutations.sh MT10_Bprime_whitespace MT10b_Bprime_literal MT6_route MT11_shared_closure \
    MT1_whitespace MT2_comment MT3_literal MT8_crossproject_lean MT9_A_output MT4_input_statement MT5_target
python pv8_study/scripts/mutation_table.py
pv8_study/scripts/mt7_compiler.sh pv8_study/evidence/mt7_compiler
# Remedy
(cd pv8_wtU && python -m unittest tests.test_solution_drift_path_deps -v; python -m unittest discover -s tests -q)
```

## 5. Logs and outputs (all exist; nothing listed here is reconstructed)

| What | Where |
|---|---|
| census of 7 snapshots | `evidence/census/census_*.json` |
| rule audit | `evidence/rules/rules_3280a3c{,_checked}.{txt,json}`, `rules_agentA_091288d.*` |
| consumer axioms (17 theorems) and the shadowing demo | `evidence/axioms/consumer_*.txt`, `shadowing_demo_FKS2.v4_lake_env.txt` |
| leaf-set guard | `evidence/leafset/L1`–`L5` |
| policy checks | `evidence/policy/{poc,upstream}_check-*.log` |
| blocker probe | `evidence/blocker/B1_check_closure.log`, `B2_upstream_check_closure.log` |
| builds | `evidence/builds/*.log` and `*.log.summary` (one line per build) |
| previews and axioms of the layouts | `evidence/preview/*.out`, `evidence/axioms/M{1,2,3}_*.txt` |
| structural metrics | `evidence/metrics/*` |
| trust leaves | `evidence/trust/leaves_world{A,B}.json` |
| static closures | `evidence/closures/*.json` |
| mutation records | `evidence/mutations/<id>_<worktree>/record.json` with edit/restore logs; `DIGEST.json` |
| compiler flags | `evidence/mt7_compiler/MT7_results.txt` |
| remedy | `evidence/remedy/` (patch, tests before/after, full suite, input-file audit) |
| first study logs | `evidence/pv7/` (reused only where named) |

## 6. Status of the claims that were *not* fully checked

| Claim | Status | Why |
|---|---|---|
| Any layout is Comparator-accepted | **UNVERIFIED** | no Comparator on the host; only the documented local preview ran |
| A receipt would be BROKEN/green after a statement mutation | **NEWLY TESTED, in memory** | `assess` run on receipt dicts built from committed fingerprints; no receipt file written |
| Fresh per-node verification cost | **STATIC COUNT** | import closures from source; fresh builds of each consumer alone were not run |
| The 11-04 `DDExpansionSolution` fan-out to `CH2.v6` density certificates | **NOT REPRODUCED** | at `3280a3c` the closure has 112 modules and no `CertData`; the earlier fan-out came through an import not identified here |
| Agent A's coefficients and native counts | **SOURCE-GROUNDED** | read from Agent A's documents at each commit; not rebuilt |
| Upstream behaviour of a program-verified solution | **COUNTERFACTUAL** | upstream has no `include_str` user (0 files) |
