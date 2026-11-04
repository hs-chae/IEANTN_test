# Test and replay log: structural program-verification upgrade

## Pins and caches

- **Lean.** `leanprover/lean4:v4.34.0-rc2` (Lake 5.0.0) everywhere.
- **Mathlib.** `71a80585ee49`, fetched with `lake exe cache get`. Every solution project shares the
  worktree's `.lake/packages` through a symlink, and every manifest pins the same Mathlib.
- **Build state.** All IEANTN and solution modules were compiled in this worktree. No cold Mathlib
  build is claimed.
- **Branch.** `agentB/pv-structural`, from `3388918` (`agentB/native-assisted`). Commits are listed
  in `FINAL_IEANTN_PV_UPGRADE_REPORT.md`. Nothing pushed.

## Builds

| Project | Command | Result |
|---|---|---|
| core | `lake build` | OK, 4129 jobs. The new nodes' `Conclusions` and `Challenge` compile. |
| `Solutions/ProgramVerification` | `lake build PVCore PVRamanujan` | OK |
| `Solutions/RamanujanNumerics.v3` | `lake build Solution RamanujanBudget` | OK |
| `Solutions/RamanujanGap.v3` | `lake build Solution RamanujanGapReplay` | OK |
| `pilots/pv-replay` | `lake build PVReplay` | OK |
| **stopped** | `RamanujanGap.v3` replay importing `DDExpansionSolution` | The closure compiles CH2.v6 density certificates: about 120 parallel Lean jobs at about 10 GB each on a shared machine. Stopped and every process killed. The replay now keeps the π input as a premise. |

## Repository checks (at `9b748db`)

| Check | Result |
|---|---|
| `ieantn.py fingerprint --check` | 0: no statement fingerprint moved. The two new nodes have their own. |
| `ieantn.py gen-challenges --check` | 0 |
| `ieantn.py check` | Exit 1 only for the 49 inherited receipt-provenance items (`teorth/IEANTN` against `hs-chae/IEANTN_test`), as before. The local evidence check passes. New warnings: only the two new nodes' missing issue numbers and stale CI-owned pages, the same kinds the v2 nodes have. |
| `python -m unittest discover -s tests` | 350 OK: 346 before, plus 4 page-row tests |
| Freeze manifests | forward 30/30, Table 4 19/19 byte-identical |
| Node pages, `551f552` → now | 13 existing pages differ, each explained: 11 attested nodes; `DudekPlattNumerics.v5`, whose "Assumed by" row now lists `RamanujanGap.v3`; and the index. There are 2 new pages. The others are byte-identical. |

## Lean-level tests

| Test | Expected | Observed |
|---|---|---|
| `pilots/pv-replay/tests/TokenMatch.lean` | the generic renderer reproduces the 6 existing selected files; 2 negatives fail | 6 `true`, 2 `false` |
| `pilots/pv-replay/tests/Axioms.lean`, `AxiomsPilot.lean` | shared theorems use the standard axioms only; each instance adds only its certificate | as expected (table below) |
| `pilots/pv-replay/tests/LinkMismatch.lean` | feeding B′ the deviation 0.0913 instead of A's certified 0.0914 does not elaborate | `Type mismatch: … has type ↑NewB.M = 120 + ↑NewA.bound but is expected to have type ↑NewB.M = 120 + ↑(913 / 10000)` |
| Lake `input_file` + `needs`, scratch project | with `needs`, a changed file reruns and recompiles; without it, the stale result is replayed | as expected (`agentB/evidence/pv3`) |

## Axiom closures (`#print axioms`)

| Theorem | Axioms beyond `propext`, `Classical.choice`, `Quot.sound` |
|---|---|
| `PVCore.certified`, `PVCore.le_bound_of_check`, `PVCore.bound_le_of_check`, `PVRamanujan.budget_of_check` | none |
| `PVRamanujan.V1/V2/OldGrouped.epsilon_budget`, `UpdatedGrouped.epsilon_budget_fixed_target` | its own `certificate` (1 each) |
| `RamanujanNumerics.v3.challenge_epsilon_budget` | `RamanujanNumerics.v3.Provider.certificate` |
| `RamanujanGap.v3.challenge_loss_bound`, `challenge_gap_lower_bound` | none |
| `RamanujanGap.v3.gap_from_pi`, `ramanujan_401_second_route` | `RamanujanNumerics.v3.Provider.certificate` |
| `PVTable4.QRH.qrh_pi` | `FKS2Table4.analytic_checks`, `input_certificate`, `scaled_cells_upper` (existing analytic enclosures), `PVTable4.QRH.certificate` |
| `PVTable4.Old.old_pi` | `FKS2Pair.Old.boundary_checks`, `enclosure_checks`, `exp_checks` (existing), `PVTable4.Old.certificate` |
| `PVPilot.Updated.gap_exceeds_leading` | `certificateA`, `certificateB` (2; the original chain has 13) |

Each listed name is a `…._native.native_decide.ax_1_1` axiom. Every one is audited by the local
gate: owning theorem, module, source file and SHA256, the `native_decide` token at its recorded
range, the decided proposition, and the count of trusted library implementations.

## Local gate

All 25 attestations pass, all on a clean tree. The 16 earlier endpoints were re-run in this task at `9b748db`, with the same methods and native-fact counts as before. The 9 new ones ran at `da75940`. `RamanujanGap.v3.ramanujan` was attested and then removed together with its conclusion, a duplicate of `DudekPlatt.v5.ramanujan_401`.

| Endpoint | Status | Method | Native facts | Checked at (clean tree) |
|---|---|---|---|---|
| `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` | passed | lean-verified-program | 1 | `9b748db` |
| `@pilot.CalibrationPilot.NewChain.new_chain` | passed | lean-verified-program | 13 | `9b748db` |
| `@pv.PVPilot.Updated.gap_exceeds_leading` | passed | lean-verified-program | 2 | `da75940` |
| `@pv.PVRamanujan.OldGrouped.epsilon_budget` | passed | lean-verified-program | 1 | `da75940` |
| `@pv.PVRamanujan.V1.epsilon_budget` | passed | lean-verified-program | 1 | `da75940` |
| `@pv.PVRamanujan.V2.epsilon_budget` | passed | lean-verified-program | 1 | `da75940` |
| `@pv.PVTable4.Old.old_pi` | passed | lean-verified-program | 4 | `da75940` |
| `@pv.PVTable4.QRH.qrh_pi` | passed | lean-verified-program | 4 | `da75940` |
| `@solution.FKS2Pair.assembled` | passed | lean-verified-program | 16 | `9b748db` |
| `@solution.ForwardRamanujan.forward` | passed | lean-verified-program | 12 | `9b748db` |
| `FKS2.v5.updated_theta` | passed | not-program-verified | 0 | `9b748db` |
| `FKS2.v9.qrh_absolute_pi` | passed | not-program-verified | 0 | `9b748db` |
| `FKS2Numerics.v2.nu_asymp_e30_le` | passed | not-program-verified | 8 | `9b748db` |
| `FKS2Numerics.v3.baseline_bound` | passed | lean-verified-program | 8 | `9b748db` |
| `FKS2Numerics.v3.calibration_bound` | passed | not-program-verified | 8 | `9b748db` |
| `FKS2Numerics.v4.updated_bound` | passed | lean-verified-program | 12 | `9b748db` |
| `FKS2Numerics.v5.numerical_pi` | passed | lean-verified-program | 7 | `9b748db` |
| `FKS2Numerics.v6.old_pi` | passed | lean-verified-program | 8 | `9b748db` |
| `FKS2Numerics.v7.qrh_pi` | passed | lean-verified-program | 8 | `9b748db` |
| `RamanujanGap.v2.loss_bound` | passed | not-program-verified | 0 | `9b748db` |
| `RamanujanGap.v3.gap_lower_bound` | passed | not-program-verified | 0 | `da75940` |
| `RamanujanGap.v3.loss_bound` | passed | not-program-verified | 0 | `da75940` |
| `RamanujanNumerics.v1.epsilon_budget` | passed | lean-verified-program | 6 | `9b748db` |
| `RamanujanNumerics.v2.epsilon_budget` | passed | lean-verified-program | 6 | `9b748db` |
| `RamanujanNumerics.v3.epsilon_budget` | passed | lean-verified-program | 1 | `da75940` |

## Controls (`scripts/native_assisted/controls_pv.py`, scratch copy; repository tree hash unchanged)

| # | Mutation or fixture | Expected | Observed |
|---|---|---|---|
| A | changed literal in `c/budget.c`, generated lakefile | Lake reruns `selected_source`; certificate fails | rebuilt; build fails at the certificate |
| B | same change, `needs` removed | Lake replays the stale build; the gate's S check catches it | build rc 0 (stale); S fails |
| C | changed literal in the Lean data module only | certificate fails (token mismatch) | fails |
| D | scale 4097 in both files | certificate fails (budget exceeded) | fails |
| E | first entry dropped from both files | certificate fails (enclosure) | fails |
| F | offset 300 in both files: negative intermediate | certificate fails (outside the certified binary64 range) | fails |
| G | coefficient 118 in data, C file and certificate | certificate passes; the node statement (119) rejects it | first error inside `epsilon_budget`, after the certificate |
| H | certificate replaced by `sorry` | gate fails | failed (`sorryAx`) |
| I | numeric-only proof of the same statement, no program | gate passes; method `not-program-verified` | as expected |
| J | `decide +native` instead of `native_decide` | gate does not accept the fact | failed |
| — | genuine provider theorem | passes, `lean-verified-program` | as expected |
| K | official status after a local pass | designated kind unchanged, no receipt | `lean-noncompliant`, no receipt |

All 12 behave as expected (`pv-evidence/controls/CONTROLS_PV.json`). The earlier 10 controls
(`pv-evidence/controls/CONTROLS.json`) are unchanged.

## Preserved contracts and inherited errors

- **Untouched.** No frozen file, existing statement, fingerprint, challenge, receipt, `kind` or
  `designated` value changed.
- **New nodes.** `RamanujanNumerics.v3` and `RamanujanGap.v3` are new versions, with their own
  fingerprints and challenges.
- **Inherited errors.** The 49 receipt-provenance diagnostics are inherited from the fork and
  unchanged. They were not "fixed" by editing receipts.
