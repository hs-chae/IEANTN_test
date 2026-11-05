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

---

## Second round (2026-11-05)

### Builds

| Project | Command | Result |
|---|---|---|
| merged tree (`fa70b6a`) | core `lake build` | OK, 4129 jobs |
| `Solutions/ScopedWinnerA.v1` (Agent A) | `lake build Solution` | OK, 9174 jobs, 16 min, peak 7.3 GB per process |
| `Solutions/RamanujanGap.v3` | `lake build Solution RamanujanGapReplay` (now requiring `DudekPlattNumerics.v5`) | OK, 17 s: the closure was already built (`lake build --no-build`: up to date, 9000 jobs) |
| `pilots/pv-twobackend` | `lake build TwoBackend` | OK |
| `pilots/pv-replay` | `lake build PVReplay` (now with `KernelChain`, `Chunked`) | OK; `KernelChain` 177 s, 22.7 GB peak; `Chunked` 5.2 s |
| `Solutions/ProgramVerification` | `lake build PVCore PVRamanujan` + `PVCore.Kernel`, `PVCore.Chunked`, `PVRamanujan.Kernel` | OK |

### Axiom closures (`#print axioms`)

| Theorem | Axioms beyond the three standard ones |
|---|---|
| `PVCore.check_of_decode`, `upperCheck_of_decode`, `certifiedChunked`, `le_bound_of_checkChunked`, `PVRamanujan.budgetCheck_of_decode`, `budget_shift` | none |
| `PVTwoBackend.pi_input_of_powerLog` (the data link) | none |
| `PVTwoBackend.StageB.budget` | `StageB.certificate` (1) |
| `ScopedWinnerA.pi_00947147` (Agent A) | 49 `native_decide` facts |
| `PVTwoBackend.gap_exceeds_leading` | 50: Agent A's 49 + `StageB.certificate` |
| `PVPilot.Kernel.gap_exceeds_leading` | `decodeA`, `decodeB` (literal decoding only) |
| `PVPilot.Updated.gap_exceeds_leading` (now `gap_of` with the native certificates) | `certificateA`, `certificateB` (unchanged) |
| `PVChunked.Table4QRH.qrh_pi` | 3 existing analytic facts + the chunked certificate (4, as the single-call replay) |
| `PVChunked.InverseSquares.sum_le` | its certificate (1) |
| `RamanujanGap.v3.gap_from_psi`, `loss_from_psi`, `gap_from_qrh` | `RamanujanNumerics.v3.Provider.certificate` (1) |
| `DudekPlattNumerics.v5.challenge_pi_two_sided_qrh` | none |

### Freshness controls on the retrofitted providers (`controls_freshness.py`, scratch copies)

| Provider | A: changed literal, with `needs` | B: same change, `needs` removed | Repository tree |
|---|---|---|---|
| `RamanujanNumerics.v2` (`updated.c`) | rebuilt; `native_decide` evaluates the certificate to false (rc 1); restored build rc 0 | stale build replayed, rc 0 | unchanged |
| `FKS2Numerics.v5` (`fks2_table4_transport.c`) | rebuilt; certificate false (rc 1); restored rc 0 | stale build replayed, rc 0 | unchanged |

### Progress probe and solution modules

| Check | Before | After |
|---|---|---|
| `ieantn.py progress RamanujanGap.v3` | "does NOT typecheck": the probe's `import Solution` loaded `Solutions/CH2.v1/Solution` | typechecks, 0 holes, both challenge theorems proved |
| `ieantn.py progress RamanujanGap.v2` | crashed: `comparator.json` missing | typechecks, 0 holes |
| `ieantn.py progress RamanujanNumerics.v3` | same shadowing | typechecks, 0 holes, challenge proved |
| first `Solution.olean` on `LEAN_PATH` in `FKS2Numerics.v5`, `v7`, `RamanujanNumerics.v3` | `Solutions/CH2.v1` | unchanged for v5/v7 (owner decision); v3 uses `RamanujanBudget.NodeTheorem` |

### Local gate

All 31 attestations pass, all at `b985e41` on a clean tree: the 25 of the first round and 6 new
ones, marked "(new)". One `check-all` run, 17 min 12 s wall, peak 9.5 GB. The attestations are
committed in `79a22e0`; the log is `agentB/evidence/pv4/gate_all_b985e41.log` (outside the
repository). Methods and native-fact counts of the 25 earlier endpoints are unchanged.

| Endpoint | Status | Method | Backends | Native facts |
|---|---|---|---|---|
| `RamanujanNumerics.v2.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 6 |
| `RamanujanNumerics.v1.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 6 |
| `FKS2Numerics.v7.qrh_pi` | passed | lean-verified-program | restricted-c-binary64 | 8 |
| `FKS2Numerics.v6.old_pi` | passed | lean-verified-program | restricted-c-binary64 | 8 |
| `FKS2Numerics.v5.numerical_pi` | passed | lean-verified-program | restricted-c-binary64 | 7 |
| `FKS2Numerics.v2.nu_asymp_e30_le` | passed | not-program-verified | - | 8 |
| `FKS2Numerics.v3.calibration_bound` | passed | not-program-verified | - | 8 |
| `FKS2Numerics.v3.baseline_bound` | passed | lean-verified-program | restricted-c-binary64 | 8 |
| `FKS2Numerics.v4.updated_bound` | passed | lean-verified-program | restricted-c-binary64 | 12 |
| `RamanujanGap.v2.loss_bound` | passed | not-program-verified | - | 0 |
| `FKS2.v9.qrh_absolute_pi` | passed | not-program-verified | - | 0 |
| `FKS2.v5.updated_theta` | passed | not-program-verified | - | 0 |
| `@solution.ForwardRamanujan.forward` | passed | lean-verified-program | restricted-c-binary64 | 12 |
| `@solution.FKS2Pair.assembled` | passed | lean-verified-program | restricted-c-binary64 | 16 |
| `@pilot.CalibrationPilot.NewChain.new_chain` | passed | lean-verified-program | restricted-c-binary64 | 13 |
| `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `RamanujanNumerics.v3.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `RamanujanGap.v3.loss_bound` | passed | not-program-verified | - | 0 |
| `RamanujanGap.v3.gap_lower_bound` | passed | not-program-verified | - | 0 |
| `@pv.PVRamanujan.V1.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `@pv.PVRamanujan.V2.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `@pv.PVRamanujan.OldGrouped.epsilon_budget` | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `@pv.PVTable4.QRH.qrh_pi` | passed | lean-verified-program | restricted-c-binary64 | 4 |
| `@pv.PVTable4.Old.old_pi` | passed | lean-verified-program | restricted-c-binary64 | 4 |
| `@pv.PVPilot.Updated.gap_exceeds_leading` | passed | lean-verified-program | restricted-c-binary64 | 2 |
| `@scoped.ScopedWinnerA.pi_00947147` (new) | passed | lean-verified-program | lean-dyadic-expr | 49 |
| `@twobackend.PVTwoBackend.gap_exceeds_leading` (new) | passed | lean-verified-program | lean-dyadic-expr, restricted-c-binary64 | 50 |
| `@replay.RamanujanGap.v3.gap_from_psi` (new) | passed | lean-verified-program | restricted-c-binary64 | 1 |
| `@pv.PVPilot.Kernel.gap_exceeds_leading` (new) | passed | lean-verified-program | restricted-c-binary64 | 2 |
| `@pv.PVChunked.Table4QRH.qrh_pi` (new) | passed | lean-verified-program | restricted-c-binary64 | 4 |
| `@pv.PVChunked.InverseSquares.sum_le` (new) | passed | lean-verified-program | restricted-c-binary64 | 1 |

### Repository checks (at `65a0851`)

| Check | Result |
|---|---|
| `ieantn.py fingerprint --check` | 0: no statement fingerprint moved |
| `ieantn.py gen-challenges --check` | 0 |
| `ieantn.py check` | Exit 1 only for the 49 inherited receipt-provenance items, as before. The local evidence check passes. One new warning: `RamanujanGap.v2` is `awaiting-solution` although every unjustified conclusion has a complete local proof (the owner's decision). |
| `python -m unittest discover -s tests` | 374 OK: 350 before, plus 13 page-proposal tests, 1 progress path-order test, 5 dyadic-backend and 2 challenge-module tests, 3 update-entry tests |
| Freeze manifests | forward 30/30, Table 4 19/19 byte-identical |
| Node pages, `649959d` (end of the first round) → now | 20 of 115 pages differ, each explained, no new page, index identical. 6 gain "Local proof" rows (`CH2` v7–v9, `QRHCH2` v3–v5: self-assessed nodes whose solutions record 0 holes). 1 gains the README link (`DudekPlattNumerics.v3`). 11 change only the re-attested gate rows (`FKS2Numerics` v2–v7, `FKS2` v5 and v9, `RamanujanNumerics` v1–v3). `RamanujanGap.v2` and `v3` gain both, from their new progress blocks; `v3`'s status reads `awaiting-verification`. |

### Independent reader

One Fable 5.1 subagent, launched 2026-11-05 on hschae's "try everything" (it was the open request
from the first round). Read-only: no builds, no edits, no paid APIs (it confirmed "no"). Its
report is in `agentB/evidence/pv4/REVIEW.md` (outside the repository).

| Finding | Kind | Fixed in |
|---|---|---|
| Tutorial put the statement before `plan`, which computes the bound it needs | blocker | tutorial §3 |
| Registry example hid five location keys; an update without them inherited the old provider's and `generate` would overwrite its files | blocker, a real hazard | `pv_update.py` now refuses such entries (3 tests); tutorial lists the keys |
| Tutorial still said the challenge theorem goes in `Solution.lean` | blocker (stale) | tutorial §3, §4 |
| No `endpoints.json` step before the gate | blocker | tutorial §3 |
| Kernel-route snippet used `m = 0` constants with the `m = 119` example | minor | tutorial §7 |
| "every lower-order term ≤ 10⁻³·x/log⁶x": false for the `I₆` tail (2.47·u, the reason `M = 122.5`) | wrong sentence | composition §4, `Link.lean` docstring |
| "the seven inputs are not node conclusions": four are | wrong sentence | composition §4, `Chain.lean`, Agent A doc, report |
| "the latter also return the decoded fields": reversed | wrong sentence | shared contracts §9 |
| 64-line chain file and 382 shared lines: stale | stale count | now 78 and 702 |
| Agent A's handoff file quoted as if in this repository | unclear | Agent A doc |
| `PiInput`'s upper half holds on `x > e^301`, not `e^300` | precision | composition §4, `Link.lean` |
| 177 s / 22.7 GB not in this log | missing | this section |

**Checked and confirmed by the reader.** Every native-fact count (50 = 49 + 1, 49 = 1 + 32 + 8 + 7 +
1, 2, 13, 4 = 3 + 1, 1, 0), the theorem statements quoted in the docs, and the mathematics of the
data link: no off-by-one in exponents, strictness or the offset of `Li` at 2.
