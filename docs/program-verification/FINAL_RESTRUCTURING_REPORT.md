# Final restructuring report: native-assisted and lean-verified-program in IEANTN

- **Scope.** Local branch `agentB/native-assisted` of `hs-chae/IEANTN_test`. Nothing pushed, no
  PR, no receipt.
- **Attestations.** Local research reports in `pv-evidence/`, not official verification.

## Outcomes first

- **16 of 16** audited endpoints pass the local `native-assisted` gate, rerun on a clean tree at commit `d7dfcbe` (12) and `20aabf4` (4). `20aabf4` only renamed the four non-node keys in `endpoints.json`.
- **11** of them are `lean-verified-program`: the real C source, an association fact, an execution witness and a reviewed correctness theorem are all present in the proof closure.
- **5** pass the gate but are `not-program-verified`: `FKS2Numerics.v2.nu_asymp_e30_le`, `FKS2Numerics.v3.calibration_bound`, `RamanujanGap.v2.loss_bound`, `FKS2.v9.qrh_absolute_pi`, `FKS2.v5.updated_theta`.
  These are the two PoC 1 numeric certificates without a source link and the three standard-axiom consumers, which have 0 native facts.
- No endpoint failed or was blocked.
- **Official classification is unchanged everywhere.** No `kind` or `designated` value moved. No receipt was written. Every audited node conclusion is still `lean-noncompliant`, or `none-yet` for the consumers.

| endpoint | gate | evidence method | native facts | official kind | receipt | checked at |
|---|---|---|---|---|---|---|
| `RamanujanNumerics.v2.epsilon_budget` | **passed** | lean-verified-program | 6 | lean-noncompliant | absent | `d7dfcbe` |
| `RamanujanNumerics.v1.epsilon_budget` | **passed** | lean-verified-program | 6 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v7.qrh_pi` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v6.old_pi` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v5.numerical_pi` | **passed** | lean-verified-program | 7 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v2.nu_asymp_e30_le` | **passed** | not-program-verified | 8 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v3.calibration_bound` | **passed** | not-program-verified | 8 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v3.baseline_bound` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | `d7dfcbe` |
| `FKS2Numerics.v4.updated_bound` | **passed** | lean-verified-program | 12 | lean-noncompliant | absent | `d7dfcbe` |
| `RamanujanGap.v2.loss_bound` | **passed** | not-program-verified | 0 | none-yet | absent | `d7dfcbe` |
| `FKS2.v9.qrh_absolute_pi` | **passed** | not-program-verified | 0 | none-yet | absent | `d7dfcbe` |
| `FKS2.v5.updated_theta` | **passed** | not-program-verified | 0 | none-yet | absent | `d7dfcbe` |
| `@solution.ForwardRamanujan.forward` | **passed** | lean-verified-program | 12 | n/a | n/a | `20aabf4` |
| `@solution.FKS2Pair.assembled` | **passed** | lean-verified-program | 16 | n/a | n/a | `20aabf4` |
| `@pilot.CalibrationPilot.NewChain.new_chain` | **passed** | lean-verified-program | 13 | n/a | n/a | `20aabf4` |
| `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` | **passed** | lean-verified-program | 1 | n/a | n/a | `20aabf4` |

**Acceptance criterion: met.** Ramanujan (v1, v2) and Table 4 (old, QRH) each have a freshly rerun
`native-assisted: passed` attestation and are classified `lean-verified-program`. Each is backed by
the reviewed source, the challenge type match, and an exact axiom ledger in which every native
fact is traced to a `native_decide` token in a hashed source file. Comparator and the trust report
are unchanged for every other node:
- only the pages of the 11 attested nodes changed; the other 102 of 113 are byte-identical;
- every statement fingerprint and challenge is unchanged;
- `check` fails only on the same 49 inherited provenance items.

## What remains `lean-noncompliant`, and what official certification would need

- **Every audited provider stays `lean-noncompliant`.** Its proof still uses finite native facts:
  6 per Ramanujan instance, 7–8 per Table 4 instance, 8–12 in PoC 1.
- **What Comparator would need.** The same conclusion with a proof whose closure is exactly
  `propext`, `Classical.choice` and `Quot.sound`.
- **Shown feasible in the pilot.** `KernelA` reduces a provider of this exact shape to one native
  fact. Source match, enclosure, domain, execution, rounding and budget are all kernel-checked.
- **The blocker.** The last fact is decimal literal decoding: `FKS2Scalar.decimal` uses
  `String.splitOn`/`toNat?`, which the kernel does not reduce. Removing it needs a structurally
  recursive decoder plus a proof that it agrees with `decimal`. After that, an authentic workflow
  run could issue receipts.
- **The consumers already qualify by axioms.** `RamanujanGap.v2.loss_bound`, `FKS2.v9.qrh_absolute_pi`
  and `FKS2.v5.updated_theta` are standard-axiom implications (0 native facts). They are eligible for
  ordinary Comparator verification today, as conditional theorems.
- **No official subtype.** A receipt-backed official `lean-verified-program` kind would need an
  upstream policy decision. Until then the method is an optional, validated field and the
  promotion rule is unchanged.

## How the redesign helps readers

- **Every attested page shows four separate facts.** Evidence method, local gate, official
  classification and receipt status, so nothing reads as officially verified.
- **The method is evidence-based.** It comes from the proof itself, not from a justification's
  name. PoC 1 shows why this matters: two conclusions called "source-verified" have no C source in
  their proofs.
- **The ledger is exact and reproducible.** For each fact: the owning theorem, file:line, the token
  `native_decide`, the source SHA256, the decided proposition, and the count of trusted library
  implementations it reaches.

## Metadata migration (non-frozen nodes only)

- `FKS2Numerics.v2.nu_asymp_e30_le` (justification `checked-source-stability`): note sentence only. Evidence method not-program-verified; S, A and E fail because no C source is embedded.
- `FKS2Numerics.v3.calibration_bound` (`source-verified`): note sentence only. not-program-verified; S, A and E fail.
- `FKS2Numerics.v3.baseline_bound` (`source-verified`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v4.updated_bound` (`source-verified`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v5.numerical_pi` (`source-transport`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v7.qrh_pi` (`source-model-qrh`): `verification_method: lean-verified-program` + note sentence.
- `RamanujanNumerics.v2.epsilon_budget` (`source-model`): `verification_method: lean-verified-program` + note sentence.
- Untouched on purpose: `RamanujanNumerics.v1` and `FKS2Numerics.v6` (frozen by SHA256), and the consumers `RamanujanGap.v2`, `FKS2.v9`, `FKS2.v5` (designated `none-yet`, not a Lean justification).
- All edits are pure additions: 6 files, +29 lines, 0 deletions. Each was checked by re-parsing: only that note, and possibly the new key, changed.

Frozen nodes (`RamanujanNumerics.v1`, `FKS2Numerics.v6`, …) are untouched. Their pages get the
gate rows from the sidecar.

**Comparator-certified conclusions.** The A→B pilot (`@pilot.*`, passed) re-derives
`DudekPlattNumerics.v4.pi_two_sided_footnote` and `DudekPlatt.v4.ramanujan_inequality_9401` by a
program-verified route. That route is **not** registered as an extra justification on those nodes:
- a `lean-noncompliant` justification asserts that the proof lives in `Solutions/<node>/`, but the
  pilot proof lives in `pilots/`;
- registering it would mean moving the pilot into the node's solution project first.

Either way, the designated `lean-comparator` justification, which is stronger and kernel-only,
stays untouched.

## Per-endpoint final tables

#### `RamanujanNumerics.v2.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanNumerics.v2.epsilon_budget` → `RamanujanNumerics.v2.challenge_epsilon_budget` : `RamanujanNumerics.v2.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:46:52+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 6: `ForwardRamanujan.Updated.budget_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Updated.data).sum = ForwardRamanujan.Up`); `ForwardRamanujan.Updated.domain_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Updated.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Updated.enclosure_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:41, token `native_decide`, decides `ForwardRamanujan.Updated.data.length = 7 ∧   ForwardRamanujan.Updated.`); `ForwardRamanujan.Updated.execution_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.progra`); `ForwardRamanujan.Updated.source_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Updated.actualSource F`); `ForwardRamanujan.Updated.suffix_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.program.scale = `) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v2/c/updated.c` sha256 `3de9c2d75ed984719aee22f05f0217a605e72f419a737134f269074b34c09f5c` embedded by `ForwardRamanujan.Updated.actualSource`. Proofs: source_association: `ForwardRamanujan.Updated.concrete_execution`, `ForwardRamanujan.Updated.source_check`, `ForwardRamanujan.Updated.source_check._native.native_decide.ax_1_1`; execution_witness: `ForwardRamanujan.Updated.concrete_execution`, `ForwardRamanujan.Updated.verified_with_domain`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `611147087b56d0f9`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/RamanujanNumerics.v2`; `python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v2.epsilon_budget` |

#### `RamanujanNumerics.v1.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanNumerics.v1.epsilon_budget` → `RamanujanNumerics.v1.challenge_epsilon_budget` : `RamanujanNumerics.v1.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:47:23+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 6: `ForwardRamanujan.Old.budget_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Old.data).sum = ForwardRamanujan.Old.da`); `ForwardRamanujan.Old.domain_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Old.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Old.enclosure_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:41, token `native_decide`, decides `ForwardRamanujan.Old.data.length = 7 ∧   ForwardRamanujan.Old.targets.`); `ForwardRamanujan.Old.execution_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.in`); `ForwardRamanujan.Old.source_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Old.actualSource Forwa`); `ForwardRamanujan.Old.suffix_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.scale = some`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v1/c/baseline.c` sha256 `4f468d7f31d5bdd678f8692337ff6c21b0747828c0248685671c2a69b82f9be2` embedded by `ForwardRamanujan.Old.actualSource`. Proofs: source_association: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.source_check`, `ForwardRamanujan.Old.source_check._native.native_decide.ax_1_1`; execution_witness: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.verified_with_domain`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `3fdfdcf84bd2a28b`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/RamanujanNumerics.v1`; `python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v1.epsilon_budget` |

#### `FKS2Numerics.v7.qrh_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v7.qrh_pi` → `FKS2Numerics.v7.challenge_qrh_pi` : `QRHCH2.v5.psi_refined_bound → FKS2.v6.table4_anchor_300 → FKS2Numerics.v7.qrh_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-qrh`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:47:44+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Pair.qr_literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean:39, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Table4.selected.scale = some FKS2Table4.sca`); `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧   SumStability.gamma 29 < 1 ∧     0 ≤ FKS2`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧   FKS2Table4.scale = 1 / 2 ^ 58 ∧`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧   FKS2S`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Pair.Updated.concrete_execution`, `FKS2Pair.Updated.verified_qrh_transport`, `FKS2Pair.original_execution_at`; execution_witness: `FKS2Pair.Updated.concrete_execution`, `FKS2Pair.Updated.verified_qrh_transport`, `FKS2Pair.original_execution_at`; generic_correctness: `FKS2Table4.verified_fks2_transport`, `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `193339c9030dd447`, 31 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v7`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v7.qrh_pi` |

#### `FKS2Numerics.v6.old_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v6.old_pi` → `FKS2Numerics.v6.challenge_old_pi` : `FKS2.v8.table3_theta_300 →   FKS2.v8.table3_theta_310 →     FKS2.v8.table3_theta_320 → FKS2.v8.table3_theta_330 → FKS2.v6.table4_anchor_300 → FKS2Numerics.v6.old_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-old`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:48:28+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Pair.Old.boundary_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:21, token `native_decide`, decides `FKS2Pair.Old.scale = 1 / 2 ^ 48 ∧   FKS2Pair.Old.anchorHi ≤ FKS2Pair.O`); `FKS2Pair.Old.budget_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:93, token `native_decide`, decides `0 ≤ FKS2Pair.Old.totalError ∧   FKS2Pair.Old.totalError ≤ 1 / 10 ^ 26 `); `FKS2Pair.Old.enclosure_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:29, token `native_decide`, decides `FKS2Pair.Old.data.length = 30 ∧   (∀ r ∈ FKS2Pair.Old.data, FKS2SumBri`); `FKS2Pair.Old.execution_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:57, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.inputs = some`); `FKS2Pair.Old.exp_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:22, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true`); `FKS2Pair.Old.literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:38, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.scale = some FKS2Pair.O`); `FKS2Pair.Old.source_tokens` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:54, token `native_decide`, decides `(SumStability.tokens FKS2Pair.Old.oldSource).isSome = true ∧   SumStab`); `FKS2Pair.Old.suffix_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:33, token `native_decide`, decides `FKS2Pair.Old.scaledOutput = FKS2Pair.Old.scale * FKS2Pair.Old.sumOut ∧`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` sha256 `fcce411cc6c2a1c9bd64109f421dd94b8a4ed131eb02afd9d6da7c20e22cdc54` embedded by `FKS2Pair.Old.oldSource`. Proofs: source_association: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.source_checked`, `FKS2Pair.Old.source_tokens`; execution_witness: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.verified_old_transport`; generic_correctness: `FKS2Pair.source_linked_transport_upper`, `FKS2Pair.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `a261df6b98746e98`, 26 project modules hashed |
| Mathematical hypotheses | `FKS2.v8.table3_theta_300`; `FKS2.v8.table3_theta_310`; `FKS2.v8.table3_theta_320`; `FKS2.v8.table3_theta_330`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v6`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v6.old_pi` |

#### `FKS2Numerics.v5.numerical_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v5.numerical_pi` → `FKS2Numerics.v5.challenge_numerical_pi` : `QRHCH2.v5.psi_refined_bound → FKS2.v6.table4_anchor_300 → FKS2Numerics.v5.numerical_pi` |
| Official designated `kind` | lean-noncompliant (`source-transport`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:49:11+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 7: `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧   SumStability.gamma 29 < 1 ∧     0 ≤ FKS2`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧   FKS2Table4.scale = 1 / 2 ^ 58 ∧`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧   FKS2S`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Table4.concrete_execution`, `FKS2Table4.output_unique`, `FKS2Table4.source_checked`; execution_witness: `FKS2Table4.concrete_execution`, `FKS2Table4.output_unique`, `FKS2Table4.verified_fks2_transport`; generic_correctness: `FKS2Table4.verified_fks2_transport`, `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `2d601713081c1f1a`, 28 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v5`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v5.numerical_pi` |

#### `FKS2Numerics.v2.nu_asymp_e30_le`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v2.nu_asymp_e30_le` → `FKS2Numerics.v2.challenge_nu_asymp_e30_le` : `FKS2Numerics.v2.nu_asymp_e30_le` |
| Official designated `kind` | lean-noncompliant (`checked-source-stability`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:49:59+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43,   FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Sc`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44,   FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2`); `FKS2Scalar.target_enclosure` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:113, token `native_decide`, decides `0 ≤ FKS2Scalar.uLo ∧   0 ≤ FKS2Scalar.expLo (2 * FKS2Scalar.zLo) ∧    `); `FKS2Scalar.z_exp_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:96, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Scalar.zLo) (FKS2Scalar.expLo (2 * FKS2Sc`); `FKS2SumBridge.composition_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Whole.lean:36, token `native_decide`, decides `0 < FKS2SumBridge.prefactor ∧   0 < FKS2SumBridge.sumCoefficient ∧    `); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧   FKS2SumBridge.trace2.steps.`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 `); `FKS2SumBridge.integration_budget_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Integration.lean:42, token `native_decide`, decides `0 ≤ FKS2SumBridge.specError1 ∧   0 ≤ FKS2SumBridge.specError2 ∧     0 `) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/fks2.c` sha256 `a0fde9cefcbf3064b4a47bf85889fc459db89b6c68ceabe579254ecbb34b06a6` embedded by NOTHING. Proofs: source_association: ; execution_witness: ; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `3bc115abdc4c2976`, 25 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build CalibrationSolution` rc 0 in `Solutions/FKS2Numerics.v2`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v2.nu_asymp_e30_le` |

#### `FKS2Numerics.v3.calibration_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v3.calibration_bound` → `FKS2Numerics.v3.challenge_calibration_bound` : `FKS2Numerics.v3.calibration_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:50:22+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43,   FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Sc`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44,   FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2`); `FKS2Scalar.target_enclosure` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:113, token `native_decide`, decides `0 ≤ FKS2Scalar.uLo ∧   0 ≤ FKS2Scalar.expLo (2 * FKS2Scalar.zLo) ∧    `); `FKS2Scalar.z_exp_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:96, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Scalar.zLo) (FKS2Scalar.expLo (2 * FKS2Sc`); `FKS2SumBridge.composition_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Whole.lean:36, token `native_decide`, decides `0 < FKS2SumBridge.prefactor ∧   0 < FKS2SumBridge.sumCoefficient ∧    `); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧   FKS2SumBridge.trace2.steps.`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 `); `FKS2SumBridge.integration_budget_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Integration.lean:42, token `native_decide`, decides `0 ≤ FKS2SumBridge.specError1 ∧   0 ≤ FKS2SumBridge.specError2 ∧     0 `) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v3/c/baseline.c` sha256 `9893599de3561ab8da90396530ad95a31ee0d2beaaabbdc3f20969ad34a912c9` embedded by NOTHING. Proofs: source_association: ; execution_witness: ; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `e8773edf23e10fcd`, 28 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v3`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v3.calibration_bound` |

#### `FKS2Numerics.v3.baseline_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v3.baseline_bound` → `FKS2Numerics.v3.challenge_baseline_bound` : `FKS2Numerics.v3.baseline_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:50:45+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Correction.baseline_prefix_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:79, token `native_decide`, decides `StateT.run       (FKS2Scalar.evalBlock FKS2Scalar.round64 FKS2Correcti`); `FKS2Correction.composition_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Whole.lean:53, token `native_decide`, decides `0 < FKS2Correction.prefactor ∧   0 < FKS2Correction.sumCoefficient ∧  `); `FKS2Correction.target_enclosure` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:62, token `native_decide`, decides `0 ≤ FKS2Correction.uLo ∧   0 ≤ FKS2Scalar.expLo (2 * FKS2Correction.zL`); `FKS2Correction.z_exp_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:45, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Correction.zLo) (FKS2Scalar.expLo (2 * FK`); `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43,   FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Sc`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44,   FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧   FKS2SumBridge.trace2.steps.`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 `) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v3/c/baseline.c` sha256 `9893599de3561ab8da90396530ad95a31ee0d2beaaabbdc3f20969ad34a912c9` embedded by `FKS2Correction.baselineSource`. Proofs: source_association: `FKS2Correction.baseline_prefix_execution`, `FKS2Correction.baseline_prefix_execution._native.native_decide.ax_1_1`, `FKS2Correction.baseline_sum_errors`; execution_witness: `FKS2Correction.baseline_prefix_execution`, `FKS2Correction.baseline_prefix_execution._native.native_decide.ax_1_1`, `FKS2Correction.baseline_sum_errors`; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `3f78438ad2601446`, 23 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v3`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v3.baseline_bound` |

#### `FKS2Numerics.v4.updated_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v4.updated_bound` → `FKS2Numerics.v4.challenge_updated_bound` : `FKS2Numerics.v4.updated_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:51:08+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 12: `FKS2Correction.baseline_prefix_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:79, token `native_decide`, decides `StateT.run       (FKS2Scalar.evalBlock FKS2Scalar.round64 FKS2Correcti`); `FKS2Correction.baseline_source_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:68, token `native_decide`, decides `FKS2Scalar.execute FKS2Correction.baselineProgram = some FKS2Correctio`); `FKS2Correction.composition_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Whole.lean:53, token `native_decide`, decides `0 < FKS2Correction.prefactor ∧   0 < FKS2Correction.sumCoefficient ∧  `); `FKS2Correction.target_enclosure` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:62, token `native_decide`, decides `0 ≤ FKS2Correction.uLo ∧   0 ≤ FKS2Scalar.expLo (2 * FKS2Correction.zL`); `FKS2Correction.z_exp_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:45, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Correction.zLo) (FKS2Scalar.expLo (2 * FK`); `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43,   FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Sc`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44,   FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧   FKS2SumBridge.trace2.steps.`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 `); `FKS2Update.output_transport_check` (Solutions/FKS2Numerics.v4/FKS2Update/Source.lean:39, token `native_decide`, decides `\|FKS2Update.updatedQ - FKS2Update.coefficientRatio * FKS2Correction.ba`); `FKS2Update.updated_budget_checks` (Solutions/FKS2Numerics.v4/FKS2Update/Result.lean:23, token `native_decide`, decides `0 < FKS2Update.coefficientRatio ∧   0 ≤ FKS2Update.updatedError ∧     `); `FKS2Update.updated_source_execution` (Solutions/FKS2Numerics.v4/FKS2Update/Source.lean:29, token `native_decide`, decides `FKS2Scalar.execute FKS2Update.updatedProgram = some FKS2Update.updated`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v4/c/updated.c` sha256 `83c208e7ae9a74b89945f6a90867a4252e465a75325efdac00aa0aaf489b1b5a` embedded by `FKS2Update.updatedSource`. Proofs: source_association: `FKS2Update.updated_source_error`, `FKS2Update.updated_source_execution`, `FKS2Update.updated_source_execution._native.native_decide.ax_1_1`; execution_witness: `FKS2Update.updated_source_error`, `FKS2Update.updated_source_execution`, `FKS2Update.updated_source_execution._native.native_decide.ax_1_1`; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `fbe34fb463dcc20b`, 26 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v4`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v4.updated_bound` |

#### `RamanujanGap.v2.loss_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanGap.v2.loss_bound` → `RamanujanGap.v2.challenge_loss_bound` : `DudekPlattNumerics.v5.pi_two_sided_qrh → RamanujanNumerics.v2.epsilon_budget → RamanujanGap.v2.loss_bound` |
| Official designated `kind` | none-yet (`solution`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✗/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:51:33+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 0 |
| Other unwanted axioms / sorry | none |
| Source / executable model | none configured. Proofs: source_association: ; execution_witness: ; generic_correctness: . Closure fingerprint `efe879897266ea2e`, 11 project modules hashed |
| Mathematical hypotheses | `DudekPlattNumerics.v5.pi_two_sided_qrh`; `RamanujanNumerics.v2.epsilon_budget` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build ForwardRamanujanUpdate.Consumer` rc 0 in `Solutions/RamanujanNumerics.v2`; `python scripts/native_assisted/native_assisted_check.py check RamanujanGap.v2.loss_bound` |

#### `FKS2.v9.qrh_absolute_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2.v9.qrh_absolute_pi` → `FKS2.v9.challenge_qrh_absolute_pi` : `FKS2Numerics.v7.qrh_pi → FKS2.v9.qrh_absolute_pi` |
| Official designated `kind` | none-yet (`solution`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✗/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:52:03+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 0 |
| Other unwanted axioms / sorry | none |
| Source / executable model | none configured. Proofs: source_association: ; execution_witness: ; generic_correctness: . Closure fingerprint `7ef21581dbe03c3a`, 5 project modules hashed |
| Mathematical hypotheses | `FKS2Numerics.v7.qrh_pi` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build FKS2PairConsumers` rc 0 in `Solutions/FKS2Numerics.v7`; `python scripts/native_assisted/native_assisted_check.py check FKS2.v9.qrh_absolute_pi` |

#### `FKS2.v5.updated_theta`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2.v5.updated_theta` → `FKS2.v5.challenge_updated_theta` : `QRHPropagation.v3.psi_classical_bound → BKLNW.v1.corollary_5_1 → FKS2Numerics.v4.updated_bound → FKS2.v5.updated_theta` |
| Official designated `kind` | none-yet (`solution`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✗/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:52:26+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 0 |
| Other unwanted axioms / sorry | none |
| Source / executable model | none configured. Proofs: source_association: ; execution_witness: ; generic_correctness: . Closure fingerprint `73bf177a22ce02b7`, 11 project modules hashed |
| Mathematical hypotheses | `QRHPropagation.v3.psi_classical_bound`; `BKLNW.v1.corollary_5_1`; `FKS2Numerics.v4.updated_bound` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2.v5`; `python scripts/native_assisted/native_assisted_check.py check FKS2.v5.updated_theta` |

#### `@solution.ForwardRamanujan.forward`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@solution.ForwardRamanujan.forward` → `ForwardRamanujan.forward` : `QRHCH2.v5.psi_refined_bound → RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:55:54+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 12: `ForwardRamanujan.Old.budget_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Old.data).sum = ForwardRamanujan.Old.da`); `ForwardRamanujan.Old.domain_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Old.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Old.enclosure_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:41, token `native_decide`, decides `ForwardRamanujan.Old.data.length = 7 ∧   ForwardRamanujan.Old.targets.`); `ForwardRamanujan.Old.execution_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.in`); `ForwardRamanujan.Old.source_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Old.actualSource Forwa`); `ForwardRamanujan.Old.suffix_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.scale = some`); `ForwardRamanujan.Updated.budget_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Updated.data).sum = ForwardRamanujan.Up`); `ForwardRamanujan.Updated.domain_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Updated.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Updated.enclosure_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:41, token `native_decide`, decides `ForwardRamanujan.Updated.data.length = 7 ∧   ForwardRamanujan.Updated.`); `ForwardRamanujan.Updated.execution_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.progra`); `ForwardRamanujan.Updated.source_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Updated.actualSource F`); `ForwardRamanujan.Updated.suffix_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.program.scale = `) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v1/c/baseline.c` sha256 `4f468d7f31d5bdd678f8692337ff6c21b0747828c0248685671c2a69b82f9be2` embedded by `ForwardRamanujan.Old.actualSource`; `Solutions/RamanujanNumerics.v2/c/updated.c` sha256 `3de9c2d75ed984719aee22f05f0217a605e72f419a737134f269074b34c09f5c` embedded by `ForwardRamanujan.Updated.actualSource`. Proofs: source_association: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.source_check`, `ForwardRamanujan.Old.source_check._native.native_decide.ax_1_1`; execution_witness: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.verified_with_domain`, `ForwardRamanujan.Updated.concrete_execution`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `180524921ed4bed4`, 38 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build ForwardRamanujanUpdate.Assembly` rc 0 in `Solutions/RamanujanNumerics.v2`; `python scripts/native_assisted/native_assisted_check.py check @solution.ForwardRamanujan.forward` |

#### `@solution.FKS2Pair.assembled`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@solution.FKS2Pair.assembled` → `FKS2Pair.assembled` : `FKS2.v8.table3_theta_300 →   FKS2.v8.table3_theta_310 →     FKS2.v8.table3_theta_320 →       FKS2.v8.table3_theta_330 →         ZetaLogDeriv.v1.logDeriv_functional_equation →           GammaAsymptotics.v2.digamma_sub_log_isBigO_strip →             CH2.v2.proposition_2_4_upper →               CH2.v2.proposition_2_4_lower →                 ZetaLogDerivValues.v1.logDeriv_laurent_alternating →                   ZetaLogDerivValues.v1.logDeriv_neg_one →                     ZetaLogDerivValues.v1.logDeriv_two →                       ZetaLogDerivValues.v1.logDeriv_three_halves →                         CotangentSeries.v1.cot_series_zeta_values →                           ZeroCount.v1.rvm_error_bound →                             ZeroCount.v1.rvm_error_small →                               LowZeroes.v1.no_zeroes_below_first_ordinate →                                 ZetaHadamard.v1.logDeriv_partial_fractions →                                   OpenAIQRH.v1.zeta_seven_eighths →                                     FKS2.v6.table4_anchor_300 →                                       FKS2Numerics.v6.old_pi ∧                                         FKS2Numerics.v7.qrh_pi ∧                                           FKS2.v9.paired_absolute_pi ∧                                             FKS2.v9.strict_reconstructed_improvement ∧                                               FKS2.v9.strict_historical_improvement ∧ FKS2.v9.exact_allowance_ratios` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:56:30+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 16: `FKS2Pair.Old.boundary_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:21, token `native_decide`, decides `FKS2Pair.Old.scale = 1 / 2 ^ 48 ∧   FKS2Pair.Old.anchorHi ≤ FKS2Pair.O`); `FKS2Pair.Old.budget_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:93, token `native_decide`, decides `0 ≤ FKS2Pair.Old.totalError ∧   FKS2Pair.Old.totalError ≤ 1 / 10 ^ 26 `); `FKS2Pair.Old.enclosure_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:29, token `native_decide`, decides `FKS2Pair.Old.data.length = 30 ∧   (∀ r ∈ FKS2Pair.Old.data, FKS2SumBri`); `FKS2Pair.Old.execution_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:57, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.inputs = some`); `FKS2Pair.Old.exp_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:22, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true`); `FKS2Pair.Old.literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:38, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.scale = some FKS2Pair.O`); `FKS2Pair.Old.source_tokens` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:54, token `native_decide`, decides `(SumStability.tokens FKS2Pair.Old.oldSource).isSome = true ∧   SumStab`); `FKS2Pair.Old.suffix_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:33, token `native_decide`, decides `FKS2Pair.Old.scaledOutput = FKS2Pair.Old.scale * FKS2Pair.Old.sumOut ∧`); `FKS2Pair.qr_literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean:39, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Table4.selected.scale = some FKS2Table4.sca`); `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧   SumStability.gamma 29 < 1 ∧     0 ≤ FKS2`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧   FKS2Table4.scale = 1 / 2 ^ 58 ∧`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧   FKS2S`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` sha256 `fcce411cc6c2a1c9bd64109f421dd94b8a4ed131eb02afd9d6da7c20e22cdc54` embedded by `FKS2Pair.Old.oldSource`; `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.source_checked`, `FKS2Pair.Old.source_tokens`; execution_witness: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.verified_old_transport`, `FKS2Pair.Updated.concrete_execution`; generic_correctness: `FKS2Pair.source_linked_transport_upper`, `FKS2Pair.sum_upper`, `FKS2Table4.verified_fks2_transport`. Closure fingerprint `fadead91faf0264c`, 107 project modules hashed |
| Mathematical hypotheses | `FKS2.v8.table3_theta_300`; `FKS2.v8.table3_theta_310`; `FKS2.v8.table3_theta_320`; `FKS2.v8.table3_theta_330`; `ZetaLogDeriv.v1.logDeriv_functional_equation`; `GammaAsymptotics.v2.digamma_sub_log_isBigO_strip`; `CH2.v2.proposition_2_4_upper`; `CH2.v2.proposition_2_4_lower`; `ZetaLogDerivValues.v1.logDeriv_laurent_alternating`; `ZetaLogDerivValues.v1.logDeriv_neg_one`; `ZetaLogDerivValues.v1.logDeriv_two`; `ZetaLogDerivValues.v1.logDeriv_three_halves`; `CotangentSeries.v1.cot_series_zeta_values`; `ZeroCount.v1.rvm_error_bound`; `ZeroCount.v1.rvm_error_small`; `LowZeroes.v1.no_zeroes_below_first_ordinate`; `ZetaHadamard.v1.logDeriv_partial_fractions`; `OpenAIQRH.v1.zeta_seven_eighths`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build FKS2PairReplay` rc 0 in `Solutions/FKS2Numerics.v7`; `python scripts/native_assisted/native_assisted_check.py check @solution.FKS2Pair.assembled` |

#### `@pilot.CalibrationPilot.NewChain.new_chain`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pilot.CalibrationPilot.NewChain.new_chain` → `CalibrationPilot.NewChain.new_chain` : `QRHCH2.v5.psi_refined_bound →   (∀ x > Real.exp 9400,       DudekPlatt.v3.mainTerm x + (120 - CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6 < IEANTN.primeCounting x ∧         IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6) ∧     (∀ x > Real.exp 9401, (1 + 68431 / 5000 / Real.log x) * x ^ 2 / Real.log x ^ 6 < ForwardRamanujan.gap x) ∧       (∀ x > Real.exp 9401, ForwardRamanujan.loss x = 0) ∧ DudekPlatt.v4.ramanujan_inequality_9401` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:57:22+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 13: `CalibrationPilot.NewA.budget_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:67, token `native_decide`, decides `(List.map abs CalibrationPilot.NewA.data).sum = CalibrationPilot.NewA.`); `CalibrationPilot.NewA.canon_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:39, token `native_decide`, decides `(ForwardRamanujan.tokens (ForwardRamanujan.renderProgram CalibrationPi`); `CalibrationPilot.NewA.domain_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:45, token `native_decide`, decides `∀ r ∈ CalibrationPilot.NewA.data, FKS2SumBridge.inputCheck r = true`); `CalibrationPilot.NewA.enclosure_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:43, token `native_decide`, decides `CalibrationPilot.NewA.data.length = 7 ∧   CalibrationPilot.NewA.target`); `CalibrationPilot.NewA.execution_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:52, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.i`); `CalibrationPilot.NewA.source_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:36, token `native_decide`, decides `CalibrationPilot.sourceMatchesNamed CalibrationPilot.NewA.actualSource`); `CalibrationPilot.NewA.suffix_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:62, token `native_decide`, decides `ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.scale = som`); `CalibrationPilot.NewB.budget_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:65, token `native_decide`, decides `(List.map abs CalibrationPilot.NewB.data).sum = CalibrationPilot.NewB.`); `CalibrationPilot.NewB.domain_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:43, token `native_decide`, decides `∀ r ∈ CalibrationPilot.NewB.data, FKS2SumBridge.inputCheck r = true`); `CalibrationPilot.NewB.enclosure_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:41, token `native_decide`, decides `CalibrationPilot.NewB.data.length = 7 ∧   CalibrationPilot.NewB.target`); `CalibrationPilot.NewB.execution_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewB.program.i`); `CalibrationPilot.NewB.source_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches CalibrationPilot.NewB.actualSource Cali`); `CalibrationPilot.NewB.suffix_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral CalibrationPilot.NewB.program.scale = som`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `pilots/agentB-calibration/c/calibration_new.c` sha256 `f206bd817deab53b2fbaa38e4f7a84b5ad6958d5c5d625fc49eb407975be0568` embedded by `CalibrationPilot.NewA.actualSource`; `pilots/agentB-calibration/c/ramanujan_9401_new.c` sha256 `86d204a5a7ba913a43e8e387990b7ea60dc146e4eac336b98f9bffa2f35d8895` embedded by `CalibrationPilot.NewB.actualSource`. Proofs: source_association: `CalibrationPilot.NewA.concrete_execution`, `CalibrationPilot.NewA.source_check`, `CalibrationPilot.NewA.source_check._native.native_decide.ax_1_1`; execution_witness: `CalibrationPilot.NewA.concrete_execution`, `CalibrationPilot.NewA.verified_with_domain`, `CalibrationPilot.NewB.concrete_execution`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `9805000b3b6eb266`, 32 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build CalibrationPilot` rc 0 in `pilots/agentB-calibration`; `python scripts/native_assisted/native_assisted_check.py check @pilot.CalibrationPilot.NewChain.new_chain` |

#### `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` → `CalibrationPilot.KernelChain.pi_calibrated_k` : `QRHCH2.v5.psi_refined_bound →   ∀ x > Real.exp 9400,     DudekPlatt.v3.mainTerm x + (120 - CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6 < IEANTN.primeCounting x ∧       IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:57:57+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `CalibrationPilot.KernelA.decode_check` (pilots/agentB-calibration/CalibrationPilot/KernelA.lean:36, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.i`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `pilots/agentB-calibration/c/calibration_new.c` sha256 `f206bd817deab53b2fbaa38e4f7a84b5ad6958d5c5d625fc49eb407975be0568` embedded by `CalibrationPilot.NewA.actualSource`. Proofs: source_association: `CalibrationPilot.KernelA.execution_k`, `CalibrationPilot.KernelA.source_k`, `CalibrationPilot.KernelA.source_k._proof_1_1`; execution_witness: `CalibrationPilot.KernelA.execution_k`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`. Closure fingerprint `019456a6cec99c2f`, 28 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `ℝ`; `x > Real.exp 9400` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build CalibrationPilot` rc 0 in `pilots/agentB-calibration`; `python scripts/native_assisted/native_assisted_check.py check @pilot.CalibrationPilot.KernelChain.pi_calibrated_k` |



## Reader check: self-audit, NOT independent

No separate reader agent was approved, so this is a documented, reviewer-style self-audit. It
uses only the standard IEANTN entry points:
- the generated node page (`ieantn.py pages`);
- the node's `Conclusions.lean` docstrings and `formalization.yaml` notes;
- the `Solutions/*/README.md` maps;
- `docs/qrh/README.md` and the walkthroughs it links;
- `docs/program-verification/`.

| Question | Ramanujan (`RamanujanNumerics.v2`) | Table 4 (`FKS2Numerics.v7`) | PoC 1 (`FKS2Numerics.v3/v4`, `v2`) |
|---|---|---|---|
| What theorem? | Page: docstring "Spelled out…" + Lean body: `εUpper(131,x) − εLower(119,e^3914,x) ≤ 9.101` on `x > e^3915` | Page: `Eπ(x) ≤ 5·10⁻¹⁶` for `x ≥ e^330`, with premises named | Page: the ν* bounds, with the meaning of `ν*` now in the docstrings |
| Why C? | Docstring "How it is checked": C sums seven upward-rounded terms, scales and subtracts | Docstring: the program evaluates `B_safe(Q)` over 30 cells | v3/v4 baseline/updated docstrings name `c/baseline.c` / `c/updated.c`. v2 and v3 calibration: the docstring says the designated proof does **not** use C source |
| What did Lean verify? | Page row "Evidence method: lean-verified-program"; the attestation lists S/A/E/C/M with theorem names (`source_check`, `concrete_execution`, `source_linked_upper`) | Same row; attestation names `FKS2Table4.source_checked`, `FKS2Pair.Updated.concrete_execution`, `FKS2Table4.verified_fks2_transport` | Attestation per conclusion. For v2/v3 calibration the page shows "Evidence method: not-program-verified" |
| Which native facts are trusted? | Page: "6 finite native facts"; note lists their roles; attestation gives each owning theorem, file:line and decided proposition | 8, same detail | 8 or 12, same detail |
| What is not proved about compilation/hardware? | Docstring "compiler and hardware are trusted"; page row "not a receipt"; attestation `trust_boundary` | Same | Same |
| How does the result reach the downstream theorem? | Page "Assumed by: RamanujanGap.v2.*"; docstring names the consumer | Page "Assumed by: FKS2.v9.*" | `FKS2.v4` / `FKS2.v5` docstrings and imports |

**Unresolved ambiguities (findings).**
1. On every page, `Evidence: lean, noncompliant` sits directly above `Evidence method:
   lean-verified-program`. A reader may take "noncompliant" for "unverified". The added row
   `Official IEANTN classification … (designated; unchanged)` mitigates this. A one-line legend on
   the pages index would help further; that is a proposal, not done.
2. **Frozen nodes.** `RamanujanNumerics.v1` and `FKS2Numerics.v6` show the gate rows, but their
   docstrings cannot be extended. The mathematics-first text is one link away, in the walkthroughs.
3. **Ambiguous label.** "Sources traced: none" (literature sources of the imports) can be misread
   as "no source code". This is inherited wording.
4. **Broken links on the fork.** The page's `Source`/`Solution` links point at `teorth/IEANTN` and
   return 404 there. Inherited.
5. **Consumer pages.** Pages of consumers (`RamanujanGap.v2.*`, `FKS2.v9.*`) do not show gate rows
   unless they are audited. They are standard-axiom implications, and their attestations record
   method `not-program-verified`, since they consume the budget as a hypothesis. A reader has to
   follow "Assumes" to reach the program-verified provider.


## Pointers

- [NATIVE_ASSISTED_DESIGN.md](NATIVE_ASSISTED_DESIGN.md)
- [PROGRAM_VERIFICATION_INVENTORY.md](PROGRAM_VERIFICATION_INVENTORY.md)
- [PV_HUMAN_READABLE_GUIDE.md](PV_HUMAN_READABLE_GUIDE.md), which includes the English technical
  summary and the Korean explanation
- [INTEGRATION_DIFF_AND_CHECKS.md](INTEGRATION_DIFF_AND_CHECKS.md)
- the tool: `scripts/native_assisted/README.md`
