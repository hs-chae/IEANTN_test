# Per-endpoint final tables

Generated from `pv-evidence/*.native-assisted.local.json` by
`scripts/native_assisted/final_tables.py`. Do not edit by hand. There is one table per audited
endpoint, with the twelve fields the restructuring task requires. Each attestation is a local
research report, not an IEANTN verification receipt.

Shortened entries end in "…". Every native fact has type `@Eq Bool e Bool.true` (the checker
verifies this shape), and the "decides" text is the proposition `e` decides. Its full text is in the
attestation under `axioms.native_facts[].decided_proposition`, and the full theorem lists are under
`method_checks`.

## `RamanujanNumerics.v2.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanNumerics.v2.epsilon_budget` → `RamanujanNumerics.v2.challenge_epsilon_budget` : `RamanujanNumerics.v2.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:46:52+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 6: `ForwardRamanujan.Updated.budget_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Updated.data).sum = ForwardRamanujan.Up…`); `ForwardRamanujan.Updated.domain_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Updated.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Updated.enclosure_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:41, token `native_decide`, decides `ForwardRamanujan.Updated.data.length = 7 ∧ ForwardRamanujan.Updated.ta…`); `ForwardRamanujan.Updated.execution_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.progra…`); `ForwardRamanujan.Updated.source_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Updated.actualSource F…`); `ForwardRamanujan.Updated.suffix_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.program.scale = …`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v2/c/updated.c` sha256 `3de9c2d75ed984719aee22f05f0217a605e72f419a737134f269074b34c09f5c` embedded by `ForwardRamanujan.Updated.actualSource`. Proofs: source_association: `ForwardRamanujan.Updated.concrete_execution`, `ForwardRamanujan.Updated.source_check`, `ForwardRamanujan.Updated.source_check._native.native_decide.ax_1_1`, … (1 more); execution_witness: `ForwardRamanujan.Updated.concrete_execution`, `ForwardRamanujan.Updated.verified_with_domain`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `611147087b56d0f9`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/RamanujanNumerics.v2`; `python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v2.epsilon_budget` |

## `RamanujanNumerics.v1.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanNumerics.v1.epsilon_budget` → `RamanujanNumerics.v1.challenge_epsilon_budget` : `RamanujanNumerics.v1.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:47:23+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 6: `ForwardRamanujan.Old.budget_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Old.data).sum = ForwardRamanujan.Old.da…`); `ForwardRamanujan.Old.domain_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Old.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Old.enclosure_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:41, token `native_decide`, decides `ForwardRamanujan.Old.data.length = 7 ∧ ForwardRamanujan.Old.targets.le…`); `ForwardRamanujan.Old.execution_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.in…`); `ForwardRamanujan.Old.source_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Old.actualSource Forwa…`); `ForwardRamanujan.Old.suffix_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.scale = some…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v1/c/baseline.c` sha256 `4f468d7f31d5bdd678f8692337ff6c21b0747828c0248685671c2a69b82f9be2` embedded by `ForwardRamanujan.Old.actualSource`. Proofs: source_association: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.source_check`, `ForwardRamanujan.Old.source_check._native.native_decide.ax_1_1`, … (1 more); execution_witness: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.verified_with_domain`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `3fdfdcf84bd2a28b`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/RamanujanNumerics.v1`; `python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v1.epsilon_budget` |

## `FKS2Numerics.v7.qrh_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v7.qrh_pi` → `FKS2Numerics.v7.challenge_qrh_pi` : `QRHCH2.v5.psi_refined_bound → FKS2.v6.table4_anchor_300 → FKS2Numerics.v7.qrh_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-qrh`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:47:44+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Pair.qr_literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean:39, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Table4.selected.scale = some FKS2Table4.sca…`); `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧ SumStability.gamma 29 < 1 ∧ 0 ≤ FKS2Table4…`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS…`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧ FKS2Table4.scale = 1 / 2 ^ 58 ∧ (…`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa…`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧ FKS2Sca…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Pair.Updated.concrete_execution`, `FKS2Pair.Updated.verified_qrh_transport`, `FKS2Pair.original_execution_at`, … (6 more); execution_witness: `FKS2Pair.Updated.concrete_execution`, `FKS2Pair.Updated.verified_qrh_transport`, `FKS2Pair.original_execution_at`, … (4 more); generic_correctness: `FKS2Table4.verified_fks2_transport`, `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `193339c9030dd447`, 31 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v7`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v7.qrh_pi` |

## `FKS2Numerics.v6.old_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v6.old_pi` → `FKS2Numerics.v6.challenge_old_pi` : `FKS2.v8.table3_theta_300 →   FKS2.v8.table3_theta_310 →     FKS2.v8.table3_theta_320 → FKS2.v8.table3_theta_330 → FKS2.v6.table4_anchor_300 → FKS2Numerics.v6.old_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-old`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:48:28+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Pair.Old.boundary_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:21, token `native_decide`, decides `FKS2Pair.Old.scale = 1 / 2 ^ 48 ∧ FKS2Pair.Old.anchorHi ≤ FKS2Pair.Old…`); `FKS2Pair.Old.budget_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:93, token `native_decide`, decides `0 ≤ FKS2Pair.Old.totalError ∧ FKS2Pair.Old.totalError ≤ 1 / 10 ^ 26 ∧ …`); `FKS2Pair.Old.enclosure_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:29, token `native_decide`, decides `FKS2Pair.Old.data.length = 30 ∧ (∀ r ∈ FKS2Pair.Old.data, FKS2SumBridg…`); `FKS2Pair.Old.execution_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:57, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.inputs = some…`); `FKS2Pair.Old.exp_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:22, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Pair.Old.literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:38, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.scale = some FKS2Pair.O…`); `FKS2Pair.Old.source_tokens` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:54, token `native_decide`, decides `(SumStability.tokens FKS2Pair.Old.oldSource).isSome = true ∧ SumStabil…`); `FKS2Pair.Old.suffix_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:33, token `native_decide`, decides `FKS2Pair.Old.scaledOutput = FKS2Pair.Old.scale * FKS2Pair.Old.sumOut ∧…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` sha256 `fcce411cc6c2a1c9bd64109f421dd94b8a4ed131eb02afd9d6da7c20e22cdc54` embedded by `FKS2Pair.Old.oldSource`. Proofs: source_association: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.source_checked`, `FKS2Pair.Old.source_tokens`, … (2 more); execution_witness: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.verified_old_transport`; generic_correctness: `FKS2Pair.source_linked_transport_upper`, `FKS2Pair.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `a261df6b98746e98`, 26 project modules hashed |
| Mathematical hypotheses | `FKS2.v8.table3_theta_300`; `FKS2.v8.table3_theta_310`; `FKS2.v8.table3_theta_320`; `FKS2.v8.table3_theta_330`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v6`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v6.old_pi` |

## `FKS2Numerics.v5.numerical_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v5.numerical_pi` → `FKS2Numerics.v5.challenge_numerical_pi` : `QRHCH2.v5.psi_refined_bound → FKS2.v6.table4_anchor_300 → FKS2Numerics.v5.numerical_pi` |
| Official designated `kind` | lean-noncompliant (`source-transport`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:49:11+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 7: `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧ SumStability.gamma 29 < 1 ∧ 0 ≤ FKS2Table4…`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS…`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧ FKS2Table4.scale = 1 / 2 ^ 58 ∧ (…`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa…`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧ FKS2Sca…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Table4.concrete_execution`, `FKS2Table4.output_unique`, `FKS2Table4.source_checked`, … (2 more); execution_witness: `FKS2Table4.concrete_execution`, `FKS2Table4.output_unique`, `FKS2Table4.verified_fks2_transport`; generic_correctness: `FKS2Table4.verified_fks2_transport`, `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `2d601713081c1f1a`, 28 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v5`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v5.numerical_pi` |

## `FKS2Numerics.v2.nu_asymp_e30_le`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v2.nu_asymp_e30_le` → `FKS2Numerics.v2.challenge_nu_asymp_e30_le` : `FKS2Numerics.v2.nu_asymp_e30_le` |
| Official designated `kind` | lean-noncompliant (`checked-source-stability`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:49:59+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43, FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Scal…`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44, FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2Sc…`); `FKS2Scalar.target_enclosure` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:113, token `native_decide`, decides `0 ≤ FKS2Scalar.uLo ∧ 0 ≤ FKS2Scalar.expLo (2 * FKS2Scalar.zLo) ∧ 0 ≤ F…`); `FKS2Scalar.z_exp_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:96, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Scalar.zLo) (FKS2Scalar.expLo (2 * FKS2Sc…`); `FKS2SumBridge.composition_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Whole.lean:36, token `native_decide`, decides `0 < FKS2SumBridge.prefactor ∧ 0 < FKS2SumBridge.sumCoefficient ∧ \|FKS2…`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧ FKS2SumBridge.trace2.steps.le…`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 …`); `FKS2SumBridge.integration_budget_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Integration.lean:42, token `native_decide`, decides `0 ≤ FKS2SumBridge.specError1 ∧ 0 ≤ FKS2SumBridge.specError2 ∧ 0 ≤ FKS2…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/fks2.c` sha256 `a0fde9cefcbf3064b4a47bf85889fc459db89b6c68ceabe579254ecbb34b06a6` embedded by NOTHING. Proofs: source_association: ; execution_witness: ; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `3bc115abdc4c2976`, 25 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build CalibrationSolution` rc 0 in `Solutions/FKS2Numerics.v2`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v2.nu_asymp_e30_le` |

## `FKS2Numerics.v3.calibration_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v3.calibration_bound` → `FKS2Numerics.v3.challenge_calibration_bound` : `FKS2Numerics.v3.calibration_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:50:22+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43, FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Scal…`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44, FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2Sc…`); `FKS2Scalar.target_enclosure` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:113, token `native_decide`, decides `0 ≤ FKS2Scalar.uLo ∧ 0 ≤ FKS2Scalar.expLo (2 * FKS2Scalar.zLo) ∧ 0 ≤ F…`); `FKS2Scalar.z_exp_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:96, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Scalar.zLo) (FKS2Scalar.expLo (2 * FKS2Sc…`); `FKS2SumBridge.composition_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Whole.lean:36, token `native_decide`, decides `0 < FKS2SumBridge.prefactor ∧ 0 < FKS2SumBridge.sumCoefficient ∧ \|FKS2…`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧ FKS2SumBridge.trace2.steps.le…`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 …`); `FKS2SumBridge.integration_budget_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Integration.lean:42, token `native_decide`, decides `0 ≤ FKS2SumBridge.specError1 ∧ 0 ≤ FKS2SumBridge.specError2 ∧ 0 ≤ FKS2…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v3/c/baseline.c` sha256 `9893599de3561ab8da90396530ad95a31ee0d2beaaabbdc3f20969ad34a912c9` embedded by NOTHING. Proofs: source_association: ; execution_witness: ; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `e8773edf23e10fcd`, 28 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v3`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v3.calibration_bound` |

## `FKS2Numerics.v3.baseline_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v3.baseline_bound` → `FKS2Numerics.v3.challenge_baseline_bound` : `FKS2Numerics.v3.baseline_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:50:45+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 8: `FKS2Correction.baseline_prefix_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:79, token `native_decide`, decides `StateT.run (FKS2Scalar.evalBlock FKS2Scalar.round64 FKS2Correction.bas…`); `FKS2Correction.composition_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Whole.lean:53, token `native_decide`, decides `0 < FKS2Correction.prefactor ∧ 0 < FKS2Correction.sumCoefficient ∧ \|FK…`); `FKS2Correction.target_enclosure` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:62, token `native_decide`, decides `0 ≤ FKS2Correction.uLo ∧ 0 ≤ FKS2Scalar.expLo (2 * FKS2Correction.zLo)…`); `FKS2Correction.z_exp_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:45, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Correction.zLo) (FKS2Scalar.expLo (2 * FK…`); `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43, FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Scal…`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44, FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2Sc…`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧ FKS2SumBridge.trace2.steps.le…`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 …`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v3/c/baseline.c` sha256 `9893599de3561ab8da90396530ad95a31ee0d2beaaabbdc3f20969ad34a912c9` embedded by `FKS2Correction.baselineSource`. Proofs: source_association: `FKS2Correction.baseline_prefix_execution`, `FKS2Correction.baseline_prefix_execution._native.native_decide.ax_1_1`, `FKS2Correction.baseline_sum_errors`, … (10 more); execution_witness: `FKS2Correction.baseline_prefix_execution`, `FKS2Correction.baseline_prefix_execution._native.native_decide.ax_1_1`, `FKS2Correction.baseline_sum_errors`, … (10 more); generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `3f78438ad2601446`, 23 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v3`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v3.baseline_bound` |

## `FKS2Numerics.v4.updated_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `FKS2Numerics.v4.updated_bound` → `FKS2Numerics.v4.challenge_updated_bound` : `FKS2Numerics.v4.updated_bound` |
| Official designated `kind` | lean-noncompliant (`source-verified`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:51:08+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 12: `FKS2Correction.baseline_prefix_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:79, token `native_decide`, decides `StateT.run (FKS2Scalar.evalBlock FKS2Scalar.round64 FKS2Correction.bas…`); `FKS2Correction.baseline_source_execution` (Solutions/FKS2Numerics.v3/FKS2Correction/Source300.lean:68, token `native_decide`, decides `FKS2Scalar.execute FKS2Correction.baselineProgram = some FKS2Correctio…`); `FKS2Correction.composition_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Whole.lean:53, token `native_decide`, decides `0 < FKS2Correction.prefactor ∧ 0 < FKS2Correction.sumCoefficient ∧ \|FK…`); `FKS2Correction.target_enclosure` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:62, token `native_decide`, decides `0 ≤ FKS2Correction.uLo ∧ 0 ≤ FKS2Scalar.expLo (2 * FKS2Correction.zLo)…`); `FKS2Correction.z_exp_checks` (Solutions/FKS2Numerics.v3/FKS2Correction/Enclosure.lean:45, token `native_decide`, decides `FKS2Scalar.expCheck (2 * FKS2Correction.zLo) (FKS2Scalar.expLo (2 * FK…`); `FKS2Scalar.sum1_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:31, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 43, FKS2Scalar.expCheck (FKS2Scalar.x1 k) (FKS2Scal…`); `FKS2Scalar.sum2_checks` (Solutions/FKS2Numerics.v2/applications/fks2_scalar_fp/lean/FKS2Scalar/Enclosure.lean:36, token `native_decide`, decides `∀ k ∈ Finset.Icc 3 44, FKS2Scalar.expCheck (FKS2Scalar.x2lo k) (FKS2Sc…`); `FKS2SumBridge.concrete_trace_checks` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Instances.lean:93, token `native_decide`, decides `FKS2SumBridge.trace1.steps.length = 41 ∧ FKS2SumBridge.trace2.steps.le…`); `FKS2SumBridge.extracted_sum_indexing` (Solutions/FKS2Numerics.v2/applications/fks2_sum_bridge/lean/FKS2SumBridge/Analysis.lean:28, token `native_decide`, decides `FKS2SumBridge.terms1.sum = ∑ k ∈ Finset.Icc 3 43, FKS2SumBridge.term1 …`); `FKS2Update.output_transport_check` (Solutions/FKS2Numerics.v4/FKS2Update/Source.lean:39, token `native_decide`, decides `\|FKS2Update.updatedQ - FKS2Update.coefficientRatio * FKS2Correction.ba…`); `FKS2Update.updated_budget_checks` (Solutions/FKS2Numerics.v4/FKS2Update/Result.lean:23, token `native_decide`, decides `0 < FKS2Update.coefficientRatio ∧ 0 ≤ FKS2Update.updatedError ∧ FKS2Up…`); `FKS2Update.updated_source_execution` (Solutions/FKS2Numerics.v4/FKS2Update/Source.lean:29, token `native_decide`, decides `FKS2Scalar.execute FKS2Update.updatedProgram = some FKS2Update.updated…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v4/c/updated.c` sha256 `83c208e7ae9a74b89945f6a90867a4252e465a75325efdac00aa0aaf489b1b5a` embedded by `FKS2Update.updatedSource`. Proofs: source_association: `FKS2Update.updated_source_error`, `FKS2Update.updated_source_execution`, `FKS2Update.updated_source_execution._native.native_decide.ax_1_1`; execution_witness: `FKS2Update.updated_source_error`, `FKS2Update.updated_source_execution`, `FKS2Update.updated_source_execution._native.native_decide.ax_1_1`; generic_correctness: `SumStability.c_sum_forward_error`, `SumStability.c_sum_forward_error_real`. Closure fingerprint `fbe34fb463dcc20b`, 26 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `d7dfcbe3d9c4`; `lake build Solution` rc 0 in `Solutions/FKS2Numerics.v4`; `python scripts/native_assisted/native_assisted_check.py check FKS2Numerics.v4.updated_bound` |

## `RamanujanGap.v2.loss_bound`

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

## `FKS2.v9.qrh_absolute_pi`

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

## `FKS2.v5.updated_theta`

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

## `@solution.ForwardRamanujan.forward`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@solution.ForwardRamanujan.forward` → `ForwardRamanujan.forward` : `QRHCH2.v5.psi_refined_bound → RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:55:54+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 12: `ForwardRamanujan.Old.budget_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Old.data).sum = ForwardRamanujan.Old.da…`); `ForwardRamanujan.Old.domain_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Old.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Old.enclosure_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:41, token `native_decide`, decides `ForwardRamanujan.Old.data.length = 7 ∧ ForwardRamanujan.Old.targets.le…`); `ForwardRamanujan.Old.execution_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.in…`); `ForwardRamanujan.Old.source_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Old.actualSource Forwa…`); `ForwardRamanujan.Old.suffix_check` (Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Old.program.scale = some…`); `ForwardRamanujan.Updated.budget_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:65, token `native_decide`, decides `(List.map abs ForwardRamanujan.Updated.data).sum = ForwardRamanujan.Up…`); `ForwardRamanujan.Updated.domain_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:43, token `native_decide`, decides `∀ r ∈ ForwardRamanujan.Updated.data, FKS2SumBridge.inputCheck r = true`); `ForwardRamanujan.Updated.enclosure_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:41, token `native_decide`, decides `ForwardRamanujan.Updated.data.length = 7 ∧ ForwardRamanujan.Updated.ta…`); `ForwardRamanujan.Updated.execution_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.progra…`); `ForwardRamanujan.Updated.source_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches ForwardRamanujan.Updated.actualSource F…`); `ForwardRamanujan.Updated.suffix_check` (Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral ForwardRamanujan.Updated.program.scale = …`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v1/c/baseline.c` sha256 `4f468d7f31d5bdd678f8692337ff6c21b0747828c0248685671c2a69b82f9be2` embedded by `ForwardRamanujan.Old.actualSource`; `Solutions/RamanujanNumerics.v2/c/updated.c` sha256 `3de9c2d75ed984719aee22f05f0217a605e72f419a737134f269074b34c09f5c` embedded by `ForwardRamanujan.Updated.actualSource`. Proofs: source_association: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.source_check`, `ForwardRamanujan.Old.source_check._native.native_decide.ax_1_1`, … (5 more); execution_witness: `ForwardRamanujan.Old.concrete_execution`, `ForwardRamanujan.Old.verified_with_domain`, `ForwardRamanujan.Updated.concrete_execution`, … (1 more); generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `180524921ed4bed4`, 38 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build ForwardRamanujanUpdate.Assembly` rc 0 in `Solutions/RamanujanNumerics.v2`; `python scripts/native_assisted/native_assisted_check.py check @solution.ForwardRamanujan.forward` |

## `@solution.FKS2Pair.assembled`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@solution.FKS2Pair.assembled` → `FKS2Pair.assembled` : `FKS2.v8.table3_theta_300 →   FKS2.v8.table3_theta_310 →     FKS2.v8.table3_theta_320 →       FKS2.v8.table3_theta_330 →         ZetaLogDeriv.v1.logDeriv_functional_equation →           GammaAsymptotics.v2.digamma_sub_log_isBigO_strip →             CH2.v2.proposition_2_4_upper →               CH2.v2.proposition_2_4_lower →                 ZetaLogDerivValues.v1.logDeriv_laurent_alternating →                   ZetaLogDerivValues.v1.logDeriv_neg_one →                     ZetaLogDerivValues.v1.logDeriv_two →                       ZetaLogDerivValues.v1.logDeriv_three_halves →                         CotangentSeries.v1.cot_series_zeta_values →                           ZeroCount.v1.rvm_error_bound →                             ZeroCount.v1.rvm_error_small →                               LowZeroes.v1.no_zeroes_below_first_ordinate →                                 ZetaHadamard.v1.logDeriv_partial_fractions →                                   OpenAIQRH.v1.zeta_seven_eighths →                                     FKS2.v6.table4_anchor_300 →                                       FKS2Numerics.v6.old_pi ∧                                         FKS2Numerics.v7.qrh_pi ∧                                           FKS2.v9.paired_absolute_pi ∧                                             FKS2.v9.strict_reconstructed_improvement ∧                                               FKS2.v9.strict_historical_improvement ∧ FKS2.v9.exact_allowance_ratios` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:56:30+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 16: `FKS2Pair.Old.boundary_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:21, token `native_decide`, decides `FKS2Pair.Old.scale = 1 / 2 ^ 48 ∧ FKS2Pair.Old.anchorHi ≤ FKS2Pair.Old…`); `FKS2Pair.Old.budget_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:93, token `native_decide`, decides `0 ≤ FKS2Pair.Old.totalError ∧ FKS2Pair.Old.totalError ≤ 1 / 10 ^ 26 ∧ …`); `FKS2Pair.Old.enclosure_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:29, token `native_decide`, decides `FKS2Pair.Old.data.length = 30 ∧ (∀ r ∈ FKS2Pair.Old.data, FKS2SumBridg…`); `FKS2Pair.Old.execution_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:57, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.inputs = some…`); `FKS2Pair.Old.exp_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:22, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Pair.Old.literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:38, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Pair.Old.oldProgram.scale = some FKS2Pair.O…`); `FKS2Pair.Old.source_tokens` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:54, token `native_decide`, decides `(SumStability.tokens FKS2Pair.Old.oldSource).isSome = true ∧ SumStabil…`); `FKS2Pair.Old.suffix_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:33, token `native_decide`, decides `FKS2Pair.Old.scaledOutput = FKS2Pair.Old.scale * FKS2Pair.Old.sumOut ∧…`); `FKS2Pair.qr_literal_scale_check` (Solutions/FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean:39, token `native_decide`, decides `FKS2Table4.loadLiteral FKS2Table4.selected.scale = some FKS2Table4.sca…`); `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Table4.budget_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:46, token `native_decide`, decides `0 ≤ SumStability.gamma 29 ∧ SumStability.gamma 29 < 1 ∧ 0 ≤ FKS2Table4…`); `FKS2Table4.execution_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:85, token `native_decide`, decides `List.mapM FKS2Table4.loadLiteral FKS2Table4.selected.inputs = some FKS…`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧ FKS2Table4.scale = 1 / 2 ^ 58 ∧ (…`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa…`); `FKS2Table4.source_checked` (Solutions/FKS2Numerics.v5/FKS2Table4/Program.lean:75, token `native_decide`, decides `FKS2Table4.sourceChecked FKS2Table4.selected = true`); `FKS2Table4.suffix_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Result.lean:29, token `native_decide`, decides `FKS2Table4.scaledOutput = FKS2Table4.scale * FKS2Table4.qsum ∧ FKS2Sca…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` sha256 `fcce411cc6c2a1c9bd64109f421dd94b8a4ed131eb02afd9d6da7c20e22cdc54` embedded by `FKS2Pair.Old.oldSource`; `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `FKS2Table4.selectedSource`. Proofs: source_association: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.source_checked`, `FKS2Pair.Old.source_tokens`, … (11 more); execution_witness: `FKS2Pair.Old.concrete_execution`, `FKS2Pair.Old.verified_old_transport`, `FKS2Pair.Updated.concrete_execution`, … (6 more); generic_correctness: `FKS2Pair.source_linked_transport_upper`, `FKS2Pair.sum_upper`, `FKS2Table4.verified_fks2_transport`, … (2 more). Closure fingerprint `fadead91faf0264c`, 107 project modules hashed |
| Mathematical hypotheses | `FKS2.v8.table3_theta_300`; `FKS2.v8.table3_theta_310`; `FKS2.v8.table3_theta_320`; `FKS2.v8.table3_theta_330`; `ZetaLogDeriv.v1.logDeriv_functional_equation`; `GammaAsymptotics.v2.digamma_sub_log_isBigO_strip`; `CH2.v2.proposition_2_4_upper`; `CH2.v2.proposition_2_4_lower`; `ZetaLogDerivValues.v1.logDeriv_laurent_alternating`; `ZetaLogDerivValues.v1.logDeriv_neg_one`; `ZetaLogDerivValues.v1.logDeriv_two`; `ZetaLogDerivValues.v1.logDeriv_three_halves`; `CotangentSeries.v1.cot_series_zeta_values`; `ZeroCount.v1.rvm_error_bound`; `ZeroCount.v1.rvm_error_small`; `LowZeroes.v1.no_zeroes_below_first_ordinate`; `ZetaHadamard.v1.logDeriv_partial_fractions`; `OpenAIQRH.v1.zeta_seven_eighths`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build FKS2PairReplay` rc 0 in `Solutions/FKS2Numerics.v7`; `python scripts/native_assisted/native_assisted_check.py check @solution.FKS2Pair.assembled` |

## `@pilot.CalibrationPilot.NewChain.new_chain`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pilot.CalibrationPilot.NewChain.new_chain` → `CalibrationPilot.NewChain.new_chain` : `QRHCH2.v5.psi_refined_bound →   (∀ x > Real.exp 9400,       DudekPlatt.v3.mainTerm x + (120 - CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6 < IEANTN.primeCounting x ∧         IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6) ∧     (∀ x > Real.exp 9401, (1 + 68431 / 5000 / Real.log x) * x ^ 2 / Real.log x ^ 6 < ForwardRamanujan.gap x) ∧       (∀ x > Real.exp 9401, ForwardRamanujan.loss x = 0) ∧ DudekPlatt.v4.ramanujan_inequality_9401` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:57:22+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 13: `CalibrationPilot.NewA.budget_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:67, token `native_decide`, decides `(List.map abs CalibrationPilot.NewA.data).sum = CalibrationPilot.NewA.…`); `CalibrationPilot.NewA.canon_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:39, token `native_decide`, decides `(ForwardRamanujan.tokens (ForwardRamanujan.renderProgram CalibrationPi…`); `CalibrationPilot.NewA.domain_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:45, token `native_decide`, decides `∀ r ∈ CalibrationPilot.NewA.data, FKS2SumBridge.inputCheck r = true`); `CalibrationPilot.NewA.enclosure_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:43, token `native_decide`, decides `CalibrationPilot.NewA.data.length = 7 ∧ CalibrationPilot.NewA.targets.…`); `CalibrationPilot.NewA.execution_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:52, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.i…`); `CalibrationPilot.NewA.source_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:36, token `native_decide`, decides `CalibrationPilot.sourceMatchesNamed CalibrationPilot.NewA.actualSource…`); `CalibrationPilot.NewA.suffix_check` (pilots/agentB-calibration/CalibrationPilot/NewA.lean:62, token `native_decide`, decides `ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.scale = som…`); `CalibrationPilot.NewB.budget_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:65, token `native_decide`, decides `(List.map abs CalibrationPilot.NewB.data).sum = CalibrationPilot.NewB.…`); `CalibrationPilot.NewB.domain_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:43, token `native_decide`, decides `∀ r ∈ CalibrationPilot.NewB.data, FKS2SumBridge.inputCheck r = true`); `CalibrationPilot.NewB.enclosure_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:41, token `native_decide`, decides `CalibrationPilot.NewB.data.length = 7 ∧ CalibrationPilot.NewB.targets.…`); `CalibrationPilot.NewB.execution_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:50, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewB.program.i…`); `CalibrationPilot.NewB.source_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:36, token `native_decide`, decides `ForwardRamanujan.sourceMatches CalibrationPilot.NewB.actualSource Cali…`); `CalibrationPilot.NewB.suffix_check` (pilots/agentB-calibration/CalibrationPilot/NewB.lean:60, token `native_decide`, decides `ForwardRamanujan.loadLiteral CalibrationPilot.NewB.program.scale = som…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `pilots/agentB-calibration/c/calibration_new.c` sha256 `f206bd817deab53b2fbaa38e4f7a84b5ad6958d5c5d625fc49eb407975be0568` embedded by `CalibrationPilot.NewA.actualSource`; `pilots/agentB-calibration/c/ramanujan_9401_new.c` sha256 `86d204a5a7ba913a43e8e387990b7ea60dc146e4eac336b98f9bffa2f35d8895` embedded by `CalibrationPilot.NewB.actualSource`. Proofs: source_association: `CalibrationPilot.NewA.concrete_execution`, `CalibrationPilot.NewA.source_check`, `CalibrationPilot.NewA.source_check._native.native_decide.ax_1_1`, … (5 more); execution_witness: `CalibrationPilot.NewA.concrete_execution`, `CalibrationPilot.NewA.verified_with_domain`, `CalibrationPilot.NewB.concrete_execution`, … (1 more); generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `9805000b3b6eb266`, 32 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build CalibrationPilot` rc 0 in `pilots/agentB-calibration`; `python scripts/native_assisted/native_assisted_check.py check @pilot.CalibrationPilot.NewChain.new_chain` |

## `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` → `CalibrationPilot.KernelChain.pi_calibrated_k` : `QRHCH2.v5.psi_refined_bound →   ∀ x > Real.exp 9400,     DudekPlatt.v3.mainTerm x + (120 - CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6 < IEANTN.primeCounting x ∧       IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + CalibrationPilot.NewChain.Δ) * x / Real.log x ^ 6` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T10:57:57+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `CalibrationPilot.KernelA.decode_check` (pilots/agentB-calibration/CalibrationPilot/KernelA.lean:36, token `native_decide`, decides `List.mapM ForwardRamanujan.loadLiteral CalibrationPilot.NewA.program.i…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `pilots/agentB-calibration/c/calibration_new.c` sha256 `f206bd817deab53b2fbaa38e4f7a84b5ad6958d5c5d625fc49eb407975be0568` embedded by `CalibrationPilot.NewA.actualSource`. Proofs: source_association: `CalibrationPilot.KernelA.execution_k`, `CalibrationPilot.KernelA.source_k`, `CalibrationPilot.KernelA.source_k._proof_1_1`; execution_witness: `CalibrationPilot.KernelA.execution_k`; generic_correctness: `ForwardRamanujan.source_linked_upper`, `ForwardRamanujan.sum_upper`, `SumStability.c_sum_forward_error`, … (1 more). Closure fingerprint `019456a6cec99c2f`, 28 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `ℝ`; `x > Real.exp 9400` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `20aabf4fcbf5`; `lake build CalibrationPilot` rc 0 in `pilots/agentB-calibration`; `python scripts/native_assisted/native_assisted_check.py check @pilot.CalibrationPilot.KernelChain.pi_calibrated_k` |

## `RamanujanNumerics.v3.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanNumerics.v3.epsilon_budget` → `RamanujanNumerics.v3.challenge_epsilon_budget` : `RamanujanNumerics.v3.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`shared-contract`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:05:21+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `RamanujanNumerics.v3.Provider.certificate` (Solutions/RamanujanNumerics.v3/RamanujanBudget/Provider.lean:45, token `native_decide`, decides `PVRamanujan.budgetCheck RamanujanNumerics.v3.Provider.source Ramanujan…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v3/c/budget.c` sha256 `dfbeabbd3113b24ee392de83311269d9ea858886878d70fa30759b56e885805b` embedded by `RamanujanNumerics.v3.Provider.source`. Proofs: source_association: `RamanujanNumerics.v3.Provider.certificate`, `RamanujanNumerics.v3.Provider.certificate._native.native_decide.ax_1_1`; execution_witness: `RamanujanNumerics.v3.Provider.certificate`, `RamanujanNumerics.v3.Provider.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.out_le_exact`, … (2 more). Closure fingerprint `0de54005fce4ec53`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build Solution` rc 0 in `Solutions/RamanujanNumerics.v3`; `python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v3.epsilon_budget` |

## `RamanujanGap.v3.loss_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanGap.v3.loss_bound` → `RamanujanGap.v3.challenge_loss_bound` : `DudekPlattNumerics.v5.pi_two_sided_qrh → RamanujanNumerics.v3.epsilon_budget → RamanujanGap.v3.loss_bound` |
| Official designated `kind` | none-yet (`solution`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✗/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:21:08+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 0 |
| Other unwanted axioms / sorry | none |
| Source / executable model | none configured. Proofs: source_association: ; execution_witness: ; generic_correctness: . Closure fingerprint `8ac04cafd1e5cf0b`, 10 project modules hashed |
| Mathematical hypotheses | `DudekPlattNumerics.v5.pi_two_sided_qrh`; `RamanujanNumerics.v3.epsilon_budget` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `3a4f63a9ae20`; `lake build Solution` rc 0 in `Solutions/RamanujanGap.v3`; `python scripts/native_assisted/native_assisted_check.py check RamanujanGap.v3.loss_bound` |

## `RamanujanGap.v3.gap_lower_bound`

| Field | Value |
|---|---|
| Claim / conclusion ID | `RamanujanGap.v3.gap_lower_bound` → `RamanujanGap.v3.challenge_gap_lower_bound` : `DudekPlattNumerics.v5.pi_two_sided_qrh → RamanujanNumerics.v3.epsilon_budget → RamanujanGap.v3.gap_lower_bound` |
| Official designated `kind` | none-yet (`solution`), unchanged |
| Evidence method | not-program-verified (S/A/E/C/M = ✗/✗/✗/✗/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:21:25+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 0 |
| Other unwanted axioms / sorry | none |
| Source / executable model | none configured. Proofs: source_association: ; execution_witness: ; generic_correctness: . Closure fingerprint `a557ca830c0ac765`, 10 project modules hashed |
| Mathematical hypotheses | `DudekPlattNumerics.v5.pi_two_sided_qrh`; `RamanujanNumerics.v3.epsilon_budget` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `3a4f63a9ae20`; `lake build Solution` rc 0 in `Solutions/RamanujanGap.v3`; `python scripts/native_assisted/native_assisted_check.py check RamanujanGap.v3.gap_lower_bound` |

## `@pv.PVRamanujan.V1.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVRamanujan.V1.epsilon_budget` → `PVRamanujan.V1.epsilon_budget` : `RamanujanNumerics.v1.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:06:32+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `PVRamanujan.V1.certificate` (pilots/pv-replay/PVReplay/Ramanujan.lean:38, token `native_decide`, decides `PVRamanujan.budgetCheck PVRamanujan.V1.source PVRamanujan.V1.program (…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v1/c/baseline.c` sha256 `4f468d7f31d5bdd678f8692337ff6c21b0747828c0248685671c2a69b82f9be2` embedded by `PVRamanujan.V1.source`. Proofs: source_association: `PVRamanujan.V1.certificate`, `PVRamanujan.V1.certificate._native.native_decide.ax_1_1`; execution_witness: `PVRamanujan.V1.certificate`, `PVRamanujan.V1.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.out_le_exact`, … (2 more). Closure fingerprint `7d8c8480e991d1cc`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVRamanujan.V1.epsilon_budget` |

## `@pv.PVRamanujan.V2.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVRamanujan.V2.epsilon_budget` → `PVRamanujan.V2.epsilon_budget` : `RamanujanNumerics.v2.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:07:01+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `PVRamanujan.V2.certificate` (pilots/pv-replay/PVReplay/Ramanujan.lean:58, token `native_decide`, decides `PVRamanujan.budgetCheck PVRamanujan.V2.source PVRamanujan.V2.program 1…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v2/c/updated.c` sha256 `3de9c2d75ed984719aee22f05f0217a605e72f419a737134f269074b34c09f5c` embedded by `PVRamanujan.V2.source`. Proofs: source_association: `PVRamanujan.V2.certificate`, `PVRamanujan.V2.certificate._native.native_decide.ax_1_1`; execution_witness: `PVRamanujan.V2.certificate`, `PVRamanujan.V2.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.out_le_exact`, … (2 more). Closure fingerprint `ef8a553615490149`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVRamanujan.V2.epsilon_budget` |

## `@pv.PVRamanujan.OldGrouped.epsilon_budget`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVRamanujan.OldGrouped.epsilon_budget` → `PVRamanujan.OldGrouped.epsilon_budget` : `RamanujanNumerics.v1.epsilon_budget` |
| Official designated `kind` | lean-noncompliant (`source-model`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:07:31+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 1: `PVRamanujan.OldGrouped.certificate` (pilots/pv-replay/PVReplay/Ramanujan.lean:76, token `native_decide`, decides `PVRamanujan.budgetCheck PVRamanujan.OldGrouped.source PVRamanujan.OldG…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/RamanujanNumerics.v2/c/oldgrouped.c` sha256 `8483747e8e1337fafb5357de243e0fc110fc9923f45b3d4b5afff10fae41a8d9` embedded by `PVRamanujan.OldGrouped.source`. Proofs: source_association: `PVRamanujan.OldGrouped.certificate`, `PVRamanujan.OldGrouped.certificate._native.native_decide.ax_1_1`; execution_witness: `PVRamanujan.OldGrouped.certificate`, `PVRamanujan.OldGrouped.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.out_le_exact`, … (2 more). Closure fingerprint `b83ee84f52134db4`, 16 project modules hashed |
| Mathematical hypotheses | none (pure arithmetic or closed) |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVRamanujan.OldGrouped.epsilon_budget` |

## `@pv.PVTable4.QRH.qrh_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVTable4.QRH.qrh_pi` → `PVTable4.QRH.qrh_pi` : `QRHCH2.v5.psi_refined_bound → FKS2.v6.table4_anchor_300 → FKS2Numerics.v7.qrh_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-qrh`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:08:01+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 4: `FKS2Table4.analytic_checks` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:23, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `FKS2Table4.input_certificate` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:31, token `native_decide`, decides `FKS2Table4.inputValues.length = 30 ∧ FKS2Table4.scale = 1 / 2 ^ 58 ∧ (…`); `FKS2Table4.scaled_cells_upper` (Solutions/FKS2Numerics.v5/FKS2Table4/Certificates.lean:100, token `native_decide`, decides `FKS2Table4.inputValues.sum = ∑ j ∈ Finset.range 30, FKS2Table4.inputVa…`); `PVTable4.QRH.certificate` (pilots/pv-replay/PVReplay/Table4.lean:46, token `native_decide`, decides `PVCore.upperCheck PVTable4.QRH.source PVTable4.QRH.program (1 / 10 ^ 3…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` sha256 `0685e913a08957ec941753e0e4ffd3de33756e828976c7ae2332545e378313e7` embedded by `PVTable4.QRH.source`. Proofs: source_association: `PVTable4.QRH.certificate`, `PVTable4.QRH.certificate._native.native_decide.ax_1_1`; execution_witness: `PVTable4.QRH.certificate`, `PVTable4.QRH.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.le_bound_of_check`, … (2 more). Closure fingerprint `25e028cc7890cb8c`, 30 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVTable4.QRH.qrh_pi` |

## `@pv.PVTable4.Old.old_pi`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVTable4.Old.old_pi` → `PVTable4.Old.old_pi` : `FKS2.v8.table3_theta_300 →   FKS2.v8.table3_theta_310 →     FKS2.v8.table3_theta_320 → FKS2.v8.table3_theta_330 → FKS2.v6.table4_anchor_300 → FKS2Numerics.v6.old_pi` |
| Official designated `kind` | lean-noncompliant (`source-model-old`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:08:45+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 4: `FKS2Pair.Old.boundary_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldResult.lean:21, token `native_decide`, decides `FKS2Pair.Old.scale = 1 / 2 ^ 48 ∧ FKS2Pair.Old.anchorHi ≤ FKS2Pair.Old…`); `FKS2Pair.Old.enclosure_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:29, token `native_decide`, decides `FKS2Pair.Old.data.length = 30 ∧ (∀ r ∈ FKS2Pair.Old.data, FKS2SumBridg…`); `FKS2Pair.Old.exp_checks` (Solutions/FKS2Numerics.v6/FKS2Pair/OldInputs.lean:22, token `native_decide`, decides `FKS2Scalar.expCheck 1 (FKS2Scalar.expLo 1) (FKS2Scalar.expHi 1) = true…`); `PVTable4.Old.certificate` (pilots/pv-replay/PVReplay/Table4.lean:84, token `native_decide`, decides `PVCore.upperCheck PVTable4.Old.source PVTable4.Old.program (4 / 10 ^ 2…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` sha256 `fcce411cc6c2a1c9bd64109f421dd94b8a4ed131eb02afd9d6da7c20e22cdc54` embedded by `PVTable4.Old.source`. Proofs: source_association: `PVTable4.Old.certificate`, `PVTable4.Old.certificate._native.native_decide.ax_1_1`; execution_witness: `PVTable4.Old.certificate`, `PVTable4.Old.certificate._native.native_decide.ax_1_1`; generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.le_bound_of_check`, … (2 more). Closure fingerprint `2a64a180ef7b3d02`, 27 project modules hashed |
| Mathematical hypotheses | `FKS2.v8.table3_theta_300`; `FKS2.v8.table3_theta_310`; `FKS2.v8.table3_theta_320`; `FKS2.v8.table3_theta_330`; `FKS2.v6.table4_anchor_300` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | absent |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVTable4.Old.old_pi` |

## `@pv.PVPilot.Updated.gap_exceeds_leading`

| Field | Value |
|---|---|
| Claim / conclusion ID | `@pv.PVPilot.Updated.gap_exceeds_leading` → `PVPilot.Updated.gap_exceeds_leading` : `QRHCH2.v5.psi_refined_bound →   ∀ x > Real.exp 9401, (1 + 68431 / 5000 / Real.log x) * x ^ 2 / Real.log x ^ 6 < ForwardRamanujan.gap x` |
| Official designated `kind` | n/a (not a node conclusion) (`-`), unchanged |
| Evidence method | lean-verified-program (S/A/E/C/M = ✓/✓/✓/✓/✓) |
| Native-assisted gate | **passed** (2026-11-04T23:09:27+00:00) |
| Standard axioms | Classical.choice, Quot.sound, propext |
| Extra finite native facts | 2: `PVPilot.Updated.certificateA` (pilots/pv-replay/PVReplay/Chain.lean:50, token `native_decide`, decides `PVCore.upperCheck PVPilot.Updated.sourceA PVPilot.Updated.programA (1 …`); `PVPilot.Updated.certificateB` (pilots/pv-replay/PVReplay/Chain.lean:68, token `native_decide`, decides `PVRamanujan.budgetCheck PVPilot.Updated.sourceB PVPilot.Updated.progra…`) |
| Other unwanted axioms / sorry | none |
| Source / executable model | `pilots/agentB-calibration/c/calibration_new.c` sha256 `f206bd817deab53b2fbaa38e4f7a84b5ad6958d5c5d625fc49eb407975be0568` embedded by `PVPilot.Updated.sourceA`; `pilots/agentB-calibration/c/ramanujan_9401_new.c` sha256 `86d204a5a7ba913a43e8e387990b7ea60dc146e4eac336b98f9bffa2f35d8895` embedded by `PVPilot.Updated.sourceB`. Proofs: source_association: `PVPilot.Updated.certificateA`, `PVPilot.Updated.certificateA._native.native_decide.ax_1_1`, `PVPilot.Updated.certificateB`, … (1 more); execution_witness: `PVPilot.Updated.certificateA`, `PVPilot.Updated.certificateA._native.native_decide.ax_1_1`, `PVPilot.Updated.certificateB`, … (1 more); generic_correctness: `PVCore.certified`, `PVCore.exact_le_out`, `PVCore.le_bound_of_check`, … (3 more). Closure fingerprint `11ca08c99968cf1a`, 32 project modules hashed |
| Mathematical hypotheses | `QRHCH2.v5.psi_refined_bound`; `ℝ`; `x > Real.exp 9401` |
| Real-world trust boundary | restricted C / binary64 RN model of the token-matched source; Lean compiler + runtime for the native facts and their library implementations; C compiler, OS and hardware not modelled |
| Official Comparator receipt | n/a (not a node conclusion) |
| Reproduction | Lean 4.34.0-rc2 (leanprover/lean4:v4.34.0-rc2), Mathlib `71a80585ee49`, repo `5ccad03d24a1`; `lake build PVReplay` rc 0 in `pilots/pv-replay`; `python scripts/native_assisted/native_assisted_check.py check @pv.PVPilot.Updated.gap_exceeds_leading` |

