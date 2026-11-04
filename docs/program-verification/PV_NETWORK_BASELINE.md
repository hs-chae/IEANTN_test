# Program-verification baseline: where the network stood before the upgrade

- **Base.** Branch `agentB/native-assisted` at `3388918`, which is `qrh-2pv@0945fe9` plus Agent B's
  integration (`551f552`) and native-assisted (`3388918`) work.
- **Reproduced in this task.** All 16 earlier endpoints were re-run through the gate at `9b748db`
  and pass with the same methods and native-fact counts. Check, fingerprints and freeze are
  unchanged (`PV_TEST_AND_REPLAY_LOG.md`).
- **Measured by** `agentB/evidence/pv3/census.py` (declaration names per file) and
  `census_after.py` (code lines: non-blank, comments and docstrings excluded).

## 1. The program-verified providers and their consumers

| Conclusion | Official kind (designated) | Selected source | Execution witness | Error proof | Consumer |
|---|---|---|---|---|---|
| `RamanujanNumerics.v1.epsilon_budget` (frozen) | `lean-noncompliant` / `source-model` | `Solutions/RamanujanNumerics.v1/c/baseline.c` | `ForwardRamanujan.Old.concrete_execution` | `ForwardRamanujan.source_linked_upper` | `RamanujanGap.v1` |
| `RamanujanNumerics.v2.epsilon_budget` | `lean-noncompliant` / `source-model` | `…v2/c/updated.c` | `ForwardRamanujan.Updated.concrete_execution` | same | `RamanujanGap.v2` |
| `FKS2Numerics.v6.old_pi` (frozen) | `lean-noncompliant` / `source-model-old` | `…FKS2Numerics.v6/c/fks2_table4_transport_old.c` | `FKS2Pair.Old.concrete_execution` | `FKS2Pair.source_linked_transport_upper` | `FKS2.v8` |
| `FKS2Numerics.v7.qrh_pi` | `lean-noncompliant` / `source-model-qrh` | `…FKS2Numerics.v5/c/fks2_table4_transport.c` | `FKS2Pair.Updated.concrete_execution` | `FKS2Table4.verified_fks2_transport` | `FKS2.v9` |
| `FKS2Numerics.v5.numerical_pi` | `lean-noncompliant` / `source-transport` | same file | `FKS2Table4.concrete_execution` | same | `FKS2.v5` |
| Pilot A→B′ chain (not a node) | — | `pilots/agentB-calibration/c/*.c` | `NewA/NewB.concrete_execution` | `ForwardRamanujan.source_linked_upper` | `NewChain.gap_exceeds_leading` |

Premises are node imports: `DudekPlattNumerics.v5.pi_two_sided_qrh` (QRH-derived π coefficients
119/131 above `e^400`) for the Ramanujan v2 consumers; `QRHCH2.v5.psi_refined_bound` and
`FKS2.v6.table4_anchor_300` for Table 4 QRH; four `FKS2.v8` Table 3 θ bounds for Table 4 old.
PoC 1 (`FKS2Numerics.v2`–`v4`) keeps its earlier classification: two conclusions have no C source
in their proofs and stay `not-program-verified`.

## 2. One program shape, rebuilt three times

Every executed program above has the same shape: the frozen `sum` loop over a static array, one
multiplication by a scale literal, then a few literal additions or subtractions.

| Application | Its own copy of the shape | Suffix |
|---|---|---|
| Table 4 | `FKS2Table4.TransportProgram`, `renderTransport`, `ExecTransport`; again `FKS2Pair.ExecTransportAt` | `+ anchor + point + tail` |
| Ramanujan | `ForwardRamanujan.Program`, `renderProgram`, `Exec`, own scanner with `-` | `− 134 − max(0, m)` |
| Pilot A | `CalibrationPilot.renderNamed`, `ExecNamed` | `− 0 − 0` |

**Duplication census.** 59 declaration names are defined in two or more of the 15 application
files (`census_before.json`):

- **Glue proofs copied per instance.** `concrete_execution` appears in 11 files; `suffix_roundoff`
  in 10; `selected_execution_witness`, `suffix_IEEE` in 9; `verified_with_domain`,
  `checked_domain` in 8; `verified_transport`, `terms_cast`, `upper_as_targets`, `certified_upper`
  and `epsilon_bound` in 6.
- **Infrastructure written 2–3 times.** `loadLiteral`, `runSum`, `chainCheck`, `chain_sound`
  (Table 4 and Ramanujan); `kernel_from_chain`, `sourceMatches`, `SuffixIEEE`, `forwardError`
  (Ramanujan and `FKS2Pair`); `output_unique` and `sum_upper` (3 copies each).
- **Each Ramanujan-shape instance file** (6 of them) has 116 code lines, 39 declarations, 18
  theorems and 6 native facts. The pilot's program A files have 90 code lines and 7 native facts.

**Where the contracts genuinely differ.** All instances use binary64 with the frozen
`SumStability` loop. Its proved bound needs 1–64 entries, each a binary64 value in
`[2⁻⁴⁰, 1]`. The suffixes differ only in signs and constants. Agent A's provider is a different
backend: exact dyadic interval evaluation of a generated Lean expression, with no C source and no
binary64 (§4).

## 3. The path a reader sees, and where the program evidence was lost

```
node statement (Conclusions.lean) ──imports──▶ premise conclusions
      │
      └── designated justification (formalization.yaml: kind lean-noncompliant + a prose note)
             │
             └── Solutions/<node>/ … C file, 6–8 native facts, 120-line glue  ← not on the page
```

- Before Agent B's earlier work, the page showed the kind and a note only. The native-assisted
  branch added four rows: evidence method, local gate, official kind and receipt.
- The selected file, its hash and the proof that consumes it were still found only by reading
  `Solutions/`.
- A version change, such as v1 to v2, was explained only in prose.

## 4. Agent A's dyadic backend (read, not built)

- **Source.** `codex/ivy/qrh-winner-v2-20261104`, branch `poc/winner-program-a-v2` at `69b7506`.
- **Native facts.** 49 for the final theorem, per its `NATIVE_FACTS.json`.
- **Program.** Generated Lean `Expr` syntax with exact dyadic interval evaluation.
  - `WinnerDensityA.HeightProgram.program 300 100 8192`: 8,193 cells, 100-bit precision.
  - Generic soundness: `WinnerProgramA.source_linked_upper`.
  - Execution: `WinnerDensityA.HeightCertificate.checked`.
- **Why it was not built.** The comparable `DudekPlattNumerics.v5` closure, tried here, compiles
  the CH2.v6 density certificates: about 120 parallel Lean jobs at about 10 GB each. That build
  was stopped. See `FINAL_IEANTN_PV_UPGRADE_REPORT.md` for what the gate would need.

## 5. Before-state measures

| Measure | Value |
|---|---|
| Code lines per Ramanujan-shape instance | 116 (6 files) |
| Native facts per instance | Ramanujan 6; Table 4 8; pilot A 7, B′ 6 (chain 13) |
| Declaration names defined in ≥ 2 application files | 59 |
| Steps to add a changed instance | copy a 122-line file, regenerate data with the frozen generator, edit names, re-prove the glue |
| Rebuild on a changed C file | none: Lake replays the stale embedded source (checked again in `controls_pv.py`, control B) |
| Program evidence on the node page | method, gate, kind, receipt rows; no file, hash or theorem |
