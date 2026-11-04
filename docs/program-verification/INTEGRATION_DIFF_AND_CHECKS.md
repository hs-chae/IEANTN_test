# Integration diff and checks: native-assisted / lean-verified-program

- **Branch.** Local `agentB/native-assisted` on `hs-chae/IEANTN_test`.
- **Base.** `551f552`, which is `agentB/integration-readability`, itself on `qrh-2pv@0945fe9`.
- **Nothing pushed.** No PR and no receipt.

## 1. What changed

| Path | Change | Why |
|---|---|---|
| `scripts/ieantn.py` | +121/−1 lines. `PV_EVIDENCE` path; `VERIFICATION_METHODS`, `PV_*` constants; `pv_attestation`, `check_pv_evidence` (added to `check`); validation of the optional `verification_method` field; opt-in page rows | Schema support that is backward compatible and fail-closed. No change to kinds, trust, status, graph, fingerprints or challenges |
| `scripts/native_assisted/` (new) | `Extract.lean`, `native_assisted_check.py`, `semantics.json`, `endpoints.json`, `controls.py`, `inventory.py`, `final_tables.py`, `README.md` | The local gate, its reviewed registries, controls and generators |
| `tests/test_native_assisted.py` (new, 19 tests) | Gate policy on synthetic extracts | Pure Python; runs in the normal suite |
| `tests/test_pv_metadata.py` (new, 16 tests) | Sidecar validation, the `verification_method` field, page rows | Uses the existing `FixtureRepo` |
| `pv-evidence/*.native-assisted.local.json` (new) | One local attestation per audited endpoint, plus `controls/CONTROLS.json`; `.work/` is git-ignored | Machine-readable, non-official evidence |
| `docs/program-verification/` (new) | `NATIVE_ASSISTED_DESIGN.md`, `PROGRAM_VERIFICATION_INVENTORY.md` (generated), `PV_ENDPOINT_TABLES.md` (generated), `PV_HUMAN_READABLE_GUIDE.md`, this file, `FINAL_RESTRUCTURING_REPORT.md` | Design, inventory, per-endpoint tables, guide, report |
| Non-frozen node metadata | See §3 | Records the method and the gate result where the attestation supports them |
| `IEANTN/Nodes/FKS2Numerics/v3/Conclusions.lean`, `v4/Conclusions.lean` | Docstrings only (+23/−2): a mathematics-first explanation of `calibration_bound`, `baseline_bound` and `updated_bound`; the two `−` lines are docstring closings moved down | Readability of PoC 1. Statements unchanged (`fingerprint --check` 0) |

Nothing else was modified. In particular:
- no `Conclusions.lean` statement (only the docstrings above), no `Challenge.lean`, no `fingerprints.json`;
- no file in `receipts/`;
- no frozen file (the forward and Table 4 manifests, 49 files, are re-hashed in §4);
- no file under `Solutions/`;
- no `kind` or `designated` value.

## 2. Classification: old and new

The authoritative per-endpoint rows are in
[PROGRAM_VERIFICATION_INVENTORY.md](PROGRAM_VERIFICATION_INVENTORY.md). In summary:

| Endpoint | Old metadata | New: evidence method | New: native-assisted |
|---|---|---|---|
| `RamanujanNumerics.v1.epsilon_budget` (frozen) | `lean-noncompliant` / `source-model` | `lean-verified-program` | passed (6 native facts) |
| `RamanujanNumerics.v2.epsilon_budget` | `lean-noncompliant` / `source-model` | `lean-verified-program` | passed (6) |
| `FKS2Numerics.v6.old_pi` (frozen) | `lean-noncompliant` / `source-model-old` | `lean-verified-program` | passed (8) |
| `FKS2Numerics.v7.qrh_pi` | `lean-noncompliant` / `source-model-qrh` | `lean-verified-program` | passed (8) |
| `FKS2Numerics.v5.numerical_pi` | `lean-noncompliant` / `source-transport` | `lean-verified-program` | passed (7) |
| `FKS2Numerics.v3.baseline_bound` | `lean-noncompliant` / `source-verified` | `lean-verified-program` | passed (8) |
| `FKS2Numerics.v4.updated_bound` | `lean-noncompliant` / `source-verified` | `lean-verified-program` | passed (12) |
| `FKS2Numerics.v3.calibration_bound` | `lean-noncompliant` / `source-verified` | **`not-program-verified`** (no C source in the proof) | passed (8) |
| `FKS2Numerics.v2.nu_asymp_e30_le` | `lean-noncompliant` / `checked-source-stability` | **`not-program-verified`** (no C source in the proof) | passed (8) |
| `RamanujanGap.v2.loss_bound`, `FKS2.v9.qrh_absolute_pi`, `FKS2.v5.updated_theta` | `none-yet` / `solution` | `not-program-verified` (consumer; takes the budget as a hypothesis) | passed (0: standard axioms only) |
| `ForwardRamanujan.forward`, `FKS2Pair.assembled` (solution theorems) | not nodes | `lean-verified-program` | passed (12 / 16) |
| `CalibrationPilot.NewChain.new_chain`, `KernelChain.pi_calibrated_k` (pilot) | not nodes | `lean-verified-program` | passed (13 / 1) |

## 3. Metadata edits on non-frozen nodes

Seven conclusions in six files changed, all by pure additions (+29 lines, no deletions).
The list is reproduced in FINAL_RESTRUCTURING_REPORT.md. Each edit does at most two things:
- adds `verification_method: lean-verified-program` to a designated `lean-noncompliant`
  justification, when its attestation says `passed` and `lean-verified-program`;
- appends one sentence to its `note`.

Frozen nodes are not edited. Their pages show the gate rows from the sidecar.

## 4. Checks

| Check | Result |
|---|---|
| `python -m unittest discover -s tests` | 346 tests OK (311 existing + 35 new) |
| Pages, before (`551f552`) vs after, whole network | 11 of 113 pages differ, each one an attested node (`evidence/page_diff.sh`); 102 are byte-identical |
| `scripts/native_assisted/controls.py` | 10 of 10 as expected; repository tree hash unchanged |
| `ieantn.py fingerprint --check` / `gen-challenges --check` | 0 / 0 (statements and challenges unchanged) |
| `ieantn.py check` | Exit 1 **only** for the 49 inherited receipt-provenance diagnostics (`teorth/IEANTN` vs `hs-chae/IEANTN_test`), as before. The new `program-verification evidence` check passes |
| Freeze manifests | forward 30/30, Table 4 19/19 byte-identical (re-hashed at `a6c76d9`) |

The controls:

| Control | Expected | Observed |
|---|---|---|
| allowed `native_decide` fact | gate passes; method `not-program-verified` | ✓ |
| custom axiom | fails | ✓ "custom or unknown axiom" |
| fake native-named axiom | fails | ✓ "declaration range does not point at a `native_decide` token" |
| `sorry` | fails | ✓ `sorryAx` |
| numeric inequality without a source link | gate passes; method fails S/A/E/C | ✓ |
| program facts without the correctness theorem | method fails C only | ✓ |
| genuine program-linked theorem | passes, `lean-verified-program` | ✓ (7 native facts) |
| source hash mismatch | method fails S | ✓ |
| changed executed input literal | plain `lake build` replays a **stale** object (exit 0); the gate detects the stale embedded source (S fails); a forced rebuild fails at `source_check` | ✓ |
| wrong selected program (`scale` changed) | build fails at `source_check` | ✓ |

Per-run details (commands, timings, root `.olean` paths, log tails) are inside each attestation
under `run`.

## 5. Not reached, and why

- **No official receipts.**
  - The native facts remain, so the endpoints cannot pass Comparator.
  - Removing them needs kernel-checkable replacements. The A→B pilot's `KernelA` shows that
    everything except decimal literal decoding can be done in the kernel.
- **Official `lean-verified-program` kind not implemented.**
  - A receipt-backed subtype needs an upstream schema and Comparator policy decision.
  - The method is recorded as an optional, validated field instead.
- **Lake does not trace `include_str`.**
  - This is a build-system issue, recorded and not fixed here.
  - A fix would be a Lake-level input declaration, or a hash assertion inside the Lean module.
- **Independent reader not run.**
  - No approval was given for a separate reviewer agent.
  - The reader-question answers in the final report are a **non-independent self-audit**.
