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
| `docs/program-verification/` (new) | `NATIVE_ASSISTED_DESIGN.md`, `PROGRAM_VERIFICATION_INVENTORY.md` (generated), `PV_HUMAN_READABLE_GUIDE.md`, this file, `FINAL_RESTRUCTURING_REPORT.md` | Design, inventory, guide, report |
| Non-frozen node metadata | See §3 | Records the method and the gate result where the attestation supports them |

Nothing else was modified. In particular:
- no `Conclusions.lean` statement, no `Challenge.lean`, no `fingerprints.json`;
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
| others | see the inventory | see the inventory | see the inventory |

## 3. Metadata edits on non-frozen nodes

See the "applied" list produced by `evidence/apply_pv_metadata.py`, reproduced in
FINAL_RESTRUCTURING_REPORT.md. Each edit does at most two things:
- adds `verification_method: lean-verified-program` to a designated `lean-noncompliant`
  justification, when its attestation says `passed` and `lean-verified-program`;
- appends one sentence to its `note`.

Frozen nodes are not edited. Their pages show the gate rows from the sidecar.

## 4. Checks

| Check | Result |
|---|---|
| `python -m unittest discover -s tests` | 346 tests OK (311 existing + 35 new) |
| Pages, before (`551f552`) vs after, whole network | Only the pages of conclusions with an attestation differ; the other 110 of 113 pages are byte-identical |
| `scripts/native_assisted/controls.py` | 10 of 10 as expected; repository tree hash unchanged |
| `ieantn.py fingerprint --check` / `gen-challenges --check` | 0 / 0 (statements and challenges unchanged) |
| `ieantn.py check` | Exit 1 **only** for the 49 inherited receipt-provenance diagnostics (`teorth/IEANTN` vs `hs-chae/IEANTN_test`), as before. The new `program-verification evidence` check passes |
| Freeze manifests | forward 30/30, Table 4 19/19 byte-identical |

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
