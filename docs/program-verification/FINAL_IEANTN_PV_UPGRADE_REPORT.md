# Final report: reusable, composable program verification in IEANTN

- **Branch.** Local `agentB/pv-structural` on `hs-chae/IEANTN_test`, from `3388918`. Nothing
  pushed, no PR, no receipt.
- **Attestations.** Local research reports, not IEANTN verification receipts.

## What someone can now do that was cumbersome before

1. **Update a numerical provider by stating the change, not by copying a proof.**
   - **How.** Register the new parameters in `scripts/native_assisted/providers.json`, then run
     `pv_update.py plan / generate / build / gate`. The C file, a data-only Lean module and a
     lakefile are generated; the build checks one certificate; the gate audits it.
   - **Done for real.** `RamanujanNumerics.v2 → v3`: the budget's range moves from `x > e^3915` to
     `x > e^401` (`A 3914 → 400`, `Y 3915 → 401`), allowance 9.101 → 9.988. The new consumer
     `RamanujanGap.v3` gives the loss and gap bounds on that range.
   - **Before.** The same change meant a 116-code-line copied instance file with 18 theorems and
     6 native facts. **Now:** 26 generated code lines, 2 theorems, 1 native fact.
2. **Add an instance without re-proving the program.**
   - **Shared proof.** `Solutions/ProgramVerification` proves the execution, the loop error bound,
     the suffix rounding and a certificate's soundness once. That is 382 code lines in 4 modules,
     standard axioms only.
   - **Instance.** An instance is its file, literals, one certificate and a theorem of 2–10 lines.
   - **Measured on real instances.** The four existing Ramanujan instances go from 116 to 10–13
     code lines, and from 6 to 1 native fact each. Table 4 old and QRH go from 8 to 4 native facts:
     the 3 analytic enclosure facts are kept as they were.
3. **Trust that a changed C file is rebuilt.** The generated lakefile declares the selected file
   as an `input_file` that the provider library `needs`. Lake then reruns and recompiles; without
   it, Lake replays a stale build. Both directions are shown by controls A and B.
4. **Compose two executed programs with an explicit, checked data link.**
   - The A→B′ pilot chain is now two shared-contract stages. B′'s parameter `M = 120 + Δ` is
     linked to A's certified `Δ` by a kernel-checked equality.
   - Same chain theorem; native facts 13 → 2. Feeding B′ any other `Δ` fails to elaborate
     (`tests/LinkMismatch.lean`).
5. **Read the program evidence on the node page.** Each program-verified conclusion now shows:
   - the selected file and its SHA256;
   - the shared theorems that prove it;
   - the trust in plain words;
   - other checked routes to the same statement;
   - the registered change from its previous version.

## Results

| Endpoint | Gate | Method | Native facts | Official kind |
|---|---|---|---|---|
| `RamanujanNumerics.v3.epsilon_budget` (new) | passed | lean-verified-program | 1 | `lean-noncompliant` |
| `RamanujanGap.v3.loss_bound`, `gap_lower_bound` (new) | passed | not-program-verified (consumers) | 0 | `none-yet` |
| replays of `RamanujanNumerics.v1`, `.v2`, grouped | passed | lean-verified-program | 1 each | — (second routes) |
| replays of `FKS2Numerics.v7` (QRH), `.v6` (old) | passed | lean-verified-program | 4 each | — (second routes) |
| `PVPilot.Updated.gap_exceeds_leading` | passed | lean-verified-program | 2 | — (not a node) |
| the 16 earlier endpoints | passed (unchanged) | 11 lean-verified-program, 5 not | as before | unchanged |

**Checks.**

- `check` fails only on the 49 inherited provenance items.
- Fingerprints and challenges unchanged; freeze 49/49.
- 350 unit tests pass.
- Controls: 12/12, plus the link control.
- Page diff: every difference explained.

Details: `PV_TEST_AND_REPLAY_LOG.md`.

## The distinctions the task asked for

| Distinction | Here |
|---|---|
| Structural change vs nodes that benefit | **Structural:** the shared package, the update workflow, freshness through `input_file`/`needs`, the gate's second-route support, the page rows. **Nodes:** `RamanujanNumerics.v3` and `RamanujanGap.v3` are new versions. Existing nodes get second checked routes and richer pages; their designated proofs are unchanged. |
| Generic code reused vs proof reused | Proved theorems are applied, not restated: `PVCore.certified`, `exact_le_out`, `le_bound_of_check` and `PVRamanujan.budget_of_check` appear in every instance's axiom closure. Table 4's analytic enclosures are mathematics and stay with Table 4. |
| Conditional theorem vs concrete witness | `PVCore.certified` derives `Exec` of the actual file with the evaluated output, a concrete witness. `exact_le_out` is the conditional theorem over any execution. |
| Source-verified C vs Lean expression | Everything here is restricted C over binary64 with round-to-nearest. Agent A's dyadic evaluator was not integrated (P2, below). |
| Assumption vs native axiom vs receipt vs hardware | Assumptions are node imports, for example `DudekPlattNumerics.v5.pi_two_sided_qrh`. Native axioms are listed per endpoint. There are no receipts. The compiler and hardware are not modelled. |
| Stronger bound vs scoped comparison | `RamanujanNumerics.v3` has a *larger* allowance on a *larger* range. Ramanujan's inequality for `x > e^401` was already `DudekPlatt.v5.ramanujan_401` (bridged, standard axioms). The program route reaches it again with weaker trust and is recorded only as a second route. No best-bound claim is made. |

## Honest limitations

- **The loop error bound is not generalized.** It still needs 1–64 entries, each in `[2⁻⁴⁰, 1]`.
  The suffix certificate covers only positive normal intermediates with exponent in `[−100, 100]`.
- **One family adapter: Ramanujan.** Table 4 uses the generic bridge. No weighted sum with
  per-entry scales and no dot product was added, since no current application needs one.
- **A second composition of two executed programs was not completed.** First blocker: no other
  pair of executed providers has a data link. Table 4's allowance gives a Ramanujan coefficient
  only after a factor `log⁵x ≈ 7·10¹⁹` at `e^9400`.
- **Agent A's dyadic backend was not integrated (P2).** Its source is pinned at
  `poc/winner-program-a-v2@69b7506`, 49 native facts.
  - First blockers: build cost, since a comparable closure compiled about 120 jobs at about 10 GB
    each and was stopped; and the gate's S check, which needs a C file.
  - What the gate would need: a `backend` field per endpoint; a fingerprint check on the
    generated `Expr` constant in place of the C-file hash; and that backend's association,
    execution and correctness names in `semantics.json`. Its 49 facts are `native_decide`, so the
    existing provenance audit would apply unchanged.
- **The π premise of `RamanujanGap.v3` is not discharged in a replay.** Its solution's closure is
  the heavy build above.
- **Independence.** The new-user test is a self-audit; a reviewer subagent was not approved.
- **Cost.** Not measured beyond seconds per build. Cold Mathlib was not built.

## Decisions for the owner

1. **The shared package.** Accept `Solutions/ProgramVerification` as a solution-facing package,
   not a node, with its name and its narrow requirements. This sets the pattern for future shared
   proof components.
2. **Source freshness.** Make `input_file` + `needs` the rule for providers that embed sources.
   Decide whether to retrofit the non-frozen published providers (`RamanujanNumerics.v2`,
   `FKS2Numerics.v5`, `v7`), whose lakefiles were deliberately left alone.
3. **The new versions.** Keep `RamanujanNumerics.v3` and `RamanujanGap.v3` in the network, and
   decide whether v2 should be deprecated in their favour; v2 keeps the smaller allowance.
4. **Local evidence metadata.** Adopt the `verification_method` field and the `pv-evidence/`
   sidecars, which are local and non-official, or keep them on the fork.
5. **Page generation.** The generator is CI-owned. Accept the extra page rows: program and
   backend, proving theorems, trust, second routes, and the registered change.

## Commits on `agentB/pv-structural`

- `c9553ec` Shared program-verification contract (PVCore) and two re-derived families
- `46583c3` Update workflow: RamanujanNumerics.v3 provider generated from a registered change; RamanujanGap.v3
- `2831035` A→B′ composition on the shared contract; gate attestations for the new endpoints
- `5ccad03` Keep the shared package minimal; move replays to pilots/pv-replay
- `b36ca0e` Controls (12/12), link-mismatch control, docs, handoff, regenerated inventory and tables
- `3a4f63a` RamanujanGap.v3: drop the duplicate of DudekPlatt.v5.ramanujan_401
- `4f94ea3` Re-attest the RamanujanGap.v3 consumers at the corrected commit
- `da75940` Gate: its own outputs in pv-evidence/ do not make the tree dirty; page shows up to 5 proving theorems
- the final commit adds this report, the test log and the regenerated derived documents

---

## 한국어 요약 (Korean executive summary)

**결론.** IEANTN에 공유 program-verification 계약(`Solutions/ProgramVerification`)과 provider update workflow를 넣었다. 공식 trust semantics는 바꾸지 않았다. Push, PR, receipt 생성은 하지 않았다.

- **Provider 갱신이 쉬워졌다.** `providers.json`에 변경을 등록하고 `pv_update.py`를 실행하면 C 파일, 데이터 모듈, lakefile이 생성되고 build와 gate까지 실행된다. 실제로 `RamanujanNumerics.v2 → v3`를 만들었다. 범위는 `x > e^3915`에서 `x > e^401`로 바뀌었고, allowance는 9.101에서 9.988이 되었다. 인스턴스 코드는 116줄에서 26줄로, native fact는 6개에서 1개로 줄었다.
- **증명을 재사용한다.** 실행, loop 오차, suffix rounding, certificate soundness를 한 번만 증명했다. 표준 axiom만 쓴다. Ramanujan 인스턴스 4개는 6개에서 1개로, Table 4 두 개는 8개에서 4개로 native fact가 줄었다.
- **C 파일 변경이 확실히 다시 build된다.** `input_file` + `needs`를 쓰면 Lake가 다시 build한다. 없으면 stale 결과를 그대로 쓴다. 두 경우 모두 control로 확인했다.
- **두 program의 합성.** A→B′ chain을 공유 계약 위의 두 단계와 kernel이 확인하는 data link로 다시 증명했다. native fact는 13개에서 2개로 줄었다. 다른 Δ를 넣으면 elaborate되지 않는다.
- **Node page에서 바로 보인다.** 선택된 C 파일과 hash, 증명 theorem, 평이한 trust 설명, 다른 route, 버전 변경 내용을 보여 준다.
- **검사.** `check`는 기존 49개 provenance 진단 외에는 실패하지 않는다. Fingerprint와 challenge, freeze 49/49는 그대로다. 테스트 350개, control 12/12가 통과한다.
- **정정.** `x > e^401`에서의 Ramanujan 부등식은 이미 `DudekPlatt.v5.ramanujan_401`(bridged, 표준 axiom)에 있었다. `RamanujanGap.v3`에서 이 결론은 뺐고, program 경로는 더 약한 second route로만 남겼다.
- **남은 것.** loop 오차 bound는 아직 일반화하지 않았다. 두 번째 실행 program 합성과 Agent A의 dyadic backend 통합(P2)은 하지 못했고, 첫 blocker를 정확히 기록했다.
