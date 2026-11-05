# Second round: push, then every open item

- **Request.** hschae, 2026-11-05 02:20 UTC: "push, and just try everything as hard as possible",
  after a list of open items: Agent A's provider, the π premise of `RamanujanGap.v3`, KernelB, a
  chunked sum, the `input_file` retrofit, three maintainer proposals and a reviewer.
- **Pushed.** `qrh-2pv` `e0c1ceb..fa70b6a` (fast-forward): Agent B's 23 commits merged with Agent
  A's five, no conflicts. The work below is pushed on top at the end of the round.
- **Status.** Every listed item is done except Agent A's result as a node, which has an exact
  blocker (§2). One new defect was found and fixed for Agent B's nodes (§3).
- **Attestations.** Local research reports, not IEANTN verification receipts. No official `kind`,
  `designated` value, statement, fingerprint or receipt changed.

## 1. What was done

| Item | Result | Trust (beyond `propext`, `Classical.choice`, `Quot.sound`) |
|---|---|---|
| Agent A's provider in Agent B's gate | `ScopedWinnerA.pi_00947147` passes with a new `lean-dyadic-expr` backend check | 49 native facts, as Agent A reports |
| Two-backend chain | Agent A's π bound → kernel-checked link → C budget program at `(0, 122.5, 300, 301)`: `(1 + 7.72/log x)·x²/log⁶x < gap(x)` for `x > e^301`, under Agent A's seven inputs | 50 native facts (49 + 1) |
| π premise of `RamanujanGap.v3` | discharged by `DudekPlattNumerics.v5`'s solution; `gap_from_psi`, `loss_from_psi`, `gap_from_qrh` | 1 native fact (the v3 provider) |
| KernelB | the A→B′ chain with both certificates on the kernel route | 2 native facts, both literal decoding |
| Chunked sums | `PVCore.Chunked`: any number of entries, one frozen `sum` call per chunk of ≤ 64; Table 4 in two chunks proves `FKS2Numerics.v7.qrh_pi` again; a 100-entry test | 4 and 1 native facts |
| `input_file` retrofit | `RamanujanNumerics.v2` (3 files), `FKS2Numerics.v5` (covers `v7`) | controls pass both ways |
| Page generator | node README link; "Local proof" row for unjustified conclusions with a complete local proof; `IEANTN_REPOSITORY_URL`/`_BRANCH` | — |
| Reviewer | one independent reader for the tutorial and the new docs | see §4 |

**Measured.**
- **Builds.** Agent A's provider, 9174 jobs in 16 min, peak 7.3 GB per process; the kernel-route
  chain module, 177 s and 22.7 GB; the π-premise replay, 17 s; the chunked instances, 5.2 s.
- **Shared code.** `PVCore.Kernel`, `PVRamanujan.Kernel` and `PVCore.Chunked`, standard axioms
  only.
- **Gate.** All endpoints re-run at one clean commit: see `PV_TEST_AND_REPLAY_LOG.md`.

## 2. Not done

- **Agent A's result as a node.** Three of its seven inputs are solution-level, in `Solutions/`:
  `OriginalCHJSource`, `PrimaryInputs` (over at least 14 solution-level definitions) and the height
  constant of `RiemannHypothesisUpTo`. The other four are node conclusions. A node may not import `Solutions/`, and restating those definitions in core
  vocabulary changes Agent A's interface. That is Agent A's listed prerequisite, so it was left
  to Agent A. `AGENT_A_PROVIDER_INTEGRATION.md` §4 has the list.
- **A Table 4 numerical node** (an optional prompt-1 proposal): it needs `FKS2Pair.Bsafe` and
  `qProfile` in core vocabulary, so it has the same blocker.
- **`RamanujanGap.v2`'s status.** It now shows a "Local proof" row, and `check-graph` warns that
  its status is still `awaiting-solution`. Changing it is the owner's call; `RamanujanGap.v3`
  (Agent B's node) was set to `awaiting-verification`.

## 3. Found and fixed: a solution's own `Solution` module was shadowed

- **Symptom.** `ieantn.py progress RamanujanGap.v3` reported its challenge theorems as unknown
  constants.
- **Cause.** Lake puts the root package's build directory last on `LEAN_PATH`. In a solution
  that requires other solution projects, `import Solution` therefore loads another package's
  `Solution` module. On this fork, `FKS2Numerics.v5`, `v7`, `RamanujanNumerics.v3` and
  `RamanujanGap.v3` all resolved `Solution` to `Solutions/CH2.v1`. `scripts/verify-comparator.sh`
  runs Comparator under `lake env` in the solution directory, so it very likely resolves
  `solution_module` the same way. Comparator itself was not run.
- **Fixed.**
  - `ieantn.py progress` puts the solution's own build directory first, and no longer crashes
    when `comparator.json` is missing.
  - `RamanujanNumerics.v3` and `RamanujanGap.v3` name uniquely named modules as
    `solution_module`.
  - The progress tool then recorded `remaining_holes: 0` on `RamanujanGap.v2` (4 conclusions)
    and `v3` (2).
- **Why it matters for v3.** `RamanujanGap.v3`'s challenge theorems use standard axioms only, so
  Comparator could verify them; it now has a module name it can find.
- **Not fixed: the other QRH solutions.** Their `comparator.json` still say `Solution`. This
  matters only when Comparator is run on them. The numerical providers among them are
  `lean-noncompliant` and cannot receive receipts in any case.

## 4. Independent reader

One Fable subagent, read-only, no builds, no paid APIs. It followed the contributor tutorial as a
new contributor, checked the quoted Lean names and signatures, and reviewed the composition and
Agent A documents against the code. Findings and what was changed: `PV_TEST_AND_REPLAY_LOG.md`
("Independent reader").

## 5. Decisions for the owner

1. **Comparator module names.** Adopt unique `solution_module` names for solutions that require
   other solutions, or change the verification script to put the solution first on `LEAN_PATH`.
2. **`RamanujanGap.v2` status.** `awaiting-verification`, as the new warning suggests, or leave it.
3. **Agent A's node.** Ask Agent A to lift `OriginalCHJSource` and `PrimaryInputs` into core
   vocabulary, if its result should become a node.
4. **The two-backend chain.** Keep it as a pilot, or promote the stage-B provider (a pure
   numerical statement) to a node.
5. **Earlier decisions still open.** The 5 in `FINAL_IEANTN_PV_UPGRADE_REPORT.md`; the shared
   package and the page rows are pushed with this round.

---

## 한국어 요약 (Korean executive summary)

**결론.** 요청받은 항목은 모두 처리했다. 단, Agent A의 결과를 node로 만드는 일은 정확한 blocker가 있어 하지 않았다. 작업은 `qrh-2pv`에 push했다(force와 PR 없음). 공식 trust semantics, statement, receipt는 바꾸지 않았다.

- **Agent A provider.** Agent B의 gate에 dyadic backend 검사를 추가했다. `ScopedWinnerA.pi_00947147`이 통과했다(native fact 49개, Agent A의 보고와 같다).
- **Two-backend chain.** Agent A의 π bound를 kernel이 확인하는 연결로 C budget program에 넣었다. Agent A의 7개 입력 아래에서 `x > e^301`이면 `gap(x) > (1 + 7.72/log x)·x²/log⁶x`가 성립한다(native fact 50개). Ramanujan 부등식 자체는 이미 network에 `e^145` 이상으로 있으므로 새 결과가 아니라 합성의 시연이다.
- **π premise.** `RamanujanGap.v3`의 π premise를 실제 solution으로 해소했다(native fact 1개).
- **KernelB.** A→B′ chain의 native fact 2개가 이제 둘 다 literal decoding뿐이다. 나머지는 kernel이 확인한다(빌드 177초, 22.7 GB).
- **Chunked sum.** 64개를 넘는 합도 같은 frozen loop로 증명한다. Table 4를 15개씩 두 덩어리로 나눠 같은 정리를 다시 증명했고, 100개짜리 test도 gate를 통과했다.
- **Freshness.** `RamanujanNumerics.v2`와 `FKS2Numerics.v5`(v7 포함)에 `input_file` + `needs`를 적용했다. Control은 두 방향 모두 통과했다.
- **새로 찾은 결함.** 다른 solution을 require하는 solution에서 `import Solution`이 남의 `Solution` module(`CH2.v1`)을 읽는다. Lake가 자기 package를 `LEAN_PATH` 맨 뒤에 두기 때문이다. Comparator도 그렇게 될 가능성이 높다(직접 실행하지는 않았다). `progress` 도구와 v3 node들은 고쳤고, 다른 QRH solution은 결정 사항으로 남겼다.
- **남은 것.** Agent A 결과의 node화(입력 7개 중 3개가 Solutions 정의라 core vocabulary로 옮겨야 한다), Table 4 수치 node(같은 blocker), `RamanujanGap.v2` status(소유자 결정).
