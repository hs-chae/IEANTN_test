# Agent A's scoped-winner provider in Agent B's gate and contracts

- **What was handed over.** Agent A's `poc/scoped-winner-a@e0c1ceb` (on `qrh-2pv` since ivy's
  push) with `reports/PV_PROVIDER_HANDOFF.json`: "independently_agentB_gate_checked": false,
  prerequisites "review patch against B branch and jointly build", "lift original
  source-object/interface definitions to a Mathlib-only core vocabulary before node Conclusions
  can refer to them".
- **What was done.** Merged without conflicts (Agent A adds files and changes `README.md` only),
  built in Agent B's worktree, checked by Agent B's gate with a new backend, and composed with
  Agent B's budget program. Agent A's files are unchanged.

## 1. Joint build

| Item | Result |
|---|---|
| Merge `qrh-2pv@e0c1ceb` into `agentB/pv-structural` | no conflicts; pushed as `qrh-2pv@fa70b6a` (fast-forward) |
| `lake build Solution` in `Solutions/ScopedWinnerA.v1` | 9174 jobs, 16 min wall, peak 7.3 GB per process |
| Heavy dependency | `CH2.v6` (408 density certificates) was already built in this worktree; `lake build --no-build` reported it up to date |
| `#print axioms ScopedWinnerA.pi_00947147` | `propext`, `Classical.choice`, `Quot.sound` and 49 `native_decide` facts, as Agent A reports |

## 2. Agent B's gate on Agent A's endpoint

The gate's evidence method was C-only: its source check (S) looks for an `include_str` literal
equal to a C file. Agent A's program is a generated Lean expression (`Expr` rows) evaluated by an
exact dyadic interval evaluator; there is no C file. The gate now accepts per-endpoint `backends`.
For `lean-dyadic-expr`:

| Check | What it requires | Agent A's endpoint |
|---|---|---|
| S | each program constant is in the proof closure and defined in a pinned Lean source file whose SHA256 matches | `ScopedWinnerA.Certificate.program` (Certificate.lean), `WinnerDensityA.HeightProgram.program` (HeightProgram.lean); `WinnerProgramA/Program.lean` also pinned |
| A | a theorem associating the program syntax with its real denotation | `WinnerDensityA.HeightProgram.program_semantics` |
| E | an execution witness under the reviewed evaluator (`WinnerProgramA.run`, `Exec`, `acceptUpper`) | `ScopedWinnerA.Certificate.checked` (native, 16,385 cells) |
| C | the reviewed generic soundness theorem | `WinnerProgramA.source_linked_upper` |
| M | the endpoint is a mathematical statement | `HasPowerLogBound Eπ 0.00947147 0 (7/8) (e^300)` |

- **Result.** Passed, method `lean-verified-program`, 49 native facts, none rejected. Each fact's
  owning theorem, module, source hash and `native_decide` token were audited, as for Agent B's
  endpoints.
- **What the 49 facts are.** One is the executed program (`Certificate.checked`); 48 are finite
  scalar and profile checks (`WinnerHeightProfiles` 32, `WinnerOriginalScalars` 7,
  `WinnerHeightKernel0–3` 8, `WinnerEulerGamma` 1).
- **Unit tests.** Five for the new backend: a pinned program passes; an edited program source,
  a program outside the proof closure and an unreviewed backend name fail; with two backends,
  both must pass.

## 3. Composition with Agent B's budget program

`pilots/pv-twobackend` (see `IEANTN_PV_COMPOSITION.md` §4): Agent A's π bound, a kernel-checked
data link to the five-term shape, and the shared-contract budget program at
`(0, 122.5, 300, 301)`. Chain theorem `PVTwoBackend.gap_exceeds_leading`: under Agent A's seven
inputs, `(1 + 7.72/log x) x²/log⁶x < gap(x)` for `x > e^301`. Gate: both backends pass, 50 native
facts (49 + 1).

## 4. Not done: Agent A's result as a node

- **First exact blocker.** Two of the seven inputs are Agent A's own source packages, defined in
  `Solutions/`: `WinnerDirectKernel.OriginalCHJSource` and
  `WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000)`. `PrimaryInputs` is a structure of
  eight propositions over at least 14 solution-level definitions (`mollifier`, `meanOne`,
  `meanTwo`, `sourceMoment`, `scaledCriticalF`, `rightVExact`, `rawRectangleBound`, `cSevenAt`,
  `sourceCEight`, `sourceFdiff`, `sourceOmega`, `shifted`, `rightLine`, `height`).
- **Why it was not attempted.** Node conclusions must not import `Solutions/`. A node would
  need those definitions restated in core vocabulary, which changes the interface of Agent A's
  result; the prompt forbids mutating it, and the handoff lists this lift as Agent A's
  prerequisite.
- **Same blocker, smaller case.** The optional Table 4 node for `Bsafe(Q) ≤ 5·10⁻¹⁶` (a prompt-1
  proposal) needs `FKS2Pair.Bsafe` and `qProfile` in core vocabulary, so it was not added
  either.
