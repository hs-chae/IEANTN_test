# Composition of verified computations

Two compositions now run on the shared contract.

- **A→B′ (two executed programs).** The pilot chain is rewritten as two shared-contract stages
  joined by a data link (`pilots/pv-replay/PVReplay/Chain.lean`).
- **π input → budget program → consumer (node graph).** The new nodes `RamanujanNumerics.v3` and
  `RamanujanGap.v3` compose through ordinary node imports. The replay
  `RamanujanGap.v3.gap_from_pi` discharges the budget premise with the actual provider.

## 1. A→B′: what is checked, and where

The chain proves, under the QRH-derived θ bound `QRHCH2.v5.psi_refined_bound`:

> for every `x > e^9401`, `(1 + 13.6862/log x)·x²/(log x)⁶ < gap(x)`, where
> `gap(x) = (e·x/log x)·π(x/e) − π(x)²`.

```
θ input ──▶ stage A  calibration_deviation   (7 pieces ×4096)      certificate A
            │  A's output contract:  Σ pieces ≤ Δ = 0.0914            le_bound_of_check
            ▼
            calibrated π:  π(x) ∈ S₅(x) + (120 ± Δ)·x/log⁶x, x > e^9400   (analytic, unchanged)
            │  data link:   B′'s M = 120 + Δ   (kernel equality of rationals)
            ▼
         stage B′ ramanujan_epsilon_bound    (7 terms ×4096 − 134 − 0)  certificate B′
            │  B′'s input contract: budget at (0, 120+Δ, 9400, 9401)   budget_of_check
            ▼
         gap bound on x > e^9401                                     (analytic, unchanged)
```

The required checks, one by one:

| Requirement | How it is met |
|---|---|
| A's output satisfies B's real input contract | B′'s literals are decimal strings in its own C file; they load as binary64 values (`loadLiteral`). B′'s certificate is checked at exactly the parameters `(m, M, A, Y) = (0, 120.0914, 9400, 9401)`. The link `M = 120 + Δ` is `CalibrationPilot.NewChain.M_eq`, an equality of rationals the kernel checks. The scale changes from A's 4096 to B′'s 4096 (8192 in the old chain); each stage's scale is its own literal, checked by its own certificate. |
| Both programs have source identity and a concrete execution | Each certificate includes `sourceMatches` against its actual file. `PVCore.certified` gives `Exec` of that file with the evaluated output: a concrete witness, not a conditional. |
| B's input cannot be replaced by a desired fact, and A's theorem is not an axiom | A enters only through `stageA`, a theorem from A's certificate. B′ enters only through `stageB`, a theorem from B′'s certificate. The only non-standard axioms of the chain theorem are the two certificate evaluations. |
| The consumer depends on both programs | `#print axioms PVPilot.Updated.gap_exceeds_leading` gives `propext`, `Classical.choice`, `Quot.sound`, `certificateA…native…`, `certificateB…native…`. |

**Before and after.** The chain theorem is the same as `CalibrationPilot.NewChain.gap_exceeds_leading`.
It had 13 native facts (A 7, B′ 6) from two instance files of 90 and 116 code lines. It now has 2,
from one 64-line file that also contains the analytic glue.

**Negative control for the link.** `pilots/pv-replay/tests/LinkMismatch.lean` tries to feed B′ the
deviation `0.0913` instead of A's certified `0.0914`. The link equality is false and the file does
not elaborate; see `PV_TEST_AND_REPLAY_LOG.md`.

## 2. The node-graph composition

`RamanujanGap.v3.gap_lower_bound` imports two conclusions:

- `DudekPlattNumerics.v5.pi_two_sided_qrh`: analytic, QRH-derived;
- `RamanujanNumerics.v3.epsilon_budget`: one executed program.

Its solution uses standard axioms only. The replay

```lean
theorem RamanujanGap.v3.gap_from_pi (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    RamanujanGap.v3.gap_lower_bound :=
  RamanujanGap.v3.challenge_gap_lower_bound hp RamanujanNumerics.v3.Provider.epsilon_budget
```

discharges the budget with the actual generated provider: 3 standard axioms plus 1 native fact. The
π premise stays a premise, exactly as in the node graph.

**Ramanujan's inequality on this range already exists.** `DudekPlatt.v5.ramanujan_401` states it,
for every `x > e^401`, and its designated justification is a bridge in the core build with
standard axioms only. The replay `RamanujanGap.v3.ramanujan_401_second_route` reaches that same
statement through the program-checked budget. It is a second route with weaker trust: one native
fact. It is not a new result, and `RamanujanGap.v3` therefore states only the quantitative loss
and gap bounds.

**Why the π premise is not discharged here.** Importing `DudekPlattNumerics.v5`'s own solution
compiles the CH2.v6 density certificates, about 120 parallel Lean jobs at about 10 GB each. That
build was stopped. This is a build-cost blocker, not a mathematical one.

**How the graph shows it.** The node graph records only mathematical dependencies. The program
evidence is recorded per conclusion, in `pv-evidence/` and on the node page; no new nodes were
made for programs.

## 3. A second composition of two executed programs: not completed

**First exact blocker.** No other pair of executed providers in the network has a data dependency.

- **Table 4 → Ramanujan.** Table 4's output is an `Eπ` allowance `≤ 5·10⁻¹⁶` above `e^330`. The
  Ramanujan budget needs π in the form `S₅(x) + c·x/log⁶x` near `e^9400`. Converting the first
  into the second costs a factor `log⁵x`: `5·10⁻¹⁶·9400⁵ ≈ 3.7·10⁴ ≫ 120`.
- **PoC 1.** Its programs feed analytic theorems, not other programs.

A genuine second executed chain needs a new numerical obligation downstream of Table 4. That is
new mathematics, not integration.

**What exists instead.** Two independent compositions of different kinds:

- A→B′: two programs and a data link;
- the v3 nodes: an analytic provider, a program and a consumer.

The A→B′ interface (output contract, data link, input contract) is three named theorems that a
third stage can reuse.
