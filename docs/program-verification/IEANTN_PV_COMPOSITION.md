# Composition of verified computations

Three compositions now run on the shared contract.

- **A→B′ (two executed programs, one backend).** The pilot chain is rewritten as two
  shared-contract stages joined by a data link (`pilots/pv-replay/PVReplay/Chain.lean`). It is
  parametric in its two stage certificates; the kernel route proves both with literal decoding as
  the only native computation (`PVReplay/KernelChain.lean`, §1).
- **π input → budget program → consumer (node graph).** The new nodes `RamanujanNumerics.v3` and
  `RamanujanGap.v3` compose through ordinary node imports. The replays discharge the budget
  premise with the actual provider and the π premise with its actual solution (§2).
- **Two backends (§4).** Agent A's dyadic π provider, a kernel-checked data link, and the
  shared-contract C budget program: a three-stage chain with two executed programs of different
  kinds (`pilots/pv-twobackend`).

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
| A's output satisfies B's real input contract | B′'s literals are decimal strings in its own C file; they load as binary64 values (`loadLiteral`). B′'s certificate is checked at exactly the parameters `(m, M, A, Y) = (0, 120.0914, 9400, 9401)`. The link `M = 120 + Δ` is `CalibrationPilot.NewChain.M_eq`, an equality of rationals the kernel checks. Both stages use scale 4096 (the old stage B′ used 8192, `OldB.lean`); each stage's scale is its own literal, checked by its own certificate. |
| Both programs have source identity and a concrete execution | Each certificate includes `sourceMatches` against its actual file. `PVCore.certified` gives `Exec` of that file with the evaluated output: a concrete witness, not a conditional. |
| B's input cannot be replaced by a desired fact, and A's theorem is not an axiom | A enters only through `stageA`, a theorem from A's certificate. B′ enters only through `stageB`, a theorem from B′'s certificate. The only non-standard axioms of the chain theorem are the two certificate evaluations. |
| The consumer depends on both programs | `#print axioms PVPilot.Updated.gap_exceeds_leading` gives `propext`, `Classical.choice`, `Quot.sound`, `certificateA…native…`, `certificateB…native…`. |

**Before and after.** The chain theorem is the same as `CalibrationPilot.NewChain.gap_exceeds_leading`.
It had 13 native facts (A 7, B′ 6) from two instance files of 90 and 116 code lines. It now has 2,
from one file of 78 code lines that also contains the analytic glue and is parametric in the two
stage certificates (`gap_of`).

**Negative control for the link.** `pilots/pv-replay/tests/LinkMismatch.lean` tries to feed B′ the
deviation `0.0913` instead of A's certified `0.0914`. The link equality is false and the file does
not elaborate; see `PV_TEST_AND_REPLAY_LOG.md`.

**Kernel route (KernelB).** The chain theorem is `gap_of (hA : CertA) (hB : CertB) hpsi`, for any
proofs of the two stage certificates. `PVPilot.Updated.gap_exceeds_leading` passes the native
certificates (2 native facts, each a whole shared check). `PVPilot.Kernel.gap_exceeds_leading`
passes kernel-route certificates: per stage, one native fact `PVCore.decode program = some (…)`
(decimal literals to rationals) and `decide +kernel` for everything else — source tokens, the
binary64 summation chain, the suffix rounding, the enclosure, the budget. Axioms: the three
standard ones plus `decodeA`, `decodeB`. Cost: the module takes 177 s and 22.7 GB peak; the native
route takes seconds. Gate: passed, `lean-verified-program`, 2 native facts.

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

**The π premise, discharged.** `DudekPlattNumerics.v5`'s solution closure includes the CH2.v6
density certificates. A first build fanned out to about 120 Lean jobs at up to 10 GB each and was
stopped, but its heavy part had already finished: `lake build --no-build` later reported the whole
closure up to date. The replays now import it:

```lean
theorem RamanujanGap.v3.gap_from_psi (hpsi : QRHCH2.v5.psi_refined_bound) :
    RamanujanGap.v3.gap_lower_bound :=
  RamanujanGap.v3.gap_from_pi (DudekPlattNumerics.v5.challenge_pi_two_sided_qrh hpsi)
theorem RamanujanGap.v3.gap_from_qrh (htr : CH2.v9.refined_transfer)
    (hq : OpenAIQRH.v1.zeta_seven_eighths) : RamanujanGap.v3.gap_lower_bound
```

and `loss_from_psi` for the loss bound. Axioms: the three standard ones plus the v3 provider's
one native fact. Building the replay took 17 s. The remaining premises are the leaves
`ieantn.py report` lists for the node: literature and numerical inputs (`OpenAIQRH.v1`,
`ZeroCount.v1`, `ZetaHadamard.v1`, `LowZeroes.v1`, `ZetaLogDerivValues.v1`) and the unreceipted
`CH2.v9`/`CotangentSeries.v1` steps; they stay premises, as in the node graph.

**How the graph shows it.** The node graph records only mathematical dependencies. The program
evidence is recorded per conclusion, in `pv-evidence/` and on the node page; no new nodes were
made for programs.

## 3. A second composition of two executed programs: done with Agent A's provider (§4)

Among Agent B's C providers, no other pair has a data dependency; this is still true:

- **Table 4 → Ramanujan.** Table 4's output is an `Eπ` allowance `≤ 5·10⁻¹⁶` above `e^330`. The
  Ramanujan budget needs π in the form `S₅(x) + c·x/log⁶x` near `e^9400`. Converting the first
  into the second costs a factor `log⁵x`: `5·10⁻¹⁶·9400⁵ ≈ 3.7·10⁴ ≫ 120`.
- **PoC 1.** Its programs feed analytic theorems, not other programs.

Agent A's scoped-winner provider supplies the missing link: a bound on `π` against `Li` that is
fine enough to feed the Ramanujan budget directly.

## 4. Two backends: Agent A's dyadic provider → data link → C budget program

`pilots/pv-twobackend`. `Li(x) = ∫₂^x dt/log t` is IEANTN's offset logarithmic integral (not `li`).
Chain theorem, under Agent A's seven inputs, which are explicit hypotheses:

- node conclusions: `ZeroCount.v1.rvm_error_bound`, `ZeroCount.v1.rvm_error_small`,
  `LowZeroes.v1.no_zeroes_below_first_ordinate`, and `ZetaZeroFreeHalfPlane (7/8)`, which is
  `OpenAIQRH.v1.zeta_seven_eighths` by definition;
- solution-level: `WinnerDirectKernel.OriginalCHJSource`,
  `WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000)`, and
  `RiemannHypothesisUpTo WinnerOriginalScalars.height` (its height constant is solution-level).

> for every `x > e^301`, `(1 + 7.72/log x) · x²/log⁶x < gap(x)`, where
> `gap(x) = (e·x/log x)·π(x/e) − π(x)²`.

| Stage | What it is | Trust |
|---|---|---|
| A | `ScopedWinnerA.pi_00947147` (Agent A, unchanged): exact dyadic interval evaluation of a generated Lean expression over 16,385 cells, then Agent A's analytic transfer. Output contract `HasPowerLogBound Eπ 0.00947147 0 (7/8) (e^300)`, i.e. `|π(x) − Li(x)| ≤ 0.00947147·x^(7/8)/log x` | 49 native facts |
| link | `pi_input_of_powerLog`: `Li = mainTerm − K₅ + 120·I₆` (five integrations by parts from 2), `I₆` bounded both ways (five more, and a split at `√x`). At `log x ≥ 300` the `I₆` tail costs up to `2.47·x/log⁶x`, which is why `M = 122.5`; the endpoint constants, the `√x` term and Agent A's error are each at most `10⁻³·x/log⁶x`. Result: `π(x) > mainTerm(x) + 119.99·x/log⁶x` on `x > e^300` and `π(x) < mainTerm(x) + 122.5·x/log⁶x` on `x > e^301` (the shape of `ForwardRamanujan.PiInput`) | standard axioms |
| B | the shared-contract budget program regenerated at `(m, M, A, Y) = (0, 122.5, 300, 301)` (`c/budget_301.c`; certified output upper value 112.2612, stated bound 112.27), then `PVRamanujan.budget_shift` to `m = 119.99` | 1 native fact |
| consumer | `ForwardRamanujan.gap_from_budget`, unchanged; allowance `112.27 − 119.99 = −7.72` | standard axioms |

- **Why `m = 0` in the program.** At `m = 119.99` the budget is negative (−7.72); the shared
  rounding certificate covers positive normal intermediates only. The program runs at `m = 0`
  (output 112.26) and `m` is subtracted exactly in the proof, as the calibration pilot did.
- **Gate.** Both backends pass: `lean-dyadic-expr` for stage A (pinned program sources,
  `program_semantics`, `Certificate.checked`, `source_linked_upper`) and `restricted-c-binary64`
  for stage B. 50 native facts, none rejected.
- **Scope.** Three of the seven inputs are solution-level, so the chain cannot be a node
  (`AGENT_A_PROVIDER_INTEGRATION.md` §4). Ramanujan's inequality itself is already a network
  conclusion above `e^145` (`DudekPlatt.v6.ramanujan_145`: a local proof, no receipt, from
  `QRHCH2.v2`'s density frontier).
  What is new is the composition, and a quantitative gap bound with a negative allowance on
  `x > e^301`; `RamanujanGap.v3` has `+9.988` on `x > e^401` under a different premise. No
  best-bound claim is made.
