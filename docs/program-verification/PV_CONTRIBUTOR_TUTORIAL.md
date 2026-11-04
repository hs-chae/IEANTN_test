# Adding a small program-checked numerical node

For a mathematician who has not used program verification. The running example is a real one,
`RamanujanNumerics.v3`, added on 2026-11-04. A self-audit followed the same steps; see §6.

## 1. What you are proving

**Definition.** A Ramanujan budget is an inequality

  `∀ x > e^Y,  εUpper(M, x) − εLower(m, e^A, x) ≤ C`,

where `εUpper` and `εLower` are the seventh-order error terms of Dudek–Platt Lemma 2.1
(`DudekPlatt.v3`). `m` and `M` are coefficients of a two-sided bound for π(x); `C` is the budget.

**Small example.** With `(m, M, A, Y) = (119, 131, 400, 401)`, the majorant
`ForwardRamanujan.epsilon_majorant` reduces the left side to the finite sum

  `2·131 + (2·131+132)/401 + (4·131+288)/401² + (12·131+576)/401³ + 48·131/401⁴ + 131²/401⁵ − 134 − 119`

which is ≈ 9.98763. So `C = 9.988` works.

**Hypotheses.** None in the budget: it is pure arithmetic. The coefficients enter the consumer
through the π bound `DudekPlattNumerics.v5.pi_two_sided_qrh`, valid for `x > e^400`.

**Conclusion and next theorem.** `RamanujanGap.v3` turns the budget into Ramanujan's inequality
`π(x)² < (e·x/log x)·π(x/e)` for every `x > e^401`.

## 2. Why a program

- **What the computer does.** It adds the seven terms, after scaling each by 1/4096 and rounding
  upward, as a C program in binary64.
- **Why not by hand.** The sum is easy to get by hand. Doing it in C makes the computation the same
  object every IEANTN provider of this kind uses, with one proof for all of them.
- **What is proved.** Not that C is correct, but that this exact file, run under IEEE rounding,
  gives a number whose proved error keeps the sum below `C`.

## 3. The steps (commands from the repository root)

```bash
# 1. a new version of the provider's family, then write its statement
python scripts/ieantn.py new-version RamanujanNumerics
#    edit IEANTN/Nodes/RamanujanNumerics/v3/Conclusions.lean   (statement + allowance 9.988)
#    edit IEANTN/Nodes/RamanujanNumerics/v3/formalization.yaml (justification + note)
python scripts/ieantn.py gen-challenges && python scripts/ieantn.py fingerprint

# 2. register the change (scripts/native_assisted/providers.json)
#    "RamanujanNumerics.v3.epsilon_budget": {"updated_from": "RamanujanNumerics.v2.epsilon_budget",
#       "parameters": {"A": "400", "Y": "401"}, "bound": "9988/1000", ...}
python scripts/native_assisted/pv_update.py plan RamanujanNumerics.v3.epsilon_budget

# 3. the solution project, then generate its data and build
python scripts/ieantn.py new-solution RamanujanNumerics.v3
python scripts/native_assisted/pv_update.py generate RamanujanNumerics.v3.epsilon_budget
#    Solution.lean: theorem …challenge_epsilon_budget := RamanujanNumerics.v3.Provider.epsilon_budget
(cd Solutions/RamanujanNumerics.v3 && lake update && lake build Solution)

# 4. the local gate
python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v3.epsilon_budget
```

## 4. What you get, file by file

| File | Written by | Content |
|---|---|---|
| `c/budget.c` | generator | the frozen `sum` function, 7 literals, `×4096 − 134 − 119` |
| `RamanujanBudget/Provider.lean` | generator | literals, program, `source := include_str …`, `certificate` (one `native_decide`), `epsilon_budget` (5 lines, the family theorem) |
| `lakefile.toml` | generator | requires the shared package; declares `c/budget.c` as an input the provider needs |
| `pv-provider.lock.json` | generator | hashes of both files, diagnostic output bits |
| `Solution.lean` | you | one line naming the provider theorem |
| `Conclusions.lean`, `formalization.yaml` | you | the statement and its justification |

The proof of the inequality is not in your files. It is `PVRamanujan.budget_of_check` and
`PVCore.certified` in `Solutions/ProgramVerification`, already written once for every instance of
this shape.

## 5. What is trusted, in plain words

| Layer | Status |
|---|---|
| The inequality from the computed number | proved in Lean (kernel) |
| The C file is the program the proof talks about | proved: token match inside the certificate |
| The run of that program under IEEE round-to-nearest | proved: the certificate checks each rounding, and `certified` derives the execution |
| Evaluating the certificate itself | **trusted:** one `native_decide`, run by Lean's compiler |
| A real compiler or machine running `budget.c` | **not modelled**; agreement would be a diagnostic only |

## 6. New-user test (self-audit, not independent)

No reviewer was approved, so I followed the steps above as written, after the generator existed.

- **Counted.** Hand-written: the statement (one `def` and its docstring), one registry entry, one
  line in `Solution.lean`, the yaml justification. Generated: the C file and the 26-code-line
  module.
- **Commands.** 8.
- **Before the shared contract.** The same change meant a 116-code-line copied instance file with
  18 theorems and 6 native facts, edited by hand around the frozen generator's output.

**Still manual.**
- Choosing the bound; `plan` prints the certified value.
- `lake update` in a new solution project.
- The consumer's new version: `RamanujanGap.v3`, 4 theorems that reuse `loss_from_budget` and
  `gap_from_budget`.
- Adding the endpoint to `endpoints.json` for the gate.

**Not covered.** An instance of a different shape, such as a weighted sum with per-entry scales,
needs a new family adapter; only the Ramanujan family has one.
