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

**Conclusion and next theorem.** `RamanujanGap.v3` turns the budget into the lower bound
`(1 − 9.988/log x)·x²/(log x)⁶ < (e·x/log x)·π(x/e) − π(x)²` for every `x > e^401`. Ramanujan's
inequality on this range was already in the network as `DudekPlatt.v5.ramanujan_401`, so check
for an existing conclusion before adding one: the first version of this tutorial's example stated
it again and had to drop it.

## 2. Why a program

- **What the computer does.** It adds the seven terms, after scaling each by 1/4096 and rounding
  upward, as a C program in binary64.
- **Why not by hand.** The sum is easy to get by hand. Doing it in C makes the computation the same
  object every IEANTN provider of this kind uses, with one proof for all of them.
- **What is proved.** Not that C is correct, but that this exact file, run under IEEE rounding,
  gives a number whose proved error keeps the sum below `C`.

## 3. The steps (commands from the repository root)

```bash
# 1. register the change, and let `plan` compute the certified value before you choose the bound
#    scripts/native_assisted/providers.json, a new entry under "providers":
#    "RamanujanNumerics.v3.epsilon_budget": {
#       "updated_from": "RamanujanNumerics.v2.epsilon_budget",
#       "parameters": {"A": "400", "Y": "401"},
#       "bound": "9988/1000",
#       "project": "Solutions/RamanujanNumerics.v3",
#       "source": "Solutions/RamanujanNumerics.v3/c/budget.c",
#       "lean_lib": "RamanujanBudget",
#       "lean_module": "RamanujanBudget/Provider.lean",
#       "allowance_def": "RamanujanNumerics.v3.allowance",
#       "gate_endpoint": "RamanujanNumerics.v3.epsilon_budget"}
#    The five location keys are required: an update never inherits the old provider's files.
python scripts/native_assisted/pv_update.py plan RamanujanNumerics.v3.epsilon_budget
#    prints "certified upper 9.9876269235" and "statement bound 9988/1000 -> OK";
#    if it says NOT met, raise "bound" and run plan again

# 2. a new version of the family, with that bound in its statement
python scripts/ieantn.py new-version RamanujanNumerics
#    Conclusions.lean: the statement and `def allowance : ℝ := 9988/1000`
#    formalization.yaml: justification `id: shared-contract`, `kind: lean-noncompliant`, a note,
#    and `designated: shared-contract` (copy IEANTN/Nodes/RamanujanNumerics/v3/formalization.yaml)
python scripts/ieantn.py gen-challenges && python scripts/ieantn.py fingerprint

# 3. the solution project
python scripts/ieantn.py new-solution RamanujanNumerics.v3
python scripts/native_assisted/pv_update.py generate RamanujanNumerics.v3.epsilon_budget
#    write RamanujanBudget/NodeTheorem.lean (the module name must be unique, see §4):
#      import RamanujanBudget.Provider
#      theorem RamanujanNumerics.v3.challenge_epsilon_budget : RamanujanNumerics.v3.epsilon_budget :=
#        RamanujanNumerics.v3.Provider.epsilon_budget
#    Solution.lean:   import RamanujanBudget.NodeTheorem
#    comparator.json: "solution_module": "RamanujanBudget.NodeTheorem"
(cd Solutions/RamanujanNumerics.v3 && mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages \
   && lake build Solution)
#    the link reuses the repository's Mathlib; with no manifest yet, `lake build` writes one

# 4. the local gate: one entry in scripts/native_assisted/endpoints.json, then the check
#    "RamanujanNumerics.v3.epsilon_budget": {"project": "Solutions/RamanujanNumerics.v3",
#       "root_module": "Solution", "endpoint": "RamanujanNumerics.v3.challenge_epsilon_budget",
#       "challenge_module": "IEANTN.Nodes.RamanujanNumerics.v3.Challenge",
#       "sources": ["Solutions/RamanujanNumerics.v3/c/budget.c"], "family": "Ramanujan"}
python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v3.epsilon_budget
```

## 4. What you get, file by file

| File | Written by | Content |
|---|---|---|
| `c/budget.c` | generator | the frozen `sum` function, 7 literals, `×4096 − 134 − 119` |
| `RamanujanBudget/Provider.lean` | generator | literals, program, `source := include_str …`, `certificate` (one `native_decide`), `epsilon_budget` (5 lines, the family theorem) |
| `lakefile.toml` | generator | requires the shared package; declares `c/budget.c` as an input the provider needs |
| `pv-provider.lock.json` | generator | hashes of both files, diagnostic output bits |
| `RamanujanBudget/NodeTheorem.lean` | you | the challenge theorem, one line naming the provider theorem |
| `Solution.lean`, `comparator.json` | you | `import RamanujanBudget.NodeTheorem`; `solution_module` names that module |
| `Conclusions.lean`, `formalization.yaml` | you | the statement and its justification |

**Why the challenge theorem is not in `Solution.lean`.** Lake puts a project's own build directory
last on the module search path. A solution that requires other solution projects therefore finds
their `Solution` modules first: on this fork `import Solution` from a QRH solution loads
`Solutions/CH2.v1/Solution`. A uniquely named module, named in `comparator.json`, avoids that.

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
- Linking the shared packages in a new solution project.
- The consumer's new version: `RamanujanGap.v3`, 3 theorems that reuse `loss_from_budget` and
  `gap_from_budget`.
- The node theorem module, `comparator.json` and the `endpoints.json` entry (step 3 and 4).

**Found by the independent reader (2026-11-05).** The earlier version of these steps put the
statement before `plan`, hid the registry's location keys behind "…", missed the
`endpoints.json` entry, and still said the challenge theorem goes in `Solution.lean`. The steps
above are corrected, and `pv_update.py` now refuses an update entry that omits its own location
keys (it would otherwise have inherited, and overwritten, the old provider's files).

**Not covered.** An instance of a different shape, such as a weighted sum with per-entry scales,
needs a new family adapter; only the Ramanujan family has one.

## 7. Three variations

**Fewer trusted computations (kernel route).** Keep the instance; prove its certificate in two
parts. The decoding of the literals is the one native fact; the kernel checks the rest.

```lean
-- for v3: m = 119, so the decoded constants are 134 and 119; xs are the seven decoded literals
theorem decode_native :
    PVCore.decode program = some (xs, 4096, [(.minus, 134), (.minus, 119)]) := by
  native_decide                                            -- decimal strings → rationals, only
theorem budget_k : PVRamanujan.budgetFrom source program 119 131 400 401 (1 / 10000000000)
    (2497 / 250) xs 4096 [(.minus, 134), (.minus, 119)] = true := by
  decide +kernel                                           -- everything else, by the kernel
theorem certificate : PVRamanujan.budgetCheck source program 119 131 400 401 (1 / 10000000000)
    (2497 / 250) = true :=
  PVRamanujan.budgetCheck_of_decode decode_native budget_k
```

`xs` is the list of decoded literals, written out once (the generator's literals are exact
binary64 values, so `Fraction(literal)` is the rational). Cost: for two 7-entry stages, 177 s and
22.7 GB instead of seconds. Example: `pilots/pv-replay/PVReplay/KernelChain.lean`.

**More than 64 entries (chunked).** One call of the frozen `sum` is proved for 1–64 entries. Write
the sum as chunks: `PVCore.ChunkedProgram`, rendered as `s = sum(inputs0, n0); s = (s +
sum(inputs1, n1)); …`. `scripts/native_assisted/pv_chunked.py` writes such a file
(`pv_chunked.py table4 2` splits the Table 4 file into two chunks; `pv_chunked.py demo` writes the
100-entry test);
`upperCheckChunked` and `le_bound_of_checkChunked` replace `upperCheck` and `le_bound_of_check`.
Examples: Table 4 in two chunks of 15, and a 100-entry sum (`PVReplay/Chunked.lean`).

**A provider that is not a C program.** A generated Lean expression evaluated by an exact
interval evaluator (Agent A's backend) is registered with a `backends` entry in
`scripts/native_assisted/endpoints.json`:

```json
"backends": [{"backend": "lean-dyadic-expr",
              "program_constants": ["ScopedWinnerA.Certificate.program"],
              "program_sources": {"Solutions/ScopedWinnerA.v1/ScopedWinnerA/Certificate.lean": "<sha256>"}}]
```

The gate checks that the program constants are in the proof and defined in the pinned files,
and finds the backend's association, execution and soundness theorems (`semantics.json`,
`backends`). An endpoint that composes several programs lists one entry per backend; all must
pass. Example: `@twobackend.PVTwoBackend.gap_exceeds_leading`.
