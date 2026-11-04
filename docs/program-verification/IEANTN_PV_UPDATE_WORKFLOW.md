# Updating a program-verified provider

`scripts/native_assisted/pv_update.py` is a narrow, opt-in workflow. It runs real checks; it does
not mint any result. Its registry is `scripts/native_assisted/providers.json`.

## The steps

| Step | Command | What happens | Automated? |
|---|---|---|---|
| 1. Identify | `plan <conclusion>` | Shows the registered old provider, the changed parameters, the selected files, the computed output and proved error, and the consumers of the old and new conclusions (read from `formalization.yaml` imports). | yes |
| 2. Register the change | edit `providers.json` | One entry: `updated_from`, the changed parameters, the statement's bound, the new solution paths. | manual |
| 3. State the new conclusion | `ieantn.py new-version <Family>`, edit `Conclusions.lean` and `formalization.yaml` | The statement and its bound are the contributor's. `plan` prints the certified upper value, so the bound can be chosen above it. | manual, by design |
| 4. Generate | `generate <conclusion>` | Writes the C file in the frozen generator's layout and a data-only Lean module (literals, one certificate, the family theorem). Also writes a lakefile that declares the C file as an `input_file` the provider library `needs`, and `pv-provider.lock.json` (hashes, diagnostic output bits). | yes |
| 5. Build | `build <conclusion>` | `lake build Solution`. A changed C file or literal list is rebuilt, never replayed. | yes |
| 6. Gate | `gate <conclusion>` | Runs `native_assisted_check.py check`: builds, extracts, applies the policy, and writes `pv-evidence/<conclusion>.native-assisted.local.json`. | yes |
| 7. Consumers | new version of each consumer | A consumer that should use the new provider gets a new version importing it. Its proof is usually the old proof at new parameters. | manual |
| 8. Metadata | `formalization.yaml` | Designated `lean-noncompliant` with a note. `verification_method: lean-verified-program` is added only after the gate says so. The official kind is never changed. | manual |

`all <conclusion>` runs steps 1, 4, 5 and 6.

**What the workflow refuses.**
- **A bound below the certified value.** `generate` stops.
- **An input outside `[2⁻⁴⁰, 1]`.** `generate` stops.
- **A non-positive intermediate.** `generate` stops, because the shared certificate does not cover
  it.
- **A statement that is not what the family theorem proves.** The build fails.

## The real replay: `RamanujanNumerics.v2` → `v3`

**The change.** `A 3914 → 400`, `Y 3915 → 401`; everything else is unchanged.

- `DudekPlattNumerics.v5` proves the coefficients 119/131 for every `x > e^400`.
- v2's range `x > e^3915` was a choice made for the controlled comparison with v1. It was not a
  limit of the input.

```
$ python scripts/native_assisted/pv_update.py plan RamanujanNumerics.v3.epsilon_budget
updated from RamanujanNumerics.v2.epsilon_budget
  A              3914 -> 400         (changed)
  Y              3915 -> 401         (changed)
array entries 7; output 9.9876269234; proved error 1.002e-10; certified upper 9.9876269235
statement bound 9988/1000 -> OK
consumers of the old conclusion: RamanujanGap.v2.loss_bound, RamanujanGap.v2.gap_lower_bound, RamanujanGap.v2.paired
```

**Before and after.**

| | `RamanujanNumerics.v2` | `RamanujanNumerics.v3` |
|---|---|---|
| Statement | `∀ x > e^3915, εUpper(131,x) − εLower(119, e^3914, x) ≤ 9.101` | `∀ x > e^401, εUpper(131,x) − εLower(119, e^400, x) ≤ 9.988` |
| Selected file | `c/updated.c`, 7 entries | `c/budget.c`, 7 entries, generated |
| Literals that changed | — | 4 of 7 (entries 2–5). Entry 1, `2·131/4096`, does not depend on `Y`; entries 6 and 7 stay at the `2⁻⁴⁰` floor. |
| Instance proof | 116 code lines, 18 theorems, 6 native facts | 26 code lines (7 are literals), 2 theorems, 1 native fact |
| Consumer | `RamanujanGap.v2`, `x > e^3915` | `RamanujanGap.v3`: loss and gap bounds for `x > e^401`. Ramanujan's inequality itself on that range was already `DudekPlatt.v5.ramanujan_401` (bridged). |
| Gate | passed, 6 native facts | passed, 1 native fact, `lean-verified-program` |

**Which bound improved, and which did not.**

- **Range.** It moves from `e^3915` down to `e^401`.
- **Allowance.** It gets slightly worse, `9.101 → 9.988`, because the terms are evaluated at a
  smaller `Y`.
- **Scope of the claim.** This is a network-relative statement under the QRH-derived premise. It
  is not a claim about the literature's best range for Ramanujan's inequality; that question is
  Agent A's.

**Regenerating is deterministic.** Running `generate` again reproduces the C file and the Lean
module byte for byte; only `lake-manifest.json` changed when the shared package's dependencies
changed.

## Source freshness, now structural

- **The problem.** Lake does not track files read by `include_str`. A changed C file leaves
  `lake build` green with the old source embedded; the earlier gate caught this only afterwards,
  through its hash check.
- **The fix.** The generated lakefile declares the file as an input that the provider library
  needs:

```toml
[[input_file]]
name = "selected_source"
path = "c/budget.c"
text = true

[[lean_lib]]
name = "RamanujanBudget"
needs = ["selected_source"]
```

- **Checked both ways.**
  - Scratch project (`agentB/evidence/pv3`): with `needs`, a changed file reruns `selected_source`
    and recompiles; without it, Lake replays the stale result.
  - On the real provider: `controls_pv.py`, controls A and B.
- **Older providers keep the hash check.** Their lakefiles were not changed: they are frozen or
  published. The gate's S check still catches a stale build there.

## What stays manual, and why

- **The statement and its bound.** A theorem is the contributor's claim.
- **New consumer versions.** A consumer's statement changes with its premise.
- **The registry entry.** It is the documented reason for the update.
- **Metadata after the gate.** Official metadata is never written by a tool from a log.
