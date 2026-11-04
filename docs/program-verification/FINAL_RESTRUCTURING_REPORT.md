# Final restructuring report: native-assisted and lean-verified-program in IEANTN

- **Scope.** Local branch `agentB/native-assisted` of `hs-chae/IEANTN_test`. Nothing pushed, no
  PR, no receipt.
- **Attestations.** Local research reports in `pv-evidence/`, not official verification.

## Outcomes first

- **16 of 16** audited endpoints pass the local `native-assisted` gate, rerun on a clean tree at commit `d7dfcbe` (12) and `20aabf4` (4). `20aabf4` only renamed the four non-node keys in `endpoints.json`.
- **11** of them are `lean-verified-program`: the real C source, an association fact, an execution witness and a reviewed correctness theorem are all present in the proof closure.
- **5** pass the gate but are `not-program-verified`: `FKS2Numerics.v2.nu_asymp_e30_le`, `FKS2Numerics.v3.calibration_bound`, `RamanujanGap.v2.loss_bound`, `FKS2.v9.qrh_absolute_pi`, `FKS2.v5.updated_theta`.
  These are the two PoC 1 numeric certificates without a source link and the three standard-axiom consumers, which have 0 native facts.
- No endpoint failed or was blocked.
- **Official classification is unchanged everywhere.** No `kind` or `designated` value moved. No receipt was written. Every audited node conclusion is still `lean-noncompliant`, or `none-yet` for the consumers.

| endpoint | gate | evidence method | native facts | official kind | receipt | checked at |
|---|---|---|---|---|---|---|
| `RamanujanNumerics.v2.epsilon_budget` | **passed** | lean-verified-program | 6 | lean-noncompliant | absent | d7dfcbe |
| `RamanujanNumerics.v1.epsilon_budget` | **passed** | lean-verified-program | 6 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v7.qrh_pi` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v6.old_pi` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v5.numerical_pi` | **passed** | lean-verified-program | 7 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v2.nu_asymp_e30_le` | **passed** | not-program-verified | 8 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v3.calibration_bound` | **passed** | not-program-verified | 8 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v3.baseline_bound` | **passed** | lean-verified-program | 8 | lean-noncompliant | absent | d7dfcbe |
| `FKS2Numerics.v4.updated_bound` | **passed** | lean-verified-program | 12 | lean-noncompliant | absent | d7dfcbe |
| `RamanujanGap.v2.loss_bound` | **passed** | not-program-verified | 0 | none-yet | absent | d7dfcbe |
| `FKS2.v9.qrh_absolute_pi` | **passed** | not-program-verified | 0 | none-yet | absent | d7dfcbe |
| `FKS2.v5.updated_theta` | **passed** | not-program-verified | 0 | none-yet | absent | d7dfcbe |
| `@solution.ForwardRamanujan.forward` | **passed** | lean-verified-program | 12 | n/a | n/a | 20aabf4 |
| `@solution.FKS2Pair.assembled` | **passed** | lean-verified-program | 16 | n/a | n/a | 20aabf4 |
| `@pilot.CalibrationPilot.NewChain.new_chain` | **passed** | lean-verified-program | 13 | n/a | n/a | 20aabf4 |
| `@pilot.CalibrationPilot.KernelChain.pi_calibrated_k` | **passed** | lean-verified-program | 1 | n/a | n/a | 20aabf4 |

**Acceptance criterion: met.** Ramanujan (v1, v2) and Table 4 (old, QRH) each have a freshly rerun
`native-assisted: passed` attestation and are classified `lean-verified-program`. Each is backed by
the reviewed source, the challenge type match, and an exact axiom ledger in which every native
fact is traced to a `native_decide` token in a hashed source file. Comparator and the trust report
are unchanged for every other node:
- only the pages of the 11 attested nodes changed; the other 102 of 113 are byte-identical;
- every statement fingerprint and challenge is unchanged;
- `check` fails only on the same 49 inherited provenance items.

## What remains `lean-noncompliant`, and what official certification would need

- **Every audited provider stays `lean-noncompliant`.** Its proof still uses finite native facts:
  6 per Ramanujan instance, 7–8 per Table 4 instance, 8–12 in PoC 1.
- **What Comparator would need.** The same conclusion with a proof whose closure is exactly
  `propext`, `Classical.choice` and `Quot.sound`.
- **Shown feasible in the pilot.** `KernelA` reduces a provider of this exact shape to one native
  fact. Source match, enclosure, domain, execution, rounding and budget are all kernel-checked.
- **The blocker.** The last fact is decimal literal decoding: `FKS2Scalar.decimal` uses
  `String.splitOn`/`toNat?`, which the kernel does not reduce. Removing it needs a structurally
  recursive decoder plus a proof that it agrees with `decimal`. After that, an authentic workflow
  run could issue receipts.
- **The consumers already qualify by axioms.** `RamanujanGap.v2.loss_bound`, `FKS2.v9.qrh_absolute_pi`
  and `FKS2.v5.updated_theta` are standard-axiom implications (0 native facts). They are eligible for
  ordinary Comparator verification today, as conditional theorems.
- **No official subtype.** A receipt-backed official `lean-verified-program` kind would need an
  upstream policy decision. Until then the method is an optional, validated field and the
  promotion rule is unchanged.

## How the redesign helps readers

- **Every attested page shows four separate facts.** Evidence method, local gate, official
  classification and receipt status, so nothing reads as officially verified.
- **The method is evidence-based.** It comes from the proof itself, not from a justification's
  name. PoC 1 shows why this matters: two conclusions called "source-verified" have no C source in
  their proofs.
- **The ledger is exact and reproducible.** For each fact: the owning theorem, file:line, the token
  `native_decide`, the source SHA256, the decided proposition, and the count of trusted library
  implementations it reaches.

## Metadata migration (non-frozen nodes only)

- `FKS2Numerics.v2.nu_asymp_e30_le` (justification `checked-source-stability`): note sentence only. Evidence method not-program-verified; S, A and E fail because no C source is embedded.
- `FKS2Numerics.v3.calibration_bound` (`source-verified`): note sentence only. not-program-verified; S, A and E fail.
- `FKS2Numerics.v3.baseline_bound` (`source-verified`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v4.updated_bound` (`source-verified`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v5.numerical_pi` (`source-transport`): `verification_method: lean-verified-program` + note sentence.
- `FKS2Numerics.v7.qrh_pi` (`source-model-qrh`): `verification_method: lean-verified-program` + note sentence.
- `RamanujanNumerics.v2.epsilon_budget` (`source-model`): `verification_method: lean-verified-program` + note sentence.
- Untouched on purpose: `RamanujanNumerics.v1` and `FKS2Numerics.v6` (frozen by SHA256), and the consumers `RamanujanGap.v2`, `FKS2.v9`, `FKS2.v5` (designated `none-yet`, not a Lean justification).
- All edits are pure additions: 6 files, +29 lines, 0 deletions. Each was checked by re-parsing: only that note, and possibly the new key, changed.

Frozen nodes (`RamanujanNumerics.v1`, `FKS2Numerics.v6`, …) are untouched. Their pages get the
gate rows from the sidecar.

**Comparator-certified conclusions.** The A→B pilot (`@pilot.*`, passed) re-derives
`DudekPlattNumerics.v4.pi_two_sided_footnote` and `DudekPlatt.v4.ramanujan_inequality_9401` by a
program-verified route. That route is **not** registered as an extra justification on those nodes:
- a `lean-noncompliant` justification asserts that the proof lives in `Solutions/<node>/`, but the
  pilot proof lives in `pilots/`;
- registering it would mean moving the pilot into the node's solution project first.

Either way, the designated `lean-comparator` justification, which is stronger and kernel-only,
stays untouched.

## Reader check: self-audit, NOT independent

No separate reader agent was approved, so this is a documented, reviewer-style self-audit. It
uses only the standard IEANTN entry points:
- the generated node page (`ieantn.py pages`);
- the node's `Conclusions.lean` docstrings and `formalization.yaml` notes;
- the `Solutions/*/README.md` maps;
- `docs/qrh/README.md` and the walkthroughs it links;
- `docs/program-verification/`.

| Question | Ramanujan (`RamanujanNumerics.v2`) | Table 4 (`FKS2Numerics.v7`) | PoC 1 (`FKS2Numerics.v3/v4`, `v2`) |
|---|---|---|---|
| What theorem? | Page: docstring "Spelled out…" + Lean body: `εUpper(131,x) − εLower(119,e^3914,x) ≤ 9.101` on `x > e^3915` | Page: `Eπ(x) ≤ 5·10⁻¹⁶` for `x ≥ e^330`, with premises named | Page: the ν* bounds, with the meaning of `ν*` now in the docstrings |
| Why C? | Docstring "How it is checked": C sums seven upward-rounded terms, scales and subtracts | Docstring: the program evaluates `B_safe(Q)` over 30 cells | v3/v4 baseline/updated docstrings name `c/baseline.c` / `c/updated.c`. v2 and v3 calibration: the docstring says the designated proof does **not** use C source |
| What did Lean verify? | Page row "Evidence method: lean-verified-program"; the attestation lists S/A/E/C/M with theorem names (`source_check`, `concrete_execution`, `source_linked_upper`) | Same row; attestation names `FKS2Table4.source_checked`, `FKS2Pair.Updated.concrete_execution`, `FKS2Table4.verified_fks2_transport` | Attestation per conclusion. For v2/v3 calibration the page shows "Evidence method: not-program-verified" |
| Which native facts are trusted? | Page: "6 finite native facts"; note lists their roles; attestation gives each owning theorem, file:line and decided proposition | 8, same detail | 8 or 12, same detail |
| What is not proved about compilation/hardware? | Docstring "compiler and hardware are trusted"; page row "not a receipt"; attestation `trust_boundary` | Same | Same |
| How does the result reach the downstream theorem? | Page "Assumed by: RamanujanGap.v2.*"; docstring names the consumer | Page "Assumed by: FKS2.v9.*" | `FKS2.v4` / `FKS2.v5` docstrings and imports |

**Unresolved ambiguities (findings).**
1. On every page, `Evidence: lean, noncompliant` sits directly above `Evidence method:
   lean-verified-program`. A reader may take "noncompliant" for "unverified". The added row
   `Official IEANTN classification … (designated; unchanged)` mitigates this. A one-line legend on
   the pages index would help further; that is a proposal, not done.
2. **Frozen nodes.** `RamanujanNumerics.v1` and `FKS2Numerics.v6` show the gate rows, but their
   docstrings cannot be extended. The mathematics-first text is one link away, in the walkthroughs.
3. **Ambiguous label.** "Sources traced: none" (literature sources of the imports) can be misread
   as "no source code". This is inherited wording.
4. **Broken links on the fork.** The page's `Source`/`Solution` links point at `teorth/IEANTN` and
   return 404 there. Inherited.
5. **Consumer pages.** Pages of consumers (`RamanujanGap.v2.*`, `FKS2.v9.*`) do not show gate rows
   unless they are audited. They are standard-axiom implications, and their attestations record
   method `not-program-verified`, since they consume the budget as a hypothesis. A reader has to
   follow "Assumes" to reach the program-verified provider.


## Per-endpoint final tables

The twelve-field table for each of the 16 endpoints is in
[PV_ENDPOINT_TABLES.md](PV_ENDPOINT_TABLES.md). It is generated from the attestations by
`scripts/native_assisted/final_tables.py`. The summary table under "Outcomes first" gives each
endpoint's status.

## Pointers

- [NATIVE_ASSISTED_DESIGN.md](NATIVE_ASSISTED_DESIGN.md)
- [PROGRAM_VERIFICATION_INVENTORY.md](PROGRAM_VERIFICATION_INVENTORY.md)
- [PV_ENDPOINT_TABLES.md](PV_ENDPOINT_TABLES.md), the per-endpoint final tables
- [PV_HUMAN_READABLE_GUIDE.md](PV_HUMAN_READABLE_GUIDE.md), which includes the English technical
  summary and the Korean explanation
- [INTEGRATION_DIFF_AND_CHECKS.md](INTEGRATION_DIFF_AND_CHECKS.md)
- the tool: `scripts/native_assisted/README.md`
