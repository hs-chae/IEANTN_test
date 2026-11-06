# Should verified numerical programs be separate IEANTN nodes? Extended study

Agent B, 2026-11-06. Continuation and adversarial audit of `agentB/pv-node-split` `5b59409`. Snapshots: upstream
`teorth/IEANTN` `466b41b`; PoC `hs-chae/IEANTN_test` `qrh-2pv_B` `3280a3c`; Agent A's unpushed `091288d`.
Every experiment ran in disposable local worktrees; no owner branch, receipt or official designation was changed;
nothing was pushed. No Comparator was available, so no claim below says "Comparator-verified".

## 1. Verdict

**Zero architectural change.** Keep programs, certificates and native facts as evidence inside solutions
(design A). A numerical result gets its own node only under a three-clause rule (N1 cited evidence, N2 two
consumer families, N3 a consumer's Comparator eligibility), which the existing graph already follows.

The first study's verdict survives, on stronger evidence and with a shorter rule. What the new evidence adds:

- **A provider node changes no unproved assumption.** In all three matched pairs, built both ways, the
  consumer's transitive unproved leaves under B are exactly A's plus the provider itself.
- **It changes cost only when a result is shared.** Table 4: same build time (638 s vs 657 s) and the same 26 GB
  peak. Ramanujan A→B′: the consumer's fresh closure is 145 modules in B against 144 in A. Only the shared
  provider (`DudekPlattNumerics.v5`, two consumer families) verifies a 112-module proof once instead of once per
  consumer.
- **The real gaps are freshness and drift, and they do not depend on the layout.** 7 of the 12 PoC projects that
  read C sources leave them undeclared to Lake: editing a literal in program B′ left a stale certificate that
  still built in both layouts (MT10b), shown by declaring the files: the same edit then fails the build (R2). `solution_drift` cannot see files in another solution project (now
  shown on real mutations and fixed by a 32-line patch, tested).

## 2. What changed since the first study

| First study said | Now | Evidence |
|---|---|---|
| upstream's leaf-set guard rejects **four re-designations** | **one** re-designation (`RosserSchoenfeld.v1.zero_free_region` at `6af2f7a`) and **four flagged conclusions** (three inherit it through unchanged bridges). Re-designating the paper (one line) makes upstream's `diff` pass; tested | `evidence/leafset/` |
| only `PlattTrudgian.v1` is shared by several families | true only for direct consumers of `kind: computation` nodes. `DudekPlattNumerics.v5` (`pipeline`, program-verified) has two families; 7 of 27 computation nodes reach ≥ 2 families transitively | `evidence/rules/` |
| R1–R4 explain 25 of 27 computation nodes | the old R3 test is nearly circular: 16 of its 17 hits are providers whose evidence is entirely a citation (18 of 29), which forces a node regardless; the 17th is a mixed node. R2, re-derived from consumer axioms, explains 8 of the 9 in-repository providers that have consumers; the ninth (`DudekPlattNumerics.v5`, kernel-only) is explained by its two consumer families | `evidence/rules/`, `evidence/axioms/` |
| R4 (budget) favours a split for Table 4's 28 GB route | false: a split moves the 26 GB peak to the provider's run; it does not lower it (M1) | `evidence/builds/sol_T4_*` |
| layout A drafted, layout B built | both built for three applications | `PV_NODE_SPLIT_MATCHED_EXPERIMENTS.md` |
| freshness held through the cross-project import | it holds where `[[input_file]]` is declared (5 of 12 projects). Where it is not, a source edit replays a stale certificate (MT10, MT10b) | `evidence/mutations/`, `evidence/remedy/R2_input_file_audit.txt` |
| 13 path dependencies root a module named `Solution` (a risk) | reproduced, and observed: `lake env lean` with `import Solution` in `Solutions/FKS2.v4` loaded another package's `Solution` | `evidence/axioms/shadowing_demo_FKS2.v4_lake_env.txt` |

## 3. The policies, as the code states them (upstream `466b41b`)

| Claim | Where | Observed behaviour | Check run here? |
|---|---|---|---|
| A node is a claim; nodes import statements, never proofs; a conclusion may be one of several in a node | ARCHITECTURE §1 L18–31; NODES.md L96–106 | as stated | `check-closure` on the PoC (both tools): ok |
| `Conclusions.lean` imports only Mathlib, Vocabulary, other Conclusions, any node's `Tables` | `check_closure` L1121 | a `Conclusions.lean` importing a solution module fails with exactly that message | yes, probe in `pv8_wtC` (`evidence/blocker/`) |
| `Tables.lean` is data only, no theorems | NODES.md L238–266; `check_closure` L1221–1250 | enforced by keyword | not exercised (no table edited) |
| several justifications, exactly one designated; only the designated one carries trust | NODES.md L206–214 | as stated; re-designation is a one-line change | yes: the `rs-paper` re-designation (`evidence/leafset/`) |
| `lean-noncompliant` requires `Solutions/<NodeId>/Solution.lean` and a note | `check_graph` L1405 (rule near L1569) | ties a Lean route to the node's own project | `check-graph` ok on the PoC (both tools) |
| `native_decide` makes a proof `lean-noncompliant` permanently | ARCHITECTURE L202–209 | the 1-fact routes carry `…_native.native_decide.ax_1_1` | yes, `#print axioms` (`evidence/axioms/M*`) |
| a fingerprint is the statement's elaborated value, binder-erased, IEANTN constants followed | `Tools/Hash.lean`; `compute_fingerprints` L1946 | statement edits move only the edited conclusion's fingerprint; imports are not part of it | yes, `fingerprint` and `--check` in every core build and statement mutation |
| a receipt records the fingerprints of the conclusion **and its imports**, the commit, the environment | `record_receipt` L2707 (statement dict near L2770) | grading an import's change BROKEN is therefore possible | yes, in memory (MT4, MT5) |
| a moved fingerprint is BROKEN unless its source is unchanged (then churn) | `assess` L2223; `statement_source_unchanged` L2306 | as stated | yes, in memory |
| a solution edited after its receipt is reported, within the receipt's own project | `solution_drift` L2355; `drift_note` L2388 | blind to files read from other projects; non-Lean sources called "no Lean source" | yes, every cross-project mutation; and the patch |
| a designated bridge may not add unproved leaves | `diff` L4484, `graph_leaves` L4443, commit `67b277c` | rejects the PoC's `RosserSchoenfeld.v1` re-designation (four conclusions) | yes (`evidence/leafset/`) |
| one-hour budget per node solution | ARCHITECTURE L331–335 | a split moves peak memory, it does not lower it | M1 (`evidence/builds/sol_T4_*`) |
| a hole a solution cannot prove becomes an import hypothesis, i.e. a node | SOLUTIONS.md L57–61 | the reason all 18 cited providers are nodes | census + rules audit |
| shared numerical claims without new types | Vocabulary predicates (`HasNumericalBound`, `HasPowerLogBound`, `RiemannHypothesisUpTo`, `HasPrimeInInterval`) plus node-local definitions (`DudekPlatt.v3.mainTerm`, `RamanujanGap.v1.gap`) | sufficient for every provider statement written in M1–M3 | yes: all compiled with no Vocabulary change |

The PoC's `ieantn.py` is 5,412 lines against upstream's 5,845; `solution_drift`, `drift_note` and `assess` are
byte-identical in the two, and `graph_leaves` exists only upstream.

## 4. Findings

**F1. The network already separates statements from evidence, and the policies say so** (NODES.md L21,
L206–214, L238–266; ARCHITECTURE §1 L18–31; checked at `466b41b`). `check-closure`, `check-graph` and `check-pins`
pass on the PoC under both tool versions; `check-receipts` fails only because the fork's 49 receipts name
`teorth/IEANTN` (`evidence/policy/`).

**F2. Counts reproduce.** PoC `3280a3c`: 116 nodes, 243 conclusions, 49 receipts, 70 solution directories (53 with
a `Solution.lean`), 27 computation nodes, 14 duplicate-statement groups (9 with identical imports); upstream: 65,
136, 50, 21, 17, 5 (`evidence/census/`).

**F3. Duplicates are mostly benign.** Of 14 groups: deliberate evidence-kind splits (2), version restatements (8),
one pair of independent papers proving the same bound (`Hiary2016.v1`/`KLN.v1`), and one architectural artifact
(`FKS2Numerics.v5`/`v7`, a new proof route registered as a version) with its two-group cascade in `FKS2.v7`/`v9`. Equal fingerprints plus
equal imports mean equal challenges; the fingerprint hashes the binder-erased `def` value with IEANTN constants
followed (`Tools/Hash.lean`).

**F4. Every provider is explained by three facts, not four.** N1 cited evidence (18 of 29: a node is the only way
to state it), N2 two consumer families (2: `PlattTrudgian.v1`, `DudekPlattNumerics.v5`), N3 a native provider
under a native-free consumer (8 of the 9 in-repository providers with consumers; the ninth is `DudekPlattNumerics.v5`,
kernel-only, under N2). The two remaining providers are
versions (`DudekPlattNumerics.v4`, `FKS2Numerics.v2`). Rule stress test §2–4.

**F5. Matched pairs: B adds exactly one leaf.** M1, M2, M3: consumer leaves under B = A's leaves ∪ {provider}
(`evidence/trust/`).

**F6. Matched pairs: cost.** A split costs +1 node, +1 edge, about +9 files and +126 to +193 hand-written lines,
plus (M1) a third copy of an existing statement. Build time and memory peak equal within a workspace.

**F7. Isolation is a module property.** M1's consumer verifies in 5 modules; M2's needs 145 because the
pilot's `PVReplay.KernelChain` holds both programs' certificates. A per-program module split would isolate
either layout.

**F8. Native facts.** A provider keeps native facts out of a pure-analysis consumer (M1). It does not help a
consumer with its own program (M2: one native fact remains). Kernel-only routes (M1, M2, Agent A's partial
replacement) remove the question.

**F9. Shared results are the case for B.** M3: one 112-module verification instead of one per consumer, and a
core bridge (`DudekPlatt.v5`) that layout A cannot express.

**F10. Freshness gap (configuration).** 12 PoC projects read 35 files through `include_str`; 7 projects (20
files) declare none of them as `[[input_file]]`, including the designated providers `FKS2Numerics.v6` and
`RamanujanNumerics.v1`. Mutations MT10/MT10b changed program B′'s C file (whitespace; one literal digit):
**0 modules rebuilt, build succeeded, in both layouts**: a stale certificate. Upstream has no `include_str`
user, so this is a PoC-only configuration gap. Declaring the two pilot files (15 TOML lines, the pattern `Table4Evolution.v1` already uses) turned the same
literal edit into a build failure in `PVReplay.Chain` (mutation tests, R2): the earlier success was a stale
certificate, now shown rather than inferred.

**F11. Drift gap (tooling).** `solution_drift` diffs only the receipt's own project (identical code in the PoC and
upstream). It returned nothing for the node's own project in every cross-project mutation (MT1–MT3, MT8, MT9,
MT10, MT10b, MT11: 20 of 20 queries) and filed program sources under "no Lean source among them". A 32-line patch that also diffs the
in-repository path dependencies listed in the solution's `lake-manifest.json` reports all of them; its 5 new tests
fail before and pass after; the 357-test upstream suite passes (`evidence/remedy/`). It works at package level, so it
is sound but sometimes noisy: in MT11 it also flagged `RamanujanGap.v3`, whose `Solution` does not import the edited
module but whose lakefile requires that package for another library. Narrowing it to the import closure would need
Lean's import graph; the minimal patch accepts the noise, since drift is reported, never fatal.

**F12. Statements, routes and sources behave as designed.** 22 mutation runs, each restored byte-for-byte with a clean tree (`PV_NODE_SPLIT_MUTATION_TESTS.md`): a statement
edit moves exactly its own fingerprint and grades receipts BROKEN, including those of conclusions that import it
(MT4, MT5; in-memory receipts); a route swap rebuilds one module and moves nothing (MT6); declared source edits are
rebuilt and the certificate check rejects comments and changed literals (MT1–MT3); a Lean comment in another
project rebuilds one module (MT8, MT11). Two layout differences were measured: after an imported statement changed,
B's consumer receipt stayed green while A's went BROKEN (MT4); and B's consumer failed with its provider when program
A changed, because its solution imports program A's module (MT9). A target change broke B's consumer as well (MT5).

**F13. The trust boundary does not include compilers, and need not.** Five selected C programs compiled under
seven flag sets give identical binary64 results except program B′ under `-O2 -mfpmath=387`, which is 1 ulp lower
(`106.22239841212767` vs `…69`). The Lean proofs never use a compiled binary; they model the source with RN64
semantics, which the x87 build does not follow. Nothing in Lake, the local gate or a receipt records compiler
flags, and nothing needs to (`evidence/mt7_compiler/`).

**F14. Agent A's winner cannot be a provider yet, but less is missing than thought.** `OriginalCHJSource` uses only
Vocabulary objects (it is CHJ eq. (1.5), a literature statement; Agent A's `091288d` already registers the sibling
CHJ-II theorem as `CHJII.v1`). `PrimaryInputs` needs about 15 solution definitions; a `Conclusions.lean` importing
them is rejected by both checkers (`evidence/blocker/`). A provider node does not lift the blocker; registering
the source facts does.

## 5. Trust: two end-to-end traces and ten failure modes

Notation per arrow: **[math]** a mathematical implication; **[impl]** an implementation or evidence dependency;
**kernel** Lean kernel; **native** `native_decide` (`Lean.ofReduceBool`); **gate** the PoC's local native-assisted
gate; **Comparator** the official check (not available here). `fp` = statement fingerprint, `sha` = source hash.

**T1. Table 4, QRH input, as in the repository (layout B) and as M1-A.**

| # | Step | Kind | Checked by | Identifier |
|---|---|---|---|---|
| 1 | QRH (`OpenAIQRH.v1.zeta_seven_eighths`) + `CH2.v9.refined_transfer` + further analytic premises ⟹ `QRHCH2.v5.psi_refined_bound` | [math] | nobody in this repository (`none-yet`) | statement fp of `QRHCH2.v5` |
| 2 | ψ profile ⟹ θ allowance per unit cell `Q(b) = b²/283·e^(−b/8)` (`Table4Evolution.profile_qrh`) | [math] | kernel | solution lemma, no fp |
| 3 | `Q` ⟶ C literals of `qrh_trunc2.c` and `Data/QRHTrunc.lean` (`scripts/generate.py`) | [impl] | nobody: the generator is untrusted | sha `ef750c59…` |
| 4 | C text ⟶ embedded source string (`include_str`) | [impl] | Lake re-reads it only because `[[input_file]]` is declared here (MT1–MT3); the gate pins its sha | sha in attestation `@evo…Kernel.qrh_pi` (`cb81845`) |
| 5 | source string ⟶ program value: literals token-equal to the decoded data, comments rejected | [impl] | kernel (`decide +kernel`) in the kernel route; native in the 1-fact route | — |
| 6 | program ⟶ modelled RN64 execution with a proved forward-error bound (`PVCore`, `SumStability`) | [math] about a model | kernel | — |
| 7 | modelled output ⟶ `B_safe(Q) < 5·10⁻¹⁶` | [math] | kernel (0 native) or native (1) | — |
| 8 | certificate + whole-ray transport ⟹ `HasNumericalBound Eπ (5/10^16) (exp 330)` | [math] | kernel | provider fp `2af9dadb…` |
| 9 | provider statement ⟹ `∀ x ≥ e³³⁰, |π − Li| ≤ 5·10⁻¹⁶ x/log x` | [math] | kernel, three axioms (`FKS2.v9`, `PVMatchT4C`) | consumer fp `b6ae6e9c…` |
| 10 | designated evidence | metadata | `FKS2Numerics.v7`: `lean-noncompliant` (30-cell route, 8 native); `FKS2.v9`: `none-yet`; receipts: none; local attestations: passed, labelled local | — |
| 11 | transitive unproved leaves | report | upstream `graph_leaves` | 15 (B) / 14 (M1-A) |

What a C execution would add is outside the chain: no step runs a compiled binary. The x87 build of another
program differs from the modelled value by 1 ulp (F13), which is why the claim must read "the modelled program"
and never "the C program as compiled".

**T2. Ramanujan A → B′ (pilot; M2).** QRH ψ profile ⟹ (kernel) seven calibration pieces below their targets ⟶
(impl) `calibration_new.c` (sha `f206bd81…`, **not** declared to Lake) ⟶ (kernel) decoded program A, certified
`Σ ≤ Δ = 457/5000` ⟹ (kernel) calibrated `π` for `x > e⁹⁴⁰⁰` ⟶ (kernel equality of rationals) `M = 120 + Δ` ⟶
(impl) `ramanujan_9401_new.c` (sha `86d204a5…`, not declared) ⟶ (kernel) budget `≤ 106.2224` ⟹ (kernel) gap
bound for `x > e⁹⁴⁰¹`. Native facts: 0 (kernel route), 2 (native route; 1 + 1 when split in M2-B). Designated
evidence: none (no node). Leaves: 12 premises + itself (A); + the provider (B). Step 4's missing declaration is
where MT10b's stale certificate entered.

**Ten failure modes.** "Prevents" = the layout makes it impossible; "exposes" = the layout makes it visible to a
reader or a check; "unchanged" = the layout does not matter.

| Failure mode | A | B | D (A + B by N1–N3) | What actually handles it |
|---|---|---|---|---|
| 1 a provider statement assumed without honest provenance | exposes: the consumer's own axioms carry it | exposes: the provider is a separate leaf | exposes | `graph_leaves` walks every import; Comparator checks each compared theorem's axioms |
| 2 QRH evidence re-designated onto an unconditional theorem | unchanged | unchanged | unchanged | upstream's bridge leaf-set guard (`67b277c`); the PoC predates it (§2, first row) |
| 3 C-to-AST correspondence claimed from token equality | unchanged | unchanged | unchanged | wording: PVCore binds literals lexically; semantics is the Lean model |
| 4 source freshness taken as compiler/hardware verification | unchanged | unchanged | unchanged | nothing compiles the C in a proof; MT7 shows why the claim must stay about the model |
| 5 local attestation shown as a receipt | unchanged | unchanged | unchanged | the attestation's own notice, `official_comparator_receipt: absent`, page labels |
| 6 duplicate statements with asymmetric routes | avoided | **invites** (M1-B made a third copy) | avoided if routes are justifications (decision 1) | documentation |
| 7 reuse inflated by version aliases | unchanged | unchanged | unchanged | count consumer families, directly (rule stress test A–C) |
| 8 stale shared-source change invisible to node drift | unchanged (MT1–MT3, MT8, MT10b) | unchanged (same runs) | unchanged | `[[input_file]]` configuration; the drift patch |
| 9 kernel-only program proof read as end-to-end execution | unchanged | unchanged | unchanged | wording (T1 step 6) |
| 10 solution-level source semantics in Vocabulary | avoided | **forced** when the provider's hypotheses are solution-level (C3) | avoided | the closure check rejects it either way (`evidence/blocker/`) |

No failure mode is prevented by B. B exposes one thing A also exposes (mode 1), and it invites two others (6, 10).

## 6. Competing interpretations

| Design | Wins when | Loses when | Evidence |
|---|---|---|---|
| A, evidence in solutions | one consumer family; kernel-only or native-free routes; results that are routes of an existing statement | the result is shared by two families, or a pure-analysis consumer would inherit native facts | M1, M2, C9 |
| B, provider node | two consumer families (M3), cited evidence (N1), keeping a pure-analysis consumer Comparator-eligible while the provider is native (N3) | one family: duplicates statements (M1-B made a third copy), adds a node and an edge, isolates nothing unless modules are split too | M1, M2, M3 |
| C, node per stage | never: stage interfaces are program constants or source predicates (`NewA.bound`, `CertA`), not mathematics | always | C2, C7 |
| D, A by default, B by N1–N3 | — | — | the existing graph already follows it (F4) |

## 7. The smallest change today

Nothing in the architecture, the schema, Vocabulary, node kinds, justification kinds, receipts or trust levels.
In order of the prompt's minimal-change ladder:

0. **Do nothing** to upstream's architecture.
1. **Documentation**: one paragraph in NODES.md near L206 ("several justifications"): a new proof route of an
   existing statement is a justification, never a version; a Lean route living in another solution project is
   attached through a thin `Solutions/<NodeId>/Solution.lean` that requires that project by path.
2. **Configuration, PoC only**: declare the 20 undeclared `include_str` sources as `[[input_file]]` with `needs`
   in the 7 projects (F10); re-designate `rs-paper` for `RosserSchoenfeld.v1.zero_free_region` (one line;
   §2, first row). Both edit the owner's branch, so both need the owner's approval.
3. **Tooling, optional**: the `solution_drift` patch (F11), proposed upstream only with the first program-verified
   solution that reads files from another project; until then upstream has no case for it.
4. **Existing-kind provider nodes**: only by N1–N3; none is needed today beyond those that exist.

## 8. Claim ledger

| # | Claim | Class | Evidence |
|---|---|---|---|
| 1 | PoC/upstream counts (F2) | REPRODUCED | `evidence/census/` |
| 2 | 14 duplicate groups, classified (F3) | REPRODUCED, extended | `evidence/census/`, casebook C5 |
| 3 | one re-designation, four flagged; one-line fix passes upstream's guard | NEWLY TESTED (correction) | `evidence/leafset/L1`–`L5` |
| 4 | R3 proxy = the cited providers plus one mixed node; R2 holds on evidence for 8 of the 9 in-repository providers with consumers | NEWLY TESTED | `evidence/rules/rules_3280a3c_checked.*`, `evidence/rules/R0_conclusion_level.txt`, `evidence/axioms/` |
| 5 | `DudekPlattNumerics.v5` has two consumer families | NEWLY TESTED (correction) | `evidence/rules/` |
| 6 | B adds exactly the provider to the consumer's leaves (M1–M3) | NEWLY TESTED | `evidence/trust/` |
| 7 | split cost, build times, memory peaks (M1–M3) | NEWLY TESTED | `evidence/builds/`, `evidence/metrics/` |
| 8 | all 7 challenge theorems: same type, three axioms | NEWLY TESTED (local preview only) | `evidence/preview/` |
| 9 | any layout passes Comparator | UNVERIFIED | no Comparator binary |
| 10 | fresh per-node closures (5 / 145 / 112 / 121 / 116 modules) | NEWLY TESTED (static count, not fresh builds) | `evidence/closures/` |
| 11 | stale certificate after a C literal edit (MT10b) | NEWLY TESTED | `evidence/mutations/MT10b_*` |
| 12 | 7 of 12 projects leave `include_str` sources undeclared | SOURCE-GROUNDED | `evidence/remedy/R2_input_file_audit.txt` |
| 13 | `solution_drift` blind across projects; patch fixes it | NEWLY TESTED | `evidence/mutations/*/record.json`, `evidence/remedy/` |
| 14 | receipt grades after statement mutations | NEWLY TESTED (in-memory receipts) | `evidence/mutations/MT4_*`, `MT5_*` |
| 15 | compiler flags change one program's result by 1 ulp | NEWLY TESTED | `evidence/mt7_compiler/` |
| 16 | Agent A's coefficient trajectory and native counts | SOURCE-GROUNDED | casebook C3 |
| 17 | `OriginalCHJSource` stateable; `PrimaryInputs` not | SOURCE-GROUNDED + probe | casebook C3, `evidence/blocker/` |
| 18 | the 11-04 `DDExpansionSolution` fan-out to density certificates (an earlier session's observation) | UNVERIFIED (not reproduced at `3280a3c`) | static closure and dry run show no `CertData`; cause not identified |
| 19 | upstream behaviour for program-verified solutions | COUNTERFACTUAL | upstream has none |
| 20 | per-stage nodes (design C) | COUNTERFACTUAL (analysis only) | casebook C2, C7 |

## 9. The eight questions of the stop rule

1. **Gain and pay, same theorem.** Pay: +1 node, +1 edge, ~9 files, 126–193 hand-written lines, a possible
   duplicate statement, a second verification unit. Gain: a named, fingerprinted interface; a consumer whose
   axioms do not depend on the provider's route; finer staleness (after an imported statement changed, only the
   provider's receipt went BROKEN, MT4); one verification of a shared proof (M3 only).
2. **Trust benefit substantive?** No new trust: the same unproved leaves plus the provider. The benefit is
   presentation (a separate leaf with its own designation) and, under N3, the consumer's eligibility.
3. **Can the existing architecture represent several evolving programs?** Yes: routes as justifications and
   registry entries (C9), composition theorems and Lake's module graph as the program DAG (C7), versions when a
   statement or its imports change. Missing: freshness configuration for 7 projects and cross-project drift.
4. **Which real application benefits from a provider node?** `DudekPlattNumerics.v5` (two families). Table 4 and
   Ramanujan A→B′ are better as compositions in solutions today.
5. **What broke under source change, and why?** A literal edit in program B′ left a stale certificate (no
   `[[input_file]]`); drift was invisible from the node's own project (`solution_drift` scope). Declaring the files made
   the same edit fail the build (R2), so the earlier success was stale, not lucky. Changing program A's
   certified output broke the data link in both layouts and, in B, the consumer too (MT9: module coupling). The
   existing mechanisms were not enough because freshness is opt-in per project and drift is scoped to one project.
6. **Do the criteria generalize?** The shortened rule accepts all 29 providers but two versions and rejects five
   plausible candidates, including Agent A's results and both kernel-only providers built here.
7. **Smallest change today.** §7: documentation and PoC configuration; the drift patch optional.
8. **Still uncertain.** Comparator acceptance (no binary); fresh per-node build costs (static counts only);
   upstream behaviour (no program-verified solution there yet); the cause of the earlier density-certificate
   fan-out.

## 10. Limits

One host, one toolchain, one PoC branch. Builds in a shared workspace share package build directories, so local
rebuild counts understate what a fresh per-node verification compiles; static closures fill that gap without a
fresh build. Agent A's work was read, not built. Self-assessed: no independent reviewer was authorized.
