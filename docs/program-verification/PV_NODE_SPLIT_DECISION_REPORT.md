# Should verified numerical programs be separate IEANTN nodes?

Research decision for the owner. No core, schema or metadata change was made. Nothing was pushed. The
only code written is a hypothetical node in a disposable local worktree (§7).

**Refs.** Upstream `teorth/IEANTN` `main` `466b41b` (2026-11-02). Owner fork `hs-chae/IEANTN_test`:
`main` `2a10e72` (an older upstream commit), `QRH_phase2` `d85631a` (on upstream `ef21db9`), PoC branches
`qrh-2pv` `ce12611` and `qrh-2pv_B` `3280a3c` (this study's base). Agent A's newer work is on unpushed
local branches (`00128be`, `374bc27`; re-checked before this report at `b9b2e3c`, 2026-11-06 01:25 UTC,
which adds 89 solution modules and no node), read only. Line numbers refer to `466b41b` unless a file exists
only on the PoC branch.

## 1. Verdict

**Do not make program verification its own kind of node.** A program, its source, its certificate and its
native facts are evidence for a mathematical conclusion. They belong in the solution and in the
justification metadata, which IEANTN already models. **Default: design A (evidence only).**

**Promote a numerical *result* to its own node only by rule (design D).** Do it when two or more consumer
*families* need it, when its evidence is weaker than the consumer's Lean step, when it is an externally
meaningful computation, or when keeping it inside would break the verification budget in time or memory
(§6). The node then states mathematics with Vocabulary
(`HasNumericalBound Eπ …`, `RiemannHypothesisUpTo …`), never a program. That is design B, applied
selectively.

**Never make one node per program stage (design C).** Its interfaces would need program semantics in
Vocabulary. It would add about 36 nodes to the PoC's 116 and show implementation structure as if it were
mathematical dependency.

What the evidence says:

- The network already separates statement from evidence. A node is a claim; "how the step is justified
  is metadata, not Lean" (ARCHITECTURE §1 L18–31). Nodes import statements, never proofs. Computation
  nodes exist (17 upstream, 27 on the PoC branch), and a source change without a statement change is
  already an evidence-level event (`solution_drift`, `ieantn.py` L2355–2385).
- The real defect is narrower: a Lean justification must live in `Solutions/<NodeId>/`
  (`check-graph` L1568–1585), one project per node. A second proof route therefore had nowhere to go but
  a new node. The PoC did exactly that: `FKS2Numerics.v7.qrh_pi` restates `FKS2Numerics.v5.numerical_pi`
  (same fingerprint `2af9dadb…`, same imports), and the copy spread to the consumers. The PoC has 14
  duplicate-statement groups against upstream's 5.
- Reuse is rarer than it looks. Counted by consumer family, only `PlattTrudgian.v1` (finite RH, 6
  families) among the 27 computation nodes has several independent consumers. Evidence separation (R2)
  and statements of record (R3) explain 25 of the 27.
- The one concrete trust benefit of a provider node is mechanical. Comparator checks the axioms of each
  compared theorem, so a native-fact proof kept in its own node keeps the consumer's step
  Comparator-eligible. Kernel-only programs (12 results in the PoC) remove that reason.
- The experiment registered a C-program-verified provider as a node: 5 files and 128 lines, a 15.6 s core
  rebuild, no existing fingerprint moved. Its one-line kernel-only solution matches the challenge exactly
  with only the three standard axioms. Freshness held through the cross-project import (every byte change
  in the C file rebuilt the certificate), but `solution_drift` cannot see that C file from the node's own
  project. Separately, upstream's bridge leaf-set check, which the PoC branch predates, rejects 4 PoC
  re-designations that made unconditional results rest on QRH (§7).

## 2. The current design, as the code states it

| Fact | Where |
|---|---|
| Five node kinds: `paper`, `pipeline`, `folklore`, `computation` ("a large numerical verification, split out so several papers can import it"), `standard` | NODES.md L14–22 |
| A challenge is a conditional theorem; justification is metadata; nodes import statements, never proofs; Lean certifies edges | ARCHITECTURE §1 L18–31 |
| `Conclusions.lean` may import only Mathlib, Vocabulary, other Conclusions and any node's `Tables` | NODES.md L96–99; `check_closure` L1135–1155 |
| Several justifications, exactly one designated; kinds `lean-comparator`, `lean-noncompliant`, `numerical`, `literature`, `asserted`, `bridged`, `none-yet` | NODES.md L206–221; ARCHITECTURE §3 L163–190 |
| `native_decide` makes a proof `lean-noncompliant` permanently; such a proof is a leaf of the trust graph | ARCHITECTURE L206–209, L220 |
| `lean-noncompliant` needs `Solutions/<NodeId>/Solution.lean` and a note naming the obstruction | `check-graph` L1568–1585 |
| `Tables.lean`: data only, no theorems; a statement about a table is a conclusion, its proof a solution; any node may import any table; a table needing many imports "is usually a computation wearing a table's clothes" | NODES.md L238–266 |
| Receipts record statement fingerprints, environment, tools, repository commit, solution project and pinned dependencies, but no source hashes | ARCHITECTURE §4 L232–260; `receipts/RosserSchoenfeld1962.v1.equation_3_35.json` |
| Staleness is derived (green/yellow/orange/churn/BROKEN); a solution edited after its receipt is reported, not fatal, and only within the receipt's own project | `assess` L2223–2277; `solution_drift` L2355–2385 |
| One-hour budget per node solution, "a mechanical criterion for splitting a node" | ARCHITECTURE L331–335; §6 L487 |
| Vocabulary is Mathlib-only, theorem-free, and promotion waits for a second consumer | ARCHITECTURE L43–54, L454–457 |
| Numerical backends: tier A (certificate re-checked in Lean, stays `lean-comparator`) versus tier B (result trusted, needs its own label); a receipt would gain a `method` field | ROADMAP L155–205 |
| A bridge must be trust-neutral; the motivating case was a computation node that would have grown `Lcm.v1`'s leaves | ROADMAP L415–445 |
| A hole a solution cannot prove becomes an import hypothesis, i.e. a node | SOLUTIONS.md L57–61 |

Agent B's additions on the PoC branch (outside the official schema): a local gate
(`scripts/native_assisted/native_assisted_check.py`) whose registry `endpoints.json` maps proof routes
to node challenges (`challenge_module`, `replays`), attestations in `pv-evidence/` carrying the
non-official method label `lean-verified-program`, Lake `input_file`/`needs` so that a changed C file
rebuilds its certificate, the shared contract `PVCore` with `Chunked` sums, C→C and Lean-dyadic→C
composition, and a fix for solution-module shadowing in the progress probe (`cb2983e`).

## 3. Five things that get conflated

| Thing | Example | Lives today | Should live |
|---|---|---|---|
| Mathematical conclusion | `HasNumericalBound Eπ (5/10^16) (exp 330)` | node `Conclusions.lean` | there |
| Numerical intermediate / result specification | `Bsafe(Q) ≤ 4.93e-16`; calibrated `π ∈ S₅ + (120 ± 0.0914)x/log⁶x`; a `θ`-profile allowance table | inside solutions (generated `Data/*.lean`, theorem statements) | in the solution, unless the promotion rule holds; then as a node conclusion stated mathematically |
| Executable artifact | `c/qrh_trunc2.c`, decoded literals, dyadic AST, flags | solution project, read by `include_str`, tracked by Lake `input_file` | there; never in Conclusions or Vocabulary |
| Correctness evidence | soundness theorem, `Exec` of the modelled source, enclosure, certificate, native facts, source hash | solution + local gate attestation | there; summarised in the justification note |
| Official justification / local attestation | `lean-noncompliant` designation; `pv-evidence/*.json` | `formalization.yaml`; `pv-evidence/` | unchanged; never conflated |

A node that says "this C file is verified" is not a `Prop` about numbers. It is either the mathematical
conclusion the file's certificate implies (then state that conclusion) or metadata about evidence (then
record it as evidence). The source hash is evidence metadata and needs no graph edge.

## 4. The four designs

**A — evidence only (incumbent).** One conclusion; programs, proofs, hashes and attestations stay in its
solution and records. A program update changes evidence; the fingerprint does not move.

```yaml
- id: qrh_pi
  imports: [{node: QRHCH2.v5, conclusion: psi_refined_bound}, {node: FKS2.v6, conclusion: table4_anchor_300}]
  justifications:
    - {id: source-model-qrh, kind: lean-noncompliant, note: "30-cell C transport; 8 native facts; local gate passed"}
    - {id: kernel-route, kind: none-yet, note: "Table4Evolution 2-cell route, 0 native; thin Solution.lean imports it; no receipt"}
  designated: source-model-qrh
```

**B — separate mathematical provider node.** The program's output contract is a registered conclusion;
consumers import its statement. This is the `FKS2Numerics.vN` → `FKS2.vM` pattern the PoC already uses.
The experiment's `PowerTransport.v1` (§7) is a minimal instance.

**C — one node per program stage.** Each stage's execution contract is a node. The statements need
`PVCore.Exec`, decoded literals or ASTs, which are solution code (1,114 lines in
`Solutions/ProgramVerification/PVCore`) and cannot enter a Mathlib-only Vocabulary without moving the
program semantics into the core. For the PoC that is about 36 more nodes (33 C files, 3 Lean dyadic
program constants) and more import edges, none of which is a mathematical dependency.

**D — selective hybrid.** A by default; B for a result that meets the rule (§6). A multi-stage chain is a
composition theorem inside one solution (the PoC's `ThreeChain`, `PVReplay.Chain`) until a stage's
interface statement meets the rule. Proof artifacts, source manifests and attestations never define node
identity.

A fifth design is not needed. The one concrete gap the code shows (§5, Q2) is the location of Lean
evidence, which a thin per-node solution covers today.

## 5. Trust semantics

**Provenance paths** (Table 4, QRH input):

```
A   QRH (OpenAIQRH.v1) + 13 analytic premises ─┐
    FKS2.v6.table4_anchor_300 (numerical) ─────┼─> [FKS2.v9.qrh_absolute_pi]
                                               └── solution: transport theorem + C source (include_str, hash)
                                                   + Exec of modelled RN64 + certificate (native or kernel) + consumer step
    trust of the conclusion = designated justification of FKS2.v9 (one leaf, mixing program and analysis)

B   same premises ─> [FKS2Numerics.v7.qrh_pi] ─(statement)─> [FKS2.v9.qrh_absolute_pi]
                     └ lean-noncompliant: 8 native facts       └ consumer step: 0 native, Comparator-eligible
    the dependency report shows the provider as a separate leaf with its own evidence
```

What each design does and does not change:

- A separate node does not raise a trust grade. Native facts stay native (`Lean.ofReduceBool`), the
  compiler and hardware remain outside every proof (Layer 4), and no receipt appears because a
  `Conclusions.lean` exists.
- Importing a provider's statement is not importing its implementation. The consumer's challenge takes
  the statement as a hypothesis; its proof cannot see the provider's program, and its receipt records the
  provider's fingerprint, not its source (ARCHITECTURE §4).
- Trust laundering through edges is blocked by construction: the report computes transitive unproved
  leaves (§1 L29–31); a `lean-comparator` consumer cannot hide a native fact, because Comparator checks
  the compared theorem's axioms; and upstream refuses a designated bridge that grows the leaf set
  (ROADMAP L415–445, `ieantn.py diff`, `67b277c`). That last check exists upstream only: the PoC
  branch predates it, and upstream's checker run on the PoC graph rejects 4 re-designations that made
  unconditional results rest on QRH (§7). Two further risks remain. A `lean-noncompliant` node may compose several programs' native facts behind
  one leaf, so the note must name them. And a local attestation must never be displayed like a receipt;
  the PoC labels it "local, non-official".
- An imported conclusion carries its own designated justification. A consumer's stronger theorem does
  not inherit it; it imports it as a leaf.

**The seven counterfactuals.**

1. *Source changes, inequality and inputs identical.* The node does not change; the fingerprint cannot
   move (§7). Evidence is replaced: new attestation, new note. An existing receipt still
   attests its recorded commit, and `status` reports drift if the change is inside the node's own
   solution project. If the source lives in another project the drift is invisible today (§7), which is
   a tooling gap, not a reason for a node.
2. *QRH inputs change the data and certificate, same algorithm.* If the change comes from a new import
   (a new `ψ` profile), the provider's imports change, so it is a new conclusion via `new-version`;
   consumers stay on the old one until they migrate. If only generated data changes under a fixed
   target, it is evidence. The algorithm interface is not a graph object.
3. *Native facts 21 → 0, same proposition.* Not a node: a new justification. With 0 native facts the
   proof is eligible for `lean-comparator` once a receipt exists; until then it is a spare or a
   `none-yet` with a note. Agent A's `Parallel.pi330_friendly` (21 → 10) is the live example.
4. *A generic `VerifiedSum` lemma reused in ten applications.* A shared Lean package for solutions,
   pinned (as `Solutions/ProgramVerification` is), not a network node. It is a proof, not a claim used
   in any statement. A node would need its program semantics in Vocabulary.
5. *A `Bsafe U` intermediate used by three unrelated consumers.* Promote it (R1), but state the most
   downstream Vocabulary-expressible fact that all three use, usually the `Eπ` bound, not `Bsafe` itself.
   `Bsafe` would need its profile and cell sums defined in a `Conclusions.lean`. One designated
   justification then replaces three copies of the program proof.
6. *A source-linked provider supersedes a `numerical` citation; no Comparator.* Designate the in-repo
   proof (`lean-noncompliant`, native facts named) if the local gate passed, keep the citation as a
   spare, show the attestation as local. Never label it `lean-comparator`.
7. *A reader of `GRAPH.md`.* A provider node shows a real fact: the consumer rests on a computation
   that is a separate leaf. A stage node (C) shows data flow inside a program. `imports_status: traced`
   already marks non-drawable inputs without a node (NODES.md L186).

## 6. Scorecard and the promotion rule

| Criterion | A evidence only | B provider node | C node per stage | D selective |
|---|---|---|---|---|
| Dependency clarity | consumer hides that it rests on a computation | computation is a visible leaf | implementation drawn as mathematics | visible where it matters |
| Trust/provenance granularity | one designated leaf mixes program and analysis; local gate gives per-route detail | per-provider leaf; consumer can be Comparator-eligible while the provider is native (R2) | finest, but tiers per stage are evidence anyway | as B where R2 holds |
| Reuse across consumers | solution-level reuse by path dependency | statement import | statement import | as B where R1 holds |
| A→B, A→B→C, mixed backends | one composition theorem (measured: one-stage update rebuilds one stage) | one node per interface | one node per stage | composition inside one solution |
| Source/AST exposure, Vocabulary churn | none | none if the statement is mathematical | program semantics in Vocabulary | none |
| Counts (PoC base 116 nodes / 243 statements / 49 receipts / 70 solution dirs) | +0 | per provider: +1 node, +1 edge net (consumer imports the provider instead of its 2 premises), +1 fingerprint, +1 receipt slot, +1 solution dir | about +36 nodes | +0–2 now |
| Build/CI cost | one solution may grow past the budget | each part verified separately; provider closure can be large (§7: 9 min, 14 GB cold) | many small verifications plus semantics in core | split only when R4 holds |
| Versioning under QRH input and source changes | source change = evidence; input change = new version | the same, plus duplicate versions when routes are mistaken for statements (`FKS2Numerics.v7`) | every change versions a chain of nodes | the same as A |
| Compatibility with existing work | as now | the pattern the PoC already uses | breaks Vocabulary rules | as now |
| Official policy | unchanged | unchanged | needs Vocabulary/semantics changes | unchanged |

**The promotion rule.** Promote a numerical result to its own node if and only if at least one holds:

- **R1 reuse:** two or more consumer *families* need the same statement (versions of one family do not count);
- **R2 evidence separation:** its designated evidence is weaker than its consumer's Lean step, so keeping it inside would make the consumer `lean-noncompliant`;
- **R3 statement of record:** an externally meaningful computation (finite RH, zero counts, a published table's bound), cited or formalized;
- **R4 budget:** the combined solution would exceed the one-hour verification budget (ARCHITECTURE L331–335) or a runner's memory (ARCHITECTURE L215–217 records a node waiting on exactly that).

Never promote for a new proof route, a reduction of native facts, a source or data change under a fixed
statement, or a program stage whose statement needs program semantics.

**Tested against the repository.** On the PoC's 27 computation nodes (script `split/rule.py`): R1 holds
for 1 (`PlattTrudgian.v1`), R2 for 18, R3 for 17; 25 meet at least one. The two that meet none are a
formalized statement of record with no consumer yet (`DudekPlattNumerics.v4`, `lean-comparator`) and an
asserted computation (`Wedeniwski.v1`). The candidate rule in the prompt (reuse, ownership, external
meaning, saving duplication) explains at most 4 by reuse, even counting versions. Its duplication
criterion cuts the other way: 5 computation nodes carry statements duplicated elsewhere.
`BKLNWNumerics.v1` restates `BKLNW.v1` to separate evidence kinds; `FKS2Numerics.v2` and `.v7` restate
earlier versions. R2 is the criterion the candidate rule lacks, and it is the one the network has
actually used since `FKS2Numerics.v1` split FKS2's numerical side conditions from its Comparator-checked
analysis.

**Checks the rule must keep passing.** (a) R2 explains a split only if the consumer's own step is
native-free. Of the PoC's attested consumers of native providers, 5 of 5 are (`FKS2.v5.updated_theta`,
`FKS2.v9.qrh_absolute_pi`, `RamanujanGap.v2.loss_bound`, `RamanujanGap.v3.loss_bound` and
`gap_lower_bound`: 0 native facts each). A consumer that needed native facts itself would refute R2 as
the explanation. (b) A `computation` node meeting none of R1–R4 should either stay without consumers or
duplicate a statement; the two current cases fit. (c) Counting consumers by node instead of by family
overstates reuse four-fold here (4 node-level cases against 1 family-level).

## 7. The smallest convincing experiment

Disposable worktree `split/wt`, local branch `agentB/pv-node-split-exp` off `qrh-2pv_B`, upstream unset,
never pushed.

**Two layouts for one application** (real files; layout A drafted, not built). The application is
`FKS2.v9.qrh_absolute_pi`: under QRH and the Table 4 anchor, `|π(x) − Li(x)| ≤ 5·10⁻¹⁶·x/log x` for
`x ≥ e^330`.

*Layout B, as on the PoC.* Provider `FKS2Numerics.v7.qrh_pi` (`HasNumericalBound Eπ (5/10^16) (exp 330)`;
imports `QRHCH2.v5.psi_refined_bound`, `FKS2.v6.table4_anchor_300`; `lean-noncompliant`, 8 native facts) and
consumer `FKS2.v9.qrh_absolute_pi` (imports the provider; its `Solution.lean` is one line,
`import FKS2PairConsumers`; its own step has 0 native facts, attested). 2 conclusions, 3 edges.

*Layout A.* One conclusion with the consumer's statement and the provider's premises:

```yaml
- id: qrh_absolute_pi
  imports:
    - {node: QRHCH2.v5, conclusion: psi_refined_bound}
    - {node: FKS2.v6, conclusion: table4_anchor_300}
  justifications:
    - {id: kernel-route, kind: none-yet,
       note: "Table4Evolution 2-cell kernel route (0 native, 147 s, 28 GB) composed with the absolute-bound step; no receipt"}
  designated: kernel-route
```

```lean
theorem FKS2.vN.challenge_qrh_absolute_pi (hψ : QRHCH2.v5.psi_refined_bound)
    (hA : FKS2.v6.table4_anchor_300) : FKS2.vN.qrh_absolute_pi :=
  -- the absolute-bound step of FKS2PairConsumers, applied to the kernel route
  absoluteStep (Table4Evolution.QRHTrunc.Kernel.qrh_pi hψ hA)
```

1 conclusion, 2 edges. With the native route inside, the consumer itself becomes `lean-noncompliant`; with
the kernel route it stays eligible, but its verification carries a 28 GB kernel check.

*Rule applied.* R1 no (one family); R2 yes while the provider is native; R3 no; R4 yes on memory (a 28 GB
check inside the consumer's run). Design D keeps layout B for Table 4, so the existing split is justified,
but not the duplicate `FKS2Numerics.v7`.

**Built: layout B for a new provider.** `PowerTransport.v1.pi_power_network :=
HasPowerLogBound Eπ 0.013156 0 (7/8) (exp 330)`, importing `QRHPropagation.v2.theta_frontier` and
`FKS2.v6.table4_anchor_300`, proved by the existing kernel-only `Table4Evolution.PowerNetwork.pi_power`.

| Step | Measured |
|---|---|
| Register the node (`new-node`, hand-written statement and yaml, `gen-challenges`) | 5 files, 128 lines; `Conclusions.lean` compiles with Vocabulary imports only |
| Core build | from scratch 37 s, 4.4 GB; incremental after the node 15.6 s, 6 modules |
| `ieantn.py check` | same result as the base tree plus one warning (unjustified, no issue) |
| `ieantn.py fingerprint` | only the new node's file written; 240 existing fingerprints unchanged; `--check` ok; 7.4 s |
| Thin solution (`new-solution`, path `require` of `Solutions/Table4Evolution.v1`, one-line proof) | 5 files, 319 lines (260 of them the manifest) |
| Cold build of the solution's closure | 9 min 10 s, 14.3 GB, 118 modules (CH2.v1 and FKS2Numerics.v2 solution modules arrive through Table 4's path dependencies); `Solution.lean` itself 4.7 s |
| NODES.md L323–340 local preview | challenge type identical under `pp.all`; axioms `propext`, `Classical.choice`, `Quot.sound`; import times 3.6 s (challenge), 7.1 s (solution). No Comparator run, no receipt |
| Module names | 13 path dependencies in this workspace also root a module named `Solution`; `import Solution` resolved to the right one here, which nothing guarantees (cf. `cb2983e`); `comparator.json` allows another module name, but `check-graph` requires `Solutions/<NodeId>/Solution.lean` |

**Source-byte changes in `power_network.c`** (a file of *another* solution project), each built only
through the provider's solution, so Lake's entry-point re-tracing cannot confound the result:

| Change | Provider build | Certificate | Fingerprints | `solution_drift`, provider project | `solution_drift`, owning project |
|---|---|---|---|---|---|
| one trailing newline | rebuilt 7 modules, 81.7 s | passes (tokens unchanged) | unchanged | none | "changed … (power_network.c; no Lean source among them)" |
| a comment | rebuilt, 61.8 s | fails: the scanner rejects comments | unchanged | none | reported |
| one digit of a literal | rebuilt, 76.2 s | fails | unchanged | none | reported |
| restored | rebuilt, 79.2 s | passes | unchanged | none | none |

So: (1) freshness holds through the cross-project import, because Lake rebuilt every Table 4 module on the
import path after any change to the C file, coarse but not stale; (2) the statement's fingerprint never
moved, so the node was untouched, as intended; (3) `solution_drift` is blind for the node's own project,
and for the owning project it files the change under "no Lean source among them", the phrase its
docstring uses for the benign case, although for program-verified evidence the C file is the proof
object; (4) only whitespace edits keep a certificate (`PVCore/Source.lean` L18–22).

**Solution-level types in a statement.** A scratch `Conclusions.lean` importing
`WinnerDensityA.SourceContext` (Agent A's `OriginalInputs`): `check-closure` reports "a Conclusions file
may import only Mathlib, Vocabulary, other Conclusions and any node's Tables; found
`WinnerDensityA.SourceContext`", and the core build fails with "unknown module prefix 'WinnerDensityA'".
Deleted after the test.

**Upstream policy run on the PoC graph.** Upstream's `ieantn.py diff` (`466b41b`), base `ef21db9`, on the
PoC tree reports four *breaking* changes: `RosserSchoenfeld.v1.zero_free_region` and
`zero_free_region_classical` gained `OpenAIQRH.v1.zeta_seven_eighths` and `PlattTrudgian.v1.rh_up_to`;
`FKS.v2.psi_bound_all_x` and `psi_classical_bound` gained `OpenAIQRH.v1.zeta_seven_eighths`. They come from
`6af2f7a` (2026-10-31, QRH experiment), which designated a QRH-based "alternative complete core Lean
proof" of the unconditional zero-free region in place of the paper. The PoC's `ieantn.py` predates the
check (`67b277c`), so it passes there. No program node is involved. It is the evidence-level operation
this report recommends, re-designating a route, done without the leaf-set guard: an unconditional theorem
now rests on QRH in the dependency report.

The worktree's two commits (`a5f24d5`, `16cddb6`) are saved as `PV_NODE_SPLIT_HYPOTHETICAL.diff`
(10 files, 447 added lines, nothing modified or deleted).

## 8. Recommendation

1. Keep design A as the default and adopt design D's rule as guidance (Q5), not as CI.
2. Record new proof routes of existing statements as justifications or local registry entries, never as
   node versions (Q1). Designate a new route only if its unproved leaves are contained in the current
   route's; otherwise keep it as a spare. Use a thin `Solutions/<NodeId>/Solution.lean` to attach a route
   that lives in another project (Q2, measured in §7).
3. Rebase the PoC's checks onto upstream's leaf-set rule before anything from it is proposed upstream:
   4 of its re-designations fail it (§7).
4. Ask upstream to make `solution_drift` see files a solution reads from other projects, and not to
   file program sources under "no Lean source" (Q3).
5. For Agent A's winner, stay at the solution level until its source facts have an independent consumer
   (Q7).
6. Leave existing nodes alone, including `FKS2Numerics.v7` (Q6). Node identity survives refactoring.

Implementation is the owner's decision; `PV_NODE_SPLIT_MAINTAINER_QUESTIONS.md` lists the ten decisions.

## 9. Negative findings and limits

- Splitting a node fixes none of the trust problems the program-verification work actually found:
  native facts, the unproved compiler layer, missing receipts, stale umbrella modules, and
  cross-project source drift.
- The PoC's own provider nodes have one consumer family each. They are justified by R2 while their
  programs are native, not by reuse.
- No Comparator was run (no local binary; building one would fetch external tools). The pp.all/axiom
  check of NODES.md L323–340 is a preview, not a receipt.
- Ownership (criterion ii in the prompt) is not recorded in metadata beyond `responsible_maintainers`,
  so it could not be tested mechanically.
- Counts are for one fork branch; upstream has no program-verified provider yet.
