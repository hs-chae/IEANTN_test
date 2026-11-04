# QRH experiment handoff (`qrh-2pv`)

Mathematical status snapshot: **2026-11-03**. Handoff updated **2026-11-04**. Owner: hs-chae. This is an experimental branch of
`hs-chae/IEANTN_test`, not upstream `teorth/IEANTN/main`.

The current mathematical source snapshot is `adf3b0d34ef1a895b8824d5acb720cceafffe0fe`.
The following documentation commit adds orientation only. Use `git rev-parse HEAD`
to identify the actual checkout. The owner explicitly authorized this publication;
"nothing pushed" in older reports describes their earlier delivery date.

## Start in this order

1. Read this handoff and [reproduction instructions](REPRODUCING.md).
2. Open [RESULTS.html](RESULTS.html) for exact, statically rendered mathematics and
   trust comparisons. The [rendering-corrected full forward report](FORWARD_REPORT.html) is also included. Both work offline; GitHub may require downloading it first.
3. Read [CLAUDE.md](../../CLAUDE.md), [CONTRIBUTING.md](../../CONTRIBUTING.md),
   [ARCHITECTURE.md](../ARCHITECTURE.md) and [NODES.md](../NODES.md).
4. Follow the relevant proof path in the source map below. Inspect the actual
   `Conclusions.lean` and `formalization.yaml`, not only a generated status page.
5. Consult [ARTIFACTS.json](ARTIFACTS.json) for the separately delivered full
   replay/evidence packages and their exact SHA256 values. This JSON is an index,
   **not an IEANTN verification receipt**.

## What the project is testing

Does a stronger mathematical input update an existing verified numerical program
and then improve a mathematical consumer, while reusing the source/FP/analytic
proof infrastructure? The owner asks for **validity of all created pilot claims**,
not optimality. Do not substitute a selected weaker result for the stated pilot.

The chain is: QRH zero-free theorem → CH2 explicit estimate → pi-expansion or
theta profile → changed executable operands → source-associated numerical
certificate → whole-ray prime-counting consequence. This is not fully automatic:
input adapters, generated data, new finite certificates and consumer/metadata
wrappers are explicit engineering work.

## The two completed numerical experiments

| Experiment | Precise status | Same-domain result | Workload |
|---|---|---|---|
| FKS2 Table 4 pair | Retrospective old reconstruction; actual QRH replay checked separately | Normalized pi error allowance 1.69e−12 → 5e−16 for every real x ≥ exp(330) | Same fixed 30 cells in both programs |
| Ramanujan forward pilot | Controlled replay: old source and consumer frozen before generating updated program; implementer already knew M1 | Normalized gap-loss allowance 3914.7/log(x) → 9.101/log(x), every real x > exp(3915) | Same 7 inputs, 10 FP operations each |

These are **different error definitions**. The Table 4 error is absolute pi-minus-Li
error divided by x/log(x). The Ramanujan loss is the nonnegative normalized
shortfall of its prime-counting gap; see [rendered definitions](RESULTS.html#ramanujan).
Do not compare their numeric coefficients directly.

For Table 4, the published historical comparator is **1.6855e−12**, distinct from
our reconstructed **1.69e−12** allowance. Exact allowance ratios against 5e−16 are
3371 and 3380 respectively. They are not ratios of actual errors. An existing
Phase 2 density route is stronger with additional density/finite-RH inputs.

For Ramanujan, the allowance ratio is about **430.14**, not a ratio of true errors.
The updated theorem gives a stronger lower bound for the actual prime-counting
gap on the same ray. It does not improve the branch's already-existing Boolean
Ramanujan cutoff exp(145) under additional density/finite-RH inputs, claim a best-known theorem, or establish optimality.

The optional fixed-target test is a useful **negative result**: both old and new
inputs meet the old target using one grouped input and four FP operations. Thus
there is **no QRH-driven workload reduction** in that test. Both still generate
all seven rational terms before grouping. No wall-clock speedup is claimed.

The forward pilot covers **one additional numerical obligation** beyond Table 4,
with four checked instances (old/new seven-term and old/new one-group programs),
not four distinct applications. It adds five versions/ten conclusions. The paired
Table 4 work adds four versions/twelve conclusions.

## Chronology and frozen baselines

| Commit | What it records |
|---|---|
| `d85631a387a9b374a43ef1732b0b3ca5506eab6a` | Earlier quantitative propagation, including the exp(145) Ramanujan route |
| `5140779aef295e428f3368ed8d5214100b12a2a2` | Previously published single QRH Table 4 source verification |
| `fdfc45448ee6bdbbd781e2313ebf3513cb4609f7` | Frozen retrospectively reconstructed old Table 4 program/proof |
| `154b1d0c10e4cc3e2d6326c3996de5333842ced4` | Shared Table 4 transport and paired consumers |
| `52ab0869abbdf8b0125717ca5bbdb03d95a97eff` | Forward protocol committed before new pilot Lean/C code |
| `aedfab4e7484351cc322cca1bcac6d70ecea2be5` | Old Ramanujan source/FP/consumer frozen before updated numerical data |
| `adf3b0d34ef1a895b8824d5acb720cceafffe0fe` | Checked forward QRH update, grouped tests and kernel-source alternative |

The forward freeze was 2026-11-04 00:11:48 UTC (November 3 locally). It protects
30 source files and 17 evidence files. Table 4 has a separate 19-source/12-evidence
freeze. Publication preserves these snapshots and every previously versioned
statement/receipt; `IEANTN/Nodes.lean` only gained generated imports.

Read the original [forward protocol](../../Solutions/RamanujanNumerics.v1/FORWARD_EXPERIMENT_PROTOCOL.md)
and [source-domain amendment](../../Solutions/RamanujanNumerics.v1/FORWARD_PROTOCOL_AMENDMENT_1.md).
The amendment was recorded **before freeze**. PNT+'s historical lower pi bound
starts at exp(3914), but its upper side starts at exp(3915). The added
[DudekPlattNumerics.v7](../../IEANTN/Nodes/DudekPlattNumerics/v7/Conclusions.lean)
retains that asymmetry; the original v2 statement is untouched. The larger PNT+
proof closure was not replayed and remains an explicit source-backed premise.

**No held-out experiment or new mathematical discovery is claimed.** A single
implementer who already knew the QRH update cannot claim blindness. Table 4 is
retrospective; Ramanujan is a controlled forward replay of a known valid input.

## Source map: actual proof paths

All paths below are relative to the repository root. The linked solution files
are proof implementations; the node `Conclusions.lean` files are statements.

| Task | Files and declarations |
|---|---|
| Old Table 4 source/execution/FP | [FKS2Numerics.v6](../../Solutions/FKS2Numerics.v6/Solution.lean), `FKS2Pair/OldInputs.lean`, `OldResult.lean`, `OldProvider.lean`, `c/fks2_table4_transport_old.c` |
| Shared Table 4 transport | [GenericMath.lean](../../Solutions/FKS2Numerics.v6/FKS2Pair/GenericMath.lean), `whole_ray_transport`; [GenericSource.lean](../../Solutions/FKS2Numerics.v6/FKS2Pair/GenericSource.lean) |
| Updated Table 4/provider/pair | [FKS2PairQRH.lean](../../Solutions/FKS2Numerics.v7/FKS2PairQRH.lean), [FKS2PairConsumers.lean](../../Solutions/FKS2Numerics.v7/FKS2PairConsumers.lean), [FKS2PairReplay.lean](../../Solutions/FKS2Numerics.v7/FKS2PairReplay.lean), `FKS2Pair.assembled` |
| Original selected numerical obligation | [DudekPlatt.v2 threshold](../../Solutions/DudekPlatt.v2/Solution.lean), with the [repaired v3 estimates](../../Solutions/DudekPlatt.v3/Bounds.lean) |
| Frozen generic Ramanujan math | [Math.lean](../../Solutions/RamanujanNumerics.v1/ForwardRamanujan/Math.lean), `epsilon_majorant`, `gap_from_budget`, `loss_from_budget` |
| Frozen source/FP adapter | [Source.lean](../../Solutions/RamanujanNumerics.v1/ForwardRamanujan/Source.lean), `Exec`, `source_linked_upper`, selected indexed sum/RN64 suffix |
| Old numeric provider and consumer | [Old.lean](../../Solutions/RamanujanNumerics.v1/ForwardRamanujan/Old.lean), [Baseline.lean](../../Solutions/RamanujanNumerics.v1/ForwardRamanujan/Baseline.lean), `ForwardRamanujan.baseline` |
| M1 provider and old-input implication | [Input.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Input.lean), `supplied_pi`, `pi_input`, `implies_old` |
| Actual existing M1 pi proof | [DDExpansionSolution.lean](../../Solutions/DudekPlattNumerics.v5/DDExpansionSolution.lean), [Applications.lean](../../Solutions/QRHPropagation.v1/Applications.lean), `QRHPropagation.pi_expansion` |
| Updated numeric certificate | [Updated.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Updated.lean), [Provider.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Provider.lean), `RamanujanNumerics.v2.challenge_epsilon_budget`, `c/updated.c` |
| Updated and paired actual gap/loss | [Consumer.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Consumer.lean), [Assembly.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Assembly.lean), `ForwardRamanujan.forward` |
| Matched-target programs | [Grouped.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Grouped.lean), `OldGrouped.lean`, `UpdatedGrouped.lean`, actual `c/oldgrouped.c` and `c/updatedgrouped.c` |
| Consumed kernel-only source certificate | [KernelSource.lean](../../Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/KernelSource.lean), `source_guard`, `execution`, `certified_upper` |

The Ramanujan program does not compute pi at an enormous endpoint. It evaluates
an explicit seven-term majorant, with upward binary64 input enclosures, scaling
and two subtractions. The actual prime-counting consequence is then obtained by
a generic analytic theorem. There was no authors' C implementation for this
obligation in the inspected snapshot: implementing its source model was new
baseline engineering, not a claim to reproduce the authors' executable.

The update changes five input literals and the positive offset from 0 to 119.
The sum loop, scaling 4096, fixed offset 134 and generic math/source proofs stay
unchanged. A subtraction-token wrapper adapter and the quantitative consumer
were already engineered **before** the old freeze. They are not attributed to
unchanged Table 4 infrastructure.

The generic Table 4 transport accepts a profile, but its cell geometry is fixed:
**30 cells, not arbitrary partitions**. The Ramanujan selected-sum source theorem
supports the stated bounded list interface; only the documented concrete
instances are claimed as checked pilot outcomes.

## Exact assumption and trust boundary

The QRH theorem is the zero-free open half-plane to the right of 7/8, with the
pole at 1 excluded. It is not full RH. [OpenAIQRH.v1](../../IEANTN/Nodes/OpenAIQRH/v1/Conclusions.lean)
records the source statement. The actual upstream proof supplied in the external
compatible replay is `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, pinned at
`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

| Entry | Remaining analytic hypotheses | Finite native facts |
|---|---|---|
| Frozen old Table 4 | Four historical Table 3 inputs + shared anchor | 8 |
| Actual-QRH updated Table 4 | Thirteen CH2 inputs + shared anchor | 8 |
| Actual-QRH Table 4 pair | Four Table 3 + thirteen CH2 + shared anchor = 18 | 16 |
| Frozen old Ramanujan | One asymmetric historical two-sided pi premise | 6 |
| Canonical `ForwardRamanujan.forward` | One refined-psi premise (both numeric providers supplied) | 12 |
| Actual-QRH forward pair | Thirteen CH2 inputs; QRH and both numeric providers supplied | 12 |
| `KernelSource.certified_upper` | Pure arithmetic bound; no analytic premise | 5 |

The canonical `FKS2Pair.assembled` also has an explicit QRH argument, for 19
mathematical arguments in total. The compatible actual-proof replay supplies it
and leaves the 18 listed above. The canonical forward assembly takes hpsi;
the compatible actual replay supplies hpsi from CH2 plus the real QRH theorem.
M1 implies the weaker historical old pi input on the common ray, so that input
is not an extra hypothesis of the **new paired** forward assembly. This does
not retroactively use QRH in the independently frozen old baseline.

The thirteen CH2 hypotheses are:

- `ZetaLogDeriv.v1.logDeriv_functional_equation`
- `GammaAsymptotics.v2.digamma_sub_log_isBigO_strip`
- `CH2.v2.proposition_2_4_upper`
- `CH2.v2.proposition_2_4_lower`
- `ZetaLogDerivValues.v1.logDeriv_laurent_alternating`
- `ZetaLogDerivValues.v1.logDeriv_neg_one`
- `ZetaLogDerivValues.v1.logDeriv_two`
- `ZetaLogDerivValues.v1.logDeriv_three_halves`
- `CotangentSeries.v1.cot_series_zeta_values`
- `ZeroCount.v1.rvm_error_bound`
- `ZeroCount.v1.rvm_error_small`
- `LowZeroes.v1.no_zeroes_below_first_ordinate`
- `ZetaHadamard.v1.logDeriv_partial_fractions`

All are used in the checked actual replay bodies. They are explicit hypotheses,
not claims that this pilot reproved those source papers. The shared Table 4
anchor is `FKS2.v6.table4_anchor_300`. The complete types, including all domains,
are in the linked conclusion files and supplied proof ledgers.

Each forward numeric instance has six finite native checks: source/operand
association, upward enclosures, input FP domain/representability, loaded-data and
sum execution/output bits, suffix rounding, and the final error budget.
`KernelSource.source_guard` uses only `propext`, `Classical.choice`, `Quot.sound`;
its reconstructed bound actually removes the native old source-match fact, but
leaves the other five. The original main forward pair keeps the preserved
six-plus-six paths. A domain-only kernel attempt blocked at reduction of the
first loaded input; the failed goal is in the external evidence package.

Generic math/source kernels and conditional pure consumers use the three
standard axioms. **Official three-axiom compliance is not established for the
concrete numeric endpoints.** Do not create Comparator receipts, relabel native
facts as standard axioms, or designate `lean-comparator` by hand. Native facts,
restricted C/RN64 semantics, compiler/runtime and hardware trust remain explicit.

## What IEANTN contributes

A node contains proposition definitions; metadata identifies imported
propositions and evidence kinds. Generated challenges state the conditional
implications. Separate Lake projects implement their proofs. Statement
fingerprints prevent an old result from silently changing meaning, and graph
checks keep the declared dependency network acyclic.

The numerical nodes supply epsilon-budget propositions. The gap nodes consume
the relevant pi bounds and those budgets. The assembled proofs supply the
numeric providers from actual source-associated execution and supply the improved
pi bound from the existing analytic theorem. Proof-body audits verify that both
old/new source proofs are consumed; appending an unused numerical lemma would
not pass the experiment. This separates statement reuse, proof reuse and evidence
strength without pretending that a new node automatically updates every program.

## Check status at the mathematical snapshot

- Table 4: both full source-linked endpoints/consumers and the actual QRH assembly
  checked; 13 Lean controls and 55 acceptance CLI cases passed.
- Forward: 12 selected canonical modules and 24 compatible modules checked; full
  actual body audit reaches the real QRH proof, both source certificates and all
  13 analytic inputs; 14 Lean controls and 110 CLI cases passed.
- Forward extraction/acceptance checks cover nine routes and 5,033 bound files;
  both experiments preserve their frozen source and evidence.
- Core build, generated challenges, fingerprints, import closure, graph, pins,
  unit tests and explicit-environment Pyright passed at the recorded snapshots.
- The complete network `check` exits 1 for **49 unchanged inherited receipt
  provenance diagnostics**: old receipts name `teorth/IEANTN`, while this clone is
  `hs-chae/IEANTN_test`. Other invariants pass. Keep the receipts unchanged and
  investigate any additional failure. Missing-issue/stale-view warnings remain.
- Same-pin inherited library objects and external Mathlib caches were reused.
  This is not a cold build of all inherited dependencies or a new official
  verification workflow. The relocated external source bundle was not given a
  second full cold replay.

**Rendering correction (November 4):** review found spaces and punctuation introduced into the
embedded font URL of the last forward report. Its earlier visual gate checked
font availability through browser fallback and did not detect the missing actual
font face. [FORWARD_REPORT.html](FORWARD_REPORT.html) repairs that rendering and
retains the original mathematical content; the original delivered report/archives
and their hashes stay unchanged. This handoff now checks the registered, loaded
font face and inspects Greek glyphs directly. The earlier claim of a successful
final font/render check is superseded; Lean results, numerical certificates and
source/evidence association tests are unaffected.

These are dated checked results, not a claim that a worker is still running or
that this documentation substitutes for rerunning the relevant checks after a
change. Local research acceptance JSON is distinct from official IEANTN receipts.

## Next single implementation task

The missing two-executable chain is concrete: there is not yet a source-verified
**coefficient calibration program A** feeding the current **epsilon program B**.
The existing QRH pi-coefficient theorem is analytic Lean, not program A.

Target [DudekPlattNumerics.v4](../../IEANTN/Nodes/DudekPlattNumerics/v4/Conclusions.lean),
specifically [Numerics.lean](../../Solutions/DudekPlattNumerics.v4/Numerics.lean)
and [CalculusAssembly.lean](../../Solutions/DudekPlattNumerics.v4/CalculusAssembly.lean):
verify the finite endpoint/normalization computation for M/m, preserve its theta
premise and integral domains, freeze the old source/consumer, then introduce a
justified updated input and feed its result to B. A differently shaped QRH input
requires a real analytic adapter and uniform integral bounds; do not assume them.

The focused implementation prompt is in the forward reports package. Use an
independent evaluator for a genuinely held-out update when available; otherwise
say controlled replay. Prove validity and source consumption, retain exact first
blockers, and report no improvement honestly. Do not expand the task into
optimality, a universal C frontend, every inherited analytic theorem or GPU work.

## Preservation rules for the next agent

- Add new versions instead of editing existing statement contracts/fingerprints.
- Preserve the old frozen sources/proofs and benchmark the new route separately.
- Keep the foreign compiler replay outside canonical `Solutions/` and never
  cross-load compiled objects between the two pins.
- Do not rerun the frozen generator CLI in the baseline directory: it writes the
  baseline files. Import its parameterized generator and write into a new version.
- Keep private context, transcripts, local caches and full proof-ledger archives
  outside publishable source. The companion artifacts are intentionally separate.
- Generated `STATE.md`, `GRAPH.md`, `docs/nodes/` are not branch handoff documents;
  do not commit regenerated views or fabricate receipts to remove a warning.
- Recheck live branch state and owner authorization before any later publication.
