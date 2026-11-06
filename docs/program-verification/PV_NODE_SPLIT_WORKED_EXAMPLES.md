# Program verification and nodes: worked examples

Companion to `PV_NODE_SPLIT_DECISION_REPORT.md`. Every node id, statement and count below was read from
a repository ref, not from memory:

- **upstream**: `teorth/IEANTN` `main` at `466b41b` (2026-11-02);
- **PoC**: the owner fork `hs-chae/IEANTN_test`, branch `qrh-2pv_B` at `3280a3c`. It descends from the
  fork's `QRH_phase2` (`d85631a`), which sits on upstream `ef21db9`;
- **Agent A, unpushed**: local branches `poc/maximal-pv-evolution-a` (`00128be`) and
  `poc/three-stage-recovery` (`374bc27`), read only.

Designs, as in the report: **A** evidence only, **B** separate mathematical provider node, **C** one node
per program stage, **D** selective hybrid. In the diagrams `[N]` is a node, `(S)` a solution project,
`-->` an import edge, `==>` "proves", and `{e}` a piece of evidence that is not a graph edge.

## 0. One application, two layouts, measured

The application is the power-form `π` transport of the round-3 extension: from the QRH `θ` frontier and
FKS2's Table 4 anchor, `Eπ(x) ≤ 0.013156·x^{-1/8}` for `x ≥ e^330`. The C program `power_network.c`
and its kernel-only certificate already exist (`Solutions/Table4Evolution.v1`).

Built in a disposable local worktree (branch `agentB/pv-node-split-exp`, never pushed). The diff is
`PV_NODE_SPLIT_HYPOTHETICAL.diff`.

```
Layout A (evidence only)                       Layout B (provider node)
                                                [QRHPropagation.v2.theta_frontier]──┐
(S) Table4Evolution.v1                          [FKS2.v6.table4_anchor_300]─────────┼─> [PowerTransport.v1.pi_power_network]
    PowerNetwork.pi_power  (solution theorem,                                       │      <== (S) PowerTransport.v1:
    hypotheses = the two premises; no node)                                         │          Solution.lean, 1 line:
                                                                                    │          Table4Evolution.PowerNetwork.pi_power
    0 nodes, 0 edges                                                                1 node, 2 edges, 1 fingerprint
```

| Measure | Layout A | Layout B |
|---|---|---|
| Files / lines added | 0 | node 5 / 128; solution 5 / 319 |
| Core rebuild | none | 15.6 s, 6 modules |
| Fingerprints | unchanged | 1 new; 240 unchanged |
| Verification | local gate: passed, 0 native | NODES.md preview: challenge type identical, 3 standard axioms; Comparator-eligible in shape, no receipt |
| Byte change in `power_network.c` | certificate rebuilds; gate SHA-256 changes | the same, through the cross-project import; `solution_drift` of the node's project sees nothing |
| What the rule says | correct: one possible consumer, kernel-only, small | not warranted (no R1–R4) |

The same comparison on an existing pair, `FKS2Numerics.v7.qrh_pi` → `FKS2.v9.qrh_absolute_pi`, comes
out the other way: there the provider is native (8 facts) and its kernel route needs 28 GB, so R2 and R4
hold and the split is justified. Report §7 has both layouts as yaml and Lean.

## 1. FKS2 Table 4: the 30-cell C program and its evolutions

**Actual nodes (PoC).**

| Node.conclusion | Statement | Imports | Designated |
|---|---|---|---|
| `FKS2.v8.table3_theta_300` … `_330` | `HasNumericalBound Eθ 1.6930e-12 (exp 300)` … `1.6795e-12 (exp 330)` | none | `numerical` (published Table 3) |
| `FKS2.v6.table4_anchor_300` | `Eπ (exp 300) ≤ 1.6997e-12` | none | `numerical` |
| `QRHCH2.v5.psi_refined_bound` | the QRH `ψ` profile | `CH2.v9.refined_transfer`, `OpenAIQRH.v1.zeta_seven_eighths` (v7's note counts 13 inherited analytic premises) | `none-yet` |
| `FKS2Numerics.v5.numerical_pi` | `HasNumericalBound Eπ (5/10^16) (exp 330)` | `QRHCH2.v5.psi_refined_bound`, `FKS2.v6.table4_anchor_300` | `lean-noncompliant` (30-cell C transport, native facts) |
| `FKS2Numerics.v7.qrh_pi` | **the same statement** | **the same imports** | `lean-noncompliant` ("Preserved FKS2Numerics.v5 C/output proof … paired generic transport") |
| `FKS2Numerics.v6.old_pi` | `HasNumericalBound Eπ 1.69e-12 (exp 330)` | the four `table3_theta_*`, the anchor | `lean-noncompliant` |
| `FKS2.v7.absolute_pi_bound` | absolute `π` bound | `FKS2Numerics.v5.numerical_pi` | `none-yet` |
| `FKS2.v9.{old,qrh,paired}_absolute_pi` | absolute `π` bounds | `FKS2Numerics.v6.old_pi`, `.v7.qrh_pi` | `none-yet` |

`FKS2Numerics.v5.numerical_pi` and `FKS2Numerics.v7.qrh_pi` have the same fingerprint, `2af9dadb…`
(`IEANTN/Nodes/FKS2Numerics/v{5,7}/fingerprints.json`). Version 7 was added on 2026-11-03 (`154b1d0`,
"Reuse frozen transport for preserved QRH source and paired consumers") for a new proof route of an
unchanged proposition. The duplication then reached the consumers: `FKS2.v7.absolute_pi_bound` and
`FKS2.v9.qrh_absolute_pi` also share a fingerprint, as do `FKS2.v7.strict_allowance_improvement` and
`FKS2.v9.strict_historical_improvement`. One change of evidence produced 2 nodes and 3 duplicate statements.

**Sources and evidence routes.** `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` (30 cells) is the
program of both v5 and v7. The round-3 work added `Solutions/Table4Evolution.v1` (2-cell `qrh_trunc2.c`,
3-cell `old_trunc3.c`, kernel-only routes) without new nodes: the local gate registry
(`scripts/native_assisted/endpoints.json`) records each route against the node's own challenge
(`challenge_module`, `replays`). Measured routes per conclusion: `FKS2Numerics.v7.qrh_pi` 5,
`FKS2Numerics.v6.old_pi` 4.

**Where each thing should live.**

| Item | Where | Why |
|---|---|---|
| the four Table 3 `θ` rows | node conclusions (`FKS2.v8`), as now | statements of record with their own (`numerical`) evidence; the transport imports them |
| their whole-tail hypotheses (`x ≥ e^300` etc.) | inside each conclusion's statement | they are part of the claim, and the fingerprint covers them |
| the list of `θ` values a program reads | generated data in the solution (`Table4Evolution/Data/*.lean`) | it is the program's input, not the paper's table; `Tables.lean` holds a paper's data and may not prove anything (NODES.md L238–266) |
| C text, decoded literals, certificates, the transport theorem | the solution project | implementation; a node imports statements, never proofs (ARCHITECTURE §1) |
| which proof routes exist and their trust tier | justification list (one designated) plus a local evidence registry | evidence, not mathematics |

**Source change against coefficient change.**

- *Source change, same proposition* (v5's 30 cells → round 3's 2 cells → kernel route; outputs `4.715e-16`,
  `4.930e-16`, all `≤ 5e-16`): the registered statement is the target `5e-16`, so nothing mathematical
  moved. This should be a new justification (or a registry entry), not a node. v7 shows what happens
  otherwise.
- *Coefficient change in the statement* (registering `4.715e-16` instead of `5e-16`, or a new QRH profile
  in place of `QRHCH2.v5`): the proposition or its imports change, so a new conclusion is right, through
  `new-version` (ARCHITECTURE §5 L342–358).

**Designs.**

```
A  [QRHCH2.v5]──┐
   [FKS2.v6]────┼──> [FKS2.v9.qrh_absolute_pi] <== (S: transport + absolute-bound proof)   1 node, 2 edges
                │
B  [QRHCH2.v5]──┼──> [FKS2Numerics.v7.qrh_pi] <== (S: C program)
   [FKS2.v6]────┘            └──> [FKS2.v9.qrh_absolute_pi] <== (S: 2-line consumer)       2 nodes, 3 edges (as now)

C  [Table3 rows]─>[Table4Data]─>[CellSum program]─>[Bsafe bound]─>[qrh_pi]─>[FKS2.v9]          ≥5 nodes; program
                                                                                              semantics in Vocabulary
D  = A for this case, unless a criterion below holds
```

**When a standalone `FKS2Numerics` node helps.** The provider here has one consumer family (`FKS2`), so
reuse does not justify it. What does is **evidence separation**: while the transport rested on native
facts (`lean-noncompliant`, a leaf of the trust graph, ARCHITECTURE L220), keeping it in its own node let
the consumer's analytic step stay Comparator-eligible with the numeric bound as an explicit imported leaf.
Comparator checks the axioms of each compared theorem, so a consumer proof that composed the native
transport inside it would itself become `lean-noncompliant`. After round 3 the 2-cell route proves
`qrh_pi` with 0 native facts, so that reason is gone for `qrh_pi`. The existing node stays, since node
identity survives refactoring (ARCHITECTURE L459–463); a new provider node would not be justified by
this reason any more.

## 2. Ramanujan: the A→B′ program chain

**Actual nodes (PoC).** `RamanujanNumerics.v1/v2/v3.epsilon_budget` (computation, `lean-noncompliant`,
no imports): a uniform budget `ε(x) ≤ 9.101` and variants. Consumers `RamanujanGap.v1/v2/v3` (pipeline,
`none-yet`), which also import a `π` input: `DudekPlattNumerics.v7.pi_asymmetric_pnt` (old, PNT+,
`numerical`) or `DudekPlattNumerics.v5.pi_two_sided_qrh` (QRH, `S₅(x)+119x/log⁶x < π(x) < S₅(x)+131x/log⁶x`
for `x > e^400`).

**The chain** (`pilots/pv-replay/PVReplay/Chain.lean`; `IEANTN_PV_COMPOSITION.md` §1):

```
θ input ─> stage A calibration_deviation (7 pieces × 4096)   output contract Σ ≤ Δ = 0.0914
        ─> calibrated π: π(x) ∈ S₅(x) + (120 ± Δ)·x/log⁶x, x > e^9400        (analytic)
        ─> data link: B′'s M = 120 + Δ (kernel equality of rationals)
        ─> stage B′ budget at (0, 120.0914, 9400, 9401)
        ─> (1 + 13.6862/log x)·x²/log⁶x < gap(x), x > e^9401                 (analytic)
```

**Is the intermediate reusable?** Δ alone is a program constant. The *calibrated π statement* is
mathematics of the same type as `DudekPlattNumerics.v5.pi_two_sided_qrh` (a two-sided `S₅` expansion with
explicit constants), so it could serve any Ramanujan-type consumer. Today it has exactly one consumer
(B′). If a second appeared, the right promotion is a `π`-input conclusion of that existing shape, not a
"Program A" node.

**Does splitting A and B′ improve trust tracking?** No. The chain already carries its trust per stage:
13 native facts (A 7, B′ 6) became 2 (round 2) and 0 (round 3 kernel route). Splitting would not change
those counts; with 0 native facts the composed chain is one Comparator-eligible proof. The link negative
control (`tests/LinkMismatch.lean`, `0.0913` against A's `0.0914`) is a kernel equality inside one
solution and needs no graph edge.

**Alternative inputs and source versions.** The old (PNT+) and QRH inputs are different imports, so their
consumers are different conclusions; the network already versions them (`RamanujanGap.v1` against `.v2`,
`RamanujanNumerics.v1` against `.v2`). Source versions of the same budget are evidence: the registry
holds 5 routes for `RamanujanNumerics.v1.epsilon_budget` (its own solution and 4 kernel replays).

```
A  [π input]──> [RamanujanGap.vN] <== (S: A, link, B′, consumer)           1 node per input version
B  [π input]──> [calibrated π, vN] ──> [RamanujanGap.vN]                     +1 node, +1 edge per input version
C  [θ]─>[stage A]─>[Δ]─>[stage B′]─>[budget]─>[gap]                          +4 nodes; Δ is not a theorem
```

## 3. Agent A's scoped winner and evolved programs

**Statements.** `ScopedWinnerA.pi_00947147` (PoC, `Solutions/ScopedWinnerA.v1/ScopedWinnerA/Result.lean:28`):

```
(hCHJ : OriginalCHJSource)                                   -- Solutions/WinnerDensityA.v1, DirectCHJPairing.lean:12
(hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)     -- node conclusions
(hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)                               -- node conclusion
(h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))  -- structure in Solutions/, HeightPrimary.lean:11
(hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)           -- Vocabulary predicate, solution constant
(hQRH : ZetaZeroFreeHalfPlane (7/8))                                 -- Vocabulary
: HasPowerLogBound Eπ (947147/100000000) 0 (7/8) (exp 300)          -- Vocabulary
```

Later, on Agent A's unpushed branches: `0.009468286` from `e^300`, `0.009150521` from `e^330` and
`0.009145878` from `e^330.5`, 49 native facts per ray (`00128be`, `PVEvolutionA.v1`); then
`Parallel.pi330_friendly`, `0.009134616` from `e^330`, 21 native facts, reduced to 10 by kernel checks
(`374bc27`, `docs/qrh/THREE_STAGE_TRUST.md`). Agent A's latest commit (`b9b2e3c`) adds a Stage 3 with 89
new solution modules and a finite-window allowance `0.009131826` (67 native facts), still without an `Eπ`
coefficient. All of it lives in solution projects; no node.

**Theorem change against evaluator change.** `e^300 → e^330` changes the domain, so it is a different
proposition. `0.009150521 → 0.009134616` on the same ray changes the coefficient, so it is also a
different proposition, although what changed underneath was the evaluator configuration (65,536 cubic
cells against 128 height profiles × 8,192 cells). The coefficient is the program's output, so an evaluator
change becomes a statement change unless the contract fixes a target. A provider contract that states a
rounded target (as `FKS2Numerics.v7` states `5e-16`) absorbs evaluator changes as evidence.

**The blocker.** `OriginalCHJSource` and `PrimaryInputs` are defined over solution-level analytic objects
(`mollifier`, `sourceMoment`, `rightVExact`, `rawRectangleBound`, `WinnerBetaA.Minkowski.gaussianWeight`).
A node can import them only as conclusions of some node, and a `Conclusions.lean` may import only
Mathlib, Vocabulary, other Conclusions and Tables (`ieantn.py` `check_closure`, L1135–1155). A provider
node therefore does not remove the blocker. It forces the blocker to be resolved first, by transcribing
those definitions into a `Conclusions.lean` (node-local is enough: NODES.md L105–106) and stating the
seven source facts as conclusions of a source node, with equality adapters in the solution. An abstract
interface in the style of `Lcm.v2` (hypotheses internalised into the `Prop`, ROADMAP L463–470) needs the
same definitions in order to state the hypotheses. Vocabulary is not needed until a second node uses
them (ARCHITECTURE L454–457).

**Recommendation for this case.** Design A now: solution-level results, recorded in the local registry
with their seven inputs listed. Promote only when the source facts are registered as their own node for
an independent reason (they are KLN/HPY/Hiary statements that other work could cite), or when a second
consumer family needs a winner coefficient. Agent A's note (`PV_EVOLUTION_AGENT_A.md` L23) proposes
lifting the objects to public vocabulary and registering provider/consumer conclusions; that would be a
global Vocabulary change for one consumer.

```
A  (S: 7 Winner* projects) ==> pi_00947147        0 nodes; 3 hypotheses are node conclusions, 4 are not
B  [WinnerSources] ──> [WinnerPi.v1] ──> consumer   needs ~10 analytic definitions transcribed first
```

## 4. A real numerical computation with several consumers

Counted by **consumer family**, since versions of one family are not independent consumers (PoC):

| Provider | Kind | Import edges | Consumer nodes | Consumer families |
|---|---|---|---|---|
| `PlattTrudgian.v1` (`rh_up_to`, `rh_up_to_exact`) | computation | 13 | 8 | **6** (CH2, FKS, MT, PlattTrudgian2021, QRHCH2, QRHConsequences) |
| `ZetaLogDerivValues.v1` | computation | 36 | 7 | 1 (CH2 versions) |
| `LowZeroes.v1` | computation | 7 | 6 | 1 (CH2) |
| `BKLNW.v1` (with `Tables.lean`) | paper | 12 | 3 | 1 (FKS2) |
| `FKS2Numerics.v1` | computation | 15 | 1 | 1 (FKS2.v1) |
| `RamanujanNumerics.v1` | computation | 4 | 2 | 1 (RamanujanGap) |

`PlattTrudgian.v1` is the network's genuine multi-family computation: `RiemannHypothesisUpTo (3·10¹²)`,
externally meaningful, cited by six families, justified by `literature`. A computation node exists and
should.

`BKLNW` shows the cost side. `BKLNW.v1.Tables` (Table 8, 58 rows) is the single copy of the data,
imported by `BKLNW.v1–v4` and `BKLNWNumerics.v1`. `BKLNWNumerics.v1` restates
`BKLNW.v1.table8_psi_bound` and `theta_error_le_one` with identical fingerprints, "split off `BKLNW.v1`
so the paper node is not also a computation node" (its `Conclusions.lean`); the paper's version is
`literature`, the computation's is `numerical`. So the network already pays one duplicate statement per
claim to separate evidence kinds, and avoids data drift by importing one `Tables.lean`.

Against `Tables.lean` + solution: a table that a program reads is data; a claim that the table's rows
satisfy an inequality is a conclusion; the program that checks it is a solution. A separate computation
node is warranted when the claim is externally meaningful (finite RH, zero counts, a published table's
bound) or has several consumer families, not when a program happens to produce it.

## 5. Two backends and a one-stage update

`pilots/pv-twobackend` (PoC, outside the node graph):

```
Agent A θ (Lean dyadic, revers_source_theta300; 17 native)
   ─> power transport (C, power_agentA.c; 0 native) ─> Eπ ≤ 0.0098163·x^{-1/8}, x ≥ e^330
   ─> Ramanujan budget (C, budget_331.c; 0 native) ─> (1 + 7.84/log x)·x²/log⁶x < gap(x), x > e^331
```

The update replaced stage 1's input (`source_theta300`, original inputs, `0.009904`). Measured rebuild
(`agentB/evidence/pv6/threechain_source_build.log`, `rebuild_t4_final.log`): the generated data module
(1.3 s), `PowerAgentASource` (51 s), `Link330` and `ChainSource` (about 6 s each), and Agent A's
original-input closure on first build (`SharpCertificate`, 298 s). `StageB331` and its certificate were
replayed, not rebuilt.

**What goes stale, by design.**

| Change | A: one solution, local attestation | B/D: provider node per stage interface |
|---|---|---|
| stage-1 source bytes change, same output | chain attestation stale (it pins all sources by SHA-256); stage 1 re-proved | stage-1 evidence stale; downstream receipts untouched (statement fingerprints unchanged) |
| stage-1 output changes (`0.009782 → 0.009904`) | stage 2 data regenerated and re-proved; consumer re-proved | the interface statement changes, so stage 2's conclusion changes (`0.0098163 → 0.0099388`): new versions of stage 2 and the consumer |
| compiler/toolchain bump | nothing (Lean checks the modelled source; no binary is trusted) | same |

The re-verification work is the same in both designs; nodes change only the bookkeeping. Upstream's own
tooling has a gap in both designs: `solution_drift` (`ieantn.py` L2355–2385) diffs only the receipt's own
solution folder, so a C file in another solution project that the proof imports is invisible to it
(§0; report §7).

## 6. Graph size

| | Nodes | Statements | Note |
|---|---|---|---|
| upstream `466b41b` | 65 | 136 (128 distinct) | 17 computation nodes, 5 duplicate-statement groups |
| PoC `3280a3c` | 116 | 243 (226 distinct) | 27 computation nodes, 14 duplicate-statement groups |
| PoC + design C | about 116 + 36 | + the same | 33 C programs and 3 Lean dyadic program constants, each a stage; their interfaces need `PVCore.Exec` semantics (1,114 lines) in Vocabulary, which is Mathlib-only |
| PoC + design D | 116 + 0 to 2 | | only the providers that meet the rule (report §6) |
