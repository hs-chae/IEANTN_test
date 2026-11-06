# Casebook: ten real cases

Snapshots: PoC `qrh-2pv_B` `3280a3c` unless stated; upstream `466b41b`; Agent A's unpushed work at `091288d`
(read only, never built here). Evidence paths are relative to this study directory (`agentB/pv8_study/`).
Deep traces: C1, C2, C3, C4, C7 (each follows artifact → source binding → modelled execution → certificate →
native facts → statement → consumer). Program-to-program flows: C2 (A → B′), C7 (θ program → π program →
budget program), C10 (QRH → ψ profile → three program-verified providers → consumers).

Notation: `[N]` node conclusion, `(S)` solution project, `-->` import edge, `==>` proves, `{e}` evidence that is
not a graph edge.

## C1. FKS2 Table 4: from the published QRH-free profile to program-verified QRH transport

**Statements (PoC).**

| Node.conclusion | Statement | Imports | Designated |
|---|---|---|---|
| `FKS2.v8.table3_theta_300` … `_330` | `HasNumericalBound Eθ c (exp b)`, `c = 1.6930e-12 … 1.6795e-12` | none | `numerical` (FKS2 Table 3) |
| `FKS2.v6.table4_anchor_300` | `Eπ(e³⁰⁰) ≤ 1.6997e-12` | none | `numerical` (Table 4) |
| `QRHCH2.v5.psi_refined_bound` | `Eψ(x) ≤ (1/566) log²x · x^(−1/8)` for `x ≥ e³⁰⁰` | `CH2.v9.refined_transfer`, `OpenAIQRH.v1.zeta_seven_eighths` | `none-yet` |
| `FKS2Numerics.v6.old_pi` | `HasNumericalBound Eπ 1.69e-12 (exp 330)` | the four Table 3 rows, the anchor | `lean-noncompliant` |
| `FKS2Numerics.v5.numerical_pi` = `FKS2Numerics.v7.qrh_pi` | `HasNumericalBound Eπ (5/10^16) (exp 330)` (fingerprint `2af9dadb…`) | `QRHCH2.v5.psi_refined_bound`, anchor | `lean-noncompliant` (both) |
| `FKS2.v9.qrh_absolute_pi` | `∀ x ≥ e³³⁰, |π(x) − Li(x)| ≤ 5·10⁻¹⁶ · x/log x` | `FKS2Numerics.v7.qrh_pi` | `none-yet` (solution exists, 0 native facts, `evidence/axioms/consumer_FKS2.v9.txt`) |

**Trace, QRH 30-cell route** (designated for v5/v7):

```
QRHCH2.v5 ψ profile --(analytic: ψ→θ, Q(b) = b²/283·e^(−b/8))--> θ allowance per unit cell
  {e} Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c  (30 cells; sha256 0685e913…)
      source binding: include_str + PVCore token check (literals must equal the decoded data; comments rejected)
      modelled execution: binary64 sum with forward error (SumStability), RN64 ops
      certificate: B_safe(Q) < 5·10⁻¹⁶   (program output 4.7154676038087135e-16, compiled at -O0…-O3: same bits)
      native facts: 8 (attestation pv-evidence/FKS2Numerics.v7.qrh_pi…json at b985e41)
  ==> [FKS2Numerics.v7.qrh_pi]  --> [FKS2.v9.qrh_absolute_pi]  (step: normalisation inversion, 0 native)
```

**Other routes of the same statement**, recorded in the local registry, none a node: the 2-cell
`Table4Evolution.QRHTrunc.qrh_pi` (`qrh_trunc2.c`, output `4.9302189588862413e-16`, 1 native fact) and its
kernel-only twin `Table4Evolution.QRHTrunc.Kernel.qrh_pi` (0 native facts; 129–147 s and 25–26 GB to check, six builds here);
`QRHQuarter` (120 chunked cells, `4.7146e-16`). The QRH-free reconstruction (`FKS2Numerics.v6.old_pi`, 3-cell
`old_trunc3.c`, `1.68991e-12`) reads the Table 3 rows as inputs: its imports differ, so it is a different
conclusion, as it should be.

**The four questions the prompt asks.** Measured on matched pair M1 and the mutation matrix
(`PV_NODE_SPLIT_MUTATION_TESTS.md`):

| Change | Should be | Observed |
|---|---|---|
| (i) only the C source changes | evidence event | MT1–MT3: whitespace rebuilt 8 modules and the certificate still passed; a comment and a changed literal digit each failed in `Table4Evolution.QRHTrunc`. No fingerprint moved. Layout B's consumer was never rebuilt. The attestation pin stopped matching. `solution_drift` was silent for the node's own project (patched tool: reported) |
| (ii) the θ/ψ input profile changes | a new import statement → new version of whoever imports it | MT4 (`1/566` → `1/565` in the ψ profile): only `QRHCH2.v5.psi_refined_bound`'s fingerprint moved (`fingerprint --check` says to make a new version if it has dependants); Challenge files unchanged. In-memory receipts: A's consumer BROKEN; B's provider BROKEN, **B's consumer green**. Builds failed first in `QRHCH2.v5`'s own solution (`RefinedConsumer`), which the route imports; B's consumer still built |
| (iii) the target constant changes | new statement → new version | MT5 (`5·10⁻¹⁶` → `4.95·10⁻¹⁶` in the statement carrying it): its fingerprint moved, its receipt went BROKEN, the route failed. In B the consumer's fingerprint did not move, but its receipt went BROKEN (it records the provider's) and its proof failed (exact constant): a new statement in both layouts |
| (iv) proof route changes, type does not | new justification, no version | MT6: swapping the kernel route for the native one rebuilt only `Solution` (1 module); no fingerprint moved; the proof gains one native fact (`evidence/axioms/M1_*`); B's consumer untouched |

**A versus B.** M1 built both. B costs one more node, one more edge, 9 more files and 126 more hand-written lines,
and makes the provider a third copy of the v5/v7 statement. Its gain: the consumer step is its own Comparator unit
(3 GB, 4.7 s) and stays native-free whichever route the provider uses. With the kernel route the consumer in A is
also native-free, and its single solution peaks at the same 26 GB as B's provider. **Verdict:** for this
application today, A; the existing split (v7 → v9) was justified by R2 while the designated route was native.

## C2. Ramanujan, program A → program B′ (deep)

**Code**: `pilots/agentB-calibration` (programs, analytic adapters) and `pilots/pv-replay` (`PVReplay.Chain`,
`KernelChain`, `KernelOnly`). No node holds any of it.

```
[QRHCH2.v5.psi_refined_bound]
   │ analytic (NewInput.point/tail): seven calibration pieces, each < its target
   ▼
{e} program A  calibration_new.c  "calibration_deviation"
     7 literals × scale 4096, two exact subtractions; decoded by PVCore (kernel, decode_of_decodeL)
     certificate CertA: upperCheck … NewA.bound (= 457/5000) ∧ ops ∧ targets.sum ≤ scale·Σxs
     output contract: Σ targets ≤ Δ = 0.0914                      (C binary at -O0…-O3: 0.091397841972234092)
   ▼ analytic (calibrated_pi): π(x) ∈ S₅(x) + (120 ± Δ)·x/log⁶x for x > e⁹⁴⁰⁰       ← stateable with
   │                                                                                   DudekPlatt.v3.mainTerm
   ▼ data link (kernel equality of rationals): NewB.M = 600457/5000 = 120 + Δ
{e} program B′ ramanujan_9401_new.c "ramanujan_epsilon_bound"
     7 literals × 4096 − 134; certificate CertB: budgetCheck at (m, M, A, Y) = (0, 120.0914, 9400, 9401),
     bound 66389/625 = 106.2224            (C binary: 106.22239841212769; -O2 -mfpmath=387: 106.22239841212767)
   ▼ analytic (epsilon_shift_nonneg, gap_from_budget): C = 106.2224 − 119.9086 = −13.6862
[gap(x) > (1 + 13.6862/log x)·x²/log⁶x for x > e⁹⁴⁰¹]          (gap = RamanujanGap.v1.gap)
```

Native facts per route: `PVPilot.Updated` 2 (one certificate per program), `PVPilot.Kernel` 2 (literal decoding
only), `PVPilot.KernelOnly` 0 (attestations under `pv-evidence/@pv.PVPilot.*`).

**The mathematical contract between the programs** is the calibrated expansion. It is stateable today with
existing definitions only (`DudekPlatt.v3.mainTerm`, `primeCounting`), exactly like the existing
`DudekPlattNumerics.v5.pi_two_sided_qrh` (coefficients 119/131 for `x > e⁴⁰⁰`). M2's provider states it for
`x > e⁹⁴⁰⁰` with `Δ = 457/5000`. **Other consumers of A**: none in any snapshot (searched: no conclusion or
solution outside the pilots uses `NewChain.Δ`, `CertA` or the 9400 expansion).

**Layouts (M2).** A: one node, the chain in its solution. B: provider `pi_calibrated_9400` (program A) + consumer
`gap_9401` (program B′), the consumer proof written against B′'s constants and the provider's numbers only.
C (analysis only): stage nodes would need `Δ` as a statement (`NewA.bound` is a program constant, not a claim
about numbers) or `CertA` (a `PVCore.upperCheck` predicate over a source string) in a `Conclusions.lean`; both
are solution semantics, not mathematics. Measured (M2): A 9 files / 144 hand-written lines, B 18 / 337; builds 250.5 s (A) against 231.8 + 11.0 s (B), both peaking at 21 GB in `PVReplay.KernelChain`; fresh per-node closures 144 (A), 144 (B provider) and **145** (B consumer: its solution must import `PVReplay.KernelOnly`, whose `KernelChain` module holds both programs' kernel certificates). With native routes A carries 2 native facts, B's provider 1 and B's consumer 1.

**Which edits force what** (mutation matrix MT9, MT10, MT10b):

| Edit | Layout A | Layout B |
|---|---|---|
| MT9: program A's certified output weakened, `NewA.bound` 457/5000 → 458/5000 | fails in `CalibrationPilot.NewChain` (`m_val`, `M_eq`: the data link `M = 120 + Δ` no longer holds) | the provider fails in the same module, and **so does the consumer**: its own build compiles `NewChain` and fails there. Its proof never mentions `NewA`, but its solution imports `PVReplay.KernelOnly`, which imports `NewChain` (static closure: 145 modules, `NewA` and `NewChain` included) |
| MT10: a newline appended to B′'s C file | 0 modules rebuilt; build succeeds | same, in both projects |
| MT10b: one digit of a B′ literal changed | 0 modules rebuilt; build succeeds on the old embedded source: a stale certificate (shown by R2: with the files declared, the same edit fails the build) | same |

All restored byte-for-byte; trees clean (`evidence/mutations/MT9_*`, `MT10_*`, `MT10b_*`).

**Verdict.** Keep the chain as one composition in one solution (layout A). The calibrated expansion is a real mathematical contract, and M2 shows the consumer's proof can be written against it alone; but the solution modules couple both programs, so a provider node isolated neither failures (MT9) nor verification cost (145 modules). If the expansion gains a second consumer family, promote it (N2) and split the pilot's modules per program at the same time: the module split, not the node, is what isolates. Declare both C files to Lake first (MT10b).

## C3. Agent A's scoped winner and its evolution (deep, read only)

**What evolved, with the correct domains** (Agent A's own documents at each commit):

| Commit | Result | Ray | What changed underneath | Native facts |
|---|---|---|---|---|
| `e0c1ceb` (pushed in `qrh-2pv`) | `ScopedWinnerA.pi_00947147`: `HasPowerLogBound Eπ 0.00947147 0 (7/8) (exp 300)` | `x ≥ e³⁰⁰` | dyadic Lean evaluator; height grid refined from 8,192 to 16,384 cells (`SCOPED_WINNER_AGENT_A.md` L5) | 49 (bound), 50 joint |
| `00128be` (`PVEvolutionA`) | `0.009468286`; `0.009150521`; `0.009145878` | `e³⁰⁰`; `e³³⁰`; `e^330.5` | evolved provider: 65,536 cubic σ cells plus one base cell (`PV_EVOLUTION_AGENT_A.md` L11) | 49 per ray |
| `374bc27` (three-stage recovery) | `Parallel.pi330_friendly`: `0.009134616` | `e³³⁰` | 128 height profiles and a cubic 8,192-cell σ grid (`THREE_STAGE_RECOVERY.md` L18); 43 inherited facts kernel-checked | 21 → 10 |
| `b9b2e3c` | finite-window allowance `0.009131826` | finite window | Stage 3, 89 new solution modules | 67 |

So `0.00947147 → 0.009150521 → 0.009134616` mixes a domain change (`e³⁰⁰ → e³³⁰`: a different proposition), an
evaluator change (cells), and a trust change (native 49 → 21 → 10). Each coefficient is the program's output,
so each is a new statement; a provider that fixed a rounded target (as `FKS2Numerics.v7` fixes `5e-16`) would
absorb evaluator changes as evidence.

**The interface blocker, re-examined.** The winner's seven hypotheses:

| Hypothesis | Where defined | Stateable in a `Conclusions.lean` today? |
|---|---|---|
| `ZeroCount.v1.rvm_error_bound`, `rvm_error_small`, `LowZeroes.v1.no_zeroes_below_first_ordinate` | node conclusions | already are |
| `ZetaZeroFreeHalfPlane (7/8)` (QRH) | Vocabulary | yes (`OpenAIQRH.v1`) |
| `RiemannHypothesisUpTo WinnerOriginalScalars.height` | Vocabulary predicate, solution constant | yes, once the constant is written as a number |
| `WinnerDirectKernel.OriginalCHJSource` | `Solutions/WinnerDensityA.v1/…/DirectCHJPairing.lean:12` | **yes**: its body uses only `Chebyshev.psi`, `IEANTN.zetaZeroesSum`, `Ioo`, `Icc`, `exp`, `log`, `sqrt`. It is CHJ Theorem 1.2 eq. (1.5), a literature statement. Agent A's `091288d` registers the analogous CHJ-II Theorem 1.3 as the paper node `CHJII.v1` (`literature`) |
| `WinnerNewHeightSource.PrimaryInputs d δ` | `…/HeightPrimary.lean:11`, a structure of 8 fields | **no**: its fields use about 15 solution definitions (`mollifier`, `meanOne`, `meanTwo`, `sourceMoment`, `rightLine`, `rightVExact`, `rawRectangleBound`, `cSevenAt`, `sourceCEight`, `sourceFdiff`, `shifted`, `sourceOmega`, `scaledCriticalF`, `gaussianWeight`, `vertical`) |

Probe (`evidence/blocker/B1_*.log`, `B2_*.log`): a `Conclusions.lean` that imports `WinnerDensityA.DirectCHJPairing`
is rejected by both the PoC's and upstream's `check-closure` ("a Conclusions file may import only Mathlib,
Vocabulary, other Conclusions and any node's Tables"). **A provider node does not remove the blocker:** the
provider's challenge must state the seven hypotheses, and four of them are not stateable without transcribing
the definitions. The minimal legal path is (1) a paper node for CHJ eq. (1.5), as `CHJII.v1` already does for its
sibling, (2) node-local transcription of the `PrimaryInputs` objects into a source node's `Conclusions.lean`
(NODES.md L96–106 allows node-local definitions; Vocabulary only when a second node needs them), then (3) the
provider. Until then A is the only legal layout.

**Agent A's newest nodes** (`091288d`): `PrimeInterval.v2` (prime in `(x, x + x^{4/5}]` for `x ≥ e³³⁰`; imports
`CHJII.v1`, `FKS.v3.density_0618`, `ZeroCount.v1.rvm_error_bound`, QRH) keeps two numerical programs and three
native facts inside its own solution and says it cannot be officially verified as it stands: layout A by choice.
`QRHLambda.v1` consumes `QRHCH2.v5.psi_refined_bound`, adding a fifth consumer family to that profile.

## C4. A real shared numerical input

Three real cases, by the kind of evidence:

1. **`PlattTrudgian.v1.rh_up_to`** (`RiemannHypothesisUpTo 3·10¹²`, `literature`): 7 consumer nodes, 5 families
   for this conclusion (`FKS`, `MT`, `PlattTrudgian2021`, `QRHCH2`, `QRHConsequences`), plus `CH2` through
   `rh_up_to_exact`. No proof is in the repository, so layout A cannot even be written without changing every
   consumer's proposition (each would have to carry `RiemannHypothesisUpTo 3e12` inside its statement); a node
   is the only representation (R0/N1). Two of its families are QRH variants of others.
2. **`DudekPlattNumerics.v5.pi_two_sided_qrh`** (`pipeline`, program-verified, `none-yet`): consumed by
   `DudekPlatt.v5.ramanujan_401` (core bridge, with `DudekPlatt.v3.criterion`) and `RamanujanGap.v2/v3` (solutions).
   Its proof (`DDExpansionSolution`, 112 modules statically, no native fact) and both consumers are real.
   **Matched pair M3** builds layout A (two consumer nodes, each solution carrying the provider's proof) against
   the repository's layout B. Measured: layout A's two consumers each carry the 112-module proof (fresh closures 121 and 116 modules); layout B checks it once (provider, 112 modules), with consumers of 11 modules and 0 (a core bridge). All five challenge theorems use the three standard axioms only. A comment in a module of the proof rebuilt exactly one module in each layout (mutation MT11), but that module lies in both A consumers' closures and in neither B consumer's.
3. **BKLNW Table 8** (`BKLNW.v1.Tables`, 58 rows): the data live once in `Tables.lean`; `BKLNW.v1` (paper,
   `literature`) and `BKLNWNumerics.v1` (computation, `numerical`) state the same two claims, identical
   fingerprints, to separate evidence kinds; consumers are `BKLNW.v2–v4` (one family). A `Tables.lean`-only
   alternative already exists for the data; the claim that the rows satisfy an inequality has to be a conclusion.

**Two-consumer demonstration.** M3 is it: one statement, two families, and both layouts built.

## C5. Duplicate statements

| Group (PoC) | Imports equal? | Designated | Cause | Least-disruptive treatment |
|---|---|---|---|---|
| `FKS2Numerics.v5.numerical_pi` / `v7.qrh_pi` | yes | both `lean-noncompliant` | a new proof route registered as a version (`154b1d0`) | leave both (identity survives); record v7's route as a spare of v5; optionally two trivial bridges + `deprecate v7 --for v5` |
| `FKS2.v7.absolute_pi_bound` / `FKS2.v9.qrh_absolute_pi`, and the two `strict_*_improvement` | no / yes | `none-yet` | cascade of the above | same |
| `FKS2Numerics.v1` / `v2` (4 conclusions) | yes | `numerical` | v2 corrected one value and restated four unchanged ones | normal versioning; nothing to do |
| `BKLNW.v1` / `BKLNWNumerics.v1` (2) | yes | `literature` / `numerical` | deliberate evidence-kind split | deliberate; nothing to do |
| `Hiary2016.v1` / `KLN.v1` | no | `literature` / `literature` | two independent papers prove the same bound | genuine independent provenance; keep |
| others (`FKS.v1/v2`, `BKLNW.v1/v2`, `CH2.v6/v8`, `QRHCH2.v2/v4`) | mostly no | mixed | version restatements with different imports | normal |

Statement identity is the fingerprint (`Tools/Hash.lean`: binder-erased structural value, IEANTN constants
followed); provenance is the import set plus the designated justification. Only `FKS2Numerics.v5/v7` (and its
cascade) is an architectural artifact: the tooling ties a Lean proof to `Solutions/<NodeId>/`, so a second route
found no home but a new node. M1's layout B shows how easily it recurs: the provider became a third copy.

## C6. Native-backed provider, kernel-only consumer

| | `FKS2Numerics.v7` → `FKS2.v9.qrh_absolute_pi` | `RamanujanNumerics.v3` → `RamanujanGap.v3.gap_lower_bound` |
|---|---|---|
| Provider statement | `HasNumericalBound Eπ (5/10^16) (exp 330)` | budget `ε(x) ≤ 9.988` on `x > e⁴⁰¹` |
| Provider native facts | 8 (30-cell route) | 1 (`RamanujanNumerics.v3.Provider.certificate`) |
| Provider official | `lean-noncompliant`, no receipt | `lean-noncompliant`, no receipt |
| Consumer axioms | standard three (attested 0; `#print axioms` here) | standard three (attested 0) |
| Consumer official | `none-yet`; Comparator-eligible in shape | `none-yet`; Comparator-eligible in shape |
| Consumer's transitive leaves (upstream `graph_leaves`) | 15: the provider, 13 analytic premises, itself | 15: `DudekPlattNumerics.v5`, `RamanujanNumerics.v3`, the analytic premises, itself |
| Single-node alternative | M1 layout A with the native route: the consumer theorem gains `Table4Evolution.QRHTrunc.certificate._native.native_decide.ax_1_1` | the existing replay `RamanujanGap.v3.gap_from_psi` (A for both providers): standard + 1 native fact |

The consumer's eligibility is real and local: its own proof imports only statements. Its trust is not raised: the
provider remains a leaf, visible in the dependency report. No laundering is possible through the edge because
Comparator checks each compared theorem's axioms and the report walks every import. What would launder is a
`lean-comparator` label on a native provider, or a local attestation displayed like a receipt; neither happens
in the PoC (attestations carry "LOCAL RESEARCH ATTESTATION … Not an IEANTN verification receipt").

## C7. Kernel-only and two-backend composition (deep)

`pilots/pv-twobackend`, library `ThreeChain` (no node):

```
stage 1  Agent A θ program (Lean dyadic evaluator, WinnerDensityA.ReversResult / source_theta300)
         output: Eθ(x) ≤ K·x^(−1/8), x ≥ e³⁰⁰   (K = 0.009782+1e-12, or 0.009904+1e-12 from original inputs)
         native facts: 17 (WinnerOriginalScalars 14, WinnerOriginalDensity 2, SharpCertificate 1)
stage 2  power_agentA.c / power_agentA_source.c (C, PVCore, kernel-only) → Eπ(x) ≤ 0.0098163·x^(−1/8), x ≥ e³³⁰
         interface lemma Link330.pi_input_330_of (K ≤ 1/100 → Ramanujan π input)
stage 3  budget_331.c (C, kernel-only) at (0, 122.5, 330, 331), bound 112.15
final    PVThreeChain.gap_exceeds_leading: gap(x) > (1 + 7.84/log x)·x²/log⁶x, x > e³³¹
```

Hypotheses of the final theorem are Agent A's solution-level source structures (`WinnerDensityA.CH2Source` /
`OriginalInputs`), so no layout B exists for stage 1 (C3). Stage 2's output is a Vocabulary statement
(`HasPowerLogBound Eπ 0.0098163 0 (7/8) (exp 330)`) but has one consumer.

**Existing dependency view.** Lake's module graph *is* the program DAG: stage modules import the stage below
through `PVCore` and the link lemma. Round-3 changed-input replay (`../evidence/pv6/threechain_source_build.log`,
stage-1 input `0.009782 → 0.009904`): rebuilt the generated data module, `PowerAgentASource` (52 s), `Link330`
and `ChainSource` (≈6 s each), Agent A's `SharpCertificate` on first build (298 s); `StageB331` and its
certificate **replayed**. It also re-built `Table4Evolution.Partition/Bounds/Instance/PowerTransport/PowerAgentA`
(44 s) although none changed: Lake traces a module differently when it is reached from another root package.
Rebuild scope is therefore an upper bound on what changed, not an exact one. No new graph engine is needed to
see the stage DAG; it is not a mathematical dependency either.

**Freshness of the stages.** This chain's C sources are declared to Lake (`budget_301.c`, `budget_331.c` in
`pv-twobackend`; `power_agentA*.c` in `Table4Evolution.v1`), so a stage-source edit rebuilds the stage, as
MT1–MT3 show for the same mechanism. The A→B′ pilot of C2 is the counterexample: its sources are not declared,
and MT10/MT10b changed stage B′'s source without any rebuild, in both layouts. Whether a chain notices a stage
edit depends on four lines of Lake configuration per file, not on how the chain is split into nodes.

## C8. Negative controls: results that should not become nodes, and odd nodes that exist

| Candidate | What it is | Rule (N1–N3, rule stress test §4) | Verdict |
|---|---|---|---|
| hypothetical `PowerTransport.v1` (first study) | kernel-only power transport `0.013156` from `e³³⁰`; no consumer | N1 no, N2 no, N3 no | reject; stays a solution theorem |
| M1/M2 layout-B providers | kernel-only, one consumer | no, no, no | reject |
| `Table4Evolution` routes (2-cell, 3-cell, 120-chunk, kernel) | routes of existing statements | — | justifications/registry entries, never nodes |
| Agent A's winner | solution result, two solution-level consumer families | N2 not at node level; hypotheses not stateable | reject now |
| `Wedeniwski.v1` (exists) | ZetaGrid verification height, `asserted`; one consumer (`Kadiri2005.v1`), 8 families transitively | N1 | needed (a website claim can only be a node) |
| `DudekPlattNumerics.v4` (exists, no consumer) | Comparator-checked formalization of `DudekPlattNumerics.v3`'s cited bound from `MT.v2.corollary_1` | not a promotion: a version (new imports) | fine; `DudekPlatt.v4` could migrate to it |
| `PrimeInterval.v2` internals (Agent A) | two programs, three native facts inside a consumer | N3 yes | the rule predicts a split (or a kernel route); the author kept A |

The rule rejects five plausible-looking candidates and accepts every existing provider except two versions,
which the versioning rule covers.

## C9. Program improvement with no mathematical change

`FKS2Numerics.v7.qrh_pi` (`HasNumericalBound Eπ (5/10^16) (exp 330)`, one fingerprint throughout):

| Route | Program | Native facts | Where recorded |
|---|---|---|---|
| designated (v5/v7) | 30-cell `fks2_table4_transport.c` | 8 | `formalization.yaml` |
| `PVTable4.QRH.qrh_pi` (pv-replay) | same C, shared contract | 4 | `endpoints.json` |
| `Table4Evolution.QRHTrunc.qrh_pi` | 2-cell `qrh_trunc2.c` | 1 | `endpoints.json` |
| `Table4Evolution.QRHTrunc.Kernel.qrh_pi` | same 2 cells | 0 | `endpoints.json` |
| `PVChunked.Table4QRH.qrh_pi` | 30 cells, chunked sum | 4 | `endpoints.json` |

Same for `RamanujanNumerics.v1.epsilon_budget` (6 → 1 → 0 across replays). None of these needed a node, a
version or a fingerprint change; the one time a route was made a node (`FKS2Numerics.v7`) it produced the duplicate
of C5. What must be refreshed on such a change: the local attestation (it pins source and module hashes), the
justification note, and a receipt only if the designated route changes (M1 mutation MT6 measures the
route swap). Mutation MT6 swapped the kernel route for the native one under the same statement: only `Solution` was rebuilt (1 module, 11 s), no fingerprint moved, the drift line named `Solution.lean` (inside the node's own project, so the current tool sees it), and the consumer of layout B was not rebuilt at all.

## C10. Propagation through the network

```
OpenAIQRH.v1 (QRH) + CH2.v9.refined_transfer
   └─> [QRHCH2.v5.psi_refined_bound]   5 consumer families at 091288d:
          ├─> [FKS2Numerics.v5/v7.qrh_pi]  (program, 30 cells)  ─> [FKS2.v7/v9 absolute π]
          ├─> [DudekPlattNumerics.v5 π expansion] (large kernel proof) ─> [DudekPlatt.v5 Ramanujan ≥ e⁴⁰¹]
          │                                                          └─> [RamanujanGap.v2/v3 loss, gap]
          ├─> [QRHPropagation …] and theta frontier ─> (S) tertiary intervals 1/24 from 1339, counts, Mills
          ├─> (pilots) A→B′ chain: gap > (1 + 13.6862/log x)x²/log⁶x, x > e⁹⁴⁰¹
          └─> [QRHLambda.v1] weighted Σ Λ(n)/n (Agent A, 091288d)
```

(a) **Evidence for fixed statements**: every route of C9; the kernel-only replays; re-designations. (b) **Stronger
results that need new statements**: `RamanujanNumerics.v3` (range `e³⁹¹⁵ → e⁴⁰¹`), the A→B′ chain at `e⁹⁴⁰¹`
(stronger than `RamanujanGap.v2` on that sub-ray), Agent A's coefficient sequence, `PrimeInterval.v2`. Node
granularity matters for discoverability exactly at the statements in (b) that someone else imports; the graph
edges already carry the mathematics (`psi_refined_bound` is visibly the hub). The tertiary results live in
solutions and are invisible to the graph: that is the discoverability cost of layout A, paid only when nobody
imports them.
