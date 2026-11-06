# Matched A/B experiments

Three applications, each built twice in isolated disposable worktrees on the same base, machine and toolchain.
Layout **A**: one conclusion; the program, its certificate and the composition stay in that conclusion's
solution. Layout **B**: a provider node states the program's output as mathematics; the consumer imports that
statement. Layout C (one node per program stage) was not built: its interfaces would need program semantics in
`Conclusions.lean` (casebook C2 and C7).

## Setup (common to all three)

| Item | Value |
|---|---|
| Base | `qrh-2pv_B` `3280a3c`; toolchain `leanprover/lean4:v4.34.0-rc2`; Lake `5.0.0-src+6a10ac8`; Mathlib `71a80585` |
| Worktrees | `agentB/pv8_wtA` (local branch `agentB/pv8-A`, final `4b5b867`), `agentB/pv8_wtB` (`agentB/pv8-B`, final `26bc2c5`); no upstream, never pushed |
| Packages | Mathlib and the other Lake packages shared read-only by symlink with `agentB/network`; no network fetch |
| Build discipline | one Lean build at a time, each through `scripts/guarded_build.sh` (GNU `time -v`; samples every 2 s; kills the process group below 300 GB `MemAvailable` or 60 GB free disk). Lake 5 has no jobs flag, so parallelism is not capped: peak 56 concurrent `lean` processes (core, about 99 GB summed RSS), 14 for the solutions (40 GB summed) |
| Host during the runs | 128 cores, load 20–24 from other users, 1,054–1,082 GB `MemAvailable`, swap 8/8 GB used, `/ryu` 471 GB free |
| Held fixed | proposition and hypotheses; C sources (byte-identical); Lean proof terms (B calls the same theorems as A, split at the provider statement); native-fact count of each route |
| Cache policy | each worktree's `.lake/build` starts empty ("cold" = first build in that worktree, "warm" = immediate rebuild). M2 and M3 ran after M1 in the same worktrees, so modules shared with M1's closure were already built, identically for both layouts. Fresh per-node verification cost is reported separately as the static import closure (`scripts/import_closure.py`, in-repository modules only, Mathlib excluded; 0–5 imports per closure could not be resolved statically) |
| Not available | Comparator (no binary on the host). The check run is the NODES.md L323–340 local preview: `pp.all` type match plus `#print axioms`, run twice, once exactly as documented and once with the project's build directory pinned first on `LEAN_PATH` (both agreed for every theorem here) |

Evidence: `evidence/builds/*.log` (+ `.summary`), `evidence/metrics/`, `evidence/preview/`, `evidence/axioms/M*`,
`evidence/trust/leaves_world{A,B}.json`, `evidence/closures/fresh_*.json`.

## M1. Single-stage computation: FKS2 Table 4, QRH input

**Proposition** (statement of `FKS2.v9.qrh_absolute_pi`): for every real `x ≥ e³³⁰`,
`|π(x) − Li(x)| ≤ 5·10⁻¹⁶ · x / log x`. **Hypotheses**: `QRHCH2.v5.psi_refined_bound`
(`Eψ(x) ≤ (1/566) log²x · x^(−1/8)`, `x ≥ e³⁰⁰`) and `FKS2.v6.table4_anchor_300`. **Program**:
`Solutions/Table4Evolution.v1/c/qrh_trunc2.c` (2 cells; output `4.9302189588862413·10⁻¹⁶`; sha256 `ef750c59…`).
**Routes**: kernel-only `Table4Evolution.QRHTrunc.Kernel.qrh_pi` (0 native facts) for the challenge theorems;
native-assisted `Table4Evolution.QRHTrunc.qrh_pi` (1 native fact) as a second theorem in the same files.
**Consumer step**: a verbatim copy of `FKS2Pair.absolute_of_normalized` in both layouts.

```
A  [QRHCH2.v5.psi_refined_bound]──┐
   [FKS2.v6.table4_anchor_300]────┴─> [PVMatchT4A.v1.qrh_absolute_pi] <== (S) route + step

B  [QRHCH2.v5.psi_refined_bound]──┐
   [FKS2.v6.table4_anchor_300]────┴─> [PVMatchT4P.v1.qrh_pi] <== (S) route
                                              └─> [PVMatchT4C.v1.qrh_absolute_pi] <== (S) step only
```

| Measure | A | B (provider + consumer) |
|---|---|---|
| Commits | `1f78d30` | `a23bc28` |
| Files / lines added | 10 / 452 (hand-written 6 / 163; generated 4 / 289) | 19 / 730 (hand-written 12 / 289; generated 7 / 441) |
| Nodes / conclusions / import edges / solution projects | +1 / +1 / +2 / +1 | +2 / +2 / +3 / +2 |
| Duplicate statements | joins the `FKS2.v7`/`FKS2.v9` group | joins it, and the provider is a **third** copy of `FKS2Numerics.v5/v7`'s statement |
| Core build after adding the nodes | 13.1 s | 11.0 s |
| `fingerprint` | 12.0 s; only the new file written | 11.7 s; only the new files written |
| Solution build, cold | 637.8 s, 119 modules, peak 26 GB (`Table4Evolution.KernelOnly`) | provider 652.5 s, 119 modules, 26 GB; consumer 4.7 s, 1 module, 3 GB |
| Solution build, warm | 4.7 s | 4.7 s; 2.7 s |
| Fresh per-node closure | 134 modules | provider 134; consumer **5** |
| Local preview, challenge theorem | type identical; `propext, Classical.choice, Quot.sound` | both: type identical; the same three axioms |
| Native route of the same proposition | consumer theorem gains `Table4Evolution.QRHTrunc.certificate._native.native_decide.ax_1_1` | provider gains it; consumer unchanged (three axioms) |
| Consumer's transitive unproved leaves (upstream `graph_leaves`) | 13 premises + itself | the same 13 + itself + **the provider** |
| Receipt grade after the imported ψ profile changes (MT4, in-memory receipts) | consumer BROKEN | provider BROKEN; consumer **green** (it records only the provider's fingerprint) |
| Comparator receipt | none (no binary) | none |

**Reading.** Same work, same peak memory, same unproved premises. B buys two things: the consumer is a
5-module, 3 GB verification unit, and its axioms do not depend on which route the provider uses. A buys one less
node and no third copy of a statement. With the kernel route designated, A's single solution is itself
Comparator-eligible in shape, so the second benefit of B is idle.

## M2. Multi-program chain: Ramanujan A → B′

**Proposition**: for every real `x > e⁹⁴⁰¹`, `(1 + 13.6862/log x)·x²/log⁶x < gap(x)`, with
`gap(x) = (e·x/log x)·π(x/e) − π(x)²` (`RamanujanGap.v1.gap`). **Hypothesis**: `QRHCH2.v5.psi_refined_bound`.
**Programs**: A = `pilots/agentB-calibration/c/calibration_new.c` (certified `Δ = 457/5000`), B′ =
`ramanujan_9401_new.c` (budget at `(0, 120.0914, 9400, 9401)`, bound `66389/625`). **Routes**: kernel-only
(`PVPilot.KernelOnly.certificateA/B`, 0 native facts) for the challenges; native-assisted (`PVPilot.Updated`, one
native fact per program) as second theorems.

```
A  [QRHCH2.v5.psi_refined_bound] ─> [PVMatchRamA.v1.gap_9401] <== (S) A, link M = 120 + Δ, B′, gap step

B  [QRHCH2.v5.psi_refined_bound] ─> [PVMatchRamP.v1.pi_calibrated_9400] <== (S) program A + calibration step
       π(x) ∈ S₅(x) + (119.9086 … 120.0914)·x/log⁶x, x > e⁹⁴⁰⁰         └─> [PVMatchRamC.v1.gap_9401] <== (S) program B′ + gap step
```

The provider's contract is an inequality (`NewChain.Δ ≤ 457/5000`), and the consumer's proof uses only B′'s
constants and the provider's numbers (`PVMatchRam.gap_of_calibrated`), so a better program A would not touch the
consumer. Both proofs compiled at the first attempt.

| Measure | A | B (provider + consumer) |
|---|---|---|
| Commits | `26dc23d` (+ fingerprints in `4b5b867`) | `5ceee2e`, `26bc2c5` |
| Files / lines added | 9 / 457 (hand-written 6 / 144; generated 3 / 313) | 18 / 963 (hand-written 12 / 337; generated 6 / 626) |
| Nodes / import edges | +1 / +1 | +2 / +2 |
| Solution build, cold | 250.5 s, 20 modules (`PVReplay.KernelChain` 185 s), peak 21 GB | provider 231.8 s, 20 modules (`KernelChain` 166 s), 21 GB; consumer 11.0 s, 1 module, 6 GB |
| Solution build, warm | 4.7 s | 4.7 s; 6.8 s |
| Fresh per-node closure | 144 modules | provider 144; consumer **145** |
| Local preview | identical; three axioms | both identical; three axioms |
| Native routes | 2 native facts in the one theorem (`certificateA`, `certificateB`) | provider 1 (`certificateA`); consumer **1** (`certificateB`) |
| Consumer's transitive leaves | 12 premises + itself | the same 12 + itself + the provider |

**Reading.** The split did not isolate anything that matters here. The consumer's fresh closure is as large
as A's (145 vs 144 modules) because the pilot puts both programs' kernel certificates in one module
(`PVReplay.KernelChain`), which the consumer must import to reach program B′. For the same reason, weakening program
A's certified output (mutation MT9) made B's consumer fail to build along with the provider, although the consumer's
proof never mentions program A. With native routes the consumer still carries a native fact, its own program's. B would pay off only with a solution-module split per program,
which layout A can use just as well, and with a kernel-only B′. The node gave the inter-program contract a
name and a fingerprint; it changed neither cost nor trust.

## M3. A shared numerical result: `DudekPlattNumerics.v5` and its two consumer families

**Provider statement** (`DudekPlattNumerics.v5.pi_two_sided_qrh`): for `x > e⁴⁰⁰`,
`S₅(x) + 119·x/log⁶x < π(x) < S₅(x) + 131·x/log⁶x`, from `QRHCH2.v5.psi_refined_bound`; proof
`DDExpansionSolution` (kernel-only: three axioms). **Consumers** (two families): `RamanujanGap.v3.gap_lower_bound`
(+ `RamanujanNumerics.v3.epsilon_budget`) and `DudekPlatt.v5.ramanujan_401` (Ramanujan's inequality for
`x > e⁴⁰¹`; + `DudekPlatt.v3.criterion`; designated `bridged`, the bridge is core Lean).

Layout **B** is the repository as it stands. Layout **A** adds two nodes with the consumers' statements, each
importing the provider's premises instead of the provider, each solution carrying the provider's proof
(`PVMatchShrR.v1`, `PVMatchShrD.v1`). A first attempt at `PVMatchShrD.v1` failed to build because the bridge also
needs `DudekPlatt.v3.criterion`; the corrected node imports it (commit `4b5b867`; failing log kept).

| Measure | A (two consumers carry the proof) | B (repository) |
|---|---|---|
| Files / lines | 18 / 829 (hand-written 12 / 289) for the two consumers | 0 new |
| Nodes / import edges | 2 consumer nodes, 4 edges | provider + 2 consumers, 5 edges (existing) |
| Where the 112-module proof is checked | inside **each** consumer's solution: fresh closures 121 and 116 modules | once, in the provider's solution (112 modules); consumers 11 modules (`RamanujanGap.v3`) and 0 (`DudekPlatt.v5`: a core bridge, compiled by the core build) |
| Builds here (shared closure already warm from M1) | 17.2 s (3 modules) and 11.0 s (1) | provider 13.1 s (1 module), consumer 8.9 s (2) |
| Axioms | three, both consumers | three: provider and consumer |
| Consumer's transitive leaves | premises + itself | the same premises + **the provider** (one leaf shared by both consumers) |
| A comment added to a module of the proof (mutation MT11, `QRHPropagation.v1/Applications.lean`) | 1 module rebuilt (the edited one, shared by both consumers' builds in one workspace; Lean's unchanged output stopped propagation); the module lies in **both** consumers' closures, so fresh per-node verification re-checks it twice | provider 1 module; `RamanujanGap.v3` 0 (not in its closure) |

**Reading.** This is where a provider node earns its place: one statement, two families, one verification of a
large proof instead of one per consumer, and a cheap core bridge for the second consumer that layout A cannot
have (a bridge can only consume node conclusions). The axioms do not decide it (the provider is kernel-only);
sharing does. This is the N2 case of the rule (rule stress test §4).

## What the three pairs say together

1. **Trust.** In every pair, B's consumer rests on exactly A's unproved leaves plus the provider. No unproved
   mathematics is removed or added; the program-verified step becomes a visible, separately designated leaf.
   Comparator would check each compared theorem's axioms in both layouts.
2. **Cost.** A split costs +1 node, +1 import edge, about +9 files and +126 to +193 hand-written lines, and in M1
   a third copy of an existing statement. Build time and peak memory are the same in one workspace; the peak moves
   to the provider's run.
3. **Isolation is a module property, not a node property.** M1's consumer is a 5-module unit; M2's is 145 modules
   because its solution imports a module holding both programs. Node boundaries isolate verification only when
   the solution code is split the same way, and that split is available to layout A too.
4. **Native facts.** A provider keeps native facts out of a consumer whose own step is pure analysis (M1). It
   does not help a consumer that runs its own program (M2: 1 native fact remains). A kernel-only route removes the
   question in either layout.
5. **Sharing is the real reason.** Only M3, a result with two consumer families, shows a benefit that layout A
   cannot match: one verification instead of one per consumer, and a core bridge.
6. **Official staleness is finer in B.** When an imported statement changed (MT4), B's consumer receipt stayed green
   and only the provider's went BROKEN; in A the single receipt went BROKEN. Only the provider then needs
   re-verification, a saving as large as the consumer's own check (here 5 modules, 4.7 s).
7. **Freshness and drift do not depend on the layout.** Mutations MT10/MT10b replayed a stale certificate in
   both layouts, and `solution_drift` was blind from every node's own project in both (mutation tests).
