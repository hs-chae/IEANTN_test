# Stress test of the promotion rule

The first study proposed: give a numerical result its own node if (R1) two or more consumer *families* need it,
(R2) its evidence is weaker than its consumer's Lean step, (R3) it is an externally meaningful statement of
record, or (R4) keeping it inside would exceed the time or memory budget. This file tries to break that rule on
the repository, then replaces it with a shorter one.

Snapshots: PoC `qrh-2pv_B` `3280a3c` (29 providers: the 27 `computation` nodes plus the two `pipeline` nodes whose
names mark them as numerical providers, `DudekPlattNumerics.v5/v6`); Agent A's unpushed `091288d` gives the same
table (`evidence/rules/rules_agentA_091288d.txt`). Script `scripts/rules_audit.py`; output
`evidence/rules/rules_3280a3c_checked.{txt,json}`.

## 1. How the criteria were evaluated this time

| Criterion | First study (`5b59409`) | This study |
|---|---|---|
| R1 | distinct consumer node families, direct imports, computation nodes only | direct **and** transitive families, all 29 providers |
| R2 | provider designates a leaf kind, and some consumer is `lean-comparator` or merely *has* a `Solution.lean` | provider evidence weaker than Comparator **and** some direct consumer's step checked native-free: a receipt, a local attestation with 0 native facts, or `#print axioms` run here (17 consumer theorems, `evidence/axioms/consumer_*.txt`) |
| R3 | provider designates `literature` or `numerical` | kept as the old proxy, and compared with **R0**: no proof of the provider exists in the repository (cited, asserted or `none-yet` without a solution) |
| R4 | asserted from the Table 4 kernel route's 28 GB | measured on the matched pairs |

## 2. Results

| Criterion | Fires on (of 29) | What it actually detects | Verdict |
|---|---|---|---|
| R0 (new) no in-repository proof of any conclusion | 18 | the evidence is a citation, an assertion or nothing; the only way to state the fact in the network is a node (SOLUTIONS.md L57–61) | **necessary and sufficient** for these 18; no design choice is involved |
| R3 old proxy | 17: 16 inside R0, plus the mixed `FKS2Numerics.v2` (four cited conclusions, one source-verified) | the same thing as R0, minus `Wedeniwski.v1` (asserted) and `DudekPlattNumerics.v6` (`none-yet`, no solution) | **nearly circular**: it restates "the evidence is a citation" and fires on no purely in-repository provider, so it explains none of the 10 program-verified ones |
| R1 direct families | 2: `PlattTrudgian.v1` (6 families), `DudekPlattNumerics.v5` (2: `DudekPlatt`, `RamanujanGap`) | genuine sharing of one statement by unrelated consumers | holds; the first study missed `DudekPlattNumerics.v5` because it filtered on `kind: computation` |
| R1 transitive families | 7 of the 27 computation nodes | any root input reaches many families eventually (`Wedeniwski.v1` 8, `LowZeroes.v1` 12, `ZetaLogDerivValues.v1` 12) | too permissive: every cited root qualifies |
| R2 metadata proxy | 18 | — | one false positive: `DudekPlattNumerics.v5`, whose proof is kernel-only (three axioms, checked) |
| R2 from evidence | 17 | for **8 of the 9** program-verified providers that have consumers (FKS2Numerics.v3–v7, RamanujanNumerics.v1–v3), every consumer step checked is native-free while the provider's designated proof uses native facts; the ninth, `DudekPlattNumerics.v5`, is kernel-only and falls under R1. The other 9 hits are cited providers with a native-free consumer (`FKS2Numerics.v1` → `FKS2.v1`, `PlattTrudgian.v1` → `CH2.v1`, ...) | **the criterion that explains the native in-repository providers**; but see counterexample E |
| R4 budget | 0 measured | — | see counterexample F: a split moves the memory peak to another run, it does not lower it |

Two in-repository providers have no consumer at all: `DudekPlattNumerics.v4` (a Comparator-checked formalization of
`DudekPlattNumerics.v3`'s cited statement, from `MT.v2.corollary_1`; `DudekPlatt.v4` still imports v3) and
`FKS2Numerics.v2` (v1's numerics with one value corrected by source verification, `6.3376e-7` → `6.339e-7`). Both
are **versions** of providers that exist under R0: the versioning rule (new imports or a corrected statement → new
version) explains them, not a promotion rule.

## 3. Counterexamples and near misses

**A. R1 by node count (false positive).** `ZetaLogDerivValues.v1` has 7 consumer nodes and 36 import edges, all
`CH2.v4`–`v10`: one family. Counting nodes or edges would call it shared. The family rule says no, and the node is
needed for another reason (R0: Chirre–Helfgott's computed values, cited).

**B. R1 by kind filter (false negative).** `DudekPlattNumerics.v5` (`kind: pipeline`, designated `none-yet`) states
the QRH expansion `S₅(x) + 119x/log⁶x < π(x) < S₅(x) + 131x/log⁶x` for `x > e⁴⁰⁰`. Its solution is a large Lean
proof (112 modules in the static closure, kernel-checked), and it is imported by two families: `DudekPlatt.v5`
(Ramanujan's inequality from `e⁴⁰¹`, a core bridge) and `RamanujanGap.v2/v3`. It is the repository's only
program-verified result with two consumer families, and the first study's count did not see it. Matched pair M3
measures it.

**C. R1 transitive (over-inclusion).** `Wedeniwski.v1` (ZetaGrid, `asserted`) has one direct consumer
(`Kadiri2005.v1`) and reaches 8 families through it. Counting transitively makes every root citation "shared";
the count is then a property of the graph's depth, not of reuse.

**D. R1 at node level only (missed potential reuse).** Agent A's `ScopedWinnerA.pi_00947147`
(`HasPowerLogBound Eπ 0.00947147 0 (7/8) (exp 300)`, solution only) is consumed in solutions by two families:
the tertiary intervals and counts (`QRHGlobal.intervals_from_agentA_pi`, `count_from_agentA_pi`) and the Ramanujan
chain (`PVThreeChain` via `Link330`). R1 at node level rejects it, and it cannot be promoted anyway: four of its
seven hypotheses are solution-level (casebook C3). Waiting for two node-level consumers costs little: measured
promotion later is what M1's layout B costs over layout A: +1 node, +1 import edge, +9 files, +126 hand-written lines (`evidence/metrics/M1_*_metrics.json`).

**E. R2 depends on the current proof route (time instability).** `FKS2Numerics.v7.qrh_pi` satisfies R2 today
(designated 30-cell route, 8 native facts; consumer `FKS2.v9` native-free). The same statement now also has a
kernel-only route (`Table4Evolution.QRHTrunc.Kernel.qrh_pi`, 0 native facts, attested at `cb81845`). Designate
that route and R2 no longer holds; the node stays only because node identity survives refactoring
(ARCHITECTURE L459–463). The same is true of `RamanujanNumerics.v1/v2` (kernel replays with 0 native facts).
R2 therefore justifies a split at the moment of creation and never asks for a merge. That asymmetry is
acceptable, but R2 is not a statement about the mathematics.

**F. R4 on memory (false positive).** M1 measured the Table 4 kernel route inside layout A's single solution
(peak 26 GB, `Table4Evolution.KernelOnly`) and inside layout B's provider solution (peak 26 GB, same module).
Lean compiles module by module, so a run's peak is the largest module, not the sum: splitting moved the 26 GB
check from the consumer's run to the provider's run and lowered nothing. On time, A took 637.8 s cold and B
657.2 s (provider 652.5 s + consumer 4.7 s), both far under the one-hour budget (ARCHITECTURE L331–335).
M2 behaves the same way (A 250.5 s, B 231.8 + 11.0 s, 21 GB peak in both). Only M3 shows a real saving, and it
comes from sharing (the proof is checked once instead of once per consumer), which is R1/N2, not R4.

**G. R2 predicted a benefit nobody took (false negative of practice).** Agent A's new `PrimeInterval.v2`
(`091288d`, unpushed: prime in `(x, x + x^{4/5}]` for `x ≥ e³³⁰`) keeps two numerical programs inside its own
solution; its note says the proof "consumes exactly three finite numerical facts", that "these native axioms do not
qualify under the present official Comparator policy", and that "a kernel-checked numerical replacement is
required". This is layout A with native facts: the analytic step cannot be verified on its own. R2 says a
provider for the program outputs would let the consumer's step be Comparator-checked now. The alternative R2
ignores, a kernel-only route (as M1 and M2 use), removes the reason without a node.

**H. Hidden R5, ownership and lifecycle.** Ownership is recorded per node (`authors`,
`responsible_maintainers`), and per justification only in prose. Across the 29 providers it does not
discriminate: 15 are by Terence Tao (maintainer Tao), 10 by OpenAI (Codex) with maintainer hschae, 4 others; and
every PoC provider shares author and maintainer with its consumer (`FKS2Numerics.v5/v7` and `FKS2.v7/v9`,
`RamanujanNumerics.v1–v3` and `RamanujanGap.v1–v3`). The one PoC split made for a new lifecycle,
`FKS2Numerics.v7` (a new proof route for v5's unchanged statement, same author and maintainer as v5, commit
`154b1d0`), is the duplicate the rule should forbid. Two owners of two routes need two justifications of one
conclusion, which the schema already supports (`justifications` is a list), not two statements. Ownership alone
fails as a criterion.

## 4. The rule, shortened

A numerical result gets its own node if and only if one of these holds **today**:

- **N1. Cited evidence.** Its evidence is not a proof in this repository (a paper, a table, a website). A node
  is the only way to state it. (This is what the old R3 detected.)
- **N2. Two consumer families.** Conclusions of at least two different node families import this exact
  statement (counted directly, by family, at node level).
- **N3. Comparator eligibility.** A consumer whose own step is Lean-checked with the three standard axioms would
  otherwise have to carry the result's native facts.

Nothing else creates a node: not a new proof route, fewer native facts, a source edit, a new owner, a stage of a
program, or a build budget (split modules instead; M1 shows a node split does not lower the memory peak).
Versions of an existing provider follow the versioning rule (imports or statement changed), not this one.

**Falsifiable.** The rule is wrong if a node that fails N1–N3 turns out to be needed, or if a result meeting N2
is better kept inside one solution. Checked against the repository: it accepts the 29 existing providers except
the two versions noted in §2 (which the versioning rule covers) and it **rejects** these plausible candidates:
the hypothetical `PowerTransport.v1` (kernel-only, no consumer), the M1 and M2 layout-B providers
(`PVMatchT4P.v1`, `PVMatchRamP.v1`: kernel-only, one consumer), the Table 4 program variants as nodes (routes of
one statement), Agent A's winner (no node-level consumer; hypotheses not stateable yet), and
`FKS2Numerics.v7` if it were proposed today (same statement as v5). N3 is the weakest leg: it lapses when a
kernel-only route appears (E), so it should be read as "keep the consumer eligible now", not as a reason the
node must exist forever.

**Not CI.** N1 and N2 are mechanical (`rules_audit.py` computes them). N3 needs the consumer's axioms, which only a
build or a receipt gives; it belongs in review, not in a check.
