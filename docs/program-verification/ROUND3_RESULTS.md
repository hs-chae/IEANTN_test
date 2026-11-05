# Round 3: deeper verified applications, with almost no change to IEANTN

- **Branch.** `agentB/round3`, pushed to `hs-chae/IEANTN_test` branch `qrh-2pv_B` (hschae, 2026-11-05: "push to a new branch, say qrh-2pv_B"). Base: `qrh-2pv@ce12611` (end of round 2). No PR.
- **Trust labels.** "Standard axioms" means `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`. "Native-assisted" means `native_decide` facts remain; they are counted. Attestations are local research reports, not IEANTN receipts. No official `kind`, `designated` value, statement, fingerprint or receipt changed. Comparator was not run.
- **Change outside solution-local areas.** One new module in the shared package (`PVCore/Decimal.lean`), one pilot module, the gate's endpoint list. All additive. See `ROUND3_MAINTAINER_DIFF.md`.

## Status matrix

| # | Prompt item | Status | Strongest result | Native facts (beyond standard axioms) |
|---|---|---|---|---|
| 1 | QRH-driven **program evolution** beyond literals | **achieved; benefit mostly not QRH-specific** | One transport theorem for **any partition** of `[300, 330]`. QRH input: **2 cells** (was 30) prove the registered `FKS2Numerics.v7.qrh_pi` (`Eπ ≤ 5·10⁻¹⁶`). QRH-free input: **3 cells** prove the registered `FKS2Numerics.v6.old_pi`. 120 quarter cells: `4.7146·10⁻¹⁶` (−0.02%). | 1 per configuration (30-cell route: 4) |
| 2 | Further downstream mathematical application (tertiary) | **achieved** | Under QRH: a prime in `(x, x + x^{7/8}]` for **every `x ≥ 1`**; in `(x, x + x^{7/8}/16]` for every `x ≥ 1361`; a prime between `n^k` and `(n+1)^k` for **every `k ≥ 8`, `n ≥ 1`**; `p_{n+1} − p_n ≤ p_n^{7/8}`. From Agent A's θ coefficient: `0.0196·x^{7/8}` from `e^300` (network: `0.0264`). | **0** |
| 3 | One reusable correctness theorem in ≥ 2 real applications | **achieved** | `Table4Evolution.pi_bound`: 5 configurations, 3 input profiles. `PVCore.decode_of_decodeL`: 3 programs. `QRHGlobal.ladder_sound`: 2 constants. | — |
| 4 | Kernel-only C→C chain | **achieved** | `PVPilot.KernelOnly.gap_exceeds_leading` (the A→B′ Ramanujan chain): standard axioms only. Also the 2-cell Table 4 provider (`Table4Evolution.QRHTrunc.Kernel.qrh_pi`). | **0** |
| 5 | Cross-backend update/replay with a real changed input | **partly achieved** | Agent A's two committed θ coefficients (`0.009904 → 0.009782`) through the same transport: exact rebuild scope measured, old statement rejected, new one proved. A three-program chain was **not** built: blocker below. | 1 per configuration |
| F | Adversarial controls | **13 of 13 rejected** (see `ROUND3_TRUST_AUDIT.md`) | wrong β, swapped profile, non-monotone and wrong-end partitions, omitted tail, wrong anchor, wrong chunking, target too low, empty program, composite rung, missing rung, wrong frontier row, range below 1361 | — |
| F | Independent read-only reviewer | **not run** | Launch was asked for twice (07:37 and 10:15 UTC); no answer, so not launched (standing rule: ask before launching). | — |

**Was QRH-driven program evolution beyond literals achieved?** Yes, in the program: the evolved program has a different number of cells (2 instead of 30), a different geometry (one coarse cell over 29 units of `log x`), a different scale, and is generated and proved from one generic theorem. **But the benefit is mostly not QRH's**: the same truncation applied to the QRH-free input proves its registered target with 3 cells. What QRH changes is small: one cell fewer (its allowance has 6% slack, against 0.01%) and the possibility of refinement, which buys 0.02%. The real gain of the evolved program is **trust**: with 2 cells the kernel can check everything (147 s, 28 GB), so the registered QRH Table 4 statement now has a native-fact-free proof.

## Strongest mathematical theorems (proved in Lean, axioms audited)

| Theorem | Statement | Hypotheses (node conclusions) | Axioms |
|---|---|---|---|
| `QRHGlobal.global_interval` | `∀ x ≥ 1, ∃ p prime, x < p ≤ x + x^{7/8}` | `QRHPropagation.v2.theta_frontier`, `Dusart2018.v1.proposition_5_4`, `PrimeInterval.v1.eTheta_criterion` | standard |
| `QRHGlobal.prime_between_powers` | `∀ k ≥ 8, ∀ n ≥ 1, ∃ p prime, n^k < p < (n+1)^k` | same | standard |
| `QRHGlobal.sixteenth_interval` | `∀ x ≥ 1361, ∃ p prime, x < p ≤ x + x^{7/8}/16` | same + `KadiriLumley.v1.table_2` | standard |
| `PVPilot.KernelOnly.gap_exceeds_leading` | `(1 + 13.6862/log x)·x²/log⁶x < gap(x)` for `x > e^9401` | `QRHCH2.v5.psi_refined_bound` | standard |
| `Table4Evolution.QRHTrunc.Kernel.qrh_pi` | `FKS2Numerics.v7.qrh_pi`: `Eπ ≤ 5·10⁻¹⁶` on `x ≥ e^330` | `QRHCH2.v5.psi_refined_bound`, `FKS2.v6.table4_anchor_300` | standard |
| `Table4Evolution.OldTrunc.old_pi` | `FKS2Numerics.v6.old_pi`: `Eπ ≤ 1.69·10⁻¹²` on `x ≥ e^330` | the four `FKS2.v8.table3_theta_*`, the anchor | + 1 native |
| `Table4Evolution.QRHQuarter.qrh_pi_refined` | `Eπ ≤ 4.7146·10⁻¹⁶` on `x ≥ e^330` | as `qrh_pi` | + 1 native |
| `Table4Evolution.AgentATrunc.pi_from_theta_power` | `Eπ ≤ 1.2078·10⁻²⁰` on `x ≥ e^330` | `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` on `x ≥ e^300`, the anchor | + 1 native |

QRH enters every QRH result as a hypothesis through a node conclusion whose own imports end at `OpenAIQRH.v1.zeta_seven_eighths` (no zeros with `Re s > 7/8`), together with the literature and numerical inputs of that chain (CH2 density transfer, FKS zero density, RH verified to a height). None of those inputs is proved here.

## What is new, and what is not

- **New (tertiary).** The network had QRH short intervals only for large `x`: `0.0345·x^{7/8}` from `e^192` and `0.0264·x^{7/8}` from `e^300` (`QRHPropagation.v2`). It had no statement valid for all `x`, and no consecutive-powers statement. Under RH, primes between consecutive cubes are classical; QRH with exponent `7/8` gives `k ≥ 8`, and the method cannot give `k = 7` (the gap `7x^{6/7}` is eventually below `x^{7/8}`). For large `x` the network's constants are better than `1/16`.
- **New (trust).** The two C→C programs of the A→B′ chain and the evolved Table 4 program now need no native evaluation at all. The bottleneck was decoding decimal literals: `String.splitOn` and `String.toNat?` do not reduce in the kernel in Lean 4.34. `PVCore.Decimal` proves, for every string, that a kernel-reducible decoder gives the same values.
- **Not new.** The Table 4 bounds are not the network's best π bounds at `e^330`: `QRHPropagation.v2.pi_density_300` gives `0.01323·e^{-41.25} ≈ 1.6·10⁻²⁰` there by partial summation, and Agent A's `ScopedWinnerA.pi_00947147` gives `1.153·10⁻²⁰`. The registered QRH Table 4 target (`5·10⁻¹⁶`) comes from the weaker profile `Q(L) = L²/283·e^{-L/8}`. The Agent A profile run (`1.2078·10⁻²⁰`) is a second route, weaker than Agent A's own π bound.

## Four-stage comparison ledger (for discussion, not a ranking)

The stages are nested sets of allowable results, so the best envelope cannot get worse. "Best" values are what this audit found in the network and in Agent A's committed solutions; no completeness claim.

**Quantity 1: `sup_{x ≥ e^330} Eπ(x)`.**

| Stage | Best known | Source | Trust |
|---|---|---|---|
| 0. before QRH | `1.6855·10⁻¹²` (FKS2 Table 4, printed); `1.69·10⁻¹²` reconstructed | `FKS2.v6.table4_330`; `FKS2Numerics.v6.old_pi` | literature; native-assisted program |
| 1. QRH, no source-linked PV | `≈ 1.6·10⁻²⁰` | `QRHPropagation.v2.pi_density_300` (`0.01323·x^{-1/8}`) | Lean proof, no native facts; frontier constants from a numerical certificate outside Lean |
| 2. + PV of non-evolved programs | `≈ 1.6·10⁻²⁰` (inherited); the PV'd 30-cell QRH Table 4 gives only `4.715·10⁻¹⁶` | `FKS2Numerics.v7.qrh_pi` | native-assisted |
| 3. + evolved verified programs | `1.153·10⁻²⁰` | Agent A, `ScopedWinnerA.pi_00947147` (49 native facts, seven named inputs) | native-assisted |

This round's contribution to quantity 1 is trust, not value: the 2-cell program proves the stage-2 registered target with no native fact.

**Quantity 2: the smallest `c` with a prime in `(x, x + c·x^{7/8}]` for all `x ≥ X₀`.**

| Stage | `X₀ = 1` | `X₀ = 1361` | `X₀ = e^192` | `X₀ = e^300` |
|---|---|---|---|---|
| 0. before QRH | none | none | none | none |
| 1. QRH, no source-linked PV | **`1` (this round)** | **`1/16` (this round)** | `0.0345` | `0.0264` |
| 3. + evolved programs | — | — | — | **`0.0196`** from Agent A's θ coefficient through the same criterion (`QRHGlobal.intervals_from_agentA_theta`, this round; Agent A's seven inputs) |

Stage 2 adds nothing to quantity 2: no PV'd non-evolved program bounds `Eθ` with an `x^{-1/8}` decay.

## Not done, with exact blockers

- **A three-program chain (θ density → Table 4 transport → Ramanujan budget).** The transport's output is a constant on a ray, `Eπ ≤ ε` for all `x ≥ e^330`. The Ramanujan budget needs `|π − mainTerm − 120·x/log⁶x| ≤ δ·x/log⁶x` for all `x` in the range, i.e. `ε·log⁵x ≤ δ`, which fails as `x → ∞`. A constant π bound on an infinite ray cannot feed it; a decaying (power) bound can, and that is the round-2 two-backend chain.
- **The 30-cell Table 4 program in the kernel.** Not run: it needs about 8 times the exponential certificates of the 2-cell program, whose kernel check already peaks at 28 GB.
- **Smaller constants than `1/16`.** About `0.042` is reachable with the BKLNW Table 8 ψ bounds and a ψ→θ correction; not implemented.
- **Agent A's newer package.** `Solutions/PVEvolutionA.v1` was staged in Agent A's worktree when this round started and was committed there at `00128be` (07:54 UTC, branch `poc/maximal-pv-evolution-a`, not pushed). Read, not used: this round pins Agent A's pushed `e0c1ceb`.
- **Independent reviewer.** Not launched without authorization.

## Corrections to earlier rounds

- Round 2 said the `input_file` retrofit makes stale builds impossible. It does so for builds of the provider's own library, which is what the controls built. A module reached through another library's import was traced without its library's `needs` in this round's measurement (`Table4Evolution`'s umbrella module); `FKS2Numerics.v5`'s default target was re-tested in a scratch copy and does rebuild. The new project's default targets are therefore its configuration libraries.
