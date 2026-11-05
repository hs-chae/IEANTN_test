# Round 3, extended threefold: results

- **Branch.** `agentB/round3`, pushed to `hs-chae/IEANTN_test` branch `qrh-2pv_B` (hschae, 2026-11-05: "extend and push 3 times more, in all directions"). Base: `qrh-2pv_B@1980f10` (end of round 3). No PR.
- **Trust labels.** As in round 3: "standard axioms" means `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`; native facts are counted. Attestations are local research reports, not IEANTN receipts. No official `kind`, `designated` value, statement, fingerprint or receipt changed. Comparator was not run.
- **Change outside solution-local areas.** Additive, except one changed line (the pilot's `defaultTargets`): `pilots/pv-twobackend` (one new library, one new `require`, two manifest entries), `pilots/pv-replay` (one new module), the gate's endpoint list (+22). See `ROUND3_MAINTAINER_DIFF.md`, section "Extension".

## Status matrix: round 3 against the extension

| Direction | Round 3 | Extension | Factor |
|---|---|---|---|
| Theorems in the tertiary project's axiom test (standard axioms, 0 native) | 7 | **29** (+22) | 4.1× |
| Smallest interval constant valid from a fixed small `X₀` | `1/16` from `1361` | **`1/24` from `1339`**, both thresholds sharp (`1/16` from `1328`) | `c` 1.5× smaller |
| Constant from `e^300` | `0.0196` (Agent A's θ) | **`0.019`** (Agent A's π, through a new π-route criterion) | |
| Prime **counts** in `(x, x + x^{7/8}]` | none | **97.4% – 102.6%** of `x^{7/8}/log x` for `x ≥ e^300`; 98.1% – 101.9% from Agent A's π bound | new |
| Mills-type constants | none | **every real `k ≥ 8`, every starting prime**; explicit `A = 2.00097489763307733758…` for `k = 8` | new |
| Program results with **0 native facts** | 2 | **12** (and the chains' C stages) | 6× |
| Program evolution of the Table 4 transport | 30 → 2 cells, constant output | **0 cells** (closed form) for power-law inputs; **decaying output** `Eπ ≤ K'·x^{-1/8}` | |
| Chains of verified programs | 2 programs (A→B′) | **3 programs, 2 backends** (Agent A's θ → π transport → Ramanujan budget), replayed with Agent A's other θ input | |
| Gate endpoints (local) | 11 | **33** (+22); the 22 new ones all passed at `2a3ff26` | 3× |
| Negative controls | 13 | **43** (+30), all rejected | 3.3× |
| Independent reviewer | not run | not run (launch asked three times, no answer) | |

## 1. Tertiary results (all under QRH; standard axioms, no native fact)

`Solutions/QRHGlobalIntervals.v1`, new modules `TwentyFourth`, `Counting`, `Counts`, `Mills`, `MillsExplicit`, `Corollaries`.

| Theorem | Statement | Extra inputs |
|---|---|---|
| `twentyfourth_interval` | a prime in `(x, x + x^{7/8}/24]` for every `x ≥ 1339` | BKLNW Table 8 and Corollary 5.1, Kadiri–Lumley, Dusart |
| `not_twentyfourth_1338` | no prime in `(1338, 1338 + 1338^{7/8}/24]`: `1339` is the sharp integer threshold | none |
| `sixteenth_interval_sharp`, `not_sixteenth_1327` | `1/16` from `1328`, and `1327` fails | as round 3 |
| `count_300` | `0.9737·x^{7/8} ≤ N(x)·log(x + x^{7/8})` and `N(x)·log x ≤ 1.0263·x^{7/8}`, `x ≥ e^300`, where `N(x) = π(x + x^{7/8}) − π(x)` | frontier row `(300, 0.01310)` |
| `count_80`, `count_1000` | the same with `[0.5255, 1.4745]` from `e^80` and `[0.9796, 1.0204]` from `e^1000` | frontier rows 80, 1000 |
| `count_from_agentA_pi` | `[0.98105, 1.01895]` from `e^300` | Agent A's `Eπ ≤ 0.00947147·x^{-1/8}` (hypothesis) |
| `intervals_from_agentA_pi` | a prime in `(x, x + 0.019·x^{7/8}]`, `x ≥ e^300` | the same |
| `mills_qrh` | for every real `k ≥ 8` and prime `p₀` there is `A ∈ [p₀, p₀+1)` with `⌊A^{k^n}⌋` prime for all `n` | none beyond round 3 |
| `mills_explicit` | `⌊A^{8^n}⌋` prime for all `n`, `⌊A⌋ = 2`, `⌊A^8⌋ = 257`, `⌊A^{64}⌋ = 19031147999601100901`, `2.000974897633077337586 ≤ A < 2.000974897633077337588` | none (Lucas certificates, kernel-computed) |
| `oppermann_powers` | primes in `(n^k − n^{k−1}, n^k)` and `(n^k, n^k + n^{k−1})`, `k ≥ 8`, `n ≥ 2` | none |
| `andrica_eighth`, `andrica_eighth_24` | consecutive primes: `p'^{1/8} − p^{1/8} ≤ 1/8`; `≤ 1/192` once `p ≥ 1339` | as the intervals |

Reusable statements behind them: `count_of_theta_power` and `count_of_pi_power` (two-sided counts from any `Eθ` or `Eπ` power bound), `interval_of_pi_power` (a π-route prime-interval criterion, not in `PrimeInterval.v1`), `mills_of_step` (Mills' construction for any real exponent `k > 1`), `prime_of_lucas` (Lucas certificates with kernel-computed modular powers).

**How to read them.** The constant `1/24` is the floor of what the network's tables reach: the QRH frontier row `(160, 0.02069)` needs `c > 0.0414`, and between `e^{148}` and `e^{160}` only BKLNW's ψ table reaches (`Eθ ≤ 2.4530·10⁻¹²` on `[e^{100}, e^{25000}]` after the ψ→θ correction). The counts say that from `e^300` on, every interval `(x, x + x^{7/8}]` holds the expected number of primes up to 2.6%. Mills' theorem itself is classical and unconditional for `k = 3` (from Ingham's intervals, with a large, inexplicit start); what QRH adds is that every `k ≥ 8` works **from every starting prime**, so the constant is explicit: the least choices give `2, 257, 19031147999601100901 = 257^8 + 100, …` and twenty decimals of `A`.

## 2. Program evolution: the transport for a power-law input

`Solutions/Table4Evolution.v1/Table4Evolution/PowerTransport.lean`. For `Eθ ≤ K·t^{-1/8}` on `t ≥ e^300` the cell sum of round 3 is not needed: `t^{-1/8}/log² t` has the majorant antiderivative `κ·t^{7/8}/log² t`, `κ = 600/521`, on `t ≥ e^300`. With the anchor `Eπ(e^300) ≤ 1.6997·10⁻¹²`:

`Eπ(x) ≤ (K·(1 + κ/330) + (330/300)·e^{45/4}·(1.6997·10⁻¹² + K·e^{-75/2}))·x^{-1/8}` for every `x ≥ e^330` (`power_ray`).

| Configuration | Input | Program | Output | `Eπ(e^330) ≤` | Native |
|---|---|---|---|---|---|
| round 1 | QRH `Q(L)` | 30 cells | `Eπ ≤ 4.715·10⁻¹⁶` (constant on the ray) | `4.7·10⁻¹⁶` | 4 |
| round 3 | QRH `Q(L)` | 2 cells | `Eπ ≤ 4.930·10⁻¹⁶` (constant) | `4.9·10⁻¹⁶` | 0 (kernel route) |
| round 3 | Agent A `K = 0.009782` | 4 cells | `Eπ ≤ 1.2078·10⁻²⁰` (constant) | `1.21·10⁻²⁰` | 1 → **0** |
| **extension** | network frontier row `(300, 0.01310)` | **0 cells**: 2 inputs, 1 constant | **`Eπ ≤ 0.013156·x^{-1/8}`** (decaying) | `1.601·10⁻²⁰` | **0** |
| **extension** | Agent A `K = 0.009782` | 0 cells | **`Eπ ≤ 0.0098163·x^{-1/8}`** | `1.195·10⁻²⁰` | **0** |

Against the network: `QRHPropagation.v2.pi_density_300` gives `0.01323·x^{-1/8}` from `e^300`; the network-input program gives `0.013156` from `e^330` (0.56% smaller on the subray). Against Agent A: its own π theorem gives `0.00947147` (`1.153·10⁻²⁰` at `e^330`), so the Agent A configuration is a second route, weaker by 3.6%; its point is that its output decays.

**What evolved.** Round 3 changed the number of cells; here the program's **output type** changes, from a constant on a ray to the coefficient of a decaying profile, and the cells disappear because the input profile has a closed-form integral. That decaying output is what the Ramanujan budget can consume (section 4).

## 3. Kernel-only programs: 2 → 12

| Program result | Statement | Kernel time, peak memory |
|---|---|---|
| `Table4Evolution.QRHTrunc.Kernel.qrh_pi` (round 3) | registered `FKS2Numerics.v7.qrh_pi` | 147 s, 28 GB |
| `PVPilot.KernelOnly.gap_exceeds_leading` (round 3) | the A→B′ Ramanujan chain | +16 s, 8 GB |
| `Table4Evolution.OldTrunc.Kernel.old_pi` | registered `FKS2Numerics.v6.old_pi` (3 cells) | 156 s, 37 GB (module group peak) |
| `Table4Evolution.AgentATrunc.Kernel.pi_from_theta_power` | `Eπ ≤ 1.2078·10⁻²⁰` (4 cells) | 214 s |
| `Table4Evolution.AgentASource.Kernel.pi_from_theta_power_source` | `Eπ ≤ 1.2228·10⁻²⁰` (4 cells) | 209 s |
| `PVRamanujan.KernelOnly.V1.epsilon_budget` | registered `RamanujanNumerics.v1.epsilon_budget` | 264 s and 19 GB for the four |
| `PVRamanujan.KernelOnly.V2.epsilon_budget` | registered `RamanujanNumerics.v2.epsilon_budget` | (same module) |
| `PVRamanujan.KernelOnly.OldGrouped.epsilon_budget` | `RamanujanNumerics.v1.epsilon_budget`, one-entry array | (same module) |
| `PVRamanujan.KernelOnly.UpdatedGrouped.epsilon_budget_fixed_target` | grouped updated budget at 3914.7 | (same module) |
| `Table4Evolution.PowerNetwork.pi_power` | `Eπ ≤ 0.013156·x^{-1/8}` | 49 s, 14 GB |
| `Table4Evolution.PowerAgentA.pi_power` | `Eπ ≤ 0.0098163·x^{-1/8}` | 45 s |
| `Table4Evolution.PowerAgentASource.pi_power` | `Eπ ≤ 0.0099388·x^{-1/8}` (changed input) | 51 s |

Every one decodes the C literals with `PVCore.decode_of_decodeL` and checks every certificate with `decide +kernel`. Three of them prove registered network statements (`FKS2Numerics.v6.old_pi`, `RamanujanNumerics.v1/v2.epsilon_budget`) with no native fact.

## 4. A chain of three programs

`pilots/pv-twobackend/ThreeChain`. `PVThreeChain.gap_exceeds_leading`: on `x > e^331`,
`(1 + 7.84/log x)·x²/log⁶x < (e x/log x)·π(x/e) − π(x)²`.

1. Agent A's θ program (`WinnerDensityA.revers_source_theta300`, unchanged; exact dyadic evaluation): `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` from `e^300`.
2. The power-form transport (`power_agentA.c`, kernel only): `Eπ ≤ 0.0098163·x^{-1/8}` from `e^330`.
3. The Ramanujan budget regenerated at `(m, M, A, Y) = (0, 122.5, 330, 331)` (`budget_331.c`, kernel only, certified output `112.1461`, stated `112.15`), shifted exactly to `m = 119.99`.

The data link `pi_input_330` reads stage 2's decaying bound as the budget's five-term π input. The chain has 17 native facts, all in Agent A's stage; stages 2 and 3 add none. In round 3 this chain was blocked because the transport only gave a constant on a ray (`ε·log⁵x` is unbounded); the decaying output removes the blocker. It is a composition demonstration: Ramanujan's inequality is already a network conclusion from `e^145`.

### Changed-input replay through the chain

Agent A has two committed θ evaluations on `x ≥ e^300`: `0.009904 + 10⁻¹²` (`source_theta300`, original
inputs) and `0.009782 + 10⁻¹²` (`revers_source_theta300`, Revers inputs). The chain above uses the second;
`PVThreeChain.gap_exceeds_leading_source` replays it with the first. What changed: stage 1's theorem
and inputs, and stage 2's data, which `scripts/generate_power.py` wrote from the coefficient alone
(`power_agentA_source.c`, output `0.0099388` instead of `0.0098163`). What did not: stage 2's theorem
(`power_pi_bound`), stage 3's program and certificate, the consumer, and the conclusion. The link
`pi_input_330_of` reads any transported coefficient up to `1/100`, so the budget program is not
regenerated. Rebuilt for the replay: in Table 4, the generated data module (1.3 s) and
`PowerAgentASource` (51 s); in the pilot, `Link330` and `ChainSource` (about 6 s each) and Agent A's
original-input closure, compiled here for the first time (`WinnerDensityA.SharpCertificate`, 298 s,
native). `StageB331` and the budget certificate were replayed, not rebuilt. The replayed chain has 17
native facts, all in Agent A's stage (`WinnerOriginalScalars`, `WinnerOriginalDensity`,
`WinnerDensityA.SharpCertificate`).

## 5. One theorem, many uses

| Reusable theorem | Uses |
|---|---|
| `Table4Evolution.pi_bound` | 6 uses in round 3 (5 configurations, 1 kernel route) → 9 (3 more kernel routes) |
| `Table4Evolution.power_pi_bound` | 3 configurations (network, Agent A's two inputs) |
| `PVCore.decode_of_decodeL` | 3 programs (round 3) → 13 |
| `QRHGlobal.interval_of_theta_power` | 3 constants (round 3) → 4 (adds `1/24`) |
| `QRHGlobal.ladder_sound` | 2 ladders → 4 (adds `1/24` and the sharp `1/16` rung) |
| `QRHGlobal.count_of_theta_power` / `count_of_pi_power` | 3 / 2 instances |
| `QRHGlobal.mills_of_step` | `mills_qrh` (all real `k ≥ 8`), `mills_eight`, `mills_explicit` |
| `QRHGlobal.prime_of_lucas` | 2 certificates (`854184623791`, `19031147999601100901`) |
| `PVRamanujan.budgetCheck_of_decode` | 1 (round 3) → 6 (four replays and the chain's budget) |

## 6. Four-stage ledger, updated

Stages are nested; "best" is what this audit found, no completeness claim.

| Quantity | 0. before QRH | 1. QRH, no source-linked PV | 2. + PV of non-evolved programs | 3. + evolved verified programs |
|---|---|---|---|---|
| `sup_{x ≥ e^330} Eπ(x)` | `1.69·10⁻¹²` | `1.610·10⁻²⁰` (`pi_density_300`) | inherited | `1.153·10⁻²⁰` (Agent A); **`1.601·10⁻²⁰` from the network's own θ row through a 0-native evolved program** |
| interval constant `c` from `X₀` | none | **`1/24` from `1339`**; `0.0264` from `e^300` | inherited | **`0.019` from `e^300`** (Agent A's π program) |
| fraction of the expected primes in `(x, x + x^{7/8}]`, `x ≥ e^300` | none | **`[0.9737, 1.0263]`** | inherited | **`[0.98105, 1.01895]`** (Agent A's π program) |
| Mills exponent from every prime | none (`k = 3` only from a large start) | **every real `k ≥ 8`** | inherited | inherited |

## 7. Not done, with exact blockers

- **`c` below `1/24`.** Blocked by the network's θ frontier: the row `(160, 0.02069)` needs `c > 0.0414`, and the next row is at `192`. A frontier row between `e^{160}` and `e^{183}` (where BKLNW stops reaching) would lower it.
- **Counts below `e^80`.** Only existence is proved there (ladders, Dusart, Kadiri–Lumley give one prime, not a count).
- **More digits of the Mills constant.** The next term has 155 digits; a primality certificate at that size needs an elliptic-curve (ECPP) checker, not a Lucas certificate.
- **The 30-cell kernel run.** Not attempted; for power-law inputs the closed form makes the cells unnecessary.
- **Independent reviewer.** Not launched without your yes.
- **Node registration** of the tertiary theorems: proposal only (owner's call).

## 8. Finding: Lake traces a module differently by entry point

The same `Table4Evolution` module gets one trace from a root `lake build` and another when a build
reaches it through an import (another configuration library, or the pilot that requires the package),
so each recompiles it in the package's `.lake`. During the controls this made a concurrent gate
extraction find an `.olean` missing ("blocked"). Results do not depend on it, since every
recompilation compiles the same sources. The final gate run was made with nothing else building, after a
full root build (`ROUND3X_TRUST_AUDIT.md` §5). Separately, the umbrella module that the tests and the gate
import was not a default target, so a plain `lake build` left it stale; it is one now (§2 of the audit).

## Corrections

- Round 3 said `1361` cannot be lowered for the constant `1/16`. Wrong: `1328` works and is sharp (`sixteenth_interval_sharp`, `not_sixteenth_1327`).
- A progress message said the three-program chain has 19 native facts. It has 17.
- A round-3 progress message gave Agent A's π bound at `e^330` as `1.157·10⁻²⁰`. It is `0.00947147·e^{-41.25} = 1.153·10⁻²⁰`, as the round-3 documents state.
- Round 3's replay recipe for Table 4 (`lake build && lake env lean tests/Axioms.lean`) fails from a fresh checkout: the umbrella module the test imports was not a default target. It is now, and the round-3 recipe carries a note.
