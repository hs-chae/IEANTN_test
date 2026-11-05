# Round 3: mathematical applications

"Tertiary" is not defined in the IEANTN repository. The PNT+ blueprint, where the IEANTN
classification comes from (`blueprint/src/blueprint.tex`, lines 118–140), defines **primary**
estimates as bounds on `ψ(x)` and `M(x)`, **secondary** as general-purpose bounds such as those on
`π(x)` or the `n`-th prime, derived from primary ones, and **tertiary** as "bespoke applications to
particular problems in analytic number theory or combinatorics that often require secondary
estimates as input". The applications below are tertiary in that sense: short prime intervals,
prime gaps, primes between consecutive powers.

## 1. Primes in `(x, x + x^{7/8}]` for every `x ≥ 1` (under QRH)

**Theorem** (`QRHGlobal.global_interval`, `Solutions/QRHGlobalIntervals.v1`). Assume the node
conclusions `QRHPropagation.v2.theta_frontier`, `Dusart2018.v1.proposition_5_4` and
`PrimeInterval.v1.eTheta_criterion`. Then for every real `x ≥ 1` there is a prime `p` with
`x < p ≤ x + x^{7/8}`.

| range | input | numerical content |
|---|---|---|
| `1 ≤ x < 2` | the prime 2 | `x + x^{7/8} ≥ 2` |
| `2 ≤ x < 93967` | prime ladder `2, 3, 5, 7, 11, 19, 31, 47, 73, 113, …, 75437, 93967` (32 rungs) | `(p' − p)^8 ≤ p^7` at each step, decided by the kernel; primality by `norm_num` |
| `89693 ≤ x ≤ e^{80}` | Dusart: a prime in `(x, x + x/log³x]` for `x ≥ 89693` | `x/log³x ≤ x^{7/8}` ⟸ `e^{log x/8} ≤ log³x`, in two pieces: `e^7 ≤ 11³`, `e^{10} ≤ 56³` |
| `x ≥ e^{80}` | QRH frontier row `(80, 0.23719)`: `Eθ ≤ 0.23720·x^{-1/8}` | `0.2372·(2 + e^{-10}) < 1`, through the `Eθ` criterion |

**Corollaries.** (`prime_between_powers`) For every `k ≥ 8` and `n ≥ 1` there is a prime strictly
between `n^k` and `(n+1)^k`: at `x = n^k`, `x^{7/8} = n^{7k/8} ≤ n^{k−1}` and
`(n+1)^k ≥ n^k + n^{k−1} + 1`. (`prime_gap_le`) After every prime `p` the next prime is at most
`p + p^{7/8}`.

**Why 8.** QRH places the zeros in `Re s ≤ 7/8`, so the explicit formula bounds `θ(x) − x` by about
`x^{7/8}`, and intervals shorter than that are out of reach. Consecutive `k`-th powers are `≈ k·x^{1−1/k}`
apart at `x = n^k`; this exceeds `x^{7/8}` for large `x` exactly when `k ≥ 8`. For `k = 7` the gap
`7x^{6/7}` is eventually smaller than `x^{7/8}`.

**Compared with.** The network's QRH intervals are `0.0345·x^{7/8}` for `x ≥ e^192` and
`0.0264·x^{7/8}` for `x ≥ e^300` (`QRHPropagation.v2`), better constants on their ranges but no
statement for small `x`. Unconditionally, explicit results cover all `n` only for much larger `k`.
The same argument under RH would work with intervals of size about `√x·log²x` and so reach `k ≥ 3`
for large `n`; QRH's `7/8` is what forces `8`.

## 2. Primes in `(x, x + x^{7/8}/16]` for every `x ≥ 1361` (under QRH)

**Theorem** (`QRHGlobal.sixteenth_interval`). With the hypotheses above and
`KadiriLumley.v1.table_2`: for every `x ≥ 1361`, a prime in `(x, x + x^{7/8}/16]`.

| range | input | check |
|---|---|---|
| `1361 ≤ x < 90289` | 230-rung ladder | `(p' − p)^8·16^8 ≤ p^7` |
| `90289 ≤ x ≤ e^{44}` | Dusart | `e^4 ≤ 11³/16`, `e^6 ≤ 32³/16` |
| `e^{44} ≤ x ≤ e^{64}` | Kadiri–Lumley, `x ≥ 4·10^18`, `Δ = 36082898` | `e^8 ≤ (Δ−1)/16` |
| `e^{64} ≤ x ≤ e^{128}` | Kadiri–Lumley, `x ≥ e^60`, `Δ = 1966196911` | `e^{16} ≤ (Δ−1)/16` |
| `x ≥ e^{128}` | QRH frontier row `(128, 0.03013)` | `0.03014·(2 + e^{-16}/16) < 1/16` |

A Kadiri–Lumley row gives a prime in `(y(1 − 1/Δ), y)` for `y ≥ X`; at `y = x + c·x^{7/8}` the
prime exceeds `x` once `x^{1/8} ≤ c(Δ − 1)` (`kl_piece`). The threshold 1361 is sharp for this
constant: there is no prime in `(1327, 1327 + 1327^{7/8}/16] = (1327, 1360.7]`.

## 3. `0.0196·x^{7/8}` from `e^300`, from Agent A's θ coefficient

**Theorem** (`QRHGlobal.intervals_from_agentA_theta`). If `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` on
`x ≥ e^300` (Agent A's `WinnerDensityA.revers_source_theta300`, under its seven named inputs), then
for every `x ≥ e^300` there is a prime in `(x, x + 0.0196·x^{7/8}]`. The network's constant there is
`0.0264`. The improvement is Agent A's θ coefficient, a Lean-evaluated dyadic program with native
facts; the criterion is the same as in §1.

## 4. The Table 4 θ→π transport

Statements, inputs and the ablation are in `ROUND3_NUMERICAL_EVOLUTION.md`. As π bounds on
`[e^330, ∞)` they are not the network's best: `QRHPropagation.v2.pi_density_300` gives
`≈ 1.6·10⁻²⁰` there and Agent A's π theorem `1.153·10⁻²⁰`. What they add is a registered statement
(`FKS2Numerics.v7.qrh_pi`) with a native-fact-free proof.

## 5. The Ramanujan A→B′ chain, kernel only

`PVPilot.KernelOnly.gap_exceeds_leading`: under `QRHCH2.v5.psi_refined_bound`,
`(1 + 13.6862/log x)·x²/log⁶x < gap(x)` for `x > e^9401`, where `gap(x) = π(x)² − e·x/log x·π(x/e)`.
The statement is round 2's; the proof now has no native fact. Ramanujan's inequality itself is
known on much larger ranges in the network (`DudekPlatt.v6.ramanujan_145`, from `e^145`), so this is
a trust result, not a mathematical improvement.

## 6. What could not be composed

A chain θ density (Agent A) → Table 4 transport → Ramanujan budget does not go through: the
transport gives `Eπ ≤ ε` uniformly on `[e^330, ∞)`, while the budget's input needs
`|π − mainTerm − 120·x/log⁶x| ≤ δ·x/log⁶x`, i.e. `ε·log⁵x ≤ δ`, for every `x` in the range. A
constant bound on an infinite ray cannot give that; the power bound used in round 2 does.
