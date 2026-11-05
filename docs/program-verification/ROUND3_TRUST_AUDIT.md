# Round 3: trust audit and replay

Every claim below was checked by building the code and printing axioms (`tests/Axioms*.lean` in
each project). Times are wall-clock on the shared 128-core machine with dependency caches warm.

## 1. Final theorems, axioms, native facts

| Theorem | Project | Native facts | Owners |
|---|---|---|---|
| `QRHGlobal.global_interval` | `Solutions/QRHGlobalIntervals.v1` | **0** | — |
| `QRHGlobal.prime_between_powers`, `QRHGlobal.prime_gap_le` | same | **0** | — |
| `QRHGlobal.sixteenth_interval`, `QRHGlobal.prime_gap_sixteenth` | same | **0** | — |
| `QRHGlobal.intervals_from_agentA_theta` | same | **0** (Agent A's θ bound is a hypothesis) | — |
| `PVPilot.KernelOnly.gap_exceeds_leading` | `pilots/pv-replay` | **0** | — |
| `Table4Evolution.QRHTrunc.Kernel.qrh_pi` | `Solutions/Table4Evolution.v1` | **0** | — |
| `Table4Evolution.QRHTrunc.qrh_pi` | same | 1 | `QRHTrunc.certificate` |
| `Table4Evolution.OldTrunc.old_pi` | same | 1 | `OldTrunc.certificate` |
| `Table4Evolution.QRHQuarter.qrh_pi_refined` | same | 1 | `QRHQuarter.certificate` |
| `Table4Evolution.AgentATrunc.pi_from_theta_power` | same | 1 | `AgentATrunc.certificate` |
| `Table4Evolution.AgentASource.pi_from_theta_power_source` | same | 1 | `AgentASource.certificate` |
| generic: `whole_ray`, `cellsOK_sound`, `constOK_sound`, `pi_bound`, `program_bound`, `chunked_bound` | same | 0 | — |
| generic: `PVCore.decimal_of_decimalL`, `PVCore.decode_of_decodeL` | `Solutions/ProgramVerification` | 0 | — |

"0" means `#print axioms` lists exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`
anywhere. Each native fact is a `native_decide` over one finite Boolean check: source tokens, the
binary64 loop and suffix rounding, the cell and constant certificates.

## 2. Literal decoding: from two native facts to none

`FKS2Scalar.decimal`, the literal semantics in `PVCore.Exec`, uses `String.splitOn` (well-founded
recursion over UTF-8 byte positions) and `String.toNat?` (a slice iterator). In Lean 4.34.0-rc2
`String` is `ByteArray`-backed and neither reduces in the kernel: `decide +kernel` on
`"0.5".splitOn "." = ["0", "5"]` gets stuck, with or without `unseal`.

| Attempt | Result |
|---|---|
| `decide +kernel` on `decimal s` | stuck |
| unfolding `splitOnAux`'s equation by `simp`, then `decide` | works: 55-character literal in 28 s, 5.6 GB; a 137-character literal ran 4.5 min, 27.5 GB and failed |
| **fuel copy `splitOnFuel` with a soundness theorem, digits through the library's `forIn`/`foldl` → `toList` lemmas** | **works for every string**; the A→B′ decodings take 16 s, 7.9 GB together |

`PVCore.splitOnFuel_sound` unfolds `String.splitOnAux` once per step; `PVCore.toNat?_eq` is
`String.Slice.forIn_eq_forIn_toList`, `foldl_eq_foldl_toList` and `copy_toSlice`. The literal
semantics is unchanged: `decode` still means `decimal` and `round64`.

## 3. Local gate (`scripts/native_assisted/native_assisted_check.py`)

Eleven new endpoints, run at `a45338c` on a clean tree (log
`agentB/evidence/pv5/gate_round3_a45338c.log`, about 10 s to 70 s each, peak 8.9 GB). The kernel-route
Table 4 endpoint was re-run at `cb81845`, after its final theorem was made to use the named source
certificate (`certificate_k`); before that the gate found no execution witness in its closure and
classified it "not-program-verified".

| Endpoint | Status | Method | Native |
|---|---|---|---|
| `@evo.Table4Evolution.QRHTrunc.qrh_pi` | passed | lean-verified-program | 1 |
| `@evo.Table4Evolution.QRHTrunc.Kernel.qrh_pi` | passed (`cb81845`) | **lean-verified-program** | **0** |
| `@evo.Table4Evolution.OldTrunc.old_pi` | passed | lean-verified-program | 1 |
| `@evo.Table4Evolution.QRHQuarter.qrh_pi_refined` | passed | lean-verified-program | 1 |
| `@evo.Table4Evolution.AgentATrunc.pi_from_theta_power` | passed | lean-verified-program | 1 |
| `@evo.Table4Evolution.AgentASource.pi_from_theta_power_source` | passed | lean-verified-program | 1 |
| `@pv.PVPilot.KernelOnly.gap_exceeds_leading` | passed | **lean-verified-program** | **0** |
| `@tertiary.QRHGlobal.global_interval` | passed | not-program-verified (no program) | 0 |
| `@tertiary.QRHGlobal.sixteenth_interval` | passed | not-program-verified | 0 |
| `@tertiary.QRHGlobal.prime_between_powers` | passed | not-program-verified | 0 |
| `@tertiary.QRHGlobal.intervals_from_agentA_theta` | passed | not-program-verified | 0 |

"lean-verified-program" with 0 native facts means the gate found the source identity, the source
association, an execution witness and the generic correctness theorems in the proof closure, and
no `native_decide` at all. The tertiary theorems execute no program: their finite checks are kernel
`decide` (ladder steps) and `norm_num` (primality).

## 4. Negative controls (`agentB/evidence/controls_round3.py`, 13 of 13 rejected)

Scratch copies of the two new projects (dependencies are the shared, built ones); one mutation at a
time; the affected module must fail to build. Result `pv5/controls_round3.json`: all rejected,
both baselines build.

| Mutation | Rejected by |
|---|---|
| cells certified for `e^{-L/7}` while the profile is proved for `e^{-L/8}` | type mismatch in `pi_bound` |
| QRH program's constants checked against the QRH-free step profile | type mismatch in `pi_bound` |
| non-monotone partition `300, 331, 330` | certificate (`cellsOK`: `lo ≤ hi`) |
| partition ending at 331 | certificate (`decide` on the last boundary) |
| program without the ray-tail constant `U(330)/328` | certificate (`ops` shape) |
| anchor literal replaced by the point literal | certificate (`constOK`) |
| chunks `60 + 60` against the file's `64 + 56` | certificate (`sourceMatchesChunked`) |
| target `4·10⁻¹⁶`, below the 2-cell output | certificate (`upperCheck`) |
| empty program | certificate (`1 ≤ inputs.length`) |
| composite ladder rung `4347 = 3³·7·23` (steps still pass) | `ladder1_prime` |
| ladder rung removed (`3187 → 5869` too long) | `ladder1_ok` (kernel `decide`) |
| frontier row `(80, 0.2)`, not in the node's table | membership proof |
| range of the `1/16` theorem extended to `x ≥ 1327` | proof fails; the statement is false there (no prime in `(1327, 1360.7]`) |

Also: one digit of a C literal changed (`pv5/rebuild_scope.log`, step 4): the configuration rebuilt
and its certificate failed. Not run: mismatched Lean or Mathlib versions (a changed manifest makes
Lake try to fetch).

## 5. Trust boundary

- **Mathematical premises.** Every QRH result assumes the QRH chain as node conclusions:
  `QRHCH2.v5.psi_refined_bound` or `QRHPropagation.v2.theta_frontier` (whose imports end at
  `OpenAIQRH.v1.zeta_seven_eighths`, CH2's density transfer, FKS's zero density, RH to a height),
  plus literature rows (`Dusart2018.v1.proposition_5_4`, `KadiriLumley.v1.table_2`, FKS2 Table 3,
  the FKS2 Table 4 anchor). The Agent A configurations assume `Eθ ≤ K·x^{-1/8}` as a hypothesis.
- **Program semantics.** C correctness is for the modelled restricted-C/binary64 execution of the
  token-matched source (`PVCore.Exec`), not a compiled binary; compiler, OS and hardware are not
  modelled. For the 0-native theorems, the Lean kernel is the only computational trust.
- **Official status.** Nothing here is a Comparator receipt or an official `kind`. Standard axioms
  are necessary, not sufficient, for official acceptance.

## 6. Replay recipe

From a checkout of `qrh-2pv_B` with the shared Lake packages at `network/.lake/packages`
(each project needs `.lake/packages` symlinked to it before any `lake` call, or Lake clones
the packages):

```bash
cd network
for p in Solutions/QRHGlobalIntervals.v1 Solutions/Table4Evolution.v1; do
  mkdir -p $p/.lake && ln -sfn "$PWD/.lake/packages" $p/.lake/packages; done
# Tertiary (about 10 s after the core is built)
(cd Solutions/QRHGlobalIntervals.v1 && lake build && lake env lean tests/Axioms.lean)
# Table 4 evolution: all configurations, the 2-cell kernel route included (about 3 min, 28 GB peak).
# Corrected in the round-3 extension: at this round's commit the umbrella module `Table4Evolution`,
# which tests/Axioms.lean imports, was not a default target, so `lake build Table4EvolutionAll` is
# needed before the axiom check (from the extension on it is a default target).
(cd Solutions/Table4Evolution.v1 && python3 scripts/generate.py --check && lake build \
   && lake build Table4EvolutionAll && lake env lean tests/Axioms.lean)
# Kernel-only A->B' chain (the round-2 KernelChain module is about 3 min, 23 GB)
(cd pilots/pv-replay && lake build PVReplay.KernelOnly && lake env lean tests/AxiomsKernelOnly.lean)
# Local gate on the new endpoints (about 1 min each)
../tools/bin/python scripts/native_assisted/native_assisted_check.py check @evo.Table4Evolution.QRHTrunc.qrh_pi
# Changed-input replay and negative controls (scratch copies; the tree is restored)
bash ../evidence/rebuild_scope.sh; python3 ../evidence/controls_round3.py /tmp/controls
```

Fresh versus cached: the numbers in this document were taken with every dependency (Mathlib, the
core, the FKS2 solutions) already built; only the round-3 modules were compiled. A cold build of the
dependency closure is the round-1/2 cost (the QRH solutions pull in CH2's density certificates).

## 7. Source identities (sha256)

| File | sha256 |
|---|---|
| `Solutions/Table4Evolution.v1/c/agentA_source4.c` | `09aa4ec38505113f…` |
| `Solutions/Table4Evolution.v1/c/agentA_trunc4.c` | `80b73a580817c8fc…` |
| `Solutions/Table4Evolution.v1/c/old_trunc3.c` | `4d9ddac7bbf2d2ca…` |
| `Solutions/Table4Evolution.v1/c/qrh_quarter120.c` | `2f37f28c2f0d1bcf…` |
| `Solutions/Table4Evolution.v1/c/qrh_trunc2.c` | `ef750c59da9f2ba1…` |
| `pilots/agentB-calibration/c/calibration_new.c` | `f206bd817deab53b…` |
| `pilots/agentB-calibration/c/ramanujan_9401_new.c` | `86d204a5a7ba913a…` |
| `Solutions/ProgramVerification/PVCore/Decimal.lean` | `7000eadec394a495…` |
| `Solutions/Table4Evolution.v1/Table4Evolution/Partition.lean` | `e212f99bba9fe87d…` |
| `Solutions/Table4Evolution.v1/Table4Evolution/Bounds.lean` | `d7f1943f49217200…` |
| `Solutions/Table4Evolution.v1/Table4Evolution/Instance.lean` | `e7c3a07b38b25aff…` |
| `Solutions/Table4Evolution.v1/Table4Evolution/Profiles.lean` | `b3662ed780489bad…` |
| `Solutions/QRHGlobalIntervals.v1/QRHGlobalIntervals/Criterion.lean` | `1391b260958fab95…` |
| `Solutions/QRHGlobalIntervals.v1/QRHGlobalIntervals/Ladder.lean` | `252517445dee3024…` |
| `Solutions/QRHGlobalIntervals.v1/QRHGlobalIntervals/Global.lean` | `9b567c01c4c5e496…` |
| `Solutions/QRHGlobalIntervals.v1/QRHGlobalIntervals/Sixteenth.lean` | `85c4bb666d911da4…` |

Full hashes are in each attestation under `pv-evidence/` (`pins`, `method_checks.S_source_identity`).
