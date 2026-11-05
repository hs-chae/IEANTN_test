# Round 3 extension: trust audit and replay

Every claim below was checked by building the code and printing axioms (`tests/Axioms*.lean` in each
project). Times are wall-clock on the shared 128-core machine with dependency caches warm. Paths under
`agentB/evidence/` are in the author's workspace next to the checkout, not in the repository (as in
round 3); the gate results and control outcomes they hold are reproduced in the tables below, and the
gate's attestations are committed under `pv-evidence/`.

## 1. Final theorems, axioms, native facts

"0" means `#print axioms` lists exactly `propext`, `Classical.choice`, `Quot.sound`.

| Theorem | Project | Native facts |
|---|---|---|
| `QRHGlobal.twentyfourth_interval`, `prime_gap_twentyfourth`, `not_twentyfourth_1338` | `Solutions/QRHGlobalIntervals.v1` | **0** |
| `QRHGlobal.sixteenth_interval_sharp`, `not_sixteenth_1327` | same | **0** |
| `QRHGlobal.eTheta_le_bklnw` (BKLNW `ψ` row + Corollary 5.1 ⇒ `Eθ ≤ 2.4530·10⁻¹²`) | same | **0** |
| `QRHGlobal.count_of_theta_power`, `count_of_pi_power`, `interval_of_pi_power` | same | **0** |
| `QRHGlobal.count_80`, `count_300`, `count_1000` | same | **0** |
| `QRHGlobal.count_from_agentA_pi`, `intervals_from_agentA_pi` (Agent A's `π` bound a hypothesis) | same | **0** |
| `QRHGlobal.mills_of_step`, `mills_qrh`, `mills_eight` | same | **0** |
| `QRHGlobal.prime_p2`, `mills_explicit` | same | **0** |
| `QRHGlobal.oppermann_powers`, `andrica_eighth`, `andrica_eighth_24` | same | **0** |
| `Table4Evolution.power_ray`, `power_pi_bound` (generic) | `Solutions/Table4Evolution.v1` | **0** |
| `Table4Evolution.PowerNetwork.pi_power`, `PowerAgentA.pi_power`, `PowerAgentASource.pi_power` | same | **0** |
| `Table4Evolution.OldTrunc.Kernel.old_pi` (`FKS2Numerics.v6.old_pi`) | same | **0** |
| `Table4Evolution.AgentATrunc.Kernel.pi_from_theta_power`, `AgentASource.Kernel.pi_from_theta_power_source` | same | **0** |
| `PVRamanujan.KernelOnly.{V1, V2, OldGrouped}.epsilon_budget`, `UpdatedGrouped.epsilon_budget_fixed_target` | `pilots/pv-replay` | **0** |
| `PVThreeChain.StageB.budget`, `PVThreeChain.pi_input_330`, `pi_input_330_of` | `pilots/pv-twobackend` | **0** |
| `PVThreeChain.gap_exceeds_leading` | same | 17, all in Agent A's θ stage (`WinnerOriginalScalars.*`, `WinnerReversDensity.*`, `ReversCertificate.checked300`, `Revers.*` checks) |
| `PVThreeChain.gap_exceeds_leading_source` (changed input) | same | 17, all in Agent A's θ stage (`WinnerOriginalScalars.*` 14, `WinnerOriginalDensity.*` 2, `SharpCertificate.checked300`) |

## 2. Local gate (`scripts/native_assisted/native_assisted_check.py`)

Twenty-two new endpoints, run one at a time at `2a3ff26` on a clean tree with no other build running (log `agentB/evidence/pv6/gate_round3x_final_2a3ff26.log`): 22/22 passed, max 142 s, peak 14.2 GB.

| Endpoint | Status | Method | Native | Time, peak |
|---|---|---|---|---|
| `@evo.Table4Evolution.OldTrunc.Kernel.old_pi` | passed | lean-verified-program | 0 | 44 s, 8.9 GB |
| `@evo.Table4Evolution.AgentATrunc.Kernel.pi_from_theta_power` | passed | lean-verified-program | 0 | 34 s, 8.9 GB |
| `@evo.Table4Evolution.AgentASource.Kernel.pi_from_theta_power_source` | passed | lean-verified-program | 0 | 34 s, 8.9 GB |
| `@evo.Table4Evolution.PowerNetwork.pi_power` | passed | lean-verified-program | 0 | 34 s, 8.9 GB |
| `@evo.Table4Evolution.PowerAgentA.pi_power` | passed | lean-verified-program | 0 | 34 s, 8.9 GB |
| `@evo.Table4Evolution.PowerAgentASource.pi_power` | passed | lean-verified-program | 0 | 33 s, 8.9 GB |
| `@pv.PVRamanujan.KernelOnly.V1.epsilon_budget` | passed | lean-verified-program | 0 | 30 s, 8.8 GB |
| `@pv.PVRamanujan.KernelOnly.V2.epsilon_budget` | passed | lean-verified-program | 0 | 30 s, 8.8 GB |
| `@pv.PVRamanujan.KernelOnly.OldGrouped.epsilon_budget` | passed | lean-verified-program | 0 | 30 s, 8.8 GB |
| `@pv.PVRamanujan.KernelOnly.UpdatedGrouped.epsilon_budget_fixed_target` | passed | lean-verified-program | 0 | 24 s, 8.8 GB |
| `@twobackend.PVThreeChain.gap_exceeds_leading` | passed | lean-verified-program | 17 | 142 s, 14.2 GB |
| `@twobackend.PVThreeChain.gap_exceeds_leading_source` | passed | lean-verified-program | 17 | 59 s, 9.5 GB |
| `@tertiary.QRHGlobal.twentyfourth_interval` | passed | not-program-verified | 0 | 12 s, 5.3 GB |
| `@tertiary.QRHGlobal.sixteenth_interval_sharp` | passed | not-program-verified | 0 | 10 s, 5.3 GB |
| `@tertiary.QRHGlobal.count_300` | passed | not-program-verified | 0 | 11 s, 5.3 GB |
| `@tertiary.QRHGlobal.count_from_agentA_pi` | passed | not-program-verified | 0 | 13 s, 5.3 GB |
| `@tertiary.QRHGlobal.intervals_from_agentA_pi` | passed | not-program-verified | 0 | 13 s, 5.3 GB |
| `@tertiary.QRHGlobal.mills_qrh` | passed | not-program-verified | 0 | 11 s, 5.3 GB |
| `@tertiary.QRHGlobal.mills_eight` | passed | not-program-verified | 0 | 10 s, 5.3 GB |
| `@tertiary.QRHGlobal.mills_explicit` | passed | not-program-verified | 0 | 11 s, 5.3 GB |
| `@tertiary.QRHGlobal.oppermann_powers` | passed | not-program-verified | 0 | 10 s, 5.3 GB |
| `@tertiary.QRHGlobal.andrica_eighth_24` | passed | not-program-verified | 0 | 12 s, 5.3 GB |

For the two chains the gate checks both backends: Agent A's `lean-dyadic-expr` program
(`WinnerDensityA.ModelProgram.program`, source files pinned by SHA-256) and the two
`restricted-c-binary64` files (`power_agentA.c` or `power_agentA_source.c`, and `budget_331.c`).

For the Table 4 endpoints the gate's build step, `lake build Table4Evolution`, builds the core
library of that name, not the umbrella module `Table4Evolution` that the extractor imports. Before
this extension the umbrella was not a default target either, so a plain `lake build` left its `.olean`
stale: the axiom test reported `PowerAgentASource.pi_power` as an unknown constant. The umbrella library
is now a default target, and the gate run above came right after a build from the project's own root
(`agentB/evidence/pv6/rebuild_t4_pregate2.log`; the full package rebuild, 24 modules, 3 min 58 s,
37 GB, is `rebuild_t4_final.log`). Round 3's Table 4 attestations likewise imported an umbrella built
outside the gate. The first chain endpoint's build step took 90 s: it recompiled the Table 4 modules
that the chain imports (§5).

## 3. Negative controls (`agentB/evidence/controls_round3x.py`, 30 of 30 rejected; every baseline built)

Scratch copies of the four projects, dependencies shared and built; a baseline build of the affected
modules first; one mutation at a time; the affected module must fail to build; the baseline is rebuilt at
the end. The first run copied `pilots/pv-replay` flat, and its baseline failed because pilot modules read
sibling solutions through relative `include_str` paths (`../../../Solutions/…`); the script now mirrors
the repository layout for pilots, and the two `pv-replay` cases were rerun. Results
`agentB/evidence/pv6/controls_round3x.json` (28 cases) and `controls_round3x_pv-replay.json` (2 cases).

| Mutation | Module | First build error |
|---|---|---|
| 1/24 from the frontier row (128, 0.03013): needs c > 0.0603 | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:338:4: linarith failed to find a contradiction |
| 1/24 threshold lowered to 1338 (step 1338 -> 1361 exceeds 1338^{7/8}/24) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:72:58: Tactic `decide` proved that the proposition |
| 1/24 ladder rung 1381 removed (step 1361 -> 1399 too long) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:72:58: Tactic `decide` proved that the proposition |
| BKLNW Table 8 row (50, 1.1199e-9) in place of (100, 2.45299e-12) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:157:32: Type mismatch: After simplification, term |
| a2(100) <= 140 claimed (145 terms of at most 1) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:131:2: linarith failed to find a contradiction |
| no prime in (1339, 1339 + 1339^{7/8}/24] claimed (1361 is in it) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:379:32: linarith failed to find a contradiction |
| 1/16 threshold lowered to 1327 (step 1327 -> 1361 exceeds 1327^{7/8}/16) | `QRHGlobalIntervals.TwentyFourth` | QRHGlobalIntervals/TwentyFourth.lean:360:55: Tactic `decide` proved that the proposition |
| count from e^300: lower constant 0.9739 (> 1 - 2*0.01311) | `QRHGlobalIntervals.Counts` | QRHGlobalIntervals/Counts.lean:83:4: linarith failed to find a contradiction |
| count from e^300: upper constant 1.0262 (< 1 + 2*0.01311) | `QRHGlobalIntervals.Counts` | QRHGlobalIntervals/Counts.lean:86:4: linarith failed to find a contradiction |
| count from Agent A's pi bound: lower constant 0.98106 (> 1 - 2*0.00947147) | `QRHGlobalIntervals.Counts` | QRHGlobalIntervals/Counts.lean:132:4: linarith failed to find a contradiction |
| pi-route interval constant 0.0189 (< 2*0.00947147) | `QRHGlobalIntervals.Counts` | QRHGlobalIntervals/Counts.lean:146:2: linarith failed to find a contradiction |
| pi-route criterion without the boundary terms | `QRHGlobalIntervals.Counting` | QRHGlobalIntervals/Counting.lean:366:16: linarith failed to find a contradiction |
| Mills step for k >= 7 (q^{7k/8} <= q^{k-1} needs k >= 8) | `QRHGlobalIntervals.Mills` | QRHGlobalIntervals/Mills.lean:178:46: linarith failed to find a contradiction |
| Mills construction with p < (q+1)^k instead of p + 1 < (q+1)^k | `QRHGlobalIntervals.Mills` | QRHGlobalIntervals/Mills.lean:112:47: Application type mismatch: The argument |
| Oppermann-type intervals for k >= 7 | `QRHGlobalIntervals.Corollaries` | QRHGlobalIntervals/Corollaries.lean:57:63: Application type mismatch: The argument |
| Andrica-type bound 1/200 from 1339 (1/192 is what 1/24 gives) | `QRHGlobalIntervals.Corollaries` | QRHGlobalIntervals/Corollaries.lean:151:2: linarith failed to find a contradiction |
| power kernel majorant with kappa = 8/7 (derivative no longer dominates at log t = 300) | `Table4Evolution.PowerTransport` | Table4Evolution/PowerTransport.lean:82:6: linarith failed to find a contradiction |
| anchor term with e^{11} in place of e^{45/4} | `Table4Evolution.PowerTransport` | Table4Evolution/PowerTransport.lean:180:15: unsolved goals |
| network power transport: target 0.013155 below the program output | `Table4Evolution.PowerNetwork` | Table4Evolution/PowerNetwork.lean:43:2: Tactic `decide` failed for proposition |
| network theta coefficient misread as 0.01300 (row says 0.01310) | `Table4Evolution.PowerNetwork` | Table4Evolution/PowerNetwork.lean:62:49: Type mismatch |
| C file: anchor constant changed (1.4374e-7 -> 1.3374e-7) | `Table4Evolution.PowerAgentA` | Table4Evolution/PowerAgentA.lean:41:2: Tactic `decide` failed for proposition |
| Agent A power transport: claimed 0.0098162 below the certified 0.0098163 | `Table4Evolution.PowerAgentA` | Table4Evolution/PowerAgentA.lean:60:2: Type mismatch |
| kernel route, 3 cells: target 1.68e-12 below the output 1.68991e-12 | `Table4Evolution.OldTruncKernel` | Table4Evolution/OldTruncKernel.lean:31:2: Tactic `decide` failed for proposition |
| kernel route, 4 cells: cells certified at scale 2^-74 (file has 2^-73) | `Table4Evolution.AgentATruncKernel` | Table4Evolution/AgentATruncKernel.lean:33:2: Tactic `decide` failed for proposition |
| data link claimed from e^300 with a pi bound valid from e^330 | `ThreeChain.Chain` | ThreeChain/Chain.lean:89:30: Type mismatch |
| budget target 112.14 below the certified 112.1461 | `ThreeChain.StageB331` | ThreeChain/StageB331.lean:53:2: Tactic `decide` failed for proposition |
| chain factor 7.88 (the budget gives 119.99 - 112.15 = 7.84) | `ThreeChain.Chain` | ThreeChain/Chain.lean:111:92: unsolved goals |
| C file: first budget literal changed | `ThreeChain.StageB331` | ThreeChain/StageB331.lean:53:2: Tactic `decide` failed for proposition |
| kernel decoding: first V1 literal claimed 714/1024 (file decodes to 713/1024) | `PVReplay.RamanujanKernel` | PVReplay/RamanujanKernel.lean:40:24: Tactic `decide` failed for proposition |
| V2 budget target 9.100 below the program's certified 9.10... | `PVReplay.RamanujanKernel` | PVReplay/RamanujanKernel.lean:73:2: Tactic `decide` failed for proposition |

## 4. Literal decoding and the output tolerance

The kernel routes reuse round 3's `PVCore.decode_of_decodeL`. One new constraint surfaced: the shared
contract's `check` requires the binary64 output to be within `eps` of the exact value of the program's
operations. Round 3's Table 4 programs output about `5·10⁻¹⁶`, so `eps = 10⁻³⁰` worked; the power-form
programs output about `10⁻²`, whose rounding is about `10⁻¹⁸`, so they use `eps = 10⁻¹⁷`. With the
smaller `eps` the check is simply `false` and `decide +kernel` reports that it did not reduce.

## 5. Lake: one module, two traces

Lake records a different trace for the same `Table4Evolution` module depending on how a build
reaches it. A plain `lake build` from the package root compiles the core modules as members of the core
library. A build that reaches them through an import, such as `lake build T4PowerNetwork` alone or a
downstream package like `pilots/pv-twobackend`, traces them differently and recompiles them inside the
package's `.lake`. Observed three times:

- the control harness's scratch copy of `pilots/pv-twobackend` recompiled `Profiles`, `Partition`,
  `Bounds`, `Instance` and `PowerTransport` at 11:48–11:51 UTC, and a gate extraction running at the
  same time found `Table4Evolution/Partition.olean` missing and stopped as "blocked";
- right after a full root build, `lake build --no-build` reported everything current while
  `lake build --no-build T4PowerNetwork` reported `Partition` out of date;
- the repository's own pilot, building `ThreeChain` at 12:36 UTC, recompiled `Partition`, `Bounds`,
  `Instance`, `PowerTransport`, `PowerAgentA` and `PowerAgentASource`
  (`agentB/evidence/pv6/threechain_source_build.log`).

Each recompilation compiles the same sources, so no result depends on it. It does mean that two builds
sharing the package must never run at the same time. So the final gate run (§2) was made with nothing
else building, after a full build from the package root, with the Table 4 endpoints first.

## 6. Replay recipe

From a checkout of `qrh-2pv_B` with the shared Lake packages at `network/.lake/packages`:

```bash
cd network
for p in Solutions/QRHGlobalIntervals.v1 Solutions/Table4Evolution.v1; do
  mkdir -p $p/.lake && ln -sfn "$PWD/.lake/packages" $p/.lake/packages; done
# Tertiary, including the explicit Mills constant (about 30 s after the core is built)
(cd Solutions/QRHGlobalIntervals.v1 && lake build && lake env lean tests/Axioms.lean)
# Table 4: every configuration, the kernel routes, the power-form transports and the umbrella module
# the tests import (about 4 min and 37 GB peak for the package; generators must reproduce the C files)
(cd Solutions/Table4Evolution.v1 && python3 scripts/generate.py --check \
   && python3 scripts/generate_power.py --check && lake build && lake env lean tests/Axioms.lean)
# Ramanujan replays, kernel only (about 4.5 min, 19 GB)
(cd pilots/pv-replay && lake build PVReplay.RamanujanKernel && lake env lean tests/AxiomsRamanujanKernel.lean)
# Three-program chain, after Table4Evolution (the first build compiles Agent A's Revers closure, about 6 min)
(cd pilots/pv-twobackend && lake build ThreeChain && lake env lean tests/AxiomsThreeChain.lean)
# Local gate, one endpoint at a time
../tools/bin/python scripts/native_assisted/native_assisted_check.py check @twobackend.PVThreeChain.gap_exceeds_leading
# Negative controls (script in the author's workspace, agentB/evidence/; scratch copies, the tree is not touched)
python3 ../evidence/controls_round3x.py /tmp/controls3x
```

## 7. Trust boundary

- **Mathematical premises.** As in round 3: the QRH chain enters as node conclusions
  (`QRHPropagation.v2.theta_frontier`, `QRHCH2.v5.psi_refined_bound`), plus literature rows
  (`Dusart2018.v1.proposition_5_4`, `KadiriLumley.v1.table_2`, `BKLNW.v1.table8_psi_bound_above`,
  `BKLNW.v1.corollary_5_1_above`, `FKS2.v8.table3_theta_*`, `FKS2.v6.table4_anchor_300`) and the
  pipeline criterion `PrimeInterval.v1.eTheta_criterion`. Agent A's bounds are hypotheses, except in
  the chain, which calls Agent A's theorem with Agent A's named inputs as its own hypotheses.
- **Program semantics.** The modelled restricted-C/binary64 execution of the token-matched source; the
  compiler and hardware are not modelled.
- **Official status.** Nothing here is a Comparator receipt or an official `kind`.
