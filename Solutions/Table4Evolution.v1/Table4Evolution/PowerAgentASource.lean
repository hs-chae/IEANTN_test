/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.PowerTransport
import Table4Evolution.Data.PowerAgentASource
import PVCore.Decimal

/-!
# Power-form transport from Agent A's other θ coefficient, kernel only

Changed-input replay of `Table4Evolution.PowerAgentA`. Input: Agent A's
`Eθ ≤ (0.009904 + 10⁻¹²)·x^{-1/8}` on `x ≥ e^300` (`WinnerDensityA.source_theta300`, original inputs),
taken as a hypothesis, and the anchor. Output: `Eπ ≤ 0.0099388·x^{-1/8}` on `x ≥ e^330`. The C file
and the data module were generated from the coefficient alone (`scripts/generate_power.py`); the
theorem used is the same `power_pi_bound`. Consumed by `PVThreeChain.gap_exceeds_leading_source`
(`pilots/pv-twobackend`).
-/

namespace Table4Evolution.PowerAgentASource

open Real IEANTN PVCore Table4Evolution

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Agent A's θ coefficient, original inputs. -/
def K : ℚ := 9904 / 10 ^ 6 + 1 / 10 ^ 12

def program : Program :=
  ⟨"fks2_power_transport", literals, scaleLiteral, [(.plus, anchorLiteral)]⟩

def source : String := include_str ".." / "c" / "power_agentA_source.c"

theorem decode_k : decode program = some (xsQ, 1 / 2 ^ 6, [(.plus, anchorQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (1 / 10 ^ 17) (99388 / 10 ^ 7) xsQ (1 / 2 ^ 6)
    [(.plus, anchorQ)] = true := by
  decide +kernel

theorem power_k : powerOK K 6 xsQ anchorQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (1 / 10 ^ 17) (99388 / 10 ^ 7) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- `Eπ ≤ 0.0099388·x^{-1/8}` on `x ≥ e^330`, from Agent A's θ coefficient and the anchor. -/
theorem pi_power (hθ : HasPowerLogBound Eθ (0.009904 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300))
    (hAnchor : FKS2.v6.table4_anchor_300) :
    HasPowerLogBound Eπ 0.0099388 0 (7 / 8) (exp 330) := by
  have hK : ((K : ℚ) : ℝ) = 0.009904 + 1 / 10 ^ 12 := by norm_num [K]
  obtain ⟨-, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hB := program_bound1 certificate_k hs ho
  rw [hx] at hB
  have h := power_pi_bound (K := K) (by rw [hK]; exact hθ) hAnchor power_k hB
  norm_num at h ⊢
  exact h

end Table4Evolution.PowerAgentASource
