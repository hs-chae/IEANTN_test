/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.PowerTransport
import Table4Evolution.Data.PowerAgentA
import PVCore.Decimal

/-!
# Power-form transport from Agent A's θ coefficient, kernel only

Input: Agent A's `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` on `x ≥ e^300`
(`WinnerDensityA.revers_source_theta300`, the output of Agent A's evaluated dyadic program, under its
own named inputs), taken as a hypothesis, and the anchor. Output: `Eπ ≤ 0.0098163·x^{-1/8}` on
`x ≥ e^330`, a decaying bound that the Ramanujan budget can consume (`pilots/pv-twobackend`,
`ThreeChain`). Weaker than Agent A's own `π` theorem (`0.00947147`); its role is the middle program of
a three-program chain.
-/

namespace Table4Evolution.PowerAgentA

open Real IEANTN PVCore Table4Evolution

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Agent A's θ coefficient. -/
def K : ℚ := 9782 / 10 ^ 6 + 1 / 10 ^ 12

def program : Program :=
  ⟨"fks2_power_transport", literals, scaleLiteral, [(.plus, anchorLiteral)]⟩

def source : String := include_str ".." / "c" / "power_agentA.c"

theorem decode_k : decode program = some (xsQ, 1 / 2 ^ 6, [(.plus, anchorQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (1 / 10 ^ 17) (98163 / 10 ^ 7) xsQ (1 / 2 ^ 6)
    [(.plus, anchorQ)] = true := by
  decide +kernel

theorem power_k : powerOK K 6 xsQ anchorQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (1 / 10 ^ 17) (98163 / 10 ^ 7) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- `Eπ ≤ 0.0098163·x^{-1/8}` on `x ≥ e^330`, from Agent A's θ coefficient and the anchor. -/
theorem pi_power (hθ : HasPowerLogBound Eθ (0.009782 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300))
    (hAnchor : FKS2.v6.table4_anchor_300) :
    HasPowerLogBound Eπ 0.0098163 0 (7 / 8) (exp 330) := by
  have hK : ((K : ℚ) : ℝ) = 0.009782 + 1 / 10 ^ 12 := by norm_num [K]
  obtain ⟨-, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hB := program_bound1 certificate_k hs ho
  rw [hx] at hB
  have h := power_pi_bound (K := K) (by rw [hK]; exact hθ) hAnchor power_k hB
  norm_num at h ⊢
  exact h

end Table4Evolution.PowerAgentA
