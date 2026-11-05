/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.PowerTransport
import Table4Evolution.Data.PowerNetwork
import PVCore.Decimal
import IEANTN.Nodes.QRHPropagation.v2.Conclusions

/-!
# Power-form transport from the network's own θ row, kernel only

Input: `QRHPropagation.v2.theta_frontier`, row `(300, 0.01310)`, i.e. `Eθ ≤ 0.01311·x^{-1/8}` on
`x ≥ e^300`, and the anchor `FKS2.v6.table4_anchor_300`. The program `c/power_network.c` computes the
coefficient `K·(1 + κ/330) + (330/300)·e^{45/4}·(1.6997·10⁻¹² + K·e^{-75/2})` (two inputs, one
constant). Output: `Eπ ≤ 0.013156·x^{-1/8}` on `x ≥ e^330`.

Compared with `QRHPropagation.v2.pi_density_300` (`Eπ ≤ 0.01323·x^{-1/8}` on `x ≥ e^300`, from the
same frontier): 0.56% smaller on the subray `x ≥ e^330`. Every finite fact is `decide +kernel`.
-/

namespace Table4Evolution.PowerNetwork

open Real IEANTN PVCore Table4Evolution

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The frontier coefficient `0.01310 + 10⁻⁵`. -/
def K : ℚ := 1310 / 10 ^ 5 + 1 / 10 ^ 5

def program : Program :=
  ⟨"fks2_power_transport", literals, scaleLiteral, [(.plus, anchorLiteral)]⟩

def source : String := include_str ".." / "c" / "power_network.c"

theorem decode_k : decode program = some (xsQ, 1 / 2 ^ 6, [(.plus, anchorQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (1 / 10 ^ 17) (13156 / 10 ^ 6) xsQ (1 / 2 ^ 6)
    [(.plus, anchorQ)] = true := by
  decide +kernel

theorem power_k : powerOK K 6 xsQ anchorQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (1 / 10 ^ 17) (13156 / 10 ^ 6) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- `Eπ ≤ 0.013156·x^{-1/8}` on `x ≥ e^330`, from the network's θ frontier and the anchor. -/
theorem pi_power (hθ : QRHPropagation.v2.theta_frontier) (hAnchor : FKS2.v6.table4_anchor_300) :
    HasPowerLogBound Eπ 0.013156 0 (7 / 8) (exp 330) := by
  have hrow : ((300 : ℝ), (0.01310 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have hb := hθ 300 0.01310 hrow
  have hK : ((K : ℚ) : ℝ) = 0.01310 + 1 / 100000 := by norm_num [K]
  obtain ⟨-, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hB := program_bound1 certificate_k hs ho
  rw [hx] at hB
  have h := power_pi_bound (K := K) (by rw [hK]; exact hb) hAnchor power_k hB
  norm_num at h ⊢
  exact h

end Table4Evolution.PowerNetwork
