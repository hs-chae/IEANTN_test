/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.AgentASource
import PVCore.Decimal

/-!
# The four-cell power-profile transport (AgentASource) with no native fact

The kernel route of `KernelOnly.lean` for the configuration `AgentASource` (Agent A's earlier θ coefficient `0.009904 + 10⁻¹²` as a
hypothesis, cells `[300, 327]` and three unit cells, scale `2^-73`): literal decoding, the
shared-contract check, the cell and constant certificates, each `decide +kernel`.
-/

namespace Table4Evolution.AgentASource.Kernel

open Real IEANTN PVCore Table4Evolution Table4Evolution.AgentASource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem decode_k : decode program =
    some (xsQ, 1 / 2 ^ 73, [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (1 / 10 ^ 30) (12228 / 10 ^ 24) xsQ (1 / 2 ^ 73)
    [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] = true := by
  decide +kernel

theorem cells_k : cellsOK (1 / 8) 73 (fun _ => K) bs xsQ = true := by
  decide +kernel

theorem const_k : constOK (1 / 8) K K anchorQ pointQ tailQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (1 / 10 ^ 30) (12228 / 10 ^ 24) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- The statement of `AgentASource.pi_from_theta_power_source`, kernel only. -/
theorem pi_from_theta_power_source
    (hθ : HasPowerLogBound Eθ (0.009904 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300))
    (hAnchor : FKS2.v6.table4_anchor_300) :
    HasNumericalBound Eπ (12228 / 10 ^ 24) (exp 330) := by
  obtain ⟨-, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hb := program_bound certificate_k hs ho
  rw [hx] at hb
  have hK : ((K : ℚ) : ℝ) = 0.009904 + 1 / 10 ^ 12 := by norm_num [K]
  have hprof := profile_power (K := K) (by norm_num [K]) (by rw [hK]; exact hθ)
  have h := pi_bound (rest := [327, 328, 329, 330]) hprof hAnchor cells_k (by decide) const_k hb
  norm_num at h ⊢
  exact h

end Table4Evolution.AgentASource.Kernel
