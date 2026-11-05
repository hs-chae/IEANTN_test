/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Profiles
import Table4Evolution.Data.AgentASource

/-!
# The earlier Agent A θ coefficient through the same transport

Agent A's `WinnerDensityA.source_theta300` (original inputs) gives `Eθ ≤ (0.009904 + 10⁻¹²)·x^{-1/8}`
on `x ≥ e^300`; `revers_source_theta300` (Revers inputs) gives `0.009782 + 10⁻¹²` (`AgentATrunc`).
Same partition, same proof core; only `K`, the four literals and the three constants differ.
Result: `Eπ ≤ 1.2228·10⁻²⁰` on `x ≥ e^330`, against `1.2078·10⁻²⁰` for the Revers coefficient.
One native fact: `certificate`.
-/

namespace Table4Evolution.AgentASource

open Real IEANTN PVCore

/-- Agent A's θ coefficient. -/
def K : ℚ := 9904 / 10 ^ 6 + 1 / 10 ^ 12

def program : Program :=
  ⟨"fks2_table4_transport", literals, scaleLiteral,
    [(.plus, anchorLiteral), (.plus, pointLiteral), (.plus, tailLiteral)]⟩

def source : String := include_str ".." / "c" / "agentA_source4.c"

theorem certificate :
    upperCheck source program (1 / 10 ^ 30) (12228 / 10 ^ 24) = true ∧
    cellsOK (1 / 8) 73 (fun _ => K) bs (valuesOf program).xs = true ∧
    (valuesOf program).scale = 1 / 2 ^ 73 ∧
    (valuesOf program).ops = [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] ∧
    constOK (1 / 8) K K anchorQ pointQ tailQ = true := by
  native_decide

/-- From the earlier θ coefficient `0.009904 + 10⁻¹²` and the shared anchor, `Eπ ≤ 1.2228·10⁻²⁰` on
`x ≥ e^330`. -/
theorem pi_from_theta_power_source
    (hθ : HasPowerLogBound Eθ (0.009904 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300))
    (hAnchor : FKS2.v6.table4_anchor_300) :
    HasNumericalBound Eπ (12228 / 10 ^ 24) (exp 330) := by
  have hK : ((K : ℚ) : ℝ) = 0.009904 + 1 / 10 ^ 12 := by norm_num [K]
  have hprof := profile_power (K := K) (by norm_num [K]) (by rw [hK]; exact hθ)
  have h := pi_bound (rest := [327, 328, 329, 330]) hprof hAnchor certificate.2.1 (by decide)
    certificate.2.2.2.2 (program_bound certificate.1 certificate.2.2.1 certificate.2.2.2.1)
  norm_num at h ⊢
  exact h

end Table4Evolution.AgentASource
