/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Profiles
import Table4Evolution.Data.AgentATrunc

/-!
# A later θ profile through the same transport: `Eθ ≤ K·x^{-1/8}`

Agent A's committed solution `WinnerDensityA` proves `HasPowerLogBound Eθ (0.009782 + 10⁻¹²) 0 (7/8)
(exp 300)` (`revers_source_theta300`, under its own named inputs). Taken here as a hypothesis, it is
a new input profile `U(L) = K·e^{-L/8}`, a factor `L²/(283 K) ≈ 3.9·10⁴` below `Q(L)` at `L = 330`.
The proof core is unchanged; the partition data, four cell literals and three constants are new.
Four cells: `[300, 327]` and three unit cells.

Result: `Eπ ≤ 1.2078·10⁻²⁰` on `x ≥ e^330`. A second route, not a new bound: Agent A's own π
theorem `ScopedWinnerA.pi_00947147` gives `0.00947147·e^{-41.25} ≈ 1.157·10⁻²⁰` there directly.
One native fact: `certificate`.
-/

namespace Table4Evolution.AgentATrunc

open Real IEANTN PVCore

/-- Agent A's θ coefficient. -/
def K : ℚ := 9782 / 10 ^ 6 + 1 / 10 ^ 12

def program : Program :=
  ⟨"fks2_table4_transport", literals, scaleLiteral,
    [(.plus, anchorLiteral), (.plus, pointLiteral), (.plus, tailLiteral)]⟩

def source : String := include_str ".." / "c" / "agentA_trunc4.c"

theorem certificate :
    upperCheck source program (1 / 10 ^ 30) (12078 / 10 ^ 24) = true ∧
    cellsOK (1 / 8) 73 (fun _ => K) bs (valuesOf program).xs = true ∧
    (valuesOf program).scale = 1 / 2 ^ 73 ∧
    (valuesOf program).ops = [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] ∧
    constOK (1 / 8) K K anchorQ pointQ tailQ = true := by
  native_decide

/-- **Later profile.** From a θ power bound `K·x^{-1/8}` on `x ≥ e^300` (Agent A's coefficient) and
the shared anchor, `Eπ ≤ 1.2078·10⁻²⁰` on `x ≥ e^330`. -/
theorem pi_from_theta_power
    (hθ : HasPowerLogBound Eθ (0.009782 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300))
    (hAnchor : FKS2.v6.table4_anchor_300) :
    HasNumericalBound Eπ (12078 / 10 ^ 24) (exp 330) := by
  have hK : ((K : ℚ) : ℝ) = 0.009782 + 1 / 10 ^ 12 := by norm_num [K]
  have hprof := profile_power (K := K) (by norm_num [K]) (by rw [hK]; exact hθ)
  have h := pi_bound (rest := [327, 328, 329, 330]) hprof hAnchor certificate.2.1 (by decide)
    certificate.2.2.2.2 (program_bound certificate.1 certificate.2.2.1 certificate.2.2.2.1)
  norm_num at h ⊢
  exact h

end Table4Evolution.AgentATrunc
