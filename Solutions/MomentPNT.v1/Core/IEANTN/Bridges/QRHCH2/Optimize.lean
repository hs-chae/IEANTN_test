/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.QRHCH2.v2.Conclusions
import Mathlib.Tactic

/-! Conditional composition only. The analytic transfers are separate named hypotheses. -/
namespace QRHCH2.v2

/-- Apply the same-input paired transfer to the QRH source conclusion. -/
theorem paired_bound_of_inputs (qrh : OpenAIQRH.v1.zeta_seven_eighths)
    (transfer : CH2.v6.paired_transfer) : psi_paired_bound :=
  transfer qrh

/-- Apply the density-enhanced transfer, retaining all four mathematical inputs. -/
theorem density_frontier_of_inputs (qrh : OpenAIQRH.v1.zeta_seven_eighths)
    (transfer : CH2.v6.density_transfer) (density : FKS.v3.density_0618)
    (rh : PlattTrudgian.v1.rh_up_to) : psi_density_frontier :=
  transfer density rh qrh

/-- Normalize the existing CH2 bound and retain the smaller allowance. -/
theorem density_hybrid_of_inputs (power : psi_density_frontier)
    (ch2 : CH2.v1.corollary_1_3_psi) : psi_density_hybrid := by
  intro L C hLC x hx1 hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  refine le_min ?_ (power L C hLC x hx)
  rw [IEANTN.Eψ, div_le_iff₀ hx0]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have he :
      (Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) + 113.67 / Real.sqrt x) * x =
        Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) * x + 113.67 * Real.sqrt x := by
    field_simp
    nlinarith [Real.sq_sqrt hx0.le]
  rw [he]
  exact ch2 x hx1

end QRHCH2.v2
