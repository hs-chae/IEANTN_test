/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.QRHCH2.v1.Conclusions
import Mathlib.Tactic

/-! Short composition proofs. No analytic transfer is hidden in this bridge. -/

namespace QRHCH2.v1

/-- Apply the fixed-strip pipeline to the QRH source node. -/
theorem power_bound_of_inputs (qrh : OpenAIQRH.v1.zeta_seven_eighths)
    (transfer : CH2.v5.psi_bound_of_fixed_strip) : psi_power_bound := by
  intro x hx
  have h := transfer (7 / 8) (by norm_num) (by norm_num) qrh
  norm_num at h
  exact h x hx

/-- Normalize the existing CH2 bound and intersect it with the new conclusion. -/
theorem hybrid_bound_of_inputs (power : psi_power_bound)
    (ch2 : CH2.v1.corollary_1_3_psi) : psi_hybrid_bound := by
  intro x hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 128)).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  refine le_min ?_ (power x hx)
  rw [IEANTN.Eψ, div_le_iff₀ hx0]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have he :
      (Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) + 113.67 / Real.sqrt x) * x =
        Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) * x + 113.67 * Real.sqrt x := by
    field_simp
    nlinarith [Real.sq_sqrt hx0.le]
  rw [he]
  exact ch2 x hx1

end QRHCH2.v1
