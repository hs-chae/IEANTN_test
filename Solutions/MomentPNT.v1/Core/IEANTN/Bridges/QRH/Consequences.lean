/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Bridges.QRH.Geometry
import IEANTN.Nodes.ZeroFreeHalfPlane.v1.Conclusions
import IEANTN.Nodes.QRHConsequences.v1.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.ZeroFreeHeight.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Actual QRH instances; finite verified height is used only for the descent result. -/
namespace QRHConsequencesProof
open Real IEANTN

theorem density_vanishes (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (h : ZeroFreeHalfPlane.v1.density_vanishes) : QRHConsequences.v1.density_vanishes :=
  fun σ T hσ ↦ h (7 / 8) σ T hqrh hσ

theorem reciprocal_differentiable (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (h : ZeroFreeHalfPlane.v1.reciprocal_differentiable) :
    QRHConsequences.v1.reciprocal_differentiable := h (7 / 8) hqrh

theorem classical_region (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hregion : ZeroFreeHalfPlane.v1.classical_region)
    (hdesc : ZeroFreeHeight.v1.classical_region_descends)
    (hRH : PlattTrudgian.v1.rh_up_to) : QRHConsequences.v1.classical_region := by
  have hhigh : ClassicalZeroFreeRegion (1 / 3) (exp 25) :=
    hregion (7 / 8) (1 / 3) (exp 25) (by norm_num) (by norm_num)
      (by linarith [add_one_le_exp (25 : ℝ)]) (by rw [log_exp]; norm_num) hqrh
  have hheight : exp (25 : ℝ) ≤ 3 * (10 : ℝ) ^ 12 := by
    have h3 : exp 1 ≤ (3 : ℝ) := by linarith [exp_one_lt_d9]
    have hp := pow_le_pow_left₀ (exp_pos 1).le h3 25
    rw [Real.exp_one_pow] at hp
    norm_num at hp ⊢
    linarith
  apply hdesc (1 / 3) (exp 7) (exp 25) (3 * (10 : ℝ) ^ 12) (by norm_num)
  · norm_num
  · exact exp_le_exp.mpr (by norm_num)
  · exact hheight
  · exact hRH
  · exact hhigh

theorem all_height_classical_region (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hregion : ZeroFreeHalfPlane.v1.classical_region)
    (hdesc : ZeroFreeHeight.v1.classical_region_descends)
    (hRH : PlattTrudgian.v1.rh_up_to) : QRHConsequences.v1.all_height_classical_region := by
  have hhigh : ClassicalZeroFreeRegion 3 (exp 3) :=
    hregion (7 / 8) 3 (exp 3) (by norm_num) (by norm_num)
      (by linarith [add_one_le_exp (3 : ℝ)]) (by rw [log_exp]; norm_num) hqrh
  have hheight : exp (3 : ℝ) ≤ 3 * (10 : ℝ) ^ 12 := by
    have h3 : exp 1 ≤ (3 : ℝ) := by linarith [exp_one_lt_d9]
    have hp := pow_le_pow_left₀ (exp_pos 1).le h3 3
    rw [Real.exp_one_pow] at hp
    norm_num at hp ⊢
    linarith
  apply hdesc 3 2 (exp 3) (3 * (10 : ℝ) ^ 12) (by norm_num)
  · calc
      _ < exp (log 2) := exp_lt_exp.mpr (by linarith [log_two_gt_d9])
      _ = 2 := exp_log (by norm_num)
  · linarith [add_one_le_exp (3 : ℝ)]
  · exact hheight
  · exact hRH
  · exact hhigh

end QRHConsequencesProof
