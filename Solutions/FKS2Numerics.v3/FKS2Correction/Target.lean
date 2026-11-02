/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2SumBridge.NodeBound
import IEANTN.Nodes.FKS2Numerics.v3.Conclusions

namespace FKS2Correction
open Real

noncomputable def normalizedTarget (A L : ℝ) : ℝ :=
  (1 / A) * sqrt (5.5666305 / L) ^ 3 * exp (2 * sqrt (L / 5.5666305)) *
    ((1 + 1.93378e-8) * L * exp (-L / 2) +
      ((1 + 1.93378e-8) * max FKS2Scalar.sum1 FKS2Scalar.sum2) * L * exp (-2 * L / 3))

theorem anchor_coefficient : BKLNW.v1.a₂ 30 =
    (1 + 1.93378e-8) * max FKS2Scalar.sum1 FKS2Scalar.sum2 := by
  unfold BKLNW.v1.a₂
  rw [FKS2Scalar.floor30]
  rw [show (43 + 1 : ℕ) = 44 by rfl]
  rw [FKS2Scalar.f_exp30, FKS2Scalar.f_pow44]

theorem original_specialization :
    FKS2Numerics.v3.nuStar 121.096 30 = FKS2Numerics.v1.nuAsympE30 := by
  simp only [FKS2Numerics.v3.nuStar, FKS2.v2.nuAsymp, Real.log_exp,
    FKS2Numerics.v1.nuAsympE30]

theorem target_normalization {A L : ℝ} (hL : 0 < L) :
    FKS2Numerics.v3.nuStar A L = normalizedTarget A L := by
  have h1 : exp L ^ (-(1 : ℝ) / 2) = exp (-L / 2) := by
    rw [rpow_def_of_pos (exp_pos L), log_exp]
    congr 1
    ring
  have h2 : exp L ^ (-(2 : ℝ) / 3) = exp (-2 * L / 3) := by
    rw [rpow_def_of_pos (exp_pos L), log_exp]
    congr 1
    ring
  unfold FKS2Numerics.v3.nuStar FKS2.v2.nuAsymp normalizedTarget
  rw [log_exp, anchor_coefficient, rpow_div_two_eq_sqrt _ (by positivity), h1, h2]
  norm_num

theorem calibration_provider : FKS2Numerics.v3.calibration_bound := by
  change FKS2Numerics.v3.nuStar 121.096 30 ≤ (6.339e-7 : ℝ)
  rw [original_specialization]
  have h := FKS2SumBridge.corrected_node_multiplier
  change FKS2Numerics.v1.nuAsympE30 ≤ IEANTN.margin 0 * (6.339e-7 : ℝ) at h
  simpa [IEANTN.margin] using h

end FKS2Correction
