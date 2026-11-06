/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Envelope
namespace E1FrozenN
open CH2QRH
/-! Ordinary analytic remainder sharpening from the inherited exp_one bound.
The quantified exp_nat_bounds theorem is used, not a new numerical provider. -/
theorem remainder_330 {x : ℝ} (hx0 : 0 < x) (hL330 : 330 ≤ Real.log x) :
    finiteRemainder (Real.exp ((1/3:ℝ) * Real.log x) + 1 / 2) x * x ^ ((1 : ℝ) / 8) ≤
      (1 : ℝ) / 10 ^ (28 : ℕ) := by
  have hL : 64≤Real.log x := by linarith
  have hk : (1/3:ℝ)≤7/10 := by norm_num
  have hsep : 34≤(1/3:ℝ)*Real.log x-Real.log x/8 := by linarith
  let T := Real.exp ((1/3:ℝ) * Real.log x) + 1 / 2
  obtain ⟨hTlo, _, hxlo, hlogT, hTdiv, _⟩ := density_height_parameters hx0 hL hk hsep
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hscaled := density_scaled_remainder
    (by dsimp [T]; norm_num at hTlo ⊢; linarith : 1000000 ≤ T) hxlo hL hlogT hTdiv
  have hratio : x ^ ((1 : ℝ) / 8) / T ≤ Real.exp (-68) := by
    calc
      _ ≤ x ^ ((1 : ℝ) / 8) / Real.exp ((1/3:ℝ) * Real.log x) := by dsimp [T]; gcongr; linarith
      _ = Real.exp (Real.log x / 8 - (1/3:ℝ) * Real.log x) := by
        rw [Real.rpow_def_of_pos hx0, Real.exp_sub]; congr 2; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hT0).mpr hscaled)
    (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 8)).le
  have h68 := (CH2Section7A.exp_nat_bounds 68).1
  have he : (3.2 : ℝ) * Real.exp (-68) ≤ (1 : ℝ) / 10 ^ (28 : ℕ) := by
    rw [Real.exp_neg, ← one_div, mul_one_div, div_le_iff₀ (Real.exp_pos (68 : ℝ))]
    norm_num at h68 ⊢; linarith
  have hr := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 3.2)
  change finiteRemainder T x * x ^ ((1 : ℝ) / 8) ≤ _
  convert (hmul.trans (by convert hr.trans he using 1 <;> ring)) using 1

#print axioms remainder_330
end E1FrozenN
