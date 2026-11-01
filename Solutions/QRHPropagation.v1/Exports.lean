/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PiPower

/-! Concrete consumers and quantified comparisons of the resulting bounds. -/
namespace QRHExports
open Real IEANTN

theorem theta_power (hpsi : QRHCH2.v5.psi_refined_bound) :
    HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 300) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  let L := log x
  have hL : 300 ≤ L := by
    have hh := log_le_log (exp_pos (300 : ℝ)) hx
    simpa [L] using hh
  have heq : exp L = x := exp_log hx0
  have hb := QRHPropagation.theta_exp_bound hpsi hL
  rw [← heq, log_exp, rpow_def_of_pos (exp_pos L), log_exp]
  change |DudekPlattNumerics.Calculus.thetaError (exp L)| / exp L ≤ _
  calc
    _ ≤ ((1 / 283 : ℝ) * L ^ 2 * exp (7 * L / 8)) / exp L := by gcongr
    _ = _ := by
      rw [show 7 * L / 8 = L + L * ((7 / 8 : ℝ) - 1) from by ring, exp_add]
      field_simp

theorem moving_intervals
    (hθ : HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 300))
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x ≥ exp 320, HasPrimeInInterval x ((4 / 283 : ℝ) * log x ^ 2 * x ^ ((7 : ℝ) / 8)) := by
  have ht : HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 320) :=
    fun x hx ↦ hθ x ((exp_le_exp.mpr (by norm_num : (300 : ℝ) ≤ 320)).trans hx)
  have hsmall : (1 / 283 : ℝ) * (320 : ℝ) ^ 2 * exp (-(1 - 7 / 8) * 320) ≤ 1 / 4 := by
    have he := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 40
    norm_num at he ⊢
    nlinarith
  have hp := QRHPowerBounds.intervals_of_power hcrit (by norm_num : (0 : ℝ) < 1 / 283)
    (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : (0 : ℝ) < 320) (k := 2)
    (by norm_num) hsmall ht
  intro x hx
  convert hp x hx using 1 <;> ring

/-- A comparison certificate, not an extra QRH propagation claim. -/
theorem width_improves {x : ℝ} (hx : exp 320 ≤ x) :
    (4 / 283 : ℝ) * log x ^ 2 * x ^ ((7 : ℝ) / 8) ≤ x / 120000000000000 := by
  have hx0 : 0 < x := (exp_pos (320 : ℝ)).trans_le hx
  have hn := QRHPowerBounds.numerical_of_power (E := fun y ↦
      (4 / 283 : ℝ) * log y ^ 2 * y ^ ((7 / 8 : ℝ) - 1))
    (by norm_num : (0 : ℝ) ≤ 4 / 283) (by norm_num : (7 / 8 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 320) (k := 2) (by norm_num)
    (fun _ _ ↦ le_rfl)
  have he := QRHPropagation.exp_neg_nat_upper 40
  have hc : (4 / 283 : ℝ) * 320 ^ 2 * exp (-40) ≤ 1 / 120000000000000 := by
    calc
      _ ≤ (4 / 283 : ℝ) * 320 ^ 2 * (10 / 27 : ℝ) ^ 40 :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := by norm_num
  have hc' : (4 / 283 : ℝ) * (320 : ℝ) ^ 2 *
      exp (-(1 - 7 / 8) * 320) ≤ 1 / 120000000000000 := by
    convert hc using 1 <;> norm_num
  have hb := (hn x hx).trans hc' 
  have hm := mul_le_mul_of_nonneg_left hb hx0.le
  have hid : x * ((4 / 283 : ℝ) * log x ^ 2 * x ^ ((7 / 8 : ℝ) - 1)) =
      (4 / 283 : ℝ) * log x ^ 2 * x ^ ((7 : ℝ) / 8) := by
    rw [rpow_sub hx0, rpow_one]
    field_simp
  rw [hid] at hm
  simpa only [mul_one_div] using hm

end QRHExports
