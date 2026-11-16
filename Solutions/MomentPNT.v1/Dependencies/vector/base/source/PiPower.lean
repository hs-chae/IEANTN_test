/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PowerBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Partial summation with a genuine power-saving envelope; no sampled extrapolation. -/
namespace QRHPiPower
open Real MeasureTheory Set IEANTN
open DudekPlattNumerics.Calculus

/-- Only the ordinary early-range bound and the supplied late theta envelope are used. -/
theorem error_integral_bound {A β X x : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hX : 2 ≤ X) (hXx : X ≤ x) (hθ : HasPowerLogBound Eθ A 2 β X) :
    |errorIntegral x| ≤ 4 * X + A / β * x ^ β := by
  have hx : 2 ≤ x := hX.trans hXx
  have hX0 : 0 < X := by linarith
  have hlog2 := DudekPlattNumerics.v4.Numerics.hlog2_proof
  have h1 : |∫ t in (2 : ℝ)..X, thetaError t / (t * log t ^ 2)| ≤ 4 * (X - 2) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (2 : ℝ)) (b := X) (C := (4 : ℝ))
      (f := fun t ↦ thetaError t / (t * log t ^ 2)) (fun t ht ↦ by
        rw [Set.uIoc_of_le hX] at ht
        simpa only [Real.norm_eq_abs] using abs_errorKernel_le_four hlog2 ht.1.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hX)] using hb
  have hi : IntervalIntegrable (fun t : ℝ ↦ A * t ^ (β - 1)) volume X x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β - 1)).const_mul A
  have hpoint : ∀ t ∈ Set.Ioc X x,
      ‖thetaError t / (t * log t ^ 2)‖ ≤ A * t ^ (β - 1) := by
    intro t ht
    have ht0 : 0 < t := hX0.trans ht.1
    have hl : 0 < log t := log_pos (by linarith [ht.1])
    have he := div_le_div_of_nonneg_right (hθ t ht.1.le) (pow_nonneg hl.le 2)
    have hid : |thetaError t / (t * log t ^ 2)| = Eθ t / log t ^ 2 := by
      rw [abs_div, abs_of_pos (mul_pos ht0 (pow_pos hl 2))]
      dsimp [thetaError, Eθ]
      ring
    rw [Real.norm_eq_abs, hid]
    calc
      _ ≤ (A * log t ^ 2 * t ^ (β - 1)) / log t ^ 2 := he
      _ = _ := by field_simp
  have h2 : |∫ t in X..x, thetaError t / (t * log t ^ 2)| ≤ A / β * x ^ β := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le hXx
      (Filter.Eventually.of_forall hpoint) hi
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < β - 1))] at hb
    rw [show β - 1 + 1 = β from by ring] at hb
    calc
      _ ≤ A * ((x ^ β - X ^ β) / β) := hb
      _ ≤ _ := by
        have hn : 0 ≤ A / β * X ^ β := by positivity
        calc
          _ = A / β * x ^ β - A / β * X ^ β := by ring
          _ ≤ _ := sub_le_self _ hn
  unfold errorIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_errorKernel (le_refl 2) hX)
    (intervalIntegrable_errorKernel hX hx)]
  exact (abs_add_le _ _).trans (by linarith [h1, h2])

/-- An explicit finite-base-point allowance accompanies the power term. -/
theorem pi_power_transfer {A β X x : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hX : 2 ≤ X) (hXx : X ≤ x) (hθ : HasPowerLogBound Eθ A 2 β X) :
    Eπ x ≤ (A * log x ^ 2 + A / β * log x) * x ^ (β - 1) +
      (4 * X + 3) * log x / x := by
  have hx : 2 ≤ x := hX.trans hXx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hb := error_integral_bound hA hβ hX hXx hθ
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc : 2 / log (2 : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hlog2]
    linarith [DudekPlattNumerics.v4.Numerics.hlog2_proof]
  have htri : |primeCounting x - Li x| ≤ |thetaError x| / log x + 3 +
      (4 * X + A / β * x ^ β) := by
    rw [FKS2Sol.piMinusLi_eq hx]
    have h1 := abs_add_le ((Chebyshev.theta x - x) / log x + 2 / log 2)
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2))
    have h2 := abs_add_le ((Chebyshev.theta x - x) / log x) (2 / log 2)
    rw [abs_div, abs_of_pos hl] at h2
    have h3 : |2 / log (2 : ℝ)| = 2 / log 2 := abs_of_nonneg (by positivity)
    rw [h3] at h2
    dsimp [thetaError, errorIntegral] at hb ⊢
    linarith
  have hscale : 0 ≤ log x / x := by positivity
  have hnorm := mul_le_mul_of_nonneg_left htri hscale
  have hpoint := hθ x hXx
  calc
    Eπ x = log x / x * |primeCounting x - Li x| := by unfold Eπ; field_simp
    _ ≤ log x / x * (|thetaError x| / log x + 3 + (4 * X + A / β * x ^ β)) := hnorm
    _ = Eθ x + (A / β * log x) * x ^ (β - 1) + (4 * X + 3) * log x / x := by
      rw [rpow_sub hx0, rpow_one]
      dsimp [Eθ, thetaError]
      field_simp
      ring
    _ ≤ _ := by linarith

/-- A concrete QRH instance keeps the same power and logarithmic exponent for pi. -/
theorem pi_bound (hθ : HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 300)) :
    HasPowerLogBound Eπ (1 / 280) 2 (7 / 8) (exp 400) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (400 : ℝ)).trans_le hx
  let L := log x
  have hL : 400 ≤ L := by
    have hh := log_le_log (exp_pos (400 : ℝ)) hx
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  have heq : exp L = x := exp_log hx0
  have hx300 : exp 300 ≤ exp L := exp_le_exp.mpr (by linarith)
  have hp := pi_power_transfer (A := (1 / 283 : ℝ)) (β := (7 / 8 : ℝ))
    (by norm_num) (by norm_num) (show 2 ≤ exp 300 by linarith [add_one_le_exp (300 : ℝ)])
    hx300 hθ
  rw [log_exp, rpow_def_of_pos (exp_pos L), log_exp] at hp
  have hid : exp (L * ((7 / 8 : ℝ) - 1)) = exp (-L / 8) := by congr 1; ring
  rw [hid] at hp
  have hearly : (4 * exp 300 + 3) * L / exp L ≤
      (7 / (2 : ℝ) ^ 50) * L * exp (-L / 8) := by
    have h300 : 1 ≤ exp (300 : ℝ) := by linarith [add_one_le_exp (300 : ℝ)]
    have hex : exp (300 - 7 * L / 8) ≤ 1 / (2 : ℝ) ^ 50 := by
      calc
        _ ≤ exp (-(50 : ℕ)) := exp_le_exp.mpr (by norm_num; linarith)
        _ ≤ _ := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 50
    calc
      _ ≤ (7 * exp 300) * L / exp L := by gcongr; linarith
      _ = 7 * L * exp (-L / 8) * exp (300 - 7 * L / 8) := by
        rw [mul_assoc (7 * L), ← exp_add]
        rw [show -L / 8 + (300 - 7 * L / 8) = 300 - L from by ring, exp_sub]
        ring
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_left hex
          (show 0 ≤ 7 * L * exp (-L / 8) by positivity)
        nlinarith [hmul]
  have hcoef : ((1 / 283 : ℝ) * L ^ 2 + (1 / 283) / (7 / 8) * L) +
      (7 / (2 : ℝ) ^ 50) * L ≤ (1 / 280 : ℝ) * L ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 400 by linarith)]
  have hfinal : Eπ (exp L) ≤ (1 / 280 : ℝ) * L ^ 2 * exp (-L / 8) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef (exp_pos (-L / 8)).le]
  rw [← heq, log_exp, rpow_def_of_pos (exp_pos L), log_exp, hid]
  exact hfinal

/-- Shape adapter for the existing FKS2 interface. The cutoff is explicit. -/
theorem classical_of_power {E : ℝ → ℝ} {A β L : ℝ} (hA : 0 ≤ A) (hβ : β < 1)
    (hL : 0 < L) (hcut : 2 ≤ (1 - β) * sqrt L)
    (hE : HasPowerLogBound E A 2 β (exp L)) :
    HasClassicalBound E A 2 2 1 (exp L) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hl : L ≤ log x := by
    have h := log_le_log (exp_pos L) hx
    simpa only [log_exp] using h
  have hlu : 0 ≤ log x := by linarith
  have hs : 2 ≤ (1 - β) * sqrt (log x) :=
    hcut.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hl) (sub_pos.mpr hβ).le)
  have hsq := sq_sqrt hlu
  have hmul := mul_le_mul_of_nonneg_right hs (sqrt_nonneg (log x))
  have hex : exp (log x * (β - 1)) ≤ exp (-2 * sqrt (log x)) := by
    apply exp_le_exp.mpr
    nlinarith
  have hp := hE x hx
  rw [rpow_def_of_pos hx0] at hp
  have hb := mul_le_mul_of_nonneg_left hex (show 0 ≤ A * log x ^ 2 by positivity)
  have ht := hp.trans hb
  simpa only [admissibleBound, div_one, rpow_two, ← sqrt_eq_rpow, neg_mul] using ht

/-- An actual instance of the existing FKS2 Theorem 3, with its exact boundary correction.
The coefficient is a defined real expression; it is not presented as a rounded numerical value. -/
theorem fks2_replay (h3 : FKS2.v2.theorem_3)
    (hθ : HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 300)) :
    HasClassicalBound Eπ
      ((1 + FKS2.v2.muAsymp (1 / 283) 2 2 1 (exp 300) (exp 400)) * (1 / 283))
      2 2 1 (exp 400) := by
  have hclass : HasClassicalBound Eθ (1 / 283) 2 2 1 (exp 300) :=
    classical_of_power (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 300), sqrt_nonneg (300 : ℝ)]) hθ
  apply h3 (1 / 283) 2 2 1 (exp 300) (exp 400)
  · norm_num
  · norm_num
  · linarith [add_one_le_exp (300 : ℝ)]
  · norm_num
  · norm_num
  · rw [log_exp]
    norm_num
  · norm_num
  · exact hclass

end QRHPiPower
