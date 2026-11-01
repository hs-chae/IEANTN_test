/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RefinedConsumer
import ThetaPi
import IntegralBounds
import CalculusAssembly
import Numerics
import Stieltjes
import IEANTN.Nodes.DudekPlatt.v3.Conclusions

namespace QRHPropagation

open Real MeasureTheory Set

open IEANTN DudekPlattNumerics.Calculus
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le hlog2_proof exp_one_pow)

/-- A small rational endpoint bound proved using the usual real exponential. -/
theorem exp_neg_nat_upper (n : ℕ) : exp (-(n : ℝ)) ≤ (10 / 27 : ℝ) ^ n := by
  have h27 : (27 / 10 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp : (27 / 10 : ℝ) ^ n ≤ exp (n : ℝ) := by
    rw [← Real.exp_one_pow n]
    exact pow_le_pow_left₀ (by norm_num) h27 n
  rw [exp_neg, ← one_div]
  calc
    1 / exp (n : ℝ) ≤ 1 / (27 / 10 : ℝ) ^ n :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = (10 / 27 : ℝ) ^ n := by rw [← one_div_pow]; norm_num

/-- Keep the pointwise power saving when applying the existing psi-to-theta interface. -/
theorem theta_exp_bound (hpsi : QRHCH2.v5.psi_refined_bound) {L : ℝ} (hL : 300 ≤ L) :
    |thetaError (exp L)| ≤ (1 / 283 : ℝ) * L ^ 2 * exp (7 * L / 8) := by
  have he : 0 < exp L := exp_pos L
  have hx1 : 1 ≤ exp L := by linarith [add_one_le_exp L]
  have hp := hpsi (exp L) (exp_le_exp.mpr hL)
  rw [log_exp, rpow_def_of_pos he, log_exp] at hp
  have hc := div_le_div_of_nonneg_right (Chebyshev.psi_sub_theta_le hx1) he.le
  rw [← exp_half, log_exp] at hc
  have hratio : exp (L / 2) / exp L = exp (-L / 2) := by
    rw [← exp_sub]; congr 1; ring
  have hc' : (Chebyshev.psi (exp L) - Chebyshev.theta (exp L)) / exp L ≤
      2 * L * exp (-L / 2) := by
    calc
      _ ≤ (2 * exp (L / 2) * L) / exp L := hc
      _ = 2 * L * (exp (L / 2) / exp L) := by ring
      _ = _ := by rw [hratio]
  have hsmall : exp (-3 * L / 8) ≤ 1 / 4 := by
    calc
      _ ≤ exp (-(2 : ℕ)) := exp_le_exp.mpr (by norm_num; linarith)
      _ ≤ _ := by
        have h := exp_neg_nat_le 2
        norm_num at h
        exact h
  have hsplit : exp (-L / 2) = exp (-L / 8) * exp (-3 * L / 8) := by
    rw [← exp_add]; congr 1; ring
  have hcoef : 2 * L * (1 / 4) ≤ (1 / 566 : ℝ) * L ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 283 by linarith)]
  have hcorrection : 2 * L * exp (-L / 2) ≤
      (1 / 566 : ℝ) * L ^ 2 * exp (-L / 8) := by
    rw [hsplit]
    calc
      _ ≤ 2 * L * (exp (-L / 8) * (1 / 4)) := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef (exp_pos (-L / 8)).le]
  have ht := FKS2Sol.Etheta_le_Epsi_add he
  have hb : Eθ (exp L) ≤ (1 / 283 : ℝ) * L ^ 2 * exp (-L / 8) := by
    have hex : exp (L * (-(1 : ℝ) / 8)) = exp (-L / 8) := by congr 1; ring
    rw [hex] at hp
    linarith
  have habs := (div_le_iff₀ he).mp hb
  change |thetaError (exp L)| ≤ _ at habs
  have hid : ((1 / 283 : ℝ) * L ^ 2 * exp (-L / 8)) * exp L =
      (1 / 283 : ℝ) * L ^ 2 * exp (7 * L / 8) := by
    rw [mul_assoc, ← exp_add]; congr 2; ring
  exact habs.trans_eq hid

/-- Whole-ray tail certificate: no finite grid or extrapolation is used. -/
theorem theta_log5_tail (hpsi : QRHCH2.v5.psi_refined_bound) {u : ℝ}
    (hu : exp 320 ≤ u) : |thetaError u| ≤ (1 / 100 : ℝ) * u / log u ^ 5 := by
  have hu0 : 0 < u := (exp_pos (320 : ℝ)).trans_le hu
  let L := log u
  have hL : 320 ≤ L := by
    have h := log_le_log (exp_pos (320 : ℝ)) hu
    simpa [L] using h
  have hLpos : 0 < L := by linarith
  have hb := theta_exp_bound hpsi (show 300 ≤ L by linarith)
  have hscaled : L ^ 5 / exp L * |thetaError (exp L)| ≤
      (1 / 283 : ℝ) * L ^ 7 * exp (-L / 8) := by
    calc
      _ ≤ L ^ 5 / exp L * ((1 / 283 : ℝ) * L ^ 2 * exp (7 * L / 8)) := by gcongr
      _ = _ := by
        rw [show 7 * L / 8 = L + (-L / 8) from by ring, exp_add]
        field_simp
  have hdec := poly_exp_decreasing 7 (L0 := (320 : ℝ)) (c := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hdec' : L ^ 7 * exp (-L / 8) ≤ (320 : ℝ) ^ 7 * exp (-40) := by
    convert hdec using 1 <;> congr 1 <;> ring
  have hep : exp (-40) ≤ (10 / 27 : ℝ) ^ 40 := by
    simpa using exp_neg_nat_upper 40
  have hvalue : (1 / 283 : ℝ) * L ^ 7 * exp (-L / 8) < (1 / 100 : ℝ) := by
    calc
      _ ≤ (1 / 283 : ℝ) * ((320 : ℝ) ^ 7 * exp (-40)) := by linarith [hdec']
      _ ≤ (1 / 283 : ℝ) * ((320 : ℝ) ^ 7 * (10 / 27 : ℝ) ^ 40) := by gcongr
      _ < _ := by norm_num
  have heq : exp L = u := exp_log hu0
  have hs := hscaled.trans hvalue.le
  rw [heq] at hs
  have hn : 0 < L ^ 5 / u := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ = L ^ 5 / u * |thetaError u| := by ring
    _ ≤ 1 / 100 := hs
    _ = (L ^ 5 / u) * ((1 / 100 : ℝ) * u / log u ^ 5) := by
      dsimp [L]
      field_simp [hu0.ne', show log u ≠ 0 from hLpos.ne']

/-- Stronger endpoint estimate at every point beyond the new expansion threshold. -/
theorem theta_point_small (hpsi : QRHCH2.v5.psi_refined_bound) {L : ℝ} (hL : 400 ≤ L) :
    L ^ 6 / exp L * |thetaError (exp L) / L| < 1 / 1000 := by
  have hLpos : 0 < L := by linarith
  have hb := theta_exp_bound hpsi (show 300 ≤ L by linarith)
  have hscaled : L ^ 5 / exp L * |thetaError (exp L)| ≤
      (1 / 283 : ℝ) * L ^ 7 * exp (-L / 8) := by
    calc
      _ ≤ L ^ 5 / exp L * ((1 / 283 : ℝ) * L ^ 2 * exp (7 * L / 8)) := by gcongr
      _ = _ := by
        rw [show 7 * L / 8 = L + (-L / 8) from by ring, exp_add]
        field_simp
  have hdec := poly_exp_decreasing 7 (L0 := (400 : ℝ)) (c := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hdec' : L ^ 7 * exp (-L / 8) ≤ (400 : ℝ) ^ 7 * exp (-50) := by
    convert hdec using 1 <;> congr 1 <;> ring
  have hep : exp (-50) ≤ (10 / 27 : ℝ) ^ 50 := by
    simpa using exp_neg_nat_upper 50
  have hvalue : (1 / 283 : ℝ) * L ^ 7 * exp (-L / 8) < (1 / 1000 : ℝ) := by
    calc
      _ ≤ (1 / 283 : ℝ) * ((400 : ℝ) ^ 7 * exp (-50)) := by linarith [hdec']
      _ ≤ (1 / 283 : ℝ) * ((400 : ℝ) ^ 7 * (10 / 27 : ℝ) ^ 50) := by gcongr
      _ < _ := by norm_num
  have hid : L ^ 6 / exp L * |thetaError (exp L) / L| =
      L ^ 5 / exp L * |thetaError (exp L)| := by
    rw [abs_div, abs_of_pos hLpos]
    field_simp
  rw [hid]
  exact hscaled.trans_lt hvalue

/-- The early/late integral split is at exp(4L/5). -/
theorem scalar_error {L : ℝ} (hL : 400 ≤ L) :
    4 * L ^ 6 * exp (-L / 5) + (1 / 100 : ℝ) / ((4 / 5 : ℝ) ^ 7 * L) <
      1 / 1000 := by
  have hL0 : (0 : ℝ) < 400 := by norm_num
  have hLpos : (0 : ℝ) < L := by linarith
  have h1 : L ^ 6 * Real.exp (-(1 / 5 : ℝ) * L) ≤
      (400 : ℝ) ^ 6 * Real.exp (-(1 / 5 : ℝ) * 400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have h4exp : Real.exp (-(80:ℕ) : ℝ) ≤ 1 / 2 ^ (80:ℕ) := exp_neg_nat_le 80
  have hearly : 4 * L ^ 6 * Real.exp (-L / 5) ≤ 4 * (400 : ℝ) ^ 6 / 2 ^ 80 := by
    have e1 : Real.exp (-L / 5) = Real.exp (-(1 / 5 : ℝ) * L) := by congr 1; ring
    have e2 : Real.exp (-(1 / 5 : ℝ) * (400:ℝ)) = Real.exp (-(80:ℕ) : ℝ) := by
      congr 1; push_cast; ring
    calc 4 * L ^ 6 * Real.exp (-L / 5)
        = 4 * (L ^ 6 * Real.exp (-(1 / 5 : ℝ) * L)) := by rw [e1]; ring
      _ ≤ 4 * ((400:ℝ) ^ 6 * Real.exp (-(1 / 5 : ℝ) * 400)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4 * (400:ℝ) ^ 6 * Real.exp (-(80:ℕ) : ℝ) := by rw [e2]; ring
      _ ≤ 4 * (400:ℝ) ^ 6 * (1 / 2 ^ (80:ℕ)) :=
          mul_le_mul_of_nonneg_left h4exp (by positivity)
      _ = 4 * (400 : ℝ) ^ 6 / 2 ^ 80 := by ring
  have hlate : (1 / 100) / ((4 / 5 : ℝ) ^ 7 * L) ≤ (1 / 100) / ((4 / 5 : ℝ) ^ 7 * 400) := by
    gcongr
  have hfin : (4 * (400:ℝ) ^ 6 / 2 ^ 80 + (1 / 100) / ((4 / 5 : ℝ) ^ 7 * 400) : ℝ) < 1 / 1000 := by
    norm_num
  linarith [hearly, hlate, hfin]

/-- The existing finite integration-by-parts remainder bound at a much smaller threshold. -/
theorem scalar_I7 {L : ℝ} (hL : 400 ≤ L) :
    720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2)) < 10 := by
  have hL0 : (0 : ℝ) < 400 := by norm_num
  have hLpos : (0:ℝ) < L := by linarith
  have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
  have h1 : (1:ℝ) / L ≤ 1 / 400 := one_div_le_one_div_of_le hL0 hL
  have h4 : (256:ℝ) / L ^ 2 ≤ 256 / 400 ^ 2 := by gcongr
  have hpos : (0:ℝ) ≤ 1 / Real.log 2 := by positivity
  have hub := DudekPlattNumerics.v4.Numerics.inv_log2_lt
  have h3 : (1:ℝ) / Real.log 2 ^ 8 ≤ (3/2:ℝ) ^ 8 := by
    rw [show (1:ℝ) / Real.log 2 ^ 8 = (1/Real.log 2)^8 by rw [div_pow]; ring]
    exact pow_le_pow_left₀ hpos hub.le 8
  have hb1 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) ≤ (400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have hb2 : Real.exp (-(1/2:ℝ) * (400:ℝ)) ≤ 1 / 2 ^ (120:ℕ) := by
    have e : (-(1/2:ℝ) * (400:ℝ)) = -(200:ℕ) := by push_cast; ring
    rw [e]
    calc Real.exp (-(200:ℕ) : ℝ) ≤ Real.exp (-(120:ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr; norm_num
      _ ≤ 1 / 2 ^ (120:ℕ) := exp_neg_nat_le 120
  have hb3 : (400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 400) ≤ (400:ℝ) ^ 6 / 2 ^ (120:ℕ) := by
    calc (400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 400) ≤ (400:ℝ) ^ 6 * (1 / 2 ^ (120:ℕ)) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = (400:ℝ) ^ 6 / 2 ^ (120:ℕ) := by ring
  have hb4 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) ≤ (400:ℝ) ^ 6 / 2 ^ (120:ℕ) := le_trans hb1 hb3
  have hb6 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) * ((1:ℝ) / Real.log 2 ^ 8) ≤
      ((400:ℝ) ^ 6 / 2 ^ (120:ℕ)) * (3/2:ℝ) ^ 8 :=
    mul_le_mul hb4 h3 (by positivity) (by positivity)
  have hfinnum : (((400:ℝ) ^ 6 / 2 ^ (120:ℕ)) * (3/2:ℝ) ^ 8 : ℝ) < 1 / 10 ^ 9 := by norm_num
  have hnegl : L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8 ≤ 1 / 10 ^ 9 := by
    have e1 : Real.exp (-L / 2) = Real.exp (-(1/2:ℝ) * L) := by congr 1; ring
    rw [e1, div_eq_mul_one_div]
    linarith [hb6, hfinnum]
  have heq : 720 * (1 / L + 7 * (L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8 + 256 / L ^ 2)) =
      720 * (1/L) + 720*7 * (L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8) + 720*7*(256 / L ^ 2) := by
    ring
  rw [heq]
  have hcalc : (720:ℝ) * (1/400) + 720*7*(1/10^9) + 720*7*(256/400^2) < 10 := by norm_num
  nlinarith [h1, h4, hnegl, hcalc]

theorem scalar_A {L : ℝ} (hL : 400 ≤ L) :
    2 * DudekPlattNumerics.Calculus.A * L ^ 6 * exp (-L) < 1 / 1000 := by
  have hL0 : (0 : ℝ) < 400 := by norm_num
  have h1 : L ^ 6 * Real.exp (-(1:ℝ) * L) ≤ (400:ℝ) ^ 6 * Real.exp (-(1:ℝ) * 400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have he : Real.exp (-(1:ℝ) * L) = Real.exp (-L) := by congr 1; ring
  have he2 : Real.exp (-(1:ℝ) * (400:ℝ)) = Real.exp (-(400:ℕ) : ℝ) := by
    congr 1; push_cast; ring
  rw [he, he2] at h1
  have hAnn : (0:ℝ) ≤ A := by
    have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
    unfold A; positivity
  have hAb : DudekPlattNumerics.Calculus.A < 1600 :=
    DudekPlattNumerics.v4.Numerics.A_lt
  -- avoid the huge-exponent evaluator threshold: reduce -400 to a safely negligible -200 first
  have hexp400 : Real.exp (-(400:ℕ) : ℝ) ≤ 1 / 2 ^ (200:ℕ) := by
    calc Real.exp (-(400:ℕ) : ℝ) ≤ Real.exp (-(200:ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr; norm_num
      _ ≤ 1 / 2 ^ (200:ℕ) := exp_neg_nat_le 200
  have hstep : 2 * A * (L ^ 6 * Real.exp (-L)) ≤
      2 * 1600 * ((400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) := by
    calc 2 * A * (L ^ 6 * Real.exp (-L))
        ≤ 2 * A * ((400:ℝ) ^ 6 * Real.exp (-(400:ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * 1600 * ((400:ℝ) ^ 6 * Real.exp (-(400:ℕ) : ℝ)) := by gcongr
      _ ≤ 2 * 1600 * ((400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) := by gcongr
  have hfin : (2 * 1600 * ((400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) : ℝ) < 1 / 1000 := by
    norm_num
  nlinarith [hstep, hfin]

/-- A split parameter is exposed so later upstream bounds change certificates locally. -/
theorem normalize_error {L K a : ℝ} (hL : 0 < L) (ha : a ≠ 0) :
    L ^ 6 / exp L * (4 * exp (a * L) + K * exp L / log (exp (a * L)) ^ 7) =
      4 * L ^ 6 * exp (-(1 - a) * L) + K / (a ^ 7 * L) := by
  have hL0 := ne_of_gt hL
  have he0 := ne_of_gt (exp_pos L)
  have hr : exp (a * L) / exp L = exp (-(1 - a) * L) := by
    rw [← exp_sub]; congr 1; ring
  rw [log_exp]
  calc
    _ = 4 * L ^ 6 * (exp (a * L) / exp L) + K / (a ^ 7 * L) := by field_simp
    _ = _ := by rw [hr]

theorem normalized_errorIntegral (hpsi : QRHCH2.v5.psi_refined_bound)
    {L : ℝ} (hL : 400 ≤ L) : L ^ 6 / exp L * |errorIntegral (exp L)| < 1 / 1000 := by
  have hLpos : 0 < L := by linarith
  have hs : 2 ≤ exp ((4 / 5 : ℝ) * L) := by linarith [add_one_le_exp ((4 / 5 : ℝ) * L)]
  have hsx : exp ((4 / 5 : ℝ) * L) ≤ exp L := exp_le_exp.mpr (by linarith)
  have hb := errorIntegral_split_bound hlog2_proof hs hsx (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (fun t ht ↦ theta_log5_tail hpsi ((exp_le_exp.mpr (by linarith)).trans ht.1))
  calc
    _ ≤ L ^ 6 / exp L * (4 * exp ((4 / 5 : ℝ) * L) +
        (1 / 100 : ℝ) * exp L / log (exp ((4 / 5 : ℝ) * L)) ^ 7) := by gcongr
    _ = 4 * L ^ 6 * exp (-L / 5) + (1 / 100 : ℝ) / ((4 / 5 : ℝ) ^ 7 * L) := by
      rw [normalize_error hLpos (by norm_num : (4 / 5 : ℝ) ≠ 0)]
      congr 2
      ring
    _ < _ := scalar_error hL

/-- New coefficients from the existing exact prime-counting expansion and integral bounds. -/
theorem pi_coefficients (hpsi : QRHCH2.v5.psi_refined_bound) {L : ℝ} (hL : 400 ≤ L) :
    119 < L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) ∧
      L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) < 131 := by
  have hLpos : 0 < L := by linarith
  have hL0 := hLpos.ne'
  have he0 := (exp_pos L).ne'
  have hx : 2 ≤ exp L := by linarith [add_one_le_exp L]
  have hq : 0 < L ^ 6 / exp L := by positivity
  have hp : |L ^ 6 / exp L * (thetaError (exp L) / L)| < 1 / 1000 := by
    rw [abs_mul, abs_of_pos hq]
    exact theta_point_small hpsi hL
  have he : |L ^ 6 / exp L * errorIntegral (exp L)| < 1 / 1000 := by
    rw [abs_mul, abs_of_pos hq]
    exact normalized_errorIntegral hpsi hL
  have hi : L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) < 10 := by
    have hb := I7_bound (show 4 ≤ exp L by linarith [add_one_le_exp L])
    calc
      _ ≤ L ^ 6 / exp L * (720 * (exp L / log (exp L) ^ 7 +
          7 * (sqrt (exp L) / log 2 ^ 8 + 256 * exp L / log (exp L) ^ 8))) := by gcongr
      _ = 720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2)) := by
        rw [DudekPlattNumerics.Calculus.normalize_I7_majorant hLpos]
      _ < _ := scalar_I7 hL
  have hi0 : 0 ≤ L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) := by
    exact mul_nonneg hq.le (mul_nonneg (by norm_num) (logIntegral_nonneg 7 hx))
  have ha : L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) < 1 / 1000 := by
    convert scalar_A hL using 1
    rw [exp_neg]
    ring
  have ha0 : 0 ≤ L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) := by
    have : 0 ≤ DudekPlattNumerics.Calculus.A := by
      unfold DudekPlattNumerics.Calculus.A
      have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
      positivity
    positivity
  have hn : L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) =
      120 + L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) -
        L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) +
        L ^ 6 / exp L * (thetaError (exp L) / L) +
        L ^ 6 / exp L * errorIntegral (exp L) := by
    rw [primeCounting_expansion hx, log_exp]
    field_simp
    ring
  rw [hn]
  rcases abs_lt.mp hp with ⟨hp1, hp2⟩
  rcases abs_lt.mp he with ⟨he1, he2⟩
  constructor <;> linarith

/-- The two-sided estimate is for actual pi, with all endpoints and the real variable retained. -/
theorem pi_expansion (hpsi : QRHCH2.v5.psi_refined_bound) {x : ℝ} (hx : exp 400 < x) :
    DudekPlatt.v3.mainTerm x + 119 * x / log x ^ 6 < primeCounting x ∧
      primeCounting x < DudekPlatt.v3.mainTerm x + 131 * x / log x ^ 6 := by
  have hx0 : 0 < x := (exp_pos (400 : ℝ)).trans hx
  have hL : 400 ≤ log x := by
    have h := log_lt_log (exp_pos (400 : ℝ)) hx
    simpa using h.le
  have hl : 0 < log x := by linarith
  have hq : 0 < log x ^ 6 / x := by positivity
  have hcoef := pi_coefficients hpsi hL
  rw [exp_log hx0] at hcoef
  have hinv : (log x ^ 6 / x) * (x / log x ^ 6) = 1 := by field_simp
  change S5 x + 119 * x / log x ^ 6 < primeCounting x ∧
    primeCounting x < S5 x + 131 * x / log x ^ 6
  have h1 : 119 / (log x ^ 6 / x) < primeCounting x - S5 x :=
    (div_lt_iff₀ hq).mpr (by simpa [mul_comm] using hcoef.1)
  have h2 : primeCounting x - S5 x < 131 / (log x ^ 6 / x) :=
    (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using hcoef.2)
  have hid (c : ℝ) : c / (log x ^ 6 / x) = c * x / log x ^ 6 := by
    field_simp
  rw [hid] at h1 h2
  constructor <;> linarith

/-- The repaired existing Dudek--Platt criterion is reused without alteration. -/
theorem ramanujan (hpsi : QRHCH2.v5.psi_refined_bound) (hDP : DudekPlatt.v3.criterion) :
    ∀ x : ℝ, exp 401 < x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  apply hDP 119 131 (exp 400) (exp 401)
  · linarith [add_one_le_exp (400 : ℝ)]
  · intro x hx
    exact (pi_expansion hpsi hx).1
  · intro x hx
    have heq : exp 1 * exp 400 = exp (401 : ℝ) := by rw [← exp_add]; norm_num
    rw [heq] at hx
    exact (pi_expansion hpsi ((exp_le_exp.mpr (by norm_num : (400 : ℝ) ≤ 401)).trans_lt hx)).2
  · rw [← exp_add]; norm_num
  · intro x hx
    have hl : 400 ≤ log x := by
      have h := log_lt_log (exp_pos (401 : ℝ)) hx
      rw [log_exp] at h
      linarith
    have hl0 : 0 < log x := by linarith
    have h1 : (394 : ℝ) / log x ≤ 394 / 400 := by gcongr
    have h2 : (812 : ℝ) / log x ^ 2 ≤ 812 / 400 ^ 2 := by gcongr
    have h3 : (2148 : ℝ) / log x ^ 3 ≤ 2148 / 400 ^ 3 := by gcongr
    have h4 : (6288 : ℝ) / log x ^ 4 ≤ 6288 / 400 ^ 4 := by gcongr
    have h5 : (17161 : ℝ) / log x ^ 5 ≤ 17161 / 400 ^ 5 := by gcongr
    have hup : DudekPlatt.v3.εUpper 131 x < 336 := by
      unfold DudekPlatt.v3.εUpper
      norm_num at h1 h2 h3 h4 h5 ⊢
      linarith
    have hpos : 0 ≤ 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 +
        97 / log x ^ 4 + 30 / log x ^ 5 + 8 / log x ^ 6 := by positivity
    have hlo : 325 ≤ DudekPlatt.v3.εLower 119 (exp 400) x := by
      norm_num [DudekPlatt.v3.εLower, DudekPlatt.v3.εPos]
      linarith
    linarith

end QRHPropagation
