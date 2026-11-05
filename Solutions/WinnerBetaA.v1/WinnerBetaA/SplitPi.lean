/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityApplications
import WinnerBetaA.Source

namespace WinnerBetaA
open Real IEANTN
open DudekPlattNumerics.Calculus

/-- Partial summation keeps the actual theta value at x, allowing a sharper later profile. -/
theorem pi_log2_split {c β A x : ℝ} (hc : 0 ≤ c) (hβ : 0 < β)
    (hA : 2 ≤ A) (hAx : A ≤ x) (hθ : HasPowerLogBound Eθ c 2 β A) :
    Eπ x ≤ Eθ x + c / β * log x * x ^ (β - 1) + (4 * A + 3) * log x / x := by
  have hx : 2 ≤ x := hA.trans hAx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp := QRHDensityApplications.pi_from_error_integral hx
  have hi := QRHPiPower.error_integral_bound hc hβ hA hAx hθ
  have hm := mul_le_mul_of_nonneg_left
    (show 3 + |errorIntegral x| ≤ 3 + (4 * A + c / β * x ^ β) by linarith)
    (show 0 ≤ log x / x by positivity)
  calc
    Eπ x ≤ Eθ x + log x / x * (3 + (4 * A + c / β * x ^ β)) := by linarith
    _ = _ := by
      rw [rpow_sub hx0, rpow_one]
      field_simp
      ring

/-- Joint coefficient/range adapter: numerical point and integral profiles may differ.
The exponential tail certificate is independent from the numerical coefficient provider. -/
theorem pi_log2_two_profiles {cA cB β a b δ cπ : ℝ}
    (hcA : 0 ≤ cA) (hβ : 0 < β) (ha : 1 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (htail : exp (a - β * b) ≤ δ)
    (hcoef : cB + (cA / β + 7 * δ) / b ≤ cπ)
    (hθA : HasPowerLogBound Eθ cA 2 β (exp a))
    (hθB : HasPowerLogBound Eθ cB 2 β (exp b)) :
    HasPowerLogBound Eπ cπ 2 β (exp b) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos b).trans_le hx
  let L := log x
  have hL : b ≤ L := by
    have hh := log_le_log (exp_pos b) hx
    simpa [L] using hh
  have hLp : 0 < L := hb.trans_le hL
  have hLn : L ≠ 0 := hLp.ne'
  have heq : exp L = x := exp_log hx0
  have hA : 2 ≤ exp a := by linarith [add_one_le_exp a]
  have hAx : exp a ≤ exp L := exp_le_exp.mpr (hab.trans hL)
  have hp := pi_log2_split hcA hβ hA hAx hθA
  have ht := hθB (exp L) (exp_le_exp.mpr hL)
  rw [log_exp, rpow_def_of_pos (exp_pos L), log_exp] at hp ht
  have hδ : 0 ≤ δ := (exp_pos _).le.trans htail
  have htailL : exp (a - β * L) ≤ δ := by
    exact (exp_le_exp.mpr (by nlinarith [hL])).trans htail
  have hea : 1 ≤ exp a := by linarith [add_one_le_exp a]
  have hearly : (4 * exp a + 3) * L / exp L ≤
      7 * δ * L * exp (L * (β - 1)) := by
    calc
      _ ≤ (7 * exp a) * L / exp L := by gcongr; linarith
      _ = 7 * L * exp (L * (β - 1)) * exp (a - β * L) := by
        rw [mul_assoc (7 * L), ← exp_add]
        rw [show L * (β - 1) + (a - β * L) = a - L by ring, exp_sub]
        ring
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left htailL
          (show 0 ≤ 7 * L * exp (L * (β - 1)) by positivity)
        nlinarith
  have hn : 0 ≤ cA / β + 7 * δ := by positivity
  have hcoefL : cB + (cA / β + 7 * δ) / L ≤ cπ := by
    have hd : (cA / β + 7 * δ) / L ≤ (cA / β + 7 * δ) / b := by gcongr
    linarith
  have hpoly : cB * L^2 + (cA / β + 7 * δ) * L ≤ cπ * L^2 := by
    have hm := mul_le_mul_of_nonneg_right hcoefL (sq_nonneg L)
    have hid : (cB + (cA / β + 7 * δ) / L) * L^2 =
        cB * L^2 + (cA / β + 7 * δ) * L := by field_simp
    rwa [hid] at hm
  have hfinal : Eπ (exp L) ≤ cπ * L^2 * exp (L * (β - 1)) := by
    nlinarith [mul_le_mul_of_nonneg_right hpoly (exp_pos (L * (β - 1))).le]
  rw [← heq, log_exp, rpow_def_of_pos (exp_pos L), log_exp]
  exact hfinal

/-- Uniform slack used by all supplied numerical profiles, independent of QRH. -/
theorem tiny_theta_slack {β L₀ : ℝ} (hβ : (7/8 : ℝ) ≤ β) (hL₀ : 200 ≤ L₀) :
    2 * L₀ * exp (-(β - 1 / 2) * L₀) ≤ (1 / 1000000000000 : ℝ) := by
  have hLp : 0 < L₀ := by linarith
  have he : exp (-(β - 1 / 2) * L₀) ≤ exp (-(3/8 : ℝ)*L₀) := by
    apply exp_le_exp.mpr
    nlinarith
  have hd := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0 := (200 : ℝ)) (c := (3/8 : ℝ)) (by norm_num) (by norm_num) hL₀
  have h75 := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 75
  have hd' : L₀ * exp (-(3/8 : ℝ)*L₀) ≤ 200 * exp (-75) := by
    convert hd using 1 <;> congr 1 <;> ring
  norm_num only [pow_one, Nat.cast_ofNat] at hd' h75
  have hs : 2 * L₀ * exp (-(β - 1 / 2) * L₀) ≤ 400 / (2 : ℝ)^75 := by
    calc
      _ ≤ 2 * L₀ * exp (-(3/8 : ℝ)*L₀) :=
        mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * L₀ by positivity)
      _ ≤ 400 * exp (-75) := by linarith [hd']
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left h75 (show (0 : ℝ) ≤ 400 by norm_num)
        norm_num at hm ⊢
        exact hm
  exact hs.trans (by norm_num)

theorem theta_from_large_psi_log2 {C β L₀ : ℝ} (hβ : (7/8 : ℝ) ≤ β) (hL₀ : 200 ≤ L₀)
    (hψ : HasPowerLogBound Eψ C 2 β (exp L₀)) :
    HasPowerLogBound Eθ (C + 1 / 1000000000000) 2 β (exp L₀) := by
  apply theta_from_psi_log2 (by linarith)
  · nlinarith
  · exact tiny_theta_slack hβ hL₀
  · exact hψ

#print axioms pi_log2_two_profiles
end WinnerBetaA
