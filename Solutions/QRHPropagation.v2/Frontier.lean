/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityApplications

/-! Phase2 concrete quantitative transfers. Draft obligations are not completion evidence. -/
namespace QRHPhase2
open Real IEANTN
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing)

theorem theta_from_psi {L₀ C : ℝ} (hL₀ : 64 ≤ L₀)
    (hpsi : HasPowerLogBound Eψ C 0 (7 / 8) (exp L₀)) :
    HasPowerLogBound Eθ (C + 1 / 100000) 0 (7 / 8) (exp L₀) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L₀).trans_le hx
  let L := log x
  have hL : L₀ ≤ L := by
    have hh := log_le_log (exp_pos L₀) hx
    simpa [L] using hh
  have h64 : 64 ≤ L := hL₀.trans hL
  have hLpos : 0 < L := by linarith
  have heq : exp L = x := exp_log hx0
  have hψ := hpsi (exp L) (exp_le_exp.mpr hL)
  simp only [pow_zero, mul_one] at hψ
  rw [rpow_def_of_pos (exp_pos L), log_exp] at hψ
  have he1 : L * ((7 / 8 : ℝ) - 1) = -L / 8 := by ring
  rw [he1] at hψ
  have hc := div_le_div_of_nonneg_right
    (Chebyshev.psi_sub_theta_le (show 1 ≤ exp L by linarith [add_one_le_exp L]))
    (exp_pos L).le
  rw [← exp_half, log_exp] at hc
  have hratio : exp (L / 2) / exp L = exp (-L / 2) := by
    rw [← exp_sub]; congr 1; ring
  have hc' : (Chebyshev.psi (exp L) - Chebyshev.theta (exp L)) / exp L ≤
      2 * L * exp (-L / 2) := by
    calc
      _ ≤ (2 * exp (L / 2) * L) / exp L := hc
      _ = 2 * L * (exp (L / 2) / exp L) := by ring
      _ = _ := by rw [hratio]
  have hd := poly_exp_decreasing 1 (L0 := (64 : ℝ)) (c := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) h64
  have hs : L * exp (-3 * L / 8) ≤ (64 : ℝ) * (10 / 27 : ℝ) ^ 24 := by
    calc
      _ ≤ 64 * exp (-(24 : ℝ)) := by
        convert hd using 1 <;> congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (QRHPropagation.exp_neg_nat_upper 24)
        (by norm_num)
  have hcorr : 2 * L * exp (-L / 2) ≤ (1 / 100000 : ℝ) * exp (-L / 8) := by
    rw [show -L / 2 = -3 * L / 8 + (-L / 8) from by ring, exp_add]
    have hnum : (128 : ℝ) * (10 / 27 : ℝ) ^ 24 ≤ 1 / 100000 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hs (exp_pos (-L / 8)).le,
      mul_le_mul_of_nonneg_right hnum (exp_pos (-L / 8)).le]
  have ht := FKS2Sol.Etheta_le_Epsi_add (exp_pos L)
  have hfin : Eθ (exp L) ≤ (C + 1 / 100000) * exp (-L / 8) := by
    nlinarith
  rw [← heq, pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp, he1]
  exact hfin

/-- All twelve earlier psi rows are transported without a new density assumption. -/
theorem theta_frontier (hpsi : QRHCH2.v2.psi_density_frontier) :
    ∀ L₀ C : ℝ, (L₀, C) ∈ CH2.v6.densityFrontier →
      HasPowerLogBound Eθ (C + 1 / 100000) 0 (7 / 8) (exp L₀) := by
  intro L₀ C hLC
  have hmin : ∀ p ∈ CH2.v6.densityFrontier, (64 : ℝ) ≤ p.1 := by
    norm_num [CH2.v6.densityFrontier]
  apply theta_from_psi (hmin (L₀, C) hLC)
  intro x hx
  convert hpsi L₀ C hLC x hx using 1 <;> norm_num

theorem theta_96 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ 0.08350 0 (7 / 8) (exp 96) := by
  convert theta_frontier hpsi 96 0.08349
    (by norm_num [CH2.v6.densityFrontier]) using 1 <;> norm_num

theorem theta_128 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ 0.03014 0 (7 / 8) (exp 128) := by
  convert theta_frontier hpsi 128 0.03013
    (by norm_num [CH2.v6.densityFrontier]) using 1 <;> norm_num

theorem theta_192 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ 0.01714 0 (7 / 8) (exp 192) := by
  convert theta_frontier hpsi 192 0.01713
    (by norm_num [CH2.v6.densityFrontier]) using 1 <;> norm_num

theorem theta_300 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ 0.01311 0 (7 / 8) (exp 300) := by
  convert theta_frontier hpsi 300 0.01310
    (by norm_num [CH2.v6.densityFrontier]) using 1 <;> norm_num

theorem theta_1000 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ 0.01015 0 (7 / 8) (exp 1000) := by
  convert theta_frontier hpsi 1000 0.01014
    (by norm_num [CH2.v6.densityFrontier]) using 1 <;> norm_num

end QRHPhase2
