/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PiPower

namespace WinnerBetaA
open Real IEANTN
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing)

/-- The prime-power correction with any explicit whole-ray slack. -/
theorem theta_correction_ray {β L₀ ε L : ℝ} (hL₀ : 0 < L₀) (hL : L₀ ≤ L)
    (hdec : 1 ≤ (β - 1 / 2) * L₀)
    (hslack : 2 * L₀ * exp (-(β - 1 / 2) * L₀) ≤ ε) :
    Eθ (exp L) ≤ Eψ (exp L) + ε * exp ((β - 1) * L) := by
  have hLpos : 0 < L := hL₀.trans_le hL
  have he : 0 < exp L := exp_pos L
  have hx1 : 1 ≤ exp L := by linarith [add_one_le_exp L]
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
  have hd := poly_exp_decreasing 1 (L0 := L₀) (c := β - 1 / 2) hL₀
    ((div_le_iff₀ hL₀).mpr (by simpa only [Nat.cast_one] using hdec)) hL
  have hs : 2 * L * exp (-(β - 1 / 2) * L) ≤ ε := by
    simp only [pow_one] at hd
    linarith
  have hsplit : exp (-L / 2) = exp (-(β - 1 / 2) * L) * exp ((β - 1) * L) := by
    rw [← exp_add]; congr 1; ring
  have hcorr : 2 * L * exp (-L / 2) ≤ ε * exp ((β - 1) * L) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right hs (exp_pos ((β - 1) * L)).le]
  have ht := FKS2Sol.Etheta_le_Epsi_add he
  linarith

/-- A constant psi profile transfers uniformly, consuming an independently checked slack. -/
theorem theta_from_psi {C β L₀ ε : ℝ} (hL₀ : 0 < L₀)
    (hdec : 1 ≤ (β - 1 / 2) * L₀)
    (hslack : 2 * L₀ * exp (-(β - 1 / 2) * L₀) ≤ ε)
    (hψ : HasPowerLogBound Eψ C 0 β (exp L₀)) :
    HasPowerLogBound Eθ (C + ε) 0 β (exp L₀) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L₀).trans_le hx
  let L := log x
  have hL : L₀ ≤ L := by
    have hh := log_le_log (exp_pos L₀) hx
    simpa [L] using hh
  have heq : exp L = x := exp_log hx0
  have hp := hψ x hx
  have ht := theta_correction_ray hL₀ hL hdec hslack
  rw [heq] at ht
  simp only [pow_zero, mul_one] at hp ⊢
  rw [rpow_def_of_pos hx0]
  have hid : log x * (β - 1) = (β - 1) * L := by dsimp [L]; ring
  rw [hid]
  rw [rpow_def_of_pos hx0, hid] at hp
  nlinarith

/-- The same correction transports a log-squared psi profile, with arbitrary beta. -/
theorem theta_from_psi_log2 {C β L₀ ε : ℝ} (hL₀ : 1 ≤ L₀)
    (hdec : 1 ≤ (β - 1 / 2) * L₀)
    (hslack : 2 * L₀ * exp (-(β - 1 / 2) * L₀) ≤ ε)
    (hψ : HasPowerLogBound Eψ C 2 β (exp L₀)) :
    HasPowerLogBound Eθ (C + ε) 2 β (exp L₀) := by
  intro x hx
  have hL₀pos : 0 < L₀ := by linarith
  have hx0 : 0 < x := (exp_pos L₀).trans_le hx
  let L := log x
  have hL : L₀ ≤ L := by
    have hh := log_le_log (exp_pos L₀) hx
    simpa [L] using hh
  have hLone : 1 ≤ L := hL₀.trans hL
  have heq : exp L = x := exp_log hx0
  have hε : 0 ≤ ε := (by positivity : 0 ≤ 2 * L₀ * exp (-(β - 1 / 2) * L₀)).trans hslack
  have hp := hψ x hx
  have ht := theta_correction_ray hL₀pos hL hdec hslack
  rw [heq] at ht
  rw [rpow_def_of_pos hx0]
  have hid : log x * (β - 1) = (β - 1) * L := by dsimp [L]; ring
  rw [hid]
  rw [rpow_def_of_pos hx0, hid] at hp
  have heps : ε * exp ((β - 1) * L) ≤ ε * log x ^ 2 * exp ((β - 1) * L) := by
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    exact le_mul_of_one_le_right hε (by dsimp [L] at hLone; nlinarith [sq_nonneg (log x - 1)])
  nlinarith

#print axioms theta_from_psi
#print axioms theta_from_psi_log2
end WinnerBetaA
