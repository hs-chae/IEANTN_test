/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Frontier

/-! Replace the old factor4transport loss by2.01with its actual smallness condition. -/
namespace QRHPhase2
open Real IEANTN

theorem intervals_of_power_sharp (hcrit : PrimeInterval.v1.eTheta_criterion)
    {A β L : ℝ} {k : ℕ} (hA : 0 < A) (hβ : β < 1) (hL : 0 < L)
    (hdec : (k : ℝ) ≤ (1 - β) * L)
    (hsmall : A * L ^ k * exp (-(1 - β) * L) ≤ 1 / 1000)
    (hE : HasPowerLogBound Eθ A k β (exp L)) :
    ∀ x ≥ exp L, HasPrimeInInterval x ((201 / 100) * A * log x ^ k * x ^ β) := by
  have hshape : HasNumericalBound
      (fun x ↦ A * log x ^ k * x ^ (β - 1))
      (A * L ^ k * exp (-(1 - β) * L)) (exp L) :=
    QRHPowerBounds.numerical_of_power hA.le hβ hL hdec (fun _ _ ↦ le_rfl)
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hlx : L ≤ log x := by
    have hh := log_le_log (exp_pos L) hx
    simpa only [log_exp] using hh
  have hlx0 : 0 < log x := hL.trans_le hlx
  have hdecx : (k : ℝ) ≤ (1 - β) * log x := by
    nlinarith [mul_nonneg (sub_pos.mpr hβ).le (sub_nonneg.mpr hlx)]
  have hin : HasPowerLogBound Eθ A k β (exp (log x)) := by
    rw [exp_log hx0]
    intro y hy
    exact hE y (hx.trans hy)
  let δ := A * log x ^ k * x ^ (β - 1)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 1000 := (hshape x hx).trans hsmall
  have hn := QRHPowerBounds.numerical_of_power hA.le hβ hlx0 hdecx hin
  have heq : A * log x ^ k * exp (-(1 - β) * log x) = δ := by
    dsimp [δ]
    rw [rpow_def_of_pos hx0]
    congr 2
    ring
  rw [exp_log hx0, heq] at hn
  let h := (201 / 100 : ℝ) * x * δ
  have hh : 0 < h := by dsimp [h]; positivity
  have h1 := mul_le_mul_of_nonneg_left (hn x le_rfl) hx0.le
  have h2 := mul_le_mul_of_nonneg_left
    (hn (x + h) (by linarith)) (show 0 ≤ x + h by positivity)
  have hc : x * Eθ x + (x + h) * Eθ (x + h) < h := by
    have hprod : 0 < x * δ := mul_pos hx0 hδpos
    have hδsq := mul_le_mul_of_nonneg_left hδsmall hδpos.le
    have hδsqx := mul_le_mul_of_nonneg_left hδsq hx0.le
    dsimp [h] at *
    nlinarith
  have hp := hcrit x h hx0 hh hc
  have hwidth : h = (201 / 100 : ℝ) * A * log x ^ k * x ^ β := by
    dsimp [h, δ]
    rw [rpow_sub hx0, rpow_one]
    field_simp
  rw [hwidth] at hp
  exact hp


theorem intervals_frontier_sharp (hpsi : QRHCH2.v2.psi_density_frontier)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ L C : ℝ, (L, C) ∈ CH2.v6.densityFrontier → ∀ x ≥ exp L,
      HasPrimeInInterval x ((201 / 100) * (C + 1 / 100000) * x ^ ((7 : ℝ) / 8)) := by
  intro L C hLC
  have hnum : ∀ p ∈ CH2.v6.densityFrontier,
      (64 : ℝ) ≤ p.1 ∧ 0 < p.2 + 1 / 100000 ∧ p.2 + 1 / 100000 ≤ 1 := by
    norm_num [CH2.v6.densityFrontier]
  rcases hnum (L, C) hLC with ⟨hL, hC, hC1⟩
  have hs : (C + 1 / 100000) * L ^ 0 * exp (-(1 - (7 / 8 : ℝ)) * L) ≤
      1 / 1000 := by
    have he : exp (-(1 - (7 / 8 : ℝ)) * L) ≤ (10 / 27 : ℝ) ^ 8 :=
      (exp_le_exp.mpr (by linarith)).trans (QRHPropagation.exp_neg_nat_upper 8)
    norm_num only [pow_zero, mul_one]
    have hm := mul_le_mul_of_nonneg_right hC1 (exp_pos (-(1 - (7 / 8 : ℝ)) * L)).le
    have hrat : (10 / 27 : ℝ) ^ 8 ≤ 1 / 1000 := by norm_num
    linarith
  have hp := intervals_of_power_sharp hcrit hC (by norm_num : (7 / 8 : ℝ) < 1)
    (by linarith : 0 < L) (k := 0) (by norm_num; linarith) hs (theta_frontier hpsi L C hLC)
  simpa only [pow_zero, mul_one] using hp

/-- Strictly shorter intervals on an earlier domain than the old0.08/exp300result. -/
theorem intervals_192 (hpsi : QRHCH2.v2.psi_density_frontier)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x ≥ exp 192, HasPrimeInInterval x (0.0345 * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hp := intervals_frontier_sharp hpsi hcrit 192 0.01713
    (by norm_num [CH2.v6.densityFrontier]) x hx
  rcases hp with ⟨p, hprime, hleft, hright⟩
  refine ⟨p, hprime, hleft, hright.trans ?_⟩
  have hx0 : 0 < x := (exp_pos (192 : ℝ)).trans_le hx
  have hc : (201 / 100 : ℝ) * (0.01713 + 1 / 100000) ≤ 0.0345 := by norm_num
  exact add_le_add (le_refl x)
    (mul_le_mul_of_nonneg_right hc (rpow_pos_of_pos hx0 (7 / 8 : ℝ)).le)

theorem intervals_300 (hpsi : QRHCH2.v2.psi_density_frontier)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x ≥ exp 300, HasPrimeInInterval x (0.0264 * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hp := intervals_frontier_sharp hpsi hcrit 300 0.01310
    (by norm_num [CH2.v6.densityFrontier]) x hx
  rcases hp with ⟨p, hprime, hleft, hright⟩
  refine ⟨p, hprime, hleft, hright.trans ?_⟩
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hc : (201 / 100 : ℝ) * (0.01310 + 1 / 100000) ≤ 0.0264 := by norm_num
  exact add_le_add (le_refl x)
    (mul_le_mul_of_nonneg_right hc (rpow_pos_of_pos hx0 (7 / 8 : ℝ)).le)

end QRHPhase2
