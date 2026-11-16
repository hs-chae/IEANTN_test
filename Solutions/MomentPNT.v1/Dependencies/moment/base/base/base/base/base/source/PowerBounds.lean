/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Applications
import IEANTN.Vocabulary.PowerError
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

/-! A general envelope interface reused across error functions and interval widths. -/
namespace QRHPowerBounds
open Real IEANTN
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing)

/-- The same proof handles every error function and every admissible beta. -/
theorem numerical_of_power {E : ℝ → ℝ} {A β L : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hβ : β < 1) (hL : 0 < L) (hdec : (k : ℝ) ≤ (1 - β) * L)
    (hE : HasPowerLogBound E A k β (exp L)) :
    HasNumericalBound E (A * L ^ k * exp (-(1 - β) * L)) (exp L) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hlx : L ≤ log x := by
    have hh := log_le_log (exp_pos L) hx
    simpa only [log_exp] using hh
  have h := poly_exp_decreasing k hL ((div_le_iff₀ hL).mpr hdec) hlx
  have hb := hE x hx
  rw [rpow_def_of_pos hx0] at hb
  have hid : log x * (β - 1) = -(1 - β) * log x := by ring
  rw [hid] at hb
  calc
    E x ≤ A * log x ^ k * exp (-(1 - β) * log x) := hb
    _ = A * (log x ^ k * exp (-(1 - β) * log x)) := by ring
    _ ≤ A * (L ^ k * exp (-(1 - β) * L)) := mul_le_mul_of_nonneg_left h hA
    _ = _ := by ring

/-- The existing prime-interval criterion consumes the whole moving envelope. -/
theorem intervals_of_power (hcrit : PrimeInterval.v1.eTheta_criterion)
    {A β L : ℝ} {k : ℕ} (hA : 0 < A) (hβ : β < 1) (hL : 0 < L)
    (hdec : (k : ℝ) ≤ (1 - β) * L)
    (hsmall : A * L ^ k * exp (-(1 - β) * L) ≤ 1 / 4)
    (hE : HasPowerLogBound Eθ A k β (exp L)) :
    ∀ x ≥ exp L, HasPrimeInInterval x (4 * A * log x ^ k * x ^ β) := by
  have hshape : HasNumericalBound
      (fun x ↦ A * log x ^ k * x ^ (β - 1))
      (A * L ^ k * exp (-(1 - β) * L)) (exp L) :=
    numerical_of_power hA.le hβ hL hdec (fun _ _ ↦ le_rfl)
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
  have hδsmall : δ ≤ 1 / 4 := (hshape x hx).trans hsmall
  have hn := numerical_of_power hA.le hβ hlx0 hdecx hin
  have heq : A * log x ^ k * exp (-(1 - β) * log x) = δ := by
    dsimp [δ]
    rw [rpow_def_of_pos hx0]
    congr 2
    ring
  rw [exp_log hx0, heq] at hn
  let h := 4 * x * δ
  have hh : 0 < h := by dsimp [h]; positivity
  have hhx : h ≤ x := by dsimp [h]; nlinarith [hδsmall]
  have h1 := mul_le_mul_of_nonneg_left (hn x le_rfl) hx0.le
  have h2 := mul_le_mul_of_nonneg_left (hn (x + h) (by linarith))
    (show 0 ≤ x + h by positivity)
  have hc : x * Eθ x + (x + h) * Eθ (x + h) < h := by
    have hprod : 0 < x * δ := mul_pos hx0 hδpos
    have hhprod := mul_le_mul_of_nonneg_right hhx hδpos.le
    dsimp [h] at *
    nlinarith
  have hp := hcrit x h hx0 hh hc
  have hwidth : h = 4 * A * log x ^ k * x ^ β := by
    dsimp [h, δ]
    rw [rpow_sub hx0, rpow_one]
    field_simp
  rw [hwidth] at hp
  exact hp

end QRHPowerBounds
