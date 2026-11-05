/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

/-!
# From a power bound on `Eθ` to primes in `(x, x + c·x^{7/8}]`

`interval_of_theta_power` turns a bound `Eθ y ≤ C·y^{-1/8}` on `[e^L, ∞)` into a prime in every
interval `(x, x + c·x^{7/8}]` with `x ≥ e^L`, through the node criterion
`PrimeInterval.v1.eTheta_criterion`, provided `C·(2 + c·e^{-L/8}) < c`.

The two endpoint errors are bounded separately: `x·Eθ x ≤ C·x^{7/8}`, and, because `y ↦ y^{-1/8}`
decreases, `(x+h)·Eθ (x+h) ≤ C·(x+h)·x^{-1/8} = C·(x^{7/8} + h·x^{-1/8})`.
-/

namespace QRHGlobal

open Real IEANTN

theorem HasPrimeInInterval.mono {x h h' : ℝ} (hp : HasPrimeInInterval x h) (hh : h ≤ h') :
    HasPrimeInInterval x h' := by
  obtain ⟨p, hp, h1, h2⟩ := hp
  exact ⟨p, hp, h1, h2.trans (by linarith)⟩

theorem interval_of_theta_power (hcrit : PrimeInterval.v1.eTheta_criterion)
    {C c L : ℝ} (hθ : HasPowerLogBound Eθ C 0 (7 / 8) (exp L)) (hC : 0 ≤ C) (hc : 0 < c)
    (hsmall : C * (2 + c * exp (-L / 8)) < c) :
    ∀ x ≥ exp L, HasPrimeInInterval x (c * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hLx : L ≤ log x := by simpa using log_le_log (exp_pos L) hx
  have hw0 : 0 < x ^ ((7 : ℝ) / 8) := rpow_pos_of_pos hx0 _
  have hu0 : 0 < x ^ ((7 : ℝ) / 8 - 1) := rpow_pos_of_pos hx0 _
  have hxu : x * x ^ ((7 : ℝ) / 8 - 1) = x ^ ((7 : ℝ) / 8) := by
    rw [rpow_sub hx0, rpow_one]; field_simp
  have huL : x ^ ((7 : ℝ) / 8 - 1) ≤ exp (-L / 8) := by
    rw [rpow_def_of_pos hx0]
    apply exp_le_exp.mpr
    have : log x * ((7 : ℝ) / 8 - 1) = -(log x) / 8 := by ring
    rw [this]
    linarith
  set w := x ^ ((7 : ℝ) / 8) with hw
  set u := x ^ ((7 : ℝ) / 8 - 1) with hu
  set h := c * w with hh
  have hh0 : 0 < h := by positivity
  have hxh : 0 < x + h := by linarith
  have h1 : x * Eθ x ≤ C * w := by
    have hb := hθ x hx
    simp only [pow_zero, mul_one] at hb
    calc x * Eθ x ≤ x * (C * u) := mul_le_mul_of_nonneg_left hb hx0.le
      _ = C * (x * u) := by ring
      _ = C * w := by rw [hxu]
  have h2 : (x + h) * Eθ (x + h) ≤ C * (w + h * u) := by
    have hb := hθ (x + h) (by linarith)
    simp only [pow_zero, mul_one] at hb
    have hmono : (x + h) ^ ((7 : ℝ) / 8 - 1) ≤ u :=
      rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
    calc (x + h) * Eθ (x + h) ≤ (x + h) * (C * (x + h) ^ ((7 : ℝ) / 8 - 1)) :=
          mul_le_mul_of_nonneg_left hb hxh.le
      _ ≤ (x + h) * (C * u) := by gcongr
      _ = C * (x * u + h * u) := by ring
      _ = C * (w + h * u) := by rw [hxu]
  apply hcrit x h hx0 hh0
  have hhu : h * u ≤ c * w * exp (-L / 8) := by
    rw [hh, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huL hw0.le) hc.le
  have key : C * w + C * (w + h * u) ≤ C * w * (2 + c * exp (-L / 8)) := by
    have := mul_le_mul_of_nonneg_left hhu hC
    nlinarith
  have hlt : C * w * (2 + c * exp (-L / 8)) < c * w := by
    have := mul_lt_mul_of_pos_right hsmall hw0
    linarith
  linarith

end QRHGlobal
