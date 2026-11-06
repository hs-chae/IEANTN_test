/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Tight
import E1FrozenN.Interval.PrimeConsumer
import WinnerBetaA.Theta
import PowerBounds
namespace E1FrozenN
open Real IEANTN
open scoped Chebyshev
set_option maxHeartbeats 0
theorem criterion : PrimeInterval.v1.eTheta_criterion := by
  intro x h hx hh
  intro hE
  have hxh : 0 < x + h := by linarith
  have hx_bound : θ x ≤ x + x * IEANTN.Eθ x := by
    have hx_abs : x * IEANTN.Eθ x = |θ x - x| := by
      unfold IEANTN.Eθ; field_simp [hx.ne']
    have habs : |θ x - x| ≤ x * IEANTN.Eθ x := by simp [hx_abs]
    linarith [abs_sub_le_iff.mp habs |>.1]
  have hxh_bound : (x + h) - (x + h) * IEANTN.Eθ (x + h) ≤ θ (x + h) := by
    have hxh_abs : (x + h) * IEANTN.Eθ (x + h) = |θ (x + h) - (x + h)| := by
      unfold IEANTN.Eθ; field_simp [hxh.ne']
    have habs : |θ (x + h) - (x + h)| ≤ (x + h) * IEANTN.Eθ (x + h) := by simp [hxh_abs]
    linarith [abs_sub_le_iff.mp habs |>.2]
  exact E1FrozenN.Interval.theta_increase_has_prime hx.le hh.le (by linarith)

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



/-- Baseline theta consumer: only elementary scalar slack, no fresh program. -/
theorem theta330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (9150520022/1000000000000+1/10^12) 0 (7/8) (exp 330) := by
  have he : 2*(330:ℝ)*exp (-((7/8:ℝ)-1/2)*330)≤1/10^12 := by
    have hb := (CH2Section7A.exp_nat_bounds 120).1
    have hm : exp (120:ℝ)≤exp (((7/8:ℝ)-1/2)*330) := exp_le_exp.mpr (by norm_num)
    rw [neg_mul,exp_neg,←one_div,mul_one_div,div_le_iff₀ (exp_pos _)]
    norm_num at hb ⊢
    linarith
  apply WinnerBetaA.theta_from_psi (by norm_num : (0:ℝ)<330)
    (by norm_num : (1:ℝ)≤((7/8:ℝ)-1/2)*330) he
  intro x hx
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num]
    using psi330 hs h hRH hqrh hx

/-- Actual whole-real-ray prime interval from the frozen baseline. -/
theorem prime330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    ∀x:ℝ,exp 330≤x→HasPrimeInInterval x
      ((201/100:ℝ)*(9150520022/1000000000000+1/10^12)*x^(7/8:ℝ)) := by
  have hsml : (9150520022/1000000000000+1/10^12:ℝ)*330^0*
      exp (-(1-(7/8:ℝ))*330)≤1/1000 := by
    have hb := (CH2Section7A.exp_nat_bounds 40).1
    have hm : exp (40:ℝ)≤exp ((1-(7/8:ℝ))*330) := exp_le_exp.mpr (by norm_num)
    rw [neg_mul,exp_neg,←one_div,mul_one_div,div_le_iff₀ (exp_pos _)]
    norm_num at hb ⊢
    linarith
  have hp := intervals_of_power_sharp criterion
    (by norm_num : (0:ℝ)<9150520022/1000000000000+1/10^12)
    (by norm_num : (7/8:ℝ)<1) (by norm_num : (0:ℝ)<330)
    (k:=0) (by norm_num) hsml (theta330 hs h hRH hqrh)
  simpa only [pow_zero,mul_one] using hp

#print axioms theta330
#print axioms prime330
end E1FrozenN
