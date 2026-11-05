/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.RawSource
import WinnerBetaA.ParamMoment

namespace WinnerBetaA.ActualObject
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.Minkowski

/-- Reusable source-input adapter for any independently supplied high-t
subconvexity coefficient and explicitly certified amplitude-floor adjustment.
It is instantiated later; no numerical floor premise is silently discharged. -/
theorem zeta_on_initial_interval_param {a₁ a₂ low : ℝ}
    (ha₁ : 0 ≤ a₁) (hFloor : 6*a₁/exp 1+low ≤ a₂)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ low)
    (hHigh : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ a₁*u^((1:ℝ)/6)*log u)
    {t u : ℝ} (ht : 0 < t) (hu : u ∈ Icc 0 t) :
    ‖riemannZeta (vertical (1/2) u)‖ ≤ a₁*t^((1:ℝ)/6)*log t+a₂ := by
  by_cases hsmall : u ≤ 3
  · have hfl : low ≤ a₁*t^((1:ℝ)/6)*log t+a₂ := by
      linear_combination a₁*(power_log_minimum ht)+hFloor
    exact (hLow u hu.1 hsmall).trans hfl
  · have hu3 : 3 ≤ u := le_of_lt (lt_of_not_ge hsmall)
    have htu : u^((1:ℝ)/6)*log u ≤ t^((1:ℝ)/6)*log t :=
      power_log_monotone (by change 1≤u; linarith) (by change 1≤t; linarith [hu.2]) hu.2
    have hh := mul_le_mul_of_nonneg_left htu ha₁
    have hLow0 : 0 ≤ low := by
      exact (norm_nonneg _).trans (hLow 0 (by norm_num) (by norm_num))
    have ha₂ : 0 ≤ a₂ := le_trans (by positivity) hFloor
    linarith [hHigh u hu3]

theorem raw_of_zeta_and_mean_square_param {T a₁ a₂ low : ℝ}
    (hHT : height ≤ T) (ha₁ : 0 ≤ a₁)
    (hFloor : 6*a₁/exp 1+low ≤ a₂)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ low)
    (hHigh : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ a₁*u^((1:ℝ)/6)*log u)
    (hMeanSquare : ∀ t > 0, (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T) :
    ∀ x > 0, scaledCriticalF T x ≤ rawAmplitude a₁ a₂ sourceM1 sourceM2 T x ^ 2 := by
  intro x hx
  have hT : 0 < T := lt_of_lt_of_le (by norm_num [height]) hHT
  have ht : 0 < x*T := mul_pos hx hT
  have hZ : ∀ u ∈ Icc 0 (x*T),
      ‖riemannZeta (vertical (1/2) u)‖ ≤ a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂ :=
    fun u hu => zeta_on_initial_interval_param ha₁ hFloor hLow hHigh ht hu
  have hB : 0 ≤ a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂ :=
    (norm_nonneg _).trans (hZ 0 ⟨le_rfl,ht.le⟩)
  have hh := integral_minkowski_sub_one ht critical_zeta_continuous
    ((mollifier_continuous T).comp (vertical_continuous (1/2))) hB hZ (hMeanSquare (x*T) ht)
  simpa only [scaledCriticalF,cumulativeSquare,mollifiedError,rawAmplitude,
    Function.comp_apply,mul_assoc] using hh

#print axioms zeta_on_initial_interval_param
#print axioms raw_of_zeta_and_mean_square_param
end WinnerBetaA.ActualObject
