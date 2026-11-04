/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.RawSource
import OriginalIntegralTight

namespace WinnerBetaA.ClosedMoment
open Real Set MeasureTheory
open WinnerBetaA.Minkowski WinnerOriginalScalars

theorem actual_tight_kernel_budget : (∫ y, rationalKernel y) ≤ (358047/100000:ℝ) := by
  rw [kernel_identity]
  exact WinnerOriginalDensity.Tight.full_integral_bound

theorem finite_U1315 :
    8*(601/5000:ℝ)*(1000000000001/1000000000000)*(309/500)^2*(358047/100000)
      ≤ 263/200 := by norm_num

/-- A second genuine numerical instantiation uses tighter checks of exactly
the same source kernel; the original U=1.34 theorem remains available. -/
theorem source_left_moment_U1315 {F : ℝ → ℝ} {M T : ℝ}
    (hHT : height ≤ T)
    (hFcont : ContinuousOn F (Ioi 0))
    (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0,
      F x ≤ rawAmplitude (309/500) (1413/500) sourceM1 sourceM2 T x ^ 2)
    (hsmooth : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, gaussianWeight x * F x)) :
    M ≤ (263/200:ℝ)*T^((4:ℝ)/3)*log T^3 := by
  have h : M ≤ (263/200:ℝ)*(log T^3*T^((4:ℝ)/3)) := by
    exact uniform_left_moment (by norm_num) (by norm_num)
      source_mone_nonneg source_mtwo_nonneg (by norm_num [height]) hHT
      (by convert source_mone_upper using 1 <;> norm_num) source_mtwo_upper source_log_lower
      source_rzero_upper source_rone_upper hFcont hFpos hraw hsmooth
      actual_kernel_integrable actual_tight_kernel_budget source_omega_upper finite_U1315
  convert h using 1
  ring
end WinnerBetaA.ClosedMoment

namespace WinnerBetaA.ActualObject
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.Minkowski WinnerBetaA.ClosedMoment

/-- Same actual source objects and independent primary inputs, with the second
executed finite configuration materially reducing U from1.34 to1.315. -/
theorem actual_left_U1315_from_primary_inputs {T : ℝ}
    (hHT : height ≤ T)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHPY : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u)
    (hMeanSquare : ∀ t > 0, (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T)
    (hSourceSmoothing : sourceMoment T (1/2) ≤
      (8*(601/5000:ℝ)*Real.exp ((601/5000:ℝ)/(2*T^2)))*
        (∫ x in Ioi 0, gaussianWeight x * scaledCriticalF T x)) :
    sourceMoment T (1/2) ≤ (263/200:ℝ)*T^((4:ℝ)/3)*Real.log T^3 := by
  have hT : 0 ≤ T := le_trans (by norm_num [height]) hHT
  exact source_left_moment_U1315 hHT (scaledCriticalF_continuous T).continuousOn
    (fun x hx => scaledCriticalF_nonneg hT hx.le)
    (raw_of_zeta_and_mean_square hHT hLow hHPY hMeanSquare) hSourceSmoothing

#print axioms actual_left_U1315_from_primary_inputs
#check actual_left_U1315_from_primary_inputs
end WinnerBetaA.ActualObject
