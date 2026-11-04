/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.ParamSource
import ReversScalars
import ReversIntegral

/-! A separate actual-input experiment under Revers, arXiv:2602.05614v1,
Theorem1.1(a).  Existing HPY source contracts and endpoints are preserved.
The generic envelope premise is discharged by the new exact operands and
executed full-kernel certificate; it is not a fresh desired-U assumption. -/
namespace WinnerBetaA.ReversMoment
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.Minkowski WinnerBetaA.ActualObject

theorem kernel_identity :
    WinnerBetaA.ParamMoment.envelopeKernel (137/100000) (47/500000) =
      WinnerReversDensity.kernelAll := by
  funext y
  norm_num [WinnerBetaA.ParamMoment.envelopeKernel,WinnerReversDensity.kernelAll]

theorem actual_source_kernel_bound :
    ∀ y : ℝ, logKernel (611/1000) (281/100) sourceM1 sourceM2 height y ≤
      WinnerReversDensity.kernelAll y := by
  rw [←kernel_identity]
  exact WinnerBetaA.ParamMoment.logKernel_le_envelope (by norm_num) (by norm_num)
    (by norm_num [height]) (by convert source_mone_upper using 1 <;> norm_num)
    source_mtwo_upper source_log_lower Revers.source_rzero_upper Revers.source_rone_upper

/-- Same actual source object and low-height/mean-square/smoothing results,
but a separately named Revers input.  All newly computed U=1.286 steps close. -/
theorem actual_left_U1286_from_primary_inputs {T : ℝ}
    (hHT : height ≤ T)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hRevers : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (611/1000)*u^((1:ℝ)/6)*log u)
    (hMeanSquare : ∀ t > 0, (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T)
    (hSourceSmoothing : sourceMoment T (1/2) ≤
      (8*(601/5000:ℝ)*Real.exp ((601/5000:ℝ)/(2*T^2)))*
        (∫ x in Ioi 0, gaussianWeight x * scaledCriticalF T x)) :
    sourceMoment T (1/2) ≤ (643/500:ℝ)*T^((4:ℝ)/3)*Real.log T^3 := by
  have hT : 0 ≤ T := le_trans (by norm_num [height]) hHT
  have hraw := raw_of_zeta_and_mean_square_param hHT (by norm_num : (0:ℝ)≤611/1000)
    Revers.amplitude_floor_upper hLow hRevers hMeanSquare
  have hh : sourceMoment T (1/2) ≤ (643/500:ℝ)*(log T^3*T^((4:ℝ)/3)) := by
    exact WinnerBetaA.ParamMoment.uniform_left_moment (by norm_num) (by norm_num)
      WinnerBetaA.ClosedMoment.source_mone_nonneg WinnerBetaA.ClosedMoment.source_mtwo_nonneg
      (by norm_num [height]) hHT actual_source_kernel_bound
      (scaledCriticalF_continuous T).continuousOn
      (fun x hx => scaledCriticalF_nonneg hT hx.le) hraw hSourceSmoothing
      WinnerReversDensity.kernel_integrable WinnerReversDensity.full_integral_bound
      source_omega_upper Revers.finite_U1286
  convert hh using 1
  ring

/-- This separate input can supply the existing HPY mathematical interface;
the reverse direction is not claimed. -/
theorem revers_supplies_hpy
    (hRevers : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (611/1000)*u^((1:ℝ)/6)*log u) :
    ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u := by
  intro u hu
  have hu0 : 0≤u := by linarith
  have hl : 0≤log u := log_nonneg (by linarith)
  have hp : 0≤u^((1:ℝ)/6)*log u := mul_nonneg (rpow_nonneg hu0 _) hl
  have hh := mul_le_mul_of_nonneg_right (by norm_num : (611/1000:ℝ)≤309/500) hp
  have hz := hRevers u hu
  nlinarith

#print axioms actual_source_kernel_bound
#print axioms actual_left_U1286_from_primary_inputs
#check actual_left_U1286_from_primary_inputs
end WinnerBetaA.ReversMoment
