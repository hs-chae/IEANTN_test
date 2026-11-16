/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Moment
import OriginalIntegral
import OriginalScalarSemantics

/-! Closed consumer of the newly executed source-kernel certificates.  No
kernel, quadrature, scalar, tail, or proposed U bound remains as a hypothesis.
Only independently sourced F-object regularity, raw Minkowski and smoothing
relations remain explicit, so they cannot be mistaken for proved source facts. -/
namespace WinnerBetaA.ClosedMoment
open Real Set MeasureTheory
open WinnerBetaA.Minkowski WinnerOriginalScalars

theorem kernel_identity : rationalKernel = WinnerOriginalDensity.kernelAll := by
  funext y
  norm_num [rationalKernel, WinnerOriginalDensity.kernelAll]

theorem actual_kernel_integrable : Integrable rationalKernel := by
  rw [kernel_identity]
  exact WinnerOriginalDensity.kernel_integrable

theorem actual_kernel_budget : (∫ y, rationalKernel y) ≤ (182001/50000:ℝ) := by
  rw [kernel_identity]
  exact WinnerOriginalDensity.full_integral_bound

theorem source_mone_nonneg : 0 ≤ sourceM1 := by
  have hl : 0 < log height := lt_of_lt_of_le (by norm_num) source_log_lower
  unfold sourceM1
  positivity

theorem source_mtwo_nonneg : 0 ≤ sourceM2 := by
  have hl : 0 < log height := lt_of_lt_of_le (by norm_num) source_log_lower
  have hH : 0 < height := by norm_num [height]
  have hm : 0 ≤ sourceM0 := by unfold sourceM0; positivity
  unfold sourceM2
  positivity

/-- The genuinely new left moment U=1.34, uniformly for all T≥3·10¹².
The entire new kernel normalization/integration/certification is discharged.
The remaining premises are the original source-object boundary, separately
named rather than a disguised assumption of the proposed moment bound. -/
theorem source_left_moment_U134 {F : ℝ → ℝ} {M T : ℝ}
    (hHT : height ≤ T)
    (hFcont : ContinuousOn F (Ioi 0))
    (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0,
      F x ≤ rawAmplitude (309/500) (1413/500) sourceM1 sourceM2 T x ^ 2)
    (hsmooth : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, gaussianWeight x * F x)) :
    M ≤ (67/50:ℝ)*(log T^3*T^((4:ℝ)/3)) := by
  exact uniform_left_moment (by norm_num) (by norm_num)
    source_mone_nonneg source_mtwo_nonneg (by norm_num [height]) hHT
    (by convert source_mone_upper using 1 <;> norm_num) source_mtwo_upper source_log_lower
    source_rzero_upper source_rone_upper hFcont hFpos hraw hsmooth
    actual_kernel_integrable actual_kernel_budget source_omega_upper finite_U134

/-- The form consumed by the source-count/interpolation theorem. -/
theorem source_left_moment_U134_count_form {F : ℝ → ℝ} {M T : ℝ}
    (hHT : height ≤ T)
    (hFcont : ContinuousOn F (Ioi 0))
    (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0,
      F x ≤ rawAmplitude (309/500) (1413/500) sourceM1 sourceM2 T x ^ 2)
    (hsmooth : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, gaussianWeight x * F x)) :
    M ≤ (67/50:ℝ)*T^((4:ℝ)/3)*log T^3 := by
  have h := source_left_moment_U134 hHT hFcont hFpos hraw hsmooth
  convert h using 1
  ring

#print axioms actual_kernel_integrable
#print axioms actual_kernel_budget
#print axioms source_left_moment_U134
#print source_left_moment_U134
end WinnerBetaA.ClosedMoment
