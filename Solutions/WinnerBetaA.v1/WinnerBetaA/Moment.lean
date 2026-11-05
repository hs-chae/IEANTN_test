/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Minkowski
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace WinnerBetaA.Minkowski
open Real MeasureTheory Set

noncomputable def gaussianWeight (x : ℝ) : ℝ := x*exp (-(601/2500:ℝ)*x^2)
noncomputable def gaussianKernel (a₁ a₂ m₁ m₂ H x : ℝ) : ℝ :=
  gaussianWeight x * kernelBracket a₁ a₂ m₁ m₂ H x ^ 2
noncomputable def logKernel (a₁ a₂ m₁ m₂ H y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*kernelBracket a₁ a₂ m₁ m₂ H (exp y)^2

theorem logKernel_nonneg (a₁ a₂ m₁ m₂ H y : ℝ) : 0 ≤ logKernel a₁ a₂ m₁ m₂ H y := by
  unfold logKernel
  positivity

theorem kernelBracket_exp (a₁ a₂ m₁ m₂ H y : ℝ) :
    kernelBracket a₁ a₂ m₁ m₂ H (exp y) =
      sqrt (m₁*exp y+m₂)*(exp (y/6)*(1+|y|/log H)+a₂/(a₁*H^((1:ℝ)/6)*log H)) +
        (1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)))*exp (y/2) := by
  simpa only [envelopeBracket, kernelBracket] using
    envelopeBracket_exp m₁ m₂ (log H) (a₂/(a₁*H^((1:ℝ)/6)*log H))
      (1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H))) y

theorem logKernel_continuous (a₁ a₂ m₁ m₂ H : ℝ) : Continuous (logKernel a₁ a₂ m₁ m₂ H) := by
  have hform : logKernel a₁ a₂ m₁ m₂ H = fun y : ℝ ↦
      exp (2*y-(601/2500:ℝ)*exp (2*y))*
      (sqrt (m₁*exp y+m₂)*(exp (y/6)*(1+|y|/log H)+a₂/(a₁*H^((1:ℝ)/6)*log H)) +
        (1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)))*exp (y/2))^2 := by
    funext y
    unfold logKernel
    rw [kernelBracket_exp]
  rw [hform]
  fun_prop

/-- The Jacobian is retained; this is an exact real-function identity. -/
theorem exp_gaussianKernel (a₁ a₂ m₁ m₂ H y : ℝ) :
    exp y * gaussianKernel a₁ a₂ m₁ m₂ H (exp y) = logKernel a₁ a₂ m₁ m₂ H y := by
  have hpow : (exp y)^2 = exp (2*y) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hw : exp y * gaussianWeight (exp y) = exp (2*y-(601/2500:ℝ)*exp (2*y)) := by
    unfold gaussianWeight
    calc
      _ = (exp y)^2*exp (-(601/2500:ℝ)*(exp y)^2) := by ring
      _ = exp (2*y)*exp (-(601/2500:ℝ)*exp (2*y)) := by rw [hpow]
      _ = _ := by rw [← exp_add]; congr 1; ring
  unfold gaussianKernel logKernel
  calc
    _ = (exp y * gaussianWeight (exp y))*kernelBracket a₁ a₂ m₁ m₂ H (exp y)^2 := by ring
    _ = _ := by rw [hw]

section ScalarBounds
variable {a₁ a₂ m₁ m₂ H : ℝ}
variable (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hH : 1 < H)
    (hM₁ : m₁ ≤ (645/1000:ℝ)) (hM₂ : m₂ ≤ (23/250:ℝ)) (hhH : (28:ℝ) ≤ log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H) ≤ (681/500000:ℝ))
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) ≤ (23/250000:ℝ))
include ha₁ ha₂ hH hM₁ hM₂ hhH hr₀ hr₁

/-- Actual kernel integrability follows from the proved rational-kernel certificate/tails. -/
theorem logKernel_integrable (hKR : Integrable rationalKernel) :
    Integrable (logKernel a₁ a₂ m₁ m₂ H) := by
  apply hKR.mono' (logKernel_continuous a₁ a₂ m₁ m₂ H).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (logKernel_nonneg _ _ _ _ _ _)]
    exact rational_kernel_bound ha₁ ha₂ hH hM₁ hM₂ hhH hr₀ hr₁

/-- Gaussian integral bound in the original x coordinate, with convergence supplied by domination. -/
theorem gaussianKernel_integral {J : ℝ} (hKR : Integrable rationalKernel)
    (hJ : (∫ y, rationalKernel y) ≤ J) :
    IntegrableOn (gaussianKernel a₁ a₂ m₁ m₂ H) (Ioi 0) ∧
      (∫ x in Ioi 0, gaussianKernel a₁ a₂ m₁ m₂ H x) ≤ J := by
  have hLK := logKernel_integrable ha₁ ha₂ hH hM₁ hM₂ hhH hr₀ hr₁ hKR
  have hcomp : (fun y : ℝ ↦ exp y • gaussianKernel a₁ a₂ m₁ m₂ H (exp y)) =
      logKernel a₁ a₂ m₁ m₂ H := by
    funext y
    exact exp_gaussianKernel _ _ _ _ _ _
  have hG : IntegrableOn (gaussianKernel a₁ a₂ m₁ m₂ H) (Ioi 0) := by
    apply (MeasureTheory.integrable_comp_exp _).mp
    rw [hcomp]
    exact hLK
  have heq : (∫ y, logKernel a₁ a₂ m₁ m₂ H y) =
      ∫ x in Ioi 0, gaussianKernel a₁ a₂ m₁ m₂ H x := by
    rw [← hcomp]
    exact MeasureTheory.integral_comp_exp _
  refine ⟨hG, ?_⟩
  rw [← heq]
  exact (MeasureTheory.integral_mono hLK hKR
    (fun y ↦ rational_kernel_bound ha₁ ha₂ hH hM₁ hM₂ hhH hr₀ hr₁)).trans hJ

end ScalarBounds

/-- Monotonicity of the actual squared omega1 factor, separate from the finite kernel budget. -/
theorem omega_bound {H T : ℝ} (hH : 1 < H) (hHT : H ≤ T) :
    exp ((601/5000:ℝ)/(2*T^2)) ≤ exp ((601/5000:ℝ)/(2*H^2)) := by
  have hH0 : 0 < H := by linarith
  have hT0 : 0 < T := hH0.trans_le hHT
  apply exp_le_exp.mpr
  gcongr

/-- Domination proves convergence of the actual source F integral and its new upper bound.
Only source-object continuity/nonnegativity and the unoptimized raw Minkowski inequality enter. -/
theorem sourceGaussian_integral {F : ℝ → ℝ} {a₁ a₂ m₁ m₂ H T J : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T)
    (hM₁ : m₁ ≤ (645/1000:ℝ)) (hM₂ : m₂ ≤ (23/250:ℝ)) (hhH : (28:ℝ) ≤ log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H) ≤ (681/500000:ℝ))
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) ≤ (23/250000:ℝ))
    (hFcont : ContinuousOn F (Ioi 0)) (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0, F x ≤ rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2)
    (hKR : Integrable rationalKernel) (hJ : (∫ y, rationalKernel y) ≤ J) :
    IntegrableOn (fun x ↦ gaussianWeight x * F x) (Ioi 0) ∧
      (∫ x in Ioi 0, gaussianWeight x * F x) ≤
        (a₁^2*(log T^3*T^((4:ℝ)/3)))*J := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  let D := log T^3*T^((4:ℝ)/3)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨hG,hGI⟩ := gaussianKernel_integral ha₁ ha₂ hH hM₁ hM₂ hhH hr₀ hr₁ hKR hJ
  have hBig := hG.const_mul (a₁^2*D)
  have hWcont : Continuous gaussianWeight := by unfold gaussianWeight; fun_prop
  have hmeas : AEStronglyMeasurable (fun x ↦ gaussianWeight x * F x) (volume.restrict (Ioi 0)) :=
    (hWcont.continuousOn.mul hFcont).aestronglyMeasurable measurableSet_Ioi
  have hdom : ∀ x ∈ Ioi (0:ℝ), ‖gaussianWeight x * F x‖ ≤
      (a₁^2*D)*gaussianKernel a₁ a₂ m₁ m₂ H x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hw : 0 ≤ gaussianWeight x := by unfold gaussianWeight; positivity
    have hf : 0 ≤ F x := hFpos x hx0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hf)]
    have hn := normalized_minkowski ha₁ ha₂ hm₁ hm₂ hH hHT hx0 (hraw x hx0)
    have hF := (div_le_iff₀ hD).mp hn
    have hm := mul_le_mul_of_nonneg_left hF hw
    calc
      _ ≤ gaussianWeight x * (a₁^2*kernelBracket a₁ a₂ m₁ m₂ H x^2*D) := hm
      _ = _ := by unfold gaussianKernel; ring
  have hFint : IntegrableOn (fun x ↦ gaussianWeight x * F x) (Ioi 0) := by
    apply hBig.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hdom x hx
  have hi : (∫ x in Ioi 0, gaussianWeight x * F x) ≤
      ∫ x in Ioi 0, (a₁^2*D)*gaussianKernel a₁ a₂ m₁ m₂ H x := by
    apply integral_mono_ae hFint hBig
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hdom x hx)
  rw [integral_const_mul] at hi
  refine ⟨hFint, ?_⟩
  exact hi.trans (mul_le_mul_of_nonneg_left hGI (by positivity))

/-- Complete new U reduction. The only analytic input is the original source smoothing
relation; the finite kernel budget and scalar witness are supplied by executed certificates. -/
theorem uniform_left_moment {F : ℝ → ℝ} {M a₁ a₂ m₁ m₂ H T J ωbar Ubar : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T)
    (hM₁ : m₁ ≤ (645/1000:ℝ)) (hM₂ : m₂ ≤ (23/250:ℝ)) (hhH : (28:ℝ) ≤ log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H) ≤ (681/500000:ℝ))
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) ≤ (23/250000:ℝ))
    (hFcont : ContinuousOn F (Ioi 0)) (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0, F x ≤ rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2)
    (hsmooth : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, gaussianWeight x * F x))
    (hKR : Integrable rationalKernel) (hJ : (∫ y, rationalKernel y) ≤ J)
    (hω : exp ((601/5000:ℝ)/(2*H^2)) ≤ ωbar)
    (hNum : 8*(601/5000:ℝ)*ωbar*a₁^2*J ≤ Ubar) :
    M ≤ Ubar*(log T^3*T^((4:ℝ)/3)) := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  let D := log T^3*T^((4:ℝ)/3)
  have hD : 0 < D := by dsimp [D]; positivity
  have hI := (sourceGaussian_integral ha₁ ha₂ hm₁ hm₂ hH hHT hM₁ hM₂ hhH hr₀ hr₁
    hFcont hFpos hraw hKR hJ).2
  have hJpos : 0 ≤ J := by
    have hKpos : ∀ y : ℝ, 0 ≤ rationalKernel y := by intro y; unfold rationalKernel; positivity
    exact (integral_nonneg hKpos).trans hJ
  have hωT := (omega_bound hH hHT).trans hω
  have hnorm : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*(a₁^2*D*J) := by
    have hm := mul_le_mul_of_nonneg_left hI
      (show 0 ≤ 8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)) by positivity)
    exact hsmooth.trans hm
  calc
    M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*(a₁^2*D*J) := hnorm
    _ ≤ (8*(601/5000:ℝ)*ωbar)*(a₁^2*D*J) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hωT (by norm_num : (0:ℝ)≤8*(601/5000:ℝ))) (by positivity)
    _ = (8*(601/5000:ℝ)*ωbar*a₁^2*J)*D := by ring
    _ ≤ Ubar*D := mul_le_mul_of_nonneg_right hNum hD.le

/-- The proposed final U witness is a proved rational inequality, not a numerical oracle. -/
theorem finite_U134 :
    8*(601/5000:ℝ)*(1000000000001/1000000000000)*(309/500)^2*(182001/50000) ≤ 67/50 := by
  norm_num

#print axioms gaussianKernel_integral
#print axioms sourceGaussian_integral
#print axioms uniform_left_moment
end WinnerBetaA.Minkowski
