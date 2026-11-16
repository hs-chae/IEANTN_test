/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Moment

namespace WinnerBetaA.ParamMoment
open Real Set MeasureTheory WinnerBetaA.Minkowski
set_option maxHeartbeats 0

noncomputable def envelopeKernel (r₀ r₁ y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*
    (sqrt ((645/1000:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+|y|/28)+r₀)+r₁*exp (y/2))^2

/-- Arbitrary certified residual operands, retaining the exact same source
normalization.  Concrete instances must supply their actual finite checks. -/
theorem logKernel_le_envelope {a₁ a₂ m₁ m₂ H r₀ r₁ : ℝ}
    (ha₁ : 0<a₁) (ha₂ : 0≤a₂) (hH : 1<H)
    (hM₁ : m₁≤(645/1000:ℝ)) (hM₂ : m₂≤(23/250:ℝ)) (hhH : (28:ℝ)≤log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H)≤r₀)
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H))≤r₁) :
    ∀ y : ℝ, logKernel a₁ a₂ m₁ m₂ H y≤envelopeKernel r₀ r₁ y := by
  intro y
  have hb := bracket_of_scalar_bounds ha₁ ha₂ hH (exp_pos y) hM₁ hM₂
    (show (0:ℝ)<28 by norm_num) hhH hr₀ hr₁
  have hkn : 0≤kernelBracket a₁ a₂ m₁ m₂ H (exp y) := by
    have hlH : 0<log H := log_pos hH
    have hH0 : 0<H := by linarith
    unfold kernelBracket
    positivity
  have hs := pow_le_pow_left₀ hkn hb 2
  rw [envelopeBracket_exp] at hs
  exact mul_le_mul_of_nonneg_left hs (exp_pos _).le

/-- This generic interface is a reusable lemma, not a discharged endpoint:
a concrete later instance must prove hDom and supply the actual kernel budget. -/
theorem gaussianKernel_integral {a₁ a₂ m₁ m₂ H J : ℝ} {K : ℝ → ℝ}
    (hDom : ∀ y : ℝ, logKernel a₁ a₂ m₁ m₂ H y≤K y)
    (hKR : Integrable K) (hJ : (∫ y, K y)≤J) :
    IntegrableOn (gaussianKernel a₁ a₂ m₁ m₂ H) (Ioi 0) ∧
      (∫ x in Ioi 0, gaussianKernel a₁ a₂ m₁ m₂ H x)≤J := by
  have hLK : Integrable (logKernel a₁ a₂ m₁ m₂ H) := by
    apply hKR.mono' (logKernel_continuous a₁ a₂ m₁ m₂ H).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (logKernel_nonneg _ _ _ _ _ _)]
      exact hDom y
  have hcomp : (fun y : ℝ => exp y • gaussianKernel a₁ a₂ m₁ m₂ H (exp y)) =
      logKernel a₁ a₂ m₁ m₂ H := by
    funext y
    exact exp_gaussianKernel _ _ _ _ _ _
  have hG : IntegrableOn (gaussianKernel a₁ a₂ m₁ m₂ H) (Ioi 0) := by
    apply (MeasureTheory.integrable_comp_exp _).mp
    rw [hcomp]
    exact hLK
  have heq : (∫ y, logKernel a₁ a₂ m₁ m₂ H y)=
      ∫ x in Ioi 0, gaussianKernel a₁ a₂ m₁ m₂ H x := by
    rw [←hcomp]
    exact MeasureTheory.integral_comp_exp _
  refine ⟨hG,?_⟩
  rw [←heq]
  exact (MeasureTheory.integral_mono hLK hKR hDom).trans hJ

theorem sourceGaussian_integral {F : ℝ → ℝ} {a₁ a₂ m₁ m₂ H T J : ℝ} {K : ℝ → ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T)
    (hDom : ∀ y : ℝ, logKernel a₁ a₂ m₁ m₂ H y ≤ K y)
    (hFcont : ContinuousOn F (Ioi 0)) (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0, F x ≤ rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2)
    (hKR : Integrable K) (hJ : (∫ y, K y) ≤ J) :
    IntegrableOn (fun x ↦ gaussianWeight x * F x) (Ioi 0) ∧
      (∫ x in Ioi 0, gaussianWeight x * F x) ≤
        (a₁^2*(log T^3*T^((4:ℝ)/3)))*J := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  let D := log T^3*T^((4:ℝ)/3)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨hG,hGI⟩ := gaussianKernel_integral hDom hKR hJ
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
theorem uniform_left_moment {F : ℝ → ℝ} {M a₁ a₂ m₁ m₂ H T J ωbar Ubar : ℝ} {K : ℝ → ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T)
    (hDom : ∀ y : ℝ, logKernel a₁ a₂ m₁ m₂ H y ≤ K y)
    (hFcont : ContinuousOn F (Ioi 0)) (hFpos : ∀ x > 0, 0 ≤ F x)
    (hraw : ∀ x > 0, F x ≤ rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2)
    (hsmooth : M ≤ (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, gaussianWeight x * F x))
    (hKR : Integrable K) (hJ : (∫ y, K y) ≤ J)
    (hω : exp ((601/5000:ℝ)/(2*H^2)) ≤ ωbar)
    (hNum : 8*(601/5000:ℝ)*ωbar*a₁^2*J ≤ Ubar) :
    M ≤ Ubar*(log T^3*T^((4:ℝ)/3)) := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  let D := log T^3*T^((4:ℝ)/3)
  have hD : 0 < D := by dsimp [D]; positivity
  have hI := (sourceGaussian_integral ha₁ ha₂ hm₁ hm₂ hH hHT hDom
    hFcont hFpos hraw hKR hJ).2
  have hJpos : 0 ≤ J := by
    have hKpos : ∀ y : ℝ, 0 ≤ K y := by
      intro y
      exact (logKernel_nonneg _ _ _ _ _ _).trans (hDom y)
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


#print axioms logKernel_le_envelope
#print axioms uniform_left_moment
end WinnerBetaA.ParamMoment
