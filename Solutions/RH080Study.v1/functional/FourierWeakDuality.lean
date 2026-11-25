/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

def cosineTransform (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ x : ℝ, F x * cos (2 * π * x * v)

lemma cosineTransform_eq_re_fourier (F : ℝ → ℝ) (hF : Integrable F) (v : ℝ) :
    cosineTransform F v = (𝓕 (fun x : ℝ => (F x : ℂ)) v).re := by
  have he : Integrable (fun x : ℝ =>
      Complex.exp ((-2 * π * x * v : ℝ) * Complex.I) * (F x : ℂ)) := by
    apply hF.ofReal.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change cosineTransform F v =
    (∫ x : ℝ, Complex.exp ((-2 * π * x * v : ℝ) * Complex.I) * (F x : ℂ)).re
  have hre := integral_re he
  change (∫ x : ℝ, (Complex.exp ((-2 * π * x * v : ℝ) * Complex.I) * (F x : ℂ)).re) =
    (∫ x : ℝ, Complex.exp ((-2 * π * x * v : ℝ) * Complex.I) * (F x : ℂ)).re at hre
  rw [← hre]
  unfold cosineTransform
  congr 1
  funext x
  simp [Complex.mul_re, Complex.exp_re]
  ring_nf

lemma integral_transform_eq_value_zero (F G : ℝ → ℝ)
    (hF : Integrable F) (hG : Integrable G) (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ)) :
    (∫ v : ℝ, G v) = F 0 := by
  have hFG : Integrable (𝓕 (fun x : ℝ => (F x : ℂ))) := by
    rw [hfourier]
    exact hG.ofReal
  have hinv := hF.ofReal.fourierInv_fourier_eq hFG
    ((Complex.continuous_ofReal.comp hcont).continuousAt (x := 0))
  rw [Real.fourierInv_eq_fourier_neg, neg_zero, hfourier,
    Real.fourier_real_eq_integral_exp_smul] at hinv
  have hh : (∫ v : ℝ, (G v : ℂ)) = (F 0 : ℂ) := by
    simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul] using hinv
  have hcast : (∫ v : ℝ, (G v : ℂ)) = Complex.ofReal (∫ v : ℝ, G v) :=
    integral_ofReal (𝕜 := ℂ) (f := G)
  rw [hcast] at hh
  exact_mod_cast hh

lemma integrable_cosine_product (F V : ℝ → ℝ)
    (hF : Integrable F) (hV : Integrable V) :
    Integrable (fun p : ℝ × ℝ => F p.1 * V p.2 * cos (2 * π * p.1 * p.2))
      (volume.prod volume) := by
  apply (hF.mul_prod hV).mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with p
    simpa only [Real.norm_eq_abs] using abs_cos_le_one (2 * π * p.1 * p.2)

lemma cosine_pairing (F V : ℝ → ℝ) (hF : Integrable F) (hV : Integrable V) :
    (∫ v : ℝ, cosineTransform F v * V v) =
      ∫ x : ℝ, F x * cosineTransform V x := by
  have hp := integrable_cosine_product F V hF hV
  have swap := integral_integral_swap
    (f := fun x v : ℝ => F x * V v * cos (2 * π * x * v)) hp
  calc
    (∫ v : ℝ, cosineTransform F v * V v) =
        ∫ v : ℝ, ∫ x : ℝ, F x * V v * cos (2 * π * x * v) := by
      congr 1
      funext v
      unfold cosineTransform
      rw [← integral_mul_const]
      congr 1
      funext x
      ring
    _ = ∫ x : ℝ, ∫ v : ℝ, F x * V v * cos (2 * π * x * v) := swap.symm
    _ = ∫ x : ℝ, F x * cosineTransform V x := by
      congr 1
      funext x
      unfold cosineTransform
      calc
        (∫ v : ℝ, F x * V v * cos (2 * π * x * v)) =
            ∫ v : ℝ, F x * (V v * cos (2 * π * v * x)) := by
          congr 1
          funext v
          ring_nf
        _ = _ := integral_const_mul _ _

def exterior : Set ℝ := {v : ℝ | 1 < |v|}

def exteriorPositive (G : ℝ → ℝ) : ℝ → ℝ :=
  exterior.indicator (fun v => max 0 (G v))

lemma exterior_measurable : MeasurableSet exterior := by
  exact isOpen_lt continuous_const continuous_abs |>.measurableSet

lemma exteriorPositive_integrable (G : ℝ → ℝ) (hG : Integrable G) :
    Integrable (exteriorPositive G) := by
  have hpos : Integrable (fun v : ℝ => max 0 (G v)) := by
    have hi := (hG.add hG.norm).div_const 2
    convert hi using 1
    funext v
    simp only [Real.norm_eq_abs]
    by_cases h : 0 ≤ G v
    · simp [max_eq_right h, abs_of_nonneg h]
    · have hn : G v ≤ 0 := le_of_not_ge h
      simp [max_eq_left hn, abs_of_nonpos hn]
  exact hpos.indicator exterior_measurable

lemma dual_pointwise (G V : ℝ → ℝ) (A : ℝ)
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1) (v : ℝ) :
    G v - A * exteriorPositive G v ≤ G v * V v := by
  by_cases he : 1 < |v|
  · rw [show exteriorPositive G v = max 0 (G v) by
      simp [exteriorPositive, exterior, he]]
    have hlo := hlower v he
    have hhi := hupper v he
    by_cases hG : 0 ≤ G v
    · rw [max_eq_right hG]
      nlinarith
    · rw [max_eq_left (le_of_not_ge hG)]
      nlinarith
  · simp [exteriorPositive, exterior, he, hcenter v he]

/-- Weak duality for the complete L1-Fourier fragment. All Fourier identities,
inversion, Fubini, and real-integral inequalities are proved from Mathlib.
No literature source predicate, numerical result, or prime-gap claim is assumed.
The restriction that the genuine Fourier transform G is integrable is explicit;
it includes the Gaussian and compact-hat witnesses actually used here. -/
theorem weak_duality_l1 (F G V : ℝ → ℝ) (A M : ℝ)
    (hF : Integrable F) (hG : Integrable G) (hV : Integrable V)
    (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hA : 1 ≤ A)
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1)
    (hkernel : ∀ x : ℝ, |cosineTransform V x| ≤ M) :
    F 0 - A * (∫ v in exterior, max 0 (G v)) ≤
      M * (∫ x : ℝ, |F x|) := by
  have hVbound : ∀ v : ℝ, |V v| ≤ A := by
    intro v
    by_cases he : 1 < |v|
    · exact abs_le.mpr ⟨by linarith [hlower v he], by linarith [hupper v he]⟩
    · rw [hcenter v he, abs_one]
      exact hA
  have hGV : Integrable (fun v : ℝ => G v * V v) :=
    hG.mul_bdd hV.aestronglyMeasurable (ae_of_all _ (by
      intro v
      simpa only [Real.norm_eq_abs] using hVbound v))
  have hpen := exteriorPositive_integrable G hG
  have hzero := integral_transform_eq_value_zero F G hF hG hcont hfourier
  have hle := integral_mono (hG.sub (hpen.const_mul A)) hGV
    (dual_pointwise G V A hcenter hlower hupper)
  change (∫ v : ℝ, G v - A * exteriorPositive G v) ≤
    (∫ v : ℝ, G v * V v) at hle
  rw [integral_sub hG (hpen.const_mul A), integral_const_mul] at hle
  rw [hzero, exteriorPositive, integral_indicator exterior_measurable] at hle
  have hcos : cosineTransform F = G := by
    funext v
    rw [cosineTransform_eq_re_fourier F hF v, hfourier]
    rfl
  have hpair := cosine_pairing F V hF hV
  rw [hcos] at hpair
  rw [hpair] at hle
  have hFK : Integrable (fun x : ℝ => F x * cosineTransform V x) := by
    have hp := (integrable_cosine_product F V hF hV).integral_prod_left
    convert hp using 1
    funext x
    unfold cosineTransform
    rw [← integral_const_mul]
    congr 1
    funext v
    ring_nf
  have hFM : Integrable (fun x : ℝ => |F x| * M) := by
    simpa only [Real.norm_eq_abs] using hF.norm.mul_const M
  have hpoint : ∀ x : ℝ, F x * cosineTransform V x ≤ |F x| * M := by
    intro x
    calc
      F x * cosineTransform V x ≤ |F x * cosineTransform V x| := le_abs_self _
      _ = |F x| * |cosineTransform V x| := abs_mul _ _
      _ ≤ |F x| * M := mul_le_mul_of_nonneg_left (hkernel x) (abs_nonneg _)
  have hu := integral_mono hFK hFM hpoint
  rw [integral_mul_const] at hu
  nlinarith

#print axioms weak_duality_l1

end RH080.Dual
