/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CompactDualStep
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080.Dual

lemma cosine_integrand_integrable (V : ℝ → ℝ) (hV : Integrable V) (x : ℝ) :
    Integrable (fun v : ℝ => V v * cos (2*π*v*x)) := by
  apply hV.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with v
    simpa only [Real.norm_eq_abs] using abs_cos_le_one (2*π*v*x)

/-- Integrating the proved cosine chord inequality gives a continuum bound
for an actual Fourier integral. This never replaces a continuum by samples. -/
theorem cosine_kernel_chord (V : ℝ → ℝ) (hV : Integrable V)
    (hMoment : Integrable (fun v : ℝ => |V v| *v^2))
    (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |cosineTransform V ((1-t)*a+t*b) -
      ((1-t)*cosineTransform V a+t*cosineTransform V b)| ≤
      (π^2*(b-a)^2/2)*(∫ v : ℝ, |V v| *v^2) := by
  let error : ℝ → ℝ := fun v => V v *
    (cos (2*π*v*((1-t)*a+t*b)) -
      ((1-t)*cos (2*π*v*a)+t*cos (2*π*v*b)))
  have heq : error = (fun v : ℝ => V v*cos (2*π*v*((1-t)*a+t*b))) -
      ((fun v : ℝ => (1-t)*(V v*cos (2*π*v*a))) +
        (fun v : ℝ => t*(V v*cos (2*π*v*b)))) := by
    funext v
    simp only [error, Pi.sub_apply, Pi.add_apply]
    ring
  have ha := cosine_integrand_integrable V hV a
  have hb := cosine_integrand_integrable V hV b
  have hx := cosine_integrand_integrable V hV ((1-t)*a+t*b)
  have herr : Integrable error := by
    rw [heq]
    exact hx.sub ((ha.const_mul (1-t)).add (hb.const_mul t))
  have hident : (∫ v : ℝ, error v) =
      cosineTransform V ((1-t)*a+t*b) -
      ((1-t)*cosineTransform V a+t*cosineTransform V b) := by
    rw [heq]
    change (∫ v : ℝ, V v*cos (2*π*v*((1-t)*a+t*b)) -
      ((1-t)*(V v*cos (2*π*v*a))+t*(V v*cos (2*π*v*b)))) = _
    have hsum : Integrable (fun v : ℝ => (1-t)*(V v*cos (2*π*v*a))+
        t*(V v*cos (2*π*v*b))) := (ha.const_mul (1-t)).add (hb.const_mul t)
    rw [integral_sub hx hsum,
      integral_add (ha.const_mul (1-t)) (hb.const_mul t),
      integral_const_mul, integral_const_mul]
    rfl
  have hbound : ∀ v : ℝ, |error v| ≤ (π^2*(b-a)^2/2)*(|V v| *v^2) := by
    intro v
    have hc := scaled_cosine_chord_error a b t v ht0 ht1
    have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg (V v))
    dsimp [error]
    rw [abs_mul]
    calc
      _ ≤ |V v| *(π^2*v^2*(b-a)^2/2) := hm
      _ = _ := by ring
  have hi : Integrable (fun v : ℝ => (π^2*(b-a)^2/2)*(|V v| *v^2)) :=
    hMoment.const_mul _
  have hu := integral_mono herr.norm hi (fun v => by
    simpa only [Real.norm_eq_abs] using hbound v)
  have hn := norm_integral_le_integral_norm (μ := volume) error
  rw [Real.norm_eq_abs, hident] at hn
  rw [integral_const_mul] at hu
  exact hn.trans hu

lemma compact_kernel_cell_error (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwidth : b-a = (1/128 : ℝ)) :
    |cosineTransform compactStep ((1-t)*a+t*b) -
      ((1-t)*cosineTransform compactStep a+t*cosineTransform compactStep b)| ≤
      (674585 / 134217728 : ℝ) := by
  have hc := cosine_kernel_chord compactStep compactStep_integrable
    compactStep_moment_integrable a b t ht0 ht1
  have hp : π^2 ≤ (10 : ℝ) := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hm := compactStep_moment_le
  have hnonneg : 0 ≤ (∫ v : ℝ, |compactStep v| *v^2) := by positivity
  rw [hwidth] at hc
  have ht := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ π^2*(1/128 : ℝ)^2/2)
  have ht' := mul_le_mul_of_nonneg_right hp
    (by norm_num : (0 : ℝ) ≤ (1/128)^2/2*(134917/8192))
  nlinarith

#print axioms cosine_kernel_chord
#print axioms compact_kernel_cell_error
end RH080.Dual
