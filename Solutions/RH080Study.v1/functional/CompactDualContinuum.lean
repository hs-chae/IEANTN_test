/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import KernelInterpolation
import FunctionalObstruction

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

lemma cosineTransform_neg (V : ℝ → ℝ) (x : ℝ) :
    cosineTransform V (-x) = cosineTransform V x := by
  unfold cosineTransform
  congr 1
  funext v
  rw [show 2*π*v*(-x) = -(2*π*v*x) by ring, cos_neg]

lemma compactNumerator_reflect (x : ℝ) :
    compactNumerator (4-x) = -compactNumerator x := by
  unfold compactNumerator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show π*(j+1)*(4-x)/2 = (j+1 : ℕ)*(2*π)-π*(j+1)*x/2 by push_cast; ring,
    sin_nat_mul_two_pi_sub]
  ring

lemma compactNumerator_abs_le (x : ℝ) :
    |compactNumerator x| ≤ (3192/256 : ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j ∈ Finset.range 20,
      |((jumpCoeff j : ℝ)/256)*sin (π*(j+1)*x/2)|) ≤
        ∑ j ∈ Finset.range 20, |(jumpCoeff j : ℝ)/256| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _)).trans_eq
        (mul_one _)
    _ = _ := by norm_num [Finset.sum_range_succ, jumpCoeff, height]

lemma compact_kernel_tail (x : ℝ) (hx : 4 ≤ |x|) :
    |cosineTransform compactStep x| ≤ 1 := by
  have hnx : x ≠ 0 := by intro h; subst x; norm_num at hx
  rw [compact_kernel_sine x hnx, abs_div, abs_mul, abs_of_pos pi_pos]
  apply (div_le_iff₀ (mul_pos pi_pos (by linarith : 0 < |x|))).2
  have hN := compactNumerator_abs_le x
  have hp := pi_gt_d2
  nlinarith

lemma compact_kernel_reflection_le (x : ℝ) (hx : 2 ≤ x) (hupper : x < 4) :
    |cosineTransform compactStep x| ≤ |cosineTransform compactStep (4-x)| := by
  have hxp : 0 < x := by linarith
  have hr : 0 < 4-x := by linarith
  rw [compact_kernel_sine x (ne_of_gt hxp), compact_kernel_sine (4-x) (ne_of_gt hr),
    compactNumerator_reflect, abs_div, abs_div, abs_neg,
    abs_of_pos (mul_pos pi_pos hxp), abs_of_pos (mul_pos pi_pos hr)]
  apply (div_le_div_iff₀ (mul_pos pi_pos hxp) (mul_pos pi_pos hr)).2
  have hd : π*(4-x) ≤ π*x := mul_le_mul_of_nonneg_left (by linarith) pi_pos.le
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)

lemma absolute_chord_bound (a b t C : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : |a| ≤ C) (hb : |b| ≤ C) : |(1-t)*a+t*b| ≤ C := by
  calc
    |(1-t)*a+t*b| ≤ |(1-t)*a|+|t*b| := abs_add_le _ _
    _ = (1-t)*|a|+t*|b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-t), abs_of_nonneg ht0]
    _ ≤ (1-t)*C+t*C := add_le_add
      (mul_le_mul_of_nonneg_left ha (by linarith)) (mul_le_mul_of_nonneg_left hb ht0)
    _ = C := by ring

lemma compact_kernel_on_core
    (hgrid : ∀ k : ℕ, k ≤ 256 →
      |cosineTransform compactStep ((k : ℝ)/128)| ≤ (611/500 : ℝ))
    (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    |cosineTransform compactStep x| ≤ (123/100 : ℝ) := by
  by_cases heq : x = 2
  · subst x
    have hg := hgrid 256 (by omega)
    norm_num at hg
    linarith
  have hxlt : x < 2 := by
    rcases lt_or_eq_of_le hx2 with h | h
    · exact h
    · exact False.elim (heq h)
  let k : ℕ := ⌊128*x⌋₊
  have hk : k < 256 := by
    apply (Nat.floor_lt (by positivity : 0 ≤ 128*x)).2
    norm_num
    nlinarith
  have hkle : (k : ℝ) ≤ 128*x := Nat.floor_le (by positivity)
  have hklt : 128*x < (k : ℝ)+1 := Nat.lt_floor_add_one _
  let a : ℝ := (k : ℝ)/128
  let b : ℝ := ((k+1 : ℕ) : ℝ)/128
  let t : ℝ := 128*x-k
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hw : b-a = (1/128 : ℝ) := by dsimp [a,b]; push_cast; ring
  have he : (1-t)*a+t*b = x := by dsimp [a,b,t]; push_cast; ring
  have ha : |cosineTransform compactStep a| ≤ (611/500 : ℝ) := hgrid k (by omega)
  have hb : |cosineTransform compactStep b| ≤ (611/500 : ℝ) := hgrid (k+1) (by omega)
  have hc := compact_kernel_cell_error a b t ht0 ht1 hw
  rw [he] at hc
  have hline := absolute_chord_bound
    (cosineTransform compactStep a) (cosineTransform compactStep b) (t) (611/500) ht0 ht1 ha hb
  have htri := abs_sub_le (cosineTransform compactStep x)
    ((1-t)*cosineTransform compactStep a+t*cosineTransform compactStep b) 0
  simp only [sub_zero] at htri
  nlinarith

/-- All-real Fourier-kernel bound from a finite grid and the proved integral,
interpolation, reflection, and tail estimates. The finite grid must be supplied
by the actual source-program verification path, never assumed as execution. -/
theorem compact_kernel_global_of_grid
    (hgrid : ∀ k : ℕ, k ≤ 256 →
      |cosineTransform compactStep ((k : ℝ)/128)| ≤ (611/500 : ℝ)) :
    ∀ x : ℝ, |cosineTransform compactStep x| ≤ (123/100 : ℝ) := by
  intro x
  have habs : cosineTransform compactStep |x| = cosineTransform compactStep x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), cosineTransform_neg]
  rw [← habs]
  by_cases htail : 4 ≤ |x|
  · exact (compact_kernel_tail |x| (by simpa only [abs_abs] using htail)).trans (by norm_num)
  by_cases hcore : |x| ≤ 2
  · exact compact_kernel_on_core hgrid |x| (abs_nonneg _) hcore
  · have hr : 0 ≤ 4-|x| := by linarith
    have hr2 : 4-|x| ≤ 2 := by linarith
    exact (compact_kernel_reflection_le |x| (by linarith) (by linarith)).trans
      (compact_kernel_on_core hgrid (4-|x|) hr hr2)

/-- Source-verified finite-grid bounds, once supplied, imply a complete
restricted-functional obstruction for every genuine L1 Fourier pair. -/
theorem compact_functional_obstruction
    (hgrid : ∀ k : ℕ, k ≤ 256 →
      |cosineTransform compactStep ((k : ℝ)/128)| ≤ (611/500 : ℝ))
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hden : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (4/5 : ℝ) < (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) := by
  have hweak := weak_duality_l1 F G compactStep (36/11) (123/100)
    hF hG compactStep_integrable hcont hfourier (by norm_num)
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1) (fun v _ => (compactStep_bounds v).2)
    (compact_kernel_global_of_grid hgrid)
  apply RH080.Functional.compact_dual_excludes_four_fifths (by nlinarith) hden hweak

#print axioms compact_kernel_global_of_grid
#print axioms compact_functional_obstruction
end RH080.Dual
