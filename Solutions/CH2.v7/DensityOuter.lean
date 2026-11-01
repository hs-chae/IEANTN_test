/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityHeight

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- Endpoint upper bounds give an affine upper bound for a convex integrand. -/
theorem convex_chord_bound {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b y A B : ℝ} (hab : a < b) (hy : y ∈ Set.Icc a b)
    (hA : f a ≤ A) (hB : f b ≤ B) :
    f y ≤ A + (B - A) / (b - a) * (y - a) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hα : 0 ≤ (b - y) / (b - a) := div_nonneg (by linarith [hy.2]) hd.le
  have hβ : 0 ≤ (y - a) / (b - a) := div_nonneg (by linarith [hy.1]) hd.le
  have hsum : (b - y) / (b - a) + (y - a) / (b - a) = 1 := by field_simp; ring
  have hpoint : (b - y) / (b - a) * a + (y - a) / (b - a) * b = y := by field_simp; ring
  have hh := hf.2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hsum
  simp only [smul_eq_mul, hpoint] at hh
  calc
    f y ≤ (b - y) / (b - a) * f a + (y - a) / (b - a) * f b := hh
    _ ≤ (b - y) / (b - a) * A + (y - a) / (b - a) * B := by gcongr
    _ = _ := by field_simp [hd.ne']; ring

/-- The exact finite-cell Laplace integral of the endpoint chord. -/
theorem laplace_chord_identity {L a b A B : ℝ} (hab : a < b) :
    L * (∫ y in a..b, Real.exp (-L * y) * (A + (B - A) / (b - a) * (y - a))) =
      A * Real.exp (-L * a) - B * Real.exp (-L * b) +
        (B - A) / (b - a) * (∫ y in a..b, Real.exp (-L * y)) := by
  let C : ℝ → ℝ := fun y ↦ A + (B - A) / (b - a) * (y - a)
  have hC : ∀ y : ℝ, HasDerivAt C ((B - A) / (b - a)) y := by
    intro y
    convert (hasDerivAt_const y A).add
      (((hasDerivAt_id y).sub_const a).const_mul ((B - A) / (b - a))) using 1 <;> first | rfl | simp | ring
  have hE : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ Real.exp (-L * y))
      (-L * Real.exp (-L * y)) y := by
    intro y
    convert Real.hasDerivAt_exp (-L * y) |>.comp y ((hasDerivAt_id y).const_mul (-L)) using 1 <;> first | rfl | ring
  have hder : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ ↦ - Real.exp (-L * y) * C y)
      (L * (Real.exp (-L * y) * C y) - (B - A) / (b - a) * Real.exp (-L * y)) y := by
    intro y _
    convert (hE y).neg.mul (hC y) using 1 <;> first | rfl | (simp only [Pi.neg_apply]; ring)
  have hi1 : IntervalIntegrable (fun y : ℝ ↦ L * (Real.exp (-L * y) * C y)) volume a b := by
    apply Continuous.intervalIntegrable; dsimp [C]; fun_prop
  have hi2 : IntervalIntegrable (fun y : ℝ ↦ (B - A) / (b - a) * Real.exp (-L * y)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  have hCa : C a = A := by dsimp [C]; ring
  have hCb : C b = B := by dsimp [C]; field_simp [(sub_pos.mpr hab).ne']; ring
  rw [hCa, hCb] at he
  dsimp [C] at he
  linarith

/-- A convex cell admits a certified endpoint bound for every positive Laplace parameter. -/
theorem laplace_convex_cell {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hc : Continuous f)
    {L a b A B : ℝ} (hL : 0 ≤ L) (hab : a < b) (hA : f a ≤ A) (hB : f b ≤ B) :
    L * (∫ y in a..b, Real.exp (-L * y) * f y) ≤
      A * Real.exp (-L * a) - B * Real.exp (-L * b) +
        (B - A) / (b - a) * (∫ y in a..b, Real.exp (-L * y)) := by
  have hi1 : IntervalIntegrable (fun y : ℝ ↦ Real.exp (-L * y) * f y) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun y : ℝ ↦ Real.exp (-L * y) *
      (A + (B - A) / (b - a) * (y - a))) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi := intervalIntegral.integral_mono_on hab.le hi1 hi2 (fun y hy ↦
    mul_le_mul_of_nonneg_left (convex_chord_bound hf hab hy hA hB) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left hi hL
  exact hh.trans_eq (laplace_chord_identity hab)

/-- All convex cells telescope to a finite endpoint certificate, including the far-end cap. -/
theorem laplace_convex_grid {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hc : Continuous f)
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {a q : ℕ → ℝ}
    (ha : ∀ i < n, a i < a (i + 1)) (hq : ∀ i ≤ n, f (a i) ≤ q i) :
    L * (∫ y in a 0..a n, Real.exp (-L * y) * f y) + q n * Real.exp (-L * a n) ≤
      q 0 * Real.exp (-L * a 0) +
        ∑ i ∈ Finset.range n, (q (i + 1) - q i) / (a (i + 1) - a i) *
          (∫ y in a i..a (i + 1), Real.exp (-L * y)) := by
  have hcells : ∀ i ∈ Finset.range n,
      L * (∫ y in a i..a (i + 1), Real.exp (-L * y) * f y) ≤
        q i * Real.exp (-L * a i) - q (i + 1) * Real.exp (-L * a (i + 1)) +
          (q (i + 1) - q i) / (a (i + 1) - a i) *
            (∫ y in a i..a (i + 1), Real.exp (-L * y)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    exact laplace_convex_cell hf hc hL (ha i hin) (hq i hin.le) (hq (i + 1) (by omega))
  have hs := Finset.sum_le_sum hcells
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
    (fun i _ ↦ (show Continuous (fun y : ℝ ↦ Real.exp (-L * y) * f y) by fun_prop).intervalIntegrable _ _),
    Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun i ↦ q i * Real.exp (-L * a i)) n] at hs
  linarith

/-- Each positive cell slope gives a decreasing continuation term on nonnegative ordinates. -/
theorem laplace_cell_mono {L₀ L a b : ℝ} (hL : L₀ ≤ L) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ y in a..b, Real.exp (-L * y)) ≤ ∫ y in a..b, Real.exp (-L₀ * y) := by
  have hi1 : IntervalIntegrable (fun y : ℝ ↦ Real.exp (-L * y)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun y : ℝ ↦ Real.exp (-L₀ * y)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  apply intervalIntegral.integral_mono_on hab hi1 hi2
  intro y hy
  apply Real.exp_le_exp.mpr
  have hy0 : 0 ≤ y := ha.trans hy.1
  nlinarith

/-- A monotone endpoint certificate controls the entire Laplace ray, not just its sample point. -/
theorem laplace_convex_grid_uniform {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hc : Continuous f)
    {L₀ L : ℝ} (hL0 : 0 ≤ L₀) (hL : L₀ ≤ L) {n : ℕ} {a q : ℕ → ℝ}
    (ha0 : a 0 = 0) (ha : ∀ i < n, a i < a (i + 1))
    (han : ∀ i ≤ n, 0 ≤ a i) (hq : ∀ i ≤ n, f (a i) ≤ q i)
    (hmono : ∀ i < n, q i ≤ q (i + 1)) :
    L * (∫ y in a 0..a n, Real.exp (-L * y) * f y) + q n * Real.exp (-L * a n) ≤
      q 0 + ∑ i ∈ Finset.range n, (q (i + 1) - q i) / (a (i + 1) - a i) *
        (∫ y in a i..a (i + 1), Real.exp (-L₀ * y)) := by
  have hfirst := laplace_convex_grid hf hc (hL0.trans hL) ha hq
  rw [ha0, mul_zero, Real.exp_zero, mul_one] at hfirst
  rw [ha0]
  apply hfirst.trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  apply mul_le_mul_of_nonneg_left (laplace_cell_mono hL (han i hin.le) (ha i hin).le)
  exact div_nonneg (sub_nonneg.mpr (hmono i hin)) (sub_pos.mpr (ha i hin)).le

end CH2QRH
