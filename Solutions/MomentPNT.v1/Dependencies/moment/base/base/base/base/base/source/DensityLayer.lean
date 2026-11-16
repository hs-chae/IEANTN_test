/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedSpectral

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- A strict real-part cutoff has the expected integral; its single endpoint is null. -/
theorem integral_strict_cutoff {a b c : ℝ} (hb : b ∈ Set.Icc a c) (f : ℝ → ℝ) :
    (∫ u in a..c, (Set.Iio b).indicator f u) = ∫ u in a..b, f u := by
  have he : (∫ u in a..c, (Set.Iio b).indicator f u) =
      ∫ u in a..c, (Set.Iic b).indicator f u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne b] with u hu
    intro _
    by_cases h : u < b
    · rw [Set.indicator_of_mem (show u ∈ Set.Iio b from h),
        Set.indicator_of_mem (show u ∈ Set.Iic b from h.le)]
    · have hgt : b < u := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hu)
      rw [Set.indicator_of_notMem (show u ∉ Set.Iio b from h),
        Set.indicator_of_notMem (show u ∉ Set.Iic b from not_le.mpr hgt)]
  rw [he]
  exact intervalIntegral.integral_indicator hb

/-- Layer decomposition of an individual zero contribution, with the strict density cutoff. -/
theorem rpow_layer_point_le {x a b β : ℝ} (hx : 1 ≤ x) (ha : a ≤ β) (hb : b ≤ β) :
    x ^ (b - 1) ≤ x ^ (a - 1) + Real.log x *
      (∫ σ in a..β, (Set.Iio b).indicator (fun u ↦ x ^ (u - 1)) σ) := by
  have hx0 : 0 < x := by linarith
  have hf : Continuous (fun u : ℝ ↦ x ^ (u - 1)) := by fun_prop (disch := positivity)
  have hfi : IntegrableOn (fun u : ℝ ↦ x ^ (u - 1)) (Set.Icc a β) :=
    hf.continuousOn.integrableOn_Icc
  have hcont : IntervalIntegrable ((Set.Iio b).indicator (fun u : ℝ ↦ x ^ (u - 1)))
      volume a β := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha]
    exact hfi.indicator measurableSet_Iio
  by_cases hba : b ≤ a
  · have hi : (∫ σ in a..β, (Set.Iio b).indicator (fun u ↦ x ^ (u - 1)) σ) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with u hu
      rw [Set.uIoc_of_le ha] at hu
      exact Set.indicator_of_notMem (by have hh := hu.1; change ¬ u < b; linarith) _
    rw [hi, mul_zero, add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  · have hab : a ≤ b := le_of_lt (lt_of_not_ge hba)
    rw [integral_strict_cutoff ⟨hab, hb⟩]
    have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun v : ℝ ↦ x ^ (v - 1))
        (Real.log x * x ^ (u - 1)) u := by
      intro u _
      simpa only [id_eq, one_mul, mul_one, mul_comm] using
        ((hasDerivAt_id u).sub_const 1).const_rpow hx0
    have hi : IntervalIntegrable (fun u : ℝ ↦ Real.log x * x ^ (u - 1)) volume a b := by
      exact (continuous_const.mul hf).intervalIntegrable _ _
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    rw [intervalIntegral.integral_const_mul] at he
    linarith

/-- The layer integral of a finite weighted zero sum; multiplicities can be put in the weight. -/
theorem finite_weighted_density_layer {α : Type*} (S : Finset α)
    (w b : α → ℝ) {x a β : ℝ} (hx : 1 ≤ x) (ha : a ≤ β)
    (hw : ∀ z ∈ S, 0 ≤ w z) (hb : ∀ z ∈ S, b z ≤ β) :
    ∑ z ∈ S, w z * x ^ (b z - 1) ≤
      x ^ (a - 1) * (∑ z ∈ S, w z) + Real.log x *
        (∫ σ in a..β, x ^ (σ - 1) * (∑ z ∈ S, if σ < b z then w z else 0)) := by
  classical
  have hx0 : 0 < x := by linarith
  have hf : Continuous (fun u : ℝ ↦ x ^ (u - 1)) := by fun_prop (disch := positivity)
  have hfi : IntegrableOn (fun u : ℝ ↦ x ^ (u - 1)) (Set.Icc a β) :=
    hf.continuousOn.integrableOn_Icc
  have hind : ∀ z ∈ S, IntervalIntegrable
      ((Set.Iio (b z)).indicator (fun u : ℝ ↦ x ^ (u - 1))) volume a β := by
    intro z _
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha]
    exact hfi.indicator measurableSet_Iio
  have hswap : (∑ z ∈ S, w z *
      (∫ σ in a..β, (Set.Iio (b z)).indicator (fun u ↦ x ^ (u - 1)) σ)) =
      ∫ σ in a..β, ∑ z ∈ S, w z *
        (Set.Iio (b z)).indicator (fun u ↦ x ^ (u - 1)) σ := by
    simp_rw [← intervalIntegral.integral_const_mul]
    exact (intervalIntegral.integral_finsetSum
      (fun z hz ↦ (hind z hz).const_mul (w z))).symm
  have hpt := Finset.sum_le_sum (s := S) (fun z hz ↦
    mul_le_mul_of_nonneg_left (rpow_layer_point_le hx ha (hb z hz)) (hw z hz))
  calc (∑ z ∈ S, w z * x ^ (b z - 1)) ≤
      ∑ z ∈ S, w z * (x ^ (a - 1) + Real.log x *
        (∫ σ in a..β, (Set.Iio (b z)).indicator (fun u ↦ x ^ (u - 1)) σ)) := hpt
    _ = x ^ (a - 1) * (∑ z ∈ S, w z) + Real.log x *
        (∑ z ∈ S, w z * (∫ σ in a..β, (Set.Iio (b z)).indicator (fun u ↦ x ^ (u - 1)) σ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = x ^ (a - 1) * (∑ z ∈ S, w z) + Real.log x *
        (∫ σ in a..β, ∑ z ∈ S, w z * (Set.Iio (b z)).indicator
          (fun u ↦ x ^ (u - 1)) σ) := by rw [hswap]
    _ = _ := by
      congr 2
      apply intervalIntegral.integral_congr
      intro σ _
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : σ < b z
      · rw [Set.indicator_of_mem (show σ ∈ Set.Iio (b z) from h), if_pos h]
        ring
      · rw [Set.indicator_of_notMem (show σ ∉ Set.Iio (b z) from h), if_neg h]
        ring

end CH2QRH
