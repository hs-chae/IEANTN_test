/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTail
import DensityLayer

open Real Set MeasureTheory

namespace DirectIntervalA

/-- Clipping an ordinate to `U` makes its cumulative weight vanish strictly below `U`. -/
theorem clipped_cdf_zero {α : Type*} (S : Finset α) (γ w : α → ℝ)
    {U t : ℝ} (ht : t < U) :
    (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  exact if_neg (not_le.mpr (ht.trans_le (le_max_left U (γ z))))

/-- At and above the clipping height, the clipped and ordinary cumulative weights agree. -/
theorem clipped_cdf_eq {α : Type*} (S : Finset α) (γ w : α → ℝ)
    {U t : ℝ} (ht : U ≤ t) :
    (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) =
      ∑ z ∈ S, if γ z ≤ t then w z else 0 := by
  apply Finset.sum_congr rfl
  intro z _
  simp only [max_le_iff, ht, true_and]

/-- Exact finite Abel summation for reciprocal ordinates clipped from below.
There is no zero-free or finite-RH hypothesis: clipping is an arithmetic operation. -/
theorem finite_clipped_reciprocal_partial_sum {α : Type*} (S : Finset α)
    (γ w : α → ℝ) {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hγV : ∀ z ∈ S, γ z ≤ V) :
    (∑ z ∈ S, w z / max U (γ z)) = (∑ z ∈ S, w z) / V +
      (∫ t in U..V, (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2) ∧
    IntervalIntegrable
      (fun t ↦ (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2) volume U V := by
  have hhalf : U / 2 ≤ U := by linarith
  have hhalfV : U / 2 ≤ V := hhalf.trans hUV
  have hγ : ∀ z ∈ S, U / 2 < max U (γ z) ∧ max U (γ z) ≤ V := by
    intro z hz
    exact ⟨(by linarith [le_max_left U (γ z)]), max_le hUV (hγV z hz)⟩
  obtain ⟨hid, hi⟩ := CH2QRH.finite_reciprocal_partial_sum S
    (fun z ↦ max U (γ z)) w (by linarith : 0 < U / 2) hhalfV hγ
  have hiLo : IntervalIntegrable
      (fun t ↦ (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2)
      volume (U / 2) U := by
    apply hi.mono_set
    rw [uIcc_of_le hhalf, uIcc_of_le hhalfV]
    exact Icc_subset_Icc_right hUV
  have hiHi : IntervalIntegrable
      (fun t ↦ (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2)
      volume U V := by
    apply hi.mono_set
    rw [uIcc_of_le hUV, uIcc_of_le hhalfV]
    exact Icc_subset_Icc_left hhalf
  have hLo : (∫ t in (U / 2)..U,
      (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2) = 0 := by
    calc
      _ = ∫ t in (U / 2)..U, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hhalf
        intro t ht
        change (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2 = 0
        rw [clipped_cdf_zero S γ w ht.2, zero_div]
      _ = 0 := by simp
  have hHi : (∫ t in U..V,
      (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2) =
      ∫ t in U..V, (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hUV] at ht
    change (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2 =
      (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2
    rw [clipped_cdf_eq S γ w ht.1]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hiLo hiHi
  rw [← hsplit, hLo, zero_add, hHi] at hid
  refine ⟨hid, hiHi.congr ?_⟩
  intro t ht
  rw [uIoc_of_le hUV] at ht
  change (∑ z ∈ S, if max U (γ z) ≤ t then w z else 0) / t ^ 2 =
    (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2
  rw [clipped_cdf_eq S γ w ht.1.le]

/-- A bound on the actual cumulative weighted count from `U` to `V` controls the
clipped reciprocal sum, without assuming that there are no zeros below `U`. -/
theorem finite_clipped_reciprocal_majorant {α : Type*} (S : Finset α)
    (γ w : α → ℝ) {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hγV : ∀ z ∈ S, γ z ≤ V) (F : ℝ → ℝ)
    (hF : ContinuousOn F (uIcc U V))
    (hcount : ∀ t ∈ Icc U V, (∑ z ∈ S, if γ z ≤ t then w z else 0) ≤ F t) :
    (∑ z ∈ S, w z / max U (γ z)) ≤
      F V / V + ∫ t in U..V, F t / t ^ 2 := by
  obtain ⟨hid, hi⟩ := finite_clipped_reciprocal_partial_sum S γ w hU hUV hγV
  have hV : 0 < V := hU.trans_le hUV
  have hFi : IntervalIntegrable (fun t ↦ F t / t ^ 2) volume U V := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htc := ht
    rw [uIcc_of_le hUV] at htc
    have htpos : 0 < t := hU.trans_le htc.1
    exact (hF t ht).div (by fun_prop) (by positivity)
  have hI := intervalIntegral.integral_mono_on hUV hi hFi (fun t ht ↦
    div_le_div_of_nonneg_right (hcount t ht) (by positivity))
  have hC : (∑ z ∈ S, w z) ≤ F V := by
    have hh := hcount V ⟨hUV, le_rfl⟩
    have he : (∑ z ∈ S, if γ z ≤ V then w z else 0) = ∑ z ∈ S, w z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact if_pos (hγV z hz)
    rwa [he] at hh
  rw [hid]
  exact add_le_add (div_le_div_of_nonneg_right hC hV.le) hI

end DirectIntervalA

#print axioms DirectIntervalA.finite_clipped_reciprocal_majorant
