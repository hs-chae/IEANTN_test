/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityLayer

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- Partial summation for an arbitrary finite weighted set above the lower height.
This supports strict real-part filtering without a new analytic assumption. -/
theorem finite_weighted_partial_sum {α : Type*} (S : Finset α) (γ w : α → ℝ)
    {H T : ℝ} (hHT : H ≤ T) (hγ : ∀ z ∈ S, H < γ z ∧ γ z ≤ T)
    {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc H T, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc H T)) :
    (∑ z ∈ S, w z * φ (γ z)) = φ T * (∑ z ∈ S, w z) -
      (∫ t in H..T, φ' t * (∑ z ∈ S, if γ z ≤ t then w z else 0)) ∧
    IntervalIntegrable (fun t ↦ φ' t * (∑ z ∈ S, if γ z ≤ t then w z else 0)) volume H T := by
  classical
  have hφ'int : IntegrableOn φ' (Set.Icc H T) := by
    rw [← Set.uIcc_of_le hHT]; exact hc.integrableOn_compact isCompact_uIcc
  have hftc : ∀ γ : ℝ, H < γ → γ ≤ T →
      φ γ = φ T - ∫ t in H..T, (Set.Ici γ).indicator φ' t := by
    intro γ hγ0 hγ1
    have hI : (∫ t in H..T, (Set.Ici γ).indicator φ' t) = ∫ t in γ..T, φ' t := by
      rw [intervalIntegral.integral_of_le hHT, intervalIntegral.integral_of_le hγ1,
        integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        show Set.Ici γ ∩ Set.Ioc H T = Set.Icc γ T by
          ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩,
        integral_Icc_eq_integral_Ioc]
    rw [hI, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hd t (by
        rw [Set.uIcc_of_le hγ1] at ht; rw [Set.uIcc_of_le hHT]; exact ⟨by linarith [ht.1], ht.2⟩))
      ((hc.mono (by rw [Set.uIcc_of_le hγ1, Set.uIcc_of_le hHT]; exact Set.Icc_subset_Icc_left hγ0.le)).intervalIntegrable)]
    ring
  -- the swap
  have hind_int : ∀ γ : ℝ, IntervalIntegrable ((Set.Ici γ).indicator φ') volume H T := by
    intro γ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hHT]
    exact hφ'int.indicator measurableSet_Ici
  have hi : ∀ z ∈ S, IntervalIntegrable
      (fun t ↦ w z * (Set.Ici (γ z)).indicator φ' t) volume H T := by
    intro z _
    exact (hind_int (γ z)).const_mul _
  have he : ∀ t : ℝ, (∑ z ∈ S, w z * (Set.Ici (γ z)).indicator φ' t) =
      φ' t * (∑ z ∈ S, if γ z ≤ t then w z else 0) := by
    intro t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : γ z ≤ t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ici (γ z) from h), if_pos h]
      ring
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ici (γ z) from h), if_neg h]
      ring
  have hswap : (∑ z ∈ S, w z * (∫ t in H..T, (Set.Ici (γ z)).indicator φ' t)) =
      ∫ t in H..T, φ' t * (∑ z ∈ S, if γ z ≤ t then w z else 0) := by
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum hi]
    apply intervalIntegral.integral_congr
    intro t _
    exact he t
  have hint : IntervalIntegrable (fun t ↦ φ' t *
      (∑ z ∈ S, if γ z ≤ t then w z else 0)) volume H T := by
    have hh := IntervalIntegrable.sum S hi
    refine hh.congr ?_
    intro t _
    simpa only [Finset.sum_apply] using he t
  refine ⟨?_, hint⟩
  rw [← hswap, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hftc (γ z) (hγ z hz).1 (hγ z hz).2]
  ring

/-- The reciprocal-height tail identity used to turn a zero density bound into a weight bound. -/
theorem finite_reciprocal_partial_sum {α : Type*} (S : Finset α) (γ w : α → ℝ)
    {H T : ℝ} (hH : 0 < H) (hHT : H ≤ T)
    (hγ : ∀ z ∈ S, H < γ z ∧ γ z ≤ T) :
    (∑ z ∈ S, w z / γ z) = (∑ z ∈ S, w z) / T +
      (∫ t in H..T, (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2) ∧
    IntervalIntegrable (fun t ↦ (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2) volume H T := by
  have hd : ∀ t ∈ Set.uIcc H T, HasDerivAt (fun u : ℝ ↦ 1 / u) (-1 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hHT] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    simpa only [neg_div, one_div] using hasDerivAt_inv ht0
  have hc : ContinuousOn (fun t : ℝ ↦ -1 / t ^ 2) (Set.uIcc H T) := by
    intro t ht
    rw [Set.uIcc_of_le hHT] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun u : ℝ ↦ -1 / u ^ 2) t).continuousWithinAt
  obtain ⟨heq, hint⟩ := finite_weighted_partial_sum S γ w hHT hγ hd hc
  have he : (fun t : ℝ ↦ -1 / t ^ 2 * (∑ z ∈ S, if γ z ≤ t then w z else 0)) =
      -(fun t : ℝ ↦ (∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2) := by
    funext t
    simp only [Pi.neg_apply]
    ring
  rw [he] at heq hint
  change (∑ z ∈ S, w z * (1 / γ z)) = (1 / T) * (∑ z ∈ S, w z) -
    (∫ t in H..T, -((∑ z ∈ S, if γ z ≤ t then w z else 0) / t ^ 2)) at heq
  rw [intervalIntegral.integral_neg, sub_neg_eq_add] at heq
  refine ⟨?_, ?_⟩
  · simpa only [mul_one_div, one_div_mul_eq_div] using heq
  · simpa only [neg_neg] using hint.neg

end CH2QRH
