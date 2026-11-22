/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao, OpenAI (Codex)
-/
import Section7Zeros

/-! Exact finite-zero Abel identity, extracted from the unchanged CH2 proof.
No zero-count approximation, RH, or numerical zero table is assumed. -/
open Complex Filter Topology Set MeasureTheory
namespace RHContinuation.ZeroAbel
open CH2Section7Z

theorem exact_finite {t₀ t₁ : ℝ} (h1 : 1 ≤ t₀) (h01 : t₀ ≤ t₁)
    {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc t₀ t₁)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im) =
      φ t₁ * (ZeroCount.v1.zetaNClosed t₁ - ZeroCount.v1.zetaNClosed t₀) -
        ∫ t in t₀..t₁, φ' t *
          (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀) := by
  have hπ := Real.pi_pos
  have ht0 : 0 < t₀ := by linarith
  set hfin := finite_zeros_Ioc (a := 0) (b := t₁) le_rfl
  set S := hfin.toFinset with hS
  set m : ℂ → ℝ := fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ) with hm
  have hm0 : ∀ ρ ∈ S, 0 ≤ m ρ := fun ρ hρ ↦
    zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self ((Set.Finite.mem_toFinset hfin).mp hρ)
  set c : ℝ → ℝ := fun t ↦ ∑ ρ ∈ S, (if ρ.im ≤ t then m ρ else 0) with hc_def
  -- the sum as a sum over `S`
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      = ∑ ρ ∈ S, (if t₀ < ρ.im then φ ρ.im * m ρ else 0) := by
    rw [zetaZeroesSum_eq_sum (finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le)]
    have hsub : (finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le).toFinset ⊆ S := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      exact ⟨hρ.1, ⟨ht0.trans hρ.2.1.1, hρ.2.1.2⟩, hρ.2.2⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
      rw [Set.Finite.mem_toFinset] at hρ
      rw [if_pos hρ.2.1.1]
    · intro ρ hρ hρ'
      rw [Set.Finite.mem_toFinset] at hρ hρ'
      rw [if_neg]
      intro hlt
      exact hρ' ⟨hρ.1, ⟨hlt, hρ.2.1.2⟩, hρ.2.2⟩
  -- per zero: `φ(γ) = φ(t₁) - ∫_{t₀}^{t₁} 1_{γ ≤ t} φ'(t) dt`
  have hφ'int : IntegrableOn φ' (Set.Icc t₀ t₁) := by
    rw [← Set.uIcc_of_le h01]; exact hc.integrableOn_compact isCompact_uIcc
  have hftc : ∀ γ : ℝ, t₀ < γ → γ ≤ t₁ →
      φ γ = φ t₁ - ∫ t in t₀..t₁, (Set.Ici γ).indicator φ' t := by
    intro γ hγ0 hγ1
    have hI : (∫ t in t₀..t₁, (Set.Ici γ).indicator φ' t) = ∫ t in γ..t₁, φ' t := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le hγ1,
        integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        show Set.Ici γ ∩ Set.Ioc t₀ t₁ = Set.Icc γ t₁ by
          ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩,
        integral_Icc_eq_integral_Ioc]
    rw [hI, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hd t (by
        rw [Set.uIcc_of_le hγ1] at ht; rw [Set.uIcc_of_le h01]; exact ⟨by linarith [ht.1], ht.2⟩))
      ((hc.mono (by rw [Set.uIcc_of_le hγ1, Set.uIcc_of_le h01]; exact Set.Icc_subset_Icc_left hγ0.le)).intervalIntegrable)]
    ring
  -- the swap
  have hind_int : ∀ γ : ℝ, IntervalIntegrable ((Set.Ici γ).indicator φ') volume t₀ t₁ := by
    intro γ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h01]
    exact hφ'int.indicator measurableSet_Ici
  have hswap : ∑ ρ ∈ S, (if t₀ < ρ.im then m ρ * ∫ t in t₀..t₁, (Set.Ici ρ.im).indicator φ' t else 0)
      = ∫ t in t₀..t₁, φ' t * (c t - c t₀) := by
    have e1 : ∀ ρ ∈ S, (if t₀ < ρ.im then m ρ * ∫ t in t₀..t₁, (Set.Ici ρ.im).indicator φ' t else 0)
        = ∫ t in t₀..t₁, (if t₀ < ρ.im then m ρ * (Set.Ici ρ.im).indicator φ' t else 0) := by
      intro ρ _
      split_ifs
      · rw [intervalIntegral.integral_const_mul]
      · simp
    rw [Finset.sum_congr rfl e1, ← intervalIntegral.integral_finset_sum]
    · refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le h01] at ht
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      by_cases h0 : t₀ < ρ.im
      · rw [if_pos h0, if_neg (not_le.mpr h0), sub_zero]
        by_cases h2 : ρ.im ≤ t
        · rw [Set.indicator_of_mem (show t ∈ Set.Ici ρ.im from h2), if_pos h2]; ring
        · rw [Set.indicator_of_notMem (show t ∉ Set.Ici ρ.im from h2), if_neg h2]; ring
      · rw [if_neg h0, if_pos (not_lt.mp h0), if_pos ((not_lt.mp h0).trans ht.1)]; ring
    · intro ρ _
      split_ifs
      · exact (hind_int ρ.im).const_mul _
      · exact intervalIntegrable_const
  have hmain : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      = φ t₁ * (c t₁ - c t₀) - ∫ t in t₀..t₁, φ' t * (c t - c t₀) := by
    rw [hsum, ← hswap]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
    by_cases h0 : t₀ < ρ.im
    · rw [if_pos h0, if_pos h0, if_neg (not_le.mpr h0), if_pos hρ'.2.1.2,
        hftc ρ.im h0 hρ'.2.1.2]
      ring
    · rw [if_neg h0, if_neg h0, if_pos (not_lt.mp h0), if_pos ((not_lt.mp h0).trans h01)]
      ring
  have hcN : ∀ t ∈ Set.Icc t₀ t₁,
      c t - c t₀ = ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀ := by
    intro t ht
    rw [zetaNClosed_eq_sum (by linarith [ht.1]) ht.2,
      zetaNClosed_eq_sum ht0.le h01]
  rw [hmain, hcN t₁ ⟨h01, le_rfl⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le h01] at ht
  change φ' t * (c t - c t₀) = φ' t *
    (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀)
  rw [hcN t ht]

#print axioms exact_finite
end RHContinuation.ZeroAbel
