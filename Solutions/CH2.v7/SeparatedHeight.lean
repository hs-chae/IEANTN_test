/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Section81Hardin
import GeneralTitch

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2Section81

/-- The existing CH2 discrete height selection needs zero counts, but no RH assumption. -/
theorem exists_separated_height (hrvm : ZeroCount.v1.rvm_error_bound)
    {T : ℝ} (hT : 2000 ≤ T) :
    ∃ t Δ : ℝ, T - 1 / 2 ≤ t ∧ t + 1 / 4 ≤ T ∧ 0 < Δ ∧
      1 / Δ ≤ 8 * (0.52 * Real.log T + 5) ∧
      (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ t) ∧
      (∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
        Δ ≤ |t - ρ.im|) := by
  classical
  have hT1000 : 1000 ≤ T := by linarith
  set R := Real.log T with hR
  -- the zeros in `(T - 3/4, T]` and their ordinates
  have hZ := CH2Section7Z.finite_zeros_Ioc (a := T - 3 / 4) (b := T) (by linarith)
  set G : Finset ℝ := hZ.toFinset.image Complex.im with hG
  set n := G.card with hn
  have hncard : (n : ℝ) ≤ 0.52 * R + 4 := by
    have h1 : n ≤ hZ.toFinset.card := Finset.card_image_le
    have h2 : (hZ.toFinset.card : ℝ) ≤ ∑ ρ ∈ hZ.toFinset, (1 : ℝ) * (IEANTN.zetaOrder ρ : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_le_sum fun ρ hρ ↦ ?_
      have hρ' := (Set.Finite.mem_toFinset hZ).mp hρ
      have hne : ρ ≠ 1 := fun h ↦ by
        have := hρ'.2.1.1; rw [h] at this; simp at this; linarith
      have := CH2Section6.one_le_zetaOrder hne hρ'.2.2
      rw [one_mul]; exact_mod_cast this
    have h3 := window_count_le hrvm hT1000
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hZ] at h3
    have h1' : (n : ℝ) ≤ hZ.toFinset.card := by exact_mod_cast h1
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set h : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨j, hj, hjfar⟩ := exists_far_point G (T - 1 / 2) hh0
  set t : ℝ := T - 1 / 2 + j * h with ht
  have hjh0 : 0 ≤ (j : ℝ) * h := by positivity
  have hjh : (j : ℝ) * h ≤ 1 / 4 := by
    have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
    calc (j : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hj' hh0.le
      _ ≤ 1 / 4 := by rw [hh, ← mul_div_assoc, div_le_iff₀ (by positivity)]; linarith
  have ht1 : T - 1 / 2 ≤ t := by linarith
  have ht2 : t + 1 / 4 ≤ T := by linarith
  have ht1000 : 1000 ≤ t := by linarith
  set Δ : ℝ := 1 / (8 * ((n : ℝ) + 1)) with hΔ
  have hΔh : h / 2 = Δ := by rw [hh, hΔ]; field_simp; ring
  have hΔ0 : 0 < Δ := by positivity
  have hwin : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (T - 3 / 4) T) := fun ρ hρ ↦
    ⟨trivial, ⟨by linarith [hρ.2.1.1], by linarith [hρ.2.1.2]⟩, hρ.2.2⟩
  have hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im| := by
    intro ρ hρ
    have hmem : ρ.im ∈ G := Finset.mem_image.mpr ⟨ρ, (Set.Finite.mem_toFinset hZ).mpr (hwin ρ hρ), rfl⟩
    rw [← hΔh]
    exact hjfar _ hmem
  refine ⟨t, Δ, ht1, ht2, hΔ0, ?_, ?_, hfar⟩
  · rw [hΔ, one_div_one_div]
    linarith
  · intro z hz habs
    have hz' : ∃ w : ℂ, riemannZeta w = 0 ∧ w.im = t := by
      rcases abs_eq (by linarith : (0 : ℝ) ≤ t) |>.mp habs with h | h
      · exact ⟨z, hz, h⟩
      · refine ⟨(starRingEnd ℂ) z, ?_, by simp [h]⟩
        rw [riemannZeta_conj, hz, map_zero]
    obtain ⟨w, hw, hwt⟩ := hz'
    have hmem : w ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
      ⟨trivial, ⟨by linarith, by linarith⟩, hw⟩
    have := hfar w hmem
    rw [hwt, sub_self, abs_zero] at this
    linarith

end CH2QRH
