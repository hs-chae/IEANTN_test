/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityGrid

open Complex Filter Topology Set MeasureTheory
set_option maxRecDepth 4000
namespace CH2QRH

/-- Reflection preserves convexity; this is the density real-part coordinate change. -/
theorem convexOn_reflect {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (β : ℝ) :
    ConvexOn ℝ Set.univ (fun y ↦ f (β - y)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have he : β - (a * x + b * y) = a * (β - x) + b * (β - y) := by
    linear_combination -β * hab
  rw [he]
  exact hf.2 trivial trivial ha hb hab

/-- The entire outer density integral is controlled by one fixed finite grid certificate. -/
theorem density_outer_grid_uniform {L₀ L τ t : ℝ} (hL0 : 64 ≤ L₀) (hL : L₀ ≤ L)
    (hτ : 28 ≤ τ) (hτH : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ Real.exp τ)
    (ht : Real.exp τ ≤ t) :
    L * (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ),
      Real.exp (-L * (7 / 8 - σ)) * finiteDensityWeight σ t) ≤ densityGridCertificate L₀ τ := by
  have htH := hτH.trans ht
  let f : ℝ → ℝ := fun y ↦ finiteDensityWeight (7 / 8 - y) t
  let a : ℕ → ℝ := fun i ↦ (i : ℝ) / 4096
  let q : ℕ → ℝ := fun i ↦ densityFixedEnvelope (7 / 8 - (i : ℝ) / 4096) τ
  have hf : ConvexOn ℝ Set.univ f := convexOn_reflect (finiteDensityWeight_convex htH) (7 / 8)
  have hc : Continuous f := (finiteDensityWeight_continuous htH).comp (continuous_const.sub continuous_id)
  have ha : ∀ i < 512, a i < a (i + 1) := by
    intro i _; dsimp [a]; push_cast; linarith
  have han : ∀ i ≤ 512, 0 ≤ a i := by intro i _; dsimp [a]; positivity
  have hσ : ∀ i : ℕ, i ≤ 512 → (3 / 4 : ℝ) ≤ 7 / 8 - (i : ℝ) / 4096 ∧
      7 / 8 - (i : ℝ) / 4096 ≤ 7 / 8 := by
    intro i hi
    have hcast : (i : ℝ) ≤ 512 := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    constructor <;> linarith
  have hq : ∀ i ≤ 512, f (a i) ≤ q i := by
    intro i hi
    exact finiteDensityWeight_le_fixed (hσ i hi).1 (hσ i hi).2 hτ hτH ht
  have hmono : ∀ i < 512, q i ≤ q (i + 1) := by
    intro i hi
    apply densityFixedEnvelope_antitone hτ (hσ (i + 1) (by omega)) (hσ i hi.le)
    push_cast; linarith
  have hgrid := laplace_convex_grid_uniform hf hc (by linarith : 0 ≤ L₀) hL
    (by norm_num [a]) ha han hq hmono
  have hcap : 0 ≤ q 512 * Real.exp (-L * a 512) := by
    exact mul_nonneg (densityFixedEnvelope_nonneg (hσ 512 le_rfl).1 (hσ 512 le_rfl).2 hτ)
      (Real.exp_pos _).le
  have hmass : ∀ i : ℕ, a (i + 1) - a i = (1 : ℝ) / 4096 := by
    intro i; dsimp [a]; push_cast; ring
  have hcert : q 0 + ∑ i ∈ Finset.range 512,
      (q (i + 1) - q i) / (a (i + 1) - a i) *
        (∫ y in a i..a (i + 1), Real.exp (-L₀ * y)) = densityGridCertificate L₀ τ := by
    unfold densityGridCertificate
    have hq0 : q 0 = densityFixedEnvelope (7 / 8) τ := by simp [q]
    rw [hq0]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hmass, laplace_cell_mass (by linarith : L₀ ≠ 0)]
    dsimp [a, q]
    push_cast
    simp only [mul_div_assoc]
    ring
  rw [hcert] at hgrid
  have hchange : (∫ y in a 0..a 512, Real.exp (-L * y) * f y) =
      ∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ),
        Real.exp (-L * (7 / 8 - σ)) * finiteDensityWeight σ t := by
    let F : ℝ → ℝ := fun σ ↦ Real.exp (-L * (7 / 8 - σ)) * finiteDensityWeight σ t
    have he : (fun y ↦ F (7 / 8 - y)) = (fun y ↦ Real.exp (-L * y) * f y) := by
      funext y
      dsimp [F, f]
      congr 1; congr 1; ring
    have hh := intervalIntegral.integral_comp_sub_left (f := F)
      (a := 0) (b := (1 / 8 : ℝ)) (7 / 8)
    rw [he] at hh
    norm_num [a, F] at hh ⊢
    exact hh
  rw [hchange] at hgrid
  exact (le_add_of_nonneg_right hcap).trans hgrid

end CH2QRH
