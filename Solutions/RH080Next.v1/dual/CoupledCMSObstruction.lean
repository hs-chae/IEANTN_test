/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CMSWeakDuality

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open RH080.Dual
namespace RH080Next.Dual

/-- A finite nonnegative coupling of the same CMS explicit-formula budgets
retains every common dual obstruction. Coupling alone cannot justify changing
the leakage penalty or remove the functional barrier. -/
theorem nonnegative_coupled_cms_bound {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (w : ι → ℝ) (V : ℝ → ℝ) (A M : ℝ)
    (hF : ∀ i ∈ s, Integrable (F i)) (hV : Integrable V)
    (hcont : ∀ i ∈ s, ContinuousAt (F i) 0)
    (heven : ∀ i ∈ s, Function.Even (F i))
    (hpen : ∀ i ∈ s, Integrable (exteriorPositive (cosineTransform (F i))))
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1)
    (hkernel : ∀ x : ℝ, |cosineTransform V x| ≤ M) :
    (∑ i ∈ s, w i * (F i 0 - A * (∫ v in exterior, max 0 (cosineTransform (F i) v)))) ≤
      M * (∑ i ∈ s, w i * (∫ x : ℝ, |F i x|)) := by
  calc
    _ ≤ ∑ i ∈ s, w i * (M * (∫ x : ℝ, |F i x|)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (weak_duality_even_cms (F i) V A M (hF i hi) hV (hcont i hi)
          (heven i hi) (hpen i hi) hcenter hlower hupper hkernel) (hw i hi)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

#print axioms nonnegative_coupled_cms_bound
end RH080Next.Dual
