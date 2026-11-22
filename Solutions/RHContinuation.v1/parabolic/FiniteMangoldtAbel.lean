/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Exact real-endpoint finite Abel transport for actual Mangoldt and psi.
No RH, numerical table, logarithmic-integral identity or source predicate is used.
The identification of this finite weighted Mangoldt count with pi+Q is separate.
-/
namespace FiniteMangoldtAbel
open Real Finset ArithmeticFunction MeasureTheory Set
noncomputable def J (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n

theorem J_sub {a b : ℝ} (hab : a ≤ b) : J b - J a =
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n := by
  have hsub : Finset.Icc 0 ⌊a⌋₊ ⊆ Finset.Icc 0 ⌊b⌋₊ := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_le_floor hab)⟩
  have heq : Finset.Icc 0 ⌊b⌋₊ \ Finset.Icc 0 ⌊a⌋₊ =
      Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff_eq_sub (f := fun n : ℕ =>
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n) hsub
  rw [heq] at h
  exact h.symm

theorem psi_log_kernel_integrable {a b : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t : ℝ => Chebyshev.psi t / (t * Real.log t ^ 2))
      (Set.Ioc a b) volume := by
  have hc : IntegrableOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact (continuousAt_const.div (continuousAt_id.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog.ne'))).continuousWithinAt
  have h := integrableOn_mul_sum_Icc (fun n : ℕ =>
    (ArithmeticFunction.vonMangoldt n : ℝ)) (m := 0) (by linarith : 0 ≤ a) hc
  apply (h.mono_set Set.Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
  intro t ht
  dsimp only
  rw [← Chebyshev.psi_eq_sum_Icc]
  ring

/-- Actual finite Mangoldt/log Abel identity, with both ordinary endpoints. -/
theorem abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    J b - J a = Chebyshev.psi b / Real.log b - Chebyshev.psi a / Real.log a +
      ∫ t in Set.Ioc a b, Chebyshev.psi t / (t * Real.log t ^ 2) := by
  let f : ℝ → ℝ := fun t => (Real.log t)⁻¹
  have hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have h := (Real.hasDerivAt_log ht0.ne').inv hlog.ne'
    convert h using 1 <;> first | rfl | (field_simp [ht0.ne', hlog.ne'] <;> ring)
  have hi : IntegrableOn (fun t : ℝ => -(1 / (t * Real.log t ^ 2)))
      (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact ((continuousAt_const.div (continuousAt_id.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog.ne'))).neg).continuousWithinAt
  have hdi : IntegrableOn (deriv f) (Set.Icc a b) volume := by
    apply hi.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ =>
    (ArithmeticFunction.vonMangoldt n : ℝ)) (by linarith : 0 ≤ a) hab
      (fun t ht => (hd t ht).differentiableAt) hdi
  rw [J_sub hab]
  have hsum : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (ArithmeticFunction.vonMangoldt n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f]
    ring
  rw [hsum, h, ← Chebyshev.psi_eq_sum_Icc, ← Chebyshev.psi_eq_sum_Icc]
  have he : (∫ t in Set.Ioc a b,
      deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) =
      -(∫ t in Set.Ioc a b, Chebyshev.psi t / (t * Real.log t ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [he]
  dsimp [f]
  ring

#print axioms abel
end FiniteMangoldtAbel
