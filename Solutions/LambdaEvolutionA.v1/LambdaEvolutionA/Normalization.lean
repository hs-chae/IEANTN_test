/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.MellinLimit
import Section9Cor13Sum

open Real Set MeasureTheory

namespace LambdaEvolutionA

/-- Finite Abel summation with the main logarithm separated exactly. -/
theorem lambda_finite_remainder
    (hI : IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1))
    {x : ℝ} (hx : 1 ≤ x) :
    CH2.v1.lambdaSum x - log x = Chebyshev.psi x / x +
      ∫ t in Ioc (1 : ℝ) x, (Chebyshev.psi t - t) / t ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk : IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2)
      (Ioc 1 x) := hI.mono_set Ioc_subset_Ioi_self
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc 1 x) := by
    intro t ht
    exact (continuousAt_id.inv₀ (by linarith [ht.1] : t ≠ 0)).continuousWithinAt
  have hm : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Ioc 1 x) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi : (∫ t in Ioc (1 : ℝ) x, (t ^ 2)⁻¹ * Chebyshev.psi t) =
      (∫ t in Ioc (1 : ℝ) x, t⁻¹) +
      ∫ t in Ioc (1 : ℝ) x, (Chebyshev.psi t - t) / t ^ 2 := by
    rw [← integral_add hm hk]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    dsimp only
    field_simp
    <;> ring
  have hv : (∫ t in Ioc (1 : ℝ) x, t⁻¹) = log x := by
    rw [← intervalIntegral.integral_of_le hx,
      integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hx0, div_one]
  have hab := CH2Section9.abel_lambda (x := 1) (X := x) (by norm_num) hx
  simp only [Chebyshev.psi_one, mul_zero, sub_zero, one_div] at hab
  have hA : CH2.v1.lambdaSum 1 = 0 := by
    rw [CH2Section9.lambdaSum_eq_Ioc]
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Nat.floor_one, Finset.mem_Ioc] at hn
    have hn1 : n = 1 := by omega
    subst n
    simp
  rw [hA, sub_zero, hi, hv] at hab
  rw [hab]
  simp only [div_eq_mul_inv]
  ring

/-- The exact Euler normalization removes the old fixed source floor.
This equality is conditional only on integrability of the actual psi remainder,
not on a new normalization or asymptotic source statement. -/
theorem lambda_tail_identity
    (hI : IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1))
    {x : ℝ} (hx : 1 ≤ x) :
    CH2.v1.lambdaSum x - log x + Real.eulerMascheroniConstant =
      (Chebyshev.psi x - x) / x -
      ∫ t in Ioi x, (Chebyshev.psi t - t) / t ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hI hx
  rw [intervalIntegral.integral_of_le hx] at hsplit
  have htotal := total_remainder_integral hI
  rw [htotal] at hsplit
  rw [lambda_finite_remainder hI hx]
  have hpsi : Chebyshev.psi x / x = (Chebyshev.psi x - x) / x + 1 := by
    field_simp
    <;> ring
  rw [hpsi]
  linarith

end LambdaEvolutionA

#print axioms LambdaEvolutionA.lambda_finite_remainder
#print axioms LambdaEvolutionA.lambda_tail_identity
