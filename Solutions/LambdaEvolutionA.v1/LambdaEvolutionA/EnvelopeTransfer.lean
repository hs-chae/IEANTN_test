/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.TailTransfer
import LambdaEvolutionA.Normalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Exact log-square weighted-tail envelope. These elementary estimates are
the unverified-program baseline; they do not assert a numerical-program win. -/

namespace LambdaEvolutionA
open Real Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 400000

noncomputable def logSquareMajorant (t : ℝ) : ℝ :=
  log t ^ 2 * t ^ (-(9 : ℝ) / 8)

noncomputable def logSquareTailPrimitive (t : ℝ) : ℝ :=
  (8 * log t ^ 2 + 128 * log t + 1024) * t ^ (-(1 : ℝ) / 8)

theorem logSquareTailPrimitive_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt logSquareTailPrimitive (-logSquareMajorant t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hp := (((hl.pow 2).const_mul 8).add (hl.const_mul 128)).add_const 1024
  have hr := Real.hasDerivAt_rpow_const (x := t) (p := -(1 : ℝ) / 8) (Or.inl ht.ne')
  have hpower : t ^ (-(1 : ℝ) / 8) = t * t ^ (-(9 : ℝ) / 8) := by
    calc
      _ = t ^ ((1 : ℝ) + -(9 : ℝ) / 8) := by congr 1 <;> norm_num
      _ = t ^ (1 : ℝ) * t ^ (-(9 : ℝ) / 8) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  unfold logSquareTailPrimitive
  apply (hp.mul hr).congr_deriv
  norm_num only [logSquareMajorant, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [show t ^ (-(1 / 8 : ℝ)) = t * t ^ (-(9 / 8 : ℝ)) by
    simpa only [neg_div] using hpower]
  field_simp [ht.ne']
  <;> ring

#print axioms logSquareTailPrimitive_derivative

theorem logSquareTailPrimitive_tendsto_zero :
    Tendsto logSquareTailPrimitive atTop (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ ↦ log t ^ 2 / t ^ ((1 : ℝ) / 8)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun t : ℝ ↦ log t / t ^ ((1 : ℝ) / 8)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).tendsto_div_nhds_zero
  have h0 : Tendsto (fun t : ℝ ↦ t ^ (-(1 : ℝ) / 8)) atTop (𝓝 0) :=
    by simpa only [neg_div] using tendsto_rpow_neg_atTop (y := (1 / 8 : ℝ)) (by norm_num)
  have h := ((h2.const_mul 8).add (h1.const_mul 128)).add (h0.const_mul 1024)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp [logSquareTailPrimitive]
  rw [show (-(1 : ℝ) / 8) = -(1 / 8 : ℝ) by ring, Real.rpow_neg ht.le]
  ring

theorem integrableOn_logSquareMajorant {x : ℝ} (hx : 0 < x) :
    IntegrableOn logSquareMajorant (Ioi x) := by
  have hI := integrableOn_Ioi_deriv_of_nonpos'
    (fun t (ht : t ∈ Ici x) ↦ logSquareTailPrimitive_derivative (hx.trans_le ht))
    (fun t (ht : t ∈ Ioi x) ↦ by
      dsimp [logSquareMajorant]
      exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hx.trans ht).le _)))
    logSquareTailPrimitive_tendsto_zero
  exact integrable_neg_iff.mp hI

theorem integral_logSquareMajorant {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, logSquareMajorant t) = logSquareTailPrimitive x := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (ht : t ∈ Ici x) ↦ logSquareTailPrimitive_derivative (hx.trans_le ht))
    (integrableOn_logSquareMajorant hx).neg logSquareTailPrimitive_tendsto_zero
  simpa only [integral_neg, zero_sub, neg_inj] using h

theorem tail_integrand_le_logSquare {X A t : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ y ≥ X, IEANTN.Eψ y ≤ A * log y ^ 2 * y ^ (-(1 : ℝ) / 8))
    (ht : X ≤ t) : |psiTailIntegrand t| ≤ A * logSquareMajorant t := by
  have hp : 0 < t := lt_of_lt_of_le zero_lt_one (hX.trans ht)
  calc
    |psiTailIntegrand t| = IEANTN.Eψ t / t := by
      simp only [psiTailIntegrand, IEANTN.Eψ, abs_div, abs_of_nonneg (sq_nonneg t)]
      field_simp
    _ ≤ (A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) / t :=
      div_le_div_of_nonneg_right (hbound t ht) hp.le
    _ = A * logSquareMajorant t := by
      dsimp [logSquareMajorant]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one t]
      rw [mul_assoc (A * log t ^ 2), ← Real.rpow_add hp]
      norm_num
      ring

theorem integrableOn_tail_of_logSquare_bound {X A : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) :
    IntegrableOn psiTailIntegrand (Ioi X) := by
  apply ((integrableOn_logSquareMajorant (lt_of_lt_of_le zero_lt_one hX)).const_mul A).mono'
    measurable_psiTailIntegrand.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using tail_integrand_le_logSquare hX hbound ht.le

theorem integrableOn_one_of_logSquare_bound {X A : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) :
    IntegrableOn psiTailIntegrand (Ioi 1) :=
  integrableOn_one_of_tail hX (integrableOn_tail_of_logSquare_bound hX hbound)

theorem abs_tail_integral_le_logSquare {X A x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |∫ t in Ioi x, psiTailIntegrand t| ≤ A * logSquareTailPrimitive x := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one (hX.trans hx)
  have hI := (integrableOn_tail_of_logSquare_bound hX hbound).mono_set (Ioi_subset_Ioi hx)
  calc
    _ ≤ ∫ t in Ioi x, |psiTailIntegrand t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi x, A * logSquareMajorant t := by
      apply integral_mono_ae hI.abs ((integrableOn_logSquareMajorant hp).const_mul A)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact tail_integrand_le_logSquare hX hbound (hx.trans ht.le)
    _ = _ := by rw [integral_const_mul, integral_logSquareMajorant hp]

theorem abs_remainder_minus_tail_le_logSquare {X A x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |(Chebyshev.psi x - x) / x - ∫ t in Ioi x, psiTailIntegrand t| ≤
      A * (9 * log x ^ 2 + 128 * log x + 1024) * x ^ (-(1 : ℝ) / 8) := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one (hX.trans hx)
  have hpoint : |(Chebyshev.psi x - x) / x| ≤ A * log x ^ 2 * x ^ (-(1 : ℝ) / 8) := by
    simpa only [abs_div, abs_of_pos hp, IEANTN.Eψ] using hbound x hx
  have htail := abs_tail_integral_le_logSquare hX hbound hx
  calc
    _ ≤ |(Chebyshev.psi x - x) / x| + |∫ t in Ioi x, psiTailIntegrand t| := abs_sub _ _
    _ ≤ A * log x ^ 2 * x ^ (-(1 : ℝ) / 8) + A * logSquareTailPrimitive x := add_le_add hpoint htail
    _ = _ := by dsimp [logSquareTailPrimitive]; ring

/-- A genuine psi power envelope yields the weighted von Mangoldt bound,
with Euler's constant supplied by the proved exact normalization. -/
theorem lambda_error_le_power {X C x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ C * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |CH2.v1.lambdaSum x - (log x - Real.eulerMascheroniConstant)| ≤
      9 * C * x ^ (-(1 : ℝ) / 8) := by
  have hI := integrableOn_one_of_power_bound hX hbound
  change IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1) at hI
  have hid := lambda_tail_identity hI (hX.trans hx)
  have hrewrite : CH2.v1.lambdaSum x - (log x - Real.eulerMascheroniConstant) =
      CH2.v1.lambdaSum x - log x + Real.eulerMascheroniConstant := by ring
  rw [hrewrite, hid]
  exact abs_remainder_minus_tail_le_power hX hbound hx

/-- Exact logarithmic-square transfer, with no fixed finite-RH error floor. -/
theorem lambda_error_le_logSquare {X A x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ A * log t ^ 2 * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |CH2.v1.lambdaSum x - (log x - Real.eulerMascheroniConstant)| ≤
      A * (9 * log x ^ 2 + 128 * log x + 1024) * x ^ (-(1 : ℝ) / 8) := by
  have hI := integrableOn_one_of_logSquare_bound hX hbound
  change IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1) at hI
  have hid := lambda_tail_identity hI (hX.trans hx)
  have hrewrite : CH2.v1.lambdaSum x - (log x - Real.eulerMascheroniConstant) =
      CH2.v1.lambdaSum x - log x + Real.eulerMascheroniConstant := by ring
  rw [hrewrite, hid]
  exact abs_remainder_minus_tail_le_logSquare hX hbound hx

/-- The refined coefficient1/566 is retained exactly, rather than replaced by
an older1/284 profile or by a rounded uniform constant. -/
theorem lambda_error_le_refined_logSquare {X x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ (1 / 566 : ℝ) * log t ^ 2 * t ^ (-(1 : ℝ) / 8))
    (hx : X ≤ x) :
    |CH2.v1.lambdaSum x - (log x - Real.eulerMascheroniConstant)| ≤
      (9 * log x ^ 2 + 128 * log x + 1024) / 566 * x ^ (-(1 : ℝ) / 8) := by
  convert lambda_error_le_logSquare hX hbound hx using 1 <;> ring

#print axioms integral_logSquareMajorant
#print axioms integrableOn_one_of_logSquare_bound
#print axioms abs_remainder_minus_tail_le_logSquare
#print axioms lambda_error_le_power
#print axioms lambda_error_le_logSquare
#print axioms lambda_error_le_refined_logSquare
end LambdaEvolutionA
