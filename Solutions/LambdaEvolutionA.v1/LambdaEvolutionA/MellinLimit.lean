/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

open Real Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace LambdaEvolutionA

theorem psi_sum_Icc (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) =
      Chebyshev.psi t := by
  have h : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h]
  rfl

theorem psi_sum_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  apply IsBigO.of_bound (log 4 + 4)
  filter_upwards [] with n
  rw [← Nat.floor_natCast (R := ℝ) n, psi_sum_Icc]
  simp only [Nat.floor_natCast, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg _),
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

theorem remainder_mellin_measurable {f : ℝ → ℝ}
    (hI : IntegrableOn f (Ioi (1 : ℝ))) (s : ℝ) :
    AEStronglyMeasurable (fun t : ℝ ↦ f t * t ^ (1 - s))
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hc : ContinuousOn (fun t : ℝ ↦ t ^ (1 - s)) (Ioi (1 : ℝ)) := by
    intro t ht
    change 1 < t at ht
    exact (Real.continuousAt_rpow_const t (1 - s)
      (Or.inl (by linarith : t ≠ 0))).continuousWithinAt
  exact hI.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioi)

theorem remainder_mellin_bound (f : ℝ → ℝ) {s t : ℝ} (hs : 1 ≤ s) (ht : 1 < t) :
    ‖f t * t ^ (1 - s)‖ ≤ ‖f t‖ := by
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t) (1 - s))]
  have hp : t ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)
  nlinarith [abs_nonneg (f t)]

theorem remainder_mellin_integrable {f : ℝ → ℝ}
    (hI : IntegrableOn f (Ioi (1 : ℝ))) {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn (fun t : ℝ ↦ f t * t ^ (1 - s)) (Ioi (1 : ℝ)) := by
  apply hI.norm.mono' (remainder_mellin_measurable hI s)
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun t ht ↦ remainder_mellin_bound f hs ht)

/-- Absolute integrability of the actual remainder is exactly the domination
needed to take the Mellin parameter to one from the right. -/
theorem remainder_mellin_tendsto {f : ℝ → ℝ}
    (hI : IntegrableOn f (Ioi (1 : ℝ))) :
    Tendsto (fun s : ℝ ↦ ∫ t in Ioi (1 : ℝ), f t * t ^ (1 - s))
      (𝓝[>] (1 : ℝ)) (𝓝 (∫ t in Ioi (1 : ℝ), f t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun t ↦ ‖f t‖)
  · exact Filter.Eventually.of_forall (remainder_mellin_measurable hI)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht ↦ remainder_mellin_bound f hs.le ht)
  · exact hI.norm
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [] with t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    have hc : ContinuousAt (fun s : ℝ ↦ f t * t ^ (1 - s)) 1 := by
      fun_prop (disch := positivity)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The Mellin representation of the von Mangoldt series, specialized to a
real parameter and the actual Chebyshev function. -/
theorem zeta_logderiv_mellin {s : ℝ} (hs : 1 < s) :
    (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re =
      s * ∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-(s + 1)) := by
  have hrep := LSeries_eq_mul_integral_of_nonneg
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℝ))
    (r := 1) (s := (s : ℂ)) (by norm_num) (by simpa using hs)
    psi_sum_bigO (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by simpa using hs)] at hrep
  have hi : (∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) *
        (t : ℂ) ^ (-((s : ℂ) + 1))) =
      (((∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-(s + 1))) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    have ht0 : 0 ≤ t := by linarith
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0]
    have he : (-((s : ℂ) + 1)) = ((-(s + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    congr 1
    exact_mod_cast psi_sum_Icc t
  rw [hi] at hrep
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using congrArg Complex.re hrep

theorem zeta_regularized_eq_mellin
    (hI : IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1))
    {s : ℝ} (hs : 1 < s) :
    (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re - 1 / (s - 1) =
      1 + s * ∫ t in Ioi (1 : ℝ),
        ((Chebyshev.psi t - t) / t ^ 2) * t ^ (1 - s) := by
  have hm := remainder_mellin_integrable hI hs.le
  have hp : IntegrableOn (fun t : ℝ ↦ t ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hi : (∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-(s + 1))) =
      (∫ t in Ioi (1 : ℝ), t ^ (-s)) +
      ∫ t in Ioi (1 : ℝ), ((Chebyshev.psi t - t) / t ^ 2) * t ^ (1 - s) := by
    rw [← integral_add hp hm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    dsimp only
    have hpow : t ^ (1 - s) = t ^ (-(s + 1)) * t ^ (2 : ℕ) := by
      rw [← Real.rpow_two, ← Real.rpow_add ht0]
      congr 1
      ring
    have hpow' : t ^ (-s) = t * t ^ (-(s + 1)) := by
      nth_rw 2 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [hpow, hpow']
    field_simp
    <;> ring
  have hv : (∫ t in Ioi (1 : ℝ), t ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ) < 1),
      Real.one_rpow]
    field_simp [show -s + 1 ≠ 0 by linarith, show s - 1 ≠ 0 by linarith]
    <;> ring
  rw [zeta_logderiv_mellin hs, hi, hv]
  field_simp [show s - 1 ≠ 0 by linarith]
  <;> ring

theorem real_to_complex_right_one :
    Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change (s : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt hs : s ≠ 1)

theorem zeta_regularized_tendsto :
    Tendsto (fun s : ℝ ↦
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re - 1 / (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hc := (isLittleO_one_iff ℂ).mp
    log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  have hr : Tendsto (fun s : ℝ ↦
      (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) +
        ((s : ℂ) - 1)⁻¹ - (Real.eulerMascheroniConstant : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    (Complex.continuous_re.tendsto 0).comp (hc.comp real_to_complex_right_one)
  have hi : ∀ s : ℝ, ((s : ℂ) - 1)⁻¹ = (((s - 1)⁻¹ : ℝ) : ℂ) := by
    intro s
    push_cast
    rfl
  simp only [hi, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hr
  convert hr.neg.sub_const Real.eulerMascheroniConstant using 1
  · ext s
    simp only [neg_div, Complex.neg_re, one_div]
    ring
  · simp

/-- The Euler constant is determined by Mathlib's zeta expansion, rather than
introduced as a further source assumption. -/
theorem total_remainder_integral
    (hI : IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Ioi 1)) :
    (∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2) =
      -1 - Real.eulerMascheroniConstant := by
  have hJ := remainder_mellin_tendsto hI
  have hs : Tendsto (fun s : ℝ ↦ s) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s : ℝ ↦ 1 + s *
      ∫ t in Ioi (1 : ℝ), ((Chebyshev.psi t - t) / t ^ 2) * t ^ (1 - s))
      (𝓝[>] (1 : ℝ))
      (𝓝 (1 + 1 * ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)) :=
    tendsto_const_nhds.add (hs.mul hJ)
  have hR' : Tendsto (fun s : ℝ ↦
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re - 1 / (s - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (1 + ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)) := by
    simp only [one_mul] at hR
    apply hR.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (zeta_regularized_eq_mellin hI hs).symm
  have he := tendsto_nhds_unique zeta_regularized_tendsto hR'
  linarith

end LambdaEvolutionA

#print axioms LambdaEvolutionA.remainder_mellin_tendsto
#print axioms LambdaEvolutionA.zeta_logderiv_mellin
#print axioms LambdaEvolutionA.total_remainder_integral
