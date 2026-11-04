/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectKernelHigh
import WinnerDensityA.DirectKernelLow

open Complex MeasureTheory Set
namespace WinnerDirectKernel

noncomputable def zeroSum {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ i ∈ S, (w i : ℂ) * zexp (z i) u / z i

lemma zero_row_integrable {ι : Type*} (z : ι → ℂ) (w : ι → ℝ) (i : ι)
    {v L : ℝ} (hv : 0 < v) (hL : v ≤ L) :
    IntervalIntegrable (fun u : ℝ => ((w i : ℂ)*zexp (z i) u/z i)/(u : ℂ)^2) volume v L := by
  apply ContinuousOn.intervalIntegrable_of_Icc hL
  have hc : Continuous (fun u : ℝ => (w i : ℂ)*zexp (z i) u/z i) := by
    unfold zexp; fun_prop
  apply hc.continuousOn.div (by fun_prop)
  intro u hu
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (hv.trans_le hu.1).ne'
  exact pow_ne_zero 2 hu0

lemma zero_sum_integrable {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    {v L : ℝ} (hv : 0 < v) (hL : v ≤ L) :
    IntervalIntegrable (fun u : ℝ => zeroSum S z w u/(u : ℂ)^2) volume v L := by
  simp only [zeroSum, Finset.sum_div]
  convert! IntervalIntegrable.sum S
    (fun i _ => zero_row_integrable z w i hv hL) using 1
  funext u
  simp only [Finset.sum_apply]

/-- Finite sums are integrated before taking absolute values; no infinite exchange is used. -/
theorem integrated_zeroSum {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    {v L : ℝ} (hv : 0 < v) (hL : v ≤ L) :
    zeroSum S z w L/(L : ℂ) + (∫ u in v..L, zeroSum S z w u/(u : ℂ)^2) =
      ∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L := by
  simp only [zeroSum, Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum (fun i _ => zero_row_integrable z w i hv hL),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [piKernel, mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · apply intervalIntegral.integral_congr
    intro u hu
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The real part interface used by the real-valued explicit formula. -/
theorem integrated_zeroSum_re {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    {v L : ℝ} (hv : 0 < v) (hL : v ≤ L) :
    (zeroSum S z w L).re/L + (∫ u in v..L, (zeroSum S z w u).re/u^2) =
      (∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L).re := by
  have h := congrArg Complex.re (integrated_zeroSum S z w hv hL)
  have hi := intervalIntegral.intervalIntegral_re (zero_sum_integrable S z w hv hL)
  rw [Complex.add_re] at h
  simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.div_ofReal_re] at hi h
  rw [← hi] at h
  exact h

/-- A finite high-zero spectral budget, with actual nonnegative multiplicities. -/
theorem high_sum_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    {a H v L : ℝ} (ha : 0 < a) (hH : 0 < H) (hv : 0 < v) (hL : v ≤ L)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hb : ∀ i ∈ S, a ≤ (z i).re)
    (hg : ∀ i ∈ S, H ≤ |(z i).im|) :
    ‖∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L‖ ≤
      highFactor a H v L * (∑ i ∈ S, w i*Real.exp ((z i).re*L)/|(z i).im|)/L := by
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ)*piKernel (z i) v L‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, w i*((Real.exp ((z i).re*L)/(|(z i).im| * L))*highFactor a H v L) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (norm_piKernel_high ha hH hv hL (hb i hi) (hg i hi)) (hw i hi)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms integrated_zeroSum
#print axioms integrated_zeroSum_re
#print axioms high_sum_bound
end WinnerDirectKernel
