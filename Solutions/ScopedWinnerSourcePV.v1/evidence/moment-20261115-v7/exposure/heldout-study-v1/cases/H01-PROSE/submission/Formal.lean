import TaskDefinitions
import Mathlib.NumberTheory.AbelSummation

noncomputable section
open Real MeasureTheory Finset
namespace ExposureTask

def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

lemma sum_primeIndicator (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, primeIndicator k) = (Nat.primeCounting n : ℝ) := by
  simp only [primeIndicator, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]

lemma weighted_sum_primeIndicator (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (1 / (k : ℝ)) * primeIndicator k) =
      primeReciprocal x := by
  simp only [primeIndicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [← Nat.primesLE_eq_filter_Icc_zero]
  rfl

lemma inv_derivative {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t^2)) t := by
  simpa only [one_div] using hasDerivAt_inv ht

/-- The actual discrete-prime partial-summation formula. -/
theorem prime_partial_summation {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocal x = pi x / x + ∫ t in Set.Ioc 2 x, pi t / t^2 := by
  have hd : ∀ t ∈ Set.Icc (2:ℝ) x,
      HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t^2)) t := by
    intro t ht
    exact inv_derivative (by linarith [ht.1])
  have he : Set.EqOn (deriv (fun t : ℝ => 1 / t))
      (fun t : ℝ => -(1 / t^2)) (Set.Icc 2 x) := by
    intro t ht
    exact (hd t ht).deriv
  have hc : ContinuousOn (fun t : ℝ => -(1 / t^2)) (Set.Icc 2 x) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  have hi : IntegrableOn (deriv (fun t : ℝ => 1 / t)) (Set.Icc 2 x) :=
    (hc.integrableOn_Icc).congr_fun he.symm measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ primeIndicator
    (by simp [primeIndicator, Nat.not_prime_zero]) (by simp [primeIndicator, Nat.not_prime_one]) x
    (fun t ht => (hd t ht).differentiableAt) hi
  rw [weighted_sum_primeIndicator, sum_primeIndicator] at h
  have hint : (∫ t in Set.Ioc 2 x,
      deriv (fun t : ℝ => 1 / t) t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeIndicator k) =
      -(∫ t in Set.Ioc 2 x, pi t / t^2) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [he ⟨ht.1.le, ht.2⟩, sum_primeIndicator]
    simp [pi, div_eq_mul_inv, mul_comm]
  rw [hint] at h
  simpa [pi, div_eq_mul_inv, mul_comm] using h

/-- Clearing the normalization uses the positive logarithm, not an estimate below A. -/
theorem error_bound_at {t : ℝ} (ht : Real.exp 300 ≤ t)
    (h : Epi t ≤ C * t ^ (-(1:ℝ)/8)) :
    |pi t - Li2 t| ≤ C * t ^ (-(1:ℝ)/8) * (t / Real.log t) := by
  have h1 : 1 < Real.exp (300:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hpos : 0 < t := lt_trans zero_lt_one (lt_of_lt_of_le h1 ht)
  have hlog : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le h1 ht)
  exact (div_le_iff₀ (div_pos hpos hlog)).mp h

open scoped Interval

lemma invLog_continuousOn {x : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) := by
  apply continuousOn_const.div
    (Real.continuousOn_log.mono (by intro t ht; change t ≠ 0; linarith [ht.1]))
  intro t ht
  exact ne_of_gt (Real.log_pos (by linarith [ht.1]))

lemma Li2_hasDerivAt {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt Li2 (1 / Real.log t) t := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 t := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le ht] using invLog_continuousOn ht
  have hc : ContinuousAt (fun t : ℝ => 1 / Real.log t) t := by
    apply continuousAt_const.div
      (Real.continuousAt_log (by linarith))
      (ne_of_gt (Real.log_pos (by linarith)))
  exact intervalIntegral.integral_hasDerivAt_right hi ((by fun_prop : Measurable (fun t : ℝ => 1 / Real.log t)).stronglyMeasurable.stronglyMeasurableAtFilter) hc

lemma Li2_continuousOn {x : ℝ} (hx : 2 ≤ x) :
    ContinuousOn Li2 (Set.Icc 2 x) := by
  intro t ht
  exact (Li2_hasDerivAt ht.1).continuousAt.continuousWithinAt

/-- The offset Li2 cancels the logarithmic main term, with its lower endpoint. -/
theorem Li2_partial_summation {x : ℝ} (hx : 2 ≤ x) :
    Li2 x / x + (∫ t in (2:ℝ)..x, Li2 t / t^2) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
  have hd : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun t => Li2 t / t - Real.log (Real.log t))
        (-(Li2 t / t^2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    convert! ((Li2_hasDerivAt ht.1).fun_div (hasDerivAt_id t) ht0).sub
      ((Real.hasDerivAt_log hlog).comp t (Real.hasDerivAt_log ht0)) using 1 <;>
      try dsimp
    all_goals first | rfl | (field_simp; ring)
  have hc : ContinuousOn (fun t : ℝ => -(Li2 t / t^2)) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.neg
    apply (Li2_continuousOn hx).div (by fun_prop)
    intro t ht
    exact pow_ne_zero _ (by linarith [ht.1])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simp only [intervalIntegral.integral_neg] at h
  have h2 : Li2 2 = 0 := by simp [Li2]
  rw [h2] at h
  linarith

lemma pi_weight_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => pi t / t^2) volume 2 x := by
  have hc : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.Icc 2 x) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  have hi := integrableOn_mul_sum_Icc primeIndicator (m := 0)
    (by norm_num : (0:ℝ) ≤ 2) hc.integrableOn_Icc
  have he : (fun t : ℝ => 1 / t^2 * ∑ k ∈ Icc 0 ⌊t⌋₊, primeIndicator k) =
      (fun t : ℝ => pi t / t^2) := by
    funext t
    rw [sum_primeIndicator]
    simp [pi, div_eq_mul_inv, mul_comm]
  rw [he] at hi
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hi

lemma Li2_weight_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Li2 t / t^2) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hx]
  apply (Li2_continuousOn hx).div (by fun_prop)
  intro t ht
  exact pow_ne_zero _ (by linarith [ht.1])

/-- Finite exact error identity for actual H and the specified offset Li2. -/
theorem reciprocal_error_identity {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocal x - Real.log (Real.log x) =
      -Real.log (Real.log 2) + (pi x - Li2 x) / x +
        ∫ t in (2:ℝ)..x, (pi t - Li2 t) / t^2 := by
  have hp := prime_partial_summation hx
  rw [← intervalIntegral.integral_of_le hx] at hp
  have hl := Li2_partial_summation hx
  have hi : (∫ t in (2:ℝ)..x, (pi t - Li2 t) / t^2) =
      (∫ t in (2:ℝ)..x, pi t / t^2) - (∫ t in (2:ℝ)..x, Li2 t / t^2) := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub (pi_weight_integrable hx) (Li2_weight_integrable hx)
  rw [hi, sub_div]
  linarith

end ExposureTask
