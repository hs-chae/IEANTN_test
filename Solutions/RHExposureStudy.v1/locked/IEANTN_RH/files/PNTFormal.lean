import FullRH
import Section9Cor13

open Real IEANTN
namespace PNTStudy

noncomputable def height (L : ℝ) := 20 * exp (L/2) / L

theorem height_conditions {L : ℝ} (hL : 34 ≤ L) :
    (10:ℝ)^7 ≤ height L ∧ max (height L) ((10:ℝ)^9) < exp L := by
  have hpos : 0 < L := by linarith
  have he : (2718/1000:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have h17 : (2718/1000:ℝ)^17 ≤ exp 17 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) he 17
    rw [Real.exp_one_pow] at hh
    exact_mod_cast hh
  have hdelta : 1+(L-34)/2 ≤ exp ((L-34)/2) := by simpa [add_comm] using Real.add_one_le_exp ((L-34)/2)
  have hfac : exp (L/2) = exp 17 * exp ((L-34)/2) := by rw [←exp_add]; congr 1; ring
  have hquarter : L/34 ≤ 1+(L-34)/2 := by linarith
  have hs : exp 17 * L / 34 ≤ exp (L/2) := by
    rw [hfac, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hquarter.trans hdelta) (exp_nonneg _)
  have hm : (10:ℝ)^7 * 34 ≤ 20 * exp 17 := by
    calc
      _ ≤ 20 * (2718/1000:ℝ)^17 := by norm_num
      _ ≤ _ := by gcongr
  have hbig : (10:ℝ)^9 < exp L := by
    have hpsi : (2:ℝ)^34 ≤ exp 34 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) exp_one_gt_two.le 34
      rw [Real.exp_one_pow] at hh
      exact_mod_cast hh
    exact (show (10:ℝ)^9 < 2^34 by norm_num).trans_le (hpsi.trans (exp_le_exp.mpr hL))
  refine ⟨?_, max_lt_iff.mpr ⟨?_,hbig⟩⟩
  · unfold height
    apply (le_div_iff₀ hpos).2
    have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ L/34 by positivity)
    nlinarith
  · unfold height
    apply (div_lt_iff₀ hpos).2
    have hmul : exp L = exp (L/2) * exp (L/2) := by rw [← exp_add]; congr 1; ring
    rw [hmul]
    have e1 : 1 ≤ exp (L/2) := one_le_exp (by positivity)
    have h20 : 20 < exp (L/2)*L := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h20 (exp_pos (L/2))]

/-- Actual reuse of the existing proof of the smoothing-center correction. -/
theorem centered (hRH : SharedRH.hypothesis) (hc : CH2.v1.corollary_1_2_psi)
    {x T : ℝ} (hT : (10:ℝ)^7 ≤ T) (hx : max T ((10:ℝ)^9) < x) :
    |Chebyshev.psi x - x| ≤
      (π / (T - 1) + (π / T)^2)*x + CH2.v1.CT T * sqrt x := by
  have hx0 : 0 ≤ x := le_of_lt ((by norm_num : (0:ℝ) < 10^9).trans
    ((le_max_right T ((10:ℝ)^9)).trans_lt hx))
  have htπ : π ≤ T := by linarith [pi_lt_four, show (4:ℝ) ≤ 10^7 by norm_num]
  have hco := CH2Section9.mainFactor_bounds htπ
  have h := FullRH.adaptive_ch2 hRH hc hT hx
  have he : Chebyshev.psi x - x =
      (Chebyshev.psi x - x * CH2.v1.mainFactor T) + x*(CH2.v1.mainFactor T-1) := by ring
  have hnonneg : 0 ≤ x*(CH2.v1.mainFactor T-1) := mul_nonneg hx0 (sub_nonneg.mpr hco.1)
  have hterm := mul_le_mul_of_nonneg_left
    (show CH2.v1.mainFactor T-1 ≤ (π/T)^2 by linarith [hco.2]) hx0
  rw [he]
  calc
    _ ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T| + |x*(CH2.v1.mainFactor T-1)| :=
      abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg hnonneg]; nlinarith

theorem adaptive_centered (hRH : SharedRH.hypothesis)
    (hc : CH2.v1.corollary_1_2_psi) {L : ℝ} (hL : 34 ≤ L) :
    |Chebyshev.psi (exp L) - exp L| ≤
      (π / (height L - 1) + (π / height L)^2)*exp L +
      CH2.v1.CT (height L) * sqrt (exp L) :=
  centered hRH hc (height_conditions hL).1 (height_conditions hL).2

section Providers
theorem actual_psi
    (hRH : SharedRH.hypothesis)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hsum : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {L : ℝ} (hL : 34 ≤ L) :
    |Chebyshev.psi (exp L) - exp L| ≤
      (π / (height L - 1) + (π / height L)^2)*exp L +
      CH2.v1.CT (height L) * sqrt (exp L) :=
  adaptive_centered hRH (CH2Section9.corollary_1_2_psi hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hsum hH) hL
end Providers

#print axioms actual_psi
#print axioms height_conditions
#print axioms adaptive_centered
end PNTStudy
