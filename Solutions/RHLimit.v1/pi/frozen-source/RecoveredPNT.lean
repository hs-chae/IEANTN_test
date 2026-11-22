import PNTScalar
import RecoveredLimit
import RecoveredLowSum

open Real IEANTN
namespace PNTStudy

/-- Loses only 0.181 sqrt(x), while avoiding the separate numerical
reciprocal-ordinate-sum premise of the original CH2 proof. -/
theorem no_ordinate_sum_recovered
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
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {L : ℝ} (hL : 34 ≤ L) :
    |Chebyshev.psi (exp L) - exp L| ≤ (coeffA L + 0.181) * sqrt (exp L) := by
  obtain ⟨ht,hx⟩ := height_conditions hL
  have hT := lt_of_le_of_lt (le_max_left _ _) hx
  have hx9 := lt_of_le_of_lt (le_max_right _ _) hx
  have h := RecoveredLimit.corollary_1_2_psi_at hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall
    (RHContinuation.RecoveredLowSum.recovered_cap hrvm hsmall).le hH ht hx9.le hT.le
    (RH.LogicalAdapters.finite_height hRH (height L))
  have hp : π ≤ height L := by linarith [pi_lt_four, show (4:ℝ) ≤ 10^7 by norm_num]
  have hco := CH2Section9.mainFactor_bounds hp
  have hcorr := mul_le_mul_of_nonneg_left
    (show CH2.v1.mainFactor (height L) - 1 ≤ (π/height L)^2 by linarith [hco.2])
    (exp_nonneg L)
  apply le_trans ?_ (scalar_simplify hL 0.181)
  rw [show Chebyshev.psi (exp L)-exp L =
    (Chebyshev.psi (exp L) - exp L * CH2.v1.mainFactor (height L)) +
      exp L*(CH2.v1.mainFactor (height L)-1) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg (exp_nonneg _) (sub_nonneg.mpr hco.1))]
  nlinarith

#print axioms no_ordinate_sum_recovered
end PNTStudy
