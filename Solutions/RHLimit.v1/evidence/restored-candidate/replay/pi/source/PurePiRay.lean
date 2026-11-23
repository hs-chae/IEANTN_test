import NormalizedFormula
namespace RHLimit.PurePi
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

theorem ch_pi_stronger_classical
    (rh : SharedRH.hypothesis)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hn : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hc : CotangentSeries.v1.cot_series_zeta_values)
    (hr : ZeroCount.v1.rvm_error_bound) (hs : ZeroCount.v1.rvm_error_small)
    (hh : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 100 ≤ L) :
    |primeCounting (exp L)-IEANTN.Li (exp L)| <
      exp (L/2)*(L/(8*π)-1/3) := by
  have hb := ch_pi rh hk hn h2 hv hc hr hs hh hGM hP hJ (by linarith : 34 ≤ L)
  have hco := ch_normalized_improves_classical hL
  have hL0 : 0 < L := by linarith
  have he : envelope RHSmoothing.chBound L+2 =
      normalized RHSmoothing.chBound L * (exp (L/2)/L) := by
    unfold normalized
    field_simp [hL0.ne', exp_ne_zero]
  calc
    _ ≤ envelope RHSmoothing.chBound L+2 := hb
    _ = normalized RHSmoothing.chBound L*(exp (L/2)/L) := he
    _ < (L^2/(8*π)-L/3)*(exp (L/2)/L) :=
      mul_lt_mul_of_pos_right hco (div_pos (exp_pos _) hL0)
    _ = exp (L/2)*(L/(8*π)-1/3) := by
      field_simp [hL0.ne']
      <;> ring

lemma ch_at_100 : normalized RHSmoothing.chBound 100 < (361199/1000:ℝ) := by
  rw [normalized_formula _ (by norm_num)]
  unfold correction RHSmoothing.chBound
  interval_decide 80 (trust := kernel) <;>
    simp [LeanCert.Core.MathConst.toReal, div_eq_mul_inv]

lemma box_at_100 : normalized RHSmoothing.fastBound 100 < (357041/1000:ℝ) := by
  rw [normalized_formula _ (by norm_num)]
  unfold correction RHSmoothing.fastBound RHSmoothing.envelope RHSmoothing.v
  interval_decide 80 (trust := kernel) <;>
    simp [LeanCert.Core.MathConst.toReal, div_eq_mul_inv]

#print axioms ch_pi_stronger_classical
#print axioms ch_at_100
#print axioms box_at_100
end RHLimit.PurePi
