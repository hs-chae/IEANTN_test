/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RefinedEnvelope
import IEANTN.Nodes.CH2.v9.Conclusions

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

theorem refined_transfer_proved (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
 : CH2.v9.refined_transfer := by
  intro hqrh x hx
  have hx0 : 0 < x := (Real.exp_pos (300 : ℝ)).trans_le hx
  have hL : 300 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (300 : ℝ)) hx
    simpa using hh
  have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    norm_num at hh
    linarith
  have hxnum : 1000000 ≤ x := h16.trans ((Real.exp_le_exp.mpr (by norm_num : (16 : ℝ) ≤ 300)).trans hx)
  have hTexp : x ^ ((1 : ℝ) / 8) = Real.exp (Real.log x / 8) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hT : 2000 ≤ x ^ ((1 : ℝ) / 8) := by
    have hh : Real.exp 16 ≤ x ^ ((1 : ℝ) / 8) := by
      rw [hTexp]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hR : 16 ≤ Real.log (x ^ ((1 : ℝ) / 8)) := by rw [hTexp, Real.log_exp]; linarith
  exact (paired_finite_transfer hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    hT hR hxnum (by linarith) hqrh).trans (paired_refined_envelope_bound hx)

end CH2QRH
