/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedEnvelope
import IEANTN.Nodes.CH2.v5.Conclusions

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

set_option maxHeartbeats 2000000 in
/-- Uniform contour remainder for every allowed fixed strip. -/
theorem scaled_remainder_fixed_strip {a x : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2)
    (hx : Real.exp (16 / a) ≤ x) :
    finiteRemainder (x ^ a) x * x ^ a ≤ 3.2 := by
  have hx0 : 0 < x := (Real.exp_pos (16 / a : ℝ)).trans_le hx
  have hLbase : 16 / a ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (16 / a : ℝ)) hx
    simpa using hh
  have hR : 16 ≤ a * Real.log x := by
    have hh := (div_le_iff₀ ha).mp hLbase
    nlinarith
  have hL : 32 ≤ Real.log x := by
    have hl : 0 < Real.log x := lt_of_lt_of_le (by positivity : (0 : ℝ) < 16 / a) hLbase
    nlinarith
  have hL0 : 0 < Real.log x := by linarith
  set T := x ^ a with hT
  set U := T - 1 / 2 with hU
  have hTe : T = Real.exp (a * Real.log x) := by
    rw [hT, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hT0 : 0 < T := by rw [hTe]; positivity
  have hTlo : (1000000 : ℝ) ≤ T := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    exact h16.trans (by rw [hTe]; exact Real.exp_le_exp.mpr (by linarith))
  have hlogT : Real.log T = a * Real.log x := by rw [hTe, Real.log_exp]
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hUlo : (0.99 : ℝ) * T ≤ U := by dsimp [U]; linarith
  have hinv : T / U ^ 2 ≤ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith [sq_nonneg (U - 0.99 * T)]
  have hinv' : T / U ^ 2 ≤ (2 : ℝ) / 1000000 :=
    hinv.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hTlo)
  have hTx : T ^ 2 ≤ x := by
    rw [hTe, ← Real.exp_nat_mul]
    rw [← Real.exp_log hx0]
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith
  have hTdiv : T / x ≤ (1 : ℝ) / 1000000 := by
    have hh : T / x ≤ 1 / T := by rw [div_le_div_iff₀ hx0 hT0]; nlinarith
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) hTlo)
  have hpi : Real.pi / U * T ≤ (3.19 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hU0]
    have hp := Real.pi_lt_d2
    nlinarith
  have hJL : 10 * Real.log T ^ 2 / Real.log x ^ 2 ≤ (3 : ℝ) := by
    rw [hlogT, div_le_iff₀ (by positivity)]
    have ha2 := pow_le_pow_left₀ ha.le ha' 2
    have hm := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (Real.log x))
    norm_num at hm
    nlinarith
  have he : Real.exp (-(3 / 2 * (Real.log x - 1))) ≤ 1 / x := by
    calc _ ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / x := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hJT : Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * T) ≤ (1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ 15 + 2 * T by positivity)
    have ht : 15 + 2 * T ≤ x := by nlinarith
    have hg : 1 / x * (15 + 2 * T) ≤ (1 : ℝ) := by
      rw [one_div_mul_eq_div, div_le_one hx0]
      exact ht
    exact hh.trans hg
  have hJ : horizontalCorrection T T x ≤ 4 := by unfold horizontalCorrection; linarith
  have hK : Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 ≤ 1 := by
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have h1 : Real.eulerMascheroniConstant / Real.log x ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : (1.8 : ℝ) / Real.log x ^ 3 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 3
      norm_num at hh
      linarith
    linarith
  have hC : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2) * T ≤ (0.001 : ℝ) := by
    have hJK : horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3 ≤ 5 := by linarith
    have heq : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / U ^ 2) * T =
        (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3)) * (T / U ^ 2) := by ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right (show 2 * (horizontalCorrection T T x +
      Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) ≤ 10 by linarith)
      (show 0 ≤ T / U ^ 2 by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hinv' (by norm_num : (0 : ℝ) ≤ 10)
    norm_num at hh2 ⊢
    linarith
  have hPole : Real.pi ^ 2 / (3 * U ^ 2) * T ≤ (0.001 : ℝ) := by
    have heq : Real.pi ^ 2 / (3 * U ^ 2) * T = (Real.pi ^ 2 / 3) * (T / U ^ 2) := by ring
    rw [heq]
    have hp2 : Real.pi ^ 2 / 3 ≤ (16 / 3 : ℝ) := by
      have hp := Real.pi_pos
      have hp4 := Real.pi_lt_four
      nlinarith
    have hh := mul_le_mul hp2 hinv' (by positivity) (by norm_num : (0 : ℝ) ≤ 16 / 3)
    norm_num at hh ⊢
    linarith
  have hLog : Real.log (2 * Real.pi) / x * T ≤ (0.001 : ℝ) := by
    have hl : Real.log (2 * Real.pi) ≤ (8 : ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
      linarith [Real.pi_lt_four]
    rw [show Real.log (2 * Real.pi) / x * T = Real.log (2 * Real.pi) * (T / x) by ring]
    have hh := mul_le_mul hl hTdiv (by positivity) (by norm_num : (0 : ℝ) ≤ 8)
    norm_num at hh ⊢
    linarith
  have hTail : ((2 * Real.pi / U + 1 / 2) / x *
      (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) * T ≤ (0.001 : ℝ) := by
    have hx2 : 2 ≤ x := by nlinarith
    have hp := Real.pi_pos
    have hxp : x ^ (-2 : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two, inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    have hden : 0 < 1 - x ^ (-2 : ℝ) := by linarith
    have hz0 : 0 ≤ x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) := by positivity
    have hz1 : x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) ≤ (1 : ℝ) := by
      rw [div_le_one hden]
      linarith
    have hc : 2 * Real.pi / U + 1 / 2 ≤ (1 : ℝ) := by
      have hh : 2 * Real.pi / U ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ hU0]
        have hp4 := Real.pi_lt_four
        nlinarith
      linarith
    have heq : ((2 * Real.pi / U + 1 / 2) / x *
        (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) * T =
        (2 * Real.pi / U + 1 / 2) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) * (T / x) := by ring
    rw [heq]
    have hh : (2 * Real.pi / U + 1 / 2) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) ≤ 1 := by
      exact (mul_le_mul hc hz1 hz0 (by norm_num)).trans_eq (by ring)
    have hh2 := mul_le_mul_of_nonneg_right hh (show 0 ≤ T / x by positivity)
    norm_num at hh2 hTdiv ⊢
    linarith
  unfold finiteRemainder
  change (Real.pi / U + _ + _ + _ + _) * T ≤ _
  rw [add_mul, add_mul, add_mul, add_mul]
  linarith

/-- The unchanged general-beta numerical envelope on its original entire ray. -/
theorem fixed_strip_envelope {β x : ℝ} (hβ : (1 / 2 : ℝ) ≤ β) (hβ' : β < 1)
    (hx : Real.exp (16 / (1 - β)) ≤ x) :
    finiteErrorBound (x ^ (1 - β)) β x ≤
      2 * (1 - β) ^ 2 * Real.log x ^ 2 * x ^ (β - 1) := by
  set a := 1 - β with ha
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hx0 : 0 < x := (Real.exp_pos (16 / a : ℝ)).trans_le hx
  have hLbase : 16 / a ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (16 / a : ℝ)) hx
    simpa using hh
  set R := a * Real.log x with hRdef
  have hR : 16 ≤ R := by
    have hh := (div_le_iff₀ ha0).mp hLbase
    dsimp [R]
    nlinarith
  have hR0 : 0 ≤ R := by linarith
  set T := x ^ a with hT
  have hTe : T = Real.exp R := by
    rw [hT, Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [R]
    ring
  have hT0 : 0 < T := by rw [hTe]; positivity
  have hlogT : Real.log T = R := by rw [hTe, Real.log_exp]
  have hC0 : 0 ≤ spectralBound T := by unfold spectralBound; rw [hlogT]; positivity
  have hCup : spectralBound T ≤ 0.17 * R ^ 2 + 2.34 * R := by
    unfold spectralBound
    rw [hlogT]
    have hp := Real.pi_pos
    have hp3 := Real.pi_gt_three
    have h1 : 1 / (2 * Real.pi) ≤ (0.17 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 : 2 + 1 / Real.pi ≤ (2.34 : ℝ) := by
      have hh : 1 / Real.pi ≤ (0.34 : ℝ) := by rw [div_le_iff₀ hp]; linarith
      linarith
    have hh1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg R)
    have hh2 := mul_le_mul_of_nonneg_right h2 hR0
    rw [one_div_mul_eq_div] at hh1
    linarith
  have hprod : x ^ β * T = x := by
    rw [hT, ← Real.rpow_add hx0]
    have he : β + a = 1 := by dsimp [a]; ring
    rw [he, Real.rpow_one]
  have hscale : x ^ β / x * T = 1 := by
    rw [div_mul_eq_mul_div, hprod, div_self hx0.ne']
  have herr : finiteErrorBound T β x = finiteRemainder T x + spectralBound T * (x ^ β / x) := by
    unfold finiteErrorBound finiteRemainder
    ring
  have hrem := scaled_remainder_fixed_strip ha0 ha1 hx
  have hb : finiteErrorBound T β x * T ≤ 2 * R ^ 2 := by
    rw [herr, add_mul, mul_assoc, hscale, mul_one]
    have hpoly : (3.2 : ℝ) + 0.17 * R ^ 2 + 2.34 * R ≤ 2 * R ^ 2 := by
      nlinarith only [hR, sq_nonneg (R - 16)]
    linarith
  have hinv : x ^ (β - 1) = 1 / T := by
    have he : β - 1 = -a := by dsimp [a]; ring
    rw [he, Real.rpow_neg hx0.le, ← hT, one_div]
  rw [hinv, mul_one_div]
  apply (le_div_iff₀ hT0).mpr
  calc finiteErrorBound T β x * T ≤ 2 * R ^ 2 := hb
    _ = 2 * (1 - β) ^ 2 * Real.log x ^ 2 := by dsimp [R, a]; ring

/-- Prove the exact original general-beta contract from the named CH2 ingredients. -/
theorem general_fixed_strip_proved (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
 : CH2.v5.psi_bound_of_fixed_strip := by
  intro β hβ hβ' hfree x hx
  have ha0 : 0 < 1 - β := by linarith
  have ha1 : 1 - β ≤ 1 / 2 := by linarith
  have hx0 : 0 < x := (Real.exp_pos (16 / (1 - β))).trans_le hx
  have hL : 16 / (1 - β) ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (16 / (1 - β))) hx
    simpa using hh
  have hR : 16 ≤ (1 - β) * Real.log x := by
    have hh := (div_le_iff₀ ha0).mp hL
    nlinarith
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by positivity : (0 : ℝ) < 16 / (1 - β)) hL
  have hL32 : 32 ≤ Real.log x := by nlinarith
  have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    norm_num at hh
    linarith
  have hxnum : 1000000 ≤ x := h16.trans (by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith))
  have hTe : x ^ (1 - β) = Real.exp ((1 - β) * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hTnum : 1000000 ≤ x ^ (1 - β) := by
    rw [hTe]
    exact h16.trans (Real.exp_le_exp.mpr hR)
  have hlogT : 16 ≤ Real.log (x ^ (1 - β)) := by rw [hTe, Real.log_exp]; exact hR
  exact (finite_transfer hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (by linarith : 2000 ≤ x ^ (1 - β)) hlogT hxnum (by linarith) hfree).trans
    (fixed_strip_envelope hβ hβ' hx)

end CH2QRH
