/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FinalAnalytic

/-! Retain the already-proved analytic envelope margin as an actual gap.
No source theorem, original hypothesis, numerical input or endpoint is changed. -/
namespace RamanujanPV.AnalyticMargin
open Real Set RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0

/-- A generic quantitative version of the existing analytic bridge. -/
theorem bridge_gap {pi li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    (hlower : AxlerLiLower li)
    (hpi0 : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000, 0 ≤ pi x)
    (hpiU : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000, pi x ≤ upperPi li x)
    (hpiL : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
      li (x/exp 1)-(1061/500:ℝ)*sqrt (x/exp 1)/(log x-1) ≤ pi (x/exp 1))
    {x : ℝ} (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    (9005:ℝ) < exp 1*x/log x*pi (x/exp 1)-(pi x)^2 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hL : 0 < log x := log_pos (by linarith [hx.1])
  have hLhi := log_finite_upper hx0 hx.2
  have he : (1:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have heX : x ≤ exp 1*x := by nlinarith
  have hR := improvedEnvelope_margin hseries hderiv hlower hx
  have hsq := pow_le_pow_left₀ (hpi0 x hx) (hpiU x hx) 2
  have hterm : (pi x)^2*log x/(exp 1*x) ≤
      (upperPi li x)^2*log x/(exp 1*x) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hL.le) (by positivity)
  have hlow := hpiL x hx
  unfold improvedEnvelope at hR
  have hnorm : 90+(pi x)^2*log x/(exp 1*x) < pi (x/exp 1) := by linarith
  have hden : 0 < exp 1*x := by positivity
  have hscaled := mul_lt_mul_of_pos_right hnorm hden
  have hcancel : ((pi x)^2*log x/(exp 1*x))*(exp 1*x)=(pi x)^2*log x :=
    div_mul_cancel₀ _ hden.ne'
  rw [add_mul,hcancel] at hscaled
  rw [lt_sub_iff_add_lt,show exp 1*x/log x*pi (x/exp 1)=
    exp 1*x*pi (x/exp 1)/log x by ring]
  apply (lt_div_iff₀ hL).mpr
  have hmargin : 9005*log x < 90*(exp 1*x) := by nlinarith [hx.1]
  nlinarith [hmargin]

/-- The quantitative height40 expression is itself much larger than9005. -/
theorem quantitative_expression {x : ℝ} (hx : exp 40 ≤ x) :
    (9005:ℝ) < (37/200:ℝ)*x^2/log x^6 := by
  have hx0 : 0 < x := (exp_pos 40).trans_le hx
  have hL : (40:ℝ) ≤ log x := by simpa using log_le_log (exp_pos 40) hx
  have hp := Real.pow_div_factorial_le_exp (log x) (by linarith : 0 ≤ log x) 8
  rw [exp_log hx0] at hp
  norm_num [Nat.factorial] at hp
  have hL8 : log x^8 ≤ 40320*x := by
    simpa [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ)<40320)).mp hp
  have hL2 : (1600:ℝ) ≤ log x^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hL2 (show 0 ≤ log x^6 by positivity)
  have hdom : log x^6 ≤ 26*x := by nlinarith
  have htwo : (2:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hlarge := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) htwo 40
  norm_num [← exp_nat_mul] at hlarge
  have hxlarge : (1000000000:ℝ) ≤ x := by linarith
  apply (lt_div_iff₀ (show 0 < log x^6 by positivity)).mpr
  have hbound := mul_le_mul_of_nonneg_left hdom (by norm_num : (0:ℝ)≤9005)
  have hprod := mul_pos hx0 (show 0 < (37/200:ℝ)*x-234130 by linarith)
  nlinarith

/-- Actual IEANTN prime counting, with exactly the six bridge source inputs. -/
theorem actual_bridge_gap
    (hseries : LogIntegralSeriesIdentity IEANTN.li) (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi) (htheta : ButheThetaDeficit)
    (hlower : AxlerPiLower) (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    {x : ℝ} (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    (9005:ℝ) < gap x := by
  have hd : LogIntegralDerivative IEANTN.li := by
    intro t ht
    exact LiBarriers.actual_li_hasDerivAt hoffset ht
  have hA : AxlerLiLower IEANTN.li := by
    apply axler_lower_supplies_li (pi:=IEANTN.primeCounting)
    · intro t ht
      exact hlower t (by linarith [ht.1])
    · intro t ht
      exact hpositive t ⟨by linarith [ht.1],ht.2⟩
  have hli2 : 0 ≤ IEANTN.li 2 :=
    (primeCounting_nonneg 2).trans (hpositive 2 (by norm_num)).le
  have hlog2 : (2/3:ℝ) ≤ log 2 := by linarith [log_two_decimal.1]
  apply bridge_gap hseries hd hA
  · intro t ht
    exact primeCounting_nonneg t
  · intro t ht
    exact Middle.pi_upper_from_theta_deficit (x:=t) (α:=(1/20:ℝ))
      (by linarith [ht.1]) (by norm_num)
      (fun u hu hut=>htheta u ⟨hu,hut.trans ht.2⟩) hoffset hli2 hlog2
  · intro t ht
    exact buthe_lower_supplies_bridge hbuthe ht
  · exact hx

#print axioms bridge_gap
#print axioms quantitative_expression
#print axioms actual_bridge_gap
section OriginalInputs
variable
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hFKS : FKS.v3.density_0618) (hRH : PlattTrudgian.v1.rh_up_to)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hCH2 : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤
      Real.pi / (3 * (10 : ℝ)^12) * t + (113.67 : ℝ) * sqrt t)
    (hDusart : Middle.DusartPowerInput)

include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hqrh hFKS hRH
  hseries hoffset hpositive hbuthe hCH2 hDusart

variable (htheta : ButheThetaDeficit) (hlower : AxlerPiLower)
include htheta hlower

/-- Same exact24 analytic inputs as FinalAnalytic.analytic_ray; the retained
endpoint margin now yields an actual uniform9005 gap, rather than positivity. -/
theorem analytic_ray_gap9005 {x : ℝ} (hx : (1490000000000:ℝ) ≤ x) :
    (9005:ℝ) < gap x := by
  by_cases h19 : x ≤ (10000000000000000000:ℝ)
  · exact actual_bridge_gap hseries hoffset hpositive htheta hlower hbuthe ⟨hx,h19⟩
  · have hx40 : exp (40:ℝ) ≤ x :=
      (exp_le_exp.mpr (by norm_num : (40:ℝ)≤43)).trans
        (exp43_le_1e19.trans (le_of_not_ge h19))
    exact (quantitative_expression hx40).trans
      (FinalAnalytic.quantitative_from40 hfe hdig h24u h24l hk hneg h2v hv hcs
        hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart hx40)

end OriginalInputs
#print axioms analytic_ray_gap9005
end RamanujanPV.AnalyticMargin
