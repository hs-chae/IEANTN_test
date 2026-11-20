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
  have hscaled := (mul_lt_mul_right hden).mpr hnorm
  have hcancel : ((pi x)^2*log x/(exp 1*x))*(exp 1*x)=(pi x)^2*log x :=
    div_mul_cancel₀ _ hden.ne'
  rw [add_mul,hcancel] at hscaled
  rw [lt_sub_iff_add_lt,show exp 1*x/log x*pi (x/exp 1)=
    exp 1*x*pi (x/exp 1)/log x by ring]
  apply (lt_div_iff₀ hL).mpr
  nlinarith

/-- The quantitative height40 expression is itself much larger than9005. -/
theorem quantitative_expression {x : ℝ} (hx : exp 40 ≤ x) :
    (9005:ℝ) < (37/200:ℝ)*x^2/log x^6 := by
  have hx0 : 0 < x := (exp_pos 40).trans_le hx
  have hL : (40:ℝ) ≤ log x := by simpa using log_le_log (exp_pos 40) hx
  have hp := Real.pow_div_factorial_le_exp (by linarith : 0 ≤ log x) 8
  rw [exp_log hx0] at hp
  norm_num [Nat.factorial] at hp
  have hL8 : log x^8 ≤ 40320*x := (div_le_iff₀ (by norm_num : (0:ℝ)<40320)).mp hp
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
end RamanujanPV.AnalyticMargin
