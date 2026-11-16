import SynergyAnalytic.EndpointPNT
import SynergyAnalytic.EndpointAnyWidth
namespace SynergyAnalytic
open Real
set_option autoImplicit false
set_option maxHeartbeats 0

theorem pairedFactor_upper_fraction {D r L : ℝ} (hD : 0 ≤ D) (hDL : D < L) :
    pairedFactor D r L ≤ L/(L-D) := by
  have hd : 0 < L-D := sub_pos.mpr hDL
  rw [pairedFactor_closed hd.ne']
  calc
    _ = L/(L-D)-(D/(L-D))*Real.exp (-(L-D)*r) := by field_simp;ring
    _ ≤ L/(L-D) := sub_le_self _ (mul_nonneg (div_nonneg hD hd.le) (Real.exp_pos _).le)

theorem spectralBase_330_tiny : spectralBase 330 110 ≤ 1/1000000000000 := by
  let tau : ℝ := 110+1/1000000000
  have htau : 0 ≤ tau ∧ tau ≤ 111 := by norm_num [tau]
  have hp : 1 ≤ Real.pi := Real.pi_gt_three.le.trans' (by norm_num)
  have hi : 1/Real.pi ≤ (1:ℝ) := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
  have hden : 1 ≤ 2*Real.pi := by linarith
  have hb : tau^2/(2*Real.pi)+(2+1/Real.pi)*tau ≤ 20000 := by
    have hdiv := div_le_self (sq_nonneg tau) hden
    have hm := mul_le_mul hi htau.2 htau.1 (by norm_num : (0:ℝ)≤1)
    nlinarith
  have he : Real.exp (-(330:ℝ)/8) ≤ Real.exp (-40) := Real.exp_le_exp.mpr (by norm_num)
  have hsmall : (20000:ℝ)*Real.exp (-40) ≤ 1/1000000000000 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 40)).mpr
    exact (by norm_num : (20000:ℝ) ≤ (1/1000000000000)*(8/3:ℝ)^40).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 40) (by norm_num))
  unfold spectralBase
  norm_num only [show (10:ℝ)^9=1000000000 by norm_num]
  have hb' : 0 ≤ (110+1/1000000000:ℝ)^2/(2*Real.pi)+(2+1/Real.pi)*(110+1/1000000000) := by positivity
  have hfinal := (mul_le_mul he (by simpa only [tau] using hb) hb' (Real.exp_pos _).le).trans (by simpa only [mul_comm] using hsmall)
  norm_num only at hfinal
  exact hfinal

/-- Once the new finite sum is kernel enclosed by0.008434, the EXISTING
analytic tail and truncation allowances give0.008442. No new tail premise or
numerical exponential assumption is introduced. -/
theorem height_budget_of_finite_sum {a c D : ℕ→ℝ} {n : ℕ}
    (hfinite : 2*(∑i∈Finset.range n,((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤ 4217/500000) :
    finalCoefficient a c D n ≤ 4221/500000 := by
  have ht := pairedFactor_upper_fraction (r:=(1/8:ℝ)) (by norm_num : (0:ℝ)≤160) (by norm_num : (160:ℝ)<330)
  have hc := pairedFactor_upper_fraction (r:=(1/8:ℝ)) (by norm_num : (0:ℝ)≤880/3) (by norm_num : (880/3:ℝ)<330)
  unfold finalCoefficient profileCoefficient
  have hb := spectralBase_330_tiny
  norm_num at ht hc
  nlinarith

#print axioms pairedFactor_upper_fraction
#print axioms spectralBase_330_tiny
#print axioms height_budget_of_finite_sum
end SynergyAnalytic
