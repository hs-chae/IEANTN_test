/- Quantitative decay in log x from the same source-backed height data.
No Gaussian, zero-free, moment or interpolation assumption is changed. -/
import SynergyAnalytic.HeightBudgetTransfer
namespace SynergyAnalytic
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem pairedFactor_fraction_sub {D r K : ℝ} (separated : D < K) :
    pairedFactor D r K=K/(K-D)-(D/(K-D))*Real.exp (-(K-D)*r) := by
  have denominator : K-D ≠ 0 := (sub_pos.mpr separated).ne'
  rw [pairedFactor_closed denominator]
  field_simp [denominator]
  ring

theorem pairedFactor_lower_fraction {D r K epsilon : ℝ}
    (nonnegative : 0 ≤ D) (separated : D < K) (eps : 0 ≤ epsilon)
    (small : Real.exp (-(K-D)*r) ≤ epsilon) :
    (1-epsilon)*(K/(K-D)) ≤ pairedFactor D r K := by
  have denominator : 0 < K-D := sub_pos.mpr separated
  have lower : 0 ≤ D/(K-D) := div_nonneg nonnegative denominator.le
  have fraction : D/(K-D) ≤ K/(K-D) :=
    div_le_div_of_nonneg_right separated.le denominator.le
  have product := (mul_le_mul_of_nonneg_left small lower).trans
    (mul_le_mul_of_nonneg_right fraction eps)
  rw [pairedFactor_fraction_sub separated]
  nlinarith

theorem fraction_ratio_contraction {D d K L : ℝ}
    (d_nonnegative : 0 ≤ d) (lower : d ≤ D) (separated : D < K) (future : K ≤ L) :
    L/(L-D) ≤ (L*(K-d)/(K*(L-d)))*(K/(K-D)) := by
  have dK : d < K := lower.trans_lt separated
  have Kpos : 0 < K := lt_of_le_of_lt (d_nonnegative.trans lower) separated
  have Lpos : 0 < L := Kpos.trans_le future
  have KD : 0 < K-D := sub_pos.mpr separated
  have LD : 0 < L-D := by linarith
  have Ld : 0 < L-d := by linarith
  have algebra : (L*(K-d)/(K*(L-d)))*(K/(K-D))=
      (L*(K-d))/((L-d)*(K-D)) := by
    field_simp
  rw [algebra]
  apply (div_le_div_iff₀ LD (mul_pos Ld KD)).2
  have positive := mul_nonneg Lpos.le
    (mul_nonneg (sub_nonneg.mpr future) (sub_nonneg.mpr lower))
  nlinarith

theorem pairedFactor_relative_contraction {D d r K L epsilon : ℝ}
    (d_nonnegative : 0 ≤ d) (lower : d ≤ D) (separated : D < K) (future : K ≤ L)
    (eps_nonnegative : 0 ≤ epsilon) (eps_small : epsilon < 1)
    (small : Real.exp (-(K-D)*r) ≤ epsilon) :
    pairedFactor D r L ≤
      (L*(K-d)/(K*(L-d))/(1-epsilon))*pairedFactor D r K := by
  have nonnegative : 0 ≤ D := d_nonnegative.trans lower
  have dK : d < K := lower.trans_lt separated
  have Kpos : 0 < K := lt_of_le_of_lt nonnegative separated
  have Lpos : 0 < L := Kpos.trans_le future
  have Ld : 0 < L-d := by linarith
  have eps : 0 < 1-epsilon := sub_pos.mpr eps_small
  let q := L*(K-d)/(K*(L-d))
  have q_nonnegative : 0 ≤ q := div_nonneg
    (mul_nonneg Lpos.le (sub_nonneg.mpr dK.le)) (mul_nonneg Kpos.le Ld.le)
  have amplified := mul_le_mul_of_nonneg_left
    (pairedFactor_lower_fraction nonnegative separated eps_nonnegative small)
    (div_nonneg q_nonnegative eps.le)
  have cancellation : (q/(1-epsilon))*((1-epsilon)*(K/(K-D)))=q*(K/(K-D)) := by
    field_simp
  rw [cancellation] at amplified
  exact (pairedFactor_upper_fraction (r:=r) nonnegative (separated.trans_le future)).trans
    ((fraction_ratio_contraction d_nonnegative lower separated future).trans amplified)

theorem slope_exponential_small {D : ℝ} (upper : D ≤ 163) :
    Real.exp (-((330:ℝ)-D)/8) ≤ 1/100000000 := by
  have exponent : -((330:ℝ)-D)/8 ≤ -20 := by linarith
  have huge : (100000000:ℝ) ≤ Real.exp 20 :=
    (by norm_num : (100000000:ℝ) ≤ (8/3:ℝ)^20).trans
      (exp_nat_lower_eight_thirds 20)
  have inverse : Real.exp (-20) ≤ (1:ℝ)/100000000 := by
    rw [Real.exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) huge
  exact (Real.exp_le_exp.mpr exponent).trans inverse

theorem pairedFactor_77_163_contraction {D L : ℝ}
    (lower : 77 ≤ D) (upper : D ≤ 163) (future : 330 ≤ L) :
    pairedFactor D (1/8) L ≤
      (L*253/(330*(L-77))/(1-1/100000000))*pairedFactor D (1/8) 330 := by
  have small : Real.exp (-((330:ℝ)-D)*(1/8)) ≤ 1/100000000 := by
    convert slope_exponential_small upper using 1 <;> ring
  simpa only [show (330:ℝ)-77=253 by norm_num] using
    (pairedFactor_relative_contraction (d:=77) (K:=330)
      (by norm_num) lower (by linarith) future (by norm_num) (by norm_num) small)

#print axioms pairedFactor_lower_fraction
#print axioms fraction_ratio_contraction
#print axioms pairedFactor_relative_contraction
#print axioms slope_exponential_small
#print axioms pairedFactor_77_163_contraction
end SynergyAnalytic
