/- Earlier-onset spectral allowance proved from the existing exact source formula. -/
import SynergyAnalytic.HeightBudgetTransfer
namespace SynergyAnalytic
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem spectralBase_300_tiny : spectralBase 300 100 ≤ 1/1000000000000 := by
  let tau : ℝ := 100+1/1000000000
  have htau : 0 ≤ tau ∧ tau ≤ 101 := by norm_num [tau]
  have hp : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hi : 1/Real.pi ≤ (1/3:ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hp
  have hden : 6 ≤ 2*Real.pi := by linarith
  have hdiv : tau^2/(2*Real.pi) ≤ tau^2/6 :=
    div_le_div_of_nonneg_left (sq_nonneg tau) (by norm_num) hden
  have hsquare : tau^2 ≤ (101:ℝ)^2 := pow_le_pow_left₀ htau.1 htau.2 2
  have hm := mul_le_mul_of_nonneg_right hi htau.1
  have hb : tau^2/(2*Real.pi)+(2+1/Real.pi)*tau ≤ 2000 := by
    nlinarith
  have he : Real.exp (-(300:ℝ)/8) ≤ Real.exp (-37) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hsmall : (2000:ℝ)*Real.exp (-37) ≤ 1/1000000000000 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 37)).mpr
    exact (by norm_num : (2000:ℝ) ≤ (1/1000000000000)*(8/3:ℝ)^37).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 37) (by norm_num))
  unfold spectralBase
  have nonnegative : 0 ≤ (100+1/1000000000:ℝ)^2/(2*Real.pi)+
      (2+1/Real.pi)*(100+1/1000000000) := by positivity
  have bound := (mul_le_mul he (by simpa only [tau] using hb) nonnegative
    (Real.exp_pos _).le).trans (by simpa only [mul_comm] using hsmall)
  norm_num only [show (10:ℝ)^9=1000000000 by norm_num] at bound ⊢
  exact bound

#print axioms spectralBase_300_tiny
end SynergyAnalytic
