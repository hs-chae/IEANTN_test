import IEANTN.Vocabulary.PowerError
import Mathlib
namespace SynergyAnalytic.HeightPoint
open Real
set_option autoImplicit false
set_option maxHeartbeats 0

theorem height_coefficient_lt_0086 : (4221/500000:ℝ)<43/5000 := by norm_num
theorem height_coefficient_lt_original_evolved :
    (4221/500000:ℝ)<9471462010471452/1000000000000000000 := by norm_num

theorem height_bound_strict {x:ℝ} (hx:0<x) :
    (4221/500000:ℝ)*x^((7/8:ℝ)-1)<
      (9471462010471452/1000000000000000000:ℝ)*x^((7/8:ℝ)-1) :=
  mul_lt_mul_of_pos_right height_coefficient_lt_original_evolved (Real.rpow_pos_of_pos hx _)

theorem height_bound_strict_on_original_interval {x:ℝ}
    (hx:x∈Set.Icc (Real.exp 330) (Real.exp 331)) :
    (4221/500000:ℝ)*x^((7/8:ℝ)-1)<
      (9471462010471452/1000000000000000000:ℝ)*x^((7/8:ℝ)-1) :=
  height_bound_strict ((Real.exp_pos 330).trans_le hx.1)

theorem shorter_prime_interval_width : (17/1000:ℝ)<9/500 := by norm_num

theorem old_0086_017_transfer_negative :
    (17/1000:ℝ)/(1000001/1000000)-(43/5000)*(5001/5000+1)<0 := by norm_num

theorem new_008442_017_transfer_positive :
    (0:ℝ)<(57/500000) ∧ (57/500000:ℝ) ≤
      (17/1000)/(1000001/1000000)-(4221/500000)*(5001/5000+1) := by norm_num

#print axioms height_coefficient_lt_0086
#print axioms height_bound_strict_on_original_interval
#print axioms shorter_prime_interval_width
end SynergyAnalytic.HeightPoint
