import Mathlib

/-! Pure scalar control of the exponential factor. No numerical evaluation or
assumed actual Box moment is used in this generic lemma. -/
namespace RHOcticPush.BoxZero
open Real

lemma exp_minus_one_le_two_mul {d : ℝ} (hd : 0≤d) (hd1 : d≤1/2) :
    Real.exp d - 1 ≤ 2*d := by
  have hdlt : d<1 := by linarith
  have he := Real.exp_bound_div_one_sub_of_interval hd hdlt
  have hb : 1/(1-d) ≤ 1+2*d := by
    apply (div_le_iff₀ (by linarith : 0<1-d)).mpr
    nlinarith [mul_nonneg hd (show 0≤1-2*d by linarith)]
  linarith

lemma exp_main_inflation {d P L : ℝ} (hd : 0≤d) (hd1 : d≤1/2)
    (hP : P≤L^2) :
    Real.exp d * P ≤ P + 2*d*L^2 := by
  have he0 : 0≤Real.exp d - 1 := by
    have hh := Real.one_le_exp_iff.mpr hd
    linarith
  have h1 := mul_le_mul_of_nonneg_left hP he0
  have h2 := mul_le_mul_of_nonneg_right (exp_minus_one_le_two_mul hd hd1) (sq_nonneg L)
  nlinarith

#print axioms exp_main_inflation
end RHOcticPush.BoxZero
