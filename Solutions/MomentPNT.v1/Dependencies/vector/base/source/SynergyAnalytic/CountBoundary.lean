import SynergyAnalytic.CoarseElementary
import WinnerDensityA.Moment
namespace SynergyAnalytic
open Real WinnerDensityA
set_option maxHeartbeats 0

theorem exp_nat_lower_eight_thirds (n:ℕ) : (8/3:ℝ)^n ≤ Real.exp n := by
  calc
    _ ≤ (Real.exp 1)^n := pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) n
    _ = Real.exp n := by rw [←Real.exp_nat_mul];simp

/-- The count-at-truncation contribution at tau110 is retained explicitly.
A very loose pure-kernel bound makes it two positive exponential rows. -/
theorem count_boundary_affine {sigma:ℝ} (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) :
    4*Real.pi*(poly 2000 6 sigma (Real.exp 110)/Real.exp 110) ≤
      (1/1000000000000:ℝ)*Real.exp ((880/3:ℝ)*((7/8)-sigma))+1/1000000000000 := by
  have hq : (110:ℝ)^(5-2*sigma) ≤ (110:ℝ)^4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 110)
      (show 5-2*sigma ≤ (4:ℝ) by linarith)
    simpa only [Real.rpow_ofNat] using hh
  have hex : (Real.exp (110:ℝ))^(8*(1-sigma)/3)/Real.exp 110 =
      Real.exp (-220/3)*Real.exp ((880/3:ℝ)*((7/8)-sigma)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_sub,←Real.exp_add]
    congr 1
    ring
  have hsmallMain : (16:ℝ)*2000*110^4*Real.exp (-220/3) ≤ 1/1000000000000 := by
    have hExp : Real.exp (-220/3:ℝ) ≤ Real.exp (-72) := Real.exp_le_exp.mpr (by norm_num)
    apply (mul_le_mul_of_nonneg_left hExp (by norm_num : (0:ℝ) ≤ 16*2000*110^4)).trans
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 72)).mpr
    exact (by norm_num : (16:ℝ)*2000*110^4 ≤ (1/1000000000000)*(8/3:ℝ)^72).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 72) (by norm_num))
  have hsmallBoundary : (96:ℝ)*110^2*Real.exp (-110) ≤ 1/1000000000000 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 110)).mpr
    exact (by norm_num : (96:ℝ)*110^2 ≤ (1/1000000000000)*(8/3:ℝ)^110).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 110) (by norm_num))
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have heq : 4*Real.pi*(poly 2000 6 sigma (Real.exp 110)/Real.exp 110) =
      (4*Real.pi*2000*Real.exp (-220/3)*(110:ℝ)^(5-2*sigma))*Real.exp ((880/3:ℝ)*((7/8)-sigma))+
        24*Real.pi*110^2*Real.exp (-110) := by
    unfold poly
    rw [Real.log_exp]
    have he : (Real.exp 110)⁻¹=Real.exp (-110) := (Real.exp_neg 110).symm
    rw [add_div]
    rw [show (2000*(Real.exp (110:ℝ))^(8*(1-sigma)/3)*(110:ℝ)^(5-2*sigma))/Real.exp 110 =
      2000*(110:ℝ)^(5-2*sigma)*((Real.exp (110:ℝ))^(8*(1-sigma)/3)/Real.exp 110) by ring]
    rw [hex]
    rw [show (6:ℝ)*110^2/Real.exp 110=6*110^2*Real.exp (-110) by rw [div_eq_mul_inv,he]]
    ring
  rw [heq]
  have hMain : 4*Real.pi*2000*Real.exp (-220/3)*(110:ℝ)^(5-2*sigma) ≤ 1/1000000000000 := by
    apply LE.le.trans _ hsmallMain
    have hh := mul_le_mul hp hq (by positivity) (by norm_num : (0:ℝ) ≤ 4)
    nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ 4*2000*Real.exp (-220/3))]
  have hBoundary : 24*Real.pi*110^2*Real.exp (-110) ≤ 1/1000000000000 := by
    apply LE.le.trans _ hsmallBoundary
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ) ≤ 24*110^2*Real.exp (-110))]
  exact add_le_add (mul_le_mul_of_nonneg_right hMain (Real.exp_pos _).le) hBoundary

#print axioms count_boundary_affine
end SynergyAnalytic
