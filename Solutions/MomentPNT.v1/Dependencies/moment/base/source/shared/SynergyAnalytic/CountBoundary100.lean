/- Earlier truncation threshold: derived from the same coarse count statement.
All added exponential allowances are proved here; no new density input is assumed. -/
import SynergyAnalytic.CountBoundary
namespace SynergyAnalytic
open Real WinnerDensityA
set_option maxHeartbeats 200000
theorem count_boundary_affine_at100_narrow {sigma:ℝ} (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) :
    4*Real.pi*(poly 2000 6 sigma (Real.exp 100)/Real.exp 100) ≤
      (1/1000000000000:ℝ)*Real.exp ((800/3:ℝ)*((7/8)-sigma))+1/1000000000000 := by
  have hq : (100:ℝ)^(5-2*sigma) ≤ (100:ℝ)^4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 100)
      (show 5-2*sigma ≤ (4:ℝ) by linarith)
    simpa only [Real.rpow_ofNat] using hh
  have hex : (Real.exp (100:ℝ))^(8*(1-sigma)/3)/Real.exp 100 =
      Real.exp (-200/3)*Real.exp ((800/3:ℝ)*((7/8)-sigma)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_sub,←Real.exp_add]
    congr 1
    ring
  have hsmallMain : (16:ℝ)*2000*100^4*Real.exp (-200/3) ≤ 1/1000000000000 := by
    have hExp : Real.exp (-200/3:ℝ) ≤ Real.exp (-66) := Real.exp_le_exp.mpr (by norm_num)
    apply (mul_le_mul_of_nonneg_left hExp (by norm_num : (0:ℝ) ≤ 16*2000*100^4)).trans
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 66)).mpr
    exact (by norm_num : (16:ℝ)*2000*100^4 ≤ (1/1000000000000)*(8/3:ℝ)^66).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 66) (by norm_num))
  have hsmallBoundary : (96:ℝ)*100^2*Real.exp (-100) ≤ 1/1000000000000 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 100)).mpr
    exact (by norm_num : (96:ℝ)*100^2 ≤ (1/1000000000000)*(8/3:ℝ)^100).trans
      (mul_le_mul_of_nonneg_left (exp_nat_lower_eight_thirds 100) (by norm_num))
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have heq : 4*Real.pi*(poly 2000 6 sigma (Real.exp 100)/Real.exp 100) =
      (4*Real.pi*2000*Real.exp (-200/3)*(100:ℝ)^(5-2*sigma))*Real.exp ((800/3:ℝ)*((7/8)-sigma))+
        24*Real.pi*100^2*Real.exp (-100) := by
    unfold poly
    rw [Real.log_exp]
    have he : (Real.exp 100)⁻¹=Real.exp (-100) := (Real.exp_neg 100).symm
    rw [add_div]
    rw [show (2000*(Real.exp (100:ℝ))^(8*(1-sigma)/3)*(100:ℝ)^(5-2*sigma))/Real.exp 100 =
      2000*(100:ℝ)^(5-2*sigma)*((Real.exp (100:ℝ))^(8*(1-sigma)/3)/Real.exp 100) by ring]
    rw [hex]
    rw [show (6:ℝ)*100^2/Real.exp 100=6*100^2*Real.exp (-100) by rw [div_eq_mul_inv,he]]
    ring
  rw [heq]
  have hMain : 4*Real.pi*2000*Real.exp (-200/3)*(100:ℝ)^(5-2*sigma) ≤ 1/1000000000000 := by
    apply LE.le.trans _ hsmallMain
    have hh := mul_le_mul hp hq (by positivity) (by norm_num : (0:ℝ) ≤ 4)
    nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ 4*2000*Real.exp (-200/3))]
  have hBoundary : 24*Real.pi*100^2*Real.exp (-100) ≤ 1/1000000000000 := by
    apply LE.le.trans _ hsmallBoundary
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ) ≤ 24*100^2*Real.exp (-100))]
  exact add_le_add (mul_le_mul_of_nonneg_right hMain (Real.exp_pos _).le) hBoundary


theorem count_boundary_affine_at100 {sigma : ℝ} (hs : (3/4:ℝ) ≤ sigma)
    (hs' : sigma ≤ 7/8) :
    4*Real.pi*(poly 2000 6 sigma (Real.exp 100)/Real.exp 100) ≤
      (1/1000000000000:ℝ)*Real.exp ((880/3:ℝ)*((7/8)-sigma))+1/1000000000000 := by
  have small := count_boundary_affine_at100_narrow hs hs'
  have exponent : (800/3:ℝ)*((7/8)-sigma) ≤ (880/3:ℝ)*((7/8)-sigma) := by
    nlinarith
  exact small.trans (add_le_add (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr exponent) (by norm_num : (0:ℝ) ≤ 1/1000000000000)) le_rfl)

#print axioms count_boundary_affine_at100_narrow
#print axioms count_boundary_affine_at100
end SynergyAnalytic
