import SynergyAnalytic.CoarseProfile
import SynergyAnalytic.UniformFive
import SynergyAnalytic.RightHundred
namespace SynergyAnalytic
open Real WinnerOriginalScalars WinnerNewHeightSource WinnerDensitySource
set_option maxHeartbeats 0

theorem coarse_coefficient_two_thousand :
    densityCoefficient (7/8) (3681/10000) (3599/10000) WinnerNewHeightSource.alpha 5 100 sourceSmoothingR ≤ 2000 := by
  have hR : sourceSmoothingR ≤ 1 := by norm_num [sourceSmoothingR,height]
  have hR0 : 0 ≤ sourceSmoothingR := by unfold sourceSmoothingR;positivity
  have he : Real.exp (2*WinnerNewHeightSource.alpha) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num [WinnerNewHeightSource.alpha] : 2*WinnerNewHeightSource.alpha ≤ 1)).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hpref : sourceSmoothingR*Real.exp (2*WinnerNewHeightSource.alpha)/(2*Real.pi*(3681/10000:ℝ)) ≤ 3/2 := by
    have hpi : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
    calc
      _ ≤ (1:ℝ)*3/(2*3*(3681/10000)) := by gcongr
      _ ≤ 3/2 := by norm_num
  have hUV : (5:ℝ)^((1:ℝ)/4)*(100:ℝ)^((3:ℝ)/4) ≤ 100 := by
    calc
      _ ≤ (100:ℝ)^((1:ℝ)/4)*(100:ℝ)^((3:ℝ)/4) := by gcongr <;> norm_num
      _ = 100 := by rw [←Real.rpow_add (by norm_num : (0:ℝ)<100)];norm_num
  have hphi : interpolationPhi (3599/10000) 5 100 ≤ 3/2 := by
    have he0 : Real.exp (-8*(3599/10000:ℝ)/3-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    unfold interpolationPhi
    linarith
  have harg : (2*(3681/10000:ℝ)+2*(3599/10000)*((2:ℝ)*(7/8)-1))*
      interpolationPhi (3599/10000) 5 100 ≤ 2 := by nlinarith
  have hexp : Real.exp ((2*(3681/10000:ℝ)+2*(3599/10000)*((2:ℝ)*(7/8)-1))*
      interpolationPhi (3599/10000) 5 100) ≤ 9 := by
    apply (Real.exp_le_exp.mpr harg).trans
    have he2 : Real.exp 2=(Real.exp 1)^2 := by rw [←Real.exp_nat_mul];norm_num
    rw [he2]
    have he1 : Real.exp (1:ℝ) ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    exact (pow_le_pow_left₀ (Real.exp_pos _).le he1 2).trans (by norm_num)
  unfold densityCoefficient interpolationCoefficient
  norm_num only at hUV ⊢
  have h1 := mul_le_mul hpref hUV (by positivity) (by norm_num : (0:ℝ) ≤ 3/2)
  have h2 := mul_le_mul h1 hexp (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ (3/2)*100)
  nlinarith

theorem coarse_slope_nonneg : 0 ≤ densitySlope (3599/10000) 5 100 := by
  unfold densitySlope interpolationPhi
  have hl : 0 ≤ Real.log ((100:ℝ)/5) := Real.log_nonneg (by norm_num)
  positivity

/-- Whole source density for the far tail. All three new Jcaps are the only
new numerical residuals; the deliberately loose scalar budget is kernel-proved. -/
theorem source_coarse_density {sigma T:ℝ}
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcaps:UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) (hT:height ≤ T) :
    IEANTN.zetaN' sigma T ≤ WinnerDensityA.poly 2000 6 sigma T := by
  exact coarse_count h (by norm_num) (by norm_num) (by norm_num) le_rfl hT (by norm_num) (by norm_num)
    (fun u hu=>actual_left_five h hcaps hu) right_hundred coarse_coefficient_two_thousand coarse_slope_nonneg hRH hs hs'

theorem source_coarse_density_closed {sigma T:ℝ}
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcaps:UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) (hT:height ≤ T) :
    IEANTN.zetaZeroesSum (Set.Ioo sigma 1) (Set.Ioc 0 T) (fun _=>(1:ℝ)) ≤ WinnerDensityA.poly 2000 6 sigma T := by
  exact WinnerDensityA.count_closed hT (fun u hu=>source_coarse_density h hcaps hRH hs hs' hu)

#print axioms coarse_coefficient_two_thousand
#print axioms source_coarse_density_closed
end SynergyAnalytic
