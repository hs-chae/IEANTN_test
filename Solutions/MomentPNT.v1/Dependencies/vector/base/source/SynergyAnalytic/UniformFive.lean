import SynergyAnalytic.CoarseElementary
namespace SynergyAnalytic
open Real WinnerOriginalScalars WinnerBetaA.ActualObject WinnerNewHeightSource
set_option maxHeartbeats 0

theorem uniform_basis_five : uniformBasisBudget height 1 1 28 (1/1000) (1/1000) (1/1000)
    (373/200) (1273/2000) (129/250) ≤ 5 := by
  have hC : (1+(1/1000:ℝ))*(373/200+(2/28)*(1273/2000)+(1/28^2)*(129/250)+universalPeak)+
      (1+1/(1/1000:ℝ))*(1/1000:ℝ)^2*(gaussianArea+1) ≤ 3 := by
    have hp := universalPeak_le_one
    have hg := gaussianArea_le_three
    nlinarith
  have hHp : 0<height := by norm_num [height]
  have hl : 28 ≤ Real.log height := source_log_ge28 le_rfl
  have hr : (1000:ℝ) ≤ height^((1:ℝ)/3) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1000^3)
      (by norm_num [height] : (1000:ℝ)^3 ≤ height) (by norm_num : (0:ℝ) ≤ 1/3)
    have he : ((1000:ℝ)^3)^((1:ℝ)/3)=1000 := by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1000)]
      norm_num
    simpa only [he] using hh
  have hrem : (1+1/(1/1000:ℝ))*gaussianArea/(height^((1:ℝ)/3)*Real.log height^3) ≤ 1/1000 := by
    calc
      _ ≤ (1+1/(1/1000:ℝ))*3/(1000*28^3) := by
        have hg := gaussianArea_le_three
        have hg0 : 0<gaussianArea := by unfold gaussianArea;positivity
        gcongr
      _ ≤ 1/1000 := by norm_num
  have homega : Real.exp ((601/5000:ℝ)/(2*height^2)) ≤ 2 :=
    exp_half_le_two (by norm_num [height])
  have hg0 : 0<gaussianArea := by unfold gaussianArea;positivity
  have hp0 : 0<universalPeak := Real.exp_pos _
  unfold uniformBasisBudget
  norm_num only [one_mul] at *
  calc
    _ ≤ 2*2*((1+(1/1000:ℝ))*(611/1000:ℝ)^2*3+1/1000) := by gcongr <;> norm_num <;> norm_num
    _ ≤ 5 := by norm_num

/-- Entire future-height coarse moment needed for the far tail, with no
extra Gaussian grid, numerical scalar leaf, or desired moment assumption. -/
theorem actual_left_five {d delta T:ℝ} (h:PrimaryInputs d delta)
    (hcaps:UniversalBasisCaps (373/200) (1273/2000) (129/250)) (hT:height ≤ T) :
    sourceMoment T (1/2) ≤ 5*T^((4:ℝ)/3)*Real.log T^3 := by
  exact actual_left_uniform_basis h hcaps le_rfl hT (by norm_num) (source_log_ge28 le_rfl)
    (by norm_num) (by norm_num) mean_one_coarse mean_two_coarse zeta_scale_coarse
    (by norm_num) (by norm_num) (by norm_num) uniform_basis_five

#print axioms uniform_basis_five
#print axioms actual_left_five
end SynergyAnalytic
