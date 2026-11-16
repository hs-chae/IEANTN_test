import SynergyAnalytic.UniformBasis
namespace SynergyAnalytic
open Real Set WinnerOriginalScalars WinnerBetaA.HeightSource
set_option maxHeartbeats 0

theorem sourceM0_le_two : sourceM0 ≤ 2 := by
  have hs : Real.sqrt (6/5:ℝ) ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩
  unfold sourceM0
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · linarith

theorem universalPeak_le_one : universalPeak ≤ 1 := by
  unfold universalPeak peakLog
  apply Real.exp_le_one_iff.mpr
  have hl : 0 ≤ Real.log (6*(601/2500:ℝ)) := Real.log_nonneg (by norm_num)
  linarith

theorem gaussianArea_le_three : gaussianArea ≤ 3 := by
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hs : Real.sqrt (Real.pi/(601/2500:ℝ)) ≤ 6 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · apply (div_le_iff₀ (by norm_num : (0:ℝ)<601/2500)).mpr
      linarith
  unfold gaussianArea
  linarith

theorem mean_one_coarse : meanOne height ≤ 1 := by
  have hp : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hl : 28 ≤ Real.log height := source_log_ge28 le_rfl
  have hq : (0:ℝ)<Real.pi := Real.pi_pos
  unfold meanOne
  have hb : (6:ℝ)/Real.pi^2+(131/125)/Real.log height  ≤  (6:ℝ)/3^2+(131/125)/28 := by gcongr
  exact hb.trans (by norm_num)

theorem mean_two_coarse : meanTwo height ≤ 1 := by
  have hp0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpl : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hm0 : 0 ≤ sourceM0 := (source_mzero_pos).le
  have hm : sourceM0 ≤ 2 := sourceM0_le_two
  have hl : 28 ≤ Real.log height := source_log_ge28 le_rfl
  have hH : (1:ℝ) ≤ height := by norm_num [height]
  unfold meanTwo
  have hb : Real.pi*sourceM0*(31/50)/Real.log height+6*sourceM0/(Real.pi*height)+
      Real.pi*sourceM0*(131/125)/(height*Real.log height)  ≤ 
      (4:ℝ)*2*(31/50)/28+6*2/(3*height)+4*2*(131/125)/(height*28) := by gcongr
  exact hb.trans (by norm_num [height])

theorem zeta_scale_coarse : (1461/1000:ℝ)/zetaScale height ≤ 1/1000 := by
  have hH : (0:ℝ)<height := by norm_num [height]
  have hl : 28 ≤ Real.log height := source_log_ge28 le_rfl
  have hp : (100:ℝ) ≤ height^((1:ℝ)/6) := by
    have hpow := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 100^6)
      (by norm_num [height] : (100:ℝ)^6 ≤ height) (by norm_num : (0:ℝ) ≤ 1/6)
    have he : ((100:ℝ)^6)^((1:ℝ)/6)=100 := by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 100)]
      norm_num
    simpa only [he] using hpow
  have hz : (611/1000:ℝ)*100*28 ≤ zetaScale height := by unfold zetaScale;gcongr
  have hzp : 0<zetaScale height := by linarith
  exact (div_le_iff₀ hzp).mpr (by linarith)

theorem exp_half_le_two {x:ℝ} (hx:x ≤ 1/2) : Real.exp x ≤ 2 := by
  have he : (Real.exp ((1:ℝ)/2))^2=Real.exp 1 := by rw [←Real.exp_nat_mul];norm_num
  have hp := Real.exp_pos ((1:ℝ)/2)
  have hb := Real.exp_one_lt_d9
  have hl : Real.exp ((1:ℝ)/2) ≤ 2 := by nlinarith
  exact (Real.exp_le_exp.mpr hx).trans hl

#print axioms mean_one_coarse
#print axioms mean_two_coarse
#print axioms zeta_scale_coarse
end SynergyAnalytic
