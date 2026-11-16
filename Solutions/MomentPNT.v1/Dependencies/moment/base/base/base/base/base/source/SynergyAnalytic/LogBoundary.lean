import DensityTailMoments
import OriginalScalarSemantics
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars CH2QRH
set_option maxHeartbeats 0

/-- A deliberately loose global allowance for the original6log²T boundary
term. This proof uses elementary exponential bounds, not a native log check. -/
theorem source_log_le32 : Real.log height≤32 := by
  have hHp : 0<height := by norm_num [height]
  apply Real.exp_le_exp.mp
  rw [Real.exp_log hHp]
  calc
    height ≤ (8/3:ℝ)^32 := by norm_num [height]
    _ ≤ (Real.exp 1)^32 := pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) 32
    _ = Real.exp 32 := by rw [←Real.exp_nat_mul];norm_num

theorem log_boundary_budget {T : ℝ} (hT : height≤T) :
    (∫u in height..T,6*Real.log u^2/u^2)≤(1/100000000:ℝ) := by
  have hH : 1<height := by norm_num [height]
  have ht0 : 0<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hlog : 0<Real.log T := Real.log_pos (hH.trans_le hT)
  have htail := log_square_reciprocal_tail hH hT
  have hpos : 0≤Real.log T^2/T := by positivity
  have hsmall : (Real.log height^2+2*Real.log height+2)/height≤(1/600000000:ℝ) := by
    have hl : 0≤Real.log height := Real.log_nonneg hH.le
    have hb := source_log_le32
    have hs : Real.log height^2≤(32:ℝ)^2 := pow_le_pow_left₀ hl hb 2
    norm_num [height] at *
    nlinarith
  have hh : (∫u in height..T,Real.log u^2/u^2)≤(1/600000000:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤6)
  rw [←intervalIntegral.integral_const_mul] at hm
  convert hm using 1 <;> first | rfl | ring

#print axioms log_boundary_budget
end SynergyAnalytic
