import SynergyAnalytic.HeightPointLogGrid
namespace SynergyAnalytic.HeightPoint
open Real
set_option autoImplicit false
set_option maxHeartbeats 0

theorem endSurvival_pos : 0 < endSurvival := Real.exp_pos _
theorem endSurvival_le_one : endSurvival ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  linarith [h_range.2]

theorem fraction_bounds (i : Nat) :
    0 ≤ ((min i logCellCount:Nat):ℝ)/logCellCount ∧ ((min i logCellCount:Nat):ℝ)/logCellCount ≤ 1 := by
  have hn : (0:ℝ)<logCellCount := by norm_num [logCellCount]
  refine ⟨by positivity,?_⟩
  apply (div_le_one hn).mpr
  exact_mod_cast Nat.min_le_right i logCellCount

theorem survival_bounds (i : Nat) : endSurvival ≤ survival i ∧ survival i ≤ 1 := by
  have hf := fraction_bounds i
  have hq := endSurvival_le_one
  have hp := endSurvival_pos
  have hmul := mul_le_mul_of_nonneg_right hf.2 (sub_nonneg.mpr hq)
  have hm0 := mul_nonneg hf.1 (sub_nonneg.mpr hq)
  constructor <;> dsimp only [survival] <;> linarith

theorem survival_pos (i : Nat) : 0 < survival i := endSurvival_pos.trans_le (survival_bounds i).1

theorem survival_antitone : Antitone survival := by
  intro i j hij
  have hmin : min i logCellCount ≤ min j logCellCount := min_le_min hij le_rfl
  have hminR : ((min i logCellCount:Nat):ℝ) ≤ (min j logCellCount:Nat) := by exact_mod_cast hmin
  have hf := div_le_div_of_nonneg_right hminR (show (0:ℝ) ≤ logCellCount by positivity)
  have hm := mul_le_mul_of_nonneg_right hf (sub_nonneg.mpr endSurvival_le_one)
  dsimp only [survival]
  linarith

theorem logEndpoint_monotone : Monotone logEndpoint := by
  intro i j hij
  have hs := survival_antitone hij
  have hi := survival_pos i
  have hj := survival_pos j
  have hInv : (survival i)⁻¹ ≤ (survival j)⁻¹ := inv_le_inv₀ hi hj |>.mpr hs
  have hlog := Real.log_le_log (inv_pos.mpr hi) hInv
  dsimp only [logEndpoint]
  linarith

theorem heightEndpoint_monotone : Monotone heightEndpoint := fun _ _ h=>Real.exp_le_exp.mpr (logEndpoint_monotone h)

theorem heightEndpoint_zero : heightEndpoint 0=WinnerOriginalScalars.height := by
  have hH : (0:ℝ)<WinnerOriginalScalars.height := by norm_num [WinnerOriginalScalars.height]
  simp only [heightEndpoint,logEndpoint,survival,Nat.zero_min,Nat.cast_zero,zero_div,zero_mul,
    sub_zero,inv_one,Real.log_one,mul_zero,add_zero]
  exact Real.exp_log hH

theorem heightEndpoint_last : heightEndpoint logCellCount=Real.exp 60 := by
  have hn : (logCellCount:ℝ)≠0 := by norm_num [logCellCount]
  have he : survival logCellCount=endSurvival := by
    simp only [survival,Nat.min_self,div_self hn,one_mul,sub_sub_cancel]
  rw [heightEndpoint,logEndpoint,he,Real.log_inv]
  unfold endSurvival
  rw [Real.log_exp]
  congr 1
  ring

theorem log_heightEndpoint (i : Nat) : Real.log (heightEndpoint i)=logEndpoint i := Real.log_exp _

#print axioms heightEndpoint_monotone
#print axioms heightEndpoint_zero
#print axioms heightEndpoint_last
end SynergyAnalytic.HeightPoint
