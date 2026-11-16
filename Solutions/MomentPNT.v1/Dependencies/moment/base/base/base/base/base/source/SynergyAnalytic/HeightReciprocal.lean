import SynergyAnalytic.HeightPointGeometry
namespace SynergyAnalytic.HeightPoint
open Real
set_option autoImplicit false
set_option maxHeartbeats 0

theorem heightEndpoint_formula (i:Nat) :
    heightEndpoint i=WinnerOriginalScalars.height*(survival i)⁻¹^6 := by
  have hH : (0:ℝ)<WinnerOriginalScalars.height := by norm_num [WinnerOriginalScalars.height]
  rw [heightEndpoint,logEndpoint,logH,Real.exp_add,Real.exp_log hH]
  congr 1
  rw [show (6:ℝ)=(6:ℕ) by norm_num,Real.exp_nat_mul,
    Real.exp_log (inv_pos.mpr (survival_pos i))]

theorem reciprocal_heightEndpoint (i:Nat) :
    1/heightEndpoint i=survival i^6/WinnerOriginalScalars.height := by
  rw [heightEndpoint_formula]
  have hs : survival i≠0 := (survival_pos i).ne'
  have hH : WinnerOriginalScalars.height≠0 := by norm_num [WinnerOriginalScalars.height]
  field_simp

theorem reciprocal_cell_weight (i:Nat) :
    1/heightEndpoint i-1/heightEndpoint (i+1)=
      (survival i^6-survival (i+1)^6)/WinnerOriginalScalars.height := by
  rw [reciprocal_heightEndpoint,reciprocal_heightEndpoint]
  ring

#print axioms reciprocal_cell_weight
end SynergyAnalytic.HeightPoint
