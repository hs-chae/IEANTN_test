import OldFloorProgram
namespace WinnerOldFloors
open LeanCert.Core LeanCert.Engine Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem lower_1_neg_check : checkLower (floorBody 1 (-3)) (92024/1000000) = true := by native_decide
theorem lower_1_neg : (92024/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 1 (-3)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_1_neg_check)

theorem lower_1_pos_check : checkLower (floorBody 1 (0)) (1606755/1000000) = true := by native_decide
theorem lower_1_pos : (1606755/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 1 (0)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_1_pos_check)

theorem lower_2_neg_check : checkLower (floorBody 2 (-3)) (91017/1000000) = true := by native_decide
theorem lower_2_neg : (91017/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 2 (-3)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_2_neg_check)

theorem lower_2_pos_check : checkLower (floorBody 2 (0)) (1591448/1000000) = true := by native_decide
theorem lower_2_pos : (1591448/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 2 (0)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_2_pos_check)

theorem lower_4_neg_check : checkLower (floorBody 4 (-3)) (89184/1000000) = true := by native_decide
theorem lower_4_neg : (89184/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 4 (-3)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_4_neg_check)

theorem lower_4_pos_check : checkLower (floorBody 4 (0)) (1563579/1000000) = true := by native_decide
theorem lower_4_pos : (1563579/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 4 (0)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_4_pos_check)

theorem lower_8_neg_check : checkLower (floorBody 8 (-3)) (86103/1000000) = true := by native_decide
theorem lower_8_neg : (86103/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 8 (-3)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_8_neg_check)

theorem lower_8_pos_check : checkLower (floorBody 8 (0)) (1516706/1000000) = true := by native_decide
theorem lower_8_pos : (1516706/1000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) (floorBody 8 (0)) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ lower_8_pos_check)

#print axioms lower_8_pos
end WinnerOldFloors
