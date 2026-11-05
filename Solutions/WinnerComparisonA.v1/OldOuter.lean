import OldOuterProgram
namespace WinnerOldOuter
open LeanCert.Core LeanCert.Engine Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 := outerBody (13/1000) (987/494000) (1698779/1000000) (36/5)
theorem row0_check : checkLower row0 494 (4225800/1000000000)=true := by native_decide
theorem row0_lower : (4225800/1000000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 (494-1), Expr.eval (sumBodyRealEnv k) row0 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ _ row0_check)

def row1 := outerBody (1/1) (1/500) (336493/200000) (719/100)
theorem row1_check : checkLower row1 500 (2484107/1000000000)=true := by native_decide
theorem row1_lower : (2484107/1000000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 (500-1), Expr.eval (sumBodyRealEnv k) row1 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ _ row1_check)

def row2 := outerBody (2/1) (1/500) (1652763/1000000) (179/25)
theorem row2_check : checkLower row2 1000 (2243849/1000000000)=true := by native_decide
theorem row2_lower : (2243849/1000000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 (1000-1), Expr.eval (sumBodyRealEnv k) row2 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ _ row2_check)

def row3 := outerBody (4/1) (1/500) (1602809/1000000) (178/25)
theorem row3_check : checkLower row3 2000 (969649/1000000000)=true := by native_decide
theorem row3_lower : (969649/1000000000:ℝ) ≤ ∑ k ∈ Finset.Icc 0 (2000-1), Expr.eval (sumBodyRealEnv k) row3 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using (checkLower_sound _ _ _ row3_check)

#print axioms row3_lower
end WinnerOldOuter
