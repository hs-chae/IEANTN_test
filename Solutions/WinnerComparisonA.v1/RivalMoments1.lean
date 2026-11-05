/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def config1 : DyadicConfig := {precision := -90,taylorDepth := 22}
theorem m3_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (7/3) (3/4096) 0)) 0 16383 (-(3776827/10000000)) config1=true := by native_decide
theorem m3_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (7/3) (3/4096) 0) 0 16383 (3783973/10000000) config1=true := by native_decide
theorem m3_negative_bounds :
  ((3776827/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (7/3) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (7/3) 0 y)≤(3783973/10000000) := by
  have h:=integral_bounds_from_checks false (7/3) (3/4096) (3776827/10000000) (3783973/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m3_negative_lower_check m3_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m3_negative_bounds
theorem m3_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (7/3) (3/16384) 0)) 0 16383 (-(5269357/2500000)) config1=true := by native_decide
theorem m3_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (7/3) (3/16384) 0) 0 16383 (10548447/5000000) config1=true := by native_decide
theorem m3_positive_bounds :
  ((5269357/2500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (7/3) 0 y)≤(10548447/5000000) := by
  have h:=integral_bounds_from_checks true (7/3) (3/16384) (5269357/2500000) (10548447/5000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m3_positive_lower_check m3_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m3_positive_bounds
theorem m4_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (7/3) (3/4096) 1)) 0 16383 (-(857117/5000000)) config1=true := by native_decide
theorem m4_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (7/3) (3/4096) 1) 0 16383 (860053/5000000) config1=true := by native_decide
theorem m4_negative_bounds :
  ((857117/5000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (7/3) 1 y) ∧
  (∫y in (0:ℝ)..12,moment false (7/3) 1 y)≤(860053/5000000) := by
  have h:=integral_bounds_from_checks false (7/3) (3/4096) (857117/5000000) (860053/5000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m4_negative_lower_check m4_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m4_negative_bounds
theorem m4_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (7/3) (3/16384) 1)) 0 16383 (-(15472699/10000000)) config1=true := by native_decide
theorem m4_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (7/3) (3/16384) 1) 0 16383 (3098731/2000000) config1=true := by native_decide
theorem m4_positive_bounds :
  ((15472699/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 1 y) ∧
  (∫y in (0:ℝ)..3,moment true (7/3) 1 y)≤(3098731/2000000) := by
  have h:=integral_bounds_from_checks true (7/3) (3/16384) (15472699/10000000) (3098731/2000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m4_positive_lower_check m4_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m4_positive_bounds
theorem m5_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (7/3) (3/4096) 2)) 0 16383 (-(378903/2500000)) config1=true := by native_decide
theorem m5_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (7/3) (3/4096) 2) 0 16383 (380201/2500000) config1=true := by native_decide
theorem m5_negative_bounds :
  ((378903/2500000):ℝ)≤(∫y in (0:ℝ)..12,moment false (7/3) 2 y) ∧
  (∫y in (0:ℝ)..12,moment false (7/3) 2 y)≤(380201/2500000) := by
  have h:=integral_bounds_from_checks false (7/3) (3/4096) (378903/2500000) (380201/2500000) 2 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m5_negative_lower_check m5_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m5_negative_bounds
theorem m5_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (7/3) (3/16384) 2)) 0 16383 (-(2857511/2000000)) config1=true := by native_decide
theorem m5_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (7/3) (3/16384) 2) 0 16383 (14311117/10000000) config1=true := by native_decide
theorem m5_positive_bounds :
  ((2857511/2000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 2 y) ∧
  (∫y in (0:ℝ)..3,moment true (7/3) 2 y)≤(14311117/10000000) := by
  have h:=integral_bounds_from_checks true (7/3) (3/16384) (2857511/2000000) (14311117/10000000) 2 16384
    (by norm_num) (by norm_num) (by norm_num) config1 (by decide)
    m5_positive_lower_check m5_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m5_positive_bounds
end WinnerRivalMoments
