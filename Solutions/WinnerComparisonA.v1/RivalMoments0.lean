/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def config0 : DyadicConfig := {precision := -90,taylorDepth := 22}
theorem m0_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (10/3) (3/4096) 0)) 0 16383 (-(2588061/10000000)) config0=true := by native_decide
theorem m0_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (10/3) (3/4096) 0) 0 16383 (2594939/10000000) config0=true := by native_decide
theorem m0_negative_bounds :
  ((2588061/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (10/3) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (10/3) 0 y)≤(2594939/10000000) := by
  have h:=integral_bounds_from_checks false (10/3) (3/4096) (2588061/10000000) (2594939/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m0_negative_lower_check m0_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m0_negative_bounds
theorem m0_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (10/3) (3/16384) 0)) 0 16383 (-(47074413/10000000)) config0=true := by native_decide
theorem m0_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (10/3) (3/16384) 0) 0 16383 (589167/125000) config0=true := by native_decide
theorem m0_positive_bounds :
  ((47074413/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (10/3) 0 y)≤(589167/125000) := by
  have h:=integral_bounds_from_checks true (10/3) (3/16384) (47074413/10000000) (589167/125000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m0_positive_lower_check m0_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m0_positive_bounds
theorem m1_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (10/3) (3/4096) 1)) 0 16383 (-(819621/10000000)) config0=true := by native_decide
theorem m1_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (10/3) (3/4096) 1) 0 16383 (205909/2500000) config0=true := by native_decide
theorem m1_negative_bounds :
  ((819621/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (10/3) 1 y) ∧
  (∫y in (0:ℝ)..12,moment false (10/3) 1 y)≤(205909/2500000) := by
  have h:=integral_bounds_from_checks false (10/3) (3/4096) (819621/10000000) (205909/2500000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m1_negative_lower_check m1_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m1_negative_bounds
theorem m1_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (10/3) (3/16384) 1)) 0 16383 (-(8213399/2000000)) config0=true := by native_decide
theorem m1_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (10/3) (3/16384) 1) 0 16383 (2056721/500000) config0=true := by native_decide
theorem m1_positive_bounds :
  ((8213399/2000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 1 y) ∧
  (∫y in (0:ℝ)..3,moment true (10/3) 1 y)≤(2056721/500000) := by
  have h:=integral_bounds_from_checks true (10/3) (3/16384) (8213399/2000000) (2056721/500000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m1_positive_lower_check m1_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m1_positive_bounds
theorem m2_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (10/3) (3/4096) 2)) 0 16383 (-(508869/10000000)) config0=true := by native_decide
theorem m2_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (10/3) (3/4096) 2) 0 16383 (511363/10000000) config0=true := by native_decide
theorem m2_negative_bounds :
  ((508869/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (10/3) 2 y) ∧
  (∫y in (0:ℝ)..12,moment false (10/3) 2 y)≤(511363/10000000) := by
  have h:=integral_bounds_from_checks false (10/3) (3/4096) (508869/10000000) (511363/10000000) 2 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m2_negative_lower_check m2_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m2_negative_bounds
theorem m2_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (10/3) (3/16384) 2)) 0 16383 (-(21103747/5000000)) config0=true := by native_decide
theorem m2_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (10/3) (3/16384) 2) 0 16383 (10572293/2500000) config0=true := by native_decide
theorem m2_positive_bounds :
  ((21103747/5000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 2 y) ∧
  (∫y in (0:ℝ)..3,moment true (10/3) 2 y)≤(10572293/2500000) := by
  have h:=integral_bounds_from_checks true (10/3) (3/16384) (21103747/5000000) (10572293/2500000) 2 16384
    (by norm_num) (by norm_num) (by norm_num) config0 (by decide)
    m2_positive_lower_check m2_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m2_positive_bounds
end WinnerRivalMoments
