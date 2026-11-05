/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def config3 : DyadicConfig := {precision := -90,taylorDepth := 22}
theorem m9_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (13/6) (3/4096) 1)) 0 16383 (-(31211/156250)) config3=true := by native_decide
theorem m9_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (13/6) (3/4096) 1) 0 16383 (2003857/10000000) config3=true := by native_decide
theorem m9_negative_bounds :
  ((31211/156250):ℝ)≤(∫y in (0:ℝ)..12,moment false (13/6) 1 y) ∧
  (∫y in (0:ℝ)..12,moment false (13/6) 1 y)≤(2003857/10000000) := by
  have h:=integral_bounds_from_checks false (13/6) (3/4096) (31211/156250) (2003857/10000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m9_negative_lower_check m9_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m9_negative_bounds
theorem m9_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (13/6) (3/16384) 1)) 0 16383 (-(3321363/2500000)) config3=true := by native_decide
theorem m9_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (13/6) (3/16384) 1) 0 16383 (13302849/10000000) config3=true := by native_decide
theorem m9_positive_bounds :
  ((3321363/2500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (13/6) 1 y) ∧
  (∫y in (0:ℝ)..3,moment true (13/6) 1 y)≤(13302849/10000000) := by
  have h:=integral_bounds_from_checks true (13/6) (3/16384) (3321363/2500000) (13302849/10000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m9_positive_lower_check m9_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m9_positive_bounds
theorem m10_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (3/1) (3/4096) 0)) 0 16383 (-(1446729/5000000)) config3=true := by native_decide
theorem m10_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (3/1) (3/4096) 0) 0 16383 (1450207/5000000) config3=true := by native_decide
theorem m10_negative_bounds :
  ((1446729/5000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (3/1) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (3/1) 0 y)≤(1450207/5000000) := by
  have h:=integral_bounds_from_checks false (3/1) (3/4096) (1446729/5000000) (1450207/5000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m10_negative_lower_check m10_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m10_negative_bounds
theorem m10_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (3/1) (3/16384) 0)) 0 16383 (-(35463973/10000000)) config3=true := by native_decide
theorem m10_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (3/1) (3/16384) 0) 0 16383 (8876101/2500000) config3=true := by native_decide
theorem m10_positive_bounds :
  ((35463973/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (3/1) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (3/1) 0 y)≤(8876101/2500000) := by
  have h:=integral_bounds_from_checks true (3/1) (3/16384) (35463973/10000000) (8876101/2500000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m10_positive_lower_check m10_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m10_positive_bounds
theorem m11_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (2/1) (3/4096) 0)) 0 16383 (-(889563/2000000)) config3=true := by native_decide
theorem m11_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (2/1) (3/4096) 0) 0 16383 (4455081/10000000) config3=true := by native_decide
theorem m11_negative_bounds :
  ((889563/2000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (2/1) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (2/1) 0 y)≤(4455081/10000000) := by
  have h:=integral_bounds_from_checks false (2/1) (3/4096) (889563/2000000) (4455081/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m11_negative_lower_check m11_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m11_negative_bounds
theorem m11_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (2/1) (3/16384) 0)) 0 16383 (-(16629887/10000000)) config3=true := by native_decide
theorem m11_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (2/1) (3/16384) 0) 0 16383 (16643519/10000000) config3=true := by native_decide
theorem m11_positive_bounds :
  ((16629887/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (2/1) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (2/1) 0 y)≤(16643519/10000000) := by
  have h:=integral_bounds_from_checks true (2/1) (3/16384) (16629887/10000000) (16643519/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config3 (by decide)
    m11_positive_lower_check m11_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m11_positive_bounds
end WinnerRivalMoments
