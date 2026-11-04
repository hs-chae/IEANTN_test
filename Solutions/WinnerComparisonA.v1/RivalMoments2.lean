/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def config2 : DyadicConfig := {precision := -90,taylorDepth := 22}
theorem m6_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (19/6) (3/4096) 0)) 0 16383 (-(1366223/5000000)) config2=true := by native_decide
theorem m6_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (19/6) (3/4096) 0) 0 16383 (1369681/5000000) config2=true := by native_decide
theorem m6_negative_bounds :
  ((1366223/5000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (19/6) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (19/6) 0 y)≤(1369681/5000000) := by
  have h:=integral_bounds_from_checks false (19/6) (3/4096) (1366223/5000000) (1369681/5000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m6_negative_lower_check m6_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m6_negative_bounds
theorem m6_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (19/6) (3/16384) 0)) 0 16383 (-(2039061/500000)) config2=true := by native_decide
theorem m6_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (19/6) (3/16384) 0) 0 16383 (40829989/10000000) config2=true := by native_decide
theorem m6_positive_bounds :
  ((2039061/500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (19/6) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (19/6) 0 y)≤(40829989/10000000) := by
  have h:=integral_bounds_from_checks true (19/6) (3/16384) (2039061/500000) (40829989/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m6_positive_lower_check m6_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m6_positive_bounds
theorem m7_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (19/6) (3/4096) 1)) 0 16383 (-(91151/1000000)) config2=true := by native_decide
theorem m7_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (19/6) (3/4096) 1) 0 16383 (915751/10000000) config2=true := by native_decide
theorem m7_negative_bounds :
  ((91151/1000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (19/6) 1 y) ∧
  (∫y in (0:ℝ)..12,moment false (19/6) 1 y)≤(915751/10000000) := by
  have h:=integral_bounds_from_checks false (19/6) (3/4096) (91151/1000000) (915751/10000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m7_negative_lower_check m7_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m7_negative_bounds
theorem m7_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (19/6) (3/16384) 1)) 0 16383 (-(34650639/10000000)) config2=true := by native_decide
theorem m7_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (19/6) (3/16384) 1) 0 16383 (34705801/10000000) config2=true := by native_decide
theorem m7_positive_bounds :
  ((34650639/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (19/6) 1 y) ∧
  (∫y in (0:ℝ)..3,moment true (19/6) 1 y)≤(34705801/10000000) := by
  have h:=integral_bounds_from_checks true (19/6) (3/16384) (34650639/10000000) (34705801/10000000) 1 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m7_positive_lower_check m7_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m7_positive_bounds
theorem m8_negative_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false false (13/6) (3/4096) 0)) 0 16383 (-(4085729/10000000)) config2=true := by native_decide
theorem m8_negative_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true false (13/6) (3/4096) 0) 0 16383 (4092933/10000000) config2=true := by native_decide
theorem m8_negative_bounds :
  ((4085729/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (13/6) 0 y) ∧
  (∫y in (0:ℝ)..12,moment false (13/6) 0 y)≤(4092933/10000000) := by
  have h:=integral_bounds_from_checks false (13/6) (3/4096) (4085729/10000000) (4092933/10000000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m8_negative_lower_check m8_negative_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m8_negative_bounds
theorem m8_positive_lower_check : CH2QRH.DensityComputation.checkUpperBound
  (Expr.neg (cellExpr false true (13/6) (3/16384) 0)) 0 16383 (-(18686139/10000000)) config2=true := by native_decide
theorem m8_positive_upper_check : CH2QRH.DensityComputation.checkUpperBound
  (cellExpr true true (13/6) (3/16384) 0) 0 16383 (935121/500000) config2=true := by native_decide
theorem m8_positive_bounds :
  ((18686139/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (13/6) 0 y) ∧
  (∫y in (0:ℝ)..3,moment true (13/6) 0 y)≤(935121/500000) := by
  have h:=integral_bounds_from_checks true (13/6) (3/16384) (18686139/10000000) (935121/500000) 0 16384
    (by norm_num) (by norm_num) (by norm_num) config2 (by decide)
    m8_positive_lower_check m8_positive_upper_check
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  convert h using 1 <;> norm_num
#print axioms m8_positive_bounds
end WinnerRivalMoments
