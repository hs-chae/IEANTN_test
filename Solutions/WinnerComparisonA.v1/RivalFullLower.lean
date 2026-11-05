/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMoments0
import RivalMoments1
import RivalMoments2
import RivalMoments3
import RivalMomentSplit
import RivalMomentOneSided
namespace WinnerRivalMoments
open MeasureTheory
set_option maxHeartbeats 0
theorem m0_full_lower : ((24831237/5000000):ℝ)≤fullMoment (10/3) 0 := by
  have hn:((2588061/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (10/3) 0 y) := by
    have h:=integral_lower_from_check false (10/3) (3/4096) (2588061/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m0_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((47074413/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 0 y) := by
    have h:=integral_lower_from_check true (10/3) (3/16384) (47074413/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m0_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m0_full_lower
theorem m1_full_lower : ((40243359/10000000):ℝ)≤fullMoment (10/3) 1 := by
  have hn:(∫y in (0:ℝ)..12,moment false (10/3) 1 y)≤(205909/2500000) := by
    have h:=integral_upper_from_check false (10/3) (3/4096) (205909/2500000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m1_negative_upper_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((8213399/2000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 1 y) := by
    have h:=integral_lower_from_check true (10/3) (3/16384) (8213399/2000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m1_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m1_full_lower
theorem m2_full_lower : ((42716363/10000000):ℝ)≤fullMoment (10/3) 2 := by
  have hn:((508869/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (10/3) 2 y) := by
    have h:=integral_lower_from_check false (10/3) (3/4096) (508869/10000000) 2 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m2_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((21103747/5000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (10/3) 2 y) := by
    have h:=integral_lower_from_check true (10/3) (3/16384) (21103747/5000000) 2 16384
      (by norm_num) (by norm_num) (by norm_num) config0 (by decide) m2_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m2_full_lower
theorem m3_full_lower : ((4970851/2000000):ℝ)≤fullMoment (7/3) 0 := by
  have hn:((3776827/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (7/3) 0 y) := by
    have h:=integral_lower_from_check false (7/3) (3/4096) (3776827/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m3_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((5269357/2500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 0 y) := by
    have h:=integral_lower_from_check true (7/3) (3/16384) (5269357/2500000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m3_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m3_full_lower
theorem m4_full_lower : ((13752593/10000000):ℝ)≤fullMoment (7/3) 1 := by
  have hn:(∫y in (0:ℝ)..12,moment false (7/3) 1 y)≤(860053/5000000) := by
    have h:=integral_upper_from_check false (7/3) (3/4096) (860053/5000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m4_negative_upper_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((15472699/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 1 y) := by
    have h:=integral_lower_from_check true (7/3) (3/16384) (15472699/10000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m4_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m4_full_lower
theorem m5_full_lower : ((15803167/10000000):ℝ)≤fullMoment (7/3) 2 := by
  have hn:((378903/2500000):ℝ)≤(∫y in (0:ℝ)..12,moment false (7/3) 2 y) := by
    have h:=integral_lower_from_check false (7/3) (3/4096) (378903/2500000) 2 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m5_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((2857511/2000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (7/3) 2 y) := by
    have h:=integral_lower_from_check true (7/3) (3/16384) (2857511/2000000) 2 16384
      (by norm_num) (by norm_num) (by norm_num) config1 (by decide) m5_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m5_full_lower
theorem m6_full_lower : ((21756833/5000000):ℝ)≤fullMoment (19/6) 0 := by
  have hn:((1366223/5000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (19/6) 0 y) := by
    have h:=integral_lower_from_check false (19/6) (3/4096) (1366223/5000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m6_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((2039061/500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (19/6) 0 y) := by
    have h:=integral_lower_from_check true (19/6) (3/16384) (2039061/500000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m6_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m6_full_lower
theorem m7_full_lower : ((4216861/1250000):ℝ)≤fullMoment (19/6) 1 := by
  have hn:(∫y in (0:ℝ)..12,moment false (19/6) 1 y)≤(915751/10000000) := by
    have h:=integral_upper_from_check false (19/6) (3/4096) (915751/10000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m7_negative_upper_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((34650639/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (19/6) 1 y) := by
    have h:=integral_lower_from_check true (19/6) (3/16384) (34650639/10000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m7_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m7_full_lower
theorem m8_full_lower : ((5692967/2500000):ℝ)≤fullMoment (13/6) 0 := by
  have hn:((4085729/10000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (13/6) 0 y) := by
    have h:=integral_lower_from_check false (13/6) (3/4096) (4085729/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m8_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((18686139/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (13/6) 0 y) := by
    have h:=integral_lower_from_check true (13/6) (3/16384) (18686139/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config2 (by decide) m8_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m8_full_lower
theorem m9_full_lower : ((2256319/2000000):ℝ)≤fullMoment (13/6) 1 := by
  have hn:(∫y in (0:ℝ)..12,moment false (13/6) 1 y)≤(2003857/10000000) := by
    have h:=integral_upper_from_check false (13/6) (3/4096) (2003857/10000000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m9_negative_upper_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((3321363/2500000):ℝ)≤(∫y in (0:ℝ)..3,moment true (13/6) 1 y) := by
    have h:=integral_lower_from_check true (13/6) (3/16384) (3321363/2500000) 1 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m9_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m9_full_lower
theorem m10_full_lower : ((38357431/10000000):ℝ)≤fullMoment (3/1) 0 := by
  have hn:((1446729/5000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (3/1) 0 y) := by
    have h:=integral_lower_from_check false (3/1) (3/4096) (1446729/5000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m10_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((35463973/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (3/1) 0 y) := by
    have h:=integral_lower_from_check true (3/1) (3/16384) (35463973/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m10_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m10_full_lower
theorem m11_full_lower : ((10538851/5000000):ℝ)≤fullMoment (2/1) 0 := by
  have hn:((889563/2000000):ℝ)≤(∫y in (0:ℝ)..12,moment false (2/1) 0 y) := by
    have h:=integral_lower_from_check false (2/1) (3/4096) (889563/2000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m11_negative_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  have hp:((16629887/10000000):ℝ)≤(∫y in (0:ℝ)..3,moment true (2/1) 0 y) := by
    have h:=integral_lower_from_check true (2/1) (3/16384) (16629887/10000000) 0 16384
      (by norm_num) (by norm_num) (by norm_num) config3 (by decide) m11_positive_lower_check
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num
  rw [full_split]
  norm_num only [pow_zero,pow_one,one_mul,neg_one_mul,show (-1:ℝ)^2=1 by norm_num]
  linarith
#print axioms m11_full_lower
end WinnerRivalMoments
