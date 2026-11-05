/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldFloorSemantics
import OldFloors
import OriginalScalarSemantics
namespace WinnerOldFloors
open LeanCert.Core LeanCert.Engine Real Set MeasureTheory
open WinnerOldAnalytic
set_option maxHeartbeats 0

 theorem h_lower : (28:ℝ)≤h := by
  simpa only [h,WinnerOriginalScalars.height] using WinnerOriginalScalars.source_log_lower
 theorem c4_nonneg (v : ℝ) : 0≤c4Floor v := by unfold c4Floor;positivity
 theorem ratio_nonneg {v : ℝ} (hv : 0≤v) : 0≤ratioFloor v := by
  have hh : 0<h := by linarith [h_lower]
  unfold ratioFloor
  positivity

noncomputable def truncatedOldU (v : ℝ) : ℝ :=
  (8*(2371/20000:ℝ))*c4Floor v*
    ((∫ y in (-3:ℝ)..0,kernel (2371/20000) h (ratioFloor v) y)+
      (∫ y in (0:ℝ)..3,kernel (2371/20000) (h+v) (ratioFloor v) y))

 theorem gaussian_row_to_integral (v start : ℚ) (hv : 0≤v) (hs : start=0 ∨ start=-3) :
    (∑ k ∈ Finset.Icc (0:ℕ) 4095, Expr.eval (sumBodyRealEnv k) (floorBody v start)) ≤
      (8*(2371/20000:ℝ))*c4Floor v*
        ∫ y in (start:ℝ)..((start:ℝ)+3),
          kernel (2371/20000) (if start=0 then h+v else h) (ratioFloor v) y := by
  have hv' : (0:ℝ)≤v := by exact_mod_cast hv
  have hh : 0<h := by linarith [h_lower]
  have hden : 0<(if start=0 then h+(v:ℝ) else h) := by split_ifs <;> linarith
  have hfac : 0≤1+(start:ℝ)/(if start=0 then h+v else h) := by
    rcases hs with rfl|rfl
    · norm_num
    · norm_num only [OfNat.ofNat_ne_zero,neg_eq_zero,ite_false,Rat.cast_neg,Rat.cast_ofNat]
      have hd : (-1:ℝ)≤(-3:ℝ)/h := (le_div_iff₀ hh).mpr (by linarith [h_lower])
      linarith
  have hg := kernel_grid_lower (alpha:=2371/20000) (den:=if start=0 then h+v else h)
    (ratio:=ratioFloor v) (a:=start) (step:=3/4096) (n:=4096)
    (by norm_num) hden (ratio_nonneg hv') (by norm_num) hfac
  have hp := mul_le_mul_of_nonneg_left hg
    (show 0≤(8*(2371/20000:ℝ))*c4Floor (v:ℝ) from
      mul_nonneg (by norm_num) (c4_nonneg (v:ℝ)))
  have hi : Finset.Icc (0:ℕ) 4095=Finset.range 4096 := by ext k;simp;omega
  rw [hi]
  calc
    _ = (8*(2371/20000:ℝ))*c4Floor v*
      (∑ k ∈ Finset.range 4096,(3/4096)*kernelCell (2371/20000)
        (if start=0 then h+v else h) (ratioFloor v)
        ((start:ℝ)+(3/4096)*(k:ℝ)) ((start:ℝ)+(3/4096)*(k:ℝ)+3/4096)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [floorBody_semantics v start k (by linarith)]
      ring
    _ ≤ _ := by convert! hp using 1 <;> norm_num

 theorem gaussian_floor_from_rows {v : ℚ} {loNeg loPos : ℝ} (hv : 0≤v)
    (hn : loNeg ≤ ∑ k ∈ Finset.Icc (0:ℕ) 4095, Expr.eval (sumBodyRealEnv k) (floorBody v (-3)))
    (hp : loPos ≤ ∑ k ∈ Finset.Icc (0:ℕ) 4095, Expr.eval (sumBodyRealEnv k) (floorBody v 0)) :
    loNeg+loPos ≤ truncatedOldU v := by
  have h1 := hn.trans (gaussian_row_to_integral v (-3) hv (Or.inr rfl))
  have h2 := hp.trans (gaussian_row_to_integral v 0 hv (Or.inl rfl))
  norm_num only [OfNat.ofNat_ne_zero,neg_eq_zero,ite_false,ite_true,Rat.cast_neg,Rat.cast_ofNat,zero_add] at h1 h2
  unfold truncatedOldU
  linarith

 theorem oldU_floor1 : (1698779/1000000:ℝ)≤truncatedOldU 1 := by
  have h := gaussian_floor_from_rows (by norm_num : (0:ℚ)≤1) lower_1_neg lower_1_pos
  norm_num at h ⊢
  exact h
 theorem oldU_floor2 : (1682465/1000000:ℝ)≤truncatedOldU 2 := by
  have h := gaussian_floor_from_rows (by norm_num : (0:ℚ)≤2) lower_2_neg lower_2_pos
  norm_num at h ⊢
  exact h
 theorem oldU_floor4 : (1652763/1000000:ℝ)≤truncatedOldU 4 := by
  have h := gaussian_floor_from_rows (by norm_num : (0:ℚ)≤4) lower_4_neg lower_4_pos
  norm_num at h ⊢
  exact h
 theorem oldU_floor8 : (1602809/1000000:ℝ)≤truncatedOldU 8 := by
  have h := gaussian_floor_from_rows (by norm_num : (0:ℚ)≤8) lower_8_neg lower_8_pos
  norm_num at h ⊢
  exact h

#print axioms oldU_floor1
#print axioms oldU_floor8
end WinnerOldFloors
