/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Mathlib

/-! Uniform elementary constants for the coupled-integral ray.
Every numerical bound below is derived in the kernel from Mathlib's proved
exponential enclosures, not supplied as a new analytic or numerical premise. -/
namespace RamanujanPV.CoupledUniformBounds
open Real Set
set_option maxHeartbeats 0

noncomputable def K : ℝ := (1561/12375:ℝ) * Real.sqrt (Real.exp 15)
noncomputable def Uerr (x : ℝ) : ℝ :=
  K + (117/22:ℝ) * Real.sqrt (x / Real.exp 1) / (Real.log x - 1)^2
noncomputable def q (x : ℝ) : ℝ := Real.sqrt x / Real.log x

theorem exp_one_upper : Real.exp 1 ≤ (68/25:ℝ) := by
  linarith [Real.exp_one_lt_d9]

theorem exp_fifteen_upper : Real.exp 15 ≤ (1820:ℝ)^2 := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_upper 15
  have he : Real.exp (15:ℝ) = (Real.exp 1)^15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← he] at h
  exact h.trans (by norm_num)

theorem K_nonneg : 0 ≤ K := by unfold K; positivity

theorem K_le : K ≤ 230 := by
  have h : Real.sqrt (Real.exp 15) ≤ (1820:ℝ) :=
    (Real.sqrt_le_left (by norm_num)).2 exp_fifteen_upper
  unfold K
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 1561/12375)
  norm_num at hm ⊢
  linarith

theorem threshold_log_lower : (139/5:ℝ) ≤ Real.log 1250000000000 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).2
  apply le_of_pow_le_pow_left₀ (n:=5) (by norm_num) (by norm_num)
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_upper 139
  have h1 : (Real.exp (139/5:ℝ))^5 = Real.exp (139:ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : (Real.exp 1)^139 = Real.exp (139:ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h1, ← h2]
  exact h.trans (by norm_num)

theorem threshold_log_upper : Real.log 1250000000000 ≤ (28:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have he : (271/100:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271/100) he 28
  have h2 : (Real.exp 1)^28 = Real.exp (28:ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2] at h
  exact (show (1250000000000:ℝ) ≤ (271/100:ℝ)^28 by norm_num).trans h

theorem threshold_sqrt_lower : (1118000:ℝ) ≤ Real.sqrt 1250000000000 := by
  exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

theorem log_lower {x : ℝ} (hx : 1250000000000 ≤ x) :
    (139/5:ℝ) ≤ Real.log x :=
  threshold_log_lower.trans (Real.log_le_log (by norm_num) hx)

theorem log_div_sqrt_upper {x : ℝ} (hx : 1250000000000 ≤ x) :
    Real.log x / Real.sqrt x ≤ (28/1118000:ℝ) := by
  have hT : Real.exp 2 ≤ (1250000000000:ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).1 (by linarith [threshold_log_lower])
  have hm := Real.log_div_sqrt_antitoneOn hT (hT.trans hx) hx
  refine hm.trans ?_
  calc
    Real.log 1250000000000 / Real.sqrt 1250000000000 ≤
        28 / Real.sqrt 1250000000000 :=
      div_le_div_of_nonneg_right threshold_log_upper (Real.sqrt_nonneg _)
    _ ≤ (28/1118000:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) threshold_sqrt_lower

theorem sqrt_e_lower : (329/200:ℝ) ≤ Real.sqrt (Real.exp 1) := by
  apply (Real.le_sqrt (by norm_num) (Real.exp_pos 1).le).2
  linarith [Real.exp_one_gt_d9]

theorem inv_sqrt_e_upper : 1 / Real.sqrt (Real.exp 1) ≤ (200/329:ℝ) := by
  have hp : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.2 (Real.exp_pos 1)
  apply (div_le_iff₀ hp).2
  nlinarith [sqrt_e_lower]

theorem shifted_ratio_le {a L : ℝ} (ha : 1 < a) (hL : a ≤ L) :
    L/(L-1)^2 ≤ a/(a-1)^2 := by
  have hLa : 0 ≤ L-a := by linarith
  have hp : 0 ≤ a*L-1 := by nlinarith
  have hm := mul_nonneg hLa hp
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < L-1))
    (sq_pos_of_pos (by linarith : 0 < a-1))).2
  nlinarith

theorem Uerr_uniform {x : ℝ} (hx : 1250000000000 ≤ x) :
    Uerr x ≤ (131/1000:ℝ) * q x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have he : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.2 (Real.exp_pos 1)
  have hL := log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hd : Real.log x-1 ≠ 0 := by linarith
  have hq : 0 ≤ q x := by unfold q; positivity
  have hfirst : K * (Real.log x / Real.sqrt x) ≤
      230 * (28/1118000:ℝ) := by
    exact mul_le_mul K_le (log_div_sqrt_upper hx)
      (div_nonneg hL0.le hs.le) (by norm_num)
  have hlast : Real.log x / (Real.log x-1)^2 ≤
      (139/5:ℝ)/(134/5:ℝ)^2 := by
    convert shifted_ratio_le (by norm_num : (1:ℝ)<139/5) hL using 1 <;> norm_num
  have hproduct : (1 / Real.sqrt (Real.exp 1)) *
      (Real.log x / (Real.log x-1)^2) ≤
      (200/329:ℝ) * ((139/5:ℝ)/(134/5:ℝ)^2) :=
    mul_le_mul inv_sqrt_e_upper hlast (by positivity) (by norm_num)
  have hsecond := mul_le_mul_of_nonneg_left hproduct
    (by norm_num : (0:ℝ)≤117/22)
  have hcoef : K*(Real.log x/Real.sqrt x) + (117/22:ℝ) *
      ((1/Real.sqrt (Real.exp 1))*(Real.log x/(Real.log x-1)^2)) ≤
      (131/1000:ℝ) := by
    have hc : (230:ℝ)*(28/1118000)+(117/22)*(200/329)*
        ((139/5)/(134/5)^2) ≤ 131/1000 := by norm_num
    linarith
  have hid : Uerr x = (K*(Real.log x/Real.sqrt x) + (117/22:ℝ) *
      ((1/Real.sqrt (Real.exp 1))*(Real.log x/(Real.log x-1)^2))) * q x := by
    unfold Uerr q
    rw [Real.sqrt_div hx0.le]
    field_simp [hs.ne', he.ne', hL0.ne', hd]
    <;> ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hcoef hq

#print axioms K_le
#print axioms threshold_log_lower
#print axioms threshold_log_upper
#print axioms log_div_sqrt_upper
#print axioms inv_sqrt_e_upper
#print axioms shifted_ratio_le
#print axioms Uerr_uniform
end RamanujanPV.CoupledUniformBounds
