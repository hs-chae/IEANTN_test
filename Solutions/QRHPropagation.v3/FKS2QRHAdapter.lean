/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Consumer
import IEANTN.Nodes.QRHCH2.v5.Conclusions
import IEANTN.Nodes.QRHPropagation.v3.Conclusions
namespace FKS2QRHAdapter
open Real IEANTN FKS2Correction

theorem whole_tail_majorant {L : ℝ} (hL : 300 ≤ L) :
    L^2/566*exp (-L/8) ≤ (0.0000000001:ℝ)*commonShape L := by
  let s := sqrt (L/5.5666305)
  have hL0 : 0 < L := by linarith
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs2 : s^2 = L/5.5666305 := sq_sqrt (by positivity)
  have hLs : L = 5.5666305*s^2 := by
    have h := (eq_div_iff (by norm_num : (5.5666305:ℝ) ≠ 0)).mp hs2
    nlinarith only [h]
  have hs40 : s ≤ L/40 := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5.5666305)]
    nlinarith [mul_nonneg hL0.le (show 0 ≤ L-300 by linarith)]
  have hm := poly_exp_decreasing 1 (L0 := (300:ℝ)) (c := (3/40:ℝ))
    (by norm_num) (by norm_num) hL
  have he : exp (-(22.5:ℝ)) ≤ (10/27:ℝ)^22*(2/3) := by
    have hf : exp (-(0.5:ℝ)) ≤ (2/3:ℝ) := by
      rw [exp_neg, ← one_div]
      apply (div_le_iff₀ (exp_pos _)).mpr
      nlinarith [add_one_le_exp (0.5:ℝ)]
    calc
      _ = exp (-(22:ℝ))*exp (-(0.5:ℝ)) := by rw [← exp_add]; norm_num
      _ ≤ _ := mul_le_mul (exp_neg_nat_upper 22) hf (exp_pos _).le (by positivity)
  have hcore : s*exp (-L/8+2*s) ≤ (300/40:ℝ)*((10/27:ℝ)^22*(2/3)) := by
    calc
      _ ≤ (L/40)*exp (-(3/40:ℝ)*L) := by
        apply mul_le_mul hs40 (exp_le_exp.mpr (by linarith)) (exp_pos _).le (by positivity)
      _ ≤ (300/40:ℝ)*exp (-(22.5:ℝ)) := by
        norm_num only [pow_one] at hm
        nlinarith [hm]
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)
  have hratio : (5.5666305^2/566:ℝ)*s*exp (-L/8+2*s) ≤ 0.0000000001 := by
    have h := mul_le_mul_of_nonneg_left hcore (by norm_num : (0:ℝ) ≤ 5.5666305^2/566)
    have hend : (5.5666305^2/566:ℝ)*((300/40)*((10/27:ℝ)^22*(2/3))) ≤ 0.0000000001 := by
      norm_num
    nlinarith [h,hend]
  have hshape : commonShape L = s^3*exp (-2*s) := by
    unfold commonShape
    rw [rpow_div_two_eq_sqrt _ (by positivity)]
    norm_num [s]
  have heq : exp (-L/8+2*s)*exp (-2*s) = exp (-L/8) := by
    rw [← exp_add]
    congr 1
    ring
  have hid : ((5.5666305^2/566:ℝ)*s*exp (-L/8+2*s))*commonShape L =
      L^2/566*exp (-L/8) := by
    rw [hshape]
    calc
      _ = (5.5666305^2*s^4/566)*(exp (-L/8+2*s)*exp (-2*s)) := by ring
      _ = _ := by rw [heq,hLs]; ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_right hratio (by rw [hshape]; positivity)

theorem psi_same_shape (hpsi : QRHCH2.v5.psi_refined_bound) :
    QRHPropagation.v3.psi_classical_bound := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300:ℝ)).trans_le hx
  have hL : 300 ≤ log x := by simpa using log_le_log (exp_pos (300:ℝ)) hx
  have hp := hpsi x hx
  rw [rpow_def_of_pos hx0] at hp
  have hid : log x*(-(1:ℝ)/8) = -log x/8 := by ring
  rw [hid] at hp
  have hmajor := whole_tail_majorant hL
  have hfin : Eψ x ≤ (0.0000000001:ℝ)*commonShape (log x) := by
    nlinarith [hp,hmajor]
  simpa [admissibleBound,commonShape,mul_assoc,Real.sqrt_eq_rpow] using hfin

end FKS2QRHAdapter
