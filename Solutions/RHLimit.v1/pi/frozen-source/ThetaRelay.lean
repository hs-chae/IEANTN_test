/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FullRH
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
open Real IEANTN
namespace RHContinuation.ThetaRelay
set_option maxHeartbeats 0
set_option maxRecDepth 5000
theorem poly_exp_decreasing (n : ℕ) {c L0 L : ℝ} (hL0 : 0 < L0) (hc : (n : ℝ) / L0 ≤ c)
    (hL : L0 ≤ L) : L ^ n * Real.exp (-c * L) ≤ L0 ^ n * Real.exp (-c * L0) := by
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hratio_pos : (0 : ℝ) < L / L0 := div_pos hLpos hL0
  have hlog_ratio : Real.log (L / L0) ≤ L / L0 - 1 := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_sub : Real.log L - Real.log L0 ≤ (L - L0) / L0 := by
    have heq : Real.log (L / L0) = Real.log L - Real.log L0 :=
      Real.log_div (ne_of_gt hLpos) (ne_of_gt hL0)
    have heq2 : L / L0 - 1 = (L - L0) / L0 := by field_simp
    linarith [hlog_ratio, heq, heq2]
  have hkey : (n : ℝ) * (Real.log L - Real.log L0) ≤ c * (L - L0) := by
    have hLsub_nonneg : (0 : ℝ) ≤ L - L0 := by linarith
    have hstep1 : (n : ℝ) * (Real.log L - Real.log L0) ≤ (n : ℝ) * ((L - L0) / L0) :=
      mul_le_mul_of_nonneg_left hlog_sub (Nat.cast_nonneg n)
    have hstep2 : (n : ℝ) * ((L - L0) / L0) ≤ c * (L - L0) := by
      have hmm := mul_le_mul_of_nonneg_right hc hLsub_nonneg
      calc (n : ℝ) * ((L - L0) / L0) = ((n : ℝ) / L0) * (L - L0) := by ring
        _ ≤ c * (L - L0) := hmm
    linarith
  have hrw : ∀ v : ℝ, 0 < v →
      Real.exp ((n : ℝ) * Real.log v - c * v) = v ^ n * Real.exp (-c * v) := by
    intro v hvpos
    have hsplit : (n : ℝ) * Real.log v - c * v = ((n : ℝ) * Real.log v) + (-c * v) := by ring
    rw [hsplit, Real.exp_add]
    congr 1
    rw [show (n : ℝ) * Real.log v = Real.log (v ^ n) from (Real.log_pow v n).symm]
    exact Real.exp_log (by positivity)
  have hexp_le : Real.exp ((n : ℝ) * Real.log L - c * L)
      ≤ Real.exp ((n : ℝ) * Real.log L0 - c * L0) := by
    apply Real.exp_le_exp.mpr; linarith [hkey]
  rw [hrw L hLpos, hrw L0 hL0] at hexp_le
  exact hexp_le


theorem exp_neg_nat (n : ℕ) : exp (-(n:ℝ)) ≤ (1000/2718:ℝ)^n := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000)
    (show (2718/1000:ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) n
  rw [exp_one_pow] at hp
  rw [exp_neg, ← one_div, ← show (1:ℝ)/(2718/1000)=1000/2718 by norm_num,
    one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hp



theorem psi_relative (hRH : SharedRH.hypothesis)
    (hb : Buthe2016.v1.theorem_2_psi) {L : ℝ} (hL : 6 ≤ L) :
    |Chebyshev.psi (exp L) - exp L| ≤ exp L * ((1/25:ℝ)*L^2*exp (-L/2)) := by
  have he : (2:ℝ)^6 ≤ exp 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) exp_one_gt_two.le 6
    rw [exp_one_pow] at hh
    exact_mod_cast hh
  have hdom := (show (59:ℝ)<2^6 by norm_num).trans_le (he.trans (exp_le_exp.mpr hL))
  have hh := FullRH.buthe_all_psi hRH hb hdom
  rw [← exp_half,log_exp] at hh
  have hc : 1/(8*π) ≤ (1/25:ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [pi_gt_d2])
  have hq := mul_le_mul_of_nonneg_left hc (show 0 ≤ exp (L/2)*L^2 by positivity)
  have hy : exp L*exp (-L/2) = exp (L/2) := by rw [← exp_add]; congr 1; ring
  calc
    _ ≤ exp (L/2)*L^2/(8*π) := hh
    _ ≤ exp (L/2)*L^2*(1/25) := by simpa only [div_eq_mul_inv, one_mul] using hq
    _ = _ := by
      calc
        _ = (exp L*exp (-L/2))*L^2*(1/25) := by rw [hy]
        _ = _ := by ring

theorem root_error {L B : ℝ} {u0 n : ℕ} (hu0 : 4 ≤ u0)
    (hL : (u0:ℝ) ≤ L) (hn : (n:ℝ) ≤ (u0:ℝ)/2)
    (hnum : (1/25:ℝ)*(u0:ℝ)^2*(1000/2718)^n ≤ B) :
    (1/25:ℝ)*L^2*exp (-L/2) ≤ B := by
  have hu : (4:ℝ) ≤ (u0:ℝ) := by exact_mod_cast hu0
  have hp := poly_exp_decreasing 2 (L0:=(u0:ℝ)) (c:=(1/2:ℝ)) (by linarith) (by exact (div_le_iff₀ (by linarith : (0:ℝ)<u0)).2 (by norm_num; linarith)) hL
  have hp' : L^2*exp (-L/2) ≤ (u0:ℝ)^2*exp (-(u0:ℝ)/2) := by
    convert hp using 1 <;> congr 1 <;> ring
  have hn1 : exp (-(u0:ℝ)/2) ≤ exp (-(n:ℝ)) := exp_le_exp.mpr (by linarith)
  have hn2 := hn1.trans (exp_neg_nat n)
  calc
    _ = (1/25:ℝ)*(L^2*exp (-L/2)) := by ring
    _ ≤ (1/25:ℝ)*((u0:ℝ)^2*exp (-(u0:ℝ)/2)) := mul_le_mul_of_nonneg_left hp' (by norm_num)
    _ ≤ (1/25:ℝ)*(u0:ℝ)^2*(1000/2718)^n := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn2 (by positivity)) (by norm_num)
    _ ≤ _ := hnum

theorem signed_psi_to_theta (hRH : SharedRH.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    {L : ℝ} (hL : 34 ≤ L) :
    (0.99:ℝ)*exp (L/2) ≤ Chebyshev.psi (exp L) - Chebyshev.theta (exp L) ∧
      Chebyshev.psi (exp L) - Chebyshev.theta (exp L) ≤ (1.01:ℝ)*exp (L/2) := by
  have hr (U : ℝ) (hu : 6 ≤ U) :
      |Chebyshev.psi (exp U) - exp U| ≤ exp U * 0.08 := by
    exact (psi_relative hRH hb hu).trans (mul_le_mul_of_nonneg_left
      (root_error (u0:=6) (n:=3) (by norm_num) (by simpa using hu) (by norm_num) (by norm_num))
      (exp_nonneg _))
  have hs := (psi_relative hRH hb (show 6 ≤ L/2 by linarith)).trans
    (mul_le_mul_of_nonneg_left (root_error (u0:=17) (n:=8) (by norm_num)
      (by norm_num; linarith) (by norm_num) (by norm_num : (1/25:ℝ)*17^2*(1000/2718)^8 ≤ 0.004))
      (exp_nonneg _))
  have h3 := (abs_le.mp (hr (L/3) (by linarith))).2
  have h5 := (abs_le.mp (hr (L/5) (by linarith))).2
  have hu := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (exp L)
  have hl := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi (exp_nonneg L)
  simp only [rpow_def_of_pos (exp_pos L),log_exp, ← div_eq_mul_inv] at hu hl
  have h3p := Chebyshev.psi_nonneg (exp (L/3))
  have h7p := Chebyshev.psi_nonneg (exp (L/7))
  have h0 := (abs_le.mp hs).1
  constructor
  · linarith [exp_pos (L/2)]
  have hH3 : exp (-L/6) ≤ (1000/2718:ℝ)^5*(2/3) := by
    have hhi := exp_le_exp.mpr (show -L/6 ≤ -(5:ℝ)+(-(1:ℝ)/2) by linarith)
    rw [exp_add] at hhi
    have half : exp (-(1:ℝ)/2) ≤ 2/3 := by
      rw [show -(1:ℝ)/2 = -(1/2) by ring,exp_neg,← one_div]
      apply (div_le_iff₀ (exp_pos (1/2))).2
      linarith [add_one_le_exp (1/2:ℝ)]
    exact hhi.trans (mul_le_mul (by simpa using exp_neg_nat 5) half
      (exp_nonneg _) (by positivity))
  have hH5 : exp (-(3/10:ℝ)*L) ≤ (1000/2718:ℝ)^10 :=
    (exp_le_exp.mpr (show -(3/10:ℝ)*L ≤ -10 by linarith)).trans (by simpa using exp_neg_nat 10)
  have hId3 : exp (L/3) = exp (L/2)*exp (-L/6) := by rw [←exp_add]; congr 1; ring
  have hId5 : exp (L/5) = exp (L/2)*exp (-(3/10:ℝ)*L) := by rw [←exp_add]; congr 1; ring
  have hz3 := mul_le_mul_of_nonneg_left hH3 (exp_nonneg (L/2))
  have hz5 := mul_le_mul_of_nonneg_left hH5 (exp_nonneg (L/2))
  rw [←hId3] at hz3
  rw [←hId5] at hz5
  have hsum := (abs_le.mp hs).2
  norm_num at hz3 hz5
  linarith
theorem theta_relay (hRH : SharedRH.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    {L C : ℝ} (hL : 34 ≤ L)
    (hpsi : |Chebyshev.psi (exp L) - exp L| ≤ C * sqrt (exp L)) :
    |Chebyshev.theta (exp L) - exp L| ≤ (C+1.01)*sqrt (exp L) := by
  obtain ⟨h₁,h₂⟩ := signed_psi_to_theta hRH hb hL
  rw [exp_half] at h₁ h₂
  obtain ⟨h₃,h₄⟩ := abs_le.mp hpsi
  apply abs_le.mpr
  constructor <;> nlinarith [sqrt_nonneg (exp L)]
#print axioms theta_relay
#print axioms signed_psi_to_theta

end RHContinuation.ThetaRelay
