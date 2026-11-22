/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Source-local literal caption tests, not a rejection of numerical table data. -/
import Table13Check
namespace MertensPositive
open Real ArithmeticFunction Finset
private lemma pp2 : IsPrimePow (2:ℕ) := (show Nat.Prime 2 by decide).isPrimePow
private lemma pp3 : IsPrimePow (3:ℕ) := (show Nat.Prime 3 by decide).isPrimePow
private lemma pp4 : IsPrimePow (4:ℕ) := ⟨2,2,Nat.prime_two.prime,by decide,by decide⟩
private lemma pp5 : IsPrimePow (5:ℕ) := (show Nat.Prime 5 by decide).isPrimePow
private lemma pp7 : IsPrimePow (7:ℕ) := (show Nat.Prime 7 by decide).isPrimePow
private lemma pp6 : ¬IsPrimePow (6:ℕ) := by
  intro h
  obtain ⟨p,hp,hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  have h2 : 2=p := hu 2 ⟨by decide,by decide⟩
  have h3 : 3=p := hu 3 ⟨by decide,by decide⟩
  omega
lemma psi_seven : Chebyshev.psi 7=2*Real.log 2+Real.log 3+Real.log 5+Real.log 7 := by
  norm_num [Chebyshev.psi,ArithmeticFunction.vonMangoldt_apply,Finset.sum_Ioc_succ_top,pp2,pp3,pp4,pp5,pp6,pp7]
  ring
lemma theta_seven : Chebyshev.theta 7=Real.log 2+Real.log 3+Real.log 5+Real.log 7 := by
  have hp : (Finset.Ioc 0 7).filter Nat.Prime=({2,3,5,7}:Finset ℕ) := by decide
  unfold Chebyshev.theta
  norm_num only [Nat.floor_ofNat]
  rw [hp]
  norm_num
  ring
lemma log_seven_le_two : Real.log 7≤2 :=
  (Real.log_le_iff_le_exp (by norm_num)).mpr seven_in_table13_first_row.2

theorem table13_psi_literal_caption_counterexample :
    (1.415:ℝ)/Real.sqrt 7 < 7-Chebyshev.psi 7 := by
  have hs : (2.64:ℝ)<Real.sqrt 7 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hb : (1.415:ℝ)/Real.sqrt 7<0.54 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  rw [psi_seven]
  linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9,log_seven_le_two]

theorem table13_theta_literal_caption_counterexample :
    (1.435:ℝ)/Real.sqrt 7 < 7-Chebyshev.theta 7 := by
  have hs : (2.64:ℝ)<Real.sqrt 7 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hb : (1.435:ℝ)/Real.sqrt 7<0.55 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  rw [theta_seven]
  linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9,log_seven_le_two]

lemma gamma_gt_point52 : (0.52:ℝ)<Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 8
  have hl : Real.log 9=2*Real.log 3 := by
    rw [show (9:ℝ)=3*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  norm_num [Real.eulerMascheroniSeq,harmonic,Finset.sum_range_succ] at h
  rw [hl] at h
  linarith [Real.log_three_lt_d9]
lemma CA_five : CA 5=Real.log 2/2+Real.log 3/3+Real.log 2/4+Real.log 5/5 := by
  norm_num [CA,ArithmeticFunction.vonMangoldt_apply,Finset.sum_Ioc_succ_top,pp2,pp3,pp4,pp5,pp6,pp7]

theorem table13_CA_literal_caption_counterexample :
    (0.393:ℝ)/(Real.log 5*Real.sqrt 5)<CA 5-Real.log 5+Real.eulerMascheroniConstant := by
  have hs : (2.23:ℝ)<Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hl : (1.60:ℝ)<Real.log 5 := by linarith [Real.log_five_gt_d9]
  have hb : (0.393:ℝ)/(Real.log 5*Real.sqrt 5)<0.111 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  rw [CA_five]
  linarith [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_lt_d9,gamma_gt_point52]

theorem five_in_table13_first_row : Real.exp 1≤(5:ℝ) ∧ (5:ℝ)≤Real.exp 2 := by
  constructor
  · linarith [Real.exp_one_lt_d9]
  · linarith [seven_in_table13_first_row.2]
#print axioms table13_psi_literal_caption_counterexample
#print axioms table13_theta_literal_caption_counterexample
#print axioms table13_CA_literal_caption_counterexample
end MertensPositive
