/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import Mathlib
open Real MeasureTheory intervalIntegral Finset
namespace FKSComputationLed.LiTaylor
noncomputable def expPoly (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, y ^ k / (Nat.factorial k : ℝ)
noncomputable def primitive (n : ℕ) (y : ℝ) : ℝ :=
  log y + ∑ k ∈ Finset.range n,
    y ^ (k+1) / (((k+1:ℕ):ℝ) * (Nat.factorial (k+1) : ℝ))
lemma exp_bound_global {y : ℝ} {n : ℕ} (h : |y| / (n+1) ≤ 1/2) :
    |exp y - expPoly n y| ≤ |y| ^ n / (Nat.factorial n : ℝ) * 2 := by
  have hc : ‖(y : ℂ)‖ / n.succ ≤ 1/2 := by exact_mod_cast h
  unfold expPoly
  convert Complex.exp_bound' hc <;> norm_cast
lemma primitive_deriv {n : ℕ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (primitive n) (expPoly (n+1) y / y) y := by
  have hs : HasDerivAt
      (fun z : ℝ => ∑ k ∈ Finset.range n,
        z^(k+1) / (((k+1:ℕ):ℝ)*(Nat.factorial (k+1):ℝ)))
      (∑ k ∈ Finset.range n, y^k/(Nat.factorial (k+1):ℝ)) y := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hd := ((hasDerivAt_pow (k+1) y).div_const
      (((k+1:ℕ):ℝ)*(Nat.factorial (k+1):ℝ)))
    convert hd using 1 <;> try rfl
    all_goals field_simp <;> simp
  have ht := (Real.hasDerivAt_log hy).add hs
  have he : expPoly (n+1) y / y =
      y⁻¹ + ∑ k ∈ Finset.range n, y^k/(Nat.factorial (k+1):ℝ) := by
    unfold expPoly
    rw [Finset.sum_range_succ']
    simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
    rw [add_div,Finset.sum_div]
    have hh : ∀ k : ℕ, y^(k+1)/(Nat.factorial (k+1):ℝ)/y =
        y^k/(Nat.factorial (k+1):ℝ) := by
      intro k
      rw [pow_succ]
      field_simp
    simp_rw [hh]
    simp only [one_div]
    ring
  rw [he]
  convert ht using 1 <;> first | rfl | exact Subsingleton.elim _ _
lemma continuous_expPoly (n : ℕ) : Continuous (expPoly n) := by
  unfold expPoly
  fun_prop
lemma integral_exp_div_approx {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 24) :
    |(∫ t in a..b, exp t/t) - (primitive 79 b - primitive 79 a)| ≤
      2*24^80/(Nat.factorial 80:ℝ) := by
  have positive : ∀ t ∈ Set.uIcc a b, 0<t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => exp t/t) (Set.uIcc a b) :=
    continuous_exp.continuousOn.div continuous_id.continuousOn
      (fun t ht => (positive t ht).ne')
  have hpcont : ContinuousOn (fun t : ℝ => expPoly 80 t/t) (Set.uIcc a b) :=
    (continuous_expPoly 80).continuousOn.div continuous_id.continuousOn
      (fun t ht => (positive t ht).ne')
  have hi : IntervalIntegrable (fun t : ℝ => exp t/t) volume a b := hcont.intervalIntegrable
  have hip : IntervalIntegrable (fun t : ℝ => expPoly 80 t/t) volume a b := hpcont.intervalIntegrable
  have hFTC : (∫ t in a..b, expPoly 80 t/t) = primitive 79 b - primitive 79 a := by
    apply integral_eq_sub_of_hasDerivAt _ hip
    intro t ht
    exact primitive_deriv (positive t ht).ne'
  rw [←hFTC,←integral_sub hi hip]
  let C : ℝ := 2*24^79/(Nat.factorial 80:ℝ)
  have hC : 0≤C := by dsimp [C];positivity
  have hpt : ∀ t ∈ Set.Icc a b, |exp t/t-expPoly 80 t/t| ≤ C := by
    intro t ht
    have ht0 : 0<t := ha.trans_le ht.1
    have ht24 : t≤24 := ht.2.trans hb
    have hh := exp_bound_global (n:=80) (y:=t)
      (by rw [abs_of_pos ht0];norm_num;linarith)
    rw [abs_of_pos ht0] at hh
    rw [←sub_div,abs_div,abs_of_pos ht0]
    calc
      _ ≤ (t^80/(Nat.factorial 80:ℝ)*2)/t := div_le_div_of_nonneg_right hh ht0.le
      _ = 2*t^79/(Nat.factorial 80:ℝ) := by rw [show 80=79+1 by norm_num,pow_succ];field_simp
      _ ≤ C := by dsimp [C];gcongr
  have hm := integral_mono_on hab (hi.sub hip).abs (intervalIntegrable_const (c:=C)) hpt
  have hnorm := abs_integral_le_integral_abs (μ:=volume) hab
    (f:=fun t => exp t/t-expPoly 80 t/t)
  have hv : (∫ _ in a..b, C) = (b-a)*C := by simp [intervalIntegral.integral_const,smul_eq_mul]
  rw [hv] at hm
  calc
    _ ≤ (b-a)*C := hnorm.trans hm
    _ ≤ 24*C := mul_le_mul_of_nonneg_right (by linarith) hC
    _ = _ := by dsimp [C];norm_num [show 80=79+1 by norm_num,pow_succ]
noncomputable def Li2 (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, 1/log t
lemma Li2_substitution {x : ℝ} (hx : 2≤x) :
    Li2 x = ∫ u in log (2:ℝ)..log x, exp u/u := by
  have hx0 : 0<x := by linarith
  have ha0 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hab : log (2:ℝ)≤log x := log_le_log (by norm_num) hx
  have hd : ∀ u∈Set.uIcc (log (2:ℝ)) (log x), HasDerivAt exp (exp u) u := by
    intro u hu
    exact Real.hasDerivAt_exp u
  have hdc : ContinuousOn (fun u : ℝ=>exp u) (Set.uIcc (log (2:ℝ)) (log x)) :=
    continuous_exp.continuousOn
  have hcont : ContinuousOn (fun t : ℝ=>1/log t)
      (exp '' Set.uIcc (log (2:ℝ)) (log x)) := by
    rintro t ⟨u,hu,rfl⟩
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0<u := ha0.trans_le hu.1
    exact ((continuousAt_const.div (continuousAt_log (exp_pos u).ne')
      (by rw [log_exp];exact hu0.ne')).continuousWithinAt)
  have hh := integral_deriv_smul_comp' hd hdc hcont
  rw [exp_log (by norm_num : (0:ℝ)<2),exp_log hx0] at hh
  unfold Li2
  simpa only [Function.comp_apply,log_exp,smul_eq_mul,one_div,mul_comm,div_eq_mul_inv,one_mul] using hh.symm
lemma Li2_approx {x : ℝ} (hx : 2≤x) (hb : log x≤24) :
    |Li2 x - (primitive 79 (log x)-primitive 79 (log (2:ℝ)))| ≤
      (1:ℝ)/10^7 := by
  rw [Li2_substitution hx]
  have hh := integral_exp_div_approx (log_pos (by norm_num : (1:ℝ)<2))
    (log_le_log (by norm_num) hx) hb
  exact hh.trans (by norm_num)
#print axioms Li2_substitution
#print axioms Li2_approx
#print axioms integral_exp_div_approx
#print axioms exp_bound_global
#print axioms primitive_deriv
end FKSComputationLed.LiTaylor
