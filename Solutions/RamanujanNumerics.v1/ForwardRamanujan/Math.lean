/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Bounds

namespace ForwardRamanujan
open Real IEANTN DudekPlatt.v3

noncomputable def terms (m M A Y : ℝ) : List ℝ :=
  [2*M,(2*M+132)/Y,(4*M+288)/Y^2,(12*M+576)/Y^3,
    48*M/Y^4,M^2/Y^5,max 0 (-m)*(1+1/A)^6]

noncomputable def upper (m M A Y : ℝ) : ℝ :=
  (terms m M A Y).sum-134-max 0 m

/-- The existing two-sided analytic input, kept separate from numerical soundness. -/
def PiInput (m M A : ℝ) : Prop :=
  (∀ x > exp A,mainTerm x+m*x/log x^6 < primeCounting x) ∧
  (∀ x > exp (A+1),primeCounting x < mainTerm x+M*x/log x^6)

noncomputable def gap (x : ℝ) : ℝ :=
  exp 1*x/log x*primeCounting (x/exp 1)-primeCounting x^2
noncomputable def loss (x : ℝ) : ℝ := max 0 (1-log x^6/x^2*gap x)

/-- Generic endpoint majorant, including the repaired negative-lower-coefficient case. -/
theorem epsilon_majorant {m M A Y x : ℝ} (hM : 0 ≤ M) (hY : 0<Y)
    (hx : Y ≤ log x) : εUpper M x-εLower m (exp A) x ≤ upper m M A Y := by
  have hL : 0<log x := hY.trans_le hx
  have key (c : ℝ) (k : ℕ) (hc : 0≤c) : c/log x^k ≤ c/Y^k :=
    div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_left₀ hY.le hx k)
  have h1 : (2*M+132)/log x ≤ (2*M+132)/Y := by simpa using key _ 1 (by linarith)
  have h2 := key (4*M+288) 2 (by linarith)
  have h3 := key (12*M+576) 3 (by linarith)
  have h4 := key (48*M) 4 (by positivity)
  have h5 := key (M^2) 5 (sq_nonneg M)
  have n1 : (0:ℝ)≤364/log x := by positivity
  have n2 : (0:ℝ)≤381/log x^2 := by positivity
  have n3 : (0:ℝ)≤238/log x^3 := by positivity
  have n4 : (0:ℝ)≤97/log x^4 := by positivity
  have n5 : (0:ℝ)≤30/log x^5 := by positivity
  have n6 : (0:ℝ)≤8/log x^6 := by positivity
  have hlo : 206+max 0 m-max 0 (-m)*(1+1/A)^6 ≤ εLower m (exp A) x := by
    by_cases hm : 0≤m
    · rw [εLower,if_pos hm,εPos,max_eq_right hm,max_eq_left (by linarith : -m≤0)]
      nlinarith
    · have hm0 : m≤0 := (lt_of_not_ge hm).le
      rw [εLower,if_neg hm,εNeg,log_exp,max_eq_left hm0,max_eq_right (by linarith : 0≤-m)]
      nlinarith
  simp only [upper,terms,List.sum_cons,List.sum_nil,add_zero,εUpper]
  linarith

/-- Quantitative content of the original repaired Ramanujan proof. -/
theorem gap_from_budget {m M A Y C x : ℝ} (hA : 0<A) (hAY : A+1≤Y)
    (hpi : PiInput m M A) (hx : exp Y<x)
    (hbudget : εUpper M x-εLower m (exp A) x ≤ C) :
    x^2*((log x-C)/log x^7)<gap x := by
  have hxe : exp 1*exp A<x := by
    rw [←exp_add]
    exact (exp_le_exp.mpr (by linarith : (1:ℝ)+A≤Y)).trans_lt hx
  have hxa : 1<exp A := by simpa using exp_lt_exp.mpr hA
  have hxx : exp A<x := (exp_lt_exp.mpr (by linarith : A<Y)).trans hx
  have hxxUpper : exp (A+1)<x := (exp_le_exp.mpr hAY).trans_lt hx
  have hsq := DudekPlattSol.sq_pi_lt M (exp (A+1))
    (fun t ht => by simpa only [mainTerm] using hpi.2 t ht) x hxxUpper
  have hlo := DudekPlattSol.ex_pi_gt m (exp A) hxa
    (fun t ht => by simpa only [mainTerm] using hpi.1 t ht) x hxe
  have hL : 0<log x := by
    have hy := log_lt_log (exp_pos Y) hx
    rw [log_exp] at hy
    linarith
  have hx0 : 0<x := (exp_pos Y).trans hx
  have hid :
      (1/log x^2+2/log x^3+5/log x^4+16/log x^5+65/log x^6+
        εLower m (exp A) x/log x^7)-
      (1/log x^2+2/log x^3+5/log x^4+16/log x^5+64/log x^6+
        εUpper M x/log x^7) = (log x-(εUpper M x-εLower m (exp A) x))/log x^7 := by
    field_simp [hL.ne'];ring
  have hgap : x^2*((log x-(εUpper M x-εLower m (exp A) x))/log x^7)<gap x := by
    rw [←hid]
    unfold gap
    nlinarith
  have hquot : (log x-C)/log x^7 ≤
      (log x-(εUpper M x-εLower m (exp A) x))/log x^7 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  exact (mul_le_mul_of_nonneg_left hquot (sq_nonneg x)).trans_lt hgap

/-- The output certificate becomes a bound on the actual pi-expression, not merely on a parameter. -/
theorem loss_from_budget {m M A Y C x : ℝ} (hA : 0<A) (hAY : A+1≤Y)
    (hpi : PiInput m M A) (hC : 0≤C) (hx : exp Y<x)
    (hbudget : εUpper M x-εLower m (exp A) x ≤ C) : loss x ≤ C/log x := by
  have hg := gap_from_budget hA hAY hpi hx hbudget
  have hx0 : 0<x := (exp_pos Y).trans hx
  have hL : 0<log x := by
    have hy := log_lt_log (exp_pos Y) hx
    rw [log_exp] at hy
    linarith
  have hn := mul_lt_mul_of_pos_left hg (show (0:ℝ)<log x^6/x^2 by positivity)
  have hid : log x^6/x^2*(x^2*((log x-C)/log x^7))=1-C/log x := by
    field_simp [hL.ne',hx0.ne']
  rw [hid] at hn
  exact max_le (by positivity) (by linarith)

end ForwardRamanujan
