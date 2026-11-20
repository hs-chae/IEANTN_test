/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.FirstCriticalCell

/-! Reuse the actual finite cell's discarded integer slack. No new numerical
count, analytic input or native computation is assumed in this deduction. -/
namespace RamanujanPV.RecoveredMargin
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem cell_gap_lower {n m j P Q : ℕ} {x D : ℝ}
    (hn : exp 1 ≤ (n : ℝ)) (hnx : (n : ℝ) ≤ x) (hxm : x < (m : ℝ) + 1)
    (hP : Nat.primeCounting m = P) (hQ : Nat.primeCounting j = Q)
    (hj : (j : ℝ) * exp 1 ≤ n)
    (hscalar : D + (P : ℝ)^2 < exp 1 * n / log n * Q) : D < gap x := by
  have hn0 : 0 < (n : ℝ) := (exp_pos 1).trans_le hn
  have hx0 : 0 < x := hn0.trans_le hnx
  have hlx : 0 < log x := by
    have : (1 : ℝ) ≤ log x := by
      simpa using log_le_log (exp_pos 1) (hn.trans hnx)
    linarith
  have hupper : primeCounting x ≤ (P : ℝ) := by
    simpa only [hP] using primeCounting_le_of_lt_succ hx0.le hxm
  have hjx : (j : ℝ) ≤ x / exp 1 :=
    (le_div_iff₀ (exp_pos 1)).2 (hj.trans hnx)
  have hlower : (Q : ℝ) ≤ primeCounting (x / exp 1) := by
    simpa only [primeCounting_nat, hQ] using primeCounting_mono hjx
  have hfactor : exp 1 * n / log n ≤ exp 1 * x / log x := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (div_log_mono hn hnx) (exp_pos 1).le
  have hsq : primeCounting x ^ 2 ≤ (P : ℝ)^2 :=
    pow_le_pow_left₀ (primeCounting_nonneg x) hupper 2
  have hprod : exp 1 * n / log n * Q ≤
      exp 1 * x / log x * primeCounting (x / exp 1) :=
    (mul_le_mul_of_nonneg_right hfactor (by positivity)).trans
      (mul_le_mul_of_nonneg_left hlower (by positivity))
  unfold gap
  linarith

/-- The same factored integer predicate can retain an arbitrary strict margin
instead of discarding all information after the positivity test. -/
theorem factored_gap_lower {n m j P Q eLo eHi Lu A : ℕ} {x D : ℝ}
    (hn : exp 1 ≤ (n : ℝ))
    (hP : Nat.primeCounting m = P) (hQ : Nat.primeCounting j = Q)
    (heLo : (eLo : ℝ) ≤ exp 1 * (2 : ℝ)^60)
    (heHi : exp 1 * (2 : ℝ)^60 ≤ (eHi : ℝ))
    (hlog : log (n : ℝ) * (2 : ℝ)^40 ≤ (Lu : ℝ))
    (hj : j * eHi ≤ n * 2^60) (hA : A * Lu ≤ n * eLo)
    (hmargin : (2 : ℝ)^20 * ((P : ℝ)^2 + D) < (A : ℝ) * Q)
    (hnx : (n : ℝ) ≤ x) (hxm : x < (m : ℝ) + 1) : D < gap x := by
  have hj' : (j : ℝ) * exp 1 ≤ n := by
    have hji : (j : ℝ) * eHi ≤ n * (2 : ℝ)^60 := by exact_mod_cast hj
    have hje := mul_le_mul_of_nonneg_left heHi (show (0 : ℝ) ≤ j by positivity)
    nlinarith
  have hl : 0 < log (n : ℝ) := by
    have : (1 : ℝ) ≤ log (n : ℝ) := by
      simpa using log_le_log (exp_pos 1) hn
    linarith
  have hAs : (A : ℝ) * log (n : ℝ) ≤ exp 1 * n * (2 : ℝ)^20 := by
    have hAi : (A : ℝ) * Lu ≤ n * eLo := by exact_mod_cast hA
    have hAl := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ A by positivity)
    have hAe := mul_le_mul_of_nonneg_left heLo (show (0 : ℝ) ≤ n by positivity)
    have hs : (2 : ℝ)^60 = (2 : ℝ)^40 * (2 : ℝ)^20 := by norm_num
    apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (2 : ℝ)^40)).mp
    rw [hs] at hAe
    nlinarith
  have hscale : (A : ℝ) / (2 : ℝ)^20 ≤ exp 1 * n / log n := by
    apply (div_le_div_iff₀ (by positivity) hl).mpr
    exact hAs
  have hscalar : D + (P : ℝ)^2 < exp 1 * n / log n * Q := by
    have hfirst : (P : ℝ)^2 + D < (A : ℝ)*Q / (2 : ℝ)^20 :=
      (lt_div_iff₀ (by positivity)).mpr (by nlinarith [hmargin])
    have hsecond := mul_le_mul_of_nonneg_right hscale (show (0 : ℝ) ≤ Q by positivity)
    rw [div_mul_eq_mul_div] at hsecond
    linarith
  exact cell_gap_lower hn hnx hxm hP hQ hj' hscalar

open FirstCriticalCell in
/-- Recovered information at the difficult lower endpoint: the SAME two source
executions prove a uniform quantitative result throughout the first56 real units.
The concrete executions remain pending until their numerical proofs are closed. -/
theorem first_cell_margin_from_source
    (runP : QuotientCCell.SourceExecution N0 P0)
    (runQ : QuotientCCell.SourceExecution J0 Q0)
    {x : ℝ} (hx : (38358837683 : ℝ) ≤ x) (hxNext : x < 38358837739) :
    (52869788 : ℝ) < gap x := by
  obtain ⟨hn, heLo, heHi, hlog⟩ := real_enclosures
  simp only [cell, raw, RawFactoredCell.toCell, Nat.cast_pow, Nat.cast_ofNat] at hn heLo heHi hlog
  obtain ⟨hP, hQ⟩ := counts_from_source runP runQ
  have hlog' : log (N0 : ℝ) * (2 : ℝ)^40 ≤ (26795374111319 : ℝ) := by
    norm_num at hlog ⊢
    linarith only [hlog]
  have hj : J0*eHi ≤ N0*2^60 := by norm_num [N0,J0,eLo,eHi]
  have hA : (4486419048288114 : ℕ)*26795374111319 ≤ N0*eLo := by norm_num [N0,eLo]
  have hm : (2 : ℝ)^20*((P0 : ℝ)^2+52869788) < (4486419048288114 : ℝ)*Q0 := by
    norm_num [P0,Q0]
  have hend : x < ((38358837738 : ℕ) : ℝ)+1 := by norm_num; exact hxNext
  exact factored_gap_lower (n:=N0) (m:=38358837738) (j:=J0)
    (P:=P0) (Q:=Q0) (eLo:=eLo) (eHi:=eHi) (Lu:=26795374111319)
    (A:=4486419048288114) hn hP hQ heLo heHi hlog' hj hA hm hx hend

#print axioms cell_gap_lower
#print axioms factored_gap_lower
#print axioms first_cell_margin_from_source
end RamanujanPV.RecoveredMargin
