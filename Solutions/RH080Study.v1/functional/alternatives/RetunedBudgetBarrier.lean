/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

/-! Pure scalar analysis of the conservative retuned 2026 finite-window budget.
The source is Blanquer--Robles 2026v2, Eq20--21 and Table3 (physical pp13--14).
The paper proves its analytic transfer only at c=681/800. This file does not
supply a variable-c analytic theorem or conclude any prime-existence failure.
-/
noncomputable section
set_option autoImplicit false
namespace RH080.Alternatives
open Real

def retunedMargin (c t : ℝ) : ℝ :=
  ((c*(92045248904315389/100000000000000000) -
    78353189999070/100000000000000)/2)*t +
  (78353189999069/100000000000000)*log (c*t*log 2/2) -
    1101508373007/1000000000000

/-- This particular conservative budget cannot certify c=.8 anywhere above
log(x)=44. Negativity of a sufficient lower bound is not a prime counterexample,
a universal obstruction, or an assertion that the actual source margin is negative. -/
theorem retuned_eight_tenths_negative {t : ℝ} (ht : 44 ≤ t) :
    retunedMargin (4/5) t ≤ -(1/20 : ℝ) := by
  let k : ℝ := (4/5)*log 2/2
  have hk : 0 < k := by dsimp [k]; positivity
  have ht0 : 0 < t := by linarith
  have h44 : 0 < k*44 := by positivity
  have h8 : log (8 : ℝ) = 3*log 2 := by
    rw [show (8 : ℝ) = 2^(3 : ℕ) by norm_num, log_pow]
    norm_num
  have hbase := log_le_sub_one_of_pos (div_pos h44 (by norm_num : (0 : ℝ) < 8))
  rw [log_div h44.ne' (by norm_num : (8 : ℝ) ≠ 0), h8] at hbase
  have hslope := log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 44))
  rw [log_div ht0.ne' (by norm_num : (44 : ℝ) ≠ 0)] at hslope
  have hlog : log (k*t) ≤ log (k*44) + (t/44-1) := by
    rw [log_mul hk.ne' ht0.ne', log_mul hk.ne' (by norm_num : (44 : ℝ) ≠ 0)]
    linarith
  have htwo : log 2 < (7/10 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hbase' : log (k*44) ≤ (66/25 : ℝ) := by
    dsimp [k] at hbase ⊢
    nlinarith
  have hlog' : log (k*t) ≤ (66/25 : ℝ) + (t/44-1) := hlog.trans (by linarith)
  have heq : (4/5 : ℝ)*t*log 2/2 = k*t := by dsimp [k]; ring
  unfold retunedMargin
  rw [heq]
  nlinarith

#print axioms retuned_eight_tenths_negative
end RH080.Alternatives
