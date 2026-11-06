/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Evolved.Comparison
import HighAnchorIntervalB.UnionComparison
namespace E1Evolved
open Real

theorem frozen_prime_width_strict {x:ℝ} (hx:exp (330:ℝ)≤x) :
    (22/25:ℝ)*x^(79/100:ℝ)<
      (1839254524623/100000000000000:ℝ)*x^(7/8:ℝ) := by
  have hp:0<x:=(exp_pos _).trans_le hx
  have hL:330≤log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hsq:exp (99/4:ℝ)=exp (99/8:ℝ)^2 := by
    rw [pow_two,←exp_add]
    congr 1
    norm_num
  have he:100≤exp (99/4:ℝ) := by
    have hl:=add_one_le_exp (99/8:ℝ)
    have hz:=exp_pos (99/8:ℝ)
    rw [hsq]
    nlinarith
  have hr:100≤x^(3/40:ℝ) := by
    rw [rpow_def_of_pos hp]
    exact he.trans (exp_le_exp.mpr (by linarith))
  have hpow:x^(7/8:ℝ)=x^(4/5:ℝ)*x^(3/40:ℝ) := by
    rw [←rpow_add hp]
    congr 1
    norm_num
  have hpos:0<x^(4/5:ℝ):=rpow_pos_of_pos hp _
  have hm:=mul_le_mul_of_nonneg_left hr hpos.le
  have hweak:x^(4/5:ℝ)<(1839254524623/100000000000000:ℝ)*x^(7/8:ℝ) := by
    rw [hpow]
    nlinarith
  exact (HighAnchorIntervalB.interval_width_strict hx).trans hweak
#print axioms frozen_prime_width_strict
end E1Evolved
