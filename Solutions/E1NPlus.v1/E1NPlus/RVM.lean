/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Scalars
namespace E1NPlus
open Real
set_option maxHeartbeats 0

theorem rvm_count_sharp (h:ZeroCount.v1.rvm_error_bound)
    {t:ℝ} (ht:1000≤t) :
    ZeroCount.v1.zetaNClosed t≤t*log t/(2*Real.pi) := by
  have ht0:0<t:=by linarith
  have hd:0<2*Real.pi:=by positivity
  have hex:1000≤exp (10:ℝ) := by
    have hb:=(CH2Section7A.exp_nat_bounds 10).1
    norm_num at hb ⊢
    linarith
  have hlog1000:log (1000:ℝ)≤10 := by
    simpa only [log_exp] using log_le_log (by norm_num : (0:ℝ)<1000) hex
  have hh:=log_le_sub_one_of_pos (show (0:ℝ)<t/1000 by positivity)
  rw [log_div ht0.ne' (by norm_num : (1000:ℝ)≠0)] at hh
  have hlogt:log t≤9+t/1000:=by linarith
  let a:ℝ:=t/(2*Real.pi)
  have ha0:0≤a:=by dsimp [a];positivity
  have ha:t/8≤a := by
    dsimp [a]
    apply (le_div_iff₀ hd).mpr
    have hm:=mul_le_mul_of_nonneg_left (le_of_lt pi_lt_four) ht0.le
    nlinarith
  have hlp:0≤log (2*Real.pi):=log_nonneg (by linarith [Real.pi_gt_three])
  have hp:=mul_nonneg ha0 hlp
  have hN:ZeroCount.v1.zetaNClosed t-ZeroCount.v1.rvmMain t≤(1/5)*log t+2:=
    (abs_le.mp (h t (by linarith))).2
  have he:ZeroCount.v1.rvmMain t=
      a*log t-a*log (2*Real.pi)-a+7/8 := by
    rw [ZeroCount.v1.rvmMain,log_div ht0.ne' hd.ne']
    dsimp [a]
    ring
  rw [he] at hN
  have he2:t*log t/(2*Real.pi)=a*log t := by dsimp [a];ring
  rw [he2]
  linarith
#print axioms rvm_count_sharp
end E1NPlus
