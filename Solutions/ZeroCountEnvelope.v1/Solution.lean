/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ZeroCountEnvelope.v1.Conclusions
import IEANTN.Nodes.BellottiWongZeroCount.v1.Conclusions
import IEANTN.Nodes.BPTOffOrdinate.v1.Conclusions
import ZeroEnvelope
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
namespace ZeroCountEnvelope.v1
open Real
/-- Exact relation to the PAPER's displayed center, with exp1 and no7/8. -/
theorem literal_source_main {T:ℝ} (hT:0<T) :
    BellottiWongZeroCount.v1.mainWithoutConstant T =
    T/(2*π)*log (T/(2*π*exp 1)) := by
  have hpi : (2*π:ℝ)≠0 := by positivity
  rw [BellottiWongZeroCount.v1.mainWithoutConstant,
    log_div hT.ne' (mul_ne_zero hpi (exp_ne_zero _)),log_mul hpi (exp_ne_zero _),log_exp,
    log_div hT.ne' hpi]
  ring

theorem challenge_off_ordinate_envelope (hBPT:BPTOffOrdinate.v1.bound)
    (h₁:BellottiWongZeroCount.v1.bound_first) (h₂:BellottiWongZeroCount.v1.bound_second) :
    off_ordinate_envelope := by
  intro T hT hnot
  have he : exp 1 < 2*π := by linarith [Real.exp_one_lt_three,Real.pi_gt_three]
  have h₁' := h₁ T (he.trans hT).le
  have h₂' := h₂ T (he.trans hT).le
  have hc₁ := RH080.Estimates.ZeroEnvelope.recenter h₁'
  have hc₂ := RH080.Estimates.ZeroEnvelope.recenter h₂'
  have hid : BellottiWongZeroCount.v1.mainWithoutConstant T+7/8=ZeroCount.v1.rvmMain T := by
    unfold BellottiWongZeroCount.v1.mainWithoutConstant ZeroCount.v1.rvmMain
    ring
  rw [hid] at hc₁ hc₂
  have h₁'' : |ZeroCount.v1.zetaNClosed T-ZeroCount.v1.rvmMain T|≤bwFirstAllowance (log T) := by
    unfold bwFirstAllowance
    convert hc₁ using 1 <;> ring
  have h₂'' : |ZeroCount.v1.zetaNClosed T-ZeroCount.v1.rvmMain T|≤bwSecondAllowance (log T) := by
    unfold bwSecondAllowance
    convert hc₂ using 1 <;> ring
  exact le_min (hBPT T hT hnot) (le_min h₁'' h₂'')

theorem challenge_bpt_better_low : bpt_better_low := by
  intro L hlo hhi
  exact RH080.Estimates.ZeroEnvelope.bpt_better_low hlo hhi

theorem challenge_bw_second_better_high : bw_second_better_high := by
  intro L hlo
  exact RH080.Estimates.ZeroEnvelope.bw_second_better_high hlo

theorem challenge_bw_first_better_high : bw_first_better_high := by
  intro L hlo
  exact RH080.Estimates.ZeroEnvelope.bw_first_better_high hlo
end ZeroCountEnvelope.v1
#print axioms ZeroCountEnvelope.v1.literal_source_main
#print axioms ZeroCountEnvelope.v1.challenge_off_ordinate_envelope
#print axioms ZeroCountEnvelope.v1.challenge_bpt_better_low
#print axioms ZeroCountEnvelope.v1.challenge_bw_second_better_high
#print axioms ZeroCountEnvelope.v1.challenge_bw_first_better_high
