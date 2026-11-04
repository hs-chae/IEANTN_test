/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujan.Math
import IEANTN.Nodes.DudekPlattNumerics.v2.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v7.Conclusions
import IEANTN.Nodes.RamanujanNumerics.v1.Conclusions
import IEANTN.Nodes.RamanujanGap.v1.Conclusions

namespace ForwardRamanujan
open Real IEANTN DudekPlatt.v3

theorem old_pi_input (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt) :
    PiInput (-1194) 1426 3914 := by
  constructor
  · intro x hx
    have he : mainTerm x+(-1194)*x/log x^6=mainTerm x-1194*(x/log x^6) := by ring
    rw [he]
    exact hp.1 x hx
  · intro x hx
    have hx' : exp 3915<x := by norm_num at hx;exact hx
    have he : mainTerm x+1426*x/log x^6=mainTerm x+1426*(x/log x^6) := by ring
    rw [he]
    exact hp.2 x hx'

/-- The older existing node is sufficient, but its stronger upper range is not required. -/
theorem historical_v2_to_asymmetric (hp : DudekPlattNumerics.v2.pi_two_sided_pnt) :
    DudekPlattNumerics.v7.pi_asymmetric_pnt := by
  have h := hp
  simp only [DudekPlattNumerics.v2.pi_two_sided_pnt,IEANTN.margin,pow_zero,one_mul] at h
  constructor
  · intro x hx
    simpa only [mainTerm,DudekPlattNumerics.v2.mainTerm] using (h x hx).1
  · intro x hx
    exact (by simpa only [mainTerm,DudekPlattNumerics.v2.mainTerm] using
      (h x ((exp_lt_exp.mpr (by norm_num : (3914:ℝ)<3915)).trans hx)).2)
end ForwardRamanujan
open Real IEANTN ForwardRamanujan

theorem RamanujanGap.v1.challenge_loss_bound
    (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt)
    (hc : RamanujanNumerics.v1.epsilon_budget) : RamanujanGap.v1.loss_bound := by
  intro x hx
  change ForwardRamanujan.loss x≤3914.7/log x
  exact loss_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (old_pi_input hp) (by norm_num) hx (hc x hx)

theorem RamanujanGap.v1.challenge_gap_lower_bound
    (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt)
    (hc : RamanujanNumerics.v1.epsilon_budget) : RamanujanGap.v1.gap_lower_bound := by
  intro x hx
  change (1-3914.7/log x)*x^2/log x^6<ForwardRamanujan.gap x
  have hg := gap_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (old_pi_input hp) hx (hc x hx)
  have hL : 0<log x := by
    have h := log_lt_log (exp_pos (3915:ℝ)) hx
    rw [log_exp] at h
    linarith
  convert hg using 1 <;> field_simp [hL.ne'] <;> ring

theorem RamanujanGap.v1.challenge_ramanujan
    (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt)
    (hc : RamanujanNumerics.v1.epsilon_budget) : RamanujanGap.v1.ramanujan := by
  intro x hx
  have hg := gap_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (old_pi_input hp) hx (hc x hx)
  have hx0 : 0<x := (exp_pos _).trans hx
  have hL : 3915<log x := by simpa using log_lt_log (exp_pos (3915:ℝ)) hx
  have hL0 : 0<log x := by linarith
  have hnum : 0<log x-3914.7 := by linarith
  have hpos : (0:ℝ)<x^2*((log x-3914.7)/log x^7) := by positivity
  unfold ForwardRamanujan.gap at hg
  linarith
