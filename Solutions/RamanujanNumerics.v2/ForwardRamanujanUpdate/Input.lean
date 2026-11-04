/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DDExpansionSolution
import ForwardRamanujan.Consumer
namespace ForwardRamanujan.Update
open Real IEANTN DudekPlatt.v3
/-- Use the actual existing proof, not an assumed QRH-shaped coefficient array. -/
theorem supplied_pi (hpsi : QRHCH2.v5.psi_refined_bound) : DudekPlattNumerics.v5.pi_two_sided_qrh :=
  DudekPlattNumerics.v5.challenge_pi_two_sided_qrh hpsi

theorem pi_input (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) : PiInput 119 131 3914 := by
  constructor
  · intro x hx
    exact (hp x ((exp_lt_exp.mpr (by norm_num : (400:ℝ)<3914)).trans hx)).1
  · intro x hx
    have ht : (400:ℝ)<3914+1 := by norm_num
    exact (hp x ((exp_lt_exp.mpr ht).trans hx)).2

/-- This new implication does not retroactively enter the frozen independent old baseline. -/
theorem implies_old (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    DudekPlattNumerics.v7.pi_asymmetric_pnt := by
  constructor
  · intro x hx
    have h := (hp x ((exp_lt_exp.mpr (by norm_num : (400:ℝ)<3914)).trans hx)).1
    have hx0 : 0<x := (exp_pos _).trans hx
    have hq : (0:ℝ)≤x/log x^6 := by positivity
    rw [mul_div_assoc] at h
    linarith
  · intro x hx
    have h := (hp x ((exp_lt_exp.mpr (by norm_num : (400:ℝ)<3915)).trans hx)).2
    have hx0 : 0<x := (exp_pos _).trans hx
    have hq : (0:ℝ)≤x/log x^6 := by positivity
    rw [mul_div_assoc] at h
    linarith
end ForwardRamanujan.Update
