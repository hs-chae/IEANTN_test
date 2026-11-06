/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Evolved.Final
namespace E1Evolved
open Real WinnerDensityA WinnerDensityA.Program PVEvolutionA
open PVEvolutionA.Recovery PVEvolutionA.Recovery.PVFloor
set_option maxHeartbeats 0

theorem separated_floor {L τ:ℝ} (hL:0≤L) (hU:L≤331) (hτ:0<τ) :
    (floor:ℝ)≤PVEvolutionA.Separated.coefficient 65536 L τ := by
  have hc:∀i<cells,(cap (i+1):ℝ)≤cap i := by
    intro i hi
    exact_mod_cast (checked_arithmetic ⟨i,hi⟩).2
  have hlast:gradedGrid cells cells=(7/8:ℝ):=graded_last _
  have hm:=StepGrid.antitone (gradedGrid cells) (fun i=>(cap i:ℝ)) cells
    (fun i hi=>(graded_monotone cells hi).trans_eq hlast) hc hlast hU
  have hp:(floor:ℝ)≤StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells 331 := by
    rw [←PVFloor.program_semantics]
    exact lower_of_execution checked_total
  have hg:=(hp.trans hm).trans (lower_grid checked_boxes hL hτ)
  unfold PVEvolutionA.Separated.coefficient
  have ht:0≤exp (-L/8)*((L/3+1/10^9)^2/(2*Real.pi)+
      (2+1/Real.pi)*(L/3+1/10^9))+1/10^12 := by positivity
  linarith

theorem frozen_pair_full_floor {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    (floor:ℝ)*PVEvolutionA.scale x≤E1FrozenN.finalErrorBound x := by
  have hp:0<x:=(exp_pos _).trans_le hx.1
  have hL:330≤log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx.1
  have hU:log x≤331:=by simpa only [log_exp] using log_le_log hp hx.2
  have hs:0≤x^(-(1:ℝ)/8):=rpow_nonneg hp.le _
  change (floor:ℝ)*x^(-(1:ℝ)/8)≤_
  unfold E1FrozenN.finalErrorBound E1FrozenN.errorBound
  apply le_min
  · apply le_min
    · split_ifs
      · exact mul_le_mul_of_nonneg_right (by norm_num [floor]) hs
      · exact mul_le_mul_of_nonneg_right (by norm_num [floor]) hs
    · exact mul_le_mul_of_nonneg_right
        (separated_floor (by linarith) hU (by norm_num : (0:ℝ)<100)) hs
  · exact mul_le_mul_of_nonneg_right (by norm_num [floor]) hs

theorem pair_full_closed_domain_strict {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    kappa*PVEvolutionA.scale x+(2/1000000:ℝ)*PVEvolutionA.scale x<
      E1FrozenN.finalErrorBound x := by
  have hs:0<PVEvolutionA.scale x:=rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _
  have hm:=mul_lt_mul_of_pos_right
    (by norm_num [floor,kappa] : kappa+(2/1000000:ℝ)<floor) hs
  rw [add_mul] at hm
  exact hm.trans_le (frozen_pair_full_floor hx)
#print axioms pair_full_closed_domain_strict
end E1Evolved
