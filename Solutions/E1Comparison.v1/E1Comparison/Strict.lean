/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Comparison.AllGridFloor
import E1Evolved.Comparison
import E1NPlus.TightAll
namespace E1Comparison
open Real Set WinnerDensityA
open PVEvolutionA PVEvolutionA.Recovery PVEvolutionA.Recovery.PVFloor
set_option maxHeartbeats 0

theorem separated_all_floor {n:ℕ} (hn:0<n) {L τ:ℝ} (hL:0 ≤ L) (hU:L ≤ 331) (hτ:0<τ):
    (floor:ℝ) ≤ PVEvolutionA.Separated.coefficient n L τ := by
  have hc:∀i<cells,(cap (i+1):ℝ) ≤ cap i:=by
    intro i hi;exact_mod_cast (checked_arithmetic ⟨i,hi⟩).2
  have hlast:=graded_last cells
  have hmono:=StepGrid.antitone (gradedGrid cells) (fun i=>(cap i:ℝ)) cells
    (fun i hi=>(graded_monotone cells hi).trans_eq hlast) hc hlast hU
  have hp:(floor:ℝ) ≤ StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells 331:=by
    rw [←program_semantics];exact lower_of_execution checked_total
  have hg:=(((hp.trans hmono).trans (coarse_le_mass checked_arithmetic hL)).trans
    (mass_le_grid checked_boxes checked_arithmetic hn hL hτ))
  unfold PVEvolutionA.Separated.coefficient
  have ht0:0 ≤ exp (-L/8)*((L/3+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(L/3+1/10^9))+1/10^12:=by positivity
  linarith

theorem nplus_pair_floor {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    ((floor:ℝ)-1/10^12)*PVEvolutionA.scale x ≤ E1NPlus.finalPairBound x := by
  have hp:0<x:=(exp_pos _).trans_le hx.1
  have hL:330 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx.1
  have hU:log x ≤ 331:=by simpa only [log_exp] using log_le_log hp hx.2
  have hs:0 ≤ x^(-(1:ℝ)/8):=rpow_nonneg hp.le _
  have hf:(floor:ℝ)-1/10^12 ≤ floor:=by norm_num
  have hold:= (mul_le_mul_of_nonneg_right hf hs).trans (E1Evolved.frozen_pair_full_floor hx)
  have hg:((floor:ℝ)-1/10^12)*x^(-(1:ℝ)/8) ≤ E1NPlus.gridInfBound x:=by
    apply le_ciInf
    intro n
    exact mul_le_mul_of_nonneg_right (hf.trans (separated_all_floor n.pos (by linarith) hU (by norm_num : (0:ℝ)<100))) hs
  have ht:((floor:ℝ)-1/10^12)*x^(-(1:ℝ)/8) ≤ E1NPlus.tightInfBound x:=by
    apply le_ciInf
    intro n
    apply mul_le_mul_of_nonneg_right _ hs
    linarith [separated_all_floor n.pos (by norm_num : (0:ℝ) ≤ 330) (by norm_num : (330:ℝ) ≤ 331) (by norm_num : (0:ℝ)<100)]
  change ((floor:ℝ)-1/10^12)*x^(-(1:ℝ)/8) ≤ _
  unfold E1NPlus.finalPairBound E1NPlus.pairBound
  simp only [if_pos hx.1]
  exact le_min (le_min hg hold) ht

theorem nplus_pi_floor {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    (floor:ℝ)*PVEvolutionA.scale x ≤ E1NPlus.piBound x := by
  have hp:0<x:=(exp_pos _).trans_le hx.1
  have hL:330 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx.1
  have hU:log x ≤ 331:=by simpa only [log_exp] using log_le_log hp hx.2
  have hs:0 ≤ x^(-(1:ℝ)/8):=rpow_nonneg hp.le _
  refine le_min (full_floor_checked hx) ?_
  apply le_ciInf
  intro n
  unfold E1NPlus.piGridBound
  apply mul_le_mul_of_nonneg_right _ hs
  have hf:=all_grid_floor checked_boxes checked_arithmetic checked_total n.pos
    (by linarith :0 ≤ log x) hU (by linarith :0<log x/3)
  have hc:0 ≤ PVEvolutionA.Sloped.coefficient (n:ℕ) (log x) (log x/3):=
    (by norm_num [floor] : (0:ℝ) ≤ floor).trans hf
  nlinarith

theorem pair_strict {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    E1Evolved.kappa*PVEvolutionA.scale x+(2/1000000:ℝ)*PVEvolutionA.scale x<
      E1NPlus.finalPairBound x := by
  have hs:0<PVEvolutionA.scale x:=rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _
  have hm:=mul_lt_mul_of_pos_right
    (by norm_num [floor,E1Evolved.kappa] : E1Evolved.kappa+(2/1000000:ℝ)<(floor:ℝ)-1/10^12) hs
  rw [add_mul] at hm
  exact hm.trans_le (nplus_pair_floor hx)

theorem pi_strict {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    (9134616/1000000000:ℝ)*PVEvolutionA.scale x+(2/1000000:ℝ)*PVEvolutionA.scale x<
      E1NPlus.piBound x := by
  have hs:0<PVEvolutionA.scale x:=rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _
  have hm:=mul_lt_mul_of_pos_right
    (by norm_num [floor] : (9134616/1000000000:ℝ)+(2/1000000:ℝ)<floor) hs
  rw [add_mul] at hm
  exact hm.trans_le (nplus_pi_floor hx)
#print axioms pair_strict
#print axioms pi_strict
end E1Comparison
