/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.PVFloorSound
import PVEvolutionA.Pointwise
namespace PVEvolutionA.Recovery.PVFloor
open Real
set_option maxHeartbeats 0

theorem full_floor (hb : boxesAccepted) (ha : arithmetic) (ht : totalAccepted=true)
    {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x) :
    (floor:ℝ)*PVEvolutionA.scale x≤PVEvolutionA.bestBound x := by
  have hp : 0<x := (exp_pos _).trans_le hx.1
  have hL : 330≤log x := by simpa only [log_exp] using log_le_log (exp_pos _) hx.1
  have hU : log x≤331 := by simpa only [log_exp] using log_le_log hp hx.2
  have hf := floor_coefficient hb ha ht (by linarith : 0≤log x) hU
    (by linarith : 0<log x/3)
  have hs : 0<PVEvolutionA.scale x := rpow_pos_of_pos hp _
  unfold PVEvolutionA.bestBound
  apply le_min
  · unfold PVEvolutionA.bound
    have h300 : (floor:ℝ)≤PVEvolutionA.C300 := by norm_num [floor,PVEvolutionA.C300]
    have h330 : (floor:ℝ)≤PVEvolutionA.C330 := by norm_num [floor,PVEvolutionA.C330]
    have hmid : (floor:ℝ)≤PVEvolutionA.Cmid := by norm_num [floor,PVEvolutionA.Cmid]
    split_ifs
    · exact mul_le_mul_of_nonneg_right hmid hs.le
    · exact mul_le_mul_of_nonneg_right h330 hs.le
    · exact mul_le_mul_of_nonneg_right h300 hs.le
  · unfold PVEvolutionA.pointBound PVEvolutionA.pointCoefficient
    apply mul_le_mul_of_nonneg_right _ hs.le
    have hcf : 0≤PVEvolutionA.Sloped.coefficient 65536 (log x) (log x/3) :=
      (by norm_num [floor] : (0:ℝ)≤floor).trans hf
    nlinarith

/-- A strict allowance comparison on every point of the closed domain;
this does not assert any lower bound for the actual prime-counting error. -/
theorem strict_full_comparison (hb : boxesAccepted) (ha : arithmetic) (ht : totalAccepted=true)
    {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x) :
    (91347/10000000:ℝ)*PVEvolutionA.scale x+
      (2/1000000:ℝ)*PVEvolutionA.scale x<PVEvolutionA.bestBound x := by
  have hp : 0<x := (exp_pos _).trans_le hx.1
  have hs : 0<PVEvolutionA.scale x := rpow_pos_of_pos hp _
  have hstrict : (91347/10000000:ℝ)+(2/1000000:ℝ)<floor := by norm_num [floor]
  have hmul:=mul_lt_mul_of_pos_right hstrict hs
  rw [add_mul] at hmul
  exact hmul.trans_le (full_floor hb ha ht hx)
#print axioms full_floor
#print axioms strict_full_comparison
end PVEvolutionA.Recovery.PVFloor
