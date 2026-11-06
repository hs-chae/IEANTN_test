/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.PVFloorComparison
import PVEvolutionA.Recovery.PVFloorBoxRun
import PVEvolutionA.Recovery.PVFloorWeightRun
namespace PVEvolutionA.Recovery.PVFloor
 theorem full_floor_checked {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x) :
    (floor:ℝ)*PVEvolutionA.scale x≤PVEvolutionA.bestBound x :=
  full_floor checked_boxes checked_arithmetic checked_total hx
 theorem strict_full_comparison_checked {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x) :
    (91347/10000000:ℝ)*PVEvolutionA.scale x+
      (2/1000000:ℝ)*PVEvolutionA.scale x<PVEvolutionA.bestBound x :=
  strict_full_comparison checked_boxes checked_arithmetic checked_total hx
 theorem strict_all39_checked {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x)
    (i : Fin 39) : (91347/10000000:ℝ)*PVEvolutionA.scale x<
      ScopedWinnerA.Coverage.allowance x i := by
  have hs : 0≤PVEvolutionA.scale x := Real.rpow_nonneg ((Real.exp_pos _).trans_le hx.1).le _
  have hh:=strict_full_comparison_checked hx
  have hm : 0≤(2/1000000:ℝ)*PVEvolutionA.scale x := mul_nonneg (by norm_num) hs
  have hn : (91347/10000000:ℝ)*PVEvolutionA.scale x<PVEvolutionA.bestBound x := by linarith
  have ho:=PVEvolutionA.strict_old39 hx
  have hb:=min_le_left (PVEvolutionA.bound x) (PVEvolutionA.pointBound x)
  have hm' : 0≤(32393/100000000:ℝ)*PVEvolutionA.scale x := mul_nonneg (by norm_num) hs
  have he : PVEvolutionA.bestBound x<ScopedWinnerA.Coverage.envelope x := by
    change PVEvolutionA.bestBound x≤PVEvolutionA.bound x at hb
    linarith
  exact (hn.trans he).trans_le (Finset.inf'_le _ (Finset.mem_univ i))
#print axioms strict_all39_checked
#print axioms full_floor_checked
#print axioms strict_full_comparison_checked
end PVEvolutionA.Recovery.PVFloor
