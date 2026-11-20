/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCheckerMath

namespace RamanujanPV.SegmentCounts
open Finset SegmentCheckerMath
set_option autoImplicit false

/-- The actual inclusive segment has exactly the indices read by the source
loop. This is a mathematical bijection, not a numerical certificate premise. -/
theorem sum_finalFlags {lo hi : Nat} (hlo : 2 ≤ lo) (horder : lo ≤ hi) :
    (∑ i ∈ range (hi-lo+1), finalFlags lo hi i) = segmentCount lo hi := by
  classical
  calc
    (∑ i ∈ range (hi-lo+1), finalFlags lo hi i) =
        ∑ i ∈ range (hi-lo+1), if Nat.Prime (lo+i) then 1 else 0 := by
      apply sum_congr rfl
      intro i hiIndex
      exact final_flag hlo (by have := mem_range.mp hiIndex; omega)
    _ = ∑ n ∈ Icc lo hi, if Nat.Prime n then 1 else 0 := by
      apply sum_bij (fun i _ => lo+i)
      · intro i hiIndex
        have := mem_range.mp hiIndex
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · intro i _ j _ equal
        omega
      · intro n hn
        have hn := mem_Icc.mp hn
        refine ⟨n-lo,mem_range.mpr (by omega),by omega⟩
      · intro i hiIndex
        rfl
    _ = segmentCount lo hi := by simp [segmentCount]

theorem sum_finalFlags_le {lo hi : Nat} (hlo : 2 ≤ lo) (horder : lo ≤ hi) :
    (∑ i ∈ range (hi-lo+1), finalFlags lo hi i) ≤ hi-lo+1 := by
  calc
    (∑ i ∈ range (hi-lo+1), finalFlags lo hi i) ≤
        ∑ _i ∈ range (hi-lo+1), 1 := by
      apply sum_le_sum
      intro i hiIndex
      have h := final_flag_zero_or_one hlo (by have := mem_range.mp hiIndex; omega)
      omega
    _ = hi-lo+1 := by simp

/-- Exact prime count increment returned by the checker once its actual source
has computed this sum. No analytic or prime-table assumption is needed. -/
theorem count_increment {lo hi : Nat} (hlo : 2 ≤ lo) (horder : lo ≤ hi) :
    Nat.primeCounting hi = Nat.primeCounting (lo-1) +
      (∑ i ∈ range (hi-lo+1), finalFlags lo hi i) := by
  rw [sum_finalFlags hlo horder]
  exact primeCounting_increment hlo horder

#print axioms sum_finalFlags
#print axioms count_increment
end RamanujanPV.SegmentCounts
