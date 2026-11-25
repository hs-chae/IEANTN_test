/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualModel
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RH080PV.Model
/-- Every one of the257fixed input points, checked by ordinary kernel reduction. -/
theorem sampleBound_all : ∀ k : Fin 257, sampleBound k.val ≤ 1221161 := by decide

theorem gridMaximum_exact : gridMaximum = 1221161 := by decide

lemma le_foldl_max (xs : List Nat) (initial : Nat) :
    initial ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact (le_max_left initial x).trans (ih (max initial x))

lemma mem_le_foldl_max {x : Nat} (xs : List Nat) (initial : Nat) (member : x∈xs) :
    x ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact (le_max_right initial x).trans (le_foldl_max rest (max initial x))
    · exact ih (max initial first) tail

/-- The max-loop's mathematical specification controls every point without
using its evaluated decimal answer. This is the cap consumed by the source route. -/
theorem sampleBound_le_gridMaximum (k : Fin 257) : sampleBound k.val ≤ gridMaximum := by
  apply mem_le_foldl_max
  apply List.mem_map.mpr
  exact ⟨k.val,List.mem_range.mpr k.isLt,rfl⟩

#print axioms sampleBound_all
#print axioms gridMaximum_exact
#print axioms sampleBound_le_gridMaximum
end RH080PV.Model
