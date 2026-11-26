/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffinePositiveCellArea
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.ScalarPositiveArea
open RH080Next.Explicit RH080Next.Primal

def qPositiveChordArea (a b : ℚ) : ℚ :=
  if 0≤a then (if 0≤b then (a+b)/2 else a^2/(2*(a-b)))
  else (if 0≤b then b^2/(2*(b-a)) else 0)

def qPositiveArea (nodes : List ℚ) (m : ℕ) : ℚ :=
  (2/(m:ℚ))*∑ j ∈ Finset.Ico m (nodes.length-1),
    qPositiveChordArea (nodes.getD j 0) (nodes.getD (j+1) 0)

theorem qPositiveChordArea_cast (a b : ℚ) :
    (qPositiveChordArea a b : ℝ)=positiveChordArea (a:ℝ) (b:ℝ) := by
  unfold qPositiveChordArea positiveChordArea
  simp only [Rat.cast_nonneg]
  split_ifs <;> push_cast <;> rfl

theorem qPositiveArea_cast (nodes : List ℚ) (m : ℕ) :
    (qPositiveArea nodes m : ℝ)=nodalPositiveArea nodes m := by
  unfold qPositiveArea nodalPositiveArea
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact qPositiveChordArea_cast _ _

#print axioms qPositiveChordArea_cast
#print axioms qPositiveArea_cast
end RH080Next.ScalarPositiveArea
