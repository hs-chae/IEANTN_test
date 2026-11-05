/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.Kernel
import PVRamanujan.Family

/-!
# Kernel route for a Ramanujan-budget instance

`budgetCheck` without parsing: an instance states its decoded literals once (one native fact,
`PVCore.decode`), the kernel checks `budgetFrom` on them, and `budgetCheck_of_decode` returns the
ordinary certificate, so `budget_of_check` applies unchanged.
-/

namespace PVRamanujan

open PVCore

/-- `budgetCheck` on given decoded literals. -/
def budgetFrom (src : String) (p : Program) (m M A Y eps bound : ℚ) (xs : List ℚ) (scale : ℚ)
    (ops : List (Sign × ℚ)) : Bool :=
  match valuesFrom xs scale ops with
  | none => false
  | some v =>
    checkWith src p eps v && decide (v.ops = [(.minus, 134), (.minus, max 0 m)]) &&
      decide ((termsQ m M A Y).sum ≤ v.scale * v.xs.sum) && decide (0 ≤ M) && decide (0 < Y) &&
      decide (v.out + forwardError v.scale v.s eps v.xs.length ≤ bound)

theorem budgetCheck_of_decode {src : String} {p : Program} {m M A Y eps bound : ℚ} {xs : List ℚ}
    {scale : ℚ} {ops : List (Sign × ℚ)} (hd : decode p = some (xs, scale, ops))
    (hk : budgetFrom src p m M A Y eps bound xs scale ops = true) :
    budgetCheck src p m M A Y eps bound = true := by
  unfold budgetFrom at hk
  split at hk
  · contradiction
  rename_i v hv
  have hvo := valuesOf_of_decode hd hv
  have hc : check src p eps = true := by
    apply check_of_decode hd
    unfold checkFrom
    rw [hv]
    simp only [Bool.and_eq_true] at hk
    exact hk.1.1.1.1.1
  unfold budgetCheck
  rw [hvo, hc]
  simp only [Bool.and_eq_true] at hk
  simp only [Bool.true_and, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hk.1.1.1.1.2, hk.1.1.1.2⟩, hk.1.1.2⟩, hk.1.2⟩, hk.2⟩

end PVRamanujan
