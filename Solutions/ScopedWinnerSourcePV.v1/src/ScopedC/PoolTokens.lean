/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatArena
namespace ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0

 def RefsValid (a : NatArena.Arena) (refs : List Nat) : Prop :=
  ∀ i ∈ refs, i < a.values.length

 theorem clear_nil (a : NatArena.Arena) : NatArena.clear a [] = a := by
  cases a
  rfl

 theorem release_clear {a : NatArena.Arena} {rest : List Nat} {slot : Nat}
    (valid : slot < a.values.length) (owned : rest.count slot < a.owners slot) :
    NatArena.release (NatArena.clear a rest) slot = some (NatArena.clear a (slot::rest)) := by
  have hp : 0 < (NatArena.clear a rest).owners slot := by
    simp only [NatArena.clear,NatArena.readCount]
    omega
  have hp' : 0 < a.owners slot - rest.count slot := by omega
  simp only [NatArena.release,NatArena.clear,NatArena.readCount]
  simp only [valid,hp',and_self,↓reduceIte]
  apply congrArg some
  apply congrArg (NatArena.Arena.mk a.values)
  funext i
  change (if i = slot then a.owners i-rest.count i-1 else a.owners i-rest.count i) =
    a.owners i-(slot::rest).count i
  by_cases hi : i = slot
  · subst i
    simp only [↓reduceIte,List.count_cons_self]
    omega
  · have hs : slot ≠ i := Ne.symm hi
    simp [hi,hs]

 theorem release_owned_cons {a : NatArena.Arena} {first : Nat} {rest : List Nat}
    (valid : RefsValid a (first::rest)) (owned : NatArena.PoolOwned a (first::rest)) :
    ∃ after, NatArena.release a first = some after ∧
      NatArena.PoolOwned after rest ∧ RefsValid after rest ∧
      NatArena.clear after rest = NatArena.clear a (first::rest) ∧ after.values = a.values := by
  let after : NatArena.Arena := {a with owners:=fun i => if i = first then a.owners i-1 else a.owners i}
  have hf : first < a.values.length := valid first (by simp)
  have hp : 0 < a.owners first := by
    have h := owned first
    simp only [List.count_cons_self] at h
    omega
  refine ⟨after,?_,?_,?_,?_,rfl⟩
  · simp [NatArena.release,hf,hp,after]
  · intro i
    have h := owned i
    by_cases hi : i = first
    · subst i
      simp only [List.count_cons_self] at h
      dsimp [after]
      simp only [↓reduceIte]
      omega
    · simpa [after,hi,Ne.symm hi] using h
  · intro i hi
    exact valid i (by simp [hi])
  · apply congrArg (NatArena.Arena.mk a.values)
    funext i
    change (if i = first then a.owners i-1 else a.owners i)-rest.count i =
      a.owners i-(first::rest).count i
    by_cases hi : i = first
    · subst i
      simp only [↓reduceIte,List.count_cons_self]
      omega
    · simp [hi,Ne.symm hi]



end ScopedC.PoolCalls
