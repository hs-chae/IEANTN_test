/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolClearMemory
namespace ScopedC.PoolCalls
open ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem owned_cons_of_spare {a : NatArena.Arena} {refs : List Nat} {slot : Nat}
    (owned : NatArena.PoolOwned a refs) (spare : refs.count slot < a.owners slot) :
    NatArena.PoolOwned a (slot::refs) := by
  intro i
  by_cases hi : i = slot
  · subst i
    simp only [List.count_cons_self]
    omega
  · simpa [hi,Ne.symm hi] using owned i

 theorem valid_cons_of_borrow {a : NatArena.Arena} {refs : List Nat} {slot value : Nat}
    (valid : RefsValid a refs) (borrow : NatArena.Borrow a slot value) :
    RefsValid a (slot::refs) := by
  intro i hi
  rcases List.mem_cons.mp hi with h | h
  · subst i
    exact (List.getElem?_eq_some_iff.mp borrow.1).choose
  · exact valid i h

 theorem entries_keep {cells : List (Option Value)} {refs : List Nat} {slot : Nat}
    (entries : PoolEntries cells refs) (extent : refs.length < cells.length) :
    PoolEntries (cells.set refs.length (some (.natObject slot))) (slot::refs) := by
  intro i hi
  simp only [List.length_cons] at hi
  by_cases hn : i < refs.length
  · have hi' : refs.length ≠ i := by omega
    have he := entries i hn
    rw [List.getElem?_set_ne hi',List.reverse_cons,
      List.getElem?_append_left (by simpa using hn)]
    exact he
  · have heq : i = refs.length := by omega
    subst i
    simp [List.getElem?_set_self extent,List.reverse_cons,List.getElem?_append]

end ScopedC.PoolCalls
