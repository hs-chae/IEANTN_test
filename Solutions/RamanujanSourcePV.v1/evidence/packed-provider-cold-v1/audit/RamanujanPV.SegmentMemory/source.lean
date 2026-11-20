/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCExecute

namespace RamanujanPV.SegmentMemory
open QuotientCMachine QuotientCExecute
set_option autoImplicit false

/-- Actual checked zero-based uint64 array reads. No mathematical
prime/composite meaning is assumed by this memory representation. -/
def FlagsRep (heap : Heap) (base length : Nat) (flags : Nat → Nat) : Prop :=
  ∀ i, i < length → QuotientCMachine.read heap base i = some (.u64 (flags i))

theorem write_flag {heap : Heap} {base length i value : Nat} {flags : Nat → Nat}
    (owned : Owned heap) (rep : FlagsRep heap base length flags)
    (hi : i < length) (hvalue : value < modulus) :
    ∃ after, write heap base i value = some after ∧ Owned after ∧
      FlagsRep after base length (Function.update flags i value) ∧ SameShape heap after ∧
      (∀ other j, other ≠ base → QuotientCMachine.read after other j = QuotientCMachine.read heap other j) := by
  obtain ⟨block,hblock,halign,hindex,haddress,hword,hold⟩ := read_some_details (rep i hi)
  obtain ⟨after,written,same,shape,other,index⟩ :=
    write_frame_from_block hblock halign hindex haddress hvalue
  refine ⟨after,written,write_preserves_owned owned written,?_,shape,other⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa using same
  · rw [Function.update_of_ne hji,index j hji]
    exact rep j hj

theorem representation_ext {heap : Heap} {base length : Nat} {a b : Nat → Nat}
    (rep : FlagsRep heap base length a) (same : ∀i,i<length→a i=b i) :
    FlagsRep heap base length b := by
  intro i hi
  rw [←same i hi]
  exact rep i hi

#print axioms write_flag
end RamanujanPV.SegmentMemory
