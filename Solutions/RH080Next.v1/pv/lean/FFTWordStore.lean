/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArrays
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

theorem word_store {F : Type} {state : State F} {object length index value : Nat}
    {data : Nat → Nat} (rep : WordArrayRep state object length data) (hi : index<length)
    (hv : value<2^64) :
    state.store (wordPointer object index) (.integer (integer64 value)) =
      some {state with objects := fun key => if key=object then some (wordObject length (Function.update data index value)) else state.objects key} := by
  rcases rep with ⟨mode,present,fit⟩
  have hbytes : 8*index+8≤8*length := by omega
  simp [State.store,wordPointer,present,CType.byteSize,State.accessible,wordObject,
    mode,hbytes,convert64 value hv]
  funext key
  split_ifs with same
  · congr 1
    congr 1
    funext offset
    by_cases hat : offset=8*index
    · subst offset
      simp [hi]
    · by_cases halign : offset%8=0 ∧offset/8<length
      · have hdiv := Nat.mod_add_div offset 8
        have hoff : offset/8≠index := by
          intro heq
          omega
        have hseparate : ¬(offset<8*index+8 ∧8*index<offset+8) := by omega
        simp [hat,wordObject,halign,Function.update_of_ne hoff,Option.filter,integer64,hseparate]
        intro h
        have hh := of_decide_eq_true h
        omega
      · simp [hat,wordObject,halign,Option.filter]
  · rfl

#print axioms word_store
end RH080Next.FFTPV.WordArrays
