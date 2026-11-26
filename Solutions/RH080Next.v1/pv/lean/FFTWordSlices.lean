/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordStore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

/-- Actual source pointer arithmetic at an arbitrary word-slice offset. -/
theorem slice_pointer_add {F : Type} {state : State F} {object size start i : Nat}
    {data : Nat → Nat} (h : WordArrayRep state object size data) (hi : start+i < size) :
    state.pointerAdd (wordPointer object start) (integer64 i).toInt=
      some (wordPointer object (start+i)) := by
  rcases h with ⟨host,present,fit⟩
  simp [State.pointerAdd,wordPointer,CType.byteSize,integer64_toInt,
    State.pointerValid,present,State.accessible,host,wordObject,Nat.mul_comm]
  constructor <;> omega

theorem slice_word_load {F : Type} {state : State F} {object size start i : Nat}
    {data : Nat → Nat} (h : WordArrayRep state object size data) (hi : start+i < size) :
    state.load (wordPointer object (start+i))=
      some (.integer (integer64 (data (start+i)))) := word_load h hi

theorem word_data_unique {F : Type} {state : State F} {object size : Nat}
    {a b : Nat → Nat} (ha : WordArrayRep state object size a)
    (hb : WordArrayRep state object size b) (i : Nat) (hi : i < size) : a i=b i := by
  have h := (word_load ha hi).symm.trans (word_load hb hi)
  simpa [integer64] using h

/-- The actual store rule produces a typed full-array update and preserves
all values outside that single word, even within the same allocation. -/
theorem word_store_with_rep {F : Type} {state : State F}
    {object size index value : Nat} {data : Nat → Nat}
    (h : WordArrayRep state object size data) (hi : index < size) (hv : value < 2^64) :
    ∃after,state.store (wordPointer object index) (.integer (integer64 value))=some after ∧
      WordArrayRep after object size (Function.update data index value) := by
  let after : State F := {state with objects := fun key => if key = object then some (wordObject size (Function.update data index value)) else state.objects key}
  refine ⟨after,word_store h hi hv,h.1,by simp [after],?_⟩
  intro i hi
  by_cases he : i=index
  · subst i; simpa using hv
  · simpa [Function.update_of_ne he] using h.2.2 i hi

/-- A disjoint source slice remains readable after a typed word update in the
same object. No entire-object separation is required. -/
theorem updated_slice_load {F : Type} {state : State F} {object size index value start length : Nat}
    {data : Nat → Nat} (h : WordArrayRep state object size (Function.update data index value))
    (hb : start+length ≤ size) (hd : ∀ i,i < length → start+i≠index) :
    ∀ i,i < length → state.load (wordPointer object (start+i))=
      some (.integer (integer64 (data (start+i)))) := by
  intro i hi
  have hload := word_load h (show start+i < size by omega)
  simpa only [Function.update_of_ne (hd i hi)] using hload

#print axioms slice_pointer_add
#print axioms slice_word_load
#print axioms word_data_unique
#print axioms word_store_with_rep
#print axioms updated_slice_load
end RH080Next.FFTPV.WordArrays
