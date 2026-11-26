/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTInitialization
import FFTAST
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV
open GoldbachDirect GoldbachDirect.Semantics WordArrays

def zeroStoreStmt : Stmt :=
  .assign (.index (.variable "a") (.variable "j")) (.literal (.integer 0 "ULL"))

theorem zero_words_actual_body : zero_words_ast.body = .block [
    .declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
    .whileLoop (.binary .lt (.variable "j") (.variable "n")) (.block [zeroStoreStmt,
      .assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))]),
    .returnValue (some (.literal (.integer 0 "ULL")))] := by rfl

theorem zero_array_pointer_add {F : Type} {state : State F} {object length filled : Nat}
    (mode : state.mode=.host) (present : state.objects object=some (zeroPrefixObject length filled))
    (hi : filled<length) :
    state.pointerAdd (wordPointer object 0) (integer64 filled).toInt =
      some (wordPointer object filled) := by
  have he : 8*filled≤8*length := by omega
  simp [State.pointerAdd,wordPointer,CType.byteSize,integer64_toInt,
    State.pointerValid,present,State.accessible,mode,zeroPrefixObject,he,Nat.mul_comm]
  constructor <;> omega

/-- The actual first source statement inside zero_words is proved using the
existing full Goldbach C lvalue/load/store operational rules. The caller must
establish its real parameter/local bindings; they are not platform assumptions. -/
theorem zero_source_assignment {F : Type} {context : Context F} {state : State F}
    {object length filled : Nat} {aCell jCell : Pointer}
    (mode : state.mode=.host) (present : state.objects object=some (zeroPrefixObject length filled))
    (hi : filled<length)
    (aNamed : state.environment.lookup "a"=some aCell)
    (aRead : state.load aCell=some (.pointer (wordPointer object 0)))
    (jNamed : state.environment.lookup "j"=some jCell)
    (jRead : state.load jCell=some (.integer (integer64 filled))) :
    Exec context state zeroStoreStmt .normal
      {state with objects := fun key => if key=object then some (zeroPrefixObject length (filled+1)) else state.objects key} := by
  apply Exec.assign
    (Eval.literal (.integer 0 "ULL") state (.integer (integer64 0)) (by rfl))
    (Place.index (Eval.variable aNamed aRead) (Eval.variable jNamed jRead)
      (zero_array_pointer_add mode present hi))
  exact zeroPrefix_store mode present hi

#print axioms zero_words_actual_body
#print axioms zero_source_assignment
end RH080Next.FFTPV
