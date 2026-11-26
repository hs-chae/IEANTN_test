/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCallParameters
import FFTWordSlices
import FFTWordArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def leafCondition : Expr := .binary .eq (.variable "n") (.literal (.integer 1 "ULL"))
def indexedPointer (array index : String) : Expr :=
  .paren (.binary .add (.variable array)
    (.paren (.binary .mul (.variable index) (.literal (.integer 12 "ULL")))))
def leafArguments : List Expr :=
  [indexedPointer "output" "start",indexedPointer "input" "index",.literal (.integer 12 "ULL")]
def leafCopy : Stmt := .expression (.call "copy_words" leafArguments)
def zeroReturn : Stmt := .returnValue (some (.literal (.integer 0 "ULL")))
def leafBranch : Stmt := .ite leafCondition (.block [leafCopy,zeroReturn]) none

def functionStatements : List Stmt :=
  match FFTRecursivePV.fft_recursive_ast.body with
  | .block body => body
  | _ => []

theorem actual_body : FFTRecursivePV.fft_recursive_ast.body = .block functionStatements := by rfl
theorem actual_leaf_head : functionStatements = leafBranch :: functionStatements.tail := by rfl

/-- Exact typed multiplication and pointer arithmetic of the actual leaf source.
All integer/pointer guards are established from the caller's real array. -/
theorem indexed_pointer_eval {F : Type} (context : Context F) {before : State F}
    {array index : String} {object size k : Nat} {data : Nat → Nat}
    (pointer : Eval context before (.variable array) (.pointer (wordPointer object 0)) before)
    (scalar : Eval context before (.variable index) (.integer (integer64 k)) before)
    (rep : WordArrayRep before object size data)
    (fit : k < 2^64) (productFit : k*12 < 2^64) (bound : k*12 < size) :
    Eval context before (indexedPointer array index) (.pointer (wordPointer object (k*12))) before := by
  have multiplied : Eval context before
      (.paren (.binary .mul (.variable index) (.literal (.integer 12 "ULL"))))
      (.integer (integer64 (k*12))) before := by
    apply Eval.paren
    refine .binaryLR scalar (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl)) ?_
    simpa only [binary,Option.map_some] using
      congrArg (Option.map Value.integer) (binary64_mul k 12 fit (by norm_num) productFit)
  apply Eval.paren
  refine .binaryLR pointer multiplied ?_
  have added := slice_pointer_add (start:=0) (i:=k*12) rep (by omega)
  simpa only [binary,Option.map_some,Nat.zero_add] using
    congrArg (Option.map Value.pointer) added

theorem leaf_arguments_eval {F : Type} (context : Context F) {before : State F}
    {outObj outSize inObj inSize twiddleObj workObj start index step total owner : Nat} {ids : Var → Nat}
    {outData inData : Nat → Nat}
    (params : Locals before name type ids owner (value outObj inObj twiddleObj workObj start index step 1 total))
    (output : WordArrayRep before outObj outSize outData)
    (input : WordArrayRep before inObj inSize inData)
    (startFit : start < 2^64) (indexFit : index < 2^64)
    (outFit : start*12 < 2^64) (inFit : index*12 < 2^64)
    (outBound : start*12 < outSize) (inBound : index*12 < inSize) :
    Args context before leafArguments
      [.pointer (wordPointer outObj (start*12)),.pointer (wordPointer inObj (index*12)),
        .integer (integer64 12)] before := by
  have outE := indexed_pointer_eval context
    (Eval.variable (params.lookup .output) (params.read .output))
    (Eval.variable (params.lookup .start) (params.read .start)) output startFit outFit outBound
  have inE := indexed_pointer_eval context
    (Eval.variable (params.lookup .input) (params.read .input))
    (Eval.variable (params.lookup .index) (params.read .index)) input indexFit inFit inBound
  refine .ordered (List.Perm.refl _) (.cons outE (.cons inE
    (.cons (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl)) .nil))) ?_
  exact .cons rfl (.cons rfl (.cons rfl .nil))

#print axioms actual_leaf_head
#print axioms leaf_arguments_eval
end RH080Next.FFTPV.RecursiveSource
