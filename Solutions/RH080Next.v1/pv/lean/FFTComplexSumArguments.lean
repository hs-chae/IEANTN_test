/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexAddInput
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem pointer_parameter_eval {F : Type} (context : Context F) {before : State F}
    {layout : Layout} {data : Nat→Nat} {ids : PVar→Nat} {owner : Nat}
    (params : Locals before pName pType ids owner (pValue (layout.object .output) (layout.start .output)
      (layout.object .a) (layout.start .a) (layout.object .b) (layout.start .b) (layout.object .work) (layout.start .work)))
    (r : PVar) (rep : WordArrayRep before (layout.object r) (layout.length (layout.object r)) data)
    (offset : Nat) (small : offset≤36) (bound : layout.start r+offset<layout.length (layout.object r)) :
    Eval context before (pointerExpr r offset) (.pointer (wordPointer (layout.object r) (layout.start r+offset))) before:=by
  have sourceVar : Eval context before (.variable (pName r)) (.pointer (wordPointer (layout.object r) (layout.start r))) before:=by
    have ev:=Eval.variable (context:=context) (params.lookup r) (params.read r)
    cases r <;> exact ev
  by_cases zero : offset=0
  · subst offset
    simpa [pointerExpr] using sourceVar
  · have added:=slice_pointer_add rep bound
    simpa only [pointerExpr,zero,↓reduceIte] using
      Eval.paren (Eval.binaryLR sourceVar
        (Eval.literal (.integer offset "ULL") before (.integer (integer64 offset)) (by simp [Literal.value,integer64];omega))
        (by simpa only [binary,Option.map_some] using congrArg (Option.map Value.pointer) added))

theorem sum_arguments_closed (part : Fin 2) : ∀e∈addArguments part,SourcePure.CallFree e:=by
  intro e member
  unfold addArguments at member
  split at member <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl|rfl|rfl|rfl
  all_goals first | exact pointer_expression_closed _ _ | trivial

theorem sum_arguments_eval {F : Type} (context : Context F) {before : State F}
    {input : Input} {ids : PVar→Nat} {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView before input ids owner statusId stage workData outData) (part : Fin 2) :
    Args context before (addArguments part) (AddSource.arguments (sumInput h part)) before:=by
  have workBound:=input.layout.bound MultiplyParameters.Var.work
  have outBound:=input.layout.bound MultiplyParameters.Var.output
  simp at workBound outBound
  fin_cases part
  · apply four_arguments
    · exact pointer_parameter_eval context h.params .output h.output 0 (by omega) (by omega)
    · exact pointer_parameter_eval context h.params .work h.work 0 (by omega) (by omega)
    · exact pointer_parameter_eval context h.params .work h.work 6 (by omega) (by omega)
    · exact .literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)
  · apply four_arguments
    · exact pointer_parameter_eval context h.params .output h.output 6 (by omega) (by omega)
    · exact pointer_parameter_eval context h.params .work h.work 12 (by omega) (by omega)
    · exact pointer_parameter_eval context h.params .work h.work 18 (by omega) (by omega)
    · exact .literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)

#print axioms pointer_parameter_eval
#print axioms sum_arguments_eval
end RH080Next.FFTPV.ComplexSource
