/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumInput
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem arguments_eval {F : Type} (context : Context F) {before : State F}
    {outputObject workObject n owner i : Nat} {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View before outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    Args context before arguments [.pointer (wordPointer workObject 192),.pointer (wordPointer outputObject (i*12)),.integer (integer64 6)] before := by
  have hi : i<2^64:=by have b:=h.nbound;omega
  have hm : i*12<2^64:=by have b:=h.nbound;omega
  have offset : Eval context before (.paren (.binary .mul (.variable "i") (.literal (.integer 12 "ULL"))))
      (.integer (integer64 (i*12))) before :=
    .paren (.binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
      (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
      (by simp only [values,binary,binary64_mul i 12 hi (by norm_num) hm,Option.map_some]))
  have pointer : Eval context before (arguments[1]'(by decide)) (.pointer (wordPointer outputObject (i*12))) before :=
    .paren (.binaryLR (.variable (h.locals.lookup Var.output) (h.locals.read Var.output)) offset
      (by simpa only [binary,values,Nat.zero_add,Option.map_some] using
        congrArg (Option.map Value.pointer) (slice_pointer_add h.output (start:=0) (i:=i*12) (by omega))))
  refine .ordered (List.Perm.refl _) (.cons (.variable (h.locals.lookup Var.total) (h.locals.read Var.total))
    (.cons pointer (.cons (.literal (.integer 6 "ULL") _ (.integer (integer64 6)) (by rfl)) .nil))) ?_
  exact .cons rfl (.cons rfl (.cons rfl .nil))

theorem call_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "add_magnitude"=some add_magnitude_ast)
    {before : State F} {outputObject workObject n owner i : Nat}
    {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View before outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    ∃after nextWork,Exec context before callStmt .normal after ∧
      View after outputObject workObject n ids owner i outputData nextWork samples true ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      (∀k,(k<192 ∨ 198≤k) → nextWork k=workData k) ∧
      (∀other flow,Exec context before callStmt flow other → flow=.normal ∧ other=after) := by
  let actualInput:=input h inside
  have arrays:=input_arrays h inside
  obtain ⟨⟨after,called,every,workRep,fullFrame⟩,carry,digits,conservation,outside⟩:=
    AddMagnitudeSource.add_magnitude_total context selected before actualInput h.well arrays.1 arrays.2
  have zero : (AddMagnitudeSource.row actualInput actualInput.layout.n).2=0:=input_status_zero h inside
  rw [zero] at called every conservation
  have frame:=ComplexSource.add_caller_frame fullFrame
  have frame' : MultiplyCall.CallerFrame before after [workObject]:=by simpa [actualInput,input] using frame
  have params : Locals after name type ids owner (values outputObject workObject n i) := by
    refine ⟨?_,?_,h.locals.distinct,h.locals.bound.trans_le frame'.frame.nextScope⟩
    · intro v;rw [frame'.environment];exact h.locals.lookup v
    · intro v;exact ComplexSource.slot_after_call h.well (h.locals.slots v) frame' (by simpa using (h.separate v).2.symm)
  have originalOutput : WordArrayRep after outputObject (n*12) outputData:=
    ComplexSource.word_array_after_call h.well h.output frame' (by simpa using h.different)
  let nextWork:=AddMagnitudeSource.currentData actualInput actualInput.layout.n
  have totalValue : FFT.Limbs.magnitude 1000000000 6 (fun d=>nextWork (192+d))=partialSum samples i+(samples i).1.natAbs := by
    have oldValue : FFT.Limbs.magnitude AddMagnitudeSource.base actualInput.layout.n
        (fun d=>actualInput.old actualInput.layout.outObject (actualInput.layout.outStart+d))=partialSum samples i := by
      simpa only [actualInput,input,dataAt,ite_true,AddMagnitudeSource.base,Bool.false_eq_true,ite_false,Nat.add_zero] using h.totalValue
    exact conserved_total actualInput _ _ zero oldValue (input_magnitude h inside)
  have post : View after outputObject workObject n ids owner i outputData nextWork samples true := by
    refine ⟨params,originalOutput,?_,h.different,h.separate,h.nbound,h.active,h.outputDigits,h.outputValues,h.outputSmall,?_,?_,frame'.frame.well⟩
    · simpa [nextWork,actualInput,input,extent] using workRep
    · simpa [nextWork,actualInput,input,AddMagnitudeSource.base] using digits
    · simpa using totalValue
  have actualArgs:=arguments_eval context h inside
  have namedArgs : AddMagnitudeSource.arguments actualInput=
      [.pointer (wordPointer workObject 192),.pointer (wordPointer outputObject (i*12)),.integer (integer64 6)] := by rfl
  have call' : Call context "add_magnitude" [.pointer (wordPointer workObject 192),.pointer (wordPointer outputObject (i*12)),.integer (integer64 6)] before
    (.value (.integer (integer64 0))) after := namedArgs ▸ called
  have statusSlot : Slot before (ids Var.status) owner .u64 (.integer (integer64 0)):=h.locals.slots Var.status
  have afterSlot : Slot after (ids Var.status) owner .u64 (.integer (integer64 0)):=params.slots Var.status
  have assignment : Exec context before callStmt .normal after:=
    StatusCall.assignment_execution (h.locals.lookup Var.status) (params.lookup Var.status) statusSlot afterSlot actualArgs call'
  refine ⟨after,nextWork,assignment,post,frame',by simpa [nextWork,actualInput,input,dataAt] using outside,?_⟩
  intro other flow run
  apply StatusCall.assignment_every_execution (h.locals.lookup Var.status) (params.lookup Var.status) statusSlot afterSlot
    (by intro e member;simp only [arguments,List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl|rfl <;> trivial)
    actualArgs ?_ run
  intro other result called'
  exact every other result (namedArgs.symm ▸ called')

#print axioms arguments_eval
#print axioms call_execution
end RH080Next.FFTPV.OutputSumSource
