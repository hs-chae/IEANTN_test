/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootPiFramed
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

theorem scale_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some multiply_small_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids (piData input.old input.layout.workStart 5)) (scope : before.scope=owner) :
    ∃returned after : State F,Exec context before scaleStatement .normal after ∧
      Every context before scaleStatement .normal after ∧
      returned.declare .u64 "status" (some (.integer (integer64 0)))=some after ∧
      ScaleView after input owner returned.nextObject ids (twicePiData input) ∧ after.scope=owner ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.object] := by
  have digits : ∀i < 5,piData input.old input.layout.workStart 5 (input.layout.workStart+i)<base:=by
    intro i hi;rw [piData_processed _ _ _ _ hi];exact piDigit_bound i
  obtain ⟨returned,called,post,frame⟩:=MultiplySmallSource.multiply_small_call_framed context selected before
    input.layout.object input.layout.size input.layout.workStart 5 2 _ h.well h.array
    (by have b:=input.layout.workBound;omega) (by omega) digits (by norm_num [MultiplySmallSource.base])
  rw [twicePi_carry_zero] at called
  have args : Args context before [.variable "work",.literal (.integer 5 "ULL"),.literal (.integer 2 "ULL")]
      [.pointer (wordPointer input.layout.object input.layout.workStart),.integer (integer64 5),.integer (integer64 2)] before := by
    apply Args.ordered (order:=[(0,.variable "work"),(1,.literal (.integer 5 "ULL")),(2,.literal (.integer 2 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object input.layout.workStart)),(1,.integer (integer64 5)),(2,.integer (integer64 2))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.locals.lookup Param.work) (h.locals.read Param.work))
        (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
          (.cons (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl)) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  have returnedView:=h.reframe post frame.environment scope frame.scope frame.well frame.objects
  have zero:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists frame.well .u64 "status" (.integer (integer64 0)) zero
  have init:=declare_storable zero (convert64 0 (by norm_num)) declared
  have params:=ApplicationBirthFrame.locals_declare_old frame.well returnedView.locals
    (by intro v;cases v <;> decide) init
  have array:=ApplicationBirthFrame.array_declare_old frame.well returnedView.array init
  have live:=frame.well.objectIds _ _ returnedView.array.2.1
  have oldIds (v : Param) : ids v<returned.nextObject:=frame.well.objectIds _ _ (returnedView.locals.slots v).object
  have paramSeparate : ∀v,input.layout.object≠ids v:=h.separate
  have statusLookup : after.environment.lookup "status"=some (scalarPointer returned.nextObject .u64):=by simp [init.environment,List.lookup]
  have status : Slot after returned.nextObject owner .u64 (.integer (integer64 0)):=by
    rw [←scope,←frame.scope];exact init.slot
  have mulBirth : ApplicationBirthFrame.Frame before.nextObject before returned [input.layout.object]:=
    ⟨frame.well,frame.nextObject,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
      fun id bound outside=>frame.objects id bound (by simpa using outside)⟩
  have declarationBirth:=ApplicationBirthFrame.declare_frame before.nextObject [input.layout.object]
    frame.well frame.nextObject declared
  have run : Exec context before scaleStatement .normal after:=.declareSome (.call args called) declared
  have unique : CompareSource.Unique context scaleStatement:=ApplicationPureCall.declare_call_unique
    "multiply_small" [.variable "work",.literal (.integer 5 "ULL"),.literal (.integer 2 "ULL")]
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl <;> trivial) .u64 "status" (MultiplySmallSource.returned_call_unique selected)
  exact ⟨returned,after,run,every_of_unique unique run,declared,
    ⟨⟨array,params,paramSeparate,wellScoped_declare frame.well declared⟩,status,statusLookup,by omega⟩,
    init.scope.trans (frame.scope.trans scope),mulBirth.trans declarationBirth⟩


theorem divide_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat}
    (h : ScaleView before input owner statusId ids (twicePiData input)) (scope : before.scope=owner) :
    ∃after,Exec context before divideStatement .normal after ∧
      Every context before divideStatement .normal after ∧
      ScaleView after input owner statusId ids (xData input) ∧ after.scope=owner ∧ IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,called,post,frame⟩:=DivideSource.divide_small_call context selected incrementSelected before
    input.layout.object input.layout.size input.layout.workStart 5 input.n 0 (twicePiData input)
    h.params.well h.params.array (by have b:=input.layout.workBound;omega) (by omega)
    (twicePi_digits input) input.positive input.small (by omega)
  have args : Args context before [.variable "work",.literal (.integer 5 "ULL"),.variable "n",.literal (.integer 0 "ULL")]
      [.pointer (wordPointer input.layout.object input.layout.workStart),.integer (integer64 5),.integer (integer64 input.n),.integer (integer64 0)] before := by
    apply Args.ordered (order:=[(0,.variable "work"),(1,.literal (.integer 5 "ULL")),(2,.variable "n"),(3,.literal (.integer 0 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object input.layout.workStart)),(1,.integer (integer64 5)),(2,.integer (integer64 input.n)),(3,.integer (integer64 0))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.params.locals.lookup Param.work) (h.params.locals.read Param.work))
        (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
          (.cons (.variable (h.params.locals.lookup Param.n) (h.params.locals.read Param.n))
            (.cons (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) .nil)))
    · change List.Forall₂ _ [0,1,2,3] _;exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  have status : Slot after statusId owner .u64 (.integer (integer64 0)):=by
    refine ⟨h.status.storable,?_⟩
    rw [frame.objects _ (h.params.well.objectIds _ _ h.status.object) h.statusSeparate.symm];exact h.status.object
  have everyStep:=every_expression_call (args:=args)
    (callee:=fun state result actual=>DivideSource.returned_call_unique selected incrementSelected called actual)
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl <;> trivial)
  exact ⟨after,.expression (.call args called),everyStep,
    ⟨h.params.reframe post frame.environment scope frame.scope frame.well frame.objects,
      status,by rw [frame.environment];exact h.statusLookup,h.statusSeparate⟩,frame.scope.trans scope,frame⟩

#print axioms scale_framed
#print axioms divide_framed
end RH080Next.FFTPV.RootSource
