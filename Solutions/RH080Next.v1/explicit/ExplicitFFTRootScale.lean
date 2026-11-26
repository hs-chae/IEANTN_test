/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootPi
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)
open FFT.Limbs

def twicePiData (input : Input) : Nat → Nat:=MultiplySmallSource.currentData
  (piData input.old input.layout.workStart 5) input.layout.workStart 2 5

def xData (input : Input) : Nat → Nat:=DivideSource.roundedData (twicePiData input) input.layout.workStart 5 input.n 0

def scaleStatement : Stmt:=.declare .u64 "status" (some (.call "multiply_small"
  [.variable "work",.literal (.integer 5 "ULL"),.literal (.integer 2 "ULL")]))

def divideStatement : Stmt:=.expression (.call "divide_small"
  [.variable "work",.literal (.integer 5 "ULL"),.variable "n",.literal (.integer 0 "ULL")])

theorem twicePi_carry_zero (input : Input) :
    (MultiplySmallSource.scaledRow (piData input.old input.layout.workStart 5) input.layout.workStart 2 5).2=0 := by
  have equation:=MultiplySmallSource.currentData_value (piData input.old input.layout.workStart 5) input.layout.workStart 2 5
  have piValue : magnitude MultiplySmallSource.base 5 (fun i=>piData input.old input.layout.workStart 5 (input.layout.workStart+i))=FFT.IntegerModel.piInteger.toNat:=piData_value _ _
  rw [piValue] at equation
  norm_num [MultiplySmallSource.base,FFT.IntegerModel.piInteger] at equation
  omega

theorem twicePi_value (input : Input) :
    magnitude base 5 (fun i=>twicePiData input (input.layout.workStart+i))=2*FFT.IntegerModel.piInteger.toNat := by
  have equation:=MultiplySmallSource.currentData_value (piData input.old input.layout.workStart 5) input.layout.workStart 2 5
  have piValue : magnitude MultiplySmallSource.base 5 (fun i=>piData input.old input.layout.workStart 5 (input.layout.workStart+i))=FFT.IntegerModel.piInteger.toNat:=piData_value _ _
  rw [piValue,twicePi_carry_zero,zero_mul,add_zero] at equation
  exact equation

theorem twicePi_digits (input : Input) : ∀i < 5,twicePiData input (input.layout.workStart+i) < base := by
  intro i hi
  rw [twicePiData,MultiplySmallSource.currentData_slice _ _ _ _ i hi]
  exact MultiplySmallSource.processed_digit_bound _ _ _ _ i hi

theorem xData_value (input : Input) :
    magnitude base 5 (fun i=>xData input (input.layout.workStart+i))=(2*FFT.IntegerModel.piInteger.toNat)/input.n := by
  simpa only [xData,not_lt_zero',ite_false,twicePi_value] using
    DivideSource.roundedData_value (twicePiData input) input.layout.workStart 5 input.n 0 input.positive (twicePi_digits input)

theorem xData_digits (input : Input) : ∀i < 5,xData input (input.layout.workStart+i) < base :=
  DivideSource.roundedData_digits _ _ _ _ _ input.positive (twicePi_digits input)

structure ScaleView {F : Type} (state : State F) (input : Input) (owner statusId : Nat)
    (ids : Param → Nat) (data : Nat → Nat) : Prop where
  params : ParamView state input owner ids data
  status : Slot state statusId owner .u64 (.integer (integer64 0))
  statusLookup : state.environment.lookup "status"=some (scalarPointer statusId .u64)
  statusSeparate : input.layout.object≠statusId

/-- Actual multiply_small call and returned-status declaration. Its result
zero is derived from limb conservation and the original literal pi input. -/
theorem scale_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some multiply_small_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids (piData input.old input.layout.workStart 5)) (scope : before.scope=owner) :
    ∃returned after : State F,Exec context before scaleStatement .normal after ∧
      returned.declare .u64 "status" (some (.integer (integer64 0)))=some after ∧
      ScaleView after input owner returned.nextObject ids (twicePiData input) ∧ after.scope=owner := by
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
  exact ⟨returned,after,.declareSome (.call args called) declared,declared,
    ⟨⟨array,params,paramSeparate,wellScoped_declare frame.well declared⟩,status,statusLookup,by omega⟩,
    init.scope.trans (frame.scope.trans scope)⟩

/-- Actual floor division by the runtime n, preserving the true source status
slot even though the callee allocates its own temporary application objects. -/
theorem divide_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat}
    (h : ScaleView before input owner statusId ids (twicePiData input)) (scope : before.scope=owner) :
    ∃after,Exec context before divideStatement .normal after ∧
      ScaleView after input owner statusId ids (xData input) ∧ after.scope=owner := by
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
  exact ⟨after,.expression (.call args called),
    ⟨h.params.reframe post frame.environment scope frame.scope frame.well frame.objects,
      status,by rw [frame.environment];exact h.statusLookup,h.statusSeparate⟩,frame.scope.trans scope⟩

#print axioms twicePi_carry_zero
#print axioms xData_value
#print axioms scale_execution
#print axioms divide_execution
end RH080Next.FFTPV.RootSource
