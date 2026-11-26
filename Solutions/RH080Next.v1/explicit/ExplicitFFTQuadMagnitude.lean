/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadReframe
import FFTComplexModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

structure TempValue (memory : Nat → Nat) (value : Nat) : Prop where
  digits : ∀k<5,memory (160+k)<base
  sign : memory 165=0
  magnitude : FFT.Limbs.magnitude base 5 (fun k=>memory (160+k))=value

theorem View.magnitude_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData)
    (pinned : context.program=input.profile.program) :
    ∃after memory,Exec context before magnitudeStatement .normal after ∧ Every context before magnitudeStatement .normal after ∧
      View after input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory memory ∧
      TempValue memory (coefficientAbs input.profile j) ∧ ApplicationBirthFrame.Frame cutoff before after [workObject] ∧
      ∀k,(k<160 ∨ 166≤k) → memory k=workData k:=by
  let actual : MagnitudeIntoSource.Input:=⟨workObject,512,160,workData,coefficientAbs input.profile j,by norm_num,
    lt_of_le_of_lt (coefficientAbs_bound input.profile j h.body.active) (by norm_num [MagnitudeIntoSource.base])⟩
  obtain ⟨⟨after,called,calleeEvery,array,frame⟩,digits,sign,magnitude,outside⟩:=
    MagnitudeIntoSource.magnitude_into_total context (Profile.magnitude_selected input.profile context pinned)
      (Profile.zero_selected input.profile context pinned) before actual h.body.well h.work
  have temp : Eval context before (.variable "temp") (.pointer (wordPointer workObject 160)) before:=
    .variable (h.aux.lookup .temp) (h.aux.read .temp)
  have value : Eval context before (.variable "value") (.integer (integer64 (coefficientAbs input.profile j))) before:=by
    simpa [absoluteValues,varName,temporaryName] using h.body.variable context .value (by norm_num [Active,localIndex])
  have args : Args context before [.variable "temp",.variable "value"] (MagnitudeIntoSource.arguments actual) before:=by
    apply Args.ordered (order:=[(0,.variable "temp"),(1,.variable "value")])
      (evaluated:=[(0,.pointer (wordPointer workObject 160)),(1,.integer (integer64 (coefficientAbs input.profile j)))])
    · exact List.Perm.refl _
    · exact .cons temp (.cons value .nil)
    · change List.Forall₂ _ [0,1] _;exact .cons rfl (.cons rfl .nil)
  have run : Exec context before magnitudeStatement .normal after:=.expression (.call args called)
  have every:=every_expression_call (by intro e he;simp only [List.mem_cons,List.not_mem_nil,or_false] at he;rcases he with rfl|rfl <;> trivial) args calleeEvery
  have quadSame (k : Nat) (hk : k<6) : MagnitudeIntoSource.finalData actual (208+k)=workData (208+k):=outside _ (by change 208+k<160 ∨ 166≤208+k;omega)
  have quadValue : FFT.Limbs.magnitude base 6 (fun k=>MagnitudeIntoSource.finalData actual (208+k))=partialQuad input.profile j:=by
    have same:=ComplexSource.magnitude_congr _ workData 208 208 6 quadSame
    exact same.trans (by simpa [base] using h.quadValue)
  have post:=h.after_work_call (unary_caller frame) array (fun k hk=>by rw [quadSame k hk];exact h.quadDigits k hk) (nextPending:=false) (by simpa using quadValue)
  exact ⟨after,_,run,every,post,⟨fun k hk=>digits k (by omega),sign,magnitude⟩,
    lower_frame (unary_frame frame) h.body.fresh,outside⟩

#print axioms View.magnitude_execution
end RH080Next.FFTPV.QuadSource
