/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadMultiply
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem add_conserved (input : AddMagnitudeSource.Input) (sum sample : Nat)
    (zero : (AddMagnitudeSource.row input input.layout.n).2=0)
    (oldValue : FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n
      (fun k=>input.old input.layout.outObject (input.layout.outStart+k))=sum)
    (newValue : FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n (AddMagnitudeSource.aDigit input)=sample) :
    FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n
      (fun k=>AddMagnitudeSource.currentData input input.layout.n (input.layout.outStart+k))=sum+sample:=by
  have conservation:=AddMagnitudeSource.result_conservation input
  rw [zero,Nat.zero_mul,Nat.add_zero,oldValue,newValue] at conservation
  exact conservation

theorem View.add_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData)
    (temp : TempValue workData (term input.profile j)) (pinned : context.program=input.profile.program) :
    ∃after memory,Exec context before addStatement .normal after ∧ Every context before addStatement .normal after ∧
      View after input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory memory true ∧
      ApplicationBirthFrame.Frame cutoff before after [workObject] ∧
      ∀k,(k<208 ∨ 214≤ k) → memory k=workData k:=by
  let actual : AddMagnitudeSource.Input:={
    layout:={
      outObject:=workObject
      aObject:=workObject
      length:=fun _=>512
      outStart:=208
      aStart:=160
      n:=6
      outBound:=by norm_num
      aBound:=by norm_num
      safe:=Or.inr (Or.inr (by norm_num))
      small:=by norm_num}
    old:=fun _=> workData
    outDigits:=h.quadDigits
    aDigits:=temp.digits}
  have im : FFT.Limbs.magnitude AddMagnitudeSource.base 6 (AddMagnitudeSource.aDigit actual)=term input.profile j:=by
    simpa [actual,AddMagnitudeSource.aDigit,FFT.Limbs.magnitude,Finset.sum_range_succ,base,AddMagnitudeSource.base] using temp.magnitude
  have oldValue : FFT.Limbs.magnitude AddMagnitudeSource.base 6 (fun k=> workData (208+k))=partialQuad input.profile j:=by
    simpa [base,AddMagnitudeSource.base] using h.quadValue
  have zero : (AddMagnitudeSource.row actual 6).2=0:=by
    apply AddMagnitudeSource.zero_status_of_small
    change FFT.Limbs.magnitude AddMagnitudeSource.base 6 (fun k=> workData (208+k))+
      FFT.Limbs.magnitude AddMagnitudeSource.base 6 (AddMagnitudeSource.aDigit actual)< AddMagnitudeSource.base^6
    rw [oldValue,im,←partialQuad_succ]
    exact lt_trans (partialQuad_bound input.profile (j+1) (by have a:=h.body.active;omega)) (by norm_num [AddMagnitudeSource.base])
  obtain ⟨⟨after,called,calleeEvery,array,frame⟩,carry,digits,conservation,outside⟩:=
    AddMagnitudeSource.add_magnitude_total context (Profile.add_magnitude_selected input.profile context pinned) before actual h.body.well h.work h.work
  change Call context "add_magnitude" (AddMagnitudeSource.arguments actual) before (.value (.integer (integer64 (AddMagnitudeSource.row actual 6).2))) after at called
  rw [zero] at called
  have everyCall : EveryCall context before "add_magnitude" (AddMagnitudeSource.arguments actual) (.value (.integer (integer64 0))) after:=by
    simpa only [show actual.layout.n=6 from rfl,zero] using calleeEvery
  have args : Args context before [.variable "quad",.variable "temp",.literal (.integer 6 "ULL")] (AddMagnitudeSource.arguments actual) before:=by
    apply Args.ordered (order:=[(0,.variable "quad"),(1,.variable "temp"),(2,.literal (.integer 6 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer workObject 208)),(1,.pointer (wordPointer workObject 160)),(2,.integer (integer64 6))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.aux.lookup .quad) (h.aux.read .quad))
        (.cons (.variable (h.aux.lookup .temp) (h.aux.read .temp)) (.cons (.literal _ _ _ (by rfl)) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  have caller:=unary_caller frame
  have auxAfter:=generic_locals_after_call h.body.well h.aux caller (by intro a;simpa using (h.auxSeparate a).symm)
  have run : Exec context before addStatement .normal after:=StatusCall.assignment_execution
    (h.aux.lookup .status) (auxAfter.lookup .status) (h.aux.slots .status) (auxAfter.slots .status) args called
  have closed : ∀e∈[Expr.variable "quad",.variable "temp",.literal (.integer 6 "ULL")],SourcePure.CallFree e:=by
    intro e he;simp only [List.mem_cons,List.not_mem_nil,or_false] at he;rcases he with rfl|rfl|rfl <;> trivial
  have every : Every context before addStatement .normal after:=by
    intro state flow actualRun
    exact StatusCall.assignment_every_execution (h.aux.lookup .status) (auxAfter.lookup .status)
      (h.aux.slots .status) (auxAfter.slots .status) closed args everyCall actualRun
  let memory:=AddMagnitudeSource.currentData actual 6
  have value : FFT.Limbs.magnitude base 6 (fun k=>memory (208+k))=partialQuad input.profile j+term input.profile j:=
    add_conserved actual _ _ zero oldValue im
  have post:=h.after_work_call caller array digits (nextPending:=true) (by simpa using value)
  exact ⟨after,memory,run,every,post,lower_frame caller.frame h.body.fresh,outside⟩

#print axioms View.add_execution
end RH080Next.FFTPV.QuadSource
