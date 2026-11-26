/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadSmall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem View.multiply_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData)
    (temp : TempValue workData (coefficientAbs input.profile j)) (pinned : context.program=input.profile.program) :
    ∃after memory,Exec context before multiplyStatement .normal after ∧ Every context before multiplyStatement .normal after ∧
      View after input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory memory ∧
      TempValue memory (term input.profile j) ∧ ApplicationBirthFrame.Frame cutoff before after [workObject] ∧
      ∀k,(k<160 ∨ 166≤ k) → memory k=workData k:=by
  have capacity : factor j*FFT.Limbs.magnitude base 5 (fun k=> workData (160+k))< base^5:=by
    rw [temp.magnitude]
    exact lt_of_le_of_lt (term_bound input.profile j h.body.active) (by norm_num [base])
  obtain ⟨after,called,calleeEvery,array,frame,digits,magnitude,outside⟩:=multiply_small_zero context
    (Profile.multiply_small_selected input.profile context pinned) before workObject 512 160 5 (factor j) workData
    h.body.well h.work (by norm_num) (by norm_num) temp.digits (factor_bound input.profile j h.body.active) capacity
  have args : Args context before [.variable "temp",.literal (.integer 5 "ULL"),factorExpression]
      [.pointer (wordPointer workObject 160),.integer (integer64 5),.integer (integer64 (factor j))] before:=by
    apply Args.ordered (order:=[(0,.variable "temp"),(1,.literal (.integer 5 "ULL")),(2,factorExpression)])
      (evaluated:=[(0,.pointer (wordPointer workObject 160)),(1,.integer (integer64 5)),(2,.integer (integer64 (factor j)))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.aux.lookup .temp) (h.aux.read .temp))
        (.cons (.literal _ _ _ (by rfl)) (.cons (h.factor_evaluation context) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  have auxAfter:=generic_locals_after_call h.body.well h.aux frame (by intro a;simpa using (h.auxSeparate a).symm)
  have run : Exec context before multiplyStatement .normal after:=StatusCall.assignment_execution
    (h.aux.lookup .status) (auxAfter.lookup .status) (h.aux.slots .status) (auxAfter.slots .status) args called
  have closed : ∀e∈[Expr.variable "temp",.literal (.integer 5 "ULL"),factorExpression],SourcePure.CallFree e:=by
    intro e he;simp only [List.mem_cons,List.not_mem_nil,or_false] at he;rcases he with rfl|rfl|rfl <;> trivial
  have every : Every context before multiplyStatement .normal after:=by
    intro state flow actual
    exact StatusCall.assignment_every_execution (h.aux.lookup .status) (auxAfter.lookup .status)
      (h.aux.slots .status) (auxAfter.slots .status) closed args calleeEvery actual
  let memory:=MultiplySmallSource.currentData workData 160 (factor j) 5
  have quadSame (k : Nat) (hk : k<6) : memory (208+k)=workData (208+k):=outside _ (by omega)
  have quadValue : FFT.Limbs.magnitude base 6 (fun k=> memory (208+k))=partialQuad input.profile j:=
    (ComplexSource.magnitude_congr memory workData 208 208 6 quadSame).trans (by simpa [base] using h.quadValue)
  have post:=h.after_work_call frame array (fun k hk=> by change memory (208+k)< base;rw [quadSame k hk];exact h.quadDigits k hk) (nextPending:=false) (by simpa using quadValue)
  have sign : memory 165=0:=(outside 165 (by omega)).trans temp.sign
  have mag : FFT.Limbs.magnitude base 5 (fun k=> memory (160+k))=term input.profile j:=by
    exact magnitude.trans (congrArg (fun x=> factor j*x) temp.magnitude)
  exact ⟨after,memory,run,every,post,⟨digits,sign,mag⟩,lower_frame frame.frame h.body.fresh,fun k hk=> outside k (by omega)⟩

#print axioms View.multiply_execution
end RH080Next.FFTPV.QuadSource
