/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

def fapScaleStatement : Stmt:=StatusCall.statement "multiply_small"
  [.variable "quad",.literal (.integer 6 "ULL"),.literal (.integer 100 "ULL")]

theorem actual_fap_scale : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[35]?=some fapScaleStatement:=rfl

theorem fap_scale_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo input.profile.count paramIds auxIds dataMemory workData)
    (pinned : context.program=input.profile.program) :
    ∃after memory,Exec context before fapScaleStatement .normal after ∧ Every context before fapScaleStatement .normal after ∧
      WordArrayRep after input.object (12*input.profile.grid) dataMemory ∧ WordArrayRep after workObject 512 memory ∧
      Locals after parameterName parameterType paramIds fo (parameterValues input input.profile.count) ∧
      Locals after auxName auxType auxIds fo (auxValues workObject) ∧ MultiplyCall.CallerFrame before after [workObject] ∧
      (∀k<6,memory (208+k)< base) ∧ FFT.Limbs.magnitude base 6 (fun k=> memory (208+k))=100*partialQuad input.profile input.profile.count ∧
      ∀k,(k<208 ∨ 214≤ k) → memory k=workData k:=by
  have capacity : 100*FFT.Limbs.magnitude base 6 (fun k=> workData (208+k))< base^6:=by
    rw [h.quadValue]
    have small:=partialQuad_bound input.profile input.profile.count (le_refl _)
    norm_num [base] at small ⊢
    omega
  obtain ⟨after,called,calleeEvery,array,frame,digits,magnitude,outside⟩:=multiply_small_zero context
    (Profile.multiply_small_selected input.profile context pinned) before workObject 512 208 6 100 workData
    h.well h.work (by norm_num) (by norm_num) h.quadDigits (by norm_num [base]) capacity
  have parameters:=generic_locals_after_call h.well h.parameters frame (by intro p;simpa using (h.workSeparate p).symm)
  have aux:=generic_locals_after_call h.well h.aux frame (by intro a;simpa using (h.auxSeparate a).symm)
  have data:=ComplexSource.word_array_after_call h.well h.array frame (by simpa using h.different)
  have args : Args context before [.variable "quad",.literal (.integer 6 "ULL"),.literal (.integer 100 "ULL")]
      [.pointer (wordPointer workObject 208),.integer (integer64 6),.integer (integer64 100)] before:=by
    apply Args.ordered (order:=[(0,.variable "quad"),(1,.literal (.integer 6 "ULL")),(2,.literal (.integer 100 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer workObject 208)),(1,.integer (integer64 6)),(2,.integer (integer64 100))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.aux.lookup .quad) (h.aux.read .quad)) (.cons (.literal _ _ _ (by rfl)) (.cons (.literal _ _ _ (by rfl)) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  have run : Exec context before fapScaleStatement .normal after:=StatusCall.assignment_execution
    (h.aux.lookup .status) (aux.lookup .status) (h.aux.slots .status) (aux.slots .status) args called
  have closed : ∀e∈[Expr.variable "quad",.literal (.integer 6 "ULL"),.literal (.integer 100 "ULL")],SourcePure.CallFree e:=by
    intro e he;simp only [List.mem_cons,List.not_mem_nil,or_false] at he;rcases he with rfl|rfl|rfl <;> trivial
  have every : Every context before fapScaleStatement .normal after:=by
    intro state flow actual
    exact StatusCall.assignment_every_execution (h.aux.lookup .status) (aux.lookup .status)
      (h.aux.slots .status) (aux.slots .status) closed args calleeEvery actual
  exact ⟨after,_,run,every,data,array,parameters,aux,frame,digits,magnitude.trans (congrArg (fun n=>100*n) h.quadValue),outside⟩

#print axioms fap_scale_execution
end RH080Next.FFTPV.QuadSource
