/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootFramedMemory
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

theorem param_zero_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) :
    ∃after,Exec context before zeroStatement .normal after ∧
      Every context before zeroStatement .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart 0) ∧ IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,called,rep,frame⟩:=ZeroSlice.zero_words_call_framed context selected before
    input.layout.object input.layout.size input.layout.workStart 80 input.old h.well h.array
    input.layout.workBound (by norm_num)
  have args : Args context before [.variable "work",.literal (.integer 80 "ULL")]
      [.pointer (wordPointer input.layout.object input.layout.workStart),.integer (integer64 80)] before := by
    apply Args.ordered (order:=[(0,.variable "work"),(1,.literal (.integer 80 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object input.layout.workStart)),(1,.integer (integer64 80))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.locals.lookup Param.work) (h.locals.read Param.work))
        (.cons (.literal (.integer 80 "ULL") _ (.integer (integer64 80)) (by rfl)) .nil)
    · change List.Forall₂ _ [0,1] _; exact .cons rfl (.cons rfl .nil)
  have everyStep:=every_expression_call (args:=args)
    (callee:=fun state result actual=>ZeroCallUnique.returned_call_unique selected called actual)
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl <;> trivial)
  exact ⟨after,.expression (.call args called),everyStep,h.reframe rep frame.environment scope frame.scope frame.well frame.objects,
    ⟨⟨frame.environment,frame.scope,frame.foreign,frame.well,frame.objects⟩,frame.nextObject,frame.nextScope,frame.mode⟩⟩


theorem pi_store_framed {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j : Nat} {ids : Param → Nat} (h : ParamView before input owner ids (piData input.old input.layout.workStart j))
    (hj : j<5) :
    ∃after,Exec context before (piStatement j) .normal after ∧
      Every context before (piStatement j) .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart (j+1)) ∧
      IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,run,post,scope⟩:=pi_store_execution context h hj
  have bound : input.layout.workStart+j< input.layout.size:=by have b:=input.layout.workBound;omega
  have literalEval : Eval context before (.literal (.integer (piDigit j) "ULL")) (.integer (integer64 (piDigit j))) before:=
    .literal _ _ _ (by have hv : piDigit j<18446744073709551616:=lt_trans (piDigit_bound j) (by norm_num [base]);simp [Literal.value,integer64,hv])
  have place : Place context before (.index (.variable "work") (.literal (.integer j "ULL")))
      (wordPointer input.layout.object (input.layout.workStart+j)) before:=.index
        (.variable (h.locals.lookup Param.work) (h.locals.read Param.work))
        (.literal _ _ _ (by simp [Literal.value,integer64];omega))
        (slice_pointer_add h.array bound)
  exact ⟨after,run,every_pure (by simp [piStatement,PureDeterminism.Simple,SourcePure.CallFree]) run,post,assignment_full_frame h.well (by trivial) (by trivial) literalEval place rfl run⟩

theorem pi_stores_framed {F : Type} (context : Context F) (j : Nat) (hj : j≤5)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids (piData input.old input.layout.workStart 0)) :
    ∃after,ExecList context before (piStatements j) .normal after ∧
      EveryList context before (piStatements j) .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart j) ∧
      IncrementSource.FullCallerFrame before after input.layout.object := by
  induction j with
  | zero=>exact ⟨before,.nil,every_nil before,h,full_caller_frame rfl rfl (ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _))⟩
  | succ j ih=>
    obtain ⟨middle,run,firstEvery,view,first⟩:=ih (by omega)
    obtain ⟨after,step,stepEvery,post,second⟩:=pi_store_framed context view (by omega)
    have list : piStatements (j+1)=piStatements j++[piStatement j]:=by simp [piStatements,List.range_succ,List.map_append]
    refine ⟨after,?_,?_,post,full_caller_trans first second⟩
    · rw [list];exact append_normal run (.cons step .nil)
    · rw [list];exact every_append firstEvery (every_cons stepEvery (every_nil after))

theorem pi_prefix_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) :
    ∃after,ExecList context before prefixStatements .normal after ∧
      EveryList context before prefixStatements .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart 5) ∧
      IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨middle,zero,zeroEvery,view,first⟩:=param_zero_framed context selected h scope
  obtain ⟨after,run,storesEvery,post,second⟩:=pi_stores_framed context 5 (by omega) view
  exact ⟨after,.cons zero run,every_cons zeroEvery storesEvery,post,full_caller_trans first second⟩

#print axioms pi_prefix_framed
end RH080Next.FFTPV.RootSource
