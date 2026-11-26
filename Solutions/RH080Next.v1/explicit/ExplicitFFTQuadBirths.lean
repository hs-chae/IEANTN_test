/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadLoopView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem generic_locals_after_call {F I : Type} {before after : State F} {writes : List Nat}
    {names : I → String} {types : I → CType} {ids : I → Nat} {fo : Nat} {values : I → Value}
    (well : WellScoped before) (locals : Locals before names types ids fo values)
    (frame : MultiplyCall.CallerFrame before after writes) (outside : ∀v,ids v∉writes) :
    Locals after names types ids fo values:=
  ⟨by rw [frame.environment];exact locals.lookup,
    fun v=> ComplexSource.slot_after_call well (locals.slots v) frame (outside v),locals.distinct,
    locals.bound.trans_le frame.frame.nextScope⟩

theorem View.pure_birth {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo count j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {values : InputLoader.Var → Value} {dataMemory workData : Nat → Nat} {pending : Bool} {next : Temporary} {expression : Expr}
    (h : View before input workObject fo bo count j cutoff ids auxIds values dataMemory workData pending) (index : localIndex next=count)
    (storable : Storable (varType (.inr next)) (values (.inr next)))
    (evaluated : Eval context before expression (values (.inr next)) before) (pure : SourcePure.CallFree expression) :
    ∃after,Exec context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after ∧
      Every context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after ∧
      View after input workObject fo bo (count+1) j cutoff (Function.update ids (.inr next) before.nextObject) auxIds values dataMemory workData pending ∧
      ApplicationBirthFrame.Frame cutoff before after []:=by
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists h.body.well _ _ _ storable
  have d:=declare_storable storable storable.converted declared
  have run : Exec context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after:=.declareSome evaluated declared
  have aux:=ApplicationBirthFrame.locals_declare_old h.body.well h.aux (by intro a;cases a <;> cases next <;> decide) d
  have work:=ApplicationBirthFrame.array_declare_old h.body.well h.work d
  have live:=h.body.well.objectIds _ _ h.work.2.1
  have body:=h.body.declare_next index d declared
  have separate : ∀v,Active (count+1) v → workObject≠(Function.update ids (.inr next) before.nextObject) v:=by
    intro v hv
    by_cases same : v=.inr next
    · subst v;rw [Function.update_self];omega
    · rw [Function.update_of_ne same]
      exact h.workSeparate v (((active_step index v).mp hv).resolve_left same)
  have cross : ∀p a,(Function.update ids (.inr next) before.nextObject) (.inl p)≠auxIds a:=by
    intro p a
    rw [Function.update_of_ne (show Sum.inl p≠Sum.inr next from by intro e;cases e)]
    exact h.cross p a
  exact ⟨after,run,every_pure pure run,⟨body,aux,work,h.different,separate,h.auxSeparate,h.auxOld,cross,h.quadDigits,h.quadValue⟩,
    ApplicationBirthFrame.declare_frame cutoff [] h.body.well h.body.fresh declared⟩

theorem View.e_birth {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 0 j cutoff ids auxIds (plannedValues input j) dataMemory workData)
    (pinned : context.program=input.profile.program) :
    ∃returned after : State F,Exec context before eDeclaration .normal after ∧ Every context before eDeclaration .normal after ∧
      View after input workObject fo bo 1 j cutoff (Function.update ids (.inr .e) returned.nextObject) auxIds (plannedValues input j) dataMemory workData ∧
      ApplicationBirthFrame.Frame cutoff before after []:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have a:=h.body.active;omega
  have encoded64 : input.profile.encoded j<2^64:=lt_trans (input.profile.encoded_bound j h.body.active) (by norm_num [InputCell.scale])
  obtain ⟨returned,called,frame,calleeEvery⟩:=input.profile.lookup_correct context pinned before j h.body.well j64
  have args : Args context before [.variable "j"] [.integer (integer64 j)] before:=by
    apply Args.ordered (order:=[(0,.variable "j")]) (evaluated:=[(0,.integer (integer64 j))])
    · exact List.Perm.refl _
    · exact .cons (h.body.parameter_eval context .j) .nil
    · change List.Forall₂ _ [0] _;exact .cons rfl .nil
  have returnedBody:=h.body.after_call frame
  have returnedWork:=ComplexSource.word_array_after_call h.body.well h.work frame (by simp)
  have returnedAux:=generic_locals_after_call h.body.well h.aux frame (by intros;simp)
  have storable:=ZeroFrame.u64_storable (input.profile.encoded j) encoded64
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists frame.frame.well .u64 "e" (.integer (integer64 (input.profile.encoded j))) storable
  have d:=declare_storable storable storable.converted declared
  have body:=returnedBody.declare_next (next:=.e) rfl d declared
  have work:=ApplicationBirthFrame.array_declare_old frame.frame.well returnedWork d
  have aux:=ApplicationBirthFrame.locals_declare_old frame.frame.well returnedAux (by intro a;cases a <;> decide) d
  have live:=frame.frame.well.objectIds _ _ returnedWork.2.1
  have separate : ∀v,Active 1 v → workObject≠(Function.update ids (.inr .e) returned.nextObject) v:=by
    intro v hv
    by_cases same : v=.inr .e
    · subst v;rw [Function.update_self];omega
    · rw [Function.update_of_ne same]
      exact h.workSeparate v (((active_step (next:=.e) rfl v).mp hv).resolve_left same)
  have cross : ∀p a,(Function.update ids (.inr .e) returned.nextObject) (.inl p)≠auxIds a:=by
    intro p a
    rw [Function.update_of_ne (show Sum.inl p≠Sum.inr Temporary.e from by intro e;cases e)]
    exact h.cross p a
  have run : Exec context before eDeclaration .normal after:=.declareSome (.call args called) declared
  have every : Every context before eDeclaration .normal after:=by
    intro other flow actual
    cases actual with
    | declareSome evaluated actualDeclaration=>
      cases evaluated with
      | call actualArgs actualCall=>
        obtain ⟨_,rfl,rfl⟩:=ApplicationPureCall.args_unique (by intro e he;simp only [List.mem_singleton] at he;subst e;trivial) args actualArgs
        obtain ⟨resultEq,stateEq⟩:=calleeEvery _ _ actualCall
        have valueEq:=CallResult.value.inj resultEq
        cases valueEq
        cases stateEq
        exact ⟨rfl,Option.some.inj (actualDeclaration.symm.trans declared)⟩
      | load place read=> cases place
  exact ⟨returned,after,run,every,⟨body,aux,work,h.different,separate,h.auxSeparate,h.auxOld,cross,h.quadDigits,h.quadValue⟩,
    (lower_frame frame.frame h.body.fresh).trans (ApplicationBirthFrame.declare_frame cutoff [] frame.frame.well returnedBody.fresh declared)⟩

#print axioms View.pure_birth
#print axioms View.e_birth
end RH080Next.FFTPV.QuadSource
