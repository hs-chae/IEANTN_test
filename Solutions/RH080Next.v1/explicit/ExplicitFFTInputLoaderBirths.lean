/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderBodyView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem BodyView.birth {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat} {next : Temporary} {expression : Expr}
    (h : BodyView before input fo bo count j cutoff ids values memory) (index : localIndex next=count)
    (storable : Storable (varType (.inr next)) (values (.inr next)))
    (evaluated : Eval context before expression (values (.inr next)) before) (pure : SourcePure.CallFree expression) :
    ∃after,Exec context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after ∧
      Every context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after ∧
      BodyView after input fo bo (count+1) j cutoff (Function.update ids (.inr next) before.nextObject) values memory ∧
      ApplicationBirthFrame.Frame before.nextObject before after []:=by
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists h.well _ _ _ storable
  have d:=declare_storable storable storable.converted declared
  have run : Exec context before (.declare (varType (.inr next)) (temporaryName next) (some expression)) .normal after:=.declareSome evaluated declared
  exact ⟨after,run,every_pure pure run,h.declare_next index d declared,
    ApplicationBirthFrame.declare_frame _ [] h.well (le_refl _) declared⟩

def eDeclaration : Stmt:=.declare .u64 "e" (some (.call "encoded_node" [.variable "j"]))

theorem BodyView.e_birth {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 0 j cutoff ids (plannedValues input j) memory)
    (pinned : context.program=input.profile.program) :
    ∃returned after : State F,Exec context before eDeclaration .normal after ∧ Every context before eDeclaration .normal after ∧
      BodyView after input fo bo 1 j cutoff (Function.update ids (.inr .e) returned.nextObject) (plannedValues input j) memory ∧
      ApplicationBirthFrame.Frame before.nextObject before after []:=by
  have j64 : j<2^64:=by have shape:=input.profile.shape;have active:=h.active;omega
  have encoded64 : input.profile.encoded j<2^64:=lt_trans (input.profile.encoded_bound j h.active) (by norm_num [InputCell.scale])
  obtain ⟨returned,called,frame,calleeEvery⟩:=input.profile.lookup_correct context pinned before j h.well j64
  have args : Args context before [.variable "j"] [.integer (integer64 j)] before:=by
    apply Args.ordered (order:=[(0,.variable "j")]) (evaluated:=[(0,.integer (integer64 j))])
    · exact List.Perm.refl _
    · exact .cons (h.parameter_eval context .j) .nil
    · change List.Forall₂ _ [0] _;exact .cons rfl .nil
  have returnedView:=h.after_call frame
  have storable:=ZeroFrame.u64_storable (input.profile.encoded j) encoded64
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists frame.frame.well .u64 "e" (.integer (integer64 (input.profile.encoded j))) storable
  have d:=declare_storable storable storable.converted declared
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
  have fresh:=ApplicationBirthFrame.declare_frame before.nextObject [] frame.frame.well frame.frame.nextObject declared
  exact ⟨returned,after,run,every,returnedView.declare_next (next:=.e) rfl d declared,frame.frame.trans fresh⟩

#print axioms BodyView.birth
#print axioms BodyView.e_birth
end RH080Next.FFTPV.InputLoader
