/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixScopes
import FFTDropTwoSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics

theorem list_environment_scope {F : Type} {context : Context F} {statements : List Stmt}
    (preserved : ∀stmt∈statements,∀(before after : State F) flow,Exec context before stmt flow after →
      after.environment=before.environment ∧ after.scope=before.scope)
    {before after : State F} {flow : Flow} (run : ExecList context before statements flow after) :
    after.environment=before.environment ∧ after.scope=before.scope := by
  induction statements generalizing before with
  | nil=>cases run;exact ⟨rfl,rfl⟩
  | cons stmt rest ih=>
    cases run with
    | abrupt head _=>exact preserved stmt (by simp) _ _ _ head
    | cons head tail=>
      obtain ⟨e1,s1⟩:=preserved stmt (by simp) _ _ _ head
      obtain ⟨e2,s2⟩:=ih (fun stmt hs=>preserved stmt (by simp [hs])) tail
      exact ⟨e2.trans e1,s2.trans s1⟩

theorem drop_round_fields {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    (actual : Exec context before DropTwoSource.roundingBranch flow after) :
    after.environment=before.environment ∧ after.scope=before.scope:=by
  cases actual with
  | ifFalse evaluated _=>
    have same:=SourcePure.eval_state evaluated (by trivial)
    subst_vars;exact ⟨rfl,rfl⟩
  | ifTrue evaluated _ body=>
    have same:=SourcePure.eval_state evaluated (by trivial)
    subst_vars
    exact ⟨BlockEnvironment.block_environment body,BlockEnvironment.block_scope body⟩

theorem drop_tail_fields {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    (actual : ExecList context before
      [DropTwoSource.iReset,DropTwoSource.loop,DropTwoSource.clear 4,DropTwoSource.clear 5,DropTwoSource.roundingBranch] flow after) :
    after.environment=before.environment ∧ after.scope=before.scope:=by
  apply list_environment_scope ?_ actual
  intro stmt member a b f run
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl
  · exact ⟨MainTransport.pure_assignment_environment (by trivial) (by trivial) run,pure_assignment_scope (by trivial) (by trivial) run⟩
  · exact ⟨BlockEnvironment.while_block_environment (by trivial) run,BlockEnvironment.while_block_scope (by trivial) run⟩
  · exact ⟨MainTransport.pure_assignment_environment (by trivial) (by trivial) run,pure_assignment_scope (by trivial) (by trivial) run⟩
  · exact ⟨MainTransport.pure_assignment_environment (by trivial) (by trivial) run,pure_assignment_scope (by trivial) (by trivial) run⟩
  · exact drop_round_fields run

/-- All actual old lexical bindings survive the real lost-word declaration,
shift loop, clears and optional nested increment. -/
theorem drop_lookup_scope {F : Type} {context : Context F} {before after : State F}
    (actual : ExecList context before DropTwoSource.statements .normal after) :
    (∀name,name≠"lost" → after.environment.lookup name=before.environment.lookup name) ∧ after.scope=before.scope:=by
  cases actual with
  | abrupt first no=>exact False.elim (no rfl)
  | cons first rest=>
    obtain ⟨env,scope⟩:=drop_tail_fields rest
    refine ⟨?_,scope.trans (pure_declaration_scope (by trivial) first)⟩
    intro name different
    rw [env]
    exact MainTransport.pure_declaration_lookup (by trivial) different first

#print axioms drop_lookup_scope
end RH080Next.FFTPV.MainSuffix
