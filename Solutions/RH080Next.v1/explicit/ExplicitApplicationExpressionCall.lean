/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitApplicationPureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ApplicationPureCall
open GoldbachDirect GoldbachDirect.Semantics

/-- Ordinary application expression calls, including the operational rule
that permits a callee to terminate. All permitted argument orders are covered. -/
theorem expression_call_unique {F : Type} {context : Context F} (cname : String) (expressions : List Expr)
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (callee : ∀{before a b : State F} {args : List Value} {ra rb : CallResult},
      Call context cname args before ra a → Call context cname args before rb b → rb=ra ∧ b=a) :
    CompareSource.Unique context (.expression (.call cname expressions)) := by
  intro before a b fa fb first second
  cases first with
  | expression ev=>
    cases ev with
    | load place loaded=>cases place
    | call args call=>
      cases second with
      | expression ev'=>
        cases ev' with
        | load place loaded=>cases place
        | call args' call'=>
          obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
          obtain ⟨he,hs⟩:=callee call call'
          cases he
          exact ⟨rfl,hs.symm⟩
      | callTerminated args' call'=>
        obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
        cases (callee call call').1
  | callTerminated args call=>
    cases second with
    | expression ev'=>
      cases ev' with
      | load place loaded=>cases place
      | call args' call'=>
        obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
        cases (callee call call').1
    | callTerminated args' call'=>
      obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
      obtain ⟨he,hs⟩:=callee call call'
      cases he
      exact ⟨rfl,hs.symm⟩

theorem declare_call_unique {F : Type} {context : Context F} (cname : String) (expressions : List Expr)
    (closed : ∀e∈expressions,SourcePure.CallFree e) (ctype : CType) (cvariable : String)
    (callee : ∀{before a b : State F} {args : List Value} {value : Value} {result : CallResult},
      Call context cname args before (.value value) a → Call context cname args before result b →
        result=.value value ∧ b=a) :
    CompareSource.Unique context (.declare ctype cvariable (some (.call cname expressions))) := by
  intro before a b fa fb first second
  cases first with
  | declareSome ev declared=>
    cases ev with
    | load place loaded=>cases place
    | call args call=>
      cases second with
      | declareSome ev' declared'=>
        cases ev' with
        | load place loaded=>cases place
        | call args' call'=>
          obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
          obtain ⟨he,hs⟩:=callee call call'
          cases he
          cases hs
          have eq:=Option.some.inj (declared.symm.trans declared')
          exact ⟨rfl,eq⟩

#print axioms expression_call_unique
#print axioms declare_call_unique
end RH080Next.FFTPV.ApplicationPureCall
