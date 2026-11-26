/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareDeterminism
import GoldbachDirect.PureArgs
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ApplicationPureCall
open GoldbachDirect GoldbachDirect.Semantics

theorem args_unique {F : Type} {context : Context F} {before a b : State F}
    {expressions : List Expr} {xs ys : List Value}
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (first : Args context before expressions xs a) (second : Args context before expressions ys b) :
    a=before ∧ b=before ∧ xs=ys := by
  obtain ⟨ha,hx⟩:=PureArgs.args_sound first closed
  obtain ⟨hb,hy⟩:=PureArgs.args_sound second closed
  refine ⟨ha,hb,?_⟩
  clear closed first second
  induction hx generalizing ys with
  | nil=>cases hy; rfl
  | cons hx ht ih=>
    cases hy with
    | cons hy ht'=>
      have eq:=Option.some.inj (hx.symm.trans hy)
      cases eq
      exact congrArg (List.cons _) (ih ht')

/-- A returned application call is deterministic once the actual callee is
proved deterministic. Source arguments may execute in any permitted order. -/
theorem return_call_unique {F : Type} {context : Context F} (cname : String) (expressions : List Expr)
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (callee : ∀{before a b : State F} {args : List Value} {value : Value} {result : CallResult},
      Call context cname args before (.value value) a → Call context cname args before result b →
        result=.value value ∧ b=a) :
    CompareSource.Unique context (.returnValue (some (.call cname expressions))) := by
  intro before a b fa fb first second
  cases first with
  | returnSome ev=>
    cases ev with
    | call args call=>
      cases second with
      | returnSome ev'=>
        cases ev' with
        | call args' call'=>
          obtain ⟨rfl,rfl,rfl⟩:=args_unique closed args args'
          obtain ⟨he,hs⟩:=callee call call'
          cases he
          exact ⟨rfl,hs.symm⟩
        | load place loaded=>cases place
    | load place loaded=>cases place

#print axioms args_unique
#print axioms return_call_unique
end RH080Next.FFTPV.ApplicationPureCall
