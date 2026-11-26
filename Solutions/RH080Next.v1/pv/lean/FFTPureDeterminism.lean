/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.PureEval
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.PureDeterminism
open GoldbachDirect GoldbachDirect.Semantics

/-- The source expression rules, including both binary operand orders, compute
one value and preserve the whole state for call-free expressions. -/
theorem eval_unique {F : Type} {context : Context F} {before a b : State F}
    {expression : Expr} {v w : Value} (closed : SourcePure.CallFree expression)
    (first : Eval context before expression v a) (second : Eval context before expression w b) :
    v = w ∧ a = b := by
  obtain ⟨sa, va⟩ := PureEval.eval_sound first closed
  obtain ⟨sb, vb⟩ := PureEval.eval_sound second closed
  exact ⟨Option.some.inj (va.symm.trans vb), sa.trans sb.symm⟩

theorem place_unique {F : Type} {context : Context F} {before a b : State F}
    {expression : Expr} {v w : Pointer} (closed : SourcePure.CallFree expression)
    (first : Place context before expression v a) (second : Place context before expression w b) :
    v = w ∧ a = b := by
  obtain ⟨sa, va, _⟩ := PureEval.place_sound first closed
  obtain ⟨sb, vb, _⟩ := PureEval.place_sound second closed
  exact ⟨Option.some.inj (va.symm.trans vb), sa.trans sb.symm⟩

/-- A straight-line source instruction with pure expressions. Actual typed
allocation and conversion remain the existing State.declare/store operations. -/
def Simple : Stmt → Prop
  | .declare _ _ none => True
  | .declare _ _ (some expression) => SourcePure.CallFree expression
  | .assign destination expression => SourcePure.CallFree destination ∧ SourcePure.CallFree expression
  | .expression expression => SourcePure.CallFree expression
  | .returnValue none | .breakLoop | .continueLoop | .label _ | .gotoLabel _ => True
  | .returnValue (some expression) => SourcePure.CallFree expression
  | _ => False

theorem simple_unique {F : Type} {context : Context F} {before a b : State F}
    {statement : Stmt} {fa fb : Flow} (simple : Simple statement)
    (first : Exec context before statement fa a) (second : Exec context before statement fb b) :
    fa = fb ∧ a = b := by
  cases statement <;> simp only [Simple] at simple
  all_goals try contradiction
  case declare ctype cname init =>
    cases init with
    | none =>
      cases first with | declareNone da =>
        cases second with | declareNone db => exact ⟨rfl, Option.some.inj (da.symm.trans db)⟩
    | some expression =>
      cases first with | declareSome er da =>
        cases second with | declareSome er' db =>
          obtain ⟨rfl, rfl⟩ := eval_unique simple er er'
          exact ⟨rfl, Option.some.inj (da.symm.trans db)⟩
  case assign destination expression =>
    cases first with | assign er pl stored =>
      cases second with | assign er' pl' stored' =>
        obtain ⟨rfl, rfl⟩ := eval_unique simple.2 er er'
        obtain ⟨rfl, rfl⟩ := place_unique simple.1 pl pl'
        exact ⟨rfl, Option.some.inj (stored.symm.trans stored')⟩
  case expression expression =>
    cases first with
    | expression er =>
      cases second with
      | expression er' => exact ⟨rfl, (eval_unique simple er er').2⟩
      | callTerminated ar called => contradiction
    | callTerminated ar called => contradiction
  case returnValue expression =>
    cases expression with
    | none => cases first; cases second; exact ⟨rfl, rfl⟩
    | some expression =>
      cases first with | returnSome er =>
        cases second with | returnSome er' =>
          obtain ⟨rfl, rfl⟩ := eval_unique simple er er'
          exact ⟨rfl, rfl⟩
  case breakLoop => cases first; cases second; exact ⟨rfl, rfl⟩
  case continueLoop => cases first; cases second; exact ⟨rfl, rfl⟩
  case label cname => cases first; cases second; exact ⟨rfl, rfl⟩
  case gotoLabel cname => cases first; cases second; exact ⟨rfl, rfl⟩

/-- All permitted executions of a pure straight-line source list agree,
including abrupt returns. This is a proof from the execution rules. -/
theorem list_unique {F : Type} {context : Context F} {before a b : State F}
    {statements : List Stmt} {fa fb : Flow}
    (simple : ∀s ∈ statements, Simple s)
    (first : ExecList context before statements fa a) (second : ExecList context before statements fb b) :
    fa = fb ∧ a = b := by
  induction statements generalizing before fa fb a b with
  | nil => cases first; cases second; exact ⟨rfl, rfl⟩
  | cons statement statements ih =>
    have head := simple statement (by simp)
    have tail : ∀s ∈ statements, Simple s := fun s hs => simple s (by simp [hs])
    cases first with
    | cons one rest =>
      cases second with
      | cons one' rest' =>
        obtain ⟨_, rfl⟩ := simple_unique head one one'
        exact ih tail rest rest'
      | abrupt one' abrupt =>
        have eq := (simple_unique head one one').1
        exact False.elim (abrupt eq.symm)
    | abrupt one abrupt =>
      cases second with
      | cons one' rest' =>
        have eq := (simple_unique head one one').1
        exact False.elim (abrupt eq)
      | abrupt one' abrupt' => exact simple_unique head one one'

/-- Pure straight-line block scopes also have unique flow and final state. -/
theorem block_unique {F : Type} {context : Context F} {before a b : State F}
    {statements : List Stmt} {fa fb : Flow}
    (simple : ∀s ∈ statements, Simple s)
    (first : Exec context before (.block statements) fa a)
    (second : Exec context before (.block statements) fb b) : fa = fb ∧ a = b := by
  cases first with | block entered run closed =>
    cases second with | block entered' run' closed' =>
      subst_vars
      obtain ⟨rfl, rfl⟩ := list_unique simple run run'
      exact ⟨rfl, rfl⟩

#print axioms simple_unique
#print axioms list_unique
#print axioms block_unique
end RH080Next.FFTPV.PureDeterminism
