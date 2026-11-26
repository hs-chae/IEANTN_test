import GoldbachDirect.Semantics

set_option autoImplicit false

namespace GoldbachDirect.SourceControl
open Semantics

theorem assign_normal {F : Type} {context : Context F} {before after : State F}
    {destination expression : Expr} {flow : Flow}
    (run : Exec context before (.assign destination expression) flow after) : flow = .normal := by
  cases run
  rfl

theorem declare_normal {F : Type} {context : Context F} {before after : State F}
    {type : CType} {name : String} {expression : Option Expr} {flow : Flow}
    (run : Exec context before (.declare type name expression) flow after) : flow = .normal := by
  cases run <;> rfl

theorem list_normal {F : Type} {context : Context F} {statements : List Stmt}
    {before after : State F} {flow : Flow}
    (run : ExecList context before statements flow after)
    (each : ∀ statement ∈ statements, ∀ before after flow,
      Exec context before statement flow after → flow = .normal) : flow = .normal := by
  induction statements generalizing before after flow with
  | nil => cases run; rfl
  | cons statement statements ih =>
      cases run with
      | cons first rest =>
          exact ih rest (fun s hs => each s (by simp [hs]))
      | abrupt first abrupt =>
          exact False.elim (abrupt (each statement (by simp) _ _ _ first))

theorem block_normal {F : Type} {context : Context F} {statements : List Stmt}
    {before after : State F} {flow : Flow}
    (run : Exec context before (.block statements) flow after)
    (each : ∀ statement ∈ statements, ∀ before after flow,
      Exec context before statement flow after → flow = .normal) : flow = .normal := by
  cases run with
  | block entered body finished => exact list_normal body each

theorem if_normal {F : Type} {context : Context F} {test : Expr} {yes : Stmt} {no : Option Stmt}
    {before after : State F} {flow : Flow}
    (run : Exec context before (.ite test yes no) flow after)
    (yesNormal : ∀ before after flow, Exec context before yes flow after → flow = .normal)
    (noNormal : ∀ statement ∈ no, ∀ before after flow,
      Exec context before statement flow after → flow = .normal) : flow = .normal := by
  cases run with
  | ifTrue testRun test body => exact yesNormal _ _ _ body
  | ifFalse => rfl
  | ifElse testRun test body => exact noNormal _ (by simp) _ _ _ body

theorem list_head {F : Type} {context : Context F} {statement : Stmt} {statements : List Stmt}
    {before after : State F} {flow : Flow}
    (run : ExecList context before (statement :: statements) flow after)
    (normal : ∀ before after flow, Exec context before statement flow after → flow = .normal) :
    ∃ middle, Exec context before statement .normal middle ∧
      ExecList context middle statements flow after := by
  cases run with
  | cons first rest => exact ⟨_,first,rest⟩
  | abrupt first abrupt => exact False.elim (abrupt (normal _ _ _ first))

theorem list_head_at {F : Type} {context : Context F} {statement : Stmt} {statements : List Stmt}
    {before after : State F} {flow : Flow}
    (run : ExecList context before (statement :: statements) flow after)
    (normal : ∀ after flow, Exec context before statement flow after → flow = .normal) :
    ∃ middle, Exec context before statement .normal middle ∧
      ExecList context middle statements flow after := by
  cases run with
  | cons first rest => exact ⟨_,first,rest⟩
  | abrupt first abrupt => exact False.elim (abrupt (normal _ _ first))

end GoldbachDirect.SourceControl
