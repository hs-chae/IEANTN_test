/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.SourceCalls

namespace ScopedC.SourceExecute
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

abbrev Outcome := Loops.Flow State Value

def leave (before : State) : Outcome → Outcome
  | .continuing inner => .continuing (popScope before inner)
  | .returned inner v => .returned (popScope before inner) v

/- A bounded executor of the existing source semantics, not a mathematical
output checker. All expressions use the existing typed/memory evaluator.
Unsupported `for` statements fail closed; the selected C programs use while.
Fuel exhaustion also fails closed. Application callees are never leaves. -/
mutual
  def statement (cfg : Layout) (service : Call) (expressionFuel : Nat) :
      Nat → Stmt → State → Option Outcome
    | 0,_,_ => none
    | fuel+1,st,s => match st with
      | .skip => some (.continuing s)
      | .eval e => do
          let (_,t) ← evalExpr cfg service expressionFuel s e
          pure (.continuing t)
      | .declare ds => do
          let t ← declarations cfg service ds s
          pure (.continuing t)
      | .returnStmt e => do
          let (v,t) ← evalExpr cfg service expressionFuel s e
          pure (.returned t v)
      | .branch e yes no => do
          let (v,t) ← evalExpr cfg service expressionFuel s e
          statement cfg service expressionFuel fuel (if truth v then yes else no) t
      | .sequence ss => do
          let inner ← statements cfg service expressionFuel fuel ss s
          pure (leave s inner)
      | .whileLoop e body => loop cfg service expressionFuel fuel e body s
      | .forLoop _ _ _ _ => none
  def statements (cfg : Layout) (service : Call) (expressionFuel : Nat) :
      Nat → List Stmt → State → Option Outcome
    | 0,_,_ => none
    | fuel+1,[],s => some (.continuing s)
    | fuel+1,head::tail,s => do
        let first ← statement cfg service expressionFuel fuel head s
        match first with
        | .continuing t => statements cfg service expressionFuel fuel tail t
        | .returned t v => pure (.returned t v)
  def loop (cfg : Layout) (service : Call) (expressionFuel : Nat) :
      Nat → Expr → Stmt → State → Option Outcome
    | 0,_,_,_ => none
    | fuel+1,e,body,s => do
        let (v,t) ← evalExpr cfg service expressionFuel s e
        if truth v then
          let iteration ← statement cfg service expressionFuel fuel body t
          match iteration with
          | .continuing u => loop cfg service expressionFuel fuel e body u
          | .returned u w => pure (.returned u w)
        else pure (.continuing t)
end

theorem leave_scope (s : State) (inner : Outcome) : Scope s inner (leave s inner) := by
  cases inner <;> simp [Scope,leave]

theorem sound (cfg : Layout) (service : Call) (expressionFuel fuel : Nat) :
    (∀ st s out, statement cfg service expressionFuel fuel st s = some out → Run cfg service st s out) ∧
    (∀ ss s out, statements cfg service expressionFuel fuel ss s = some out →
      Loops.SeqRun (Eval cfg service) (Declare cfg service) truth Scope ss s out) ∧
    (∀ e body s out, loop cfg service expressionFuel fuel e body s = some out →
      Loops.WhileRun (Eval cfg service) (Declare cfg service) truth Scope e body s out) := by
  induction fuel with
  | zero => exact ⟨by intros; contradiction,by intros; contradiction,by intros; contradiction⟩
  | succ fuel ih =>
    constructor
    · intro st s out h
      cases st with
      | skip => simp only [statement,Option.some.injEq] at h; subst out; exact Loops.StmtRun.skip s
      | eval e =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.evaluate ⟨expressionFuel,he⟩
      | declare ds =>
          cases hd : declarations cfg service ds s with
          | none => simp [statement,hd] at h
          | some t =>
              simp only [statement,hd,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.declare hd
      | returnStmt e =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.returnValue ⟨expressionFuel,he⟩
      | branch e yes no =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure] at h
              exact Loops.StmtRun.branch ⟨expressionFuel,he⟩ (ih.1 _ _ _ h)
      | sequence ss =>
          cases hi : statements cfg service expressionFuel fuel ss s with
          | none => simp [statement,hi] at h
          | some inner =>
              simp only [statement,hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.sequence (ih.2.1 _ _ _ hi) (leave_scope s inner)
      | whileLoop e body => exact Loops.StmtRun.whileLoop (ih.2.2 _ _ _ _ h)
      | forLoop init cond step body => simp [statement] at h
    · constructor
      · intro ss s out h
        cases ss with
        | nil => simp only [statements,Option.some.injEq] at h; subst out; exact Loops.SeqRun.nil s
        | cons head tail =>
            cases hh : statement cfg service expressionFuel fuel head s with
            | none => simp [statements,hh] at h
            | some first =>
                cases first with
                | continuing t =>
                    simp only [statements,hh,Bind.bind,Option.bind,Pure.pure] at h
                    exact Loops.SeqRun.next (ih.1 _ _ _ hh) (ih.2.1 _ _ _ h)
                | returned t v =>
                    simp only [statements,hh,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                    subst out
                    exact Loops.SeqRun.returned (ih.1 _ _ _ hh)
      · intro e body s out h
        cases he : evalExpr cfg service expressionFuel s e with
        | none => simp [loop,he] at h
        | some pair =>
            rcases pair with ⟨v,t⟩
            cases hc : truth v with
            | false =>
                simp only [loop,he,Bind.bind,Option.bind,Pure.pure,hc,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at h
                subst out
                exact Loops.WhileRun.done ⟨expressionFuel,he⟩ hc
            | true =>
                simp only [loop,he,Bind.bind,Option.bind,Pure.pure,hc,↓reduceIte] at h
                cases hi : statement cfg service expressionFuel fuel body t with
                | none => simp [hi] at h
                | some inner =>
                    cases inner with
                    | continuing u =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure] at h
                        exact Loops.WhileRun.next ⟨expressionFuel,he⟩ hc (ih.1 _ _ _ hi) (ih.2.2 _ _ _ _ h)
                    | returned u w =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                        subst out
                        exact Loops.WhileRun.returned ⟨expressionFuel,he⟩ hc (ih.1 _ _ _ hi)

theorem statement_sound {cfg : Layout} {service : Call} {expressionFuel fuel : Nat}
    {st : Stmt} {s : State} {out : Outcome}
    (h : statement cfg service expressionFuel fuel st s = some out) : Run cfg service st s out :=
  (sound cfg service expressionFuel fuel).1 st s out h

end ScopedC.SourceExecute
