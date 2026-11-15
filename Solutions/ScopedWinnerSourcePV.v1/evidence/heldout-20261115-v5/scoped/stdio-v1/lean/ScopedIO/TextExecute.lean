/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedIO.TextExpressions

namespace ScopedIO.TextExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0

abbrev Outcome := Loops.Flow World Value

def declare (cfg : Layout) (pureCall : Machine.Call) (ds : List Decl)
    (s : World) : Option World := do
  let t ← ArrayDeclarations.declarations cfg pureCall ds s.app
  return ⟨t,s.stream⟩

theorem declaration_sound {cfg : Layout} {pureCall : Machine.Call} {ds : List Decl}
    {s t : World} (h : declare cfg pureCall ds s = some t) :
    WorldSource.Declare cfg pureCall ds s t := by
  cases hd : ArrayDeclarations.declarations cfg pureCall ds s.app with
  | none => simp [declare,hd] at h
  | some after =>
    simp only [declare,hd,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
    subst t
    exact ⟨hd,rfl⟩

def leave (before : World) : Outcome → Outcome
  | .continuing inner => .continuing (WorldSource.pop before inner)
  | .returned inner v => .returned (WorldSource.pop before inner) v

/- A bounded executor of the additive source semantics. Text calls use the
explicit world contract; all nested pure operations use actual typed C execution.
Unsupported `for` statements fail closed; the selected C programs use while.
Fuel exhaustion also fails closed. Application callees are never leaves. -/
mutual
  def statement (cfg : Layout) (pureCall : Machine.Call) (service : WorldIO.Call)
    (p : WorldIO.Platform) (expressionFuel : Nat) :
      Nat → Stmt → World → Option Outcome
    | 0,_,_ => none
    | fuel+1,st,s => match st with
      | .skip => some (.continuing s)
      | .eval e => do
          let (_,t) ← TextExpressions.expression cfg pureCall service expressionFuel e s
          pure (.continuing t)
      | .declare ds => do
          let t ← declare cfg pureCall ds s
          pure (.continuing t)
      | .returnStmt e => do
          let (v,t) ← TextExpressions.expression cfg pureCall service expressionFuel e s
          pure (.returned t v)
      | .branch e yes no => do
          let (v,t) ← TextExpressions.expression cfg pureCall service expressionFuel e s
          statement cfg pureCall service p expressionFuel fuel (if truth v then yes else no) t
      | .sequence ss => do
          let inner ← statements cfg pureCall service p expressionFuel fuel ss s
          pure (leave s inner)
      | .whileLoop e body => loop cfg pureCall service p expressionFuel fuel e body s
      | .forLoop _ _ _ _ => none
  def statements (cfg : Layout) (pureCall : Machine.Call) (service : WorldIO.Call)
    (p : WorldIO.Platform) (expressionFuel : Nat) :
      Nat → List Stmt → World → Option Outcome
    | 0,_,_ => none
    | fuel+1,[],s => some (.continuing s)
    | fuel+1,head::tail,s => do
        let first ← statement cfg pureCall service p expressionFuel fuel head s
        match first with
        | .continuing t => statements cfg pureCall service p expressionFuel fuel tail t
        | .returned t v => pure (.returned t v)
  def loop (cfg : Layout) (pureCall : Machine.Call) (service : WorldIO.Call)
    (p : WorldIO.Platform) (expressionFuel : Nat) :
      Nat → Expr → Stmt → World → Option Outcome
    | 0,_,_,_ => none
    | fuel+1,e,body,s => do
        let (v,t) ← TextExpressions.expression cfg pureCall service expressionFuel e s
        if truth v then
          let iteration ← statement cfg pureCall service p expressionFuel fuel body t
          match iteration with
          | .continuing u => loop cfg pureCall service p expressionFuel fuel e body u
          | .returned u w => pure (.returned u w)
        else pure (.continuing t)
end

theorem leave_scope (s : World) (inner : Outcome) : WorldSource.Scope s inner (leave s inner) := by
  cases inner <;> simp [WorldSource.Scope,leave]

theorem sound (cfg : Layout) (pureCall : Machine.Call) (service : WorldIO.Call)
    (p : WorldIO.Platform) (expressionFuel fuel : Nat) :
    (∀ st s out, statement cfg pureCall service p expressionFuel fuel st s = some out → WorldSource.Run cfg pureCall service p st s out) ∧
    (∀ ss s out, statements cfg pureCall service p expressionFuel fuel ss s = some out →
      Loops.SeqRun (WorldSource.Eval cfg pureCall service p) (WorldSource.Declare cfg pureCall) truth WorldSource.Scope ss s out) ∧
    (∀ e body s out, loop cfg pureCall service p expressionFuel fuel e body s = some out →
      Loops.WhileRun (WorldSource.Eval cfg pureCall service p) (WorldSource.Declare cfg pureCall) truth WorldSource.Scope e body s out) := by
  induction fuel with
  | zero => exact ⟨by intros; contradiction,by intros; contradiction,by intros; contradiction⟩
  | succ fuel ih =>
    constructor
    · intro st s out h
      cases st with
      | skip => simp only [statement,Option.some.injEq] at h; subst out; exact Loops.StmtRun.skip s
      | eval e =>
          cases he : TextExpressions.expression cfg pureCall service expressionFuel e s with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.evaluate (TextExpressions.expression_sound p he)
      | declare ds =>
          cases hd : declare cfg pureCall ds s with
          | none => simp [statement,hd] at h
          | some t =>
              simp only [statement,hd,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.declare (declaration_sound hd)
      | returnStmt e =>
          cases he : TextExpressions.expression cfg pureCall service expressionFuel e s with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.returnValue (TextExpressions.expression_sound p he)
      | branch e yes no =>
          cases he : TextExpressions.expression cfg pureCall service expressionFuel e s with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure] at h
              exact Loops.StmtRun.branch (TextExpressions.expression_sound p he) (ih.1 _ _ _ h)
      | sequence ss =>
          cases hi : statements cfg pureCall service p expressionFuel fuel ss s with
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
            cases hh : statement cfg pureCall service p expressionFuel fuel head s with
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
        cases he : TextExpressions.expression cfg pureCall service expressionFuel e s with
        | none => simp [loop,he] at h
        | some pair =>
            rcases pair with ⟨v,t⟩
            cases hc : truth v with
            | false =>
                simp only [loop,he,Bind.bind,Option.bind,Pure.pure,hc,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at h
                subst out
                exact Loops.WhileRun.done (TextExpressions.expression_sound p he) hc
            | true =>
                simp only [loop,he,Bind.bind,Option.bind,Pure.pure,hc,↓reduceIte] at h
                cases hi : statement cfg pureCall service p expressionFuel fuel body t with
                | none => simp [hi] at h
                | some inner =>
                    cases inner with
                    | continuing u =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure] at h
                        exact Loops.WhileRun.next (TextExpressions.expression_sound p he) hc (ih.1 _ _ _ hi) (ih.2.2 _ _ _ _ h)
                    | returned u w =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                        subst out
                        exact Loops.WhileRun.returned (TextExpressions.expression_sound p he) hc (ih.1 _ _ _ hi)

theorem statement_sound {cfg : Layout} {pureCall : Machine.Call} {service : WorldIO.Call}
    {p : WorldIO.Platform} {expressionFuel fuel : Nat}
    {st : Stmt} {s : World} {out : Outcome}
    (h : statement cfg pureCall service p expressionFuel fuel st s = some out) : WorldSource.Run cfg pureCall service p st s out :=
  (sound cfg pureCall service p expressionFuel fuel).1 st s out h

end ScopedIO.TextExecute
