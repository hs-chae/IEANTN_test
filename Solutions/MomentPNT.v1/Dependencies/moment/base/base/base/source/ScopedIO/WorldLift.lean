/- Lift bounded pure source execution into the additive I/O world.
No application trace, I/O success, or buffer contents are assumed. -/
import ScopedIO.WorldSource
import ScopedC.ArraySourceExecute
namespace ScopedIO.WorldLift
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.ArraySourceExecute
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def withStream (stream : Stream) : ArraySourceExecute.Outcome → Loops.Flow WorldIO.World Value
  | .continuing s => .continuing ⟨s,stream⟩
  | .returned s v => .returned ⟨s,stream⟩ v

theorem leave_scope (s : State) (stream : Stream) (inner : ArraySourceExecute.Outcome) :
    WorldSource.Scope ⟨s,stream⟩ (withStream stream inner)
      (withStream stream (ArraySourceExecute.leave s inner)) := by
  cases inner <;> first | rfl | exact ⟨rfl,rfl⟩

theorem pure_sound (cfg : Layout) (service : Machine.Call) (world : WorldIO.Call)
    (platform : WorldIO.Platform) (stream : Stream) (expressionFuel fuel : Nat) :
    (∀ st s out, statement cfg service expressionFuel fuel st s = some out → WorldSource.Run cfg service world platform st ⟨s,stream⟩ (withStream stream out)) ∧
    (∀ ss s out, statements cfg service expressionFuel fuel ss s = some out →
      Loops.SeqRun (WorldSource.Eval cfg service world platform) (WorldSource.Declare cfg service) truth WorldSource.Scope ss ⟨s,stream⟩ (withStream stream out)) ∧
    (∀ e body s out, loop cfg service expressionFuel fuel e body s = some out →
      Loops.WhileRun (WorldSource.Eval cfg service world platform) (WorldSource.Declare cfg service) truth WorldSource.Scope e body ⟨s,stream⟩ (withStream stream out)) := by
  induction fuel with
  | zero => exact ⟨by intros; contradiction,by intros; contradiction,by intros; contradiction⟩
  | succ fuel ih =>
    constructor
    · intro st s out h
      cases st with
      | skip => simp only [statement,Option.some.injEq] at h; subst out; exact Loops.StmtRun.skip (⟨s,stream⟩ : WorldIO.World)
      | eval e =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.evaluate (WorldSource.Eval.pure he)
      | declare ds =>
          cases hd : ArrayDeclarations.declarations cfg service ds s with
          | none => simp [statement,hd] at h
          | some t =>
              simp only [statement,hd,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.declare ⟨hd,rfl⟩
      | returnStmt e =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.returnValue (WorldSource.Eval.pure he)
      | branch e yes no =>
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [statement,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              simp only [statement,he,Bind.bind,Option.bind,Pure.pure] at h
              exact Loops.StmtRun.branch (WorldSource.Eval.pure he) (ih.1 _ _ _ h)
      | sequence ss =>
          cases hi : statements cfg service expressionFuel fuel ss s with
          | none => simp [statement,hi] at h
          | some inner =>
              simp only [statement,hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
              subst out
              exact Loops.StmtRun.sequence (ih.2.1 _ _ _ hi) (leave_scope s stream inner)
      | whileLoop e body => exact Loops.StmtRun.whileLoop (ih.2.2 _ _ _ _ h)
      | forLoop init cond step body => simp [statement] at h
    · constructor
      · intro ss s out h
        cases ss with
        | nil => simp only [statements,Option.some.injEq] at h; subst out; exact Loops.SeqRun.nil (⟨s,stream⟩ : WorldIO.World)
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
                exact Loops.WhileRun.done (WorldSource.Eval.pure he) hc
            | true =>
                simp only [loop,he,Bind.bind,Option.bind,Pure.pure,hc,↓reduceIte] at h
                cases hi : statement cfg service expressionFuel fuel body t with
                | none => simp [hi] at h
                | some inner =>
                    cases inner with
                    | continuing u =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure] at h
                        exact Loops.WhileRun.next (WorldSource.Eval.pure he) hc (ih.1 _ _ _ hi) (ih.2.2 _ _ _ _ h)
                    | returned u w =>
                        simp only [hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                        subst out
                        exact Loops.WhileRun.returned (WorldSource.Eval.pure he) hc (ih.1 _ _ _ hi)


#print axioms pure_sound
end ScopedIO.WorldLift
