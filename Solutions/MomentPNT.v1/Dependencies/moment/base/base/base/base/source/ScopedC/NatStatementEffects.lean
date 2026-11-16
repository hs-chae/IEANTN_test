/- Bounded statement/sequence/loop effects under a preserving call service. -/
import ScopedC.NatDeclarationEffects
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] Machine.evalExpr ArrayDeclarations.declarations
  ArraySourceExecute.statement ArraySourceExecute.statements ArraySourceExecute.loop

abbrev Outcome := ArraySourceExecute.Outcome

def flowArena : Outcome → NatArena.Arena
  | .continuing s => s.nats
  | .returned s _ => s.nats

theorem leave_arena (s : State) (out : Outcome) :
    flowArena (ArraySourceExecute.leave s out) = flowArena out := by
  cases out <;> rfl

theorem statements_effect (cfg : Layout) (service : Call) (keeps : Preserves service)
    (expressionFuel fuel : Nat) :
    (∀ st s out, ArraySourceExecute.statement cfg service expressionFuel fuel st s = some out →
      flowArena out = s.nats) ∧
    (∀ ss s out, ArraySourceExecute.statements cfg service expressionFuel fuel ss s = some out →
      flowArena out = s.nats) ∧
    (∀ e body s out, ArraySourceExecute.loop cfg service expressionFuel fuel e body s = some out →
      flowArena out = s.nats) := by
  induction fuel with
  | zero =>
      refine ⟨?_,?_,?_⟩
      · intro st s out h
        unfold ArraySourceExecute.statement at h
        contradiction
      · intro ss s out h
        unfold ArraySourceExecute.statements at h
        contradiction
      · intro e body s out h
        unfold ArraySourceExecute.loop at h
        contradiction
  | succ fuel ih =>
      constructor
      · intro st s out h
        cases st with
        | skip =>
            simp only [ArraySourceExecute.statement,Option.some.injEq] at h
            subst out
            rfl
        | eval e =>
            cases he : evalExpr cfg service expressionFuel s e with
            | none => simp [ArraySourceExecute.statement,he] at h
            | some pair =>
                rcases pair with ⟨v,t⟩
                simp only [ArraySourceExecute.statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                subst out
                exact expression keeps he
        | declare ds =>
            cases hd : ArrayDeclarations.declarations cfg service ds s with
            | none => simp [ArraySourceExecute.statement,hd] at h
            | some t =>
                simp only [ArraySourceExecute.statement,hd,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                subst out
                exact array_declarations keeps hd
        | returnStmt e =>
            cases he : evalExpr cfg service expressionFuel s e with
            | none => simp [ArraySourceExecute.statement,he] at h
            | some pair =>
                rcases pair with ⟨v,t⟩
                simp only [ArraySourceExecute.statement,he,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                subst out
                exact expression keeps he
        | branch e yes no =>
            cases he : evalExpr cfg service expressionFuel s e with
            | none => simp [ArraySourceExecute.statement,he] at h
            | some pair =>
                rcases pair with ⟨v,t⟩
                simp only [ArraySourceExecute.statement,he,Bind.bind,Option.bind] at h
                exact (ih.1 _ t out h).trans (expression keeps he)
        | sequence ss =>
            cases hi : ArraySourceExecute.statements cfg service expressionFuel fuel ss s with
            | none => simp [ArraySourceExecute.statement,hi] at h
            | some inner =>
                simp only [ArraySourceExecute.statement,hi,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                subst out
                rw [leave_arena]
                exact ih.2.1 ss s inner hi
        | whileLoop e body =>
            have hh : ArraySourceExecute.loop cfg service expressionFuel fuel e body s = some out := by
              simpa only [ArraySourceExecute.statement] using h
            exact ih.2.2 e body s out hh
        | forLoop initial condition step body =>
            simp only [ArraySourceExecute.statement] at h
            contradiction
      · constructor
        · intro ss s out h
          cases ss with
          | nil =>
              simp only [ArraySourceExecute.statements,Option.some.injEq] at h
              subst out
              rfl
          | cons head tail =>
              cases hh : ArraySourceExecute.statement cfg service expressionFuel fuel head s with
              | none => simp [ArraySourceExecute.statements,hh] at h
              | some first =>
                  cases first with
                  | continuing t =>
                      simp only [ArraySourceExecute.statements,hh,Bind.bind,Option.bind] at h
                      exact (ih.2.1 tail t out h).trans (ih.1 head s (.continuing t) hh)
                  | returned t value =>
                      simp only [ArraySourceExecute.statements,hh,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                      subst out
                      exact ih.1 head s (.returned t value) hh
        · intro e body s out h
          cases he : evalExpr cfg service expressionFuel s e with
          | none => simp [ArraySourceExecute.loop,he] at h
          | some pair =>
              rcases pair with ⟨v,t⟩
              cases ht : truth v with
              | false =>
                  simp only [ArraySourceExecute.loop,he,ht,Bool.false_eq_true,ite_false,
                    Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at h
                  subst out
                  exact expression keeps he
              | true =>
                  cases hi : ArraySourceExecute.statement cfg service expressionFuel fuel body t with
                  | none => simp [ArraySourceExecute.loop,he,ht,hi] at h
                  | some iteration =>
                      cases iteration with
                      | continuing u =>
                          simp only [ArraySourceExecute.loop,he,ht,ite_true,hi,Bind.bind,Option.bind] at h
                          exact (ih.2.2 e body u out h).trans
                            ((ih.1 body t (.continuing u) hi).trans (expression keeps he))
                      | returned u value =>
                          simp only [ArraySourceExecute.loop,he,ht,ite_true,hi,Bind.bind,Option.bind,
                            Pure.pure,Option.some.injEq] at h
                          subst out
                          exact (ih.1 body t (.returned u value) hi).trans (expression keeps he)

theorem statement {cfg : Layout} {service : Call} (keeps : Preserves service)
    {expressionFuel fuel : Nat} {st : Stmt} {s : State} {out : Outcome}
    (h : ArraySourceExecute.statement cfg service expressionFuel fuel st s = some out) :
    flowArena out = s.nats :=
  (statements_effect cfg service keeps expressionFuel fuel).1 st s out h

#print axioms statements_effect
#print axioms statement
end ScopedC.NatEffects
