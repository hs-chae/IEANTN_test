/- Generic mutual expression effects, assembled from independently kernel
checked opaque constructor lemmas. No arithmetic success or arena equality is assumed. -/
import ScopedC.NatExpressionCaseEffects
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] Machine.evalExpr Machine.evalLValue

theorem expression_step (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats) :
    ∀ e s v t, evalExpr cfg call (fuel+1) s e = some (v,t) → t.nats = s.nats := by
  intro e
  cases e with
  | nat number => exact case_nat cfg call keeps fuel he hl number
  | uint number => exact case_uint cfg call keeps fuel he hl number
  | character number => exact case_character cfg call keeps fuel he hl number
  | stringLiteral text => exact case_stringLiteral cfg call keeps fuel he hl text
  | conditional test yes no => exact case_conditional cfg call keeps fuel he hl test yes no
  | var name => exact case_var cfg call keeps fuel he hl name
  | unary op arg => exact case_unary cfg call keeps fuel he hl op arg
  | post op arg => exact case_post cfg call keeps fuel he hl op arg
  | cast type arg => exact case_cast cfg call keeps fuel he hl type arg
  | binary op left right => exact case_binary cfg call keeps fuel he hl op left right
  | field op object name => exact case_field cfg call keeps fuel he hl op object name
  | index object index => exact case_index cfg call keeps fuel he hl object index
  | call function args => exact case_call cfg call keeps fuel he hl function args
  | record fields => exact case_record cfg call keeps fuel he hl fields

theorem one_step (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats) :
    (∀ e s v t, evalExpr cfg call (fuel+1) s e = some (v,t) → t.nats = s.nats) ∧
    (∀ e s a w t, evalLValue cfg call (fuel+1) s e = some (a,w,t) → t.nats = s.nats) :=
  ⟨expression_step cfg call keeps fuel he hl,lvalue_step cfg call keeps fuel he hl⟩

theorem expressions (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat) :
    (∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats) ∧
    (∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats) := by
  induction fuel with
  | zero =>
      constructor
      · intro e s v t h
        unfold evalExpr at h
        contradiction
      · intro e s a w t h
        unfold evalLValue at h
        contradiction
  | succ fuel ih => exact one_step cfg call keeps fuel ih.1 ih.2

theorem expression {cfg : Layout} {call : Call} (keeps : Preserves call)
    {fuel : Nat} {s t : State} {e : Expr} {v : Value}
    (h : evalExpr cfg call fuel s e = some (v,t)) : t.nats = s.nats :=
  (expressions cfg call keeps fuel).1 e s v t h

theorem lvalue {cfg : Layout} {call : Call} (keeps : Preserves call)
    {fuel : Nat} {s t : State} {e : Expr} {a : Address} {w : Bool}
    (h : evalLValue cfg call fuel s e = some (a,w,t)) : t.nats = s.nats :=
  (expressions cfg call keeps fuel).2 e s a w t h

#print axioms expression_step
#print axioms expression
#print axioms lvalue
end ScopedC.NatEffects
