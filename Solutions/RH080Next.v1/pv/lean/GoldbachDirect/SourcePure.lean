import GoldbachDirect.Semantics

/-! Call-free source expressions preserve the entire actual heap and protocol
state, for both permitted operand orders. No allocation or value is assumed. -/
namespace GoldbachDirect.SourcePure
open Semantics

def CallFree : Expr → Prop
  | .literal _ | .variable _ => True
  | .paren e | .cast _ e | .unary _ e | .member e _ _ => CallFree e
  | .binary _ a b | .index a b => CallFree a ∧ CallFree b
  | .conditional a b c => CallFree a ∧ CallFree b ∧ CallFree c
  | .call _ _ => False

private theorem state_by_size {F : Type} {context : Context F} (fuel : Nat) :
    ∀ expression : Expr, sizeOf expression < fuel →
      (∀ {before after : State F} {pointer : Pointer},
        Place context before expression pointer after → CallFree expression → after = before) ∧
      (∀ {before after : State F} {value : Value},
        Eval context before expression value after → CallFree expression → after = before) := by
  induction fuel with
  | zero => intro expression bound; omega
  | succ fuel ih =>
    intro expression bound
    have placeSound : ∀ {before after : State F} {pointer : Pointer},
        Place context before expression pointer after → CallFree expression → after = before := by
      intro before after pointer run closed
      cases run with
      | «variable» => rfl
      | paren run => exact (ih _ (by simp_all; omega)).1 run closed
      | dereference run => exact (ih _ (by simp_all; omega)).2 run closed
      | index base index _ =>
          exact ((ih _ (by simp_all; omega)).2 index closed.2).trans
            ((ih _ (by simp_all; omega)).2 base closed.1)
    refine ⟨placeSound,?_⟩
    intro before after value run closed
    cases run with
    | literal => rfl
    | paren run => exact (ih _ (by simp_all; omega)).2 run closed
    | «variable» => rfl
    | constant => rfl
    | builtin => rfl
    | address run => exact (ih _ (by simp_all; omega)).1 run closed
    | load run _ => exact placeSound run closed
    | cast run _ => exact (ih _ (by simp_all; omega)).2 run closed
    | unary run _ => exact (ih _ (by simp_all; omega)).2 run closed
    | binaryLR left right _ =>
        exact ((ih _ (by simp_all; omega)).2 right closed.2).trans
          ((ih _ (by simp_all; omega)).2 left closed.1)
    | binaryRL right left _ =>
        exact ((ih _ (by simp_all; omega)).2 left closed.1).trans
          ((ih _ (by simp_all; omega)).2 right closed.2)
    | andFalse left _ => exact (ih _ (by simp_all; omega)).2 left closed.1
    | andTrue left _ right _ =>
        exact ((ih _ (by simp_all; omega)).2 right closed.2).trans
          ((ih _ (by simp_all; omega)).2 left closed.1)
    | orTrue left _ => exact (ih _ (by simp_all; omega)).2 left closed.1
    | orFalse left _ right _ =>
        exact ((ih _ (by simp_all; omega)).2 right closed.2).trans
          ((ih _ (by simp_all; omega)).2 left closed.1)
    | conditionalTrue test _ branch =>
        exact ((ih _ (by simp_all; omega)).2 branch closed.2.1).trans
          ((ih _ (by simp_all; omega)).2 test closed.1)
    | conditionalFalse test _ branch =>
        exact ((ih _ (by simp_all; omega)).2 branch closed.2.2).trans
          ((ih _ (by simp_all; omega)).2 test closed.1)
    | call => exact False.elim closed

theorem eval_state {F : Type} {context : Context F} {expression : Expr}
    {before after : State F} {value : Value}
    (run : Eval context before expression value after) (closed : CallFree expression) :
    after = before :=
  (state_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).2 run closed

theorem place_state {F : Type} {context : Context F} {expression : Expr}
    {before after : State F} {pointer : Pointer}
    (run : Place context before expression pointer after) (closed : CallFree expression) :
    after = before :=
  (state_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).1 run closed

end GoldbachDirect.SourcePure
