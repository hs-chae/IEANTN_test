import GoldbachDirect.PureEvalComplete
import Mathlib.Data.List.Forall2

namespace GoldbachDirect.Interpreter
open Semantics
open SourcePure

def decideCallFree (expression : Expr) : Decidable (CallFree expression) :=
  match expression with
  | .literal _ | .variable _ => isTrue trivial
  | .paren e | .cast _ e | .unary _ e | .member e _ _ => decideCallFree e
  | .binary _ a b | .index a b =>
    letI := decideCallFree a
    letI := decideCallFree b
    inferInstanceAs (Decidable (CallFree a ∧ CallFree b))
  | .conditional a b c =>
    letI := decideCallFree a
    letI := decideCallFree b
    letI := decideCallFree c
    inferInstanceAs (Decidable (CallFree a ∧ CallFree b ∧ CallFree c))
  | .call _ _ => isFalse id

instance (expression : Expr) : Decidable (CallFree expression) := decideCallFree expression

private theorem positions (indices : List Nat) (values : List Value)
    (length : indices.length = values.length) (unique : indices.Nodup) :
    List.Forall₂ (fun index value => (indices.zip values).lookup index = some value) indices values := by
  have strengthened : List.Forall₂ (fun index value => index ∈ indices ∧
      (indices.zip values).lookup index = some value) indices values := by
    induction indices generalizing values with
    | nil => cases values <;> simp_all
    | cons index indices ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
        simp only [List.length_cons,Nat.add_right_cancel_iff] at length
        have hu := List.nodup_cons.mp unique
        have tail := ih values length hu.2
        apply List.Forall₂.cons
        · simp
        · apply tail.imp
          intro index' value' fact
          have neq : index' ≠ index := by
            intro same
            subst index'
            exact hu.1 fact.1
          have neqb : (index' == index) = false := by simp [neq]
          exact ⟨by simp [fact.1],by simpa [List.lookup,neqb] using fact.2⟩
  exact strengthened.imp (fun _ _ fact => fact.2)

private theorem sequence {F : Type} {context : Context F} {state : State F}
    {expressions : List Expr} {values : List Value}
    (runs : List.Forall₂ (fun expression value => Eval context state expression value state)
      expressions values) (indices : List Nat) :
    ArgSequence context state (indices.zip expressions) (indices.zip values) state := by
  induction runs generalizing indices with
  | nil => simp; exact .nil
  | cons first rest ih =>
      cases indices with
      | nil => exact .nil
      | cons index indices => exact .cons first (ih indices)

theorem arguments {F : Type} {context : Context F} {state : State F}
    {expressions : List Expr} {values : List Value}
    (runs : List.Forall₂ (fun expression value => Eval context state expression value state)
      expressions values) : Args context state expressions values state := by
  exact .ordered (List.Perm.refl _) (sequence runs _) (positions _ _
    (by simp [runs.length_eq]) List.nodup_range)

def numbered (start : Nat) : List α → List (Nat × α)
  | [] => []
  | first :: rest => (start,first) :: numbered (start+1) rest

theorem numbered_range (start : Nat) (values : List α) :
    numbered start values = (List.range' start values.length).zip values := by
  induction values generalizing start with
  | nil => rfl
  | cons first rest ih => simp [numbered,List.range'_succ,ih]

theorem numbered_arguments {F : Type} {context : Context F}
    {before after : State F} {expressions : List Expr} {values : List Value}
    (length : values.length = expressions.length)
    (run : ArgSequence context before (numbered 0 expressions) (numbered 0 values) after) :
    Args context before expressions values after := by
  have ranges {α : Type} (xs : List α) : numbered 0 xs = (List.range xs.length).zip xs := by
    simp only [numbered_range,List.range_eq_range']
  rw [ranges expressions,ranges values,length] at run
  exact .ordered (List.Perm.refl _) run
    (positions _ _ (by simpa using length.symm) List.nodup_range)

/-- Compute a permitted argument order for the call-free argument fragment.
Each returned value carries its actual source Eval proof, not an external
summary or a state equality assumption. -/
def pureArguments (context : Context F) (state : State F) (expressions : List Expr) :
    Option {values : List Value // List.Forall₂
      (fun expression value => Eval context state expression value state) expressions values} :=
  match expressions with
  | [] => some ⟨[],.nil⟩
  | expression :: rest =>
    if closed : CallFree expression then
      match computed : PureEval.eval context state expression with
      | none => none
      | some value => do
        let values ← pureArguments context state rest
        return ⟨value :: values.val,.cons (PureEval.eval_complete closed computed) values.property⟩
    else none

end GoldbachDirect.Interpreter
