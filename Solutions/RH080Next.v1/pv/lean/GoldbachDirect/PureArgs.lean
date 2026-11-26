/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.PureEval
import Mathlib.Data.List.Forall2

set_option autoImplicit false
namespace GoldbachDirect.PureArgs
open Semantics SourcePure

private theorem lookup_member {V : Type} (pairs : List (Nat×V)) (j : Nat) (v : V)
    (h : pairs.lookup j=some v) : (j,v)∈pairs := by
  induction pairs with
  | nil => simp at h
  | cons p ps ih =>
    rcases p with ⟨i,w⟩
    by_cases he : i=j
    · subst i
      simp only [List.lookup_cons,beq_self_eq_true,↓reduceIte,Option.some.injEq] at h
      subst w
      exact List.mem_cons_self
    · have hbeq : (j==i)=false := by
        cases hh : (j==i) with
        | false => rfl
        | true => exact False.elim (he (eq_of_beq hh).symm)
      have ht : ps.lookup j=some v := by simpa only [List.lookup_cons,hbeq] using h
      exact List.mem_cons_of_mem _ (ih ht)

private theorem sequence_sound {F : Type} {context : Context F}
    {before after : State F} {order : List (Nat×Expr)} {evaluated : List (Nat×Value)}
    (run : ArgSequence context before order evaluated after)
    (closed : ∀ p∈order,CallFree p.2) :
    after=before ∧ ∀ j v,(j,v)∈evaluated →
      ∃ e,(j,e)∈order ∧ PureEval.eval context before e=some v := by
  induction order generalizing before after evaluated with
  | nil => cases run; exact ⟨rfl,by simp⟩
  | cons p expressions ih =>
    rcases p with ⟨index,expression⟩
    cases run with
    | cons ev rest =>
      have hp : CallFree expression := closed (index,expression) List.mem_cons_self
      obtain ⟨rfl,he⟩ := PureEval.eval_sound ev hp
      obtain ⟨hs,ht⟩ := ih rest (fun p hp => closed p (List.mem_cons_of_mem _ hp))
      refine ⟨hs,?_⟩
      intro j v hv
      rcases List.mem_cons.mp hv with hx|hx
      · cases hx
        exact ⟨expression,List.mem_cons_self,he⟩
      · obtain ⟨e,hm,he⟩ := ht j v hx
        exact ⟨e,List.mem_cons_of_mem _ hm,he⟩

private theorem indexed_zip {expressions : List Expr} {j : Nat} {e : Expr}
    (h : (j,e)∈(List.range expressions.length).zip expressions) : expressions[j]?=some e := by
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp h
  have hh := List.getElem?_zip_eq_some.mp hk
  have hkj : k=j := by
    by_cases hb : k<expressions.length
    · simpa [List.getElem?_range,hb] using hh.1
    · simp [List.getElem?_range,hb] at hh
  simpa [hkj] using hh.2

/-- Every permitted permutation of call-free arguments preserves the complete
state and gives precisely the unique pure values in their SOURCE positions. -/
theorem args_sound {F : Type} {context : Context F} {expressions : List Expr}
    {before after : State F} {values : List Value}
    (run : Args context before expressions values after)
    (closed : ∀ e∈expressions,CallFree e) :
    after=before ∧ List.Forall₂ (fun e v => PureEval.eval context before e=some v) expressions values := by
  cases run with
  | ordered permutation seq positions =>
    rename_i order evaluated
    have hc : ∀ (p : Nat×Expr),p∈order → CallFree p.2 := by
      intro p hp
      have hh := permutation.mem_iff.mp hp
      exact closed p.2 (List.of_mem_zip hh).2
    obtain ⟨hs,ho⟩ := sequence_sound seq hc
    refine ⟨hs,List.forall₂_of_length_eq_of_get ?_ ?_⟩
    · simpa using positions.length_eq
    · intro j hj hv
      have hpos := positions.get (by simpa using hj) hv
      simp only [List.get_eq_getElem,List.getElem_range] at hpos
      obtain ⟨e,hm,he⟩ := ho j _ (lookup_member _ _ _ hpos)
      have hidx := indexed_zip (permutation.mem_iff.mp hm)
      have heq : expressions.get ⟨j,hj⟩=e := by
        simpa only [List.getElem?_eq_getElem hj,Option.some.injEq,List.get_eq_getElem] using hidx
      simpa only [heq,List.get_eq_getElem] using he

#print axioms args_sound
end GoldbachDirect.PureArgs
