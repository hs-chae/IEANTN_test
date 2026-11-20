/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
import RamanujanPV.QuotientCFunction

namespace RamanujanPV.QuotientCHeapShape
open QuotientCMachine
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma shape_refl (heap : Heap) : SameShape heap heap := fun _=>rfl
lemma shape_trans {a b c : Heap} (h : SameShape a b) (h' : SameShape b c) : SameShape a c :=
  fun base=>(h base).trans (h' base)

lemma write_shape {heap after : Heap} {base index value : Nat}
    (written : write heap base index value=some after) : SameShape heap after := by
  unfold write at written
  cases hb : heap base with
  | none => simp [hb] at written
  | some block =>
    rw [hb] at written
    change (if base%8=0 ∧ index < block.extent ∧ base+8*index+8 ≤ modulus ∧ value < modulus then
      some (Function.update heap base (some {block with words:=Function.update block.words index value}))
      else none)=some after at written
    split at written
    · have ha := Option.some.inj written
      subst after
      exact word_update_sameShape hb
    · contradiction

lemma eval_shape {call : Service} {e : Expr} {s t : State} {value : Value}
    (run : Eval call e s t value) : SameShape s.heap t.heap := by
  unfold Eval eval at run
  split at run
  · obtain ⟨v,hv,rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨env,he,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨word,hw,last⟩ := Option.bind_eq_some_iff.mp rest
    have ht : s.heap=t.heap := congrArg State.heap (Prod.mk.inj (Option.some.inj last)).1
    rw [←ht]
    exact shape_refl _
  · obtain ⟨base,hbase,rest⟩ := Option.bind_eq_some_iff.mp run
    cases base with
    | u64 n | i32 n | i64 n => contradiction
    | ptr address =>
      obtain ⟨index,hindex,rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨rhs,hrhs,rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨raw,hraw,rest⟩ := Option.bind_eq_some_iff.mp rest
      cases raw with
      | i32 n | i64 n | ptr n => contradiction
      | u64 word =>
        obtain ⟨i,hi,rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨after,hw,last⟩ := Option.bind_eq_some_iff.mp rest
        have ht : after=t.heap := congrArg State.heap (Prod.mk.inj (Option.some.inj last)).1
        rw [←ht]
        exact write_shape hw
  · obtain ⟨raw,hr,rest⟩ := Option.bind_eq_some_iff.mp run
    cases raw with
    | i32 n | i64 n | ptr n => contradiction
    | u64 old =>
      have ht : s.heap=t.heap := congrArg State.heap (Prod.mk.inj (Option.some.inj rest)).1
      rw [←ht]
      exact shape_refl _
  · obtain ⟨raw,hr,rest⟩ := Option.bind_eq_some_iff.mp run
    cases raw with
    | i32 n | i64 n | ptr n => contradiction
    | u64 old =>
      have ht : s.heap=t.heap := congrArg State.heap (Prod.mk.inj (Option.some.inj rest)).1
      rw [←ht]
      exact shape_refl _
  · obtain ⟨raw,hr,last⟩ := Option.bind_eq_some_iff.mp run
    have ht : s.heap=t.heap := congrArg State.heap (Prod.mk.inj (Option.some.inj last)).1
    rw [←ht]
    exact shape_refl _

lemma declare_heap {call : Service} {ds : List Decl} {s t : State}
    (run : Declare call ds s t) : t.heap=s.heap := by
  induction ds generalizing s with
  | nil =>
    have heq : s=t := Option.some.inj run
    exact (congrArg State.heap heq).symm
  | cons d ds ih =>
    unfold Declare declare at run
    simp only [List.foldlM] at run
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp run
    have hmid : mid.heap=s.heap := by
      split at first
      · contradiction
      · split at first
        · contradiction
        · obtain ⟨expression,hexpression,rest⟩ := Option.bind_eq_some_iff.mp first
          obtain ⟨raw,hraw,rest⟩ := Option.bind_eq_some_iff.mp rest
          obtain ⟨word,hword,last⟩ := Option.bind_eq_some_iff.mp rest
          exact (congrArg State.heap (Option.some.inj last)).symm
    exact (ih rest).trans hmid

#print axioms eval_shape
#print axioms declare_heap

end RamanujanPV.QuotientCHeapShape
