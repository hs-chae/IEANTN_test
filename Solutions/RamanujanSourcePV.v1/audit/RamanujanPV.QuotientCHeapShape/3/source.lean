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
    have ht := congrArg State.heap (Prod.mk.inj (Option.some.inj last)).1
    change s.heap=t.heap at ht
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
      have ht := congrArg State.heap (Prod.mk.inj (Option.some.inj rest)).1
      change s.heap=t.heap at ht
      rw [←ht]
      exact shape_refl _
  · obtain ⟨raw,hr,rest⟩ := Option.bind_eq_some_iff.mp run
    cases raw with
    | i32 n | i64 n | ptr n => contradiction
    | u64 old =>
      have ht := congrArg State.heap (Prod.mk.inj (Option.some.inj rest)).1
      change s.heap=t.heap at ht
      rw [←ht]
      exact shape_refl _
  · obtain ⟨raw,hr,last⟩ := Option.bind_eq_some_iff.mp run
    have ht := congrArg State.heap (Prod.mk.inj (Option.some.inj last)).1
    change s.heap=t.heap at ht
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

def flowHeap : Flow → Heap
  | .continuing t | .returned t _ => t.heap

lemma scope_heap {s : State} {inner out : Flow} (scope : Scope s inner out) :
    flowHeap out=flowHeap inner := by
  rw [scope]
  cases inner <;> rfl

lemma guard_shape {call : Service} {cond : Option Expr} {s t : State} {flag : Bool}
    (run : GuardRun (Eval call) truth cond s t flag) : SameShape s.heap t.heap := by
  cases run with
  | omitted => exact shape_refl _
  | present h => exact eval_shape h

/-- Every selected core source statement preserves allocation identity and
extents. It may change word contents; no initial table representation or desired
count is assumed. In particular, a fresh stack-result allocation remains absent. -/
theorem run_shape {call : Service} {body : Stmt} {s : State} {out : Flow}
    (run : Run call body s out) : SameShape s.heap (flowHeap out) := by
  refine StmtRun.rec
    (motive_1:=fun body s out _ => SameShape s.heap (flowHeap out))
    (motive_2:=fun body s out _ => SameShape s.heap (flowHeap out))
    (motive_3:=fun cond step body s out _ => SameShape s.heap (flowHeap out))
    (motive_4:=fun cond body s out _ => SameShape s.heap (flowHeap out))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ run
  · intro s
    exact shape_refl _
  · intro e s t value h
    exact eval_shape h
  · intro ds s t h
    change SameShape s.heap t.heap
    rw [declare_heap h]
    exact shape_refl _
  · intro e s t value h
    exact eval_shape h
  · intro e yes no s t value result test body ih
    exact shape_trans (eval_shape test) ih
  · intro body s inner result first scope ih
    rw [scope_heap scope]
    exact ih
  · intro init cond step body s t inner result first loop scope ihFirst ihLoop
    rw [scope_heap scope]
    exact shape_trans ihFirst ihLoop
  · intro init cond step body s t value result first scope ih
    rw [scope_heap scope]
    exact ih
  · intro cond body s out loop ih
    exact ih
  · intro s
    exact shape_refl _
  · intro head tail s t out first rest ihFirst ihRest
    exact shape_trans ihFirst ihRest
  · intro head tail s t value first ih
    exact ih
  · intro cond step body s t test
    exact guard_shape test
  · intro cond step body s t b c value result test iteration increment rest ihIter ihRest
    exact shape_trans (guard_shape test) (shape_trans ihIter (shape_trans (eval_shape increment) ihRest))
  · intro cond step body s t b value test iteration ih
    exact shape_trans (guard_shape test) ih
  · intro cond body s t value test stop
    exact eval_shape test
  · intro cond body s t b value result test go iteration rest ihIter ihRest
    exact shape_trans (eval_shape test) (shape_trans ihIter ihRest)
  · intro cond body s t b condition value test go iteration ih
    exact shape_trans (eval_shape test) ih

lemma absent_preserved {before after : Heap} (shape : SameShape before after) {base : Nat}
    (fresh : before base=none) : after base=none := by
  have h := shape base
  rw [fresh] at h
  cases ha : after base with
  | none => rfl
  | some block => simp [ha] at h

lemma extent_preserved {before after : Heap} (shape : SameShape before after) {base : Nat}
    {block : Block} (hb : before base=some block) :
    ∃ next, after base=some next ∧ next.extent=block.extent := by
  have h := shape base
  rw [hb] at h
  cases ha : after base with
  | none => simp [ha] at h
  | some next => exact ⟨next,ha,by simpa [ha] using h.symm⟩

#print axioms run_shape
#print axioms eval_shape
#print axioms declare_heap

end RamanujanPV.QuotientCHeapShape
