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
    change (if base%8=0 ∧ index<block.extent ∧ base+8*index+8 ≤ modulus ∧ value<modulus then
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
  all_goals trace_state

end RamanujanPV.QuotientCHeapShape
