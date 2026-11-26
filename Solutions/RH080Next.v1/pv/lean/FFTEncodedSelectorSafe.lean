/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelector
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect

def Tree.Safe : Tree→Prop
  | .leaf v=>v<2^64
  | .branch cut left right=>cut<2^64 ∧ left.Safe ∧ right.Safe

theorem Tree.value_safe {tree : Tree} (safe : tree.Safe) (j : Nat) : tree.value j<2^64:=by
  induction tree with
  | leaf v=>exact safe
  | branch cut left right ihl ihr=>
    unfold Tree.value
    split
    · exact ihl safe.2.1
    · exact ihr safe.2.2

theorem build_safe (fuel base : Nat) (values : List Nat)
    (range : base+values.length<2^64) (safe : ∀v∈values,v<2^64) : (build fuel base values).Safe:=by
  have headSafe : values.headD 0<2^64:=by
    cases values with
    | nil=>norm_num
    | cons x xs=>exact safe x List.mem_cons_self
  induction fuel generalizing base values with
  | zero=>exact headSafe
  | succ fuel ih=>
    simp only [build]
    split
    · exact headSafe
    · rename_i long
      let split:=values.length/2
      have less : split<values.length:=by dsimp [split];omega
      have below : split≤values.length:=by omega
      have leftLength : (values.take split).length=split:=by simp [List.length_take,Nat.min_eq_left below]
      have rightLength : (values.drop split).length=values.length-split:=by simp
      refine ⟨by dsimp [split];omega,?_,?_⟩
      · apply ih base (values.take split)
        · rw [leftLength];omega
        · intro v member
          exact safe v (List.mem_of_mem_take member)
        · have : (values.take split).headD 0<2^64:=by
            cases h : values.take split with
            | nil=>norm_num
            | cons x xs=>exact safe x (List.mem_of_mem_take (by rw [h];simp))
          exact this
      · apply ih (base+split) (values.drop split)
        · rw [rightLength];omega
        · intro v member
          exact safe v (List.mem_of_mem_drop member)
        · have : (values.drop split).headD 0<2^64:=by
            cases h : values.drop split with
            | nil=>norm_num
            | cons x xs=>exact safe x (List.mem_of_mem_drop (by rw [h];simp))
          exact this

#print axioms build_safe
#print axioms Tree.value_safe
end RH080Next.FFTPV.EncodedSelector
