/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem values_remainder_update (object start n d ceiling j r q : Nat) :
    Function.update (values object start n d ceiling j r) .rem (.integer (integer64 q))=
      values object start n d ceiling j q := by funext i; cases i <;> rfl

theorem body_list_execution {F : Type} (context : Context F) {before : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old (j+1)) :
    ∃after,ExecList context before [decrement,.declare .u64 "t" (some tExpr),digitStmt,remainderStmt] .normal after ∧
      View after object length start n d ceiling owner li old j ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  obtain ⟨middle,tId,tOwner,preRun,rm,lm,tm,tNamed,frame⟩:=digit_prefix_execution context h
  have hj : j < n := by have hn:=h.active; omega
  let r:=(division old start n d (j+1)).2
  let t:=r*base+old (start+j)
  have hr : r < d:=division_remainder_lt old start n d (j+1) h.divisor_positive
  have hd:=h.digits j hj
  have hdb:=h.divisor_bound
  have ht : t < 2^64 := by dsimp [t,base]; dsimp [base] at hdb hd; omega
  have d64 : d < 2^64 := by dsimp [base] at hdb; omega
  have hrem : t%d < 2^64:=lt_trans (Nat.mod_lt t h.divisor_positive) d64
  have storable:=ZeroFrame.u64_storable (t%d) hrem
  obtain ⟨after,stored⟩:=IncrementSource.slot_store_exists (lm.slots Var.rem) (.integer (integer64 (t%d))) storable
  have readT : Eval context middle (.variable "t") (.integer (integer64 t)) middle:=.variable tNamed tm.read
  have run : Exec context middle remainderStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (t%d)))
      (Eval.paren (.binaryLR readT (.variable (lm.lookup Var.d) (lm.read Var.d))
        (by simp only [values,binary,binary64_mod t d ht d64 h.divisor_positive,Option.map_some])))
      (Place.variable (lm.lookup Var.rem))
    exact stored
  have la : Locals after name type li owner (values object start n d ceiling j (t%d)) := by
    simpa only [values_remainder_update] using lm.store Var.rem (.integer (integer64 (t%d))) storable stored
  have la' : Locals after name type li owner (values object start n d ceiling j (division old start n d j).2) := by
    simpa only [division_step old start n d j hj] using la
  have ra:=IncrementSource.array_store_other rm (h.separate Var.rem) stored
  have last:=ApplicationBirthFrame.store_frame before.nextObject (writes object li) frame.well frame.fresh
    (Or.inl (by simp [writes,scalarPointer])) stored
  have whole:=frame.trans last
  have bodyRun : ExecList context before [decrement,.declare .u64 "t" (some tExpr),digitStmt,remainderStmt] .normal after := by
    cases preRun with
    | cons a rest=>
      cases rest with
      | cons b rest'=>
        cases rest' with
        | cons c tail=>
          cases tail
          exact .cons a (.cons b (.cons c (.cons run .nil)))
        | abrupt run bad=>exact False.elim (bad rfl)
      | abrupt run bad=>exact False.elim (bad rfl)
    | abrupt run bad=>exact False.elim (bad rfl)
  exact ⟨after,bodyRun,⟨ra,la',h.separate,h.bound,h.small,by have hn:=h.active; omega,
    h.digits,h.divisor_positive,h.divisor_bound,h.ceiling_bound,whole.well⟩,whole⟩

/-- Actual reverse division iteration with its genuine temporary lifetime. -/
theorem loop_body_execution {F : Type} (context : Context F) {before : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old (j+1)) :
    ∃after,Exec context before loopBody .normal after ∧
      View after object length start n d ceiling owner li old j ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  obtain ⟨middle,run,hm,frame⟩:=body_list_execution context h.enter
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have result : Exec context before loopBody .normal after:=.block (by rfl) run (by rfl)
  have full:=ApplicationBirthFrame.close_frame h.well (le_refl _) frame
  have different : before.nextScope ≠ owner:=by have ho:=h.locals.bound; omega
  have locals:=hm.locals.leave different before.environment h.locals.lookup before.scope
  exact ⟨after,result,⟨IncrementSource.wordArray_leave hm.array,locals,h.separate,h.bound,h.small,
    by have hn:=h.active; omega,h.digits,h.divisor_positive,h.divisor_bound,h.ceiling_bound,full.well⟩,full⟩

theorem loop_execution {F : Type} (context : Context F) (j : Nat) {before : State F}
    {object length start n d ceiling owner : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old j) :
    ∃after,Exec context before loop .normal after ∧
      View after object length start n d ceiling owner li old 0 ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  induction j generalizing before with
  | zero=>
    refine ⟨before,.whileFalse (condition_eval context h) ?_,h,ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _)⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
  | succ j ih=>
    obtain ⟨middle,body,hm,first⟩:=loop_body_execution context h
    obtain ⟨after,rest,ha,last⟩:=ih hm
    have last':=IncrementSource.frame_restrict last first.nextObject
    refine ⟨after,.whileNext (condition_eval context h) ?_ body rest,ha,first.trans last'⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]

theorem actual_body_unique {F : Type} (context : Context F) : CompareSource.Unique context loopBody := by
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    exact fun first second=>PureDeterminism.simple_unique
      (by simp [PureDeterminism.Simple,SourcePure.CallFree,decrement,tExpr,digitStmt,remainderStmt]) first second

theorem actual_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop :=
  CompareSource.while_unique (by simp [condition,SourcePure.CallFree]) (actual_body_unique context)

#print axioms body_list_execution
#print axioms loop_body_execution
#print axioms loop_execution
#print axioms actual_loop_unique
end RH080Next.FFTPV.DivideSource
