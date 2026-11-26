/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

theorem values_carry_update (object start n factor j c d : Nat) :
    Function.update (values object start n factor j c) .carry (.integer (integer64 d)) =
      values object start n factor j d := by funext i; cases i <;> rfl

theorem values_j_update (object start n factor j c k : Nat) :
    Function.update (values object start n factor j c) .j (.integer (integer64 k)) =
      values object start n factor k c := by funext i; cases i <;> rfl

/-- Every statement of the actual small-factor multiplication loop body, including temporary
allocation, carry and counter stores, is executed under the word semantics. -/
theorem body_list_execution {F : Type} (context : Context F) {before : State F}
    {object length start n factor owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n factor owner li old j) (hj : j < n) :
    ∃after,
      ExecList context before [.declare .u64 "t" (some tExpr),digitStmt,carryStmt,advanceStmt] .normal after ∧
      View after object length start n factor owner li old (j+1) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  obtain ⟨middle,preRun,rm,lm,tm,tNamed,frame⟩:=digit_prefix_execution context h hj
  let t:=old (start+j)*factor+(scaledRow old start factor j).2
  have hd:=h.digits j hj
  have hc:=h.carry_bound
  have ht : t < 2^64 := h.total_safe hj
  have hq : t/base≤factor := by
    have bounds:=row_carry_le old start factor (j+1) (fun i hi=>h.digits i (by omega))
    simpa only [row_step] using bounds
  have hv:=ZeroFrame.u64_storable (t/base) (by have hf:=h.factorSmall;dsimp [base] at hf;omega)
  obtain ⟨carried,storeCarry⟩:=slot_store_exists (lm.slots Var.carry) (.integer (integer64 (t/base))) hv
  have readT : Eval context middle (.variable "t") (.integer (integer64 t)) middle :=
    .variable tNamed tm.read
  have carryRun : Exec context middle carryStmt .normal carried := by
    apply Exec.assign (value:=.integer (integer64 (t/base)))
      (Eval.paren (Eval.binaryLR readT
        (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl))
        (by simp only [binary,binary64_div t base ht (by norm_num [base]) (by norm_num [base]),Option.map_some])))
      (Place.variable (lm.lookup Var.carry))
    exact storeCarry
  have lc : Locals carried name type li owner (values object start n factor j (t/base)) := by
    simpa only [values_carry_update] using lm.store Var.carry (.integer (integer64 (t/base))) hv storeCarry
  have rc:=array_store_other rm (h.separate Var.carry) storeCarry
  have fc:=ApplicationBirthFrame.store_frame before.nextObject (writes object li) frame.well frame.fresh
    (Or.inl (by simp [writes,scalarPointer])) storeCarry
  have hj64 : j < 2^64 := by have hn:=h.small; omega
  have hj1 : j+1 < 2^64 := by have hn:=h.small; omega
  have storable:=ZeroFrame.u64_storable (j+1) hj1
  obtain ⟨after,storeJ⟩:=slot_store_exists (lc.slots Var.j) (.integer (integer64 (j+1))) storable
  have advanceRun : Exec context carried advanceStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (j+1)))
      (Eval.paren (Eval.binaryLR (.variable (lc.lookup Var.j) (lc.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add j 1 hj64 (by norm_num) hj1,Option.map_some])))
      (Place.variable (lc.lookup Var.j))
    exact storeJ
  have la : Locals after name type li owner (values object start n factor (j+1) (t/base)) := by
    simpa only [values_j_update] using lc.store Var.j (.integer (integer64 (j+1))) storable storeJ
  have ra:=array_store_other rc (h.separate Var.j) storeJ
  have fj:=ApplicationBirthFrame.store_frame before.nextObject (writes object li) fc.well fc.fresh
    (Or.inl (by simp [writes,scalarPointer])) storeJ
  have whole:=frame.trans (fc.trans fj)
  have la' : Locals after name type li owner
      (values object start n factor (j+1) (scaledRow old start factor (j+1)).2)  := by simpa only [row_step] using la
  have run : ExecList context before [.declare .u64 "t" (some tExpr),digitStmt,carryStmt,advanceStmt]
      .normal after := by
    cases preRun with
    | cons a rest =>
      cases rest with
      | cons b tail =>
        cases tail
        exact .cons a (.cons b (.cons carryRun (.cons advanceRun .nil)))
      | abrupt run bad => exact False.elim (bad rfl)
    | abrupt run bad => exact False.elim (bad rfl)
  exact ⟨after,run,⟨ra,la',h.separate,h.bound,h.small,by omega,h.digits,h.factorSmall,whole.well⟩,whole⟩

theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String×Pointer)} {data : Nat → Nat}
    (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data := by
  refine ⟨h.1,?_,h.2.2⟩
  change (state.objects object).map _=some (wordObject size data)
  rw [h.2.1]
  simp [wordObject]

/-- Scope exit kills only the real temporary; prior heap data and all
persistent function locals remain available for the next source iteration. -/
theorem loop_body_execution {F : Type} (context : Context F) {before : State F}
    {object length start n factor owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n factor owner li old j) (hj : j < n) :
    ∃after,Exec context before loopBody .normal after ∧
      View after object length start n factor owner li old (j+1) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  obtain ⟨middle,run,hm,frame⟩:=body_list_execution context h.enter hj
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have result : Exec context before loopBody .normal after := .block (by rfl) run (by rfl)
  have full:=ApplicationBirthFrame.close_frame h.well (le_refl _) frame
  have different : before.nextScope ≠ owner := by have ho:=h.locals.bound; omega
  have locals:=hm.locals.leave different before.environment h.locals.lookup before.scope
  exact ⟨after,result,⟨wordArray_leave hm.array,locals,h.separate,h.bound,h.small,by omega,h.digits,h.factorSmall,full.well⟩,full⟩

#print axioms body_list_execution
#print axioms loop_body_execution
end RH080Next.FFTPV.MultiplySmallSource
