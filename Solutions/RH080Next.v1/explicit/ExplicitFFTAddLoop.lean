/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddTail
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem add_t_eval {F : Type} (context : Context F) {state : State F} {input : Input}
    {owner j : Nat} {li : Var → Nat} (h : View state input false false owner li j) (hj : j < 5) :
    Eval context state addTExpr (.integer (integer64
      (digitTotal false (input.left false j) (input.right false j) (scan false (input.left false) (input.right false) j).2))) state := by
  have ha:=input.digitsA j hj
  have hb:=input.digitsB j hj
  have hc:=h.carry_bound
  have a64 : input.a j < 2^64:=by dsimp [Input.a,base] at ha ⊢; omega
  have b64 : input.b j < 2^64:=by dsimp [Input.b,base] at hb ⊢; omega
  have sum64 : input.a j+input.b j < 2^64:=by change input.a j < base at ha; change input.b j < base at hb; dsimp [base] at ha hb; omega
  have c64 : (scan false (input.left false) (input.right false) j).2 < 2^64:=by omega
  have total64 : input.a j+input.b j+(scan false (input.left false) (input.right false) j).2 < 2^64 := by
    change input.a j < base at ha
    change input.b j < base at hb
    dsimp [base] at ha hb
    omega
  have pair : Eval context state (.paren (.binary .add (.index (.variable "a") (.variable "j"))
      (.index (.variable "b") (.variable "j")))) (.integer (integer64 (input.a j+input.b j))) state:=
    .paren (.binaryLR (left_eval context h hj) (right_eval context h hj)
      (by simp only [binary,binary64_add _ _ a64 b64 sum64,Option.map_some]))
  exact .paren (.binaryLR pair (.variable (h.locals.lookup Var.carry) (h.locals.read Var.carry))
    (congrArg (Option.map Value.integer) (binary64_add (input.a j+input.b j)
      (scan false (input.left false) (input.right false) j).2 sum64 c64 total64)))

theorem close_view {F : Type} {before middle : State F} {input : Input} {sub swap : Bool}
    {owner j k : Nat} {li : Var → Nat}
    (h : View before input sub swap owner li j) (hm : View middle input sub swap owner li k)
    (frame : ApplicationBirthFrame.Frame before.nextObject before.enterScope middle (writes input li)) :
    View {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      input sub swap owner li k ∧
    ApplicationBirthFrame.Frame before.nextObject before
      {middle.leaveScope before.nextScope before.environment with scope:=before.scope} (writes input li) := by
  have full:=ApplicationBirthFrame.close_frame h.well (le_refl _) frame
  have different : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
  exact ⟨⟨hm.arrays.leave,hm.locals.leave different before.environment h.locals.lookup before.scope,
    h.separate,hm.active,full.well⟩,full⟩

/-- Actual same-sign source loop body, with fully proved identical-slice
aliasing, temporary allocation and all unsigned arithmetic operations. -/
theorem add_loop_body_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j : Nat} {li : Var → Nat} (h : View before input false false owner li j) (hj : j < 5) :
    ∃after,Exec context before addLoopBody .normal after ∧ View after input false false owner li (j+1) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  let entered:=before.enterScope
  let t:=digitTotal false (input.left false j) (input.right false j) (scan false (input.left false) (input.right false) j).2
  have ht : t < 2^64:=lt_trans (digitTotal_bounds false _ _ _ (input.left_bound false j hj)
    (input.right_bound false j hj) h.carry_bound).1 (by norm_num [base])
  obtain ⟨middle,declared⟩:=ZeroFrame.declare_exists h.enter.well .u64 "t" (.integer (integer64 t)) (ZeroFrame.u64_storable t ht)
  have dt:=declare_storable (ZeroFrame.u64_storable t ht) (convert64 t ht) declared
  have lm:=ApplicationBirthFrame.locals_declare_old h.enter.well h.enter.locals (by intro v; cases v <;> decide) dt
  have am:=h.enter.arrays.declare_old h.enter.well dt
  have wm:=wellScoped_declare h.enter.well declared
  have hm : View middle input false false owner li j:=⟨am,lm,h.separate,h.active,wm⟩
  have named : middle.environment.lookup "t"=some (scalarPointer entered.nextObject .u64):=by rw [dt.environment]; rfl
  obtain ⟨last,tailRun,post,lastFrame⟩:=digit_tail_execution context hm hj
    (cutoff:=before.nextObject) (by rw [dt.nextObject]; change before.nextObject ≤ before.nextObject+1; omega) dt.slot named
  have declaredFrame:=ApplicationBirthFrame.declare_frame before.nextObject (writes input li) h.enter.well (le_refl _) declared
  have bodyRun : ExecList context entered [.declare .u64 "t" (some addTExpr),digitStmt,carryStmt false,advanceStmt] .normal last:=
    .cons (.declareSome (add_t_eval context h.enter hj) declared) tailRun
  obtain ⟨view,frame⟩:=close_view h post (declaredFrame.trans lastFrame)
  exact ⟨_,.block (by rfl) bodyRun (by rfl),view,frame⟩

theorem add_loop_execution {F : Type} (context : Context F) (remaining : Nat) {before : State F} {input : Input}
    {owner j : Nat} {li : Var → Nat} (count : j+remaining=5) (h : View before input false false owner li j) :
    ∃after,Exec context before addLoop .normal after ∧ View after input false false owner li 5 ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  induction remaining generalizing before j with
  | zero=>
    have hj : j=5:=by omega
    subst j
    refine ⟨before,.whileFalse (condition_eval context h) ?_,h,ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _)⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
  | succ r ih=>
    have hj : j < 5:=by omega
    obtain ⟨middle,body,hm,first⟩:=add_loop_body_execution context h hj
    obtain ⟨after,rest,ha,last⟩:=ih (by omega) hm
    have last':=IncrementSource.frame_restrict last first.nextObject
    refine ⟨after,.whileNext (condition_eval context h) ?_ body rest,ha,first.trans last'⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

#print axioms add_t_eval
#print axioms add_loop_body_execution
#print axioms add_loop_execution
end RH080Next.FFTPV.AddSource
