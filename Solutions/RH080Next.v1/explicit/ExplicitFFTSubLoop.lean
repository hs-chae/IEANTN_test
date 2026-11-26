/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTSubOperands
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def operandIds (first : Nat) : Operand → Nat | .left=>first | .right=>first+1

/-- Complete actual subtract-with-borrow body, including the three real
temporary births and the cmp-dependent source operand swap. -/
theorem sub_loop_body_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j : Nat} {li : Var → Nat}
    (h : View before input true (decide (input.cmp=0)) owner li j) (hj : j < 5) :
    ∃after,Exec context before subLoopBody .normal after ∧
      View after input true (decide (input.cmp=0)) owner li (j+1) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  let entered:=before.enterScope
  have a64 : input.a j < 2^64:=lt_trans (input.digitsA j hj) (by norm_num [base])
  have b64 : input.b j < 2^64:=lt_trans (input.digitsB j hj) (by norm_num [base])
  obtain ⟨leftBorn,declLeft⟩:=ZeroFrame.declare_exists h.enter.well .u64 "left" (.integer (integer64 (input.a j)))
    (ZeroFrame.u64_storable (input.a j) a64)
  have dl:=declare_storable (ZeroFrame.u64_storable (input.a j) a64) (convert64 (input.a j) a64) declLeft
  have ll:=ApplicationBirthFrame.locals_declare_old h.enter.well h.enter.locals (by intro v; cases v <;> decide) dl
  have al:=h.enter.arrays.declare_old h.enter.well dl
  have wl:=wellScoped_declare h.enter.well declLeft
  have hl : View leftBorn input true (decide (input.cmp=0)) owner li j:=⟨al,ll,h.separate,h.active,wl⟩
  obtain ⟨rightBorn,declRight⟩:=ZeroFrame.declare_exists wl .u64 "right" (.integer (integer64 (input.b j)))
    (ZeroFrame.u64_storable (input.b j) b64)
  have dr:=declare_storable (ZeroFrame.u64_storable (input.b j) b64) (convert64 (input.b j) b64) declRight
  have lr:=ApplicationBirthFrame.locals_declare_old wl ll (by intro v; cases v <;> decide) dr
  have ar:=al.declare_old wl dr
  have wr:=wellScoped_declare wl declRight
  have hr : View rightBorn input true (decide (input.cmp=0)) owner li j:=⟨ar,lr,h.separate,h.active,wr⟩
  have tmp : Locals rightBorn operandName operandType (operandIds entered.nextObject) entered.scope
      (operandValues (input.a j) (input.b j)) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro v
      cases v <;> simp [operandIds,operandName,operandType,dr.environment,dl.environment,dl.nextObject,List.lookup,scalarPointer,entered]
    · intro v
      cases v with
      | left=>simpa only [operandIds,operandType,operandValues] using ApplicationBirthFrame.slot_declare_old wl dl.slot dr
      | right=>simpa only [operandIds,operandType,operandValues,dl.nextObject,dl.scope] using dr.slot
    · intro v w eq
      cases v <;> cases w <;> simp_all [operandIds] <;> omega
    · rw [dr.nextScope,dl.nextScope]
      exact h.enter.well.current
  have different : ∀v w,li v≠operandIds entered.nextObject w := by
    intro v w
    have oldId:=h.well.objectIds (li v) _ (h.locals.slots v).object
    cases w with
    | left=>change li v≠before.nextObject; omega
    | right=>change li v≠before.nextObject+1; omega
  have born : ∀w,before.nextObject ≤ operandIds entered.nextObject w:=by intro w; cases w <;> simp [operandIds,entered,State.enterScope]
  have fresh : before.nextObject ≤ rightBorn.nextObject:=by rw [dr.nextObject,dl.nextObject]; change before.nextObject ≤ before.nextObject+1+1; omega
  obtain ⟨swapped,swapRun,hs,operands,swapFrame⟩:=swap_execution context hr hj tmp different born fresh
  let t:=digitTotal true (input.left (decide (input.cmp=0)) j) (input.right (decide (input.cmp=0)) j)
    (scan true (input.left (decide (input.cmp=0))) (input.right (decide (input.cmp=0))) j).2
  have ht : t < 2^64:=lt_trans (digitTotal_bounds true _ _ _ (input.left_bound _ j hj)
    (input.right_bound _ j hj) h.carry_bound).1 (by norm_num [base])
  have evalT : Eval context swapped subTExpr (.integer (integer64 t)) swapped:=sub_t_eval context hs hj
    (.variable (operands.lookup Operand.left) (operands.read Operand.left))
    (.variable (operands.lookup Operand.right) (operands.read Operand.right))
  obtain ⟨tBorn,declT⟩:=ZeroFrame.declare_exists hs.well .u64 "t" (.integer (integer64 t)) (ZeroFrame.u64_storable t ht)
  have dt:=declare_storable (ZeroFrame.u64_storable t ht) (convert64 t ht) declT
  have lt:=ApplicationBirthFrame.locals_declare_old hs.well hs.locals (by intro v; cases v <;> decide) dt
  have arrT:=hs.arrays.declare_old hs.well dt
  have wt:=wellScoped_declare hs.well declT
  have htView : View tBorn input true (decide (input.cmp=0)) owner li j:=⟨arrT,lt,h.separate,h.active,wt⟩
  have tNamed : tBorn.environment.lookup "t"=some (scalarPointer swapped.nextObject .u64):=by rw [dt.environment]; rfl
  obtain ⟨last,tailRun,post,tailFrame⟩:=digit_tail_execution context htView hj
    (cutoff:=before.nextObject) (by rw [dt.nextObject]; exact swapFrame.fresh.trans (Nat.le_succ _)) dt.slot tNamed
  have fl:=ApplicationBirthFrame.declare_frame before.nextObject (writes input li) h.enter.well (le_refl _) declLeft
  have fr:=ApplicationBirthFrame.declare_frame before.nextObject (writes input li) wl fl.fresh declRight
  have ft:=ApplicationBirthFrame.declare_frame before.nextObject (writes input li) hs.well swapFrame.fresh declT
  have whole:=fl.trans (fr.trans (swapFrame.trans (ft.trans tailFrame)))
  have bodyRun : ExecList context entered [
      .declare .u64 "left" (some (.index (.variable "a") (.variable "j"))),
      .declare .u64 "right" (some (.index (.variable "b") (.variable "j"))),swapBranch,
      .declare .u64 "t" (some subTExpr),digitStmt,carryStmt true,advanceStmt] .normal last:=
    .cons (.declareSome (left_eval context h.enter hj) declLeft)
      (.cons (.declareSome (right_eval context hl hj) declRight)
        (.cons swapRun (.cons (.declareSome evalT declT) tailRun)))
  obtain ⟨view,frame⟩:=close_view h post whole
  exact ⟨_,.block (by rfl) bodyRun (by rfl),view,frame⟩

theorem sub_loop_execution {F : Type} (context : Context F) (remaining : Nat) {before : State F} {input : Input}
    {owner j : Nat} {li : Var → Nat} (count : j+remaining=5)
    (h : View before input true (decide (input.cmp=0)) owner li j) :
    ∃after,Exec context before subLoop .normal after ∧ View after input true (decide (input.cmp=0)) owner li 5 ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  induction remaining generalizing before j with
  | zero=>
    have hj : j=5:=by omega
    subst j
    refine ⟨before,.whileFalse (condition_eval context h) ?_,h,ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _)⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
  | succ r ih=>
    have hj : j < 5:=by omega
    obtain ⟨middle,body,hm,first⟩:=sub_loop_body_execution context h hj
    obtain ⟨after,rest,ha,last⟩:=ih (by omega) hm
    have last':=IncrementSource.frame_restrict last first.nextObject
    refine ⟨after,.whileNext (condition_eval context h) ?_ body rest,ha,first.trans last'⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

#print axioms sub_loop_body_execution
#print axioms sub_loop_execution
end RH080Next.FFTPV.AddSource
