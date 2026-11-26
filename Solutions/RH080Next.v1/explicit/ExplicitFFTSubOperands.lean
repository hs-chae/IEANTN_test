/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTSubExpression
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

inductive Operand where | left | right deriving DecidableEq
def operandName : Operand → String | .left=>"left" | .right=>"right"
def operandType (_ : Operand) : CType:=.u64
def operandValues (a b : Nat) : Operand → Value | .left=>.integer (integer64 a) | .right=>.integer (integer64 b)

theorem operand_left_update (a b c : Nat) :
    Function.update (operandValues a b) .left (.integer (integer64 c))=operandValues c b := by
  funext v; cases v <;> rfl
theorem operand_right_update (a b c : Nat) :
    Function.update (operandValues a b) .right (.integer (integer64 c))=operandValues a c := by
  funext v; cases v <;> rfl

/-- The actual cmp-dependent operand swap writes the real outer-loop
temporary slots; the extra branch scope is entered and closed explicitly. -/
theorem swap_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j tmpOwner cutoff : Nat} {li : Var → Nat} {ti : Operand → Nat}
    (h : View before input true (decide (input.cmp=0)) owner li j) (hj : j < 5)
    (tmp : Locals before operandName operandType ti tmpOwner (operandValues (input.a j) (input.b j)))
    (different : ∀v w,li v≠ti w) (born : ∀w,cutoff ≤ ti w) (fresh : cutoff ≤ before.nextObject) :
    ∃after,Exec context before swapBranch .normal after ∧
      View after input true (decide (input.cmp=0)) owner li j ∧
      Locals after operandName operandType ti tmpOwner
        (operandValues (input.left (decide (input.cmp=0)) j) (input.right (decide (input.cmp=0)) j)) ∧
      ApplicationBirthFrame.Frame cutoff before after (writes input li) := by
  by_cases he : input.cmp=0
  · have b64 : input.b j < 2^64:=lt_trans (input.digitsB j hj) (by norm_num [base])
    have a64 : input.a j < 2^64:=lt_trans (input.digitsA j hj) (by norm_num [base])
    have sb:=ZeroFrame.u64_storable (input.b j) b64
    obtain ⟨middle,storeLeft⟩:=IncrementSource.slot_store_exists (tmp.enter.slots Operand.left) (.integer (integer64 (input.b j))) sb
    have leftRun : Exec context before.enterScope
        (.assign (.variable "left") (.index (.variable "b") (.variable "j"))) .normal middle :=
      .assign (right_eval context h.enter hj) (Place.variable (tmp.enter.lookup Operand.left)) storeLeft
    have lm:=ApplicationBirthFrame.locals_store_other h.enter.locals (fun v=>different v .left) storeLeft
    have am:=h.enter.arrays.store_other
      (fun r=>(scalar_array_ne (tmp.enter.slots Operand.left) (h.enter.arrays r)).symm) storeLeft
    have tm : Locals middle operandName operandType ti tmpOwner (operandValues (input.b j) (input.b j)) := by
      simpa only [operand_left_update] using tmp.enter.store Operand.left _ sb storeLeft
    have first:=ApplicationBirthFrame.store_frame cutoff (writes input li) h.enter.well fresh (Or.inr (born .left)) storeLeft
    have hm : View middle input true (decide (input.cmp=0)) owner li j:=⟨am,lm,h.separate,h.active,first.well⟩
    have sa:=ZeroFrame.u64_storable (input.a j) a64
    obtain ⟨last,storeRight⟩:=IncrementSource.slot_store_exists (tm.slots Operand.right) (.integer (integer64 (input.a j))) sa
    have rightRun : Exec context middle
        (.assign (.variable "right") (.index (.variable "a") (.variable "j"))) .normal last:=
      .assign (left_eval context hm hj) (Place.variable (tm.lookup Operand.right)) storeRight
    have la:=ApplicationBirthFrame.locals_store_other lm (fun v=>different v .right) storeRight
    have aa:=am.store_other (fun r=>(scalar_array_ne (tm.slots Operand.right) (am r)).symm) storeRight
    have ta : Locals last operandName operandType ti tmpOwner (operandValues (input.b j) (input.a j)) := by
      simpa only [operand_right_update] using tm.store Operand.right _ sa storeRight
    have lastFrame:=ApplicationBirthFrame.store_frame cutoff (writes input li) first.well first.fresh (Or.inr (born .right)) storeRight
    have fr:=ApplicationBirthFrame.close_frame h.well fresh (first.trans lastFrame)
    let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
    have bodyRun : Exec context before (.block [
        .assign (.variable "left") (.index (.variable "b") (.variable "j")),
        .assign (.variable "right") (.index (.variable "a") (.variable "j"))]) .normal after:=
      .block (by rfl) (.cons leftRun (.cons rightRun .nil)) (by rfl)
    have ownerDifferent : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
    have tmpDifferent : before.nextScope≠tmpOwner:=by have ho:=tmp.bound; omega
    have post : View after input true (decide (input.cmp=0)) owner li j:=
      ⟨aa.leave,la.leave ownerDifferent before.environment h.locals.lookup before.scope,h.separate,h.active,fr.well⟩
    have temp : Locals after operandName operandType ti tmpOwner (operandValues (input.b j) (input.a j)):=
      ta.leave tmpDifferent before.environment tmp.lookup before.scope
    refine ⟨after,.ifTrue (cmp_eval context h) ?_ bodyRun,post,?_,fr⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,he]
    · simpa [Input.left,Input.right,he] using temp
  · refine ⟨before,.ifFalse (cmp_eval context h) ?_,h,?_,ApplicationBirthFrame.Frame.refl _ _ h.well fresh⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,he]
    · simpa [Input.left,Input.right,he] using tmp

#print axioms swap_execution
end RH080Next.FFTPV.AddSource
