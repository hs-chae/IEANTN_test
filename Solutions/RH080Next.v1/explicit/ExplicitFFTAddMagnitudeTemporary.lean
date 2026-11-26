/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudePrefix
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def total (input : Input) (j : Nat) : Nat:=input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j+(row input j).2

theorem total_bound (input : Input) (j : Nat) (hj : j< input.layout.n) : total input j<2*base:=by
  have a:=input.outDigits j hj;have b:=aDigit_bound input j;have c:=row_carry input j hj.le
  unfold total;omega

structure TView {F : Type} (state : State F) (input : Input) (owner xId tId xOwner : Nat) (li : Var → Nat) (j : Nat) : Prop extends XView state input owner xId xOwner li j (aDigit input j) where
  tSlot : Slot state tId xOwner .u64 (.integer (integer64 (total input j)))
  tLookup : state.environment.lookup "t"=some (scalarPointer tId .u64)
  tDifferent : ∀v,li v≠tId
  tOut : input.layout.outObject≠tId
  tInput : input.layout.aObject≠tId

theorem t_declare {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner xId xOwner j : Nat} {li : Var → Nat}
    (h : XView before input owner xId xOwner li j (aDigit input j)) (scope : xOwner=before.scope) (hj : j< input.layout.n) :
    ∃after,Exec context before (.declare .u64 "t" (some tExpr)) .normal after ∧
      TView after input owner xId before.nextObject xOwner li j ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  have bound : input.layout.outStart+j< input.layout.length input.layout.outObject:=by have b:=input.layout.outBound;omega
  have total64 : total input j<2^64:=lt_trans (total_bound input j hj) (by norm_num [base])
  have out64 : input.old input.layout.outObject (input.layout.outStart+j)<2^64:=lt_trans (input.outDigits j hj) (by norm_num [base])
  have a64 : aDigit input j<2^64:=lt_trans (aDigit_bound input j) (by norm_num [base])
  have carry64 : (row input j).2<2^64:=by have c:=row_carry input j hj.le;omega
  have plus64 : input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j<2^64:=by have ht:=total_bound input j hj;unfold total at ht;norm_num [base] at ht ⊢;omega
  have readOut : Eval context before (.index (.variable "out") (.variable "i"))
      (.integer (integer64 (input.old input.layout.outObject (input.layout.outStart+j)))) before:=by
    apply Eval.load (.index (.variable (h.locals.lookup Var.out) (h.locals.read Var.out))
      (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (slice_pointer_add h.array bound))
    simpa only [currentData_unread input j j (le_refl _)] using slice_word_load h.array bound
  have plus : Eval context before (.paren (.binary .add (.index (.variable "out") (.variable "i")) (.variable "x")))
      (.integer (integer64 (input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j))) before:=
    .paren (.binaryLR readOut (.variable h.xLookup h.xSlot.read)
      (by simp only [binary,binary64_add _ _ out64 a64 plus64,Option.map_some]))
  have evaluated : Eval context before tExpr (.integer (integer64 (total input j))) before:=by
    apply Eval.paren
    apply Eval.binaryLR plus (.variable (h.locals.lookup Var.carry) (h.locals.read Var.carry))
    simp only [values,binary,binary64_add _ _ plus64 carry64 total64,Option.map_some,total]
  obtain ⟨after,d⟩:=ZeroFrame.declare_exists h.well _ "t" _ (ZeroFrame.u64_storable _ total64)
  have info:=declare_storable (ZeroFrame.u64_storable _ total64) (convert64 _ total64) d
  have array:=ApplicationBirthFrame.array_declare_old h.well h.array info
  obtain ⟨data,aRep,aRead⟩:=h.inputArray
  have aRep':=ApplicationBirthFrame.array_declare_old h.well aRep info
  have locals:=ApplicationBirthFrame.locals_declare_old h.well h.locals (by intro v;cases v <;> decide) info
  have xSlot:=ApplicationBirthFrame.slot_declare_old h.well h.xSlot info
  have oldOut:=h.well.objectIds _ _ h.array.2.1
  have oldA:=h.well.objectIds _ _ aRep.2.1
  refine ⟨after,.declareSome evaluated d,⟨⟨⟨array,⟨_,aRep',aRead⟩,locals,h.separate,h.active,wellScoped_declare h.well d⟩,
    xSlot,?_,h.different,h.xOut,h.xInput⟩,?_,?_,?_,by omega,by omega⟩,
    ApplicationBirthFrame.declare_frame _ _ h.well (le_refl _) d,info.scope⟩
  · rw [info.environment];simpa [List.lookup] using h.xLookup
  · simpa only [scope] using info.slot
  · rw [info.environment];simp [List.lookup]
  · intro v;exact (h.well.objectIds _ _ (h.locals.slots v).object).ne

#print axioms t_declare
end RH080Next.FFTPV.AddMagnitudeSource
