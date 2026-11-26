/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeStore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem counters_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner tId tOwner j : Nat} {li : Var → Nat}
    (array : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (currentData input (j+1)))
    (inputArray : ∃data,WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) data ∧
      ∀k<5,data (input.layout.aStart+k)=input.old input.layout.aObject (input.layout.aStart+k))
    (locals : Locals before name ctype li owner (values input j))
    (separate : ∀v,input.layout.outObject≠li v ∧ input.layout.aObject≠li v)
    (slot : Slot before tId tOwner .u64 (.integer (integer64 (total input j))))
    (lookup : before.environment.lookup "t"=some (scalarPointer tId .u64)) (well : WellScoped before)
    (minId : ∀v,li .out≤li v) (hj : j< input.layout.n) :
    ∃after,ExecList context before [carryStmt,advanceStmt] .normal after ∧ View after input owner li (j+1) ∧
      ApplicationBirthFrame.Frame (li .out) before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  have total64 : total input j<2^64:=lt_trans (total_bound input j hj) (by norm_num [base])
  have c64 : total input j/base<2^64:=lt_of_le_of_lt (Nat.div_le_self _ _) total64
  have j64 : j<2^64:=by have n:=input.layout.small;omega
  have next64 : j+1<2^64:=by have n:=input.layout.small;omega
  obtain ⟨middle,carryStored⟩:=MultiplySmallSource.slot_store_exists (locals.slots Var.carry) (.integer (integer64 (total input j/base))) (ZeroFrame.u64_storable _ c64)
  have carryRun : Exec context before carryStmt .normal middle:=.assign
    (.paren (.binaryLR (.variable lookup slot.read)
      (.literal (.integer base "ULL") _ (.integer (integer64 base)) (by rfl))
      (by simp only [binary,binary64_div _ _ total64 (show base<2^64 by norm_num [base]) (show 0<base by norm_num [base]),Option.map_some])))
    (.variable (locals.lookup Var.carry)) carryStored
  have carried:=locals.store Var.carry (.integer (integer64 (total input j/base))) (ZeroFrame.u64_storable _ c64) carryStored
  have outMiddle:=array_store_other array (by simpa only [scalarPointer] using (separate Var.carry).1) carryStored
  obtain ⟨aData,aRep,aRead⟩:=inputArray
  have aMiddle:=array_store_other aRep (by simpa only [scalarPointer] using (separate Var.carry).2) carryStored
  have wi:=wellScoped_store well carryStored
  have iSlot : Slot middle (li Var.i) owner .u64 (.integer (integer64 j)):=by
    simpa only [Function.update_of_ne (show Var.i≠Var.carry by decide),values,ctype] using carried.slots Var.i
  obtain ⟨after,iStored⟩:=MultiplySmallSource.slot_store_exists iSlot (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ next64)
  have iEval : Eval context middle (.variable "i") (.integer (integer64 j)) middle:=
    .variable (carried.lookup Var.i) iSlot.read
  have iRun : Exec context middle advanceStmt .normal after:=.assign
    (.paren (.binaryLR iEval (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [binary,binary64_add _ _ j64 (show 1<2^64 by norm_num) next64,Option.map_some])))
    (.variable (carried.lookup Var.i)) iStored
  have advanced:=carried.store Var.i (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ next64) iStored
  have valueEq : Function.update (Function.update (values input j) Var.carry (.integer (integer64 (total input j/base)))) Var.i (.integer (integer64 (j+1)))=values input (j+1):=by
    funext v;cases v <;> simp [values,row,FFT.Limbs.addDigits,total]
  rw [valueEq] at advanced
  have outAfter:=array_store_other outMiddle (by simpa only [scalarPointer] using (separate Var.i).1) iStored
  have aAfter:=array_store_other aMiddle (by simpa only [scalarPointer] using (separate Var.i).2) iStored
  have fresh : li .out≤before.nextObject:=(well.objectIds _ _ (locals.slots Var.out).object).le
  have frame1:=ApplicationBirthFrame.store_frame (li .out) [input.layout.outObject] well fresh
    (Or.inr (by simpa only [scalarPointer] using minId Var.carry)) carryStored
  have frame2:=ApplicationBirthFrame.store_frame (li .out) [input.layout.outObject] wi frame1.fresh
    (Or.inr (by simpa only [scalarPointer] using minId Var.i)) iStored
  exact ⟨after,.cons carryRun (.cons iRun .nil),⟨outAfter,⟨_,aAfter,aRead⟩,advanced,separate,by omega,wellScoped_store wi iStored⟩,
    frame1.trans frame2,(SourceLocals.store_frame iStored).2.2.1.trans (SourceLocals.store_frame carryStored).2.2.1⟩

#print axioms counters_execution
end RH080Next.FFTPV.AddMagnitudeSource
