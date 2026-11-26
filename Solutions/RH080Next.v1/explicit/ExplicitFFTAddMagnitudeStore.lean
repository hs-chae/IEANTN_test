/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeTemporary
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem array_store_other {F : Type} {before after : State F} {object length : Nat} {data : Nat → Nat}
    {pointer : Pointer} {value : Value} (rep : WordArrayRep before object length data) (different : object≠pointer.object)
    (stored : before.store pointer value=some after) : WordArrayRep after object length data:=by
  have fields:=SourceLocals.store_frame stored
  refine ⟨fields.2.1.trans rep.1,?_,rep.2.2⟩
  rw [fields.2.2.2.2.2 _ different];exact rep.2.1

theorem digit_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner xId tId xOwner j : Nat} {li : Var → Nat}
    (h : TView before input owner xId tId xOwner li j) (hj : j< input.layout.n) :
    ∃after,Exec context before digitStmt .normal after ∧
      WordArrayRep after input.layout.outObject (input.layout.length input.layout.outObject) (currentData input (j+1)) ∧
      (∃data,WordArrayRep after input.layout.aObject (input.layout.length input.layout.aObject) data ∧
        ∀k<5,data (input.layout.aStart+k)=input.old input.layout.aObject (input.layout.aStart+k)) ∧
      Locals after name ctype li owner (values input j) ∧
      Slot after tId xOwner .u64 (.integer (integer64 (total input j))) ∧
      after.environment.lookup "t"=some (scalarPointer tId .u64) ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  have bound : input.layout.outStart+j< input.layout.length input.layout.outObject:=by have b:=input.layout.outBound;omega
  have total64 : total input j<2^64:=lt_trans (total_bound input j hj) (by norm_num [base])
  have digit64 : total input j%base<2^64:=lt_trans (Nat.mod_lt _ (by norm_num [base])) (by norm_num [base])
  obtain ⟨after,stored,outRep⟩:=word_store_with_rep h.array bound digit64
  have read : Eval context before (.paren (.binary .mod (.variable "t") (.literal (.integer base "ULL"))))
      (.integer (integer64 (total input j%base))) before:=.paren (.binaryLR (.variable h.tLookup h.tSlot.read)
        (.literal (.integer base "ULL") _ (.integer (integer64 base)) (by rfl))
        (by simp only [binary,binary64_mod _ _ total64 (show base<2^64 by norm_num [base]) (show 0<base by norm_num [base]),Option.map_some]))
  have place : Place context before (.index (.variable "out") (.variable "i")) (wordPointer input.layout.outObject (input.layout.outStart+j)) before:=
    .index (.variable (h.locals.lookup Var.out) (h.locals.read Var.out)) (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (slice_pointer_add h.array bound)
  have run : Exec context before digitStmt .normal after:=.assign read place stored
  have inputRep : ∃data,WordArrayRep after input.layout.aObject (input.layout.length input.layout.aObject) data ∧
      ∀k<5,data (input.layout.aStart+k)=input.old input.layout.aObject (input.layout.aStart+k):=by
    by_cases same : input.layout.outObject=input.layout.aObject
    · refine ⟨_,by simpa only [same] using outRep,?_⟩
      intro k hk
      have outside : input.layout.aStart+k< input.layout.outStart ∨ input.layout.outStart+input.layout.n≤ input.layout.aStart+k:=by
        rcases input.layout.safe with different|lo|hi
        · exact False.elim (different same)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      rw [Function.update_of_ne (show input.layout.aStart+k≠input.layout.outStart+j by rcases outside with lo|hi <;> omega),
        currentData_outside input j _ (by rcases outside with lo|hi <;> omega)]
      rw [same]
    · obtain ⟨data,aRep,aRead⟩:=h.inputArray
      exact ⟨_,array_store_other aRep (by simpa only [wordPointer] using Ne.symm same) stored,aRead⟩
  have lm:=ApplicationBirthFrame.locals_store_other h.locals (fun v=>by simpa only [wordPointer] using (h.separate v).1.symm) stored
  have slot:=ApplicationBirthFrame.slot_store_other h.tSlot (by simpa only [wordPointer] using h.tOut.symm) stored
  have frame:=ApplicationBirthFrame.store_frame before.nextObject [input.layout.outObject] h.well (le_refl _) (Or.inl (by simp [wordPointer])) stored
  have fields:=SourceLocals.store_frame stored
  exact ⟨after,run,outRep,inputRep,lm,slot,by rw [fields.1];exact h.tLookup,frame,fields.2.2.1⟩

#print axioms digit_execution
end RH080Next.FFTPV.AddMagnitudeSource
