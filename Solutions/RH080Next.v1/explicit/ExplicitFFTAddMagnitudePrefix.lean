/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

structure XView {F : Type} (state : State F) (input : Input) (owner xId xOwner : Nat) (li : Var → Nat) (j x : Nat) : Prop extends View state input owner li j where
  xSlot : Slot state xId xOwner .u64 (.integer (integer64 x))
  xLookup : state.environment.lookup "x"=some (scalarPointer xId .u64)
  different : ∀v,li v≠xId
  xOut : input.layout.outObject≠xId
  xInput : input.layout.aObject≠xId

private theorem array_store_other {F : Type} {before after : State F} {object length : Nat} {data : Nat → Nat}
    {pointer : Pointer} {value : Value} (rep : WordArrayRep before object length data) (different : object≠pointer.object)
    (stored : before.store pointer value=some after) : WordArrayRep after object length data:=by
  have fields:=SourceLocals.store_frame stored
  refine ⟨fields.2.1.trans rep.1,?_,rep.2.2⟩
  rw [fields.2.2.2.2.2 _ different];exact rep.2.1

theorem x_branch_unique {F : Type} (context : Context F) : CompareSource.Unique context xBranch:=by
  intro before a b fa fb first second
  cases first with
  | ifTrue e t body=>
    cases second with
    | ifTrue e' t' body'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) e e'
      exact PureDeterminism.block_unique (by simp [xAssign,indexA,PureDeterminism.Simple,SourcePure.CallFree]) body body'
    | ifFalse e' t'=>cases (PureDeterminism.eval_unique (by trivial) e e').1;simp_all
  | ifFalse e t=>
    cases second with
    | ifTrue e' t' body'=>cases (PureDeterminism.eval_unique (by trivial) e e').1;simp_all
    | ifFalse e' t'=>exact ⟨rfl,(PureDeterminism.eval_unique (by trivial) e e').2⟩

theorem x_declare {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner : Nat} {li : Var → Nat} {j : Nat}
    (h : View before input owner li j) :
    ∃after,Exec context before (.declare .u64 "x" (some (.literal (.integer 0 "ULL")))) .normal after ∧
      XView after input owner before.nextObject before.scope li j 0 ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  obtain ⟨after,d⟩:=ZeroFrame.declare_exists h.well _ "x" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have info:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) d
  have array:=ApplicationBirthFrame.array_declare_old h.well h.array info
  obtain ⟨data,aRep,aRead⟩:=h.inputArray
  have aRep':=ApplicationBirthFrame.array_declare_old h.well aRep info
  have locals:=ApplicationBirthFrame.locals_declare_old h.well h.locals (by intro v;cases v <;> decide) info
  have oldOut:=h.well.objectIds _ _ h.array.2.1
  have oldA:=h.well.objectIds _ _ aRep.2.1
  refine ⟨after,.declareSome (.literal _ _ _ (by rfl)) d,
    ⟨⟨array,⟨_,aRep',aRead⟩,locals,h.separate,h.active,wellScoped_declare h.well d⟩,info.slot,?_,?_,by omega,by omega⟩,
    ApplicationBirthFrame.declare_frame _ _ h.well (le_refl _) d,info.scope⟩
  · rw [info.environment];simp [List.lookup]
  · intro v;exact (h.well.objectIds _ _ (h.locals.slots v).object).ne

theorem x_branch_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner xId xOwner j : Nat} {li : Var → Nat}
    (h : XView before input owner xId xOwner li j 0) (scope : xOwner=before.scope) :
    ∃after,Exec context before xBranch .normal after ∧ Every context before xBranch .normal after ∧
      XView after input owner xId xOwner li j (aDigit input j) ∧
      ApplicationBirthFrame.Frame before.nextObject before after [xId] ∧ after.scope=before.scope:=by
  have hn64 : j<2^64:=by have hj:=h.active;have hn:=input.layout.small;omega
  have test : Eval context before (.binary .lt (.variable "i") (.literal (.integer 5 "ULL")))
      (.integer (.boolean (decide (j<5)))) before:=by
    exact .binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
      (by simp only [values,binary,binary64_lt j 5 hn64 (by norm_num),Option.map_some])
  by_cases hj : j<5
  · let entry:=before.enterScope
    obtain ⟨data,aRep,aRead⟩:=h.inputArray
    have hi : input.layout.aStart+j< input.layout.length input.layout.aObject:=by have hb:=input.layout.aBound;omega
    have enteredInput : WordArrayRep entry input.layout.aObject (input.layout.length input.layout.aObject) data:=aRep
    have read : Eval context entry indexA (.integer (integer64 (aDigit input j))) entry:=by
      have load : entry.load (wordPointer input.layout.aObject (input.layout.aStart+j))=some (.integer (integer64 (aDigit input j))):=by
        simpa only [aDigit,if_pos hj,aRead j hj] using slice_word_load enteredInput hi
      exact .load (.index (.variable (h.locals.enter.lookup Var.a) (h.locals.enter.read Var.a))
        (.variable (h.locals.enter.lookup Var.i) (h.locals.enter.read Var.i)) (slice_pointer_add enteredInput hi)) load
    have xSlot : Slot entry xId xOwner .u64 (.integer (integer64 0)):=⟨h.xSlot.storable,h.xSlot.object⟩
    obtain ⟨written,stored⟩:=MultiplySmallSource.slot_store_exists xSlot (.integer (integer64 (aDigit input j)))
      (ZeroFrame.u64_storable _ (lt_trans (aDigit_bound input j) (by norm_num [base])))
    have assigned : Exec context entry xAssign .normal written:=.assign read (.variable h.xLookup) stored
    let after : State F:={written.leaveScope before.nextScope before.environment with scope:=before.scope}
    have run : Exec context before xBranch .normal after:=.ifTrue test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj])
      (.block (by rfl) (.cons assigned .nil) (by rfl))
    have frameInside:=ApplicationBirthFrame.store_frame before.nextObject [xId] (wellScoped_enter h.well) (le_refl _)
      (Or.inl (by simp [scalarPointer])) stored
    have frame:=ApplicationBirthFrame.close_frame h.well (le_refl _) frameInside
    have locals:=ApplicationBirthFrame.locals_store_other h.locals.enter h.different stored
    have different : before.nextScope≠owner:=by have b:=h.locals.bound;omega
    have locals':=locals.leave different before.environment h.locals.lookup before.scope
    have slot':=(xSlot.store (ZeroFrame.u64_storable _ (lt_trans (aDigit_bound input j) (by norm_num [base]))) stored)
    have finalSlot : Slot after xId xOwner .u64 (.integer (integer64 (aDigit input j))):=by
      refine ⟨slot'.storable,?_⟩
      change (written.objects xId).map _=_
      rw [slot'.object];simp [scalarObject,show xOwner≠before.nextScope by have b:=h.well.current;omega]
    have outEntry : WordArrayRep entry input.layout.outObject (input.layout.length input.layout.outObject) (currentData input j):=h.array
    have inputEntry : WordArrayRep entry input.layout.aObject (input.layout.length input.layout.aObject) data:=aRep
    have out:=array_store_other outEntry (by simpa only [scalarPointer] using h.xOut) stored
    have a:=array_store_other inputEntry (by simpa only [scalarPointer] using h.xInput) stored
    exact ⟨after,run,every_of_unique (x_branch_unique context) run,
      ⟨⟨IncrementSource.wordArray_leave out,⟨_,IncrementSource.wordArray_leave a,aRead⟩,locals',h.separate,h.active,frame.well⟩,
        finalSlot,h.xLookup,h.different,h.xOut,h.xInput⟩,frame,rfl⟩
  · have run : Exec context before xBranch .normal before:=.ifFalse test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj])
    exact ⟨before,run,every_of_unique (x_branch_unique context) run,by simpa only [aDigit,if_neg hj] using h,
      ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _),rfl⟩

#print axioms x_declare
#print axioms x_branch_execution
end RH080Next.FFTPV.AddMagnitudeSource
