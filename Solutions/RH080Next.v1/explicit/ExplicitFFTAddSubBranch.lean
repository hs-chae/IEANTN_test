/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddChooseSign
import ExplicitApplicationLoopScope
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def Input.subtractionSign (input : Input) : Nat:=if input.cmp=0 then input.bsign else input.asign

theorem sign_survives_subloop {F : Type} {context : Context F} {before after : State F} {input : Input}
    {owner j signId signOwner signValue : Nat} {li : Var → Nat}
    (h : View before input true (decide (input.cmp=0)) owner li j)
    (sign : SignLocal before signId signOwner signValue) (different : ∀v,li v≠signId)
    (run : Exec context before subLoop .normal after)
    (frame : ApplicationBirthFrame.Frame before.nextObject before after (writes input li)) :
    SignLocal after signId signOwner signValue := by
  have fields:=ApplicationLoopScope.while_block_fields run (by simp [condition,SourcePure.CallFree])
  have old:=h.well.objectIds _ _ (sign.slots ()).object
  have absent : signId∉writes input li := by
    have neObj:=scalar_array_ne (sign.slots ()) (h.arrays .out)
    have nj:=(different Var.j).symm
    have nc:=(different Var.carry).symm
    simp [writes,neObj,nj,nc]
  refine ⟨?_,?_,sign.distinct,?_⟩
  · rw [fields.1]
    exact sign.lookup
  · intro u
    exact ⟨(sign.slots u).storable,by rw [frame.outside signId old absent]; exact (sign.slots u).object⟩
  · exact lt_of_lt_of_le sign.bound frame.nextScope

/-- The complete real opposite-sign branch, including its sign local,
comparison-dependent sign choice, reverse operands, sign store and status reset. -/
theorem sub_branch_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner : Nat} {li : Var → Nat} (h : View before input true (decide (input.cmp=0)) owner li 0) :
    ∃after,Exec context before subtractionBranch .normal after ∧
      BranchView after input true (decide (input.cmp=0)) input.subtractionSign 0 owner li ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  have as64 : input.asign < 2^64:=lt_of_le_of_lt input.signA (by norm_num)
  obtain ⟨declared,declSign⟩:=ZeroFrame.declare_exists h.enter.well .u64 "sign" (.integer (integer64 input.asign))
    (ZeroFrame.u64_storable input.asign as64)
  have ds:=declare_storable (ZeroFrame.u64_storable input.asign as64) (convert64 input.asign as64) declSign
  have ld:=ApplicationBirthFrame.locals_declare_old h.enter.well h.enter.locals (by intro v; cases v <;> decide) ds
  have ad:=h.enter.arrays.declare_old h.enter.well ds
  have wd:=wellScoped_declare h.enter.well declSign
  have hd : View declared input true (decide (input.cmp=0)) owner li 0:=⟨ad,ld,h.separate,h.active,wd⟩
  have sign : SignLocal declared before.nextObject before.nextScope input.asign := by
    refine ⟨?_,?_,?_,?_⟩
    · intro u
      rw [ds.environment]
      rfl
    · intro u
      exact ds.slot
    · intro u v eq
      cases u; cases v; rfl
    · rw [ds.nextScope]
      simp [State.enterScope]
  have different : ∀v,li v≠before.nextObject := by
    intro v
    have oldId:=h.well.objectIds _ _ (h.locals.slots v).object
    omega
  obtain ⟨chosen,chooseRun,hc,chosenSign,choiceFrame⟩:=choose_sign_execution context hd sign different
    (cutoff:=before.nextObject) (le_refl _) (by rw [ds.nextObject]; change before.nextObject ≤ before.nextObject+1; omega)
  obtain ⟨middle,loopRun,post,loopFrame⟩:=sub_loop_execution context 5 (j:=0) (by omega) hc
  have signAfter:=sign_survives_subloop hc chosenSign different loopRun loopFrame
  have sign64 : input.subtractionSign < 2^64 := by
    unfold Input.subtractionSign
    split_ifs
    · exact lt_of_le_of_lt input.bsign_bound (by norm_num)
    · exact lt_of_le_of_lt input.signA (by norm_num)
  have loopFrame':=IncrementSource.frame_restrict loopFrame choiceFrame.fresh
  obtain ⟨signed,signRun,signedPost,signFrame⟩:=store_sign_execution context post (.variable "sign")
    (.variable (signAfter.lookup ()) (signAfter.read ())) sign64 loopFrame'.fresh
  have zero:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨last,storeCarry⟩:=IncrementSource.slot_store_exists (signedPost.locals.slots Var.carry) (.integer (integer64 0)) zero
  have clearRun : Exec context signed clearCarry .normal last:=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (Place.variable (signedPost.locals.lookup Var.carry)) storeCarry
  have locals : Locals last name type li owner (values input 5 0):=by
    simpa only [values_carry_update] using signedPost.locals.store Var.carry _ zero storeCarry
  have array:=IncrementSource.array_store_other signedPost.array (h.separate .out Var.carry) storeCarry
  have clearFrame:=ApplicationBirthFrame.store_frame before.nextObject (writes input li) signedPost.well signFrame.fresh
    (Or.inl (by simp [writes,scalarPointer])) storeCarry
  have declFrame:=ApplicationBirthFrame.declare_frame before.nextObject (writes input li) h.enter.well (le_refl _) declSign
  have whole:=declFrame.trans (choiceFrame.trans (loopFrame'.trans (signFrame.trans clearFrame)))
  have frame:=ApplicationBirthFrame.close_frame h.well (le_refl _) whole
  let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
  have ownerDifferent : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
  have postLocals:=locals.leave ownerDifferent before.environment h.locals.lookup before.scope
  have bodyRun : ExecList context before.enterScope [signDeclaration,chooseSign,subLoop,storeSign "sign",clearCarry] .normal last:=
    .cons (.declareSome (.variable (h.enter.locals.lookup Var.asign) (h.enter.locals.read Var.asign)) declSign)
      (.cons chooseRun (.cons loopRun (.cons signRun (.cons clearRun .nil))))
  exact ⟨after,.block (by rfl) bodyRun (by rfl),
    ⟨IncrementSource.wordArray_leave array,postLocals,h.separate .out,frame.well⟩,frame⟩

#print axioms sign_survives_subloop
#print axioms sub_branch_execution
end RH080Next.FFTPV.AddSource
