/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyInitializedCore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

private theorem actual_initialized_core_words : (ProductRow.items fixed_multiply_ast.body).take 3=
    [zeroCall,iDeclaration,ProductOuter.outerLoop]:=by rfl

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys .normal after) : ExecList context before (xs++ys) .normal after:=by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run ne=>exact False.elim (ne rfl)

/-- The real zero_words call and i declaration discharge initialization before
the complete twenty-five source product iterations. All four actual pointer
parameters and all six words of each input survive. -/
theorem initialized_core_execution_words {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) {before : State F}
    {outObj outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart owner : Nat}
    {parameterIds : Var→Nat} {aData bData workData : Nat→Nat}
    (well : WellScoped before)
    (params : Locals before name type parameterIds owner (value outObj outStart aObj aStart bObj bStart workObj workStart))
    (ownerCurrent : owner=before.scope)
    (latestParameter : before.nextObject=parameterIds Var.work+1)
    (freshScope : before.nextScope=owner+1)
    (work : WordArrayRep before workObj workSize workData)
    (aRep : WordArrayRep before aObj aSize aData) (bRep : WordArrayRep before bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000)
    (separate : ∀v,workObj≠parameterIds v ∧ aObj≠parameterIds v ∧ bObj≠parameterIds v) :
    ∃after iId finalData,ExecList context before [zeroCall,iDeclaration,ProductOuter.outerLoop] .normal after ∧
      ProductOuter.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart
        (coreIds parameterIds iId) (fun _=>owner)
        (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k)) finalData 5 ∧
      Locals after name type parameterIds owner (value outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      Frame before.nextObject before after [workObj] ∧
      RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>aData (aStart+k))*
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>bData (bStart+k)) ∧
      (∀k,k<6 → after.load (wordPointer aObj (aStart+k))=some (.integer (integer64 (aData (aStart+k))))) ∧
      (∀k,k<6 → after.load (wordPointer bObj (bStart+k))=some (.integer (integer64 (bData (bStart+k))))) ∧
      (∀k,k<workSize → (k<workStart ∨ workStart+10≤k) →
        after.load (wordPointer workObj k)=some (.integer (integer64 (workData k)))) := by
  obtain ⟨middle,iId,prefixRun,hp,mp,freshIds,prefixFrame,readA,readB⟩:=prefix_execution context selected well params
    ownerCurrent latestParameter freshScope work aRep bRep aShape bShape aDisjoint bDisjoint
    aBound bBound workBound aDigits bDigits separate
  have initialized : ∀k,k<10 → ZeroSlice.zeroData workData workStart 10 (workStart+k)=0:=
    fun k hk=>ZeroSlice.zeroData_inside _ _ _ k hk
  obtain ⟨after,finalData,coreRun,ha,coreFrame,product⟩:=ProductOuter.source_product_core context hp initialized
  have noDecrease : before.nextObject ≤ iId:=by have last:=freshIds Var.work;rw [latestParameter];omega
  have narrow : Frame before.nextObject middle after [workObj]:=by
    refine ⟨coreFrame.well,prefixFrame.fresh.trans coreFrame.nextObject,coreFrame.nextObject,coreFrame.nextScope,
      coreFrame.mode,coreFrame.foreign,?_⟩
    intro id old outside
    apply coreFrame.outside id (old.trans_le prefixFrame.nextObject)
    simp only [coreIds,List.mem_cons,List.mem_singleton,not_or,List.not_mem_nil,or_false] at outside ⊢
    exact ⟨outside,by omega⟩
  have env:=(ProductOuter.every_core_state hp coreRun).2.2.2
  have pa : Locals after name type parameterIds owner
      (value outObj outStart aObj aStart bObj bStart workObj workStart):=by
    refine ⟨?_,?_,mp.distinct,mp.bound.trans_le coreFrame.nextScope⟩
    · rw [env];exact mp.lookup
    · intro v
      have old:=hp.well.objectIds _ _ (mp.slots v).object
      have permitted : parameterIds v∉[workObj,coreIds parameterIds iId ProductOuter.PVar.i]:=by
        simp [coreIds,(separate v).1.symm,show parameterIds v≠iId from by have hf:=freshIds v;omega]
      exact ⟨(mp.slots v).storable,by rw [coreFrame.outside _ old permitted];exact (mp.slots v).object⟩
  refine ⟨after,iId,finalData,append_normal prefixRun (.cons coreRun .nil),ha,pa,prefixFrame.trans narrow,product,?_,?_,?_⟩
  · obtain ⟨ad,ar,av⟩:=hp.aInput
    intro k hk
    have bound : aStart+k<aSize:=by omega
    have outside : aObj≠workObj ∨ aStart+k<workStart ∨ workStart+10≤aStart+k:=by
      rcases aDisjoint with no | low | high
      · exact Or.inl no
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have afterRead:=ProductOuter.every_core_read hp ar bound aShape (hp.separate ProductOuter.PVar.i).2.1 outside coreRun
    exact afterRead.trans ((word_load ar bound).symm.trans (readA k hk))
  · obtain ⟨bd,br,bv⟩:=hp.bInput
    intro k hk
    have bound : bStart+k<bSize:=by omega
    have outside : bObj≠workObj ∨ bStart+k<workStart ∨ workStart+10≤bStart+k:=by
      rcases bDisjoint with no | low | high
      · exact Or.inl no
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have afterRead:=ProductOuter.every_core_read hp br bound bShape (hp.separate ProductOuter.PVar.i).2.2 outside coreRun
    exact afterRead.trans ((word_load br bound).symm.trans (readB k hk))

  · have exactCore:=(ProductOuter.every_core_state hp coreRun).2.1
    intro k hk outside
    have read:=word_load exactCore.work hk
    rw [ProductOuter.advance_untouched workStart 0 5 _ _ _ k (by omega) outside] at read
    rw [ZeroSlice.zeroData_outside workData workStart 10 k outside] at read
    exact read

#print axioms actual_initialized_core_words
#print axioms initialized_core_execution_words
end RH080Next.FFTPV.MultiplyParameters
