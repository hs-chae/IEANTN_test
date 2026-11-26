/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyCorrect
import FFTFixedMultiplyBeginWords
import FFTFixedMultiplySuffixOutside
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

private theorem append_exec {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after:=by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run ne=>exact False.elim (ne rfl)

/-- A complete real fixed_multiply Call also proves normalization of its actual output.
It returns status0 and the exact signed
Euclidean quotient. Caller entry, parameter binding, scratch initialization,
all25productiterations and all12suffix instructions are actual source steps.
Universal Call correctness and the final caller-frame API are separate roots. -/
theorem fixed_multiply_normalized_word_call {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (caller : State F)
    (outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (old aData bData workData : Nat→Nat) (well : WellScoped caller)
    (outRep : WordArrayRep caller outObj outSize old)
    (work : WordArrayRep caller workObj workSize workData)
    (aRep : WordArrayRep caller aObj aSize aData) (bRep : WordArrayRep caller bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (outShape : outObj=workObj → outSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6 ≤ workStart ∨ workStart+10 ≤ aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6 ≤ workStart ∨ workStart+10 ≤ bStart)
    (outDisjoint : outObj≠workObj ∨ outStart+6 ≤ workStart ∨ workStart+10 ≤ outStart)
    (outBound : outStart+6 ≤ outSize) (aBound : aStart+6 ≤ aSize) (bBound : bStart+6 ≤ bSize) (workBound : workStart+10 ≤ workSize)
    (aDigits : ∀k,k < 5 → aData (aStart+k) < 1000000000)
    (bDigits : ∀k,k < 5 → bData (bStart+k) < 1000000000)
    (aBit : aData (aStart+5) ≤ 1) (bBit : bData (bStart+5) ≤ 1)
    (aSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k)) ≤ 1000*10^36)
    (bSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k)) ≤ 1000*10^36) :
    ∃after finalOutput,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ WordArrayRep after outObj outSize finalOutput ∧
      CanonicalSource.represented finalOutput outStart=
        (CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart)/(1000000000^4:Nat) ∧
      (∀k,k < 5 → finalOutput (outStart+k) < 1000000000) ∧ finalOutput (outStart+5) ≤ 1 ∧
      (∀k,k < workSize → (k < workStart ∨ workStart+10 ≤ k) →
        (workObj≠outObj ∨ k < outStart ∨ outStart+6 ≤ k) →
        after.load (wordPointer workObj k)=some (.integer (integer64 (workData k)))) ∧
      (∀k,k < outSize → (k < outStart ∨ outStart+6 ≤ k) →
        (outObj≠workObj ∨ k < workStart ∨ workStart+10 ≤ k) → finalOutput k=old k) := by
  let entry : State F:={caller.enterScope with environment:=[]}
  obtain ⟨entered,current,iId,data,binding,corePrefix,hp,params,product,readA,readB,oldFrame,beginFrame,enteredScope,readWork⟩:=
    MultiplyParameters.begin_execution_word_framed context zeroSelected caller outObj outStart aObj aSize aStart bObj bSize bStart
      workObj workSize workStart aData bData workData well work aRep bRep aShape bShape aDisjoint bDisjoint
      aBound bBound workBound aDigits bDigits
  obtain ⟨outData,outCurrent⟩:=MultiplyParameters.current_output_rep well outRep hp.work outShape oldFrame
  obtain ⟨aCurrent,ar,av⟩:=hp.aInput
  obtain ⟨bCurrent,br,bv⟩:=hp.bInput
  have bindings:=MultiplyParameters.suffix_bindings params hp
  have separate : ∀v,outObj≠MultiplyParameters.suffixIds (MultiplyParameters.ids entry.nextObject) iId v ∧
      workObj≠MultiplyParameters.suffixIds (MultiplyParameters.ids entry.nextObject) iId v:=by
    intro v
    exact ⟨MultiplyParameters.array_slot_different outCurrent (bindings.slots v),
      MultiplyParameters.array_slot_different hp.work (bindings.slots v)⟩
  have shape : workObj=outObj → workSize=outSize:=fun eq=>(outShape eq.symm).symm
  obtain ⟨middle,suffix,finalRep,suffixFrame⟩:=MultiplySuffix.suffix_framed context incSelected canonSelected bindings hp.well
    outCurrent ar br hp.work separate shape outDisjoint outBound aBound bBound workBound hp.workDigits
  let sign:=MultiplySuffix.signBit (aCurrent (aStart+5)) (bCurrent (bStart+5))
  obtain ⟨top,safe⟩:=MultiplyBounds.bounded_product (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k))
    (fun k=>data (workStart+k)) product aSmall bSmall hp.workDigits
  have zeroStatus : MultiplySuffix.finalStatus outData data outStart workStart sign=0:=
    MultiplySuffix.finalStatus_eq_zero outData data outStart workStart sign top safe
  rw [zeroStatus] at suffix
  have aSignEq : aCurrent (aStart+5)=aData (aStart+5):=by
    have same:=(word_load ar (by omega : aStart+5 < aSize)).symm.trans (readA 5 (by omega))
    simpa [integer64] using same
  have bSignEq : bCurrent (bStart+5)=bData (bStart+5):=by
    have same:=(word_load br (by omega : bStart+5 < bSize)).symm.trans (readB 5 (by omega))
    simpa [integer64] using same
  have outputMath:=MultiplySuffix.finalData_successful outData data outStart workStart sign hp.workDigits zeroStatus
  have naturalProduct : FFT.Limbs.magnitude 1000000000 10 (fun k=>data (workStart+k))=
      FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))*
      FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k)):=by
    simpa only [FFT.Limbs.value_eq_magnitude,←Nat.cast_mul,Int.natCast_inj] using product
  rw [naturalProduct] at outputMath
  have numerator : (if decide (sign≠0) then
      -((FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))*
          FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k)):Nat):Int)
      else ((FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))*
          FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k)):Nat):Int))=
      CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart:=by
    simpa only [sign,aSignEq,bSignEq] using signed_product aData bData aStart bStart aBit bBit
  rw [numerator] at outputMath
  have whole : ExecList context entered (ProductRow.items fixed_multiply_ast.body)
      (.returned (.integer (integer64 0))) middle:=by
    have suffixActual : (ProductRow.items fixed_multiply_ast.body).drop 3=MultiplySuffix.statements:=by rfl
    have full:=append_exec corePrefix suffix
    rw [←suffixActual,List.take_append_drop] at full
    exact full
  let after : State F:={middle.leaveScope entered.scope caller.environment with scope:=caller.scope}
  have called : Call context "fixed_multiply"
      [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
        .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
      (.value (.integer (integer64 0))) after:=by
    apply Call.internal (function:=fixed_multiply_ast) (entered:=entered) (middle:=middle)
      selected (by rfl) binding
    · exact Body.finish whole (by intro label impossible;cases impossible)
    · exact convert64 0 (by norm_num)
    · rfl
  have afterRep : WordArrayRep after outObj outSize (MultiplySuffix.finalData outData data outStart workStart sign):=by
    refine ⟨finalRep.1,?_,finalRep.2.2⟩
    change (middle.objects outObj).map _=some (wordObject outSize _)
    rw [finalRep.2.1];rfl
  have signBound : sign ≤ 1 := by unfold sign MultiplySuffix.signBit;split <;> omega
  have workOutside : ∀k,k < workSize → (k < workStart ∨ workStart+10 ≤ k) →
      (workObj≠outObj ∨ k < outStart ∨ outStart+6 ≤ k) →
      after.load (wordPointer workObj k)=some (.integer (integer64 (workData k))) := by
    intro k hk scratchOutside outputOutside
    have coreRead:=readWork k hk scratchOutside
    by_cases same : workObj=outObj
    · have sizes:=outShape same.symm
      have ko : k < outSize:=by omega
      have outOutside : k < outStart ∨ outStart+6 ≤ k := by
        rcases outputOutside with ne|left|right
        · exact False.elim (ne same)
        · exact Or.inl left
        · exact Or.inr right
      have pointerEq : wordPointer workObj k=wordPointer outObj k:=by rw [same]
      rw [pointerEq] at coreRead ⊢
      have valueEq : outData k=workData k := by
        have sameValue:=(word_load outCurrent ko).symm.trans coreRead
        simpa [integer64] using sameValue
      have read:=word_load afterRep ko
      rw [MultiplySuffix.finalData_outside outData data outStart workStart sign k outOutside,valueEq] at read
      exact read
    · have wo:=hp.well.objectIds _ _ hp.work.2.1
      have untouched : middle.objects workObj=current.objects workObj :=
        suffixFrame.outside workObj wo (by
          simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
          refine ⟨same,?_⟩
          simpa only [MultiplyParameters.suffixIds,MultiplyParameters.coreIds] using (hp.separate ProductOuter.PVar.i).1)
      have middleRep : WordArrayRep middle workObj workSize data :=
        ⟨suffixFrame.mode.trans hp.work.1,untouched.trans hp.work.2.1,hp.work.2.2⟩
      have resultRep : WordArrayRep after workObj workSize data := by
        refine ⟨middleRep.1,?_,middleRep.2.2⟩
        change (middle.objects workObj).map _=some (wordObject workSize _)
        rw [middleRep.2.1];rfl
      have valueEq : data k=workData k := by
        have sameValue:=(word_load hp.work hk).symm.trans coreRead
        simpa [integer64] using sameValue
      simpa only [valueEq] using word_load resultRep hk
  have outOutside : ∀k,k < outSize → (k < outStart ∨ outStart+6 ≤ k) →
      (outObj≠workObj ∨ k < workStart ∨ workStart+10 ≤ k) →
      MultiplySuffix.finalData outData data outStart workStart sign k=old k := by
    intro k hk outputOutside scratchOutside
    rw [MultiplySuffix.finalData_outside outData data outStart workStart sign k outputOutside]
    by_cases same : outObj=workObj
    · have sizes:=outShape same
      have kw : k < workSize:=by omega
      have outsideWork : k < workStart ∨ workStart+10 ≤ k := by
        rcases scratchOutside with ne|left|right
        · exact False.elim (ne same)
        · exact Or.inl left
        · exact Or.inr right
      have pointerEq : wordPointer workObj k=wordPointer outObj k:=by rw [same]
      have coreRead:=readWork k kw outsideWork
      rw [pointerEq] at coreRead
      have currentEq : outData k=workData k := by
        have sameValue:=(word_load outCurrent hk).symm.trans coreRead
        simpa [integer64] using sameValue
      have callerWork : WordArrayRep caller outObj outSize workData := by simpa only [same,sizes] using work
      exact currentEq.trans (word_data_unique outRep callerWork k hk).symm
    · have oldId:=well.objectIds _ _ outRep.2.1
      have currentOld : WordArrayRep current outObj outSize old :=
        ⟨beginFrame.mode.trans outRep.1,(oldFrame outObj oldId same).trans outRep.2.1,outRep.2.2⟩
      exact word_data_unique outCurrent currentOld k hk
  exact ⟨after,_,called,afterRep,outputMath,
    (MultiplySuffix.finalData_normalized outData data outStart workStart sign hp.workDigits signBound).1,
    (MultiplySuffix.finalData_normalized outData data outStart workStart sign hp.workDigits signBound).2,
    workOutside,outOutside⟩

#print axioms fixed_multiply_normalized_word_call
theorem fixed_multiply_correct_words {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (caller : State F)
    (outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (old aData bData workData : Nat→Nat) (well : WellScoped caller)
    (outRep : WordArrayRep caller outObj outSize old)
    (work : WordArrayRep caller workObj workSize workData)
    (aRep : WordArrayRep caller aObj aSize aData) (bRep : WordArrayRep caller bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (outShape : outObj=workObj → outSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6 ≤ workStart ∨ workStart+10 ≤ aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6 ≤ workStart ∨ workStart+10 ≤ bStart)
    (outDisjoint : outObj≠workObj ∨ outStart+6 ≤ workStart ∨ workStart+10 ≤ outStart)
    (outBound : outStart+6 ≤ outSize) (aBound : aStart+6 ≤ aSize) (bBound : bStart+6 ≤ bSize) (workBound : workStart+10 ≤ workSize)
    (aDigits : ∀k,k < 5 → aData (aStart+k) < 1000000000)
    (bDigits : ∀k,k < 5 → bData (bStart+k) < 1000000000)
    (aBit : aData (aStart+5) ≤ 1) (bBit : bData (bStart+5) ≤ 1)
    (aSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k)) ≤ 1000*10^36)
    (bSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k)) ≤ 1000*10^36) :
    ∃after finalOutput,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ WordArrayRep after outObj outSize finalOutput ∧
      CanonicalSource.represented finalOutput outStart=
        (CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart)/(1000000000^4:Nat) ∧
      (∀k,k < 5 → finalOutput (outStart+k) < 1000000000) ∧ finalOutput (outStart+5) ≤ 1 ∧
      (∀k,k < workSize → (k < workStart ∨ workStart+10 ≤ k) →
        (workObj≠outObj ∨ k < outStart ∨ outStart+6 ≤ k) →
        after.load (wordPointer workObj k)=some (.integer (integer64 (workData k)))) ∧
      (∀k,k < outSize → (k < outStart ∨ outStart+6 ≤ k) →
        (outObj≠workObj ∨ k < workStart ∨ workStart+10 ≤ k) → finalOutput k=old k) ∧ CallerFrame caller after [outObj,workObj] ∧
      ∀after' result,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller result after' →
        result=.value (.integer (integer64 0)) ∧ after'=after := by
  obtain ⟨after,finalOutput,called,output,math,digits,bit,workWords,outWords⟩:=fixed_multiply_normalized_word_call context selected zeroSelected incSelected canonSelected caller outObj outSize outStart aObj aSize aStart bObj bSize bStart
    workObj workSize workStart old aData bData workData well outRep work aRep bRep aShape bShape outShape
    aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall
  obtain ⟨other,otherData,known,knownOutput,knownMath,knownDigits,knownBit,frame,every⟩:=fixed_multiply_correct context selected zeroSelected incSelected canonSelected caller outObj outSize outStart aObj aSize aStart bObj bSize bStart
    workObj workSize workStart old aData bData workData well outRep work aRep bRep aShape bShape outShape
    aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall
  have afterEq:=(every after _ called).2
  have sameFrame : CallerFrame caller after [outObj,workObj] := by rwa [←afterEq] at frame
  refine ⟨after,finalOutput,called,output,math,digits,bit,workWords,outWords,sameFrame,?_⟩
  intro after' result actual
  obtain ⟨rv,st⟩:=every after' result actual
  exact ⟨rv,st.trans afterEq.symm⟩

#print axioms fixed_multiply_correct_words
end RH080Next.FFTPV.MultiplyCall
