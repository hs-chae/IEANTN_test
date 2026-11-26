/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyFrame
import FFTFixedMultiplySuffixOutput
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
theorem fixed_multiply_normalized_call {F : Type} (context : Context F)
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
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (outDisjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000)
    (aBit : aData (aStart+5)≤1) (bBit : bData (bStart+5)≤1)
    (aSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))≤1000*10^36)
    (bSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k))≤1000*10^36) :
    ∃after finalOutput,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ WordArrayRep after outObj outSize finalOutput ∧
      CanonicalSource.represented finalOutput outStart=
        (CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart)/(1000000000^4:Nat) ∧
      (∀k,k<5 → finalOutput (outStart+k)<1000000000) ∧ finalOutput (outStart+5)≤1 := by
  let entry : State F:={caller.enterScope with environment:=[]}
  obtain ⟨entered,current,iId,data,binding,corePrefix,hp,params,product,readA,readB,oldFrame⟩:=
    MultiplyParameters.begin_execution context zeroSelected caller outObj outStart aObj aSize aStart bObj bSize bStart
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
  obtain ⟨middle,suffix,finalRep⟩:=MultiplySuffix.suffix_execution context incSelected canonSelected bindings hp.well
    outCurrent ar br hp.work separate shape outDisjoint outBound aBound bBound workBound hp.workDigits
  let sign:=MultiplySuffix.signBit (aCurrent (aStart+5)) (bCurrent (bStart+5))
  obtain ⟨top,safe⟩:=MultiplyBounds.bounded_product (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k))
    (fun k=>data (workStart+k)) product aSmall bSmall hp.workDigits
  have zeroStatus : MultiplySuffix.finalStatus outData data outStart workStart sign=0:=
    MultiplySuffix.finalStatus_eq_zero outData data outStart workStart sign top safe
  rw [zeroStatus] at suffix
  have aSignEq : aCurrent (aStart+5)=aData (aStart+5):=by
    have same:=(word_load ar (by omega : aStart+5<aSize)).symm.trans (readA 5 (by omega))
    simpa [integer64] using same
  have bSignEq : bCurrent (bStart+5)=bData (bStart+5):=by
    have same:=(word_load br (by omega : bStart+5<bSize)).symm.trans (readB 5 (by omega))
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
  have signBound : sign≤1 := by unfold sign MultiplySuffix.signBit;split <;> omega
  exact ⟨after,_,called,afterRep,outputMath,
    MultiplySuffix.finalData_normalized outData data outStart workStart sign hp.workDigits signBound⟩

#print axioms fixed_multiply_normalized_call
theorem fixed_multiply_correct {F : Type} (context : Context F)
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
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (outDisjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000)
    (aBit : aData (aStart+5)≤1) (bBit : bData (bStart+5)≤1)
    (aSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))≤1000*10^36)
    (bSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k))≤1000*10^36) :
    ∃after finalOutput,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ WordArrayRep after outObj outSize finalOutput ∧
      CanonicalSource.represented finalOutput outStart=
        (CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart)/(1000000000^4:Nat) ∧
      (∀k,k<5 → finalOutput (outStart+k)<1000000000) ∧ finalOutput (outStart+5)≤1 ∧ CallerFrame caller after [outObj,workObj] ∧
      ∀after' result,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller result after' →
        result=.value (.integer (integer64 0)) ∧ after'=after := by
  obtain ⟨after,finalOutput,called,output,math,digits,bit⟩:=fixed_multiply_normalized_call context selected zeroSelected incSelected canonSelected caller outObj outSize outStart aObj aSize aStart bObj bSize bStart
    workObj workSize workStart old aData bData workData well outRep work aRep bRep aShape bShape outShape
    aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall
  obtain ⟨other,otherData,known,knownOutput,knownMath,every⟩:=fixed_multiply_total context selected zeroSelected incSelected canonSelected caller outObj outSize outStart aObj aSize aStart bObj bSize bStart
    workObj workSize workStart old aData bData workData well outRep work aRep bRep aShape bShape outShape
    aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall
  obtain ⟨framed,frameCall,frame⟩:=fixed_multiply_call_framed context selected zeroSelected incSelected canonSelected caller outObj outSize outStart aObj aSize aStart bObj bSize bStart
    workObj workSize workStart old aData bData workData well outRep work aRep bRep aShape bShape outShape
    aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall
  have afterEq:=(every after _ called).2
  have frameEq:=(every framed _ frameCall).2.trans afterEq.symm
  rw [frameEq] at frame
  refine ⟨after,finalOutput,called,output,math,digits,bit,frame,?_⟩
  intro after' result actual
  obtain ⟨rv,st⟩:=every after' result actual
  exact ⟨rv,st.trans afterEq.symm⟩

#print axioms fixed_multiply_correct
end RH080Next.FFTPV.MultiplyCall
