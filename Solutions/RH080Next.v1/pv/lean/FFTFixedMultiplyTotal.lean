/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyUniversal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Every permitted full actual source Call terminates with status zero and the
same exact signed floor; its execution is constructed without output assumptions. -/
theorem fixed_multiply_total {F : Type} (context : Context F)
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
      ∀after' result,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller result after' →
        result=.value (.integer (integer64 0)) ∧ after'=after := by
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
  obtain ⟨middle,suffix,finalRep,allSuffix⟩:=MultiplySuffix.suffix_total context incSelected canonSelected bindings hp.well
    outCurrent ar br hp.work separate shape outDisjoint outBound aBound bBound workBound hp.workDigits
  have uniqueBody : ∀{x y : State F}{fx fy : Flow},
      Body context functionStatements entered functionStatements fx x →
      Body context functionStatements entered functionStatements fy y → fx=fy ∧ x=y:=by
    intro x y fx fy first second
    apply body_unique_at_core zeroSelected corePrefix (first:=first) (second:=second)
    intro x y fx fy first second
    obtain ⟨xf,xs⟩:=allSuffix x fx first
    obtain ⟨yf,ys⟩:=allSuffix y fy second
    exact ⟨xf.trans yf.symm,xs.trans ys.symm⟩
  obtain ⟨after,finalOutput,called,output,math⟩:=fixed_multiply_call context selected zeroSelected incSelected canonSelected
    caller outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart old aData bData workData
    well outRep work aRep bRep aShape bShape outShape aDisjoint bDisjoint outDisjoint outBound aBound bBound workBound
    aDigits bDigits aBit bBit aSmall bSmall
  refine ⟨after,finalOutput,called,output,math,?_⟩
  intro after' result actual
  exact returned_call_unique_at selected binding uniqueBody called actual

#print axioms fixed_multiply_total
end RH080Next.FFTPV.MultiplyCall
