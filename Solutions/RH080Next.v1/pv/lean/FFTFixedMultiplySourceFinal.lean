/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyCorrect
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Literal preserved original C source syntax, actual helper lookup and the
complete universal numerical/helper contract. Final FFT/ANT consumption remains separate. -/
theorem source_fixed_multiply_correct {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
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
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
    (∃after finalOutput,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ WordArrayRep after outObj outSize finalOutput ∧
      CanonicalSource.represented finalOutput outStart=
        (CanonicalSource.represented aData aStart*CanonicalSource.represented bData bStart)/(1000000000^4:Nat) ∧
      (∀k,k<5 → finalOutput (outStart+k)<1000000000) ∧ finalOutput (outStart+5)≤1 ∧ CallerFrame caller after [outObj,workObj] ∧
      ∀after' result,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller result after' →
        result=.value (.integer (integer64 0)) ∧ after'=after) := by
  have selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  have zeroSelected : findFunction context.program "zero_words"=some zero_words_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  have incSelected : findFunction context.program "increment_words"=some increment_words_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  have canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    fixed_multiply_correct context selected zeroSelected incSelected canonSelected caller outObj outSize outStart
      aObj aSize aStart bObj bSize bStart workObj workSize workStart old aData bData workData
      well outRep work aRep bRep aShape bShape outShape aDisjoint bDisjoint outDisjoint
      outBound aBound bBound workBound aDigits bDigits aBit bBit aSmall bSmall⟩

#print axioms source_fixed_multiply_correct
end RH080Next.FFTPV.MultiplyCall
