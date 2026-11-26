/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyBegin
import FFTProductSourceCore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Literal C source syntax and the pinned actual program's function lookup
are consumed together with arbitrary real callee-entry/parameter/initialization
and complete product-loop correctness. This verifies the executed function
prefix, before its sign/drop/output/return suffix. -/
theorem source_begin_execution {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program) (caller : State F)
    (outObj outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (aData bData workData : Nat→Nat) (well : WellScoped caller)
    (work : WordArrayRep caller workObj workSize workData)
    (aRep : WordArrayRep caller aObj aSize aData) (bRep : WordArrayRep caller bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
    findFunction context.program "fixed_multiply"=some fixed_multiply_ast ∧
    (    let entry : State F:={caller.enterScope with environment:=[]}
    ∃entered after iId finalData,
      bindParameters entry fixed_multiply_ast.parameters
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some entered ∧
      ExecList context entered ((ProductRow.items fixed_multiply_ast.body).take 3) .normal after ∧
      ProductOuter.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart
        (coreIds (ids entry.nextObject) iId) (fun _=>entry.scope)
        (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k)) finalData 5 ∧
      Locals after name type (ids entry.nextObject) entry.scope
        (value outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>aData (aStart+k))*
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>bData (bStart+k)) ∧
      (∀k,k<6 → after.load (wordPointer aObj (aStart+k))=some (.integer (integer64 (aData (aStart+k))))) ∧
      (∀k,k<6 → after.load (wordPointer bObj (bStart+k))=some (.integer (integer64 (bData (bStart+k))))) ∧
      (∀id,id<caller.nextObject → id≠workObj → after.objects id=caller.objects id)) := by
  have zeroSelected : findFunction context.program "zero_words"=some zero_words_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  have multiplySelected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast:=by
    rcases programPinned with w4 | fap
    · rw [w4];rfl
    · rw [fap];rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,multiplySelected,
    begin_execution context zeroSelected caller outObj outStart aObj aSize aStart bObj bSize bStart
      workObj workSize workStart aData bData workData well work aRep bRep aShape bShape aDisjoint bDisjoint
      aBound bBound workBound aDigits bDigits⟩

#print axioms source_begin_execution
end RH080Next.FFTPV.MultiplyParameters
