/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixTotalFrame
import FFTFixedMultiplySuffixMath
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

/-- Actual unchanged C bytes, independent supported syntax, exact source-tail
extraction, and the full operational suffix helper contract. This is not a
claim that the complete FFT C caller or ANT consumer has been verified. -/
theorem source_suffix_total {before : State Unit}
    {outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar → Nat} {old aData bData data : Nat → Nat}
    (locals : Bindings before pName pType ids owners (pValue outObj outStart aObj aStart bObj bStart workObj workStart 5))
    (well : WellScoped before) (outRep : WordArrayRep before outObj outSize old)
    (aRep : WordArrayRep before aObj aSize aData) (bRep : WordArrayRep before bObj bSize bData)
    (workRep : WordArrayRep before workObj workSize data)
    (separate : ∀v,outObj≠ids v ∧ workObj≠ids v)
    (shape : workObj=outObj → workSize=outSize)
    (disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize)
    (workBound : workStart+10≤workSize) (digits : ∀k,k<10 → data (workStart+k)<1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      (match FFTRecursivePV.fixed_multiply_ast.body with | .block xs => xs.drop 3 | _ => [])=statements ∧
    (let sign:=signBit (aData (aStart+5)) (bData (bStart+5))
    ∃after,ExecList CopyLoop.sourceContext before statements
        (.returned (.integer (integer64 (finalStatus old data outStart workStart sign)))) after ∧
      WordArrayRep after outObj outSize (finalData old data outStart workStart sign) ∧
      ApplicationBirthFrame.Frame before.nextObject before after [outObj,ids PVar.i] ∧
      ∀after' flow,ExecList CopyLoop.sourceContext before statements flow after' →
        flow=.returned (.integer (integer64 (finalStatus old data outStart workStart sign))) ∧ after'=after) := by
  refine ⟨FFTRecursivePV.actual_source_syntax,actual_suffix,?_⟩
  obtain ⟨after,run,output,frame⟩:=suffix_framed CopyLoop.sourceContext (by rfl) (by rfl) locals well outRep aRep bRep workRep
    separate shape disjoint outBound aBound bBound workBound digits
  obtain ⟨canonical,known,knownOutput,every⟩:=suffix_total CopyLoop.sourceContext (by rfl) (by rfl) locals well outRep aRep bRep workRep
    separate shape disjoint outBound aBound bBound workBound digits
  have same:=(every after _ run).2
  cases same
  exact ⟨after,run,output,frame,every⟩

#print axioms source_suffix_total
end RH080Next.FFTPV.MultiplySuffix
