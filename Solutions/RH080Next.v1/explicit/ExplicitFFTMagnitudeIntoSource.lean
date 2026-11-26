/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTMagnitudeIntoMath
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MagnitudeIntoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals

def Correct {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  (∃after,Call context "magnitude_into" (arguments input) before (.value (.integer (integer64 0))) after ∧
    RootSource.EveryCall context before "magnitude_into" (arguments input) (.value (.integer (integer64 0))) after ∧
    WordArrayRep after input.object input.size (finalData input) ∧ IncrementSource.FullCallerFrame before after input.object) ∧
  (∀k<6,finalData input (input.start+k)<base) ∧ finalData input (input.start+5)=0 ∧
  FFT.Limbs.magnitude base 5 (fun k=>finalData input (input.start+k))=input.value ∧
  ∀k,(k< input.start ∨ input.start+6≤k) → finalData input k=input.old k

theorem magnitude_into_total {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_into"=some magnitude_into_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (before : State F) (input : Input) (well : WellScoped before) (rep : WordArrayRep before input.object input.size input.old) :
    Correct context before input:=
  ⟨magnitude_into_call context selected zeroSelected before input well rep,finalData_normalized input,
    finalData_sign input,finalData_magnitude input,finalData_outside input⟩

theorem source_magnitude_into_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : WordArrayRep before input.object input.size input.old) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧ Correct CompareSource.sourceContext before input:=
  ⟨RH080Next.FFTPV.actual_source_syntax,magnitude_into_total _ (by rfl) (by rfl) before input well rep⟩
theorem fap_source_magnitude_into_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : WordArrayRep before input.object input.size input.old) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧ Correct CompareSource.fapSourceContext before input:=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,magnitude_into_total _ (by rfl) (by rfl) before input well rep⟩
theorem recursive_source_magnitude_into_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : WordArrayRep before input.object input.size input.old) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧ Correct AddSource.recursiveContext before input:=
  ⟨FFTRecursivePV.actual_source_syntax,magnitude_into_total _ (by rfl) (by rfl) before input well rep⟩
theorem fap_recursive_source_magnitude_into_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : WordArrayRep before input.object input.size input.old) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧ Correct AddSource.fapRecursiveContext before input:=
  ⟨FapFFTRecursivePV.actual_source_syntax,magnitude_into_total _ (by rfl) (by rfl) before input well rep⟩

#print axioms magnitude_into_total
#print axioms source_magnitude_into_total
#print axioms fap_source_magnitude_into_total
#print axioms recursive_source_magnitude_into_total
#print axioms fap_recursive_source_magnitude_into_total
end RH080Next.FFTPV.MagnitudeIntoSource
