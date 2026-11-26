/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexIntegerBridge
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals

def SourceCorrect {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  Correct context before input ∧ resultPair input=FFT.IntegerModel.mul
    (pair (input.old (input.layout.object .a)) (input.layout.start .a))
    (pair (input.old (input.layout.object .b)) (input.layout.start .b))

/-- Both literal preserved C texts are connected through independent syntax,
actual selected functions, full operational execution and normalized signed
arithmetic to the exact paired-integer operation used by FFT traces. This is a
completed helper contract; the complete FFT/ANT program connection is separate. -/
theorem source_complex_multiply_correct {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    (caller : State F) (input : Input) (well : WellScoped caller)
    (rep : ∀r,WordArrayRep caller (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      SourceCorrect context caller input:=by
  have selected : findFunction context.program "complex_multiply"=some complex_multiply_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have multiplySelected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have zeroSelected : findFunction context.program "zero_words"=some zero_words_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have incSelected : findFunction context.program "increment_words"=some increment_words_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have addSelected : findFunction context.program "fixed_add"=some fixed_add_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  have canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast:=by
    rcases programPinned with w4|fap
    · rw [w4];rfl
    · rw [fap];rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    complex_multiply_correct context selected multiplySelected zeroSelected incSelected addSelected compareSelected canonSelected caller input well rep,
    resultPair_eq_integer_mul input⟩

#print axioms source_complex_multiply_correct
end RH080Next.FFTPV.ComplexSource
