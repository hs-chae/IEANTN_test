/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveTotal
import FapFFTRecursiveSource
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The unchanged Fap source resolves every recursive helper to the exact
already-verified source function; no favorable foreign-call behavior is used. -/
theorem fap_helpers {F : Type} (context : Context F)
    (sourceProgram : context.program=FapFFTRecursivePV.program) : Helpers context := by
  constructor <;> rw [sourceProgram] <;> rfl

theorem w4_helpers {F : Type} (context : Context F)
    (sourceProgram : context.program=FFTRecursivePV.program) : Helpers context := by
  constructor <;> rw [sourceProgram] <;> rfl

/-- Physical words consumed by the real main continuation are protected,
including the complete twelve-word root and six-word sum/quadrature slots. -/
theorem CallPost.protected_words {F : Type} {total : Nat} {buffers : Buffers total}
    {s start index step : Nat} {input table oldOutput oldWork output work : Nat → Nat}
    {before after : State F} (h : CallPost buffers s start index step input table oldOutput oldWork before after output work) :
    (∀k,k<12 → work (128+k)=oldWork (128+k)) ∧
    (∀k,k<6 → work (192+k)=oldWork (192+k)) ∧
    (∀k,k<6 → work (208+k)=oldWork (208+k)) := by
  have size:=buffers.workBound
  exact ⟨fun k hk=>h.workOutside _ (by omega) (by omega) (by omega),
    fun k hk=>h.workOutside _ (by omega) (by omega) (by omega),
    fun k hk=>h.workOutside _ (by omega) (by omega) (by omega)⟩

/-- Exact original Fap n=2^17 recursion, with independently parsed source,
actual total/every Call, trace and physical caller words. -/
theorem fap_recursive17_total {F : Type} (context : Context F)
    (sourceProgram : context.program=FapFFTRecursivePV.program)
    (buffers : Buffers 131072) (input table : Nat → Nat)
    (inputNormalized : ∀k,k<131072 → NormalizedCell input k)
    (tableNormalized : ∀k,k<65536 → NormalizedCell table k)
    (mass : FFT.coefficientMass 131072 (fun j=>FFT.IntegerModel.decode (cell input j))≤362)
    (twiddleError : ∀t,t<17 → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((stages table 131072 (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ)) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
    StrongContract context buffers input table 17 0 0 1 := by
  refine ⟨FapFFTRecursivePV.actual_source_syntax,?_⟩
  apply recursive_strong_total context (fap_helpers context sourceProgram) buffers input table 17
    (by norm_num) (by norm_num) inputNormalized tableNormalized mass twiddleError 17 0 0 1 (le_refl _)
  constructor <;> norm_num

/-- Exact original W4 n=2^24 recursion. Mathematical input hypotheses refer
to actual input/table words; no recursion output or source success is assumed. -/
theorem w4_recursive24_total {F : Type} (context : Context F)
    (sourceProgram : context.program=FFTRecursivePV.program)
    (buffers : Buffers 16777216) (input table : Nat → Nat)
    (inputNormalized : ∀k,k<16777216 → NormalizedCell input k)
    (tableNormalized : ∀k,k<8388608 → NormalizedCell table k)
    (mass : FFT.coefficientMass 16777216 (fun j=>FFT.IntegerModel.decode (cell input j))≤362)
    (twiddleError : ∀t,t<24 → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((stages table 16777216 (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ)) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    StrongContract context buffers input table 24 0 0 1 := by
  refine ⟨FFTRecursivePV.actual_source_syntax,?_⟩
  apply recursive_strong_total context (w4_helpers context sourceProgram) buffers input table 24
    (by norm_num) (by norm_num) inputNormalized tableNormalized mass twiddleError 24 0 0 1 (le_refl _)
  constructor <;> norm_num

#print axioms CallPost.protected_words
#print axioms fap_recursive17_total
#print axioms w4_recursive24_total
end RH080Next.FFTPV.RecursiveSource
