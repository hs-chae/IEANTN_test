/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyComplexInput
import FFTRecursiveHelpers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The real complex helper is applicable to the actual butterfly buffers;
its four source products/two additions execute and produce the exact integer
model product. No C output, scratch initializer or numerical answer is assumed. -/
theorem butterfly_complex_call {F : Type} (context : Context F) (helpers : Helpers context)
    {state : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner : Nat} {ids : LoopVar → Nat}
    {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half)
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) :
    let p := butterflyComplexInput buffers start index step n half j shape split active
      input table output work rightNormalized twiddleNormalized rightNorm twiddleNorm
    ComplexSource.Correct context state p ∧
      ComplexSource.resultPair p = FFT.IntegerModel.mul (cell output (start+j+half))
        (cell table (j*(total/n))) := by
  dsimp only
  constructor
  · apply ComplexSource.complex_multiply_correct context helpers.complex helpers.multiply helpers.zero
      helpers.increment helpers.add helpers.compare helpers.canonical state _ h.well
    intro r
    cases r
    · simpa [butterflyComplexInput,butterflyComplexLayout,bufferData] using h.arrays .work
    · simpa [butterflyComplexInput,butterflyComplexLayout,bufferData] using h.arrays .output
    · simpa [butterflyComplexInput,butterflyComplexLayout,bufferData] using h.arrays .twiddle
    · simpa [butterflyComplexInput,butterflyComplexLayout,bufferData] using h.arrays .work
  · rw [ComplexSource.resultPair_eq_integer_mul]
    simp [butterflyComplexInput,butterflyComplexLayout,ComplexSource.pair,cell,bufferData,Nat.mul_comm]

#print axioms butterfly_complex_call
end RH080Next.FFTPV.RecursiveSource
