/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddInput
import FFTRecursiveHelpers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- Each actual fixed_add source is applicable to the real butterfly buffers,
with overflow freedom derived from the verified child/product norm bounds. -/
theorem butterfly_add_call {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner : Nat} {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) (i : Fin 4)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1)
    (leftNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair output ((start+j)*12))‖ ≤ 400)
    (tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair work 160)‖ ≤ 801) :
    let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    AddSource.AddCorrect context before p ∧ AddSource.rawStatus p=0 ∧
      CanonicalSource.represented (AddSource.finalData p) (p.layout.start .out)=
        if i.val<2 then
          CanonicalSource.represented output ((start+j)*12+6*(addComponent i).val)+
            CanonicalSource.represented work (160+6*(addComponent i).val)
        else
          CanonicalSource.represented output ((start+j)*12+6*(addComponent i).val)-
            CanonicalSource.represented work (160+6*(addComponent i).val) := by
  dsimp only
  have zero := butterfly_add_status_zero buffers start index step n half j shape split active i
    input table output work leftNormalized tempDigits tempSigns leftNorm tempNorm
  refine ⟨?_,zero,?_⟩
  · apply AddSource.fixed_add_total context helpers.add helpers.compare helpers.canonical before _ h.well
    intro r
    cases r
    · by_cases hi : i.val<2
      · simpa [butterflyAddInput,butterflyAddLayout,bufferData,hi] using h.arrays .work
      · simpa [butterflyAddInput,butterflyAddLayout,bufferData,hi] using h.arrays .output
    · simpa [butterflyAddInput,butterflyAddLayout,bufferData] using h.arrays .output
    · simpa [butterflyAddInput,butterflyAddLayout,bufferData] using h.arrays .work
  · have correct := AddSource.finalData_integer_correct _ zero
    by_cases hi : i.val<2
    · simpa [butterflyAddInput,butterflyAddLayout,bufferData,hi] using correct
    · simpa [butterflyAddInput,butterflyAddLayout,bufferData,hi] using correct

#print axioms butterfly_add_call
end RH080Next.FFTPV.RecursiveSource
