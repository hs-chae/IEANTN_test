/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafCall
import FFTRecursiveCellModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals ApplicationBirthFrame

/-- Source-linked actual recursive leaf execution and integer operational trace.
This closes the genuine base case; it does not claim the recursive node case,
the complete main numerical consumer, or complete C FFT-to-ANT PV. -/
theorem source_leaf_execution
    (caller : State Unit) (outObj outSize inObj inSize twiddleObj workObj start index step total : Nat)
    (old input : Nat → Nat) (well : WellScoped caller)
    (output : WordArrayRep caller outObj outSize old)
    (inputRep : WordArrayRep caller inObj inSize input) (different : outObj ≠ inObj)
    (shape : IndexShape start index step 1 total)
    (outBound : 12*total ≤ outSize) (inBound : 12*total ≤ inSize)
    (table : Nat → List FFT.IntegerModel.CInt) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    ∃after data, Call CopyLoop.sourceContext "fft_recursive"
        (arguments outObj inObj twiddleObj workObj start index step 1 total)
        caller (.value (.integer (integer64 0))) after ∧
      WordArrayRep after outObj outSize data ∧
      WordArrayRep after inObj inSize input ∧
      FFT.IntegerModel.ExecutionTrace table (cell input) 0 index step [cell data start] ∧
      Frame caller.nextObject caller after [outObj] := by
  obtain ⟨after,called,outputAfter,inputAfter,frame⟩ := leaf_call CopyLoop.sourceContext (by rfl) (by rfl)
    caller outObj outSize inObj inSize twiddleObj workObj start index step total
    old input well output inputRep different shape outBound inBound
  exact ⟨FFTRecursivePV.actual_source_syntax,after,_,called,outputAfter,inputAfter,
    copied_leaf_trace table old input start index step,frame⟩

#print axioms source_leaf_execution
end RH080Next.FFTPV.RecursiveSource
