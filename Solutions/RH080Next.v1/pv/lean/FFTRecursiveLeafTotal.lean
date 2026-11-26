/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafUniversal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals ApplicationBirthFrame

/-- Source correspondence, actual total Call, exact leaf trace, full caller
frame and correctness of EVERY possible source Call at n=1. This is a complete
base-case helper contract, not completion of the nonleaf FFT or ANT program. -/
theorem source_leaf_total
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
      Frame caller.nextObject caller after [outObj] ∧
      ∀other result, Call CopyLoop.sourceContext "fft_recursive"
        (arguments outObj inObj twiddleObj workObj start index step 1 total) caller result other →
        result = .value (.integer (integer64 0)) ∧ other = after := by
  obtain ⟨hSyntax,after,data,called,outputAfter,inputAfter,trace,frame⟩ := source_leaf_execution
    caller outObj outSize inObj inSize twiddleObj workObj start index step total
    old input well output inputRep different shape outBound inBound table
  refine ⟨hSyntax,after,data,called,outputAfter,inputAfter,trace,frame,?_⟩
  intro other result otherCall
  have bounds := shape.scalar_bounds
  exact leaf_call_unique (by rfl) (by rfl) well bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.2 called otherCall

#print axioms source_leaf_total
end RH080Next.FFTPV.RecursiveSource
