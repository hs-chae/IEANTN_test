/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyEveryCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals

/-- Completed source-to-model helper theorem: independent syntactic
correspondence, existence/termination, and correctness of every permitted full
Call. It verifies the actual copy helper, not the whole numerical FFT program.
The caller's actual typed input/output allocations are explicit preconditions. -/
theorem source_copy_words_total (before : State Unit)
    (outObject outLength outStart inObject inLength inStart length : Nat)
    (old input : Nat → Nat) (well : WellScoped before)
    (outRep : WordArrayRep before outObject outLength old)
    (inRep : WordArrayRep before inObject inLength input)
    (shape : inObject = outObject → inLength = outLength)
    (ranges : outObject ≠ inObject ∨ outStart = inStart ∨ outStart+length ≤ inStart ∨ inStart+length ≤ outStart)
    (outBound : outStart+length ≤ outLength) (inBound : inStart+length ≤ inLength)
    (fits : length < 2^64) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    (∃after, Call sourceContext "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after outObject outLength (prefixData old (fun i => input (inStart+i)) outStart length) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input (inStart+i))))) ∧
      CallerFrame before after outObject) ∧
    (∀after result, Call sourceContext "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before result after →
      result = .value (.integer (integer64 0)) ∧
      WordArrayRep after outObject outLength (prefixData old (fun i => input (inStart+i)) outStart length) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input (inStart+i)))))) := by
  obtain ⟨syntaxProof, existence⟩ := source_copy_words_call before
    outObject outLength outStart inObject inLength inStart length old input well outRep inRep
    shape ranges outBound inBound fits
  refine ⟨syntaxProof, existence, ?_⟩
  intro after result run
  exact every_copy_words_call (by rfl) before after outObject outLength outStart inObject inLength inStart length
    old input well outRep inRep shape ranges outBound inBound fits result run

#print axioms source_copy_words_total
end RH080Next.FFTPV.CopyLoop
