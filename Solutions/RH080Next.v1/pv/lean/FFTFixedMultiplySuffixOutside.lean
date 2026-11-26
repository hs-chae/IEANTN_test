/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixOutput
set_option autoImplicit false
namespace RH080Next.FFTPV.MultiplySuffix

/-- Exact pointwise preservation by the computed suffix, stronger than an
object-level caller frame when output and scratch share one large allocation. -/
theorem finalData_outside (old data : Nat → Nat) (outStart workStart sign index : Nat)
    (outside : index < outStart ∨ outStart+6 ≤ index) :
    finalData old data outStart workStart sign index=old index := by
  have different : index≠outStart+5:=by omega
  have noRange : ¬(outStart ≤ index ∧ index < outStart+5):=by omega
  have canon : ∀a : Nat → Nat,CanonicalSource.canonicalData a outStart index=a index := by
    intro a
    unfold CanonicalSource.canonicalData
    split
    · exact Function.update_of_ne different _ _
    · rfl
  rw [finalData,canon]
  unfold roundedData
  split
  · simp only [IncrementSource.currentData,if_neg noRange]
    simp [retainedData,copied,CopyLoop.prefixData,Function.update_of_ne different,noRange]
  · simp [retainedData,copied,CopyLoop.prefixData,Function.update_of_ne different,noRange]

#print axioms finalData_outside
end RH080Next.FFTPV.MultiplySuffix
