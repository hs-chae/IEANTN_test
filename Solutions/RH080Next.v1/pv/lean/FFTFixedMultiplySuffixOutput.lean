/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixMath
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix

/-- The actual computed suffix output is normalized. This holds even when its
computed status is nonzero; no successful output or normalized result is assumed. -/
theorem finalData_normalized (old data : Nat → Nat) (outStart workStart sign : Nat)
    (digits : ∀j,j<10 → data (workStart+j)<1000000000) (signBound : sign≤1) :
    (∀i,i<5 → finalData old data outStart workStart sign (outStart+i)<1000000000) ∧
      finalData old data outStart workStart sign (outStart+5)≤1 := by
  let raw:=retainedData old data outStart workStart sign
  let lost:=CanonicalSource.digitSum data workStart 4
  have rd : ∀i,i<5 → raw (outStart+i)<1000000000 := by
    intro i hi
    rw [show raw=retainedData old data outStart workStart sign from rfl,retainedData_digit old data outStart workStart sign i hi]
    exact digits (i+4) (by omega)
  have normalized : ∀i,i<5 → roundedData raw outStart sign lost (outStart+i)<1000000000 := by
    intro i hi
    unfold roundedData
    split
    · rw [IncrementSource.currentData_slice raw outStart 5 i hi]
      exact (FFT.Limbs.incrementDigits_bounds 1000000000 5 (by norm_num) (fun k => raw (outStart+k)) rd).2 i hi
    · exact rd i hi
  constructor
  · intro i hi
    rw [finalData,CanonicalSource.canonicalData_digit _ _ i hi]
    exact normalized i hi
  · rw [finalData,CanonicalSource.canonicalData_sign]
    split
    · omega
    · rw [roundedData_sign,retainedData_sign]
      exact signBound

#print axioms finalData_normalized
end RH080Next.FFTPV.MultiplySuffix
