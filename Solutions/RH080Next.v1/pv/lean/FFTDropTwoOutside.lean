/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource

theorem roundData_outside (old : Nat→Nat) (start k : Nat) (outside : k<start ∨ start+6≤k) :
    roundData old start k=old k := by
  unfold roundData
  split
  · exact dropped_outside old start k outside
  · have away : ¬(start≤k ∧ k<start+6):=by omega
    simp only [IncrementSource.currentData,if_neg away]
    exact dropped_outside old start k outside

#print axioms roundData_outside
end RH080Next.FFTPV.DropTwoSource
