/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveSourceLayout
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource

/-- The source's two output indices and stride-selected global twiddle are in
bounds at every actual butterfly. No uint64 wrap or truncated index is used. -/
theorem butterfly_indices {start index step n total half j : Nat}
    (h : IndexShape start index step n total) (split : n=2*half) (hj : j<half) :
    start+j<total ∧ start+j+half<total ∧
      j*(total/n)<total/2 ∧ (j*(total/n))*12+12≤6*total := by
  have hs := h.step_positive
  have hp := h.stride
  have ho := h.output
  have halfTotal : total/2=half*step := by
    have equal : total=2*(half*step) := by nlinarith
    rw [equal]
    omega
  have mulBound : j*step<half*step := Nat.mul_lt_mul_of_pos_right hj hs
  have tableIndex : j*(total/n)<total/2 := by
    rw [h.stride_exact,halfTotal]
    exact mulBound
  refine ⟨by omega,by omega,tableIndex,?_⟩
  omega

/-- All integer products used to address a butterfly cell fit the real u64
source arithmetic. Pointer validity is separately proved from actual arrays. -/
theorem butterfly_word_offsets {start index step n total half j : Nat}
    (h : IndexShape start index step n total) (split : n=2*half) (hj : j<half) :
    (start+j)*12<2^64 ∧ (start+j+half)*12<2^64 ∧
      j*(total/n)<2^64 ∧ (j*(total/n))*12<2^64 := by
  have hb := butterfly_indices h split hj
  have small := h.total_small
  omega

#print axioms butterfly_indices
end RH080Next.FFTPV.RecursiveSource
