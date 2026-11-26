/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleLoop
import FFTIntegerTwiddleSequence
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource

theorem sequence_eq (seed : FFT.IntegerModel.CInt) (k : Nat) :
    sequence seed k=FFT.IntegerModel.sequence seed k := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [sequence,FFT.IntegerModel.sequence,ih]

theorem fixed_values_small (n : Nat) (original : n=131072 ∨ n=16777216) (k : Nat) (hk : k<n/2) :
    (sequence (FFT.IntegerModel.root n) k).1.natAbs≤1000*10^36 ∧
    (sequence (FFT.IntegerModel.root n) k).2.natAbs≤1000*10^36 := by
  rw [sequence_eq]
  rcases original with rfl|rfl
  · have h:=FFT.IntegerModel.sequence17_components k (by omega)
    constructor <;> omega
  · have h:=FFT.IntegerModel.sequence24_components k (by omega)
    constructor <;> omega

theorem fixed_root_small (n : Nat) (original : n=131072 ∨ n=16777216) :
    (FFT.IntegerModel.root n).1.natAbs≤1000*10^36 ∧ (FFT.IntegerModel.root n).2.natAbs≤1000*10^36 := by
  rcases original with rfl|rfl <;> decide

#print axioms sequence_eq
#print axioms fixed_values_small
#print axioms fixed_root_small
end RH080Next.FFTPV.TwiddleSource
