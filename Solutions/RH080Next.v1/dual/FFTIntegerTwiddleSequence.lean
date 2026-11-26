/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTGlobalTraceBounds
import W4FFTGlobalTraceBounds
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFT.IntegerModel
open Complex

def sequence (seed : CInt) : Nat → CInt
  | 0 => (unit,0)
  | k+1 => mul (sequence seed k) seed

theorem sequence_decode_zero (seed : CInt) : decode (sequence seed 0)=1 := decode_unit

theorem sequence_decode_step (seed : CInt) (k : Nat) :
    ‖decode (sequence seed (k+1))-decode seed*decode (sequence seed k)‖≤4/(unit:ℝ) := by
  rw [sequence,decode_mul,roundedComplex_comm]
  exact roundedComplex_error _ _

theorem decode_root17 : decode (root 131072)=rootSeed17 := by
  have exact : root 131072=(999999998851026827562673307794554109,-47936899603066884549003990494659) := by decide
  rw [exact]
  apply Complex.ext <;> norm_num [decode,unit,rootSeed17]

theorem decode_root24 : decode (root 16777216)=rootSeed := by
  have exact : root 16777216=(999999999999929872242879801239728737,-374507028292384123903169179084) := by decide
  rw [exact]
  apply Complex.ext <;> norm_num [decode,unit,rootSeed]

theorem sequence17_error (k : Nat) (hk : k≤65536) :
    ‖decode (sequence (root 131072) k)-negativeRoot 131072^k‖≤(1/100000000000000000000:ℝ) := by
  apply fft17_twiddle_bound (fun j=>decode (sequence (root 131072) j)) (sequence_decode_zero _) ?_ k hk
  intro j _
  simpa [decode_root17,unit] using sequence_decode_step (root 131072) j

theorem sequence24_error (k : Nat) (hk : k≤8388608) :
    ‖decode (sequence (root 16777216) k)-negativeRoot 16777216^k‖≤(1/10000000000000000000:ℝ) := by
  apply fft24_twiddle_bound (fun j=>decode (sequence (root 16777216) j)) (sequence_decode_zero _) ?_ k hk
  intro j _
  simpa [decode_root24,unit] using sequence_decode_step (root 16777216) j

theorem components_of_decode_norm (z : CInt) (bound : ‖decode z‖≤2) :
    z.1.natAbs≤2*10^36 ∧ z.2.natAbs≤2*10^36 := by
  have hu : (0:ℝ)<unit := by norm_num [unit]
  have re:= (Complex.abs_re_le_norm (decode z)).trans bound
  have im:= (Complex.abs_im_le_norm (decode z)).trans bound
  change |(z.1:ℝ)/(unit:ℝ)|≤2 at re
  change |(z.2:ℝ)/(unit:ℝ)|≤2 at im
  rw [abs_div,abs_of_pos hu] at re im
  have re' : |(z.1:ℝ)|≤(2*10^36:Nat) := by
    have h := (div_le_iff₀ hu).mp re
    norm_num [unit] at h ⊢
    exact h
  have im' : |(z.2:ℝ)|≤(2*10^36:Nat) := by
    have h := (div_le_iff₀ hu).mp im
    norm_num [unit] at h ⊢
    exact h
  constructor
  · have h : |z.1|≤(2*10^36:Nat) := by exact_mod_cast re'
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  · have h : |z.2|≤(2*10^36:Nat) := by exact_mod_cast im'
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h

theorem sequence17_components (k : Nat) (hk : k≤65536) :
    (sequence (root 131072) k).1.natAbs≤2*10^36 ∧
    (sequence (root 131072) k).2.natAbs≤2*10^36 := by
  apply components_of_decode_norm
  have h:=norm_le_norm_sub_add (decode (sequence (root 131072) k)) (negativeRoot 131072^k)
  rw [norm_pow,negativeRoot_norm,one_pow] at h
  linarith [sequence17_error k hk]

theorem sequence24_components (k : Nat) (hk : k≤8388608) :
    (sequence (root 16777216) k).1.natAbs≤2*10^36 ∧
    (sequence (root 16777216) k).2.natAbs≤2*10^36 := by
  apply components_of_decode_norm
  have h:=norm_le_norm_sub_add (decode (sequence (root 16777216) k)) (negativeRoot 16777216^k)
  rw [norm_pow,negativeRoot_norm,one_pow] at h
  linarith [sequence24_error k hk]

#print axioms sequence17_error
#print axioms sequence24_error
#print axioms sequence17_components
#print axioms sequence24_components
end RH080Next.FFT.IntegerModel
