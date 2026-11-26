/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursivePrimitiveBounds
import ExplicitFFTAddMath
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

/-- The verified norm of an arbitrary actual twelve-word source slice bounds
both actual magnitude operands in the C helper's Nat-valued scale. -/
theorem pair_magnitude_of_norm (data : Nat → Nat) (start M : Nat)
    (bound : ‖FFT.IntegerModel.decode (ComplexSource.pair data start)‖ ≤ (M:ℝ)) :
    ∀c : Fin 2, FFT.Limbs.magnitude 1000000000 5
      (fun j => data (start+6*c.val+j)) ≤ M*ComplexSource.unit := by
  have positive : (0:ℝ) < (FFT.IntegerModel.unit:ℝ) := by norm_num [FFT.IntegerModel.unit]
  have realPart := (Complex.abs_re_le_norm (FFT.IntegerModel.decode (ComplexSource.pair data start))).trans bound
  have imagPart := (Complex.abs_im_le_norm (FFT.IntegerModel.decode (ComplexSource.pair data start))).trans bound
  intro c
  fin_cases c
  · have r : |(CanonicalSource.represented data start:ℝ)| ≤ (M:ℝ)*(FFT.IntegerModel.unit:ℝ) := by
      apply (div_le_iff₀ positive).1
      simpa [FFT.IntegerModel.decode,ComplexSource.pair,abs_div,abs_of_pos positive] using realPart
    rw [represented_abs] at r
    norm_num [FFT.IntegerModel.unit,ComplexSource.unit] at r ⊢
    exact_mod_cast r
  · have r : |(CanonicalSource.represented data (start+6):ℝ)| ≤ (M:ℝ)*(FFT.IntegerModel.unit:ℝ) := by
      apply (div_le_iff₀ positive).1
      simpa [FFT.IntegerModel.decode,ComplexSource.pair,abs_div,abs_of_pos positive] using imagPart
    rw [represented_abs] at r
    norm_num [FFT.IntegerModel.unit,ComplexSource.unit] at r ⊢
    exact_mod_cast r

/-- All four butterfly additions fit the actual five-digit C arithmetic;
the bound comes from verified child/product norms, not an overflow premise. -/
theorem butterfly_add_capacity (left temp : Nat → Nat) (leftStart : Nat)
    (leftNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair left leftStart)‖ ≤ 400)
    (tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair temp 160)‖ ≤ 801)
    (c : Fin 2) :
    FFT.Limbs.magnitude IncrementSource.base 5 (fun k => left (leftStart+6*c.val+k)) +
      FFT.Limbs.magnitude IncrementSource.base 5 (fun k => temp (160+6*c.val+k)) < IncrementSource.base^5 := by
  have l := pair_magnitude_of_norm left leftStart 400 leftNorm c
  have t := pair_magnitude_of_norm temp 160 801 tempNorm c
  have small : 400*ComplexSource.unit+801*ComplexSource.unit < IncrementSource.base^5 := by
    norm_num [ComplexSource.unit,IncrementSource.base]
  exact (add_le_add l t).trans_lt small

#print axioms butterfly_add_capacity
end RH080Next.FFTPV.RecursiveSource
