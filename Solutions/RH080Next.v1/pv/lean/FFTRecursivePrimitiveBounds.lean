/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCellModel
import FFTComplexIntegerBridge
import FFTIntermediateBounds
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open WordArrays

/-- The actual six-word source magnitude is the absolute represented integer,
including either permitted sign and the canonical zero case. -/
theorem represented_abs (data : Nat → Nat) (start : Nat) :
    |(CanonicalSource.represented data start : ℝ)| =
      (FFT.Limbs.magnitude 1000000000 5 (fun j => data (start+j)) : ℝ) := by
  unfold CanonicalSource.represented FFT.Limbs.signed
  split <;> simp

/-- The verified complex norm bound supplies the actual scalar helper domain;
this does not assume that a C FFT computation returned a bounded answer. -/
theorem component_magnitude_of_norm (data : Nat → Nat) (k M : Nat)
    (bound : ‖FFT.IntegerModel.decode (cell data k)‖ ≤ (M:ℝ)) :
    ∀c : Fin 2, FFT.Limbs.magnitude 1000000000 5
      (fun j => data (12*k+6*c.val+j)) ≤ M*FFT.IntegerModel.unit := by
  have positive : (0:ℝ) < (FFT.IntegerModel.unit:ℝ) := by norm_num [FFT.IntegerModel.unit]
  have realPart := (Complex.abs_re_le_norm (FFT.IntegerModel.decode (cell data k))).trans bound
  have imagPart := (Complex.abs_im_le_norm (FFT.IntegerModel.decode (cell data k))).trans bound
  intro c
  fin_cases c
  · have r : |(CanonicalSource.represented data (12*k):ℝ)| ≤
        (M:ℝ)*(FFT.IntegerModel.unit:ℝ) := by
      apply (div_le_iff₀ positive).1
      simpa [FFT.IntegerModel.decode,cell,abs_div,abs_of_pos positive] using realPart
    rw [represented_abs] at r
    exact_mod_cast r
  · have r : |(CanonicalSource.represented data (12*k+6):ℝ)| ≤
        (M:ℝ)*(FFT.IntegerModel.unit:ℝ) := by
      apply (div_le_iff₀ positive).1
      simpa [FFT.IntegerModel.decode,cell,abs_div,abs_of_pos positive] using imagPart
    rw [represented_abs] at r
    exact_mod_cast r

#print axioms component_magnitude_of_norm
end RH080Next.FFTPV.RecursiveSource
