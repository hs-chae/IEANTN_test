/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineSignedMoment
import WindowSourceFinal

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.W4SourceMoment
open RH080Next.Explicit

def window : ℝ → ℝ := affineSpectrum WindowPV.Data.affineNodes 360
def amplitude : ℝ → ℝ := inverseCosine window

def sourceSignedUpper (f0 v1 mu2 : ℕ) : ℝ :=
  ((v1:ℝ)/10000000000000000)/(2*π^2) -
  2*((f0:ℝ)/(360*10000000000000000))*(3/8)*(1-log (3/8)) +
  40*((mu2:ℝ)/(6*360^3*1000000000))*(3/8)^3*(1/9-log (3/8)/3)

private theorem hlen : 2 ≤ WindowPV.Data.affineNodes.length := by
  rw [WindowPV.Data.affineNodes_length]
  norm_num

private theorem hlast : node WindowPV.Data.affineNodes
    (WindowPV.Data.affineNodes.length-1) = 0 := by
  unfold node WindowPV.Data.affineNodes
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
  norm_num

/-- Every accepted output of the actual C source program bounds the actual
Fourier signed-log integral. The source syntax and C main execution contained
in h are genuinely consumed through the finite nodal refinement theorem. -/
theorem source_output_signed_log_bound (f0 area height v0 v1 mu2 maximum : ℕ)
    (h : WindowPV.SourceScalarOutput f0 area height v0 v1 mu2 maximum) :
    (∫ u : ℝ, |amplitude u| *log |u|) ≤ sourceSignedUpper f0 v1 mu2 := by
  obtain ⟨hF,hH,hV,hM⟩ := WindowPV.source_output_mathematical_boundaries
    f0 area height v0 v1 mu2 maximum h
  have hb := signed_log_affine_inverse_three_eighths WindowPV.Data.affineNodes 360
    hlen (by norm_num) hlast
  unfold nodalSignedLogUpper at hb
  rw [hF,hV] at hb
  have hc : 0 ≤ 40*(3/8:ℝ)^3*(1/9-log (3/8)/3) := by
    have hl : log (3/8:ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hM hc
  unfold sourceSignedUpper
  unfold amplitude window
  nlinarith

/-- Completed source-first numerical moment provider for the original w4
window. This does not claim that the original FFT norm program is verified. -/
theorem source_first_signed_log_bound :
    (∫ u : ℝ, |amplitude u| *log |u|) ≤
      sourceSignedUpper 3599999999999999998 40713308729275680 69452659995205718 :=
  source_output_signed_log_bound _ _ _ _ _ _ _ WindowPV.actual_source_scalar_output

#print axioms source_output_signed_log_bound
#print axioms source_first_signed_log_bound
end RH080Next.W4SourceMoment
