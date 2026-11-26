/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFourierPair

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

/-- Exact source normalization of the Mellin test function, proved by change
of variables in the actual Fourier integral. -/
theorem fourier_mellin_kernel (f : ℝ → ℂ) (d L : ℝ) (hd : 0 < d) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (d:ℂ)*f ((d/(2*π))*r)*Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) ξ =
      (2*π:ℝ) • 𝓕 f ((2*π*ξ-L)/d) := by
  let Δ : ℝ := d/(2*π)
  let η : ℝ := (2*π*ξ-L)/d
  let g : ℝ → ℂ := fun u => Complex.exp ((-2*π*u*η:ℝ)*Complex.I)*f u
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ0 := hΔ.ne'
  have heq : (fun r : ℝ => Complex.exp ((-2*π*r*ξ:ℝ)*Complex.I)*
      ((d:ℂ)*f (Δ*r)*Complex.exp (Complex.I*(L:ℂ)*(r:ℂ)))) =
      (fun r : ℝ => (d:ℂ)*g (Δ*r)) := by
    funext r
    have hphase : ((-2*π*r*ξ:ℝ):ℂ)*Complex.I + Complex.I*(L:ℂ)*(r:ℂ) =
        ((-2*π*(Δ*r)*η:ℝ):ℂ)*Complex.I := by
      have hr : -2*π*r*ξ+L*r = -2*π*(Δ*r)*η := by
        dsimp [Δ,η]
        field_simp
        <;> ring
      rw [← show (((-2*π*r*ξ+L*r:ℝ):ℂ)*Complex.I) =
        ((-2*π*r*ξ:ℝ):ℂ)*Complex.I + Complex.I*(L:ℂ)*(r:ℂ) by push_cast; ring,
        hr]
    dsimp only [g]
    calc
      _ = (d:ℂ)*((Complex.exp ((-2*π*r*ξ:ℝ)*Complex.I)*
          Complex.exp (Complex.I*(L:ℂ)*(r:ℂ)))*f (Δ*r)) := by ring
      _ = (d:ℂ)*(Complex.exp (((-2*π*r*ξ:ℝ):ℂ)*Complex.I+
          Complex.I*(L:ℂ)*(r:ℂ))*f (Δ*r)) := by rw [Complex.exp_add]
      _ = _ := by rw [hphase]
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  change (∫ r : ℝ, Complex.exp ((-2*π*r*ξ:ℝ)*Complex.I)*
      ((d:ℂ)*f (Δ*r)*Complex.exp (Complex.I*(L:ℂ)*(r:ℂ)))) = (2*π:ℝ) • (∫ u : ℝ, g u)
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left g Δ,
    abs_of_pos (inv_pos.mpr hΔ)]
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcoef : (d:ℂ)*(Δ⁻¹:ℝ) = (2*π:ℝ) := by
    dsimp [Δ]
    push_cast
    field_simp [hdC]
  simp only [Complex.real_smul, ← mul_assoc, hcoef]

/-- The true compactly supported Fourier transform of the actual Mellin
kernel; this is the transform used in CMS Lemma6 and the Mellin derivation. -/
theorem fourier_mellin_affine_kernel (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (d L : ℝ) (hd : 0 < d) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (d:ℂ)*(inverseCosine (affineSpectrum nodes m) ((d/(2*π))*r):ℂ)*
      Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) ξ =
      (2*π:ℝ) • (affineSpectrum nodes m ((2*π*ξ-L)/d):ℂ) := by
  rw [fourier_mellin_kernel (fun u : ℝ => (inverseCosine (affineSpectrum nodes m) u:ℂ)) d L hd ξ,
    fourier_affine_inverse_eq_window nodes m hlen hm hlast]

/-- The same transform formula for the entire extension supplied to CMS6,
using its proved equality with the actual affine amplitude on the real axis. -/
theorem fourier_mellin_extension (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*(r:ℂ))*
      Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) ξ =
      (2*π:ℝ) • (affineSpectrum nodes m ((2*π*ξ-L)/d):ℂ) := by
  have heq : (fun r : ℝ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*(r:ℂ))*
      Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) =
      (fun r : ℝ => (d:ℂ)*(inverseCosine (affineSpectrum nodes m) ((d/(2*π))*r):ℂ)*
        Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) := by
    funext r
    rw [← Complex.ofReal_mul, hreal]
  rw [heq]
  exact fourier_mellin_affine_kernel nodes m hlen hm hlast d L hd ξ

end RH080Next.Explicit
