/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinFourier
import ExplicitGuinandWeilApplication

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

def mellinTest (H : ℂ → ℂ) (d L : ℝ) (z : ℂ) : ℂ :=
  (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*z)*Complex.exp (Complex.I*(L:ℂ)*z)

theorem fourier_mellinTest_zero (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L) :
    𝓕 (fun u : ℝ => mellinTest H d L (u:ℂ)) 0 = 0 := by
  rw [show (fun u : ℝ => mellinTest H d L (u:ℂ)) =
    (fun u : ℝ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*(u:ℂ))*Complex.exp (Complex.I*(L:ℂ)*(u:ℂ))) by rfl,
    fourier_mellin_extension nodes m hlen hm hlast H hreal d L hd]
  have hv : radius nodes m ≤ |(2*π*0-L)/d| := by
    have h := (lt_div_iff₀ hd).mpr hpositive
    have ha := le_abs_self (L/d)
    simpa only [mul_zero, zero_sub, neg_div, abs_neg] using h.le.trans ha
  rw [affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ hv]
  simp

theorem fourier_mellinTest_negative_frequency (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L)
    (n : CMSPrimeIndex) :
    𝓕 (fun u : ℝ => mellinTest H d L (u:ℂ)) (-log (n:ℕ)/(2*π)) = 0 := by
  change 𝓕 (fun u : ℝ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*(u:ℂ))*
    Complex.exp (Complex.I*(L:ℂ)*(u:ℂ))) (-log (n:ℕ)/(2*π)) = 0
  rw [fourier_mellin_extension nodes m hlen hm hlast H hreal d L hd]
  have hn : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast (show 1 ≤ (n:ℕ) by omega)
  have hlog := Real.log_nonneg hn
  have harg : (2*π*(-log (n:ℕ)/(2*π))-L)/d = -((log (n:ℕ)+L)/d) := by
    field_simp
    <;> ring
  have hv : radius nodes m ≤ |(2*π*(-log (n:ℕ)/(2*π))-L)/d| := by
    rw [harg, abs_neg]
    apply le_trans _ (le_abs_self _)
    apply (le_div_iff₀ hd).mpr
    linarith
  rw [affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ hv]
  simp

def mellinArithmeticWeight (nodes : List ℚ) (m : ℕ) (d L y : ℝ) : ℝ :=
  affineSpectrum nodes m ((log y-L)/d)/sqrt y

/-- The actual arithmetic family of CMS6 reduces to the desired weighted
von-Mangoldt family; the reflected frequency really vanishes by positive
support. -/
theorem cmsPrimeFamily_mellinTest (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L)
    (n : CMSPrimeIndex) :
    cmsPrimeFamily (mellinTest H d L) n =
      ((2*π*(ArithmeticFunction.vonMangoldt (n:ℕ):ℝ)*mellinArithmeticWeight nodes m d L (n:ℕ):ℝ):ℂ) := by
  unfold cmsPrimeFamily
  rw [fourier_mellinTest_negative_frequency nodes m hlen hm hlast H hreal d L hd hpositive n, add_zero]
  have hpos := fourier_mellin_extension nodes m hlen hm hlast H hreal d L hd (log (n:ℕ)/(2*π))
  change 𝓕 (fun u : ℝ => mellinTest H d L (u:ℂ)) (log (n:ℕ)/(2*π)) = _ at hpos
  rw [hpos]
  have harg : (2*π*(log (n:ℕ)/(2*π))-L)/d = (log (n:ℕ)-L)/d := by field_simp
  rw [harg]
  unfold mellinArithmeticWeight
  simp only [Complex.real_smul]
  push_cast
  ring

end RH080Next.Explicit
