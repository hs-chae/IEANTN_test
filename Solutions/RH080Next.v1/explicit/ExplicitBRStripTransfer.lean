/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineFourier
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- The usual horizontal-strip O((1+|Re z|)^(-2)) condition, expressed
without choosing an irrelevant numerical O constant. -/
def HorizontalQuadraticDecay (H : ℂ → ℂ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
    ∀ z : ℂ, |z.im| ≤ A → R ≤ |z.re| → ‖H z‖*(1+|z.re|)^2 ≤ C

/-- Published general input: BR v2, subsection "The Fourier pair and its
norm", Lemma labelled lem:fourier-norm, preceding equation eq:pair. It sets
N=5m and allows arbitrary rational a0,...,a(N-1), with a(±N)=0. Its entire
extension and F,F' decay assertion covers EVERY fixed horizontal strip.
This is a source proposition, not an axiom or a theorem claimed proved here.
No particular witness, support-seven statement, or final prime bound occurs. -/
def SourceBRFourierNormStrip : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0 < m → nodes.length = 5*m+1 →
    node nodes (5*m) = 0 → ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧
      (∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u : ℂ)) ∧
      HorizontalQuadraticDecay H ∧ HorizontalQuadraticDecay (deriv H)

private theorem decay_scale (H : ℂ → ℂ) (hH : HorizontalQuadraticDecay H)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 1 ≤ r) :
    HorizontalQuadraticDecay (fun z : ℂ => (a:ℂ)*H ((r:ℂ)*z)) := by
  intro A hA
  have hr0 : 0 < r := by linarith
  obtain ⟨C,R,hC,hR,hbound⟩ := hH (r*A) (mul_nonneg hr0.le hA)
  refine ⟨a*C,R/r,mul_nonneg ha hC,div_nonneg hR hr0.le,?_⟩
  intro z hz hzr
  have hzIm : |(((r:ℂ)*z).im)| ≤ r*A := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_left hz hr0.le
  have hzRe : R ≤ |(((r:ℂ)*z).re)| := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      abs_mul, abs_of_pos hr0]
    have h := (div_le_iff₀ hr0).mp hzr
    nlinarith
  have hb := hbound ((r:ℂ)*z) hzIm hzRe
  have hs : (1+|z.re|)^2 ≤ (1+|(((r:ℂ)*z).re)|)^2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      abs_mul, abs_of_pos hr0]
    have hm : |z.re| ≤ r*|z.re| := le_mul_of_one_le_left (abs_nonneg _) hr
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    ‖(a:ℂ)*H ((r:ℂ)*z)‖*(1+|z.re|)^2 = a*(‖H ((r:ℂ)*z)‖*(1+|z.re|)^2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      ring
    _ ≤ a*(‖H ((r:ℂ)*z)‖*(1+|(((r:ℂ)*z).re)|)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) ha
    _ ≤ a*C := mul_le_mul_of_nonneg_left hb ha

private theorem deriv_dilation (H : ℂ → ℂ) (hH : Differentiable ℂ H) (r : ℝ) :
    deriv (fun z : ℂ => (r:ℂ)*H ((r:ℂ)*z)) =
      fun z : ℂ => ((r^2:ℝ):ℂ)*deriv H ((r:ℂ)*z) := by
  funext z
  have hh := (((hH ((r:ℂ)*z)).hasDerivAt).comp z
    ((hasDerivAt_id z).const_mul (r:ℂ))).const_mul (r:ℂ)
  have hhd : HasDerivAt (fun z : ℂ => (r:ℂ)*H ((r:ℂ)*z))
      ((r:ℂ)*(deriv H ((r:ℂ)*z)*(r:ℂ))) z := by
    simpa only [Function.comp_def, mul_one] using hh
  rw [hhd.deriv]
  push_cast
  ring

/-- Derivation of arbitrary wider support from the published support-five
family by changing the mesh. The strip width is multiplied by n/m before
the general source estimate is used. -/
theorem affine_strip_extension_by_mesh_dilation
    (hsource : SourceBRFourierNormStrip) (nodes : List ℚ) (m n : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hlen : nodes.length = 5*n+1)
    (hlast : node nodes (5*n) = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u : ℂ)) ∧
      HorizontalQuadraticDecay H ∧ HorizontalQuadraticDecay (deriv H) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  let r : ℝ := (n:ℝ)/(m:ℝ)
  have hr : 1 ≤ r := by
    apply (le_div_iff₀ hm').mpr
    simpa only [one_mul] using (show (m:ℝ) ≤ (n:ℝ) by exact_mod_cast hmn)
  obtain ⟨H,hH,hreal,hdec,hder⟩ := hsource nodes n hn hlen hlast
  refine ⟨fun z : ℂ => (r:ℂ)*H ((r:ℂ)*z), ?_, ?_,
    decay_scale H hdec r r (by positivity) hr, ?_⟩
  · fun_prop
  · intro u
    dsimp only
    rw [show (r:ℂ)*(u:ℂ) = ((r*u:ℝ):ℂ) by simp, hreal]
    rw [← Complex.ofReal_mul]
    congr 1
    exact (inverseCosine_affineSpectrum_mesh_dilation nodes m n hm hn u).symm
  · rw [deriv_dilation H hH r]
    exact decay_scale (deriv H) hder (r^2) r (sq_nonneg _) hr

end RH080Next.Explicit
