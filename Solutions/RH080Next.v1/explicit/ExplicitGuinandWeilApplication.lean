/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitGWTestFunction
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

abbrev CMSZeroIndex := IEANTN.zetaZeroesIn (Ioo (0:ℝ) 1) univ
abbrev CMSPrimeIndex := {n : ℕ // 2 ≤ n}

def cmsZeroFamily (h : ℂ → ℂ) (ρ : CMSZeroIndex) : ℂ :=
  h (((ρ:ℂ)-(1/2:ℂ))/Complex.I) * ((IEANTN.zetaOrder (ρ:ℂ):ℤ):ℂ)

def cmsPrimeFamily (h : ℂ → ℂ) (n : CMSPrimeIndex) : ℂ :=
  (((ArithmeticFunction.vonMangoldt (n:ℕ):ℝ)/sqrt (n:ℕ)):ℂ) *
    (𝓕 (fun u : ℝ => h (u:ℂ)) (log (n:ℕ)/(2*π)) +
      𝓕 (fun u : ℝ => h (u:ℂ)) (-log (n:ℕ)/(2*π)))

def cmsGammaIntegrand (h : ℂ → ℂ) (u : ℝ) : ℂ :=
  h (u:ℂ) * ((Complex.digamma ((1/4:ℂ)+Complex.I*((u/2:ℝ):ℂ))).re:ℂ)

/-- Source formula with the actual zeta zeroes and their multiplicities.
Convergence is explicit, so no totalized infinite sum can fake the identity. -/
def CMSGuinandWeilFormula (h : ℂ → ℂ) : Prop :=
  Summable (cmsZeroFamily h) ∧ Summable (cmsPrimeFamily h) ∧
    Integrable (cmsGammaIntegrand h) ∧
    (∑' ρ : CMSZeroIndex, cmsZeroFamily h ρ) =
      h (1/(2*Complex.I)) + h (-1/(2*Complex.I)) -
      ((log π/(2*π):ℝ):ℂ) * 𝓕 (fun u : ℝ => h (u:ℂ)) 0 +
      ((1/(2*π):ℝ):ℂ) * (∫ u : ℝ, cmsGammaIntegrand h u) -
      ((1/(2*π):ℝ):ℂ) * (∑' n : CMSPrimeIndex, cmsPrimeFamily h n)

/-- CMS arXiv1708.04122v2, Lemma6, printedp17/PDFp17, citing IK5.12.
We use its genuinely general formula on the stronger entire, quadratic-strip
subclass. The source requires analyticity in |Ims|≤1/2+ε and decay exponent
1+δ; entire/quadratic decay supplies ε=1/2,δ=1. The convergence clauses spell
out the convergent sums/integral occurring in the published formula. This is a
named literature proposition, not a new Lean axiom or a proved source theorem. -/
def SourceCMSGuinandWeil : Prop :=
  ∀ h : ℂ → ℂ, Differentiable ℂ h → HorizontalQuadraticDecay h →
    CMSGuinandWeilFormula h

/-- The actual affine source window is applied to the genuinely general CMS
formula. The source assumptions concern the published whole function classes;
there is no support-seven formula, numerical error budget, or final prime bound
among this theorem's premises. Gamma elimination and zero/prime estimates are
subsequent mathematical obligations. -/
theorem guinand_weil_affine_test
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (d L : ℝ) (hd : 0 < d) :
    ∃ H : ℂ → ℂ,
      (∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ)) ∧
      CMSGuinandWeilFormula (fun z : ℂ =>
        (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*z)*Complex.exp (Complex.I*(L:ℂ)*z)) := by
  obtain ⟨H,hH,hreal,hdec,hder⟩ := affine_strip_extension_by_mesh_dilation
    hBR nodes m n hm hmn hlen hlast
  obtain ⟨hk,hkdec⟩ := mellin_test_function_strip H hH hdec d L hd
  exact ⟨H,hreal,hCMS _ hk hkdec⟩

end RH080Next.Explicit
