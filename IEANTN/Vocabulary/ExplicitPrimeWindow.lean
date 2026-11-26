/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Pure mathematical objects for explicit affine prime-interval source
interfaces. Source propositions belong to CMSExplicitInputs.v1; numerical and
analytic correctness theorems belong to Solutions. All definitions preserve
the existing CMS multiplicity and right-closed zero-count conventions. -/
noncomputable section
open Real Set MeasureTheory Filter
open scoped FourierTransform Topology
namespace IEANTN.ExplicitPrimeWindow

def HorizontalQuadraticDecay (H : ℂ → ℂ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
    ∀ z : ℂ, |z.im| ≤ A → R ≤ |z.re| → ‖H z‖*(1+|z.re|)^2 ≤ C

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

def CMSGuinandWeilFormula (h : ℂ → ℂ) : Prop :=
  Summable (cmsZeroFamily h) ∧ Summable (cmsPrimeFamily h) ∧
    Integrable (cmsGammaIntegrand h) ∧
    (∑' ρ : CMSZeroIndex, cmsZeroFamily h ρ) =
      h (1/(2*Complex.I)) + h (-1/(2*Complex.I)) -
      ((log π/(2*π):ℝ):ℂ) * 𝓕 (fun u : ℝ => h (u:ℂ)) 0 +
      ((1/(2*π):ℝ):ℂ) * (∫ u : ℝ, cmsGammaIntegrand h u) -
      ((1/(2*π):ℝ):ℂ) * (∑' n : CMSPrimeIndex, cmsPrimeFamily h n)

def dlmfDigammaIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (((exp (-u):ℝ):ℂ)-Complex.exp (-z*(u:ℂ)))/((1-exp (-u):ℝ):ℂ)

def cmsMultiplicity (ρ : CMSZeroIndex) : ℝ := |(IEANTN.zetaOrder (ρ:ℂ):ℝ)|

def cmsCountFamily (T : ℝ) (ρ : CMSZeroIndex) : ℝ :=
  if 0 < (ρ:ℂ).im ∧ (ρ:ℂ).im ≤ T then cmsMultiplicity ρ else 0

def cmsPositiveZeroCount (T : ℝ) : ℝ := ∑' ρ : CMSZeroIndex, cmsCountFamily T ρ

def cmsQ (T : ℝ) : ℝ := T/(2*π)*log (T/(2*π*exp 1))+7/8

def cmsCountRemainder (T : ℝ) : ℝ := cmsPositiveZeroCount T-cmsQ T

def cmsSignedAmplitude (F : ℝ → ℝ) (Δ s : ℝ) (ρ : CMSZeroIndex) : ℝ :=
  if 0 < s*(ρ:ℂ).im then Δ*|F (Δ*(ρ:ℂ).im)| *cmsMultiplicity ρ else 0

def cmsZeroMain (F : ℝ → ℝ) (Δ T0 : ℝ) : ℝ :=
  ∫ u in Ioi (Δ*T0), log (u/(2*π*Δ))/(2*π)*|F u|

def cmsZeroRemainder (F' : ℝ → ℝ) (Δ T0 : ℝ) : ℝ :=
  ∫ u in Ioi (Δ*T0), ((3/20:ℝ)*log (u/Δ)+3)*|F' u|

def CMSZeroAdmissible (F F' : ℝ → ℝ) (Δ T0 : ℝ) : Prop :=
  (∀ u : ℝ, HasDerivAt F (F' u) u) ∧ Continuous F' ∧ Function.Even F ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ |u| → |F u| ≤ C/u^2 ∧ |F' u| ≤ C/u^2) ∧
  IntegrableOn (fun u : ℝ => log (u/(2*π*Δ))/(2*π)*|F u|) (Ioi (Δ*T0)) ∧
  IntegrableOn (fun u : ℝ => ((3/20:ℝ)*log (u/Δ)+3)*|F' u|) (Ioi (Δ*T0)) ∧
  Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsQ T) atTop (𝓝 0) ∧
  Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsCountRemainder T) atTop (𝓝 0)

end IEANTN.ExplicitPrimeWindow
