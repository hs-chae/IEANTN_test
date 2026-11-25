/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Fourier.FourierTransform

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace IEANTN.CMSDual

/-- Actual real cosine integral of the dual function; for an even real V this
is the real inverse Fourier transform with the exp(2*pi*i*x*t) convention. -/
def cosineKernel (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, V t * cos (2*π*t*x)

/-- A finite exterior-penalty dual witness. No source-language execution types
or proof-status objects enter this Mathlib-only mathematical interface. -/
def IntegralWitness (A M : ℝ) : Prop :=
  ∃ V : ℝ → ℝ, Integrable V ∧ Function.Even V ∧
    (∀ t : ℝ, |t| ≤ 1 → V t = 1) ∧
    (∀ t : ℝ, 1 < |t| → 1-A ≤ V t ∧ V t ≤ 1) ∧
    ∀ x : ℝ, |cosineKernel V x| ≤ M

/-- Restricted Fourier-framework ratio bound: both the function and its genuine
Fourier transform must be L1, and the objective denominator must be positive.
This is not a statement that actual prime gaps have a positive lower bound. -/
def L1RatioFloor (A c : ℝ) : Prop :=
  ∀ F G : ℝ → ℝ, Integrable F → Integrable G → Continuous F →
    (𝓕 (fun x : ℝ => (F x : ℂ)) = fun t : ℝ => (G t : ℂ)) →
    0 < F 0-A*(∫ t in {t : ℝ | 1 < |t|}, max 0 (G t)) →
    c ≤ (∫ x : ℝ, |F x|)/(F 0-A*(∫ t in {t : ℝ | 1 < |t|}, max 0 (G t)))

/-- Strict exclusion within the same explicit L1-Fourier fragment. -/
def L1RatioStrictlyAbove (A c : ℝ) : Prop :=
  ∀ F G : ℝ → ℝ, Integrable F → Integrable G → Continuous F →
    (𝓕 (fun x : ℝ => (F x : ℂ)) = fun t : ℝ => (G t : ℂ)) →
    0 < F 0-A*(∫ t in {t : ℝ | 1 < |t|}, max 0 (G t)) →
    c < (∫ x : ℝ, |F x|)/(F 0-A*(∫ t in {t : ℝ | 1 < |t|}, max 0 (G t)))

end IEANTN.CMSDual
