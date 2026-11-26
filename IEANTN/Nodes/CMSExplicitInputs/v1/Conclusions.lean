/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ExplicitPrimeWindow
import IEANTN.Vocabulary.AffineFourierWindow
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting

noncomputable section
open Real Set MeasureTheory Filter
open scoped FourierTransform Topology
namespace CMSExplicitInputs.v1
open IEANTN.ExplicitPrimeWindow IEANTN.AffineFourierWindow

/-- BR2026v2 Lemma5, §2.1, eq:pair: entire extension and quadratic decay on every fixed horizontal strip. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def strip_regularity : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0 < m → nodes.length = 5*m+1 →
    node nodes (5*m) = 0 → ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧
      (∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u : ℂ)) ∧
      HorizontalQuadraticDecay H ∧ HorizontalQuadraticDecay (deriv H)

/-- CMS1708.04122v2 Lemma6, printedp17, citing Iwaniec–Kowalski Theorem5.12; entire quadratic-strip subclass and convergence made explicit. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def guinand_weil : Prop :=
  ∀ h : ℂ → ℂ, Differentiable ℂ h → HorizontalQuadraticDecay h →
    CMSGuinandWeilFormula h

/-- DLMF5.9.16, Re(z)>0: general complex digamma integral, including convergence. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def digamma_integral : Prop :=
  ∀ z : ℂ, 0 < z.re → IntegrableOn (dlmfDigammaIntegrand z) (Ioi (0:ℝ)) ∧
    Complex.digamma z+(Real.eulerMascheroniConstant:ℂ) =
      ∫ u in Ioi (0:ℝ), dlmfDigammaIntegrand z u

/-- DLMF25.5.E3, real s>0 and s≠1, after multiplication by its denominator; no numerical zeta premise. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def real_eta_integral : Prop :=
  ∀ s : ℝ, 0<s → s≠1 →
    IntegrableOn (fun x : ℝ => x^(s-1)/(exp x+1)) (Ioi (0:ℝ)) ∧
      (∫ x in Ioi (0:ℝ), x^(s-1)/(exp x+1)) =
        (1-(2:ℝ)^(1-s))*Gamma s*(riemannZeta (s:ℂ)).re

/-- CMS Lemma9, §6.1, printedp23: right-closed positive-ordinate count and the separate N(10)=0 fact. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def zero_counting : Prop :=
  (∀ T : ℝ, Summable (cmsCountFamily T)) ∧ cmsPositiveZeroCount 10 = 0 ∧
    ∀ T : ℝ, exp 1 ≤ T → |cmsCountRemainder T| ≤ (3/20:ℝ)*log T+3

/-- CMS §6.1, display after Lemma9 and before(6.9), plus negative-ordinate paragraph: general proof-scheme specialization with every C1, decay, integrability and infinity-boundary hypothesis explicit; not a claim of a separately printed universal theorem. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def zero_partial_summation : Prop :=
  zero_counting → RiemannHypothesis →
  ∀ T0 : ℝ, exp 1 ≤ T0 → T0 < 10 → cmsQ T0 = 0 → cmsPositiveZeroCount T0 = 0 →
  ∀ F F' : ℝ → ℝ, ∀ Δ : ℝ, 0 < Δ → CMSZeroAdmissible F F' Δ T0 →
  ∀ s : ℝ, (s = 1 ∨ s = -1) →
    Summable (cmsSignedAmplitude F Δ s) ∧
    (∑' ρ : CMSZeroIndex, cmsSignedAmplitude F Δ s ρ) ≤
      cmsZeroMain F Δ T0+Δ*cmsZeroRemainder F' Δ T0

/-- Montgomery–Vaughan(1973), Theorem2, printedp121,(1.10)/(1.12), modulus1; CMS(6.10). Actual real left-open/right-closed floor counts. These are explicit literature/source-proof-scheme inputs, not new Lean axioms. -/
def montgomery_vaughan : Prop :=
  ∀ a y : ℝ, 1 < a → 1 < y →
    ((Nat.primeCounting ⌊a+y⌋₊-Nat.primeCounting ⌊a⌋₊:ℕ):ℝ) ≤ 2*y/log y

/-- CMS(1.15), citing Oliveira e Silva–Herzog–Pardi §2.2: strict squared-log gap for lower primes11 through4·10¹⁸. Historical finite computation, not new source-first PV. -/
def historical_finite_gap : Prop :=
  ∀ n : ℕ, 11 ≤ Nat.nth Nat.Prime n →
    Nat.nth Nat.Prime n ≤ 4 * 10 ^ 18 →
    (Nat.nth Nat.Prime (n+1) : ℝ) - Nat.nth Nat.Prime n <
      log (Nat.nth Nat.Prime n : ℝ) ^ 2

end CMSExplicitInputs.v1
