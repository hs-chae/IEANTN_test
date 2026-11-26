/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.AffineFourierWindow
import IEANTN.Vocabulary.CMSFunctional

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace BRFourierInput.v1
open IEANTN.AffineFourierWindow

def denominatorFour (nodes : List ℚ) (m : ℕ) : ℝ :=
  inverseCosine (affineSpectrum nodes m) 0-
    4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)
def amplitudeMass (nodes : List ℚ) (m : ℕ) : ℝ :=
  ∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|
def q1Error (x : ℝ) : ℝ := log (log x)/log x+2*(log x/sqrt x)

/-- BR2026v2 Lemma5, §2.1, eq:pair: the literal general norm identity for
arbitrary rational nodes on the published support-five mesh. This source input
has no fixed test function or numerical norm bound. -/
def norm_identity : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0<m → nodes.length=5*m+1 →
    node nodes (5*m)=0 →
      (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) =
        ∫ y in (0 : ℝ)..1, |nodalPolynomial nodes y|

/-- Source-backed ordinary-RH specialization of BR2026v2 Proposition6,
§3, eq:uniform-count, to Q(x)={1}. The proof's conductor-one principal-character
case and moduli1/2 paragraph use only zeta RH. This is a literature input,
not a Lean proof of the analytic counting theorem. The actual attained maximum
and the eventual O(F,c) remainder remain explicit. It is restricted to the
published support-five construction, not asserted for arbitrary Fourier pairs. -/
def uniform_population_q1 : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0<m → nodes.length=5*m+1 →
    node nodes (5*m)=0 → ∀ M : ℝ, 0<M →
    (∀ v : ℝ, |affineSpectrum nodes m v|≤M) →
    (∃ v : ℝ, |affineSpectrum nodes m v|=M) →
    0<denominatorFour nodes m → ∀ c : ℝ, 0<c → RiemannHypothesis →
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
      (c*denominatorFour nodes m-amplitudeMass nodes m)/(2*M)-C*q1Error x ≤
        IEANTN.CMSFunctional.normalizedPopulation c x
end BRFourierInput.v1
