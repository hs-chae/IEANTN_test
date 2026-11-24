/- General CMS functional vocabulary. Mathlib-only; no numerical solution or
certificate imports. The external source propositions remain explicit inputs. -/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter
open scoped FourierTransform
namespace IEANTN.CMSFunctional

/-- The source complement of the closed unit interval. -/
def exterior : Set ℝ := {t : ℝ | 1 < |t|}
noncomputable def mass (F : ℝ → ℝ) : ℝ := ∫ x : ℝ, |F x|
noncomputable def positiveLeak (G : ℝ → ℝ) : ℝ := ∫ t in exterior, max 0 (G t)
noncomputable def denominator (F G : ℝ → ℝ) : ℝ :=
  F 0 - (36/11 : ℝ)*positiveLeak G
noncomputable def inverseObjective (F G : ℝ → ℝ) : ℝ := mass F / denominator F G

/-- Exactly the even continuous real L1 test-function class from CMS (1.3),
restricted to a finite positive Fourier leakage. The supplied G is required to
be the genuine transform with the source's exp(-2*pi*i*x*t) convention. -/
structure Eligible (F G : ℝ → ℝ) : Prop where
  continuous : Continuous F
  even : Function.Even F
  integrable : Integrable F
  nonzero : F ≠ 0
  fourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun t : ℝ => (G t : ℂ)
  leakage_integrable : IntegrableOn (fun t : ℝ => max 0 (G t)) exterior

/-- Actual Mathlib zero-based primes. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  ((primeAt (n+1) : ℝ) - primeAt n) /
    (sqrt (primeAt n : ℝ)*log (primeAt n : ℝ))
/-- The source indexes primes from one. The totalized n=0 value is irrelevant:
all source and consumer assertions are eventual and the shift uses n+1>=1. -/
noncomputable def paperPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n-1)
noncomputable def paperNormalizedGap (n : ℕ) : ℝ :=
  ((paperPrime (n+1) : ℝ) - paperPrime n) /
    (sqrt (paperPrime n : ℝ)*log (paperPrime n : ℝ))

def EventualGapBound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, normalizedGap n ≤ c+ε

def PaperEventualGapBound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, paperNormalizedGap n ≤ c+ε

/-- Universal consequence of CMS arXiv1708.04122v2 Corollary4 (1.14),
its C+(B) definition (1.3), and the unconditional B<=36/11 (1.12).
The interface contains NO particular Gaussian, coefficient, or numeric bound.
It is an external mathematical source proposition, never a proved Lean axiom. -/
def SourceCMSFunctional : Prop :=
  ∀ F G : ℝ → ℝ, Eligible F G → 0 < denominator F G →
    RiemannHypothesis → PaperEventualGapBound (inverseObjective F G)

/-- The usual real-variable pi, represented by natural floor. Only eventual
positive real arguments enter the source and final mathematical consumers. -/
noncomputable def piReal (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊
/-- Actual half-open source count: primes in (x,x+c*sqrt(x)*log(x)]. -/
noncomputable def halfOpenCount (c x : ℝ) : ℕ :=
  piReal (x+c*sqrt x*log x)-piReal x
noncomputable def normalizedPopulation (c x : ℝ) : ℝ :=
  (halfOpenCount c x : ℝ)/sqrt x
/-- A positive limiting count margin, expressed without totalizing a potentially
infinite liminf. This is equivalent to the source's strict liminf>alpha form. -/
def GoodCoefficient (α c : ℝ) : Prop := 0 < c ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop, α+δ ≤ normalizedPopulation c x

def goodCoefficients (α : ℝ) : Set ℝ := {c | GoodCoefficient α c}

/-- CMS Theorem3 (1.13), after its definition (1.3) and B<=36/11 (1.12)
are applied to any admissible function, gives this universal infimum bound.
Nonemptiness is explicit: Lean's sInf-empty convention cannot fake a bound.
No Gaussian, improved coefficient, or numerical output occurs in this input. -/
def SourceCMSPopulation : Prop :=
  ∀ F G : ℝ → ℝ, Eligible F G → 0 < denominator F G → RiemannHypothesis →
    ∀ α : ℝ, 0 ≤ α → (goodCoefficients α).Nonempty ∧
      sInf (goodCoefficients α) ≤ (1+2*α)*inverseObjective F G

end IEANTN.CMSFunctional
