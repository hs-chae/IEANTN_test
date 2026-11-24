import IEANTN.Vocabulary.RHSmoothing
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! General integrated-Perron objects. These are independent of a particular
Box kernel, threshold, smoothing scale or desired prime-number bound. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
open scoped Topology

noncomputable def psi1 (x : ℝ) : ℝ := ∫ t in (1:ℝ)..x,Chebyshev.psi t
noncomputable def transport (a b : ℝ) (f : ℝ → ℂ) : ℂ :=
  f b/(b:ℂ)-f a/(a:ℂ)+∫ t in a..b,f t/(t:ℂ)^2
noncomputable def realTransport (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  f b/b-f a/a+∫ t in a..b,f t/t^2
noncomputable def zeroCoefficient (ρ : IEANTN.RHSmoothing.Zero) : ℂ :=
  (IEANTN.zetaOrder ρ:ℂ)/((ρ:ℂ)*((ρ:ℂ)+1))
noncomputable def zeroPrimitive (x : ℝ) (ρ : IEANTN.RHSmoothing.Zero) : ℂ :=
  Complex.exp (((ρ:ℂ)+1)*(Real.log x:ℂ))*zeroCoefficient ρ
noncomputable def trivialPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  x^((1:ℤ)-2*((n+1:ℕ):ℤ))/((2*((n+1:ℕ):ℝ))*(2*((n+1:ℕ):ℝ)-1))

/-- Conservative exact general source from Hildebrand Theorem5.18/(5.32).
The unspecified additive constant cancels under transport; it is not assigned
an unverified numerical value. This is an explicit literature premise, not a
formal proof of the published integrated explicit formula. -/
def SourceIntegratedPsi : Prop := ∃ C : ℂ, ∀ x : ℝ, 1<x →
  Summable (zeroPrimitive x) ∧
  (psi1 x:ℂ)=(x:ℂ)^2/2-(∑' ρ,zeroPrimitive x ρ)-(x:ℂ)*(Real.log (2*Real.pi):ℂ)+C-
    ((∑' n : ℕ,trivialPrimitive n x):ℝ)
end RHOcticPush.BoxPerron
