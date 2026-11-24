/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! General integrated explicit formula, independent of a Box kernel or RH.
Hildebrand Thm5.18/(5.32), printed166; absolute convergence (5.34), printed167.
Multiplicity convention is corroborated explicitly by GM Eq(1.3a--b), printed2.
Only the physical subdomain x>1 is used. The additive constant has its published
value zeta'(-1)/zeta(-1); its weaker existential form suffices because it cancels. -/
namespace IntegratedPerron.v1
open Real MeasureTheory
noncomputable def psi1 (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, Chebyshev.psi t
noncomputable def zeroCoefficient (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  (IEANTN.zetaOrder r:ℂ)/((r:ℂ)*((r:ℂ)+1))
noncomputable def zeroPrimitive (x : ℝ) (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  Complex.exp (((r:ℂ)+1)*(Real.log x:ℂ))*zeroCoefficient r
noncomputable def trivialPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  x^((1:ℤ)-2*((n+1:ℕ):ℤ))/((2*((n+1:ℕ):ℝ))*(2*((n+1:ℕ):ℝ)-1))
/-- The genuine general published integrated explicit formula and absolute
all-zero convergence. This is an explicit literature-backed input, not a Lean
proof of Perron's formula, an RH assumption, or an assumed Box conclusion. -/
def formula : Prop := ∃ C : ℂ, ∀ x : ℝ, 1<x →
  Summable (zeroPrimitive x) ∧
  (psi1 x:ℂ)=(x:ℂ)^2/2-(∑' r,zeroPrimitive x r)-
    (x:ℂ)*(deriv riemannZeta 0/riemannZeta 0)+C-
      ((∑' n : ℕ,trivialPrimitive n x):ℝ)
end IntegratedPerron.v1
