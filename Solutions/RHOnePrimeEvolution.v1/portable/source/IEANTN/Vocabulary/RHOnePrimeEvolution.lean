/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Prime.Basic

/-! Shared mathematical definitions. Evidence belongs to the owning node. -/
namespace IEANTN.RHOnePrimeEvolution
open Real Set
set_option autoImplicit false

def hasPrimeClosed (x y : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ y
def hasPrimeOpen (x y : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < y
noncomputable def cmsJ : ℝ :=
  (4 * sin (9 * π / 20) - 3) / ((9 / 20) * ∫ x in (0 : ℝ)..π, sinc x)
noncomputable def cmsRatio (c L : ℝ) : ℝ := c * L / exp (L / 2)
noncomputable def cmsHalfLogSpan (c L : ℝ) : ℝ := log (1 + cmsRatio c L) / 2
noncomputable def cmsMainScale (c L : ℝ) : ℝ :=
  exp ((L + cmsHalfLogSpan c L) / 2) * cmsHalfLogSpan c L
noncomputable def cmsLogScale (c L : ℝ) : ℝ := log (1 / cmsHalfLogSpan c L)
/-- Ordinary-zeta RH is an antecedent, not Dirichlet GRH. -/
def cms616 : Prop :=
  RiemannHypothesis → ∀ L c : ℝ, 44 ≤ L → c ∈ Icc (1 / 2 : ℝ) 1 →
    ¬ hasPrimeClosed (exp L) (exp L + c * sqrt (exp L) * L) →
      cmsJ * cmsMainScale c L ≤ cmsLogScale c L + 29 / 25
/-- Conventional consecutive prime endpoints and the actual finite range. -/
def finiteGapTable : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → q < 2 ^ 64 →
    (∀ r : ℕ, p < r → r < q → ¬ r.Prime) → q - p ≤ 1550

/-- The actual continuously chosen closed-window coefficient. -/
noncomputable def coefficient (L : ℝ) : ℝ :=
  (1 - 2 * (log ((399 / 1000 : ℝ) * L) - 117 / 100) / L) /
    (28517 / 25000) + 1 / (10000 * L)
/-- Shift by one to remove the left endpoint, and allow one more absolute unit
to make the upper endpoint strictly open as well. -/
noncomputable def continuousEndpoint (x : ℝ) : ℝ :=
  x + 2 + coefficient (log (x + 1)) * sqrt (x + 1) * log (x + 1)
end IEANTN.RHOnePrimeEvolution
