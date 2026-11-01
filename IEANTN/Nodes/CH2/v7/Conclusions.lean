/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import IEANTN.Vocabulary.ZeroFreeHalfPlane

/-! A proved reusable CH2 transfer with a free truncation height. The general-beta, paired
and density developments reuse its analytic ingredients. CH2.v6 has complete separate Lean
solutions for its exact original headline contracts. -/
namespace CH2.v7

noncomputable def spectralBound (t : ℝ) : ℝ :=
  Real.log t ^ 2 / (2 * Real.pi) + (2 + 1 / Real.pi) * Real.log t

/-- The explicitly proved horizontal correction; no asymptotic notation is used. -/
noncomputable def horizontalCorrection (T t x : ℝ) : ℝ :=
  10 * Real.log T ^ 2 / Real.log x ^ 2 +
    Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * t)

/-- The explicitly computable bound after eliminating the existential contour height. -/
noncomputable def finiteErrorBound (T β x : ℝ) : ℝ :=
  let U := T - 1 / 2
  Real.pi / U + spectralBound T * (x ^ β / x) +
    2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2 +
    (2 * Real.pi / U + 1 / 2) / x * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) +
    Real.pi ^ 2 / (3 * U ^ 2) + Real.log (2 * Real.pi) / x


/-- The finite CH2 formula, zero counts and a fixed zero-free half-plane imply an explicit
bound for the normalized PNT error. The truncation height can be chosen by each consumer. -/
def finite_transfer : Prop :=
  ∀ T x β : ℝ, 2000 ≤ T → 16 ≤ Real.log T → 1000000 ≤ x → 1 ≤ Real.log x →
    IEANTN.ZetaZeroFreeHalfPlane β → IEANTN.Eψ x ≤ finiteErrorBound T β x

end CH2.v7
