/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectCHJPairing
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
The literature boundary for the new direct-interval route. This is the original
signed-zero formulation of Cully-Hugill--Johnston, arXiv:2402.04272v3,
Theorem 1.3 and Table 1, row (log xM, alpha, omega, M)=(40,1/2,0,2.894).
The proposition below is an explicit source assumption, not a formal proof of
that analytic theorem. In particular it supplies one common truncation height
for the actual difference, rather than two unrelated existential heights.
-/

namespace E1FrozenN.Interval
open Real Set MeasureTheory Complex

/-- The actual zero contribution to a difference of Chebyshev psi values. -/
noncomputable def zeroIncrement (x h : ℝ) (rho : ℂ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ rho - (x : ℂ) ^ rho) / rho

/-- CHJ-II Theorem 1.3, specialized to its explicitly tabulated first row.
Every nontrivial zero is counted with its actual meromorphic multiplicity.
The source assumption has no numerical acceptance or desired interval hidden
inside it. -/
def CHJII_Theorem1_3_Row40 : Prop :=
  ∀ x h T : ℝ, Real.exp 40 ≤ x → 0 ≤ h →
    max 51 (Real.log x ^ 2) < T → T < (Real.sqrt x - 2) / 4 →
    ∃ Tstar : ℝ, T ≤ Tstar ∧ Tstar ≤ 2 * T ∧
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h +
        (IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-Tstar) Tstar)
          (zeroIncrement x h)).re| ≤
        (2894 / 1000 : ℝ) *
          ((x + h) * Real.log (x + h) + x * Real.log x) / T

end E1FrozenN.Interval
