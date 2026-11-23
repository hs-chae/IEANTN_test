/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
namespace RHSmoothingInputs.v1
open Real MeasureTheory Set IEANTN.RHSmoothing
/-- A precise, unformalized analytic identity from the integrated explicit formula.
Summability is required, so no totalized-tsum success is possible. -/
def AveragedExplicitFormula (k : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    Summable (zeroPacket k s L) ∧
    average k s L = mainAverage k s L - (zeroAverage k s L).re -
      Real.log (2 * Real.pi) + trivialAverage k s L

/-- Exact zero observable; this remaining analytic lemma is derived in the written
proof from the zero-count formula, regularized absolute moments, and the imaginary
shift. It is not a psi-error premise. -/
def ZeroDensityMomentEstimate (k : ℝ → ℝ) : Prop :=
  RiemannHypothesis → ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    ‖zeroAverage k s L‖ ≤ Real.sqrt (Real.exp L) *
      ((v L ^ 2 + 2 * J k 0 * v L + 2 * J k 1) / (2 * Real.pi) + 131 / 1000)


/-- Exact box average identity, still awaiting full analytic formalization. -/
def box_explicit_formula : Prop := AveragedExplicitFormula box
/-- Actual box zero sum density/moment estimate, not a psi-bound assumption. -/
def box_zero_estimate : Prop := ZeroDensityMomentEstimate box
/-- Exact regularized moments; numerical/scalar evidence does not close the Mellin identity. -/
def box_moments : Prop := J box 0 = Real.log 2 ∧ J box 1 ≤ 567 / 800
/-- Original NL parabola contracts, preserved as a different provider. -/
def parabola_inputs : Prop := AveragedExplicitFormula parabola ∧
  ZeroDensityMomentEstimate parabola ∧ J parabola 0 ≤ 831 / 1000 ∧
  J parabola 1 ≤ 287 / 500
end RHSmoothingInputs.v1
