/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
namespace RHSmoothing.v1
open Real IEANTN.RHSmoothing
/-- Whole-real-ray actual Chebyshev psi bound. Analytic inputs are separately recorded. -/
def box_psi : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |Chebyshev.psi x - x| ≤ sqrt x * fastBound (log x)
/-- Original B5 whole-real-ray actual psi observable, not an abstract error surrogate. -/
def B5_psi : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |Chebyshev.psi x - x| ≤ sqrt x * envelope (831 / 1000) (287 / 500) (log x)
/-- Comparison of complete envelopes on their common ray. -/
def box_improves_B5 : Prop := ∀ L : ℝ, 35 ≤ L →
  546 / 1000 < envelope (831 / 1000) (287 / 500) L - fastBound L
/-- Recovered integer zero-count information, under the same eight existing analytic inputs. -/
def recovered_ch_psi : Prop := ∀ x : ℝ, exp 34 ≤ x →
  |Chebyshev.psi x - x| ≤ chBound (log x) * sqrt x
end RHSmoothing.v1
