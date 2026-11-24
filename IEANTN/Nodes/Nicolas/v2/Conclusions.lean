/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.SignedArithmetic

/-! Original post-lock positive-kernel consequences of the exact Nicolas source
inputs. Joint and existential conclusions are distinct from one-point records. -/
namespace Nicolas.v2
open Real IEANTN.SignedArithmetic
noncomputable def scaledLogProduct (x : ℝ) : ℝ :=
  sqrt x * log x * log (product x / (exp Real.eulerMascheroniConstant *
    log (Chebyshev.theta x)))
noncomputable def penalty (x : ℝ) : ℝ :=
  (2 + beta) / log x + 4 * beta / (log x) ^ 2 +
    sqrt x * log x / (2 * (x - 1))
noncomputable def fourEnvelope (x : ℝ) : ℝ :=
  20 - (5 / 2 : ℝ) * beta - 4 * penalty x - 3 * penalty (x ^ 2) -
    2 * penalty (x ^ 3) - penalty (x ^ 4)
/-- Full multiplicity-weighted infinite spectral inequality, not finite truncation. -/
def spectral_four : Prop := ∀ x : ℝ, 0 < x →
  -(5 / 2 : ℝ) * beta ≤ 4 * W x + 3 * W (x ^ 2) + 2 * W (x ^ 3) + W (x ^ 4)
/-- Actual four-scale Euler-product log inequality on the complete real ray. -/
def product_four : Prop := ∀ x : ℝ, 599 < x →
  fourEnvelope x ≤ 4 * scaledLogProduct x + 3 * scaledLogProduct (x ^ 2) +
    2 * scaledLogProduct (x ^ 3) + scaledLogProduct (x ^ 4)
/-- One of four explicit scales has the improved coefficient; k may depend on x. -/
def product_block : Prop := ∀ x : ℝ, 599 < x →
  ∃ k : ℕ, k ∈ ({1, 2, 3, 4} : Finset ℕ) ∧
    2 - beta / 4 - penalty (x ^ k) ≤ scaledLogProduct (x ^ k)
/-- Strict comparison with independently summing the complete previous profiles. -/
def four_gain : Prop := ∀ x : ℝ,
  4 * profile x + 3 * profile (x ^ 2) + 2 * profile (x ^ 3) + profile (x ^ 4) <
    fourEnvelope x
end Nicolas.v2
