/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOnePrimeEvolution
import IEANTN.Nodes.RH.v1.Conclusions
import IEANTN.Nodes.CMSCosineInput.v1.Conclusions
import IEANTN.Nodes.PrimeGapTable.v1.Conclusions

/-!
Exact one-prime continuation contracts. Source predicates remain external inputs.
The older octic population conclusions are preserved.
-/

namespace RHOnePrimeEvolution.v1
open Real IEANTN.RHOnePrimeEvolution
set_option autoImplicit false
/-- Kernel arithmetic on the genuine sine integral. Fourier/L1 identification
is separate and remains part of the CMS source interface. -/
def kernel_ratio_lower : Prop := (28517 / 25000 : ℝ) ≤ cmsJ
/-- Analytic ray with both endpoints open; no finite-gap-table input. -/
def late_open_08768 : Prop := ∀ x : ℝ, exp 44 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Uniform ray after the finite/analytic split, retaining the finite computation
as a separate input. This is not its new formal verification. -/
def uniform_open_08768 : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Bounded explicit improvement, not asymptotic domination of0.8358. -/
def finite_slab_open_08301 : Prop := ∀ x : ℝ, exp 44 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x)
/-- Absolute finite-range window, requiring no RH hypothesis. -/
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

/-- Full continuous endpoint, including its real-variable shift. -/
def continuous_late : Prop := ∀ x : ℝ, exp 44 ≤ x →
  hasPrimeOpen x (continuousEndpoint x)
/-- Strict comparison of entire endpoints on the complete real ray. -/
def continuous_improves_uniform : Prop := ∀ x : ℝ, exp 44 ≤ x →
  continuousEndpoint x < x + (548 / 625) * sqrt x * log x
/-- Hybrid finite/continuous frontier. No finite table is silently absorbed. -/
def continuous_uniform : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (if x < exp 44 then x + 1551 else continuousEndpoint x)
/-- Bounded coefficient below0.8358, with BOTH endpoints open. Its finite upper
range must not be replaced by an asymptotic claim. -/
def bounded_open_08357 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 →
  hasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x)
/-- Bounded strict-open comparison with the2026paper's FIXED0.85125 theorem;
this is not comparison with all retunings of that paper's full functions. -/
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)
end RHOnePrimeEvolution.v1
