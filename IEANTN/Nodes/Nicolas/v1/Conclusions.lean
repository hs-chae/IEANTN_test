/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.SignedArithmetic
import IEANTN.Nodes.RH.v1.Conclusions

/-! The full Nicolas(2012) proof function, with exact beta and actual product.
The source inequalities remain distinct from their proved normalization adapters. -/
namespace Nicolas.v1
open IEANTN.SignedArithmetic
/-- Nicolas arXiv1202.0729v2(1.19), including absolute convergence of the
actual multiplicity-weighted spectral family on x>1 under RH. -/
def spectral_bound : Prop := RiemannHypothesis → ∀ x : ℝ, 1 < x →
  Summable (spectralTerm x) ∧ |W x| ≤ beta
/-- Nicolas proof Eq(2.19), PDFp8, full unrounded profile.
The strict599<x subdomain preserves the source's endpoint safely. -/
def log_f_upper_full : Prop := RiemannHypothesis → ∀ x : ℝ, 599 < x →
  Real.log (f x) ≤ -(W x + 2) / (Real.sqrt x * Real.log x) +
    (2 + beta) / (Real.sqrt x * (Real.log x)^2) +
    4 * beta / (Real.sqrt x * (Real.log x)^3) + 1 / (2 * (x - 1))
/-- Actual log product ratio, normalized at exp(gamma)*log(theta(x)).
This installs the stronger known full published function; no novelty claim. -/
def log_product_lower : Prop := ∀ x : ℝ, 599 < x →
  profile x / (Real.sqrt x * Real.log x) ≤
    Real.log (product x / (Real.exp Real.eulerMascheroniConstant *
      Real.log (Chebyshev.theta x)))
/-- The distinct actual multiplicative ratio, via log y<=y-1 for y>0. -/
def relative_product_lower : Prop := ∀ x : ℝ, 599 < x →
  profile x / (Real.sqrt x * Real.log x) ≤
    product x / (Real.exp Real.eulerMascheroniConstant *
      Real.log (Chebyshev.theta x)) - 1
end Nicolas.v1
