import Mathlib

/-! Source-first PV is not asserted for the historical computation inputs.
These definitions expose finite prime statements without importing Solutions. -/
namespace IEANTN.FinitePrimeFrontier
open Real

def terminal : ℕ := 18446744073709551557

/-- Exact source shape of CMS(1.15): lower prime11<=p<=4e18 and consecutive q. -/
def logSquaredPrimeGaps : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → 11 ≤ p → p ≤ 4 * 10 ^ 18 →
  (∀ r : ℕ, p < r → r < q → ¬r.Prime) →
  (q : ℝ) - (p : ℝ) < (log (p : ℝ)) ^ 2

def closedWidth1550 : Prop := ∀ x : ℝ, 2 ≤ x → x < (terminal : ℝ) →
  ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ x + 1550

def strictWidth1550Add : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ x : ℝ, 2 ≤ x → x < (terminal : ℝ) →
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + (1550 + ε)

def strictLogSquared : Prop := ∀ x : ℝ, 11 ≤ x → x ≤ exp 42 →
  ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + (log x) ^ 2

def strictMinimumWidth : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ x : ℝ, 11 ≤ x → x ≤ exp 42 →
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) < x + min (1550 + ε) ((log x) ^ 2)
end IEANTN.FinitePrimeFrontier
