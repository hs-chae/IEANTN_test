import FiniteNetworkIntegration
example (h : FiniteLogSquaredPrimeGaps.v1.gaps) (h42 : (7 : ℝ) ≤ Real.exp 42) : ∃ q : ℕ, q.Prime ∧ (7 : ℝ) < q ∧ (q : ℝ) < 7 + (Real.log 7)^2 := by
  exact RH080.FiniteFrontier.strict_log_squared (x := 7) h (by norm_num) h42
