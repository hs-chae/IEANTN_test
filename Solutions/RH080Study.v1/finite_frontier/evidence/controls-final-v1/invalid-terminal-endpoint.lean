import FiniteNetworkIntegration
example (h : PrimeGapTable.v1.gaps) : ∃ q : ℕ, q.Prime ∧ (18446744073709551557 : ℝ) < q ∧ (q : ℝ) < 18446744073709551557 + (1550+1) := by
  exact RH080.FiniteFrontier.strict_width1550_add (x := 18446744073709551557) (ε := 1) h (by norm_num) (by norm_num [RH080.FiniteFrontier.terminal]) (by norm_num)
