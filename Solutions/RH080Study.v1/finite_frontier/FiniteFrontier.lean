import FiniteGapSourceConsumer
import IEANTN.Nodes.PrimeGapTable.v1.Conclusions

/-! Additive real-uniform consequences of the already recorded finite gap table.
The historical table remains an explicit input. Terminal primality is consumed
from the existing kernel Lucas proof. No RH or new numerical premise is used. -/
namespace RH080.FiniteFrontier
open Real

/-- The actual terminal prime, not all of the larger interval below 2^64. -/
def terminal : ℕ := 18446744073709551557

/-- Every real 2<=x<terminal has a prime with a closed upper width1550. -/
theorem closed_width1550 (hgap : PrimeGapTable.v1.gaps) {x : ℝ}
    (hx : 2 ≤ x) (hxQ : x < (terminal : ℝ)) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ x + 1550 := by
  obtain ⟨p, q, hp, hq, hpx, hxq, hpq, hqQ, hconsec⟩ :=
    RHOnePrime.FiniteGap.real_bracketing_primes
      RHOnePrimeEvolution.FiniteEndpoint.terminal_prime hx hxQ
  have hg := (RHOnePrime.FiniteGap.source_gap_to_terminal hgap) p q hp hq hpq hqQ hconsec
  have hgn : q ≤ p + 1550 := by omega
  have hgr : (q : ℝ) ≤ (p : ℝ) + 1550 := by exact_mod_cast hgn
  exact ⟨q, hq, hxq, by linarith⟩

/-- Any real width strictly greater than1550 gives a strict upper endpoint. -/
theorem strict_width (hgap : PrimeGapTable.v1.gaps) {x h : ℝ}
    (hx : 2 ≤ x) (hxQ : x < (terminal : ℝ)) (hh : 1550 < h) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + h := by
  exact RHOnePrime.FiniteGap.prime_in_real_interval
    RHOnePrimeEvolution.FiniteEndpoint.terminal_prime
    (RHOnePrime.FiniteGap.source_gap_to_terminal hgap) hx hxQ hh

/-- No fixed +1 loss is needed: every positive epsilon suffices. -/
theorem strict_width1550_add (hgap : PrimeGapTable.v1.gaps) {x ε : ℝ}
    (hx : 2 ≤ x) (hxQ : x < (terminal : ℝ)) (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + (1550 + ε) := by
  exact strict_width hgap hx hxQ (by linarith)

#print axioms closed_width1550
#print axioms strict_width
#print axioms strict_width1550_add
end RH080.FiniteFrontier
