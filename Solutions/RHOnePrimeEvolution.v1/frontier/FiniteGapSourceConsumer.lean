/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FiniteGapBridge
import TerminalPrime

/-! Literature-computation source interface, with terminal primality genuinely
discharged by kernel Lucas certificates. This does not source-verify the2^64
historical gap computation and does not call it PV.

Primary locator: ThomasR.Nicely, First occurrence prime gaps,12August2019,
https://oeis.org/A000101/a000101.pdf: p1 complete range, p3 record ceiling,
p4 classification, p23 maximal1550 record. The source's practical verification
and believed completeness qualifiers remain an external trust boundary.
-/
namespace RHOnePrime.FiniteGap

/-- B-tier interpretation of the reported completed historical gap computation.
Both prime endpoints and actual consecutivity are explicit; q<2^64 matches the
reported finite range. No desired real-interval conclusion occurs here. -/
def SourceGapB : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → q < 2 ^ 64 →
  (∀ r : ℕ, p < r → r < q → ¬r.Prime) → q - p ≤ 1550

theorem source_gap_to_terminal (hgap : SourceGapB) :
    ConsecutiveGapBound 18446744073709551557 1550 := by
  intro p q hp hq hpq hqQ hconsec
  apply hgap p q hp hq hpq _ hconsec
  have hterminal : 18446744073709551557 < (2 : ℕ) ^ 64 := by norm_num
  exact hqQ.trans_lt hterminal

/-- No primality assumption remains: the actual terminal source proof is
consumed. The sole external input is the precisely stated historical gap bound.
The result is unconditional with respect to RH, conditional on that computation. -/
theorem source_gap_exp24_exp44_bridge (hgap : SourceGapB)
    {c x : ℝ} (hc : (4 / 5 : ℝ) ≤ c)
    (hx : Real.exp 24 ≤ x) (hx44 : x < Real.exp 44) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) < x + c * Real.sqrt x * Real.log x :=
  finite_exp24_exp44_bridge RHOnePrimeEvolution.FiniteEndpoint.terminal_prime
    (source_gap_to_terminal hgap) hc hx hx44

#print axioms source_gap_to_terminal
#print axioms source_gap_exp24_exp44_bridge
end RHOnePrime.FiniteGap
