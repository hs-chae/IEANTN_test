import FiniteFrontier

/-! The independent finite logarithmic-gap source is the exact CMS(1.15)
consecutive-prime contract attributed to Oliveira e Silva–Herzog–Pardi §2.2.
It is a B-tier literature-computation input, not a PV or kernel recomputation.
The target real-interval theorem is derived below rather than assumed. -/
namespace RH080.FiniteFrontier
open Real

/-- Lower prime endpoint11<=p<=4e18; both prime endpoints and actual
consecutivity are explicit. No real-interval conclusion occurs in this input. -/
def SourceLogSquaredGap : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → 11 ≤ p → p ≤ 4 * 10 ^ 18 →
  (∀ r : ℕ, p < r → r < q → ¬r.Prime) →
  (q : ℝ) - (p : ℝ) < (log (p : ℝ)) ^ 2

lemma exp42_lt_four_e18 : exp (42 : ℝ) < (4 * 10 ^ 18 : ℝ) := by
  have he : exp (1 : ℝ) < 68 / 25 := by linarith [Real.exp_one_lt_d9]
  have hpow : (exp (1 : ℝ)) ^ 42 < (68 / 25 : ℝ) ^ 42 :=
    pow_lt_pow_left₀ he (exp_pos 1).le (by norm_num)
  have h42 : exp (42 : ℝ) = (exp (1 : ℝ)) ^ 42 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 42
  rw [h42]
  norm_num at hpow ⊢
  linarith

/-- A genuine all-real strict interval consequence on the entire finite join.
The source input bounds gaps at p, not the desired interval starting at x. -/
theorem strict_log_squared (hsource : SourceLogSquaredGap) {x : ℝ}
    (hx : 11 ≤ x) (hx42 : x ≤ exp 42) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + (log x) ^ 2 := by
  have hxQ : x < (18446744073709551557 : ℝ) := hx42.trans_lt
    ((exp_lt_exp.mpr (by norm_num : (42 : ℝ) < 44)).trans
      RHOnePrime.FiniteGap.exp44_lt_terminal)
  obtain ⟨p, q, hp, hq, hpx, hxq, hpq, hqQ, hconsec⟩ :=
    RHOnePrime.FiniteGap.real_bracketing_primes
      RHOnePrimeEvolution.FiniteEndpoint.terminal_prime (by linarith : 2 ≤ x) hxQ
  have h11q : 11 < q := by exact_mod_cast (show (11 : ℝ) < q from hx.trans_lt hxq)
  have hp11 : 11 ≤ p := by
    by_contra h
    exact hconsec 11 (by omega) h11q (by norm_num)
  have hpupper : p ≤ 4 * 10 ^ 18 := by
    exact_mod_cast (hpx.trans (hx42.trans exp42_lt_four_e18.le))
  have hg := hsource p q hp hq hpq hp11 hpupper hconsec
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : log (p : ℝ) ≤ log x := log_le_log hp0 hpx
  have hlog0 : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hlogsquare : (log (p : ℝ)) ^ 2 ≤ (log x) ^ 2 := by nlinarith
  exact ⟨q, hq, hxq, by linarith⟩

/-- Exact continuous crossover of a log-squared width with a fixed width. -/
theorem log_squared_le_iff {x W : ℝ} (hx : 1 ≤ x) (hW : 0 ≤ W) :
    (log x) ^ 2 ≤ W ↔ x ≤ exp (sqrt W) := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ log x := log_nonneg hx
  have hs0 : 0 ≤ sqrt W := sqrt_nonneg W
  have hs2 : (sqrt W) ^ 2 = W := sq_sqrt hW
  constructor
  · intro h
    have hl : log x ≤ sqrt W := by nlinarith
    simpa only [Real.exp_log hx0] using exp_le_exp.mpr hl
  · intro h
    have hl : log x ≤ sqrt W := by simpa using log_le_log hx0 h
    nlinarith

/-- Combine two independently named historical source inputs by selecting the
smaller justified width; no claim outside the respective finite range. -/
theorem strict_minimum_width (hgap : PrimeGapTable.v1.gaps)
    (hsource : SourceLogSquaredGap) {x ε : ℝ}
    (hx : 11 ≤ x) (hx42 : x ≤ exp 42) (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) < x + min (1550 + ε) ((log x) ^ 2) := by
  by_cases h : 1550 + ε ≤ (log x) ^ 2
  · have hxQ : x < (terminal : ℝ) := hx42.trans_lt
      ((exp_lt_exp.mpr (by norm_num : (42 : ℝ) < 44)).trans
        RHOnePrime.FiniteGap.exp44_lt_terminal)
    simpa [min_eq_left h] using strict_width1550_add hgap (by linarith) hxQ hε
  · simpa [min_eq_right (le_of_not_ge h)] using strict_log_squared hsource hx hx42

#print axioms exp42_lt_four_e18
#print axioms strict_log_squared
#print axioms log_squared_le_iff
#print axioms strict_minimum_width
end RH080.FiniteFrontier
