import FKS2Scalar.Target
import FKS2Scalar.Source

namespace FKS2Scalar

/-- Proof-side Taylor polynomial, evaluated exactly; never used by the C workload. -/
def expPoly (x : Rat) : Rat :=
  ∑ k ∈ Finset.range 19, (x / 32) ^ k / (Nat.factorial k : Rat)

def expCheck (x lo hi : Rat) : Bool := decide (
  -32 ≤ x ∧ x ≤ 32 ∧ 0 ≤ expPoly x - 1 / 10 ^ 16 ∧
  lo ≤ (expPoly x - 1 / 10 ^ 16) ^ 32 ∧
  (expPoly x + 1 / 10 ^ 16) ^ 32 ≤ hi)

theorem expPoly_cast (x : Rat) :
    (expPoly x : ℝ) = ∑ k ∈ Finset.range 19,
      ((x : ℝ) / 32) ^ k / (Nat.factorial k : ℝ) := by
  simp [expPoly, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

/-- Analytic Taylor remainder + exact rational certificate. No opaque exp oracle. -/
theorem expCheck_sound {x lo hi : Rat} (h : expCheck x lo hi = true) :
    (lo : ℝ) ≤ Real.exp (x : ℝ) ∧ Real.exp (x : ℝ) ≤ (hi : ℝ) := by
  have hr := of_decide_eq_true h
  change -32 ≤ x ∧ x ≤ 32 ∧ 0 ≤ expPoly x - 1 / 10 ^ 16 ∧
    lo ≤ (expPoly x - 1 / 10 ^ 16) ^ 32 ∧
    (expPoly x + 1 / 10 ^ 16) ^ 32 ≤ hi at hr
  have hc : (-32 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 32 ∧
      0 ≤ (expPoly x : ℝ) - 1 / 10 ^ 16 ∧
      (lo : ℝ) ≤ ((expPoly x : ℝ) - 1 / 10 ^ 16) ^ 32 ∧
      ((expPoly x : ℝ) + 1 / 10 ^ 16) ^ 32 ≤ (hi : ℝ) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hr.1
    · exact_mod_cast hr.2.1
    · simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one,
        Rat.cast_zero] using (Rat.cast_le (K := ℝ)).2 hr.2.2.1
    · simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one]
        using (Rat.cast_le (K := ℝ)).2 hr.2.2.2.1
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one]
        using (Rat.cast_le (K := ℝ)).2 hr.2.2.2.2
  have hx : |(x : ℝ) / 32| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hc.1, hc.2.1]
  have hb := Real.exp_bound hx (show 0 < 19 by norm_num)
  rw [← expPoly_cast] at hb
  have hp : |(x : ℝ) / 32| ^ 19 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have hn : (0 : ℝ) ≤ 20 / ((Nat.factorial 19 : ℝ) * 19) := by positivity
  have he : |Real.exp ((x : ℝ) / 32) - (expPoly x : ℝ)| ≤ 1 / 10 ^ 16 := by
    calc
      _ ≤ |(x : ℝ) / 32| ^ 19 * (20 / ((Nat.factorial 19 : ℝ) * 19)) := hb
      _ ≤ 1 * (20 / ((Nat.factorial 19 : ℝ) * 19)) := mul_le_mul_of_nonneg_right hp hn
      _ ≤ _ := by norm_num
  have hnear := abs_sub_le_iff.mp he
  have hl : (expPoly x : ℝ) - 1 / 10 ^ 16 ≤ Real.exp ((x : ℝ) / 32) := by linarith
  have hu : Real.exp ((x : ℝ) / 32) ≤ (expPoly x : ℝ) + 1 / 10 ^ 16 := by linarith
  have hel : Real.exp (x : ℝ) = Real.exp ((x : ℝ) / 32) ^ 32 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hel]
  exact ⟨hc.2.2.2.1.trans (pow_le_pow_left₀ hc.2.2.1 hl 32),
    (pow_le_pow_left₀ (Real.exp_nonneg _) hu 32).trans hc.2.2.2.2⟩

end FKS2Scalar
