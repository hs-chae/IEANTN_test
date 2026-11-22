/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ZeroAbel
open Real Set MeasureTheory
namespace RHContinuation.DiscreteZeroCount
open CH2Section7Z

/-- The actual multiplicity-weighted closed count is integer-valued. -/
theorem count_integer {t : ℝ} (ht : 0 ≤ t) :
    ∃ n : ℤ, ZeroCount.v1.zetaNClosed t = (n : ℝ) := by
  let hfin := finite_zeros_Ioc (a := 0) (b := t) le_rfl
  refine ⟨∑ ρ ∈ hfin.toFinset, IEANTN.zetaOrder ρ, ?_⟩
  rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum hfin]
  norm_cast
  simp

/-- Integrality retains information discarded by the continuous RvM envelope. -/
theorem count_le_of_main_le (hsmall : ZeroCount.v1.rvm_error_small)
    {t : ℝ} (ht : 0 < t) (htop : t ≤ 280) {n : ℕ}
    (hmain : ZeroCount.v1.rvmMain t ≤ (n : ℝ)) :
    ZeroCount.v1.zetaNClosed t ≤ (n : ℝ) := by
  obtain ⟨k, hk⟩ := count_integer ht.le
  have h := (abs_lt.mp (hsmall t ht htop)).2
  have he : (k : ℝ) < (n : ℝ) + 1 := by rw [hk] at h; linarith
  have hi : k < (n : ℤ) + 1 := by exact_mod_cast he
  have hi' : k ≤ (n : ℤ) := by omega
  rw [hk]
  exact_mod_cast hi'

/-- Actual multiplicities imply monotonicity of the actual closed zero count. -/
theorem count_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ZeroCount.v1.zetaNClosed a ≤ ZeroCount.v1.zetaNClosed b := by
  rw [zetaNClosed_eq_sum ha hab, zetaNClosed_eq_sum (ha.trans hab) le_rfl]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hn := zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self
    ((Set.Finite.mem_toFinset _).mp hρ)
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 (h1.trans hab))
  · exact hn
  · exact le_rfl

#print axioms count_le_of_main_le
#print axioms count_mono
end RHContinuation.DiscreteZeroCount
