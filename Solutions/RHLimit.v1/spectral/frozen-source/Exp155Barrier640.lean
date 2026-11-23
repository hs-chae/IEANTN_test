import AnalyticBarrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def expTerm (z : ℝ) (n : ℕ) : ℝ := z^n/(Nat.factorial n:ℝ)
noncomputable def expPartial155 (z : ℝ) : ℝ := ∑ n ∈ range 156, expTerm z n

lemma expTerm_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : 0 ≤ expTerm z n := by
  unfold expTerm
  positivity

lemma expTerm_succ (z : ℝ) (n : ℕ) :
    expTerm z (n+1) = expTerm z n*z/(n+1) := by
  unfold expTerm
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  field_simp
  <;> ring

/-- Exact degree155 exponential enclosure before source-directed rounding. -/
theorem exp_bounds155 {z : ℝ} (hz : 0 ≤ z) (hz44 : z ≤ 44) :
    expPartial155 z ≤ Real.exp z ∧
    Real.exp z ≤ expPartial155 z+(z^155/(Nat.factorial 155:ℝ))*z/(156-z) := by
  have hs : Summable (expTerm z) := Real.summable_pow_div_factorial z
  have he := hs.sum_add_tsum_nat_add 156
  have hr0 : 0 ≤ z/156 := by positivity
  have hr1 : z/156 < 1 := by linarith
  have hstep : ∀ k, expTerm z (156+k+1) ≤ (z/156)*expTerm z (156+k) := by
    intro k
    rw [expTerm_succ]
    have hp : 0 ≤ expTerm z (156+k) := expTerm_nonneg hz _
    have hq : z/((156+k+1:ℕ):ℝ) ≤ z/156 :=
      div_le_div_of_nonneg_left hz (by norm_num)
        (by exact_mod_cast (show (156:ℕ) ≤ 156+k+1 by omega))
    have h := mul_le_mul_of_nonneg_left hq hp
    convert! h using 1 <;> push_cast <;> ring
  have ht := geometric_tail 156 (expTerm_nonneg hz) hr0 hr1 hstep
  have heq : Real.exp z = ∑' n, expTerm z n := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    rfl
  have hrest : Real.exp z-expPartial155 z = ∑' k, expTerm z (156+k) := by
    rw [heq]
    have h : expPartial155 z+(∑' k, expTerm z (156+k)) = ∑' n, expTerm z n := by
      simpa only [expPartial155,Nat.add_comm] using he
    linarith
  have htail : expTerm z 156/(1-z/156) =
      (z^155/(Nat.factorial 155:ℝ))*z/(156-z) := by
    unfold expTerm
    have hden : (156:ℝ)-z ≠ 0 := by linarith
    norm_num [Nat.factorial]
    rw [show z^156=z^155*z by ring]
    field_simp [hden]
    <;> ring
  have hl : 0 ≤ Real.exp z-expPartial155 z := by
    rw [hrest]
    exact tsum_nonneg (fun k => expTerm_nonneg hz _)
  have hu : Real.exp z-expPartial155 z ≤
      (z^155/(Nat.factorial 155:ℝ))*z/(156-z) := by
    rw [hrest]
    exact ht.2.trans_eq htail
  constructor <;> linarith

#print axioms exp_bounds155
end Ramanujan640.AnalyticBarrier
