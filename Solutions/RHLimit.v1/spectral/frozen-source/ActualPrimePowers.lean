import ActualAnalytic
import SlabMonotonic
namespace RHContinuation.Ramanujan
open Real IEANTN Finset RamanujanPV.AnalyticTransition Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
noncomputable def upper16 (z : ℝ) : ℝ :=
  p3 (z/2)+72/(z/2)^4+(8/5:ℝ)*(ppExpSum z+64*exp (-z*(1/2-1/11)))

theorem upper16_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    upper16 b ≤ upper16 a := by
  have hp := p3_antitone (show 0 < a/2 by linarith) (show a/2 ≤ b/2 by linarith)
  have h4 := invpow_antitone (show 0 < a/2 by linarith) (show a/2 ≤ b/2 by linarith) 4
  have hs : ppExpSum b ≤ ppExpSum a := by
    unfold ppExpSum
    apply sum_le_sum
    intro k hk
    apply exp_le_exp.mpr
    have hi : 1/(k+3:ℝ) ≤ (1/3:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))])
    nlinarith
  have ht : exp (-b*(1/2-1/11)) ≤ exp (-a*(1/2-1/11)) :=
    exp_le_exp.mpr (by linarith)
  unfold upper16
  simp only [div_eq_mul_inv] at *
  linarith

theorem upper16_slab (hB : Buthe.v1.theorem_2_li_gt_pi)
    (hW : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ 8/5)
    (h3 : ∀ s : ℝ, 13 ≤ s → RamStudy.w s ≤ p3 s+72/s^4)
    {l z : ℝ} (hl : 26 ≤ l) (hlz : l ≤ z) (hz42 : z ≤ 42) :
    primePart z ≤ upper16 l := by
  have hz : 0 < z := by linarith
  have hroot : 2 ≤ exp (z/2) :=
    (exp_one_gt_two.le).trans (exp_le_exp.mpr (by linarith))
  have h := primePart_upper_from_source hB (by norm_num : (0:ℝ) ≤ 8/5) hW hz hz42 hroot
  have hb := h3 (z/2) (by linarith)
  have hp := upper16_antitone (show 0 < l by linarith) hlz
  unfold upper16 ppExpSum at hp ⊢
  linarith


#print axioms upper16_slab
end RHContinuation.Ramanujan
