import PrimePowerUpper
namespace Ramanujan640
open Real IEANTN Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem invpow_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    1/b^n ≤ 1/a^n :=
  one_div_le_one_div_of_le (pow_pos ha n) (pow_le_pow_left₀ ha.le hab n)

theorem p3_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : p3 b ≤ p3 a := by
  have h1 := invpow_antitone ha hab 1
  have h2 := invpow_antitone ha hab 2
  have h3 := invpow_antitone ha hab 3
  unfold p3
  norm_num only [pow_one] at h1
  simp only [div_eq_mul_inv] at *
  linarith

theorem q_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : q b ≤ q a := by
  have h1 := invpow_antitone ha hab 1
  have h2 := invpow_antitone ha hab 2
  unfold q
  norm_num only [pow_one] at h1
  simp only [div_eq_mul_inv] at *
  linarith

theorem q_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ q a := by unfold q;positivity

theorem pp_lower_slab (hB : Buthe.v1.theorem_2_li_minus_pi)
    (hw : ∀ s : ℝ, 13 ≤ s → p3 s ≤ RamStudy.w s)
    {l u z : ℝ} (hl : 26 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u) :
    p3 (u/2)-q (l/2)*exp (-l/4) ≤ primePart z := by
  have hz : 0 < z := by linarith
  have hroot : 2 ≤ exp (z/2) :=
    (exp_one_gt_two.le).trans (exp_le_exp.mpr (by linarith))
  have hp := primePart_lower_from_source hB hz (by linarith) hroot (hw (z/2) (by linarith))
  have hpoly := p3_antitone (show 0 < z/2 by linarith) (show z/2 ≤ u/2 by linarith)
  have hq := q_antitone (show 0 < l/2 by linarith) (show l/2 ≤ z/2 by linarith)
  have he : exp (-z/4) ≤ exp (-l/4) := exp_le_exp.mpr (by linarith)
  have hprod := mul_le_mul hq he (exp_pos _).le (q_nonneg (show 0 ≤ l/2 by linarith))
  linarith

noncomputable def ppExpSum (z : ℝ) : ℝ :=
  ∑ k ∈ range 8, exp (-z*(1/2-1/(k+3:ℝ)))

noncomputable def ppUpper (z : ℝ) : ℝ :=
  p3 (z/2)+72/(z/2)^4+(3/2:ℝ)*(ppExpSum z+64*exp (-z*(1/2-1/11)))

theorem ppUpper_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ppUpper b ≤ ppUpper a := by
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
  unfold ppUpper
  simp only [div_eq_mul_inv] at *
  linarith

theorem pp_upper_slab (hB : Buthe.v1.theorem_2_li_gt_pi)
    (hW : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ 3/2)
    (h3 : ∀ s : ℝ, 13 ≤ s → RamStudy.w s ≤ p3 s+72/s^4)
    {l z : ℝ} (hl : 26 ≤ l) (hlz : l ≤ z) (hz42 : z ≤ 42) :
    primePart z ≤ ppUpper l := by
  have hz : 0 < z := by linarith
  have hroot : 2 ≤ exp (z/2) :=
    (exp_one_gt_two.le).trans (exp_le_exp.mpr (by linarith))
  have h := primePart_upper_from_source hB (by norm_num : (0:ℝ) ≤ 3/2) hW hz hz42 hroot
  have hb := h3 (z/2) (by linarith)
  have hp := ppUpper_antitone (show 0 < l by linarith) hlz
  unfold ppUpper ppExpSum at hp ⊢
  linarith

#print axioms pp_lower_slab
#print axioms pp_upper_slab
end Ramanujan640
