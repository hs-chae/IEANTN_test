import Ram620Anchors
import ActualPrimePowers
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def lowRoot (l u : ℝ) (n : ℕ) : ℝ :=
  exp (-u*(1/2-1/(n:ℝ)))*max 0 (p3 (u/n)-q (l/n)*exp (-l/(2*n)))
noncomputable def lowerPowers (l u : ℝ) : ℝ :=
  pN 8 (u/2)-q (l/2)*exp (-l/4)+∑ k ∈ range 3, lowRoot l u (k+3)
noncomputable def highRoot (l : ℝ) (n : ℕ) : ℝ :=
  (pN 1 (l/n)+6/(l/n)^2)*exp (-l*(1/2-1/(n:ℝ)))
noncomputable def upperPowers (l : ℝ) : ℝ :=
  pN 8 (l/2)+5*362880/(l/2)^9+
    (∑ k ∈ range 3, highRoot l (k+3))+
    (8/5:ℝ)*(∑ k ∈ range 5, exp (-l*(1/2-1/(k+6:ℝ))))+
    (512/5:ℝ)*exp (-l*(1/2-1/11))

lemma count_nonneg (s : ℝ) : 0 ≤ RamStudy.count s := by
  unfold RamStudy.count
  by_cases hs : 0 ≤ s
  · exact mul_nonneg (div_nonneg hs (exp_pos _).le) (RamanujanPV.primeCounting_nonneg _)
  · have he : exp s < 2 := (exp_lt_one_iff.mpr (lt_of_not_ge hs)).trans (by norm_num)
    rw [primeCounting_zero_of_lt_two (exp_pos s).le he]
    simp
lemma root_nonneg (z : ℝ) (n : ℕ) : 0 ≤ rootTerm z n := by
  rw [rootTerm_normalized]
  exact mul_nonneg (count_nonneg _) (exp_pos _).le

lemma root_lower (hB : Buthe.v1.theorem_2_li_minus_pi)
    {l u z : ℝ} {n : ℕ} (hl : 26 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u) (hu : u ≤ 42)
    (hn : 3 ≤ n) (hn5 : n ≤ 5) : lowRoot l u n ≤ rootTerm z n := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn5' : (n:ℝ) ≤ 5 := by exact_mod_cast hn5
  have hn0 : (0:ℝ) < n := by linarith
  have hs5 : 5 ≤ z/n := (le_div_iff₀ hn0).mpr (by nlinarith)
  have hs42 : z/n ≤ 42 := (div_le_iff₀ hn0).mpr (by nlinarith)
  have hroot : 2 ≤ exp (z/n) := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hd := source_deficit_upper hB (by linarith : 0 < z/n) hroot hs42
  have hc := actual_count_lower hd
  have hw := actual_p3_lower5 hs5
  rw [pN3_eq,actual_w_eq] at hw
  have hp := p3_antitone (by positivity : 0 < z/n) (div_le_div_of_nonneg_right hzu hn0.le)
  have hq := q_antitone (by positivity : 0 < l/n) (div_le_div_of_nonneg_right hlz hn0.le)
  have he : exp (-(z/n)/2) ≤ exp (-l/(2*n)) := by
    apply exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right hlz (by positivity : (0:ℝ) ≤ 2*(n:ℝ))
    have hre : -(z/(n:ℝ))/2 = -(z/(2*(n:ℝ))) := by ring
    rw [hre]
    simpa only [neg_div] using neg_le_neg hh
  have hprod := mul_le_mul hq he (exp_pos _).le (q_nonneg (by positivity : 0 ≤ l/n))
  have hcount : max 0 (p3 (u/n)-q (l/n)*exp (-l/(2*n))) ≤ RamStudy.count (z/n) := by
    apply max_le (count_nonneg _)
    linarith
  have hfac : exp (-u*(1/2-1/(n:ℝ))) ≤ exp (z/n-z/2) := by
    apply exp_le_exp.mpr
    have hi : 1/(n:ℝ) ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hn3
    have hh := mul_le_mul_of_nonneg_right hzu (show 0 ≤ 1/2-1/(n:ℝ) by linarith)
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  unfold lowRoot
  rw [rootTerm_normalized,mul_comm (RamStudy.count _)]
  exact mul_le_mul hfac hcount (le_max_left _ _) (exp_pos _).le

lemma powers_lower (hB : Buthe.v1.theorem_2_li_minus_pi)
    {l u z : ℝ} (hl : 26 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u) (hu : u ≤ 42) :
    lowerPowers l u ≤ primePart z := by
  have hz : 0 < z := by linarith
  have hroot : 2 ≤ exp (z/2) := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hd := source_deficit_upper hB (by linarith : 0 < z/2) hroot (by linarith : z/2 ≤ 42)
  have hc := actual_count_lower hd
  have hw := (actual_p8 (show 13 ≤ z/2 by linarith)).1
  have hp := pN_antitone (show 0 < z/2 by linarith) (show z/2 ≤ u/2 by linarith) 8
  have hq := q_antitone (show 0 < l/2 by linarith) (show l/2 ≤ z/2 by linarith)
  have he : exp (-(z/2)/2) ≤ exp (-l/4) := exp_le_exp.mpr (by linarith)
  have hprod := mul_le_mul hq he (exp_pos _).le (q_nonneg (by linarith : 0 ≤ l/2))
  have hsquare : pN 8 (u/2)-q (l/2)*exp (-l/4) ≤ rootTerm z 2 := by
    rw [rootTerm_normalized]
    norm_num only [Nat.cast_ofNat,sub_self,exp_zero,mul_one]
    linarith
  have hsmall : (∑ k ∈ range 3, lowRoot l u (k+3)) ≤
      ∑ k ∈ range 3, rootTerm z (k+3) := by
    apply sum_le_sum
    intro k hk
    exact root_lower hB hl hlz hzu hu (by omega) (by have := mem_range.mp hk; omega)
  have hsum : (∑ k ∈ range 4, rootTerm z (k+2)) ≤ primePart z := by
    rw [primePart_terms hz.le (hzu.trans hu)]
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega : 4 ≤ 63))
    intro k _ _
    exact root_nonneg z (k+2)
  rw [show (4:ℕ)=3+1 by rfl,sum_range_succ'] at hsum
  norm_num only [Nat.zero_add] at hsum
  have hh : (∑ k ∈ range 3, rootTerm z (k+1+2)) = ∑ k ∈ range 3, rootTerm z (k+3) := by
    apply sum_congr rfl
    intro k hk
    congr 1 <;> omega
  rw [hh] at hsum
  unfold lowerPowers
  linarith

lemma root_upper_small (hB : Buthe.v1.theorem_2_li_gt_pi)
    {l z : ℝ} {n : ℕ} (hl : 26 ≤ l) (hlz : l ≤ z) (hz42 : z ≤ 42)
    (hn : 3 ≤ n) (hn5 : n ≤ 5) : rootTerm z n ≤ highRoot l n := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn5' : (n:ℝ) ≤ 5 := by exact_mod_cast hn5
  have hn0 : (0:ℝ) < n := by linarith
  have hs5 : 5 ≤ z/n := (le_div_iff₀ hn0).mpr (by nlinarith)
  have hs42 : z/n ≤ 42 := (div_le_iff₀ hn0).mpr (by nlinarith)
  have hroot : 2 ≤ exp (z/n) := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hd := source_deficit_pos hB (by linarith : 0 < z/n) hroot hs42
  have hc := actual_count_upper hd.le
  have hw := (actual_p1 hs5).2
  have hp := pN_antitone (by positivity : 0 < l/n) (div_le_div_of_nonneg_right hlz hn0.le) 1
  have h2 := invpow_antitone (by positivity : 0 < l/n) (div_le_div_of_nonneg_right hlz hn0.le) 2
  have hcount : RamStudy.count (z/n) ≤ pN 1 (l/n)+6/(l/n)^2 := by
    have hpos : 0 ≤ deficit (z/n)*exp (-(z/n)/2) := mul_nonneg hd.le (exp_pos _).le
    simp only [div_eq_mul_inv,zero_mul,sub_zero] at hw h2 hp hc ⊢
    linarith
  have he : exp (z/n-z/2) ≤ exp (-l*(1/2-1/(n:ℝ))) := by
    apply exp_le_exp.mpr
    have hi : 1/(n:ℝ) ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hn3
    have hh := mul_le_mul_of_nonneg_right hlz (show 0 ≤ 1/2-1/(n:ℝ) by linarith)
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  rw [rootTerm_normalized]
  unfold highRoot
  exact mul_le_mul hcount he (exp_pos _).le (by unfold pN; positivity)

lemma powers_upper (hB : Buthe.v1.theorem_2_li_gt_pi)
    {l z : ℝ} (hl : 26 ≤ l) (hlz : l ≤ z) (hz42 : z ≤ 42) :
    primePart z ≤ upperPowers l := by
  have hz : 0 < z := by linarith
  have hroot : 2 ≤ exp (z/2) := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hsq := square_term_upper hB hz hz42 hroot
  have hw := (actual_p8 (by linarith : 13 ≤ z/2)).2
  have hp := pN_antitone (by linarith : 0 < l/2) (by linarith : l/2 ≤ z/2) 8
  have h9 := invpow_antitone (by linarith : 0 < l/2) (by linarith : l/2 ≤ z/2) 9
  have hsquare : rootTerm z 2 ≤ pN 8 (l/2)+5*362880/(l/2)^9 := by
    simp only [div_eq_mul_inv] at hw h9 hp hsq ⊢
    linarith
  have hsmall : (∑ k ∈ range 3, rootTerm z (k+3)) ≤ ∑ k ∈ range 3, highRoot l (k+3) := by
    apply sum_le_sum
    intro k hk
    exact root_upper_small hB hl hlz hz42 (by omega) (by have := mem_range.mp hk; omega)
  have hmid : (∑ k ∈ range 5, rootTerm z (k+6)) ≤
      (8/5:ℝ)*(∑ k ∈ range 5, exp (-l*(1/2-1/(k+6:ℝ)))) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have h := rootTerm_upper hB (by norm_num : (0:ℝ)≤8/5) actual_global_no_series hz hz42 (n:=k+6) (by omega)
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤8/5)
    apply exp_le_exp.mpr
    have hi : 1/(k+6:ℝ) ≤ (1/6:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (show (6:ℝ) ≤ (k:ℝ)+6 by have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
    have hh := mul_le_mul_of_nonneg_right hlz (show 0 ≤ 1/2-1/(k+6:ℝ) by linarith)
    simpa only [Nat.cast_add,Nat.cast_ofNat,neg_mul] using neg_le_neg hh
  have htail : (∑ k ∈ range 54, rootTerm z (k+11)) ≤ (512/5:ℝ)*exp (-l*(1/2-1/11)) := by
    have h : (∑ k ∈ range 54, rootTerm z (k+11)) ≤
        ∑ k ∈ range 54, (8/5:ℝ)*exp (-z*(1/2-1/11)) := by
      apply sum_le_sum
      intro k hk
      exact rootTerm_tail_upper hB (by norm_num) actual_global_no_series hz hz42 (by omega)
    have he : exp (-z*(1/2-1/11)) ≤ exp (-l*(1/2-1/11)) := exp_le_exp.mpr (by linarith)
    simp only [sum_const,card_range,nsmul_eq_mul] at h
    nlinarith [exp_pos (-l*(1/2-1/11))]
  have heq : primePart z = rootTerm z 2+(∑ k ∈ range 3, rootTerm z (k+3))+
      (∑ k ∈ range 5, rootTerm z (k+6))+(∑ k ∈ range 54, rootTerm z (k+11)) := by
    rw [primePart_terms hz.le hz42]
    norm_num [sum_range_succ]
    ring
  rw [heq]
  unfold upperPowers
  linarith
#print axioms powers_lower
#print axioms powers_upper
end RHLimit.Ram620
