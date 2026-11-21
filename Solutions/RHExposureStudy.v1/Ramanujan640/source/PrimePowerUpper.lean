import SourceDeficits
namespace Ramanujan640
open Real IEANTN Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def rootTerm (z : ℝ) (n : ℕ) : ℝ :=
  (z/(n:ℝ))*primeCounting (exp (z/(n:ℝ)))/exp (z/2)

theorem primePart_terms {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    primePart z = ∑ k ∈ range 63, rootTerm z (k+2) := by
  unfold primePart
  rw [riemann_minus_pi_exp hz0 hz, sum_mul, sum_div]
  apply sum_congr rfl
  intro k hk
  unfold rootTerm
  push_cast
  ring

theorem rootTerm_normalized (z : ℝ) (n : ℕ) :
    rootTerm z n = RamStudy.count (z/n)*exp (z/n-z/2) := by
  unfold rootTerm RamStudy.count
  rw [exp_sub]
  field_simp [exp_ne_zero]
  <;> ring

theorem normalized_count_global (hB : Buthe.v1.theorem_2_li_gt_pi)
    {M : ℝ} (hM : 0 ≤ M) (hw : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ M)
    {s : ℝ} (hs : 0 < s) (hs42 : s ≤ 42) : RamStudy.count s ≤ M := by
  have h := count_upper_of_global_w hB hM hw hs hs42
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ s/exp s by positivity)
  have he : s/exp s*(M*exp s/s)=M := by field_simp [hs.ne',exp_ne_zero]
  rw [he] at hm
  simpa [RamStudy.count] using hm

theorem rootTerm_upper (hB : Buthe.v1.theorem_2_li_gt_pi)
    {M z : ℝ} (hM : 0 ≤ M) (hw : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ M)
    (hz : 0 < z) (hz42 : z ≤ 42) {n : ℕ} (hn : 2 ≤ n) :
    rootTerm z n ≤ M*exp (-z*(1/2-1/(n:ℝ))) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hs : 0 < z/(n:ℝ) := by positivity
  have hs42 : z/(n:ℝ) ≤ 42 := by
    apply (div_le_iff₀ hn0).2
    nlinarith
  have h := normalized_count_global hB hM hw hs hs42
  rw [rootTerm_normalized]
  have he : z/(n:ℝ)-z/2 = -z*(1/2-1/(n:ℝ)) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right h (exp_pos _).le

theorem rootTerm_tail_upper (hB : Buthe.v1.theorem_2_li_gt_pi)
    {M z : ℝ} (hM : 0 ≤ M) (hw : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ M)
    (hz : 0 < z) (hz42 : z ≤ 42) {n : ℕ} (hn : 11 ≤ n) :
    rootTerm z n ≤ M*exp (-z*(1/2-1/11)) := by
  have h := rootTerm_upper hB hM hw hz hz42 (show 2 ≤ n by omega)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply exp_le_exp.mpr
  have hn' : (11:ℝ) ≤ n := by exact_mod_cast hn
  have hi : 1/(n:ℝ) ≤ (1/11:ℝ) := one_div_le_one_div_of_le (by norm_num) hn'
  nlinarith [mul_le_mul_of_nonneg_left hi hz.le]

theorem square_term_upper (hB : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hz : 0 < z) (hz42 : z ≤ 42) (hroot : 2 ≤ exp (z/2)) :
    rootTerm z 2 ≤ RamStudy.w (z/2) := by
  have hd := source_deficit_pos hB (show 0 < z/2 by linarith) hroot (by linarith)
  have hc := actual_count_upper hd.le
  rw [rootTerm_normalized]
  norm_num only [Nat.cast_ofNat]
  rw [sub_self, exp_zero, mul_one]
  simpa using hc

theorem primePart_upper_from_source (hB : Buthe.v1.theorem_2_li_gt_pi)
    {M z : ℝ} (hM : 0 ≤ M) (hw : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ M)
    (hz : 0 < z) (hz42 : z ≤ 42) (hroot : 2 ≤ exp (z/2)) :
    primePart z ≤ RamStudy.w (z/2)+M*(
      (∑ k ∈ range 8, exp (-z*(1/2-1/(k+3:ℝ))))+
      64*exp (-z*(1/2-1/11))) := by
  rw [primePart_terms hz.le hz42]
  have hs : (∑ k ∈ range 63, rootTerm z (k+2)) =
      rootTerm z 2+(∑ k ∈ range 8, rootTerm z (k+3))+
        ∑ k ∈ range 54, rootTerm z (k+11) := by
    rw [show (63:ℕ)=62+1 by rfl, sum_range_succ']
    rw [show (62:ℕ)=8+54 by rfl, sum_range_add]
    simp only [Nat.zero_add]
    have ha : (∑ k ∈ range 8, rootTerm z (k+1+2)) =
        ∑ k ∈ range 8, rootTerm z (k+3) := by
      apply sum_congr rfl
      intro k hk
      congr 1 <;> omega
    have hb : (∑ k ∈ range 54, rootTerm z (8+k+1+2)) =
        ∑ k ∈ range 54, rootTerm z (k+11) := by
      apply sum_congr rfl
      intro k hk
      congr 1 <;> omega
    rw [ha,hb]
    ring
  rw [hs]
  have hfirst := square_term_upper hB hz hz42 hroot
  have hmid : (∑ k ∈ range 8, rootTerm z (k+3)) ≤
      M*(∑ k ∈ range 8, exp (-z*(1/2-1/(k+3:ℝ)))) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have h := rootTerm_upper hB hM hw hz hz42 (n:=k+3) (by omega)
    simpa only [Nat.cast_add,Nat.cast_ofNat] using h
  have hlast : (∑ k ∈ range 54, rootTerm z (k+11)) ≤
      64*(M*exp (-z*(1/2-1/11))) := by
    have hsum : (∑ k ∈ range 54, rootTerm z (k+11)) ≤
        ∑ k ∈ range 54, M*exp (-z*(1/2-1/11)) :=
      sum_le_sum (by intro k hk; exact rootTerm_tail_upper hB hM hw hz hz42 (by omega))
    simp only [sum_const,card_range,nsmul_eq_mul] at hsum
    nlinarith [mul_nonneg hM (exp_pos (-z*(1/2-1/11))).le]
  nlinarith

#print axioms primePart_upper_from_source
end Ramanujan640
