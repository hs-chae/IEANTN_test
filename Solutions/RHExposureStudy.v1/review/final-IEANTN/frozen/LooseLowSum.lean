import Section9

open Real Set MeasureTheory IEANTN
namespace LooseLowSum
open CH2Section7Z
set_option maxHeartbeats 1000000

-- This is the same finite sum instance used by the existing CH2 proof,
-- not an inference from a possibly non-summable tsum.
theorem count_zero (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (2*π) = 0 := by
  have ht0 : 0 < 2*π := by positivity
  have htmax : 2*π ≤ 280 := by linarith [pi_lt_four]
  have hm : ZeroCount.v1.rvmMain (2*π) = -1/8 := by
    simp [ZeroCount.v1.rvmMain, show (2*π:ℝ) ≠ 0 by positivity]; norm_num
  have hb := (abs_lt.mp (hsmall (2*π) ht0 htmax)).2
  rw [hm] at hb
  let s := (finite_zeros_Ioc (a:=0) (b:=2*π) le_rfl).toFinset
  have he : ZeroCount.v1.zetaNClosed (2*π) = (∑ ρ ∈ s, zetaOrder ρ : ℤ) := by
    rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum (finite_zeros_Ioc le_rfl)]
    norm_cast
    simp [s]
  rw [he] at hb ⊢
  have hb' : ((∑ ρ ∈ s, zetaOrder ρ : ℤ):ℝ) < 1 := by linarith
  have hlt : (∑ ρ ∈ s, zetaOrder ρ : ℤ) < 1 := by exact_mod_cast hb'
  have h0 : 0 ≤ (∑ ρ ∈ s, zetaOrder ρ : ℤ) := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hh : 0 ≤ (zetaOrder ρ : ℝ) :=
      zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self ((Set.Finite.mem_toFinset _).mp hρ)
    exact_mod_cast hh
  have hz : (∑ ρ ∈ s, zetaOrder ρ : ℤ) = 0 := by omega
  exact_mod_cast hz

theorem low_weight_zero (hsmall : ZeroCount.v1.rvm_error_small) (f : ℂ → ℝ) :
    zetaZeroesSum Set.univ (Set.Ioc 0 (2*π)) f = 0 := by
  let hz := finite_zeros_Ioc (a:=0) (b:=2*π) le_rfl
  have hcount := count_zero hsmall
  rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum hz] at hcount
  simp only [one_mul] at hcount
  have hnonneg : ∀ ρ ∈ hz.toFinset, (0:ℝ) ≤ (zetaOrder ρ : ℝ) :=
    fun ρ hρ => zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self ((Set.Finite.mem_toFinset _).mp hρ)
  have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hcount
  rw [zetaZeroesSum_eq_sum hz]
  exact Finset.sum_eq_zero (fun ρ hρ => by rw [hpoint ρ hρ,mul_zero])

theorem log_ratio_lt : log (20000/(2*π)) < (8.066:ℝ) := by
  rw [log_lt_iff_lt_exp (by positivity)]
  have hex : (271828/100000:ℝ)^8 ≤ exp 8 := by
    have h1 : (271828/100000:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271828/100000) h1 8
    rw [exp_one_pow] at h2
    exact_mod_cast h2
  have hh := quadratic_le_exp_of_nonneg (show 0 ≤ (0.066:ℝ) by norm_num)
  rw [show (8.066:ℝ) = 8 + 0.066 by norm_num,exp_add]
  calc
    20000/(2*π) ≤ 20000/(2*3.141592:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_d6])
    _ < (271828/100000:ℝ)^8*(1+0.066+0.066^2/2) := by norm_num
    _ ≤ _ := by gcongr

theorem integral_eval :
    (∫ t in (2*π)..20000, (1/t)*(log (t/(2*π))/(2*π)+1/(5*t))) =
      log (20000/(2*π))^2/(4*π)+(1/5)*(1/(2*π)-1/20000) := by
  have hpos : 0 < 2*π := by positivity
  have hle : (2*π:ℝ) ≤ 20000 := by linarith [pi_lt_four]
  let F : ℝ → ℝ := fun t => (log t - log (2*π))^2/(4*π) - 1/(5*t)
  have hder : ∀ t ∈ uIcc (2*π) (20000:ℝ), HasDerivAt F
      ((1/t)*(log (t/(2*π))/(2*π)+1/(5*t))) t := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    have ht0 : 0 < t := hpos.trans_le ht.1
    have hl := ((Real.hasDerivAt_log ht0.ne').sub_const (log (2*π))).pow 2
    have hi := ((hasDerivAt_id t).inv ht0.ne').const_mul (1/5:ℝ)
    have hh := (hl.div_const (4*π)).sub hi
    convert hh using 1 <;> try rfl
    · funext y
      change (log y - log (2*π))^2/(4*π) - 1/(5*y) =
        (log y - log (2*π))^2/(4*π) - 1/5 * y⁻¹
      by_cases hy : y = 0
      · simp [hy]
      · field_simp [hy]
    · norm_num [id_eq]
      rw [log_div ht0.ne' hpos.ne']
      field_simp [ht0.ne',pi_ne_zero]
      <;> ring
  have hc : ContinuousOn (fun t : ℝ => (1/t)*(log (t/(2*π))/(2*π)+1/(5*t)))
      (uIcc (2*π) 20000) := by
    rw [uIcc_of_le hle]
    have hne (x : ℝ) (hx : x ∈ Icc (2*π) (20000:ℝ)) : x ≠ 0 := (hpos.trans_le hx.1).ne'
    have h1 : ContinuousOn (fun t : ℝ => 1/t) (Icc (2*π) 20000) :=
      continuousOn_const.div continuousOn_id hne
    have h2 : ContinuousOn (fun t : ℝ => log (t/(2*π))) (Icc (2*π) 20000) :=
      (continuousOn_id.div_const (2*π)).log (fun x hx => div_ne_zero (hne x hx) hpos.ne')
    exact h1.mul ((h2.div_const _).add (continuousOn_const.div
      (continuousOn_const.mul continuousOn_id) (fun x hx => mul_ne_zero (by norm_num) (hne x hx))))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable]
  dsimp [F]
  rw [← log_div (by norm_num : (20000:ℝ) ≠ 0) hpos.ne']
  ring

/-- Only the two original RvM hypotheses. No numerical inverse-ordinate sum. -/
theorem cap (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small) :
    2 * zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1/ρ.im) ≤ (11.1404:ℝ) := by
  have ht : (1:ℝ) ≤ 2*π := by linarith [pi_gt_three]
  have huv : (2*π:ℝ) ≤ 20000 := by linarith [pi_lt_four]
  have hne (t : ℝ) (hh : t ∈ uIcc (2*π) (20000:ℝ)) : t ≠ 0 := by
    rw [uIcc_of_le huv] at hh
    linarith [hh.1,pi_pos]
  have hder : ∀ t ∈ uIcc (2*π) (20000:ℝ), HasDerivAt (fun t : ℝ => 1/t) (-(1/t^2)) t := by
    intro t hh
    have hd := hasDerivAt_inv (hne t hh)
    convert hd using 1 <;> try rfl
    · funext y; simp [one_div]
    · simp [one_div]
  have hcont : ContinuousOn (fun t : ℝ => -(1/t^2)) (uIcc (2*π) 20000) :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hne t ht))).neg
  have h := lehman_antitone hrvm ht huv hder hcont
    (fun t _ => neg_nonpos.mpr (by positivity)) (by positivity)
  have hsplit := CH2Section7A.zsum_split (a:=2*π) (b:=20000) (by positivity) huv (fun ρ : ℂ => 1/ρ.im)
  rw [low_weight_zero hsmall,zero_add] at hsplit
  rw [hsplit]
  rw [integral_eval,count_zero hsmall] at h
  have hm : ZeroCount.v1.rvmMain (2*π) = -1/8 := by
    simp [ZeroCount.v1.rvmMain, show (2*π:ℝ) ≠ 0 by positivity]; norm_num
  rw [hm] at h
  have hl0 : 0 ≤ log ((20000:ℝ)/(2*π)) := log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hslot : log ((20000:ℝ)/(2*π))^2/(4*π) ≤ (8.066:ℝ)^2/(4*3.141592) := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hl0 log_ratio_lt.le _)
      (by norm_num)
    linarith [pi_gt_d6]
  have hsmall1 : (1/5:ℝ)*(1/(2*π)-1/20000) ≤ (1/5)*(1/(2*3.141592)) := by
    have hh : 1/(2*π) ≤ 1/(2*3.141592:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [pi_gt_d6])
    linarith
  have hsmall2 : (1/(2*π))*(log (2*π)/5+2-(0-(-1/8))) ≤
      1/(2*3.141592:ℝ)*(1.9/5+2-1/8) := by
    have hh : 1/(2*π) ≤ 1/(2*3.141592:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [pi_gt_d6])
    have hlog : 0 ≤ log (2*π) := log_nonneg ht
    apply mul_le_mul hh _ (by linarith) (by norm_num)
    linarith [CH2Section9.log_two_pi_le]
  linarith
#print axioms cap
end LooseLowSum
