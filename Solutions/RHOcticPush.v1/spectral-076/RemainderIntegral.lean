import AnchorScalar
import BoxZeroScalar

/-! A valid full improper-growth allowance for the signed logarithmic remainder.
All integrals below are actual physical-variable integrals, not sampled values. -/
namespace RHOcticPush.Spectral076
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def remainderIntegrand (t : ℝ) : ℝ :=
  1/(Real.sqrt t * (Real.log t)^3)
noncomputable def remainderUpper (t : ℝ) : ℝ :=
  2*Real.sqrt t/((Real.log t)^2*(Real.log t-8))
noncomputable def remainderUpperD (t : ℝ) : ℝ :=
  ((Real.log t)^2-14*Real.log t+32)/
    (Real.sqrt t*(Real.log t)^3*(Real.log t-8)^2)

lemma remainder_integrable {a b : ℝ} (ha : 1<a) (hab : a≤b) :
    IntervalIntegrable remainderIntegrand volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht1 : 1<t := ha.trans_le ht.1
  have ht0 : 0<t := by linarith
  unfold remainderIntegrand
  exact (continuousAt_const.div
    (Real.continuous_sqrt.continuousAt.mul ((Real.continuousAt_log ht0.ne').pow 3))
      (mul_ne_zero (Real.sqrt_pos.mpr ht0).ne' (pow_ne_zero 3 (Real.log_pos ht1).ne'))).continuousWithinAt

lemma remainder_nonneg {t : ℝ} (ht : 1<t) : 0≤remainderIntegrand t := by
  unfold remainderIntegrand
  exact div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _)
    (pow_nonneg (Real.log_pos ht).le 3))

lemma log_remainder_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable remainderIntegrand volume (Real.exp a) (Real.exp b) :=
  remainder_integrable (Real.one_lt_exp_iff.mpr ha) (Real.exp_le_exp.mpr hab)

lemma twice_sqrt_derivative {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun t : ℝ => 2*Real.sqrt t) (1/Real.sqrt t) t := by
  apply ((Real.hasDerivAt_sqrt ht.ne').const_mul 2).congr_deriv
  field_simp

theorem log_slab_bound {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in Real.exp a..Real.exp b,remainderIntegrand t) ≤
      2*(Real.exp (b/2)-Real.exp (a/2))/a^3 := by
  have hp (t : ℝ) (ht : t ∈ uIcc (Real.exp a) (Real.exp b)) : 0<t := by
    rw [uIcc_of_le (Real.exp_le_exp.mpr hab)] at ht
    exact (Real.exp_pos a).trans_le ht.1
  have hder (t : ℝ) (ht : t ∈ uIcc (Real.exp a) (Real.exp b)) :
      HasDerivAt (fun t : ℝ => 2*Real.sqrt t/a^3)
        (1/(Real.sqrt t*a^3)) t := by
    apply ((twice_sqrt_derivative (hp t ht)).div_const (a^3)).congr_deriv
    ring
  have hc : ContinuousOn (fun t : ℝ => 1/(Real.sqrt t*a^3))
      (uIcc (Real.exp a) (Real.exp b)) := by
    intro t ht
    exact (continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul_const (a^3))
      (mul_ne_zero (Real.sqrt_pos.mpr (hp t ht)).ne' (pow_ne_zero 3 ha.ne'))).continuousWithinAt
  have hm : (∫ t in Real.exp a..Real.exp b,remainderIntegrand t) ≤
      ∫ t in Real.exp a..Real.exp b,1/(Real.sqrt t*a^3) := by
    apply intervalIntegral.integral_mono_on (Real.exp_le_exp.mpr hab)
      (log_remainder_integrable ha hab) hc.intervalIntegrable
    intro t ht
    have ht0 : 0<t := (Real.exp_pos a).trans_le ht.1
    have hl : a≤Real.log t := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos a) ht.1
    unfold remainderIntegrand
    apply div_le_div_of_nonneg_left zero_le_one
      (mul_pos (Real.sqrt_pos.mpr ht0) (pow_pos ha 3))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hl 3) (Real.sqrt_nonneg _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable] at hm
  rw [RHOcticPush.BoxZero.sqrt_exp_half, RHOcticPush.BoxZero.sqrt_exp_half] at hm
  convert hm using 1 <;> ring

lemma remainderUpper_derivative {t : ℝ} (ht : 0<t) (hL : 16≤Real.log t) :
    HasDerivAt remainderUpper (remainderUpperD t) t := by
  have hl0 : Real.log t ≠ 0 := by linarith
  have hl8 : Real.log t-8 ≠ 0 := by linarith
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hl := Real.hasDerivAt_log ht.ne'
  have hd := ((Real.hasDerivAt_sqrt ht.ne').const_mul 2).div
    ((hl.pow 2).mul (hl.sub_const 8)) (mul_ne_zero (pow_ne_zero 2 hl0) hl8)
  apply hd.congr_deriv
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  unfold remainderUpperD
  field_simp [ht.ne', hl0, hl8, hs]
  rw [Real.sq_sqrt ht.le]
  <;> ring

lemma remainderUpperD_majorizes {t : ℝ} (ht : 0<t) (hL : 16≤Real.log t) :
    remainderIntegrand t ≤ remainderUpperD t := by
  have hl0 : 0<Real.log t := by linarith
  have hl8 : 0<Real.log t-8 := by linarith
  have he : remainderIntegrand t = (Real.log t-8)^2 /
      (Real.sqrt t*(Real.log t)^3*(Real.log t-8)^2) := by
    unfold remainderIntegrand
    field_simp [hl8.ne']
  rw [he]
  unfold remainderUpperD
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

noncomputable def logCut (k : ℕ) : ℝ := if k=0 then 1 else 2*k

lemma logCut_pos (k : ℕ) : 0<logCut k := by
  by_cases hk : k=0
  · simp [logCut, hk]
  · simp only [logCut, if_neg hk]
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))

lemma logCut_step (k : ℕ) : logCut k≤logCut (k+1) := by
  by_cases hk : k=0
  · subst k
    norm_num [logCut]
  · simp only [logCut, if_neg hk, if_neg (Nat.succ_ne_zero k), Nat.cast_add,
      Nat.cast_one]
    linarith

lemma low_slab_sum :
    (∑ k ∈ Finset.range 8,
      2*(Real.exp (logCut (k+1)/2)-Real.exp (logCut k/2))/(logCut k)^3) < (8 : ℝ) := by
  norm_num [Finset.sum_range_succ, logCut]
  interval_decide 90 (trust := kernel) <;> ring

theorem remainder_low_bound :
    (∫ t in (3 : ℝ)..Real.exp 16,remainderIntegrand t) < (8 : ℝ) := by
  have hint (k : ℕ) : IntervalIntegrable remainderIntegrand volume
      (Real.exp (logCut k)) (Real.exp (logCut (k+1))) :=
    log_remainder_integrable (logCut_pos k) (logCut_step k)
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => Real.exp (logCut k)) (n := 8) (fun k _ => hint k)
  have hs := Finset.sum_le_sum (s := Finset.range 8)
    (fun k _ => log_slab_bound (logCut_pos k) (logCut_step k))
  rw [ht] at hs
  norm_num only [logCut, ↓reduceIte, Nat.cast_ofNat] at hs
  have he1 : Real.exp 1 ≤ (3 : ℝ) := by interval_decide 90 (trust := kernel)
  have he16 : (3 : ℝ) ≤ Real.exp 16 := by interval_decide 90 (trust := kernel)
  have hm : (∫ t in (3 : ℝ)..Real.exp 16,remainderIntegrand t) ≤
      ∫ t in Real.exp 1..Real.exp 16,remainderIntegrand t := by
    apply intervalIntegral.integral_mono_interval he1 he16 le_rfl _
      (log_remainder_integrable (by norm_num : (0 : ℝ)<1) (by norm_num : (1 : ℝ)≤16))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact remainder_nonneg ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans ht.1)
  exact (hm.trans hs).trans_lt low_slab_sum

theorem remainder_tail_bound {x : ℝ} (hx : Real.exp 16≤x) :
    (∫ t in Real.exp 16..x,remainderIntegrand t) ≤ remainderUpper x := by
  have h16 : (1 : ℝ)<Real.exp 16 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hp (t : ℝ) (ht : t ∈ uIcc (Real.exp 16) x) : 0<t := by
    rw [uIcc_of_le hx] at ht
    exact (Real.exp_pos 16).trans_le ht.1
  have hlog (t : ℝ) (ht : t ∈ uIcc (Real.exp 16) x) : 16≤Real.log t := by
    rw [uIcc_of_le hx] at ht
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 16) ht.1
  have hc : ContinuousOn remainderUpperD (uIcc (Real.exp 16) x) := by
    intro t ht
    have ht0 := hp t ht
    have hl0 : 0<Real.log t := by linarith [hlog t ht]
    have hl8 : 0<Real.log t-8 := by linarith [hlog t ht]
    have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr ht0
    unfold remainderUpperD
    fun_prop (disch := positivity)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => remainderUpper_derivative (hp t ht) (hlog t ht)) hc.intervalIntegrable
  have hm : (∫ t in Real.exp 16..x,remainderIntegrand t) ≤
      ∫ t in Real.exp 16..x,remainderUpperD t := by
    apply intervalIntegral.integral_mono_on hx (remainder_integrable h16 hx)
      hc.intervalIntegrable
    intro t ht
    have hu : t ∈ uIcc (Real.exp 16) x := by rw [uIcc_of_le hx]; exact ht
    exact remainderUpperD_majorizes (hp t hu) (hlog t hu)
  have hn : 0≤remainderUpper (Real.exp 16) := by
    unfold remainderUpper
    rw [Real.log_exp]
    positivity
  rw [hmain] at hm
  exact hm.trans (sub_le_self _ hn)

/-- Valid on the entire real ray, with the complete low integral paid once. -/
theorem remainderIntegral_bound {x : ℝ} (hx : Real.exp 24≤x) :
    (∫ t in (3 : ℝ)..x, 1/(Real.sqrt t*(Real.log t)^3)) ≤
      8+2*Real.sqrt x/((Real.log x)^2*(Real.log x-8)) := by
  have h16 : (1 : ℝ)<Real.exp 16 := Real.one_lt_exp_iff.mpr (by norm_num)
  have h3 : (3 : ℝ)≤Real.exp 16 := by interval_decide 90 (trust := kernel)
  have h16x : Real.exp 16≤x := (Real.exp_le_exp.mpr (by norm_num : (16 : ℝ)≤24)).trans hx
  change (∫ t in (3 : ℝ)..x, remainderIntegrand t) ≤ 8+remainderUpper x
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (remainder_integrable (by norm_num : (1 : ℝ)<3) h3)
    (remainder_integrable h16 h16x)]
  linarith [remainder_low_bound, remainder_tail_bound h16x]

#print axioms log_slab_bound
#print axioms remainderUpper_derivative
#print axioms remainder_low_bound
#print axioms remainderIntegral_bound
end RHOcticPush.Spectral076
