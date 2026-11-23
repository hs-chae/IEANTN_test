/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao, OpenAI (Codex)
-/
import NumericalZeroLadder
open Real Set MeasureTheory
namespace RHContinuation.ZeroCountIntegral
open CH2Section7Z RHContinuation.DiscreteZeroCount RHContinuation.NumericalZeroLadder
set_option maxHeartbeats 1000000

theorem zsum_split {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 b) f
      = IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 a) f + IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f := by
  have hfb := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := b) le_rfl
  have hfa := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := a) le_rfl
  have hfab := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfb, CH2Section7Z.zetaZeroesSum_eq_sum hfa,
    CH2Section7Z.zetaZeroesSum_eq_sum hfab,
    ← Finset.sum_filter_add_sum_filter_not hfb.toFinset (fun ρ ↦ ρ.im ≤ a)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, ⟨h2, -⟩, h3⟩, h4⟩; exact ⟨h1, ⟨h2, h4⟩, h3⟩
    · rintro ⟨h1, ⟨h2, h4⟩, h3⟩; exact ⟨⟨h1, ⟨h2, h4.trans hab⟩, h3⟩, h4⟩
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, not_le]
    constructor
    · rintro ⟨⟨h1, ⟨-, h2⟩, h3⟩, h4⟩; exact ⟨h1, ⟨h4, h2⟩, h3⟩
    · rintro ⟨h1, ⟨h4, h2⟩, h3⟩; exact ⟨⟨h1, ⟨lt_of_le_of_lt ha h4, h2⟩, h3⟩, h4⟩


theorem count_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ZeroCount.v1.zetaNClosed t := by
  rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum
    (finite_zeros_Ioc (a := 0) (b := t) le_rfl)]
  apply Finset.sum_nonneg
  intro ρ hρ
  simpa using zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self
    ((Set.Finite.mem_toFinset _).mp hρ)

theorem count_zero_base (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (2*π) = 0 := by
  have hm : ZeroCount.v1.rvmMain (2*π) ≤ (0:ℝ) := by
    norm_num [ZeroCount.v1.rvmMain, show (2*π:ℝ) ≠ 0 by positivity]
  have h := count_le_of_main_le hsmall (t := 2*π) (n := 0)
    (by positivity) (by linarith [pi_lt_four]) (by simpa using hm)
  have hh : ZeroCount.v1.zetaNClosed (2*π) ≤ (0:ℝ) := by simpa using h
  exact le_antisymm hh (count_nonneg (t := 2*π) (by positivity))

theorem low_weight_zero (hsmall : ZeroCount.v1.rvm_error_small) (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 (2*π)) f = 0 := by
  let hz := finite_zeros_Ioc (a := 0) (b := 2*π) le_rfl
  have hcount := count_zero_base hsmall
  rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum hz] at hcount
  simp only [one_mul] at hcount
  have hnonneg : ∀ ρ ∈ hz.toFinset, (0:ℝ) ≤ (IEANTN.zetaOrder ρ : ℝ) :=
    fun ρ hρ => zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
      ((Set.Finite.mem_toFinset _).mp hρ)
  have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hcount
  rw [zetaZeroesSum_eq_sum hz]
  exact Finset.sum_eq_zero (fun ρ hρ => by rw [hpoint ρ hρ,mul_zero])

theorem count_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable ZeroCount.v1.zetaNClosed volume a b := by
  apply MonotoneOn.intervalIntegrable
  intro s hs t ht hst
  rw [Set.uIcc_of_le hab] at hs ht
  exact count_mono (ha.trans hs.1) hst

theorem count_div_sq_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ZeroCount.v1.zetaNClosed t / t^2) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => (1:ℝ)/t^2) (Set.uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1))
  simpa only [div_eq_mul_inv, one_mul] using
    (count_integrable ha.le hab).mul_continuousOn hc

theorem reciprocal_identity (hsmall : ZeroCount.v1.rvm_error_small) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ => 1/ρ.im) =
      ZeroCount.v1.zetaNClosed 20000/20000 +
        ∫ t in (2*π)..20000, ZeroCount.v1.zetaNClosed t/t^2 := by
  have ha : (1:ℝ) ≤ 2*π := by linarith [pi_gt_three]
  have hab : (2*π:ℝ) ≤ 20000 := by linarith [pi_lt_four]
  have hn (t : ℝ) (ht : t ∈ uIcc (2*π) (20000:ℝ)) : t ≠ 0 := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1,pi_pos]
  have hd : ∀ t ∈ uIcc (2*π) (20000:ℝ),
      HasDerivAt (fun t : ℝ => 1/t) (-(1/t^2)) t := by
    intro t ht
    simpa only [one_div, inv_pow] using hasDerivAt_inv (hn t ht)
  have hc : ContinuousOn (fun t : ℝ => -(1/t^2)) (uIcc (2*π) 20000) :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (hn t ht))).neg
  have he := RHContinuation.ZeroAbel.exact_finite ha hab hd hc
  rw [count_zero_base hsmall, sub_zero] at he
  have hi : (∫ t in (2*π)..20000,
      -(1/t^2)*(ZeroCount.v1.zetaNClosed t-0)) =
      -(∫ t in (2*π)..20000, ZeroCount.v1.zetaNClosed t/t^2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp
    ring
  rw [hi] at he
  rw [zsum_split (by positivity) hab,low_weight_zero hsmall,zero_add,he]
  ring

/-- Primitive for the RvM main term plus an arbitrary logarithmic discrepancy. -/
noncomputable def primitive (c d t : ℝ) : ℝ :=
  log (t/(2*π))^2/(4*π) - log (t/(2*π))/(2*π) -
    (c*log t + (7/8+d+c))/t

theorem primitive_derivative {t : ℝ} (ht : 0 < t) (c d : ℝ) :
    HasDerivAt (primitive c d)
      ((ZeroCount.v1.rvmMain t+c*log t+d)/t^2) t := by
  have hpi : (2*π:ℝ) ≠ 0 := by positivity
  have hrat : t/(2*π) ≠ 0 := div_ne_zero ht.ne' hpi
  have h1 := (hasDerivAt_id t).div_const (2*π)
  have hlog := (Real.hasDerivAt_log hrat).comp t h1
  have hmain := ((hlog.pow 2).div_const (4*π)).sub (hlog.div_const (2*π))
  have htail := (((Real.hasDerivAt_log ht.ne').const_mul c).add_const
    (7/8+d+c)).div (hasDerivAt_id t) ht.ne'
  refine (hmain.sub htail).congr_deriv ?_
  unfold ZeroCount.v1.rvmMain
  simp only [Function.comp_apply, id_eq, Pi.pow_apply]
  field_simp [ht.ne',hpi,pi_ne_zero]
  ring

theorem integral_main_eval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c d : ℝ) :
    (∫ t in a..b, (ZeroCount.v1.rvmMain t+c*log t+d)/t^2) =
      primitive c d b - primitive c d a := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (primitive c d)
      ((ZeroCount.v1.rvmMain t+c*log t+d)/t^2) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact primitive_derivative (ha.trans_le ht.1) c d
  have hc : ContinuousOn
      (fun t : ℝ => (ZeroCount.v1.rvmMain t+c*log t+d)/t^2) (uIcc a b) := by
    have hne (t : ℝ) (ht : t ∈ uIcc a b) : t ≠ 0 := by
      rw [uIcc_of_le hab] at ht
      exact ne_of_gt (ha.trans_le ht.1)
    have hm : ContinuousOn ZeroCount.v1.rvmMain (uIcc a b) := by
      unfold ZeroCount.v1.rvmMain
      exact (((continuousOn_id.div_const (2*π)).mul
        ((continuousOn_id.div_const (2*π)).log
          (fun t ht => div_ne_zero (hne t ht) (by positivity)))).sub
        (continuousOn_id.div_const (2*π))).add continuousOn_const
    exact ((hm.add (continuousOn_const.mul (continuousOn_id.log hne))).add
      continuousOn_const).div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero _ (hne t ht))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

theorem integral_const_eval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, c/t^2) = c*(1/a-1/b) := by
  have hne (t : ℝ) (ht : t ∈ uIcc a b) : t ≠ 0 := by
    rw [uIcc_of_le hab] at ht
    exact ne_of_gt (ha.trans_le ht.1)
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => -c/t) (c/t^2) t := by
    intro t ht
    simpa only [div_eq_mul_inv, inv_pow, neg_mul, mul_neg, neg_neg] using
      (hasDerivAt_inv (hne t ht)).const_mul (-c)
  have hc : ContinuousOn (fun t : ℝ => c/t^2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hne t ht))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

#print axioms reciprocal_identity
#print axioms integral_main_eval
end RHContinuation.ZeroCountIntegral
