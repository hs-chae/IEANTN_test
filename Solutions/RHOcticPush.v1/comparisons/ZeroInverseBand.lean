import BoxZeroScalar
import OcticDerivativeMoments
import BPTZeroCount

/-! An independently derived reciprocal-zero lower bound, using the full BPT
count contract rather than a numerical zero table. It is a source-comparison
check; no conclusion of a candidate PNT theorem is assumed. -/
namespace RHOcticPush.ZeroComparison
open Real Set MeasureTheory
open RHLimit.BPTZeroCount RHOcticPush.DerivativeMoments
set_option maxHeartbeats 0

lemma inverse_density_primitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (Real.log (t/(2*Real.pi)))^2/(4*Real.pi))
      ((1/t)*density t) t := by
  have hl := (Real.hasDerivAt_log
    (by positivity : t/(2*Real.pi) ≠ 0)).comp t
      ((hasDerivAt_id t).div_const (2*Real.pi))
  apply ((hl.pow 2).div_const (4*Real.pi)).congr_deriv
  dsimp only [Function.comp_apply, id_eq]
  unfold density
  field_simp
  <;> ring

theorem positive_inverse_band (h : PublishedBound) :
    (14 : ℝ) < IEANTN.zetaZeroesSum Set.univ (Set.Ioc 1000 10000000)
      (fun z => 1/z.im) := by
  have hab : (1000 : ℝ) ≤ 10000000 := by norm_num
  have hp (t : ℝ) (ht : t ∈ uIcc (1000 : ℝ) 10000000) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ uIcc (1000 : ℝ) 10000000) :
      HasDerivAt (fun t : ℝ => 1/t) (-1/t^2) t := by
    simpa only [one_div, neg_div] using hasDerivAt_inv (hp t ht).ne'
  have hc : ContinuousOn (fun t : ℝ => -1/t^2) (uIcc (1000 : ℝ) 10000000) := by
    intro t ht
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (hp t ht).ne')).continuousWithinAt
  have hm : ContinuousOn (fun t : ℝ => (1/t)*density t)
      (uIcc (1000 : ℝ) 10000000) := by
    intro t ht
    unfold density
    exact ((continuousAt_const.div continuousAt_id (hp t ht).ne').mul
      (((continuousAt_id.div_const (2*Real.pi)).log
        (div_ne_zero (hp t ht).ne' (by positivity))).div_const
        (2*Real.pi))).continuousWithinAt
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => inverse_density_primitive (hp t ht)) hm.intervalIntegrable
  have hb := finite_remainder_bound h
    (by linarith [Real.pi_lt_four] : 2*Real.pi ≤ 1000) hab hd hc
  have he : (∫ t in (1000 : ℝ)..10000000, |(-1 : ℝ)/t^2| *Real.log t) ≤
      (Real.log 1000+1)/1000 := by
    have heq : (∫ t in (1000 : ℝ)..10000000, |(-1 : ℝ)/t^2| *Real.log t) =
        ∫ t in (1000 : ℝ)..10000000, Real.log t/t^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [abs_div, abs_neg, abs_one, abs_of_nonneg (sq_nonneg t)]
      ring
    rw [heq, intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ t in Ioi (1000 : ℝ), Real.log t/t^2 := by
        apply setIntegral_mono_set (RHOcticPush.BPTSpecialization.log_sq_integrable
          (by norm_num : (1 : ℝ) ≤ 1000)) _ (Filter.Eventually.of_forall
          (fun _ h => Ioc_subset_Ioi_self h))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact div_nonneg (Real.log_nonneg (by linarith [ht.out])) (sq_nonneg t)
      _ = _ := log_sq_integral (by norm_num)
  rw [hmain] at hb
  have hnum :
      (14 : ℝ) + (7/25)*
        (Real.log 10000000/10000000 + Real.log 1000/1000 + (Real.log 1000+1)/1000) <
      (Real.log (10000000/(2*Real.pi)))^2/(4*Real.pi) -
        (Real.log (1000/(2*Real.pi)))^2/(4*Real.pi) := by
    have h7 : Real.log 10000000 = 7*Real.log 10 := by
      rw [show (10000000 : ℝ) = 10^7 by norm_num, Real.log_pow]
      norm_num
    have h3 : Real.log 1000 = 3*Real.log 10 := by
      rw [show (1000 : ℝ) = 10^3 by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_div (by norm_num : (10000000 : ℝ) ≠ 0) (by positivity),
      Real.log_div (by norm_num : (1000 : ℝ) ≠ 0) (by positivity), h7, h3]
    apply sub_neg.mp
    interval_decide 90 (trust := kernel) <;>
      norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/10000000),
    abs_of_pos (by norm_num : (0 : ℝ) < 1/1000)] at hb
  have hh := (neg_le_abs _).trans hb
  nlinarith

#print axioms positive_inverse_band
end RHOcticPush.ZeroComparison
