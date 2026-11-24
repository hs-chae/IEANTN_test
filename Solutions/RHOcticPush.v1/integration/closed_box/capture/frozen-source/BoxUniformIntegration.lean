import BoxZeroUniform

/-! Full-index uniform interchange. A summable family has countable nonzero
support, so no countability of the complete zero subtype is assumed. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- Compact uniform domination by the norm of a summable coefficient family
licenses termwise interval integration over an arbitrary index type. -/
theorem interval_tsum_uniform {ι : Type*} {a b K : ℝ} (hab : a ≤ b)
    (c : ι → ℂ) (hc : Summable c) (F : ι → ℝ → ℂ)
    (hcont : ∀ i, ContinuousOn (F i) (Icc a b))
    (hbound : ∀ i x, x ∈ Icc a b → ‖F i x‖ ≤ K * ‖c i‖) :
    (∑' i, ∫ x in a..b, F i x) = ∫ x in a..b, ∑' i, F i x := by
  classical
  let T := Function.support c
  letI : Countable T := hc.countable_support.to_subtype
  have hz (i : ι) (hi : c i = 0) {x : ℝ} (hx : x ∈ Icc a b) : F i x = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hi] using hbound i x hx) (norm_nonneg _)
  have hs (x : ℝ) (hx : x ∈ Icc a b) : Function.support (fun i => F i x) ⊆ T := by
    intro i hi
    by_contra hn
    exact hi (hz i (by simpa [T, Function.mem_support] using hn) hx)
  have hi : Function.support (fun i => ∫ x in a..b, F i x) ⊆ T := by
    intro i hi
    by_contra hn
    apply hi
    calc
      (∫ x in a..b, F i x) = ∫ _x in a..b, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hz i (by simpa [T, Function.mem_support] using hn)
          (by simpa [uIcc_of_le hab] using hx)
      _ = 0 := intervalIntegral.integral_zero
  rw [← tsum_subtype_eq_of_support_subset hi]
  have hint (i : T) : IntervalIntegrable (F i) volume a b :=
    (show ContinuousOn (F i) (uIcc a b) from
      by simpa [uIcc_of_le hab] using hcont i).intervalIntegrable
  have hsum : Summable (fun i : T => ∫ x in a..b, ‖F i x‖) := by
    apply (((hc.norm.subtype (fun i => i ∈ T)).mul_left K).mul_right |b-a|).of_norm_bounded
    intro i
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    simpa only [norm_norm, Function.comp_apply] using hbound i x (Ioc_subset_Icc_self (by
      simpa only [uIoc_of_le hab] using hx))
  have heq : (∑' i : T, ∫ x in a..b, F i x) =
      ∫ x in a..b, ∑' i : T, F i x := by
    simp_rw [intervalIntegral.integral_of_le hab]
    apply MeasureTheory.integral_tsum_of_summable_integral_norm
    · intro i
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hint i)
    · simpa only [intervalIntegral.integral_of_le hab] using hsum
  rw [heq]
  apply intervalIntegral.integral_congr
  intro x hx
  exact tsum_subtype_eq_of_support_subset (hs x (by simpa [uIcc_of_le hab] using hx))

#print axioms interval_tsum_uniform
end RHOcticPush.BoxPerron
