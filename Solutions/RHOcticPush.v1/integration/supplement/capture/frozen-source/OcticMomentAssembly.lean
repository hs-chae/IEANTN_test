import OcticLowMoment
import OcticFourierMoments
namespace RHOcticPush.Moments
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma M0_split : FourierMoments.M0 =
    (∫ y in (0 : ℝ)..1000, |EvenKernel.transform 4 y|) +
      ∫ y in Ioi (1000 : ℝ), |EvenKernel.transform 4 y| := by
  unfold FourierMoments.M0 FourierMoments.F
  have hs := FourierMoments.F_integrable
  unfold FourierMoments.F at hs
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1000)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hs.mono_set Ioc_subset_Ioi_self)
    (hs.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1000))),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1000)]

lemma M1_split : FourierMoments.M1 =
    (∫ y in (0 : ℝ)..1, |EvenKernel.transform 4 y| * log y) +
    (∫ y in (1 : ℝ)..1000, |EvenKernel.transform 4 y| * log y) +
      ∫ y in Ioi (1000 : ℝ), |EvenKernel.transform 4 y| * log y := by
  unfold FourierMoments.M1 FourierMoments.F
  have hs := FourierMoments.F_log_integrable
  unfold FourierMoments.F at hs
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1000)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hs.mono_set Ioc_subset_Ioi_self)
    (hs.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1000))),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1000),
    ← intervalIntegral.integral_add_adjacent_intervals octic_low_log_integrable
      (octic_log_integrableOn (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1000))]

/-- The finite endpoint certificates feed an actual complete integral, with its
entire analytic tail paid explicitly. -/
theorem M0_le_finite {r : ℝ}
    (hfinite : (∫ y in (0 : ℝ)..1000, |EvenKernel.transform 4 y|) ≤ r) :
    FourierMoments.M0 ≤ r + 16113/1000000 := by
  rw [M0_split]
  exact add_le_add hfinite octic_abs_tail

/-- The logarithmic moment keeps the signed negative interval[0,1]; dropping it
would lose the numerical target. The full infinite tail is included. -/
theorem M1_le_finite {r l : ℝ}
    (hfinite : (∫ y in (1 : ℝ)..1000, |EvenKernel.transform 4 y| * log y) ≤ r)
    (hlog : log 1000 ≤ l) :
    FourierMoments.M1 ≤ -170/99 + r + (16113/1000000) * (l+1) := by
  rw [M1_split]
  have ht := octic_log_tail.trans
    (mul_le_mul_of_nonneg_left (by linarith : log 1000+1 ≤ l+1)
      (by norm_num : (0 : ℝ) ≤ 16113/1000000))
  exact add_le_add (add_le_add octic_low_log hfinite) ht
#print axioms M0_le_finite
#print axioms M1_le_finite
end RHOcticPush.Moments
