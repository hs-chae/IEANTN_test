import MainTerm640
import GlobalW640
import GapMonotonic
import SlabMonotonic
namespace Ramanujan640
open Real IEANTN RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem actual_w_eq (z : ℝ) :
    AnalyticBarrier.w IEANTN.li z = RamStudy.w z := by
  unfold AnalyticBarrier.w AnalyticBarrier.A RamStudy.w
  rw [exp_neg]
  ring

theorem pN3_eq (z : ℝ) : AnalyticBarrier.pN 3 z = p3 z := by
  norm_num [AnalyticBarrier.pN,p3,Finset.sum_range_succ,Nat.factorial]

theorem deriv_from_one_to_two (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li) :
    LogIntegralDerivative IEANTN.li := by
  intro x hx
  exact hd x (by linarith)

theorem actual_p3_bounds (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    {z : ℝ} (hz : 13 ≤ z) :
    p3 z ≤ RamStudy.w z ∧ RamStudy.w z ≤ p3 z+72/z^4 := by
  have h := AnalyticBarrier.factorial_barrier13 hs (deriv_from_one_to_two hd) hz
  rw [actual_w_eq,pN3_eq] at h
  norm_num [Nat.factorial] at h
  exact h

theorem actual_global_w (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li) :
    ∀ z : ℝ, 0 < z → RamStudy.w z ≤ 3/2 := by
  intro z hz
  simpa only [actual_w_eq] using AnalyticBarrier.actual_w_le_three_halves hs hd hz

theorem actual_baseBound (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    {z : ℝ} (hz : 27 ≤ z) :
    baseBound z ≤ z^4*(z/(z-1)*RamStudy.w (z-1)-(RamStudy.w z)^2) := by
  simpa only [baseBound,actual_w_eq] using
    MainTerm.actual_mainterm_lower hs (deriv_from_one_to_two hd) hz

theorem actual_w_p1 (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    {z : ℝ} (hz : 13 ≤ z) : 1+1/z ≤ RamStudy.w z := by
  have h := (actual_p3_bounds hs hd hz).1
  have hz0 : 0 < z := by linarith
  have hpos : 0 ≤ 2/z^2+6/z^3 := by positivity
  unfold p3 at h
  linarith

#print axioms actual_p3_bounds
#print axioms actual_baseBound
#print axioms actual_global_w
end Ramanujan640
