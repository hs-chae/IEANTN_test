import NLParabolicComparison
import OcticOptimizedCertified

/-! A real arithmetic consumer at the identical actual left endpoint of the
retained written NL window. The old proof is not imported or upgraded to Lean.
Its displayed full count objective is exceeded by the already source-closed
new octic theorem in a strictly shorter actual interval. -/
namespace RHOcticPush.NLParabolicComparison
open Real
set_option maxHeartbeats 0

theorem actual_prime_count_beats_old_objective
    (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis)
    {L : ℝ} (hL : 24 ≤ L) (hleft : exp 24 ≤ left L) :
    left L + (343827 / 160000 : ℝ) * sqrt (left L) * log (left L) < right L ∧
      oldCountFactor L * sqrt (left L) <
        ((QuarticWindow.primesBetween (left L)
          (left L + (343827 / 160000 : ℝ) * sqrt (left L) * log (left L))).card : ℝ) := by
  have hp : 0 < sqrt (left L) := by rw [left_sqrt]; positivity
  have hc := mul_lt_mul_of_pos_right (new_count_factor_larger hL) hp
  have hn := RHOcticPush.OptimizedFinal.strict_count_214891875 hGreen hN hB rh
    (left L) hleft
  change newCountFactor L * sqrt (left L) < _ at hn
  exact ⟨new_interval_shorter hL, hc.trans hn⟩

end RHOcticPush.NLParabolicComparison
#print axioms RHOcticPush.NLParabolicComparison.actual_prime_count_beats_old_objective
