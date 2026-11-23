import Anchor640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem pN_antitone {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (N : ℕ) :
    pN N z ≤ pN N a := by
  apply Finset.sum_le_sum
  intro k hk
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha k)
    (pow_le_pow_left₀ ha.le haz k)

lemma tail42_budget :
    pN 20 (42:ℝ)+7*(Nat.factorial 21:ℝ)/(42:ℝ)^21 ≤ 21/20 := by
  norm_num [pN,Finset.sum_range_succ,Nat.factorial]

theorem actual_w_tail_upper {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    (hderiv : LogIntegralDerivative li) {z : ℝ} (hz : 42 ≤ z) :
    w li z ≤ 21/20 := by
  have hw := factorial_barrier26 hseries hderiv (z:=z) (by linarith)
  have hp := pN_antitone (by norm_num : (0:ℝ)<42) hz 20
  have ht : 7*(Nat.factorial 21:ℝ)/z^21 ≤ 7*(Nat.factorial 21:ℝ)/(42:ℝ)^21 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤42) hz 21)
  have hb := tail42_budget
  linarith

theorem actual_w_lower_linear {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    (hderiv : LogIntegralDerivative li) {z : ℝ} (hz : 13 ≤ z) :
    1+1/z ≤ w li z := by
  have hw := (factorial_barrier13 hseries hderiv hz).1
  have hz0 : 0 < z := by linarith
  have h2 : 0 ≤ 2/z^2 := by positivity
  have h3 : 0 ≤ 6/z^3 := by positivity
  norm_num [pN,Finset.sum_range_succ,Nat.factorial] at hw
  rw [one_div]
  linarith

#print axioms actual_w_tail_upper
#print axioms actual_w_lower_linear
end Ramanujan640.AnalyticBarrier
