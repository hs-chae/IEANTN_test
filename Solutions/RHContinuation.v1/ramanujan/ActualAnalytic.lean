import ActualGlobalW
import TailW640
namespace RHContinuation.Ramanujan
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier Ramanujan640.MainTerm
open Ramanujan640.Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem actual_mainterm_no_series
    {l : ℝ} (hl : 27 ≤ l) :
    1+14/l+145/l^2+1412/l^3-1/1000 ≤
      l^4*(l/(l-1)*w IEANTN.li (l-1)-(w IEANTN.li l)^2) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have hlm : 0 < l-1 := by linarith
  have hu : 0 < 1/l := by positivity
  have hu26 : 1/l ≤ (1/26:ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<26) (by linarith)
  have hw := actual_factorial_barrier26 (z:=l) (by linarith)
  have hv := actual_factorial_barrier26 (z:=l-1) (by linarith)
  have hPN : 0 ≤ pN 20 l := by unfold pN; positivity
  have hW0 : 0 ≤ w IEANTN.li l := hPN.trans hw.1
  have hW : w IEANTN.li l ≤ P (1/l)+7*(Nat.factorial 21:ℝ)*(1/l)^21 := by
    rw [P_inv]
    simpa [one_div_pow,div_eq_mul_inv,mul_assoc] using hw.2
  have hV : first (1/l) ≤ l/(l-1)*w IEANTN.li (l-1) := by
    rw [first_inv hl1]
    exact mul_le_mul_of_nonneg_left hv.1 (by positivity)
  have h := coupled_mainterm hu hu26 hW0 hW hV
  convert! h using 1 <;> simp only [one_div_pow] <;> field_simp <;> ring


lemma actual_p3_no_series {z : ℝ} (hz : 13 ≤ z) :
    p3 z ≤ RamStudy.w z ∧ RamStudy.w z ≤ p3 z+72/z^4 := by
  have h := actual_factorial_barrier13 hz
  rw [actual_w_eq,pN3_eq] at h
  exact h

lemma actual_global_no_series : ∀ z : ℝ, 0 < z → RamStudy.w z ≤ 8/5 := by
  intro z hz
  simpa only [actual_w_eq] using actual_w_le_eight_fifths hz

lemma actual_base_no_series {z : ℝ} (hz : 27 ≤ z) :
    baseBound z ≤ z^4*(z/(z-1)*RamStudy.w (z-1)-(RamStudy.w z)^2) := by
  simpa only [baseBound,actual_w_eq] using actual_mainterm_no_series hz

lemma actual_linear_no_series {z : ℝ} (hz : 13 ≤ z) : 1+1/z ≤ RamStudy.w z := by
  have h := (actual_p3_no_series hz).1
  have hz0 : 0 < z := by linarith
  have hpos : 0 ≤ 2/z^2+6/z^3 := by positivity
  unfold p3 at h
  linarith

lemma actual_w_tail_no_series {z : ℝ} (hz : 42 ≤ z) : w IEANTN.li z ≤ 21/20 := by
  have hw := actual_factorial_barrier26 (by linarith : (26:ℝ)≤z)
  have hp := pN_antitone (by norm_num : (0:ℝ)<42) hz 20
  have ht : 7*(Nat.factorial 21:ℝ)/z^21 ≤ 7*(Nat.factorial 21:ℝ)/(42:ℝ)^21 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤42) hz 21)
  linarith [tail42_budget]

#print axioms actual_base_no_series
#print axioms actual_global_no_series
#print axioms actual_w_tail_no_series
end RHContinuation.Ramanujan
