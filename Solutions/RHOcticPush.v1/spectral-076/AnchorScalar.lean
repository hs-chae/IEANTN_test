import GMPair
import GMComparison
import LiPVDefinition

/-! Genuine small-height anchor and the full real-ray scalar budget for the
signed spectral approach. No desired spectral inequality is an assumption. -/
namespace RHOcticPush.Spectral076
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

lemma liRegular_nonneg (t : ℝ) : 0 ≤ liRegularPositive t := by
  by_cases ht : 0 ≤ t
  · simpa only [liRegularPositive, if_pos ht] using (liRegular_bounds ht).1
  · simp [liRegularPositive, ht]

lemma li_three_bounds : Real.log 2 + 1/2 ≤ IEANTN.li 3 ∧
    IEANTN.li 3 ≤ Real.log 2 + 2 := by
  have h01 : (1/2 : ℝ) ≤ ∫ t in (0 : ℝ)..1, liRegularPositive t := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_const (c := (1/2 : ℝ))) (liRegularPositive_integrable 0 1)
      (fun t ht => liRegularPositive_lower_half ht.1 ht.2)
    simpa using h
  have h01' : (∫ t in (0 : ℝ)..1, liRegularPositive t) ≤ 1 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (liRegularPositive_integrable 0 1) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t ht => by simpa [liRegularPositive, ht.1] using (liRegular_bounds ht.1).2)
    simpa using h
  have h13 : 0 ≤ ∫ t in (1 : ℝ)..3, liRegularPositive t :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => liRegular_nonneg t)
  have h13' : (∫ t in (1 : ℝ)..3, liRegularPositive t) ≤ 1 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 3)
      (liRegularPositive_integrable 1 3) (intervalIntegrable_const (c := (1/2 : ℝ)))
      (fun t ht => liRegularPositive_half ht.1)
    norm_num at h ⊢
    exact h
  rw [li_pv_regularization (by norm_num : (1 : ℝ) < 3)]
  unfold liRegularPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (liRegularPositive_integrable 0 1) (liRegularPositive_integrable 1 3)]
  norm_num only [show (3 : ℝ)-1 = 2 by norm_num]
  constructor <;> linarith

lemma actual_J_three : riemannPrimeCounting 3 = 2 := by
  rw [← actual_J_eq_riemann (by norm_num : (0 : ℝ) < 3)]
  norm_num [FiniteMangoldtAbel.J, Finset.sum_Icc_succ_top,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3),
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne']

lemma actual_psi_three : Chebyshev.psi 3 = Real.log 6 := by
  norm_num [Chebyshev.psi, Finset.sum_Ioc_succ_top,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)]
  rw [show (6 : ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem actual_error_three : |RHOcticPush.GM.error 3| ≤ 2 := by
  have hli := li_three_bounds
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc : (Real.log 2+1/2)+(Real.log 6-3)/Real.log 3 ≥ 0 := by
    interval_decide 90 (trust := kernel) <;> ring
  have hc' : Real.log 2+2+(Real.log 6-3)/Real.log 3 ≤ 4 := by
    interval_decide 90 (trust := kernel) <;> ring
  unfold RHOcticPush.GM.error
  rw [actual_J_three, actual_psi_three, abs_le]
  constructor <;> linarith

lemma exp_square_ratio_lower {L : ℝ} (hL : 24 ≤ L) :
    (280 : ℝ) < Real.exp (L/2)/L^2 := by
  have hm := RHOcticPush.GM.ratio_mono
    (show (24 : ℝ) ∈ Ici 24 by simp) (show L ∈ Ici 24 from hL) hL
  have h0 : 0 < L := by linarith
  have ha : (280 : ℝ) < Real.exp 12/24^2 := by
    interval_decide 90 (trust := kernel) <;> ring
  have hh := mul_le_mul hL hm (by positivity : 0 ≤ Real.exp (24/2)/24^3) h0.le
  have he : L*(Real.exp (L/2)/L^3) = Real.exp (L/2)/L^2 := by field_simp <;> ring
  rw [he] at hh
  norm_num only [show (24 : ℝ)/2 = 12 by norm_num] at hh
  linarith

theorem spectral_scalar_budget {L : ℝ} (hL : 24 ≤ L) :
    (5 : ℝ) + (47/1000)*(1+4/(L-6))*(Real.exp (L/2)/L^2) <
      (76/1000)*(Real.exp (L/2)/L^2) := by
  have h0 : 0 < L-6 := by linarith
  have hf : 4/(L-6) ≤ (2/9 : ℝ) := by
    apply (div_le_iff₀ h0).mpr
    linarith
  have hE := exp_square_ratio_lower hL
  have he : 0 ≤ Real.exp (L/2)/L^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (show (47/1000 : ℝ)*(1+4/(L-6)) ≤ (47/1000)*(11/9) by linarith) he
  linarith

#print axioms actual_error_three
#print axioms spectral_scalar_budget
end RHOcticPush.Spectral076
