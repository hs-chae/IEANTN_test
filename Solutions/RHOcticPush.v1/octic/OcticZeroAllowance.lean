import OcticGeometry
import BPTZeroCount

/-! Uniform scalar tail allowance for the actual fixed-width scale. This is the
scalar part of the proposed sharp BPT moment route; no zero estimate is assumed
or concluded here, and the analytic moment attachment remains separate. -/
namespace RHOcticPush.ZeroAllowance
open Real Set
set_option maxHeartbeats 0

theorem log_six_thousand_bounds : 1 < Real.log 6000 ∧ Real.log 6000 < 9 := by
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6000)).mpr
    linarith [Real.exp_one_lt_three]
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6000)).mpr
    have he : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 8 / 3)
      (by norm_num : (9 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    have hp' : (8 / 3 : ℝ) ^ 9 < Real.exp 9 := by
      simpa only [Nat.cast_ofNat, mul_one] using hp
    exact (by norm_num : (6000 : ℝ) < (8 / 3 : ℝ) ^ 9).trans hp'

theorem delta_log_bound {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / 6000) :
    δ * Real.log (1 / δ) ≤ Real.log 6000 / 6000 := by
  have hp : 0 < 1 / ((6000 : ℝ) * δ) := by positivity
  have hj := Real.log_le_sub_one_of_pos hp
  have hm : δ * Real.log (1 / (6000 * δ)) ≤ 1 / 6000 - δ := by
    calc _ ≤ δ * (1 / (6000 * δ) - 1) :=
           mul_le_mul_of_nonneg_left hj hδ.le
         _ = _ := by field_simp
  have he : Real.log (1 / δ) =
      Real.log 6000 + Real.log (1 / (6000 * δ)) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hδ.ne', Real.log_one,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : (6000 : ℝ) * δ ≠ 0),
      Real.log_one, Real.log_mul (by norm_num : (6000 : ℝ) ≠ 0) hδ.ne']
    ring
  have hpos := mul_nonneg (show 0 ≤ 1 / 6000 - δ by linarith)
    (show 0 ≤ Real.log 6000 - 1 by linarith [log_six_thousand_bounds.1])
  rw [he]
  nlinarith

noncomputable def residual (δ : ℝ) : ℝ :=
  (14 / 25) * ((16 / 9) * δ * Real.log 12 +
    12 * (δ * Real.log (1 / δ)) + 24 * δ) + 32 * δ / 9

/-- Exact all-small-scale rounding, including the missing negative-log integral.
The independently proved analytic derivative-moment bounds would feed this step. -/
theorem residual_lt_fourteen_thousandths {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / 6000) : residual δ < 14 / 1000 := by
  have hlog := delta_log_bound hδ hsmall
  have hlog' : δ * Real.log (1 / δ) < 9 / 6000 := by
    nlinarith [log_six_thousand_bounds.2]
  have h12 := RHLimit.BPTZeroCount.log_twelve_lt
  have hprod : δ * Real.log 12 ≤ (5 / 2) * δ := by
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 5 / 2 - Real.log 12 by linarith)]
  unfold residual
  nlinarith

theorem fixed_delta_small {L : ℝ} (hL : 24 ≤ L) :
    0 < EvenKernel.δ (43 / 20) L ∧ EvenKernel.δ (43 / 20) L ≤ 1 / 6000 := by
  constructor
  · have hd : 0 < EvenKernel.D (43 / 20) L := by unfold EvenKernel.D; linarith
    exact mul_pos hd (Real.exp_pos _)
  · have hs := RHLimit.OcticGeometry.delta_scaled (C := (43 / 20 : ℝ)) (by norm_num) hL
    apply hs.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5000 * L)).mpr
    linarith

theorem fixed_residual_below_original_budget {L : ℝ} (hL : 24 ≤ L) :
    residual (EvenKernel.δ (43 / 20) L) < 3 / 125 := by
  have h := fixed_delta_small hL
  have he := residual_lt_fourteen_thousandths h.1 h.2
  linarith

#print axioms delta_log_bound
#print axioms residual_lt_fourteen_thousandths
#print axioms fixed_residual_below_original_budget
end RHOcticPush.ZeroAllowance
