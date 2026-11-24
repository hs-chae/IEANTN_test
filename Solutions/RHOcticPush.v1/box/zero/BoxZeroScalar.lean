import GMComparison
import IEANTN.Vocabulary.RHSmoothing

/-! Scalar allowances for the actual Box zero estimate. No zero estimate is assumed. -/
namespace RHOcticPush.BoxZero
open Real Set IEANTN.RHSmoothing
set_option maxHeartbeats 0

noncomputable def mainCount (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7/8

noncomputable def endpointAllowance : ℝ :=
  2 * mainCount 12 / 12 + (14/25) * (Real.log 12 + 1) / 12 -
    (Real.log (12 / (2 * Real.pi)))^2 / (2 * Real.pi)

lemma endpointAllowance_nonneg : 0 ≤ endpointAllowance := by
  unfold endpointAllowance mainCount
  interval_decide 90 (trust := kernel) <;>
    norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring

theorem endpointAllowance_lt : endpointAllowance < (259/2000 : ℝ) := by
  unfold endpointAllowance mainCount
  interval_decide 90 (trust := kernel) <;>
    norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring

lemma sqrt_exp_half (L : ℝ) : Real.sqrt (Real.exp L) = Real.exp (L/2) := by
  have he : Real.exp L = (Real.exp (L/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem delta_square_budget {L : ℝ} (hL : 35 ≤ L) :
    delta L * L^2 < (1/5800 : ℝ) := by
  have h0 : 0 < L := by linarith
  have hc : (5800 : ℝ) < 2 * Real.pi * (Real.exp (35/2) / 35^3) := by
    interval_decide 90 (trust := kernel) <;>
      norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv] <;> ring
  have hm := RHOcticPush.GM.ratio_mono (by norm_num : (35 : ℝ) ∈ Ici 24)
    (show L ∈ Ici 24 by change 24 ≤ L; linarith) hL
  have hh := hc.trans_le (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * Real.pi))
  rw [← mul_div_assoc] at hh
  have hd := (lt_div_iff₀ (pow_pos h0 3)).mp hh
  have he : delta L * L^2 = L^3 / (2 * Real.pi * Real.exp (L/2)) := by
    unfold delta
    rw [sqrt_exp_half]
    ring
  rw [he]
  apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi * Real.exp (L/2))).mpr
  linarith

theorem delta_small {L : ℝ} (hL : 35 ≤ L) :
    0 < delta L ∧ delta L < (1/7000000 : ℝ) := by
  have hp : 0 < delta L := by unfold delta; exact div_pos (by linarith) (by positivity)
  have hs : (1225 : ℝ) ≤ L^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hp.le
  have hb := delta_square_budget hL
  constructor
  · exact hp
  · linarith

noncomputable def derivativeAllowance (d : ℝ) : ℝ :=
  (14/25) * (d^2 / 3 * 32768 * Real.log 32768 +
    2 * (Real.log 32768 + 1) / 32768)

noncomputable def shiftAllowance (d : ℝ) : ℝ :=
  40000 * d / 24 + 1/10000

/-- A whole-ray scalar budget. The actual zero/cutoff/shift estimates must be
proved independently before this arithmetic can discharge their remainder. -/
theorem uniform_zero_residual {L : ℝ} (hL : 35 ≤ L) :
    Real.exp (delta L) *
        (endpointAllowance + derivativeAllowance (delta L) + shiftAllowance (delta L)) +
      2 * delta L * L^2 < (131/1000 : ℝ) := by
  have hd := delta_small hL
  have hdelta0 := hd.1.le
  have hsq := delta_square_budget hL
  have hlog : 0 ≤ Real.log 32768 := Real.log_nonneg (by norm_num)
  have hder : 0 ≤ derivativeAllowance (delta L) := by
    unfold derivativeAllowance
    positivity
  have hshift : 0 ≤ shiftAllowance (delta L) := by unfold shiftAllowance; positivity
  have hpoly : endpointAllowance + derivativeAllowance (delta L) + shiftAllowance (delta L) ≤
      (259/2000 : ℝ) + derivativeAllowance (1/7000000) + shiftAllowance (1/7000000) := by
    have hb := endpointAllowance_lt.le
    unfold derivativeAllowance shiftAllowance
    gcongr <;> first | exact hdelta0 | exact hd.2.le
  calc
    _ ≤ Real.exp (1/7000000 : ℝ) *
        ((259/2000 : ℝ) + derivativeAllowance (1/7000000) + shiftAllowance (1/7000000)) +
        (1/2900 : ℝ) := by
      have hexp := Real.exp_le_exp.mpr hd.2.le
      have hnum := mul_le_mul hexp hpoly
        (add_nonneg (add_nonneg endpointAllowance_nonneg hder) hshift)
        (by positivity)
      linarith
    _ < _ := by
      unfold derivativeAllowance shiftAllowance
      interval_decide 90 (trust := kernel) <;> ring

theorem mainCount_twelve_nonneg : 0 ≤ mainCount 12 := by
  unfold mainCount
  interval_decide 90 (trust := kernel) <;>
    norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- BPT's actual count envelope at the fixed split, without any zero table. -/
theorem count_height_upper : mainCount 32768 + (7/25) * Real.log 32768 < 40000 := by
  unfold mainCount
  interval_decide 90 (trust := kernel) <;>
    norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The deliberately coarser integral-tail expression needed by the analytic
quadratic-zero-tail proof. This is a numerical inequality, not that tail theorem. -/
theorem quadratic_tail_scalar :
    (Real.log (32768 / (2 * Real.pi)) + 1) / (2 * Real.pi * 32768) +
      (7/25) * (3 * Real.log 32768 + 2) / (32768 : ℝ)^2 < (1/20000 : ℝ) := by
  interval_decide 90 (trust := kernel) <;>
    norm_num [LeanCert.Core.MathConst.toReal, div_eq_mul_inv, mul_inv_rev] <;> ring

#print axioms endpointAllowance_lt
#print axioms delta_square_budget
#print axioms delta_small
#print axioms uniform_zero_residual
#print axioms mainCount_twelve_nonneg
#print axioms count_height_upper
#print axioms quadratic_tail_scalar
end RHOcticPush.BoxZero
