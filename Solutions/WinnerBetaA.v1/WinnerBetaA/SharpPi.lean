/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PiPower
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace WinnerBetaA
open Real MeasureTheory Set IEANTN
open DudekPlattNumerics.Calculus

noncomputable def powerLogPrimitive (β t : ℝ) : ℝ := t ^ β / log t ^ 2

/-- Exact derivative, on the analytic domain actually used below. -/
theorem powerLogPrimitive_deriv {β t : ℝ} (ht : 1 < t) :
    HasDerivAt (powerLogPrimitive β)
      (t ^ (β - 1) / log t ^ 2 * (β - 2 / log t)) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht
  have hd := (Real.hasDerivAt_rpow_const (p := β) (Or.inl ht0.ne')).div
    ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')
  convert hd using 1 <;> try rfl
  simp only [Pi.pow_apply]
  rw [show t ^ β = t ^ (β - 1) * t from by
    rw [← Real.rpow_add_one ht0.ne']; congr 1; ring]
  field_simp
  ring

/-- The exact power/log integral bound retains its lower endpoint term. -/
theorem power_log_integral_bound {β A x : ℝ} (hA : 1 < A) (hAx : A ≤ x)
    (hk : 0 < β - 2 / log A) :
    (∫ t in A..x, t ^ (β - 1) / log t ^ 2) ≤
      (powerLogPrimitive β x - powerLogPrimitive β A) / (β - 2 / log A) := by
  have hA0 : 0 < A := by linarith
  have hx : 1 < x := hA.trans_le hAx
  have hlogA : 0 < log A := log_pos hA
  let κ := β - 2 / log A
  have hκ : 0 < κ := hk
  have hder : ∀ t ∈ Set.uIcc A x, HasDerivAt (powerLogPrimitive β)
      (t ^ (β - 1) / log t ^ 2 * (β - 2 / log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hAx] at ht
    exact powerLogPrimitive_deriv (hA.trans_le ht.1)
  have hcPow : ContinuousOn (fun t : ℝ ↦ t ^ (β - 1)) (Set.uIcc A x) := by
    intro t ht
    rw [Set.uIcc_of_le hAx] at ht
    exact (Real.hasDerivAt_rpow_const (p := β - 1)
      (Or.inl (ne_of_gt (hA0.trans_le ht.1)))).continuousAt.continuousWithinAt
  have hcLog : ContinuousOn (fun t : ℝ ↦ log t) (Set.uIcc A x) := by
    intro t ht
    rw [Set.uIcc_of_le hAx] at ht
    exact (Real.hasDerivAt_log (ne_of_gt (hA0.trans_le ht.1))).continuousAt.continuousWithinAt
  have hlogNe : ∀ t ∈ Set.uIcc A x, log t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hAx] at ht
    exact (log_pos (hA.trans_le ht.1)).ne'
  have hcBase : ContinuousOn (fun t : ℝ ↦ t ^ (β - 1) / log t ^ 2) (Set.uIcc A x) :=
    hcPow.div (hcLog.pow 2) (fun t ht ↦ pow_ne_zero 2 (hlogNe t ht))
  have hcFactor : ContinuousOn (fun t : ℝ ↦ β - 2 / log t) (Set.uIcc A x) :=
    continuousOn_const.sub (continuousOn_const.div hcLog hlogNe)
  have hi : IntervalIntegrable (fun t : ℝ ↦ t ^ (β - 1) / log t ^ 2) volume A x := hcBase.intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ ↦ t ^ (β - 1) / log t ^ 2 * (β - 2 / log t)) volume A x := (hcBase.mul hcFactor).intervalIntegrable
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hid
  have hmono : κ * (∫ t in A..x, t ^ (β - 1) / log t ^ 2) ≤
      powerLogPrimitive β x - powerLogPrimitive β A := by
    rw [← hf, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hAx (hi.const_mul κ) hid
    intro t ht
    have ht1 : 1 < t := hA.trans_le ht.1
    have hlt : 0 < log t := log_pos ht1
    have hlA : log A ≤ log t := log_le_log hA0 ht.1
    have hdiv : 2 / log t ≤ 2 / log A := by gcongr
    have hn : 0 ≤ t ^ (β - 1) / log t ^ 2 := by positivity
    dsimp [κ]
    nlinarith
  exact (le_div_iff₀ hk).mpr (by simpa [κ, mul_comm] using hmono)

/-- Integrability is proved on the actual positive interval, including negative exponents. -/
theorem power_log_integrable {β A x : ℝ} (hA : 1 < A) (hAx : A ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ (β - 1) / log t ^ 2) volume A x := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hAx] at ht
  have ht1 : 1 < t := hA.trans_le ht.1
  have ht0 : 0 < t := by linarith
  exact ((Real.hasDerivAt_rpow_const (p := β - 1) (Or.inl ht0.ne')).continuousAt.div
    ((Real.hasDerivAt_log ht0.ne').continuousAt.pow 2)
      (pow_ne_zero 2 (log_pos ht1).ne')).continuousWithinAt

/-- A sharper log-free theta profile integral, with no sampled continuation. -/
theorem sharp_error_integral_bound {c β A x : ℝ} (hc : 0 ≤ c)
    (hA : 2 ≤ A) (hAx : A ≤ x) (hk : 0 < β - 2 / log A)
    (hθ : HasPowerLogBound Eθ c 0 β A) :
    |errorIntegral x| ≤ 4 * (A - 2) +
      c * (powerLogPrimitive β x - powerLogPrimitive β A) / (β - 2 / log A) := by
  have hA1 : 1 < A := by linarith
  have hA0 : 0 < A := by linarith
  have hx : 2 ≤ x := hA.trans hAx
  have hlog2 := DudekPlattNumerics.v4.Numerics.hlog2_proof
  have hearly : |∫ t in (2 : ℝ)..A, thetaError t / (t * log t ^ 2)| ≤ 4 * (A - 2) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (2 : ℝ)) (b := A) (C := (4 : ℝ))
      (f := fun t ↦ thetaError t / (t * log t ^ 2)) (fun t ht ↦ by
        rw [Set.uIoc_of_le hA] at ht
        simpa only [Real.norm_eq_abs] using abs_errorKernel_le_four hlog2 ht.1.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hA)] using hb
  have hpoint : ∀ t ∈ Set.Ioc A x,
      ‖thetaError t / (t * log t ^ 2)‖ ≤ c * (t ^ (β - 1) / log t ^ 2) := by
    intro t ht
    have ht0 : 0 < t := hA0.trans ht.1
    have hl : 0 < log t := log_pos (by linarith [ht.1])
    have hbound := div_le_div_of_nonneg_right (hθ t ht.1.le) (pow_nonneg hl.le 2)
    have hid : |thetaError t / (t * log t ^ 2)| = Eθ t / log t ^ 2 := by
      rw [abs_div, abs_of_pos (mul_pos ht0 (pow_pos hl 2))]
      dsimp [thetaError, Eθ]
      ring
    rw [Real.norm_eq_abs, hid]
    simpa only [pow_zero, mul_one, mul_div_assoc] using hbound
  have hi := (power_log_integrable (β := β) hA1 hAx).const_mul c
  have hlate : |∫ t in A..x, thetaError t / (t * log t ^ 2)| ≤
      c * (powerLogPrimitive β x - powerLogPrimitive β A) / (β - 2 / log A) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le hAx
      (Filter.Eventually.of_forall hpoint) hi
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hb
    have hb2 := mul_le_mul_of_nonneg_left (power_log_integral_bound hA1 hAx hk) hc
    exact hb.trans (by simpa only [mul_div_assoc] using hb2)
  unfold errorIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_errorKernel (le_refl 2) hA)
    (intervalIntegrable_errorKernel hA hx)]
  exact (abs_add_le _ _).trans (by linarith [hearly, hlate])

/-- Actual normalized prime error, retaining the exact lower endpoint contribution.
The independently supplied profile at A may use a different coefficient from Etheta(x). -/
theorem sharp_pi_transfer_endpoint {c β A x : ℝ} (hc : 0 ≤ c)
    (hA : 2 ≤ A) (hAx : A ≤ x) (hk : 0 < β - 2 / log A)
    (hθ : HasPowerLogBound Eθ c 0 β A) :
    Eπ x ≤ Eθ x + log x / x *
      (3 + 4 * (A - 2) +
        c * (powerLogPrimitive β x - powerLogPrimitive β A) / (β - 2 / log A)) := by
  have hx : 2 ≤ x := hA.trans hAx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc2 : 2 / log (2 : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hlog2]
    linarith [DudekPlattNumerics.v4.Numerics.hlog2_proof]
  have htri : |primeCounting x - Li x| ≤ |thetaError x| / log x + 3 + |errorIntegral x| := by
    rw [FKS2Sol.piMinusLi_eq hx]
    have h1 := abs_add_le ((Chebyshev.theta x - x) / log x + 2 / log 2)
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2))
    have h2 := abs_add_le ((Chebyshev.theta x - x) / log x) (2 / log 2)
    rw [abs_div, abs_of_pos hl, abs_of_nonneg (show 0 ≤ 2 / log (2 : ℝ) by positivity)] at h2
    dsimp [thetaError, errorIntegral] at *
    linarith
  have hscale := mul_le_mul_of_nonneg_left htri (show 0 ≤ log x / x by positivity)
  have hid : log x / x * (|thetaError x| / log x + 3 + |errorIntegral x|) =
      Eθ x + log x / x * (3 + |errorIntegral x|) := by
    dsimp [Eθ, thetaError]
    field_simp
    ring
  have hp : Eπ x ≤ Eθ x + log x / x * (3 + |errorIntegral x|) := by
    unfold Eπ
    rw [div_div_eq_mul_div]
    calc
      _ = log x / x * |primeCounting x - Li x| := by ring
      _ ≤ _ := hscale.trans_eq hid
  have hi := sharp_error_integral_bound hc hA hAx hk hθ
  have hsum : 3 + |errorIntegral x| ≤
      3 + 4 * (A - 2) + c * (powerLogPrimitive β x - powerLogPrimitive β A) /
        (β - 2 / log A) := by linarith
  have hnorm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ log x / x by positivity)
  linarith

/-- Convenient form; the only discarded terms are nonpositive and shown explicitly above. -/
theorem sharp_pi_transfer {c β A x : ℝ} (hc : 0 ≤ c)
    (hA : 2 ≤ A) (hAx : A ≤ x) (hk : 0 < β - 2 / log A)
    (hθ : HasPowerLogBound Eθ c 0 β A) :
    Eπ x ≤ Eθ x + c / (β - 2 / log A) / log x * x ^ (β - 1) +
      (4 * A + 3) * log x / x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hn : 0 ≤ c * powerLogPrimitive β A / (β - 2 / log A) := by
    dsimp [powerLogPrimitive]
    positivity
  have hp := sharp_pi_transfer_endpoint hc hA hAx hk hθ
  calc
    Eπ x ≤ Eθ x + log x / x *
      (3 + 4 * (A - 2) + c * (powerLogPrimitive β x - powerLogPrimitive β A) /
        (β - 2 / log A)) := hp
    _ ≤ Eθ x + log x / x *
      (3 + 4 * A + c * powerLogPrimitive β x / (β - 2 / log A)) := by
        have hb : 3 + 4 * (A - 2) + c * (powerLogPrimitive β x - powerLogPrimitive β A) /
            (β - 2 / log A) ≤ 3 + 4 * A + c * powerLogPrimitive β x / (β - 2 / log A) := by
          have heq : c * (powerLogPrimitive β x - powerLogPrimitive β A) /
              (β - 2 / log A) = c * powerLogPrimitive β x / (β - 2 / log A) -
                c * powerLogPrimitive β A / (β - 2 / log A) := by ring
          rw [heq]
          linarith
        have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ log x / x by positivity)
        linarith
    _ = _ := by
      dsimp [powerLogPrimitive]
      rw [rpow_sub hx0, rpow_one]
      field_simp
      ring

#print axioms sharp_pi_transfer
#print axioms sharp_pi_transfer_endpoint
end WinnerBetaA
