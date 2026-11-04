/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.OldInput
import FKS2Table4.Math

/-!
# Updated calibration input: the QRH-derived theta bound

Introduced after the old chain was frozen (commit `caf4013`). The input is the existing proved
theorem `FKS2Table4.theta_input : QRHCH2.v5.psi_refined_bound → ∀ L ≥ 300, Eθ (exp L) ≤ Q L` with
`Q L = L²/283 · e^(−L/8)` (`Solutions/FKS2Numerics.v5`, unchanged). Its shape differs from
Mossinghoff–Trudgian's, so this file is the **analytic adapter**: it turns `Q` into the point and
tail constants the generic calibration theorem takes. The small endpoint pieces are reused from
the old input unchanged; they do not depend on the theta input.

Controlled replay: the QRH input was known before the old chain was built.
-/

namespace CalibrationPilot.NewInput
open Real IEANTN DudekPlattNumerics.Calculus DudekPlattNumerics.v4.Numerics

set_option exponentiation.threshold 10000 in
/-- `L⁷ e^(−L/8) / 283 ≤ 10⁻¹²` for every `L ≥ 9306`: one evaluation at `9306`, then
`poly_exp_decreasing`. -/
theorem q7_small {L : ℝ} (hL : 9306 ≤ L) : L ^ 7 * exp (-(1 / 8) * L) / 283 ≤ 1 / 10 ^ 12 := by
  have h1 := poly_exp_decreasing 7 (c := 1 / 8) (L0 := 9306) (L := L) (by norm_num)
    (by norm_num) hL
  have h2 := exp_neg_nat_le 1163
  have e : -(1 / 8 : ℝ) * 9306 ≤ -((1163 : ℕ) : ℝ) := by norm_num
  have h3 : exp (-(1 / 8 : ℝ) * 9306) ≤ 1 / 2 ^ 1163 := (exp_le_exp.mpr e).trans h2
  have h4 : (9306 : ℝ) ^ 7 * exp (-(1 / 8) * 9306) ≤ 9306 ^ 7 * (1 / 2 ^ 1163) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  have h5 : (9306 : ℝ) ^ 7 * (1 / 2 ^ 1163) / 283 ≤ 1 / 10 ^ 12 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    norm_num
  calc L ^ 7 * exp (-(1 / 8) * L) / 283 ≤ 9306 ^ 7 * exp (-(1 / 8) * 9306) / 283 := by
        gcongr
    _ ≤ 9306 ^ 7 * (1 / 2 ^ 1163) / 283 := by gcongr
    _ ≤ 1 / 10 ^ 12 := h5

/-- The QRH theta bound in the calibration shape `|θ(t) − t| ≤ K t / (log t)⁵`, any `K` dominating
`Q(log t) (log t)⁵`, for `log t ≥ 9306`. -/
theorem theta_shape (hpsi : QRHCH2.v5.psi_refined_bound) {t : ℝ} (ht : exp 9306 ≤ t) :
    |thetaError t| ≤ (1 / 10 ^ 12) * t / log t ^ 5 := by
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have hL : (9306 : ℝ) ≤ log t := by
    have := log_le_log (exp_pos _) ht
    rwa [log_exp] at this
  have hLp : 0 < log t := by linarith
  have hq := FKS2Table4.theta_input hpsi (log t) (by linarith)
  rw [exp_log ht0] at hq
  have hE : Eθ t = |Chebyshev.theta t - t| / t := rfl
  rw [hE, div_le_iff₀ ht0] at hq
  have hsmall := q7_small hL
  have hQ : FKS2Table4.Q (log t) * log t ^ 5 = log t ^ 7 * exp (-(1 / 8) * log t) / 283 := by
    unfold FKS2Table4.Q
    have : -log t / 8 = -(1 / 8) * log t := by ring
    rw [this]
    ring
  have hQ' : FKS2Table4.Q (log t) ≤ (1 / 10 ^ 12) / log t ^ 5 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  change |Chebyshev.theta t - t| ≤ _
  calc |Chebyshev.theta t - t| ≤ FKS2Table4.Q (log t) * t := hq
    _ ≤ (1 / 10 ^ 12) / log t ^ 5 * t := mul_le_mul_of_nonneg_right hQ' ht0.le
    _ = (1 / 10 ^ 12) * t / log t ^ 5 := by ring

/-- Point bound on the whole ray `L ≥ 9400`, constant `10⁻¹²`. -/
theorem point (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ L ≥ (9400 : ℝ), |thetaError (exp L)| ≤ (1 / 10 ^ 12) * exp L / L ^ 5 := by
  intro L hL
  have h := theta_shape hpsi (t := exp L) (exp_le_exp.mpr (by linarith))
  rwa [log_exp] at h

/-- Tail bound from `exp (0.99 · 9400) = exp 9306`, constant `10⁻¹²`. -/
theorem tail (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ t : ℝ, exp ((99 / 100 : ℝ) * 9400) ≤ t → |thetaError t| ≤ (1 / 10 ^ 12) * t / log t ^ 5 := by
  intro t ht
  have h9306 : (99 / 100 : ℝ) * 9400 = 9306 := by norm_num
  rw [h9306] at ht
  exact theta_shape hpsi ht

/-- The targets program A sums for the updated input: only the theta entries change. -/
def targets : List ℚ :=
  [1 / 10 ^ 12, 1 / 5000, (1 / 10 ^ 12) / ((99 / 100) ^ 7 * 9400), 720 / 9400, 1 / 10 ^ 12,
    720 * 7 * 256 / 9400 ^ 2, 1 / 10 ^ 12]

theorem deviation_lt_targets :
    1 / 10 ^ 12 + dPiece (1 / 10 ^ 12) 9400 + iPiece 9400 + aPiece 9400 <
      ((targets.sum : ℚ) : ℝ) := by
  have hd := CalibrationPilot.OldInput.small_d
  have hi := CalibrationPilot.OldInput.small_i
  have ha := CalibrationPilot.OldInput.small_a
  have hsplit : iPiece 9400 = 720 / 9400 +
      720 * 7 * ((9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 2) / log 2 ^ 8) +
      720 * 7 * 256 / 9400 ^ 2 := by
    unfold iPiece
    ring
  have hdsplit : dPiece (1 / 10 ^ 12) 9400 = 4 * (9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 100) +
      (1 / 10 ^ 12) / ((99 / 100) ^ 7 * 9400) := rfl
  rw [hsplit, hdsplit]
  simp only [targets, List.sum_cons, List.sum_nil]
  push_cast
  linarith

end CalibrationPilot.NewInput
