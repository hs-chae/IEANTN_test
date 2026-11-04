/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.Adapter
import IEANTN.Nodes.MT.v2.Conclusions

/-!
# Old calibration input: Mossinghoff–Trudgian Corollary 1 (`MT.v2.corollary_1`)

The theta input of `DudekPlattNumerics.v4`, used exactly as v4 uses it: the point constant
`3110 ≥ f_R(9400)` and the tail constant `3600 ≥ f_R(9306)` are v4's own kernel-checked endpoint
certificates (`f_R_9400_lt`, `f_R_9306_lt`). The small endpoint pieces at `L₀ = 9400` are bounded
here by kernel arithmetic (`exp (-n) ≤ 2^(-n)`); they enter program A as input targets.
-/

namespace CalibrationPilot.OldInput
open Real IEANTN DudekPlattNumerics.Calculus DudekPlattNumerics.v4.Numerics

/-- `MT.v2.corollary_1` in the nested-square-root shape of v4's numerics. Same algebra as
`DudekPlattNumericsV4Sol.hMT_of_corollary_1` in `Solutions/DudekPlattNumerics.v4/Solution.lean`;
restated here because a module named `Solution` cannot be imported unambiguously. -/
theorem hMT_of_corollary_1 (h : MT.v2.corollary_1) :
    ∀ x : ℝ, 149 ≤ x → |Chebyshev.theta x - x| ≤
      x * C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R)) := by
  intro x hx
  have hb : Eθ x ≤ admissibleBound (Real.sqrt (8 / (17 * Real.pi))) (1 / 4 : ℝ) 1
      (1263 / 200 : ℝ) x := h x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : (0 : ℝ) ≤ Real.log x / (1263 / 200 : ℝ) := by
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  have hq : (Real.log x / (1263 / 200 : ℝ)) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (Real.log x / (1263 / 200 : ℝ))) := by
    rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, Real.rpow_mul hy0, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
  have hrw : admissibleBound (Real.sqrt (8 / (17 * Real.pi))) (1 / 4 : ℝ) 1
      (1263 / 200 : ℝ) x =
      C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R)) := by
    show Real.sqrt (8 / (17 * Real.pi)) * (Real.log x / (1263 / 200)) ^ (1 / 4 : ℝ) *
        Real.exp (-1 * (Real.log x / (1263 / 200)) ^ ((1 : ℝ) / 2)) = _
    unfold C R
    rw [hq, ← Real.sqrt_eq_rpow, neg_one_mul]
  rw [hrw] at hb
  have hEθ : Eθ x = |Chebyshev.theta x - x| / x := rfl
  rw [hEθ, div_le_iff₀ hx0] at hb
  linarith [hb]

/-- Point bound on the whole ray `L ≥ 9400`, constant `3110` (v4's `f_R_9400_lt`). -/
theorem point (h : MT.v2.corollary_1) :
    ∀ L ≥ (9400 : ℝ), |thetaError (exp L)| ≤ 3110 * exp L / L ^ 5 := by
  intro L hL
  have hx149 : (149 : ℝ) ≤ exp L := by
    have := add_one_le_exp L
    linarith
  have hb := theta_bound_of_f_R_le (hMT_of_corollary_1 h) (u0 := 9400) (K := 3110)
    (by unfold R; norm_num) hx149 (by rw [log_exp]; exact hL) f_R_9400_lt.le
  rw [log_exp] at hb
  exact hb

/-- Tail bound from `exp (0.99 · 9400) = exp 9306`, constant `3600` (v4's `f_R_9306_lt`). -/
theorem tail (h : MT.v2.corollary_1) :
    ∀ t : ℝ, exp ((99 / 100 : ℝ) * 9400) ≤ t → |thetaError t| ≤ 3600 * t / log t ^ 5 := by
  intro t ht
  have h9306 : (99 / 100 : ℝ) * 9400 = 9306 := by norm_num
  rw [h9306] at ht
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have ht149 : (149 : ℝ) ≤ t := by
    have := add_one_le_exp (9306 : ℝ)
    linarith
  have hlog : (9306 : ℝ) ≤ log t := by
    have := log_le_log (exp_pos _) ht
    rwa [log_exp] at this
  exact theta_bound_of_f_R_le (hMT_of_corollary_1 h) (u0 := 9306) (K := 3600)
    (by unfold R; norm_num) ht149 hlog f_R_9306_lt.le

theorem A_eq : DudekPlattNumerics.Calculus.A = DudekPlattNumerics.v4.Numerics.A := rfl

/-- `exp (-94) ≤ 2^(-94)` already makes the first error-integral piece negligible. -/
theorem small_d : 4 * (9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 100) < 1 / 5000 := by
  have h := exp_neg_nat_le 94
  have e : -(9400 : ℝ) / 100 = -((94 : ℕ) : ℝ) := by norm_num
  rw [e]
  have hp : (0 : ℝ) < 4 * 9400 ^ 6 := by norm_num
  calc 4 * (9400 : ℝ) ^ 6 * exp (-((94 : ℕ) : ℝ)) ≤ 4 * 9400 ^ 6 * (1 / 2 ^ 94) :=
        mul_le_mul_of_nonneg_left h hp.le
    _ < 1 / 5000 := by norm_num

set_option exponentiation.threshold 10000 in
theorem small_i : 720 * 7 * ((9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 2) / log 2 ^ 8) ≤ 1 / 10 ^ 12 := by
  have h := exp_neg_nat_le 4700
  have e : -(9400 : ℝ) / 2 = -((4700 : ℕ) : ℝ) := by norm_num
  rw [e]
  have hl : (2 / 3 : ℝ) < log 2 := hlog2_proof
  have hl8 : (2 / 3 : ℝ) ^ 8 ≤ log 2 ^ 8 := pow_le_pow_left₀ (by norm_num) hl.le 8
  have hl8p : (0 : ℝ) < (2 / 3) ^ 8 := by norm_num
  have hexp0 : 0 ≤ exp (-((4700 : ℕ) : ℝ)) := (exp_pos _).le
  calc 720 * 7 * ((9400 : ℝ) ^ 6 * exp (-((4700 : ℕ) : ℝ)) / log 2 ^ 8)
      ≤ 720 * 7 * ((9400 : ℝ) ^ 6 * (1 / 2 ^ 4700) / (2 / 3) ^ 8) := by
        gcongr
    _ = (720 * 7 * 9400 ^ 6 * 3 ^ 8) / (2 ^ 8 * 2 ^ 4700) := by ring
    _ ≤ 1 / 10 ^ 12 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        norm_num

set_option exponentiation.threshold 10000 in
theorem small_a : aPiece 9400 ≤ 1 / 10 ^ 12 := by
  have h := exp_neg_nat_le 9400
  have hA := A_lt
  rw [← A_eq] at hA
  have hA0 := DudekPlattNumerics.Calculus.A_nonneg
  unfold aPiece
  have e : -(9400 : ℝ) = -((9400 : ℕ) : ℝ) := by norm_num
  rw [e]
  have hexp0 : 0 ≤ exp (-((9400 : ℕ) : ℝ)) := (exp_pos _).le
  calc 2 * DudekPlattNumerics.Calculus.A * (9400 : ℝ) ^ 6 * exp (-((9400 : ℕ) : ℝ))
      ≤ 2 * 1600 * (9400 : ℝ) ^ 6 * (1 / 2 ^ 9400) := by
        gcongr
    _ = (2 * 1600 * 9400 ^ 6) / 2 ^ 9400 := by ring
    _ ≤ 1 / 10 ^ 12 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        norm_num

/-- The targets program A sums, in the order of its input array. -/
def targets : List ℚ :=
  [3110, 1 / 5000, 3600 / ((99 / 100) ^ 7 * 9400), 720 / 9400, 1 / 10 ^ 12,
    720 * 7 * 256 / 9400 ^ 2, 1 / 10 ^ 12]

/-- The endpoint deviation is strictly below the sum of program A's targets. -/
theorem deviation_lt_targets :
    3110 + dPiece 3600 9400 + iPiece 9400 + aPiece 9400 < ((targets.sum : ℚ) : ℝ) := by
  have hd := small_d
  have hi := small_i
  have ha := small_a
  have hsplit : iPiece 9400 = 720 / 9400 +
      720 * 7 * ((9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 2) / log 2 ^ 8) +
      720 * 7 * 256 / 9400 ^ 2 := by
    unfold iPiece
    ring
  have hdsplit : dPiece 3600 9400 = 4 * (9400 : ℝ) ^ 6 * exp (-(9400 : ℝ) / 100) +
      3600 / ((99 / 100) ^ 7 * 9400) := rfl
  rw [hsplit, hdsplit]
  simp only [targets, List.sum_cons, List.sum_nil]
  push_cast
  linarith

end CalibrationPilot.OldInput
