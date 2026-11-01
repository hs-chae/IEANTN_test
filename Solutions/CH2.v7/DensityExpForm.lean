/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityHeight

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
noncomputable def densityEnvelopeExpForm (s tau : ℝ) : ℝ :=
  let h := Real.log (3000000000000 : ℝ)
  let r := (8 * s - 5) / 3
  let q := 5 - 2 * s
  let p := 1 + q / (r * h) + q * (q - 1) / (r * h)^2 +
    q * (q - 1) * (q - 2) / (r * h)^3 + q * (q - 1) * (q - 2) * (q - 3) / (r * h)^4
  2 * (9.795 * Real.exp (-r * h + q * Real.log h) * p / r +
    4.465 * (h^2 + 2*h + 2) / 3000000000000) +
    4 * Real.pi * (9.795 * Real.exp (-r*tau + q*Real.log tau) + 4.465*tau^2*Real.exp (-tau))


/-- Exact exponential form of the moment envelope; this is the expression the numeric checker sees. -/
theorem densityFixedEnvelope_eq_expForm {σ τ : ℝ} (hτ : 28 ≤ τ) :
    densityFixedEnvelope σ τ = densityEnvelopeExpForm σ τ := by
  let H : ℝ := 3000000000000
  have hH0 : 0 < H := by dsimp [H]; norm_num
  have hlH : 0 < Real.log H := Real.log_pos (by dsimp [H]; norm_num)
  have hτ0 : 0 < τ := by linarith
  have hr : 1 - 8 * (1 - σ) / 3 = (8 * σ - 5) / 3 := by ring
  have hmain : H ^ (8 * (1 - σ) / 3 - 1) * Real.log H ^ (5 - 2 * σ) =
      Real.exp (-((8 * σ - 5) / 3) * Real.log H + (5 - 2 * σ) * Real.log (Real.log H)) := by
    rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hlH, ← Real.exp_add]
    congr 1; ring
  have hheight : Real.exp τ ^ (8 * (1 - σ) / 3) * τ ^ (5 - 2 * σ) / Real.exp τ =
      Real.exp (-((8 * σ - 5) / 3) * τ + (5 - 2 * σ) * Real.log τ) := by
    rw [← Real.exp_mul, Real.rpow_def_of_pos hτ0, ← Real.exp_add, ← Real.exp_sub]
    congr 1; ring
  have hF : fksDensityMajorant σ (Real.exp τ) / Real.exp τ =
      9.795 * Real.exp (-((8 * σ - 5) / 3) * τ + (5 - 2 * σ) * Real.log τ) +
        4.465 * τ ^ (2 : ℕ) * Real.exp (-τ) := by
    unfold fksDensityMajorant
    rw [Real.log_exp]
    calc
      _ = 9.795 * (Real.exp τ ^ (8 * (1 - σ) / 3) * τ ^ (5 - 2 * σ) / Real.exp τ) +
          4.465 * τ ^ (2 : ℕ) * (1 / Real.exp τ) := by ring
      _ = _ := by rw [hheight, Real.exp_neg, one_div]
  unfold densityFixedEnvelope densityEnvelopeExpForm densityMomentMain
  norm_num only [show 3 * (10 : ℝ) ^ (12 : ℕ) = (3000000000000 : ℝ) by norm_num]
  rw [hr, hmain, hF]
  ring

end CH2QRH
