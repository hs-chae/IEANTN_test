/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Audit300

theorem FKS2Numerics.v3.challenge_calibration_bound : FKS2Numerics.v3.calibration_bound := by
  exact FKS2Correction.calibration_provider

theorem FKS2Numerics.v3.challenge_baseline_bound : FKS2Numerics.v3.baseline_bound := by
  simpa only [FKS2Numerics.v3.baseline_bound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
    using FKS2Correction.baseline_provider
